var arrays  = require("pegjs/lib/utils/arrays"),
    objects = require("pegjs/lib/utils/objects"),
    asts    = require("pegjs/lib/compiler/asts"),
    visitor = require("pegjs/lib/compiler/visitor"),
    GrammarError = require("pegjs/lib/grammar-error");

function generateCCode(ast, options) {
  function emitWarning(message, value, region) {
    // В оригинальном pegjs нет ни region-а у узлов (#225), ни коллектора ошибок (#243),
    // поэтому проверяем их наличие, прежде, чем воспользоваться.
    if (region) {
      message = 'Line ' + region.begin.line + ', column ' + region.begin.column + ': ' + message;
    }
    if (options.collector) {
      options.collector.emitWarning(message);
    } else {
      throw new GrammarError(message + ' (' + JSON.stringify(value) + ')');
    }
  }

  function CodeBuilder(code) {
    var _indent = [];
    var _indentCache = '';

    var self = this;

    function push() {
      for (var i = 0; i < arguments.length; ++i) {
        var arg = arguments[i];
        // Генерируем отступы только для непустых строк
        code.push(arg.length > 0 ? _indentCache + arg : arg);
      }
    }
    function indent() {
      // Перед отступом можно опционально добавить какой-то код
      push.apply(self, arguments);
      _indent.push('  ');
      _indentCache = _indent.join('');
    }
    function dedent() {
      _indent.pop();
      _indentCache = _indent.join('');
      // После отступа можно опционально добавить какой-то код
      push.apply(self, arguments);
    }

    this.code = code;
    this.push = push;
    this.pushAll = function(arr) { return push.apply(self, arr); };
    this.indent = indent;
    this.dedent = dedent;
  }
  function makeStack(varName, type) {
    function s(i) { return varName + i; }
    return {
      sp:    -1,///< Номер последней занятой переменной в стеке.
      maxSp: -1,///< Максимальное количество одновременно используемых переменных стека.

      push: function(exprCode) {
        var code = s(++this.sp) + ' = ' + exprCode + ';';

        if (this.sp > this.maxSp) { this.maxSp = this.sp; }

        return code;
      },

      pop: function() {
        var n, values;

        if (arguments.length === 0) {
          return s(this.sp--);
        } else {
          n = arguments[0];
          values = arrays.map(arrays.range(this.sp - n + 1, this.sp + 1), s);
          this.sp -= n;

          return values;
        }
      },

      replace: function(exprCode) {
        this.pop();
        return this.push(exprCode);
      },

      top: function() { return s(this.sp); },

      index: function(i) { return s(this.sp - i); },

      vars: function() {
        if (this.maxSp < 0) {
          return '';
        }
        return type + ' ' + arrays.map(arrays.range(0, this.maxSp + 1), s).join(', ') + ';';
      },
      range: function(sp) {
        if (sp < 0) throw Error('`sp < 0`: (sp, this.sp) == ['+sp+'; '+this.sp+']');
        return arrays.map(arrays.range(sp, this.sp + 1), s);
      },
      /// Возвращает массив с именами переменных для вызова функции
      /// @env Отображение имен меток результатов на позицию в стеке, где он хранится.
      /// @return список имен переменных этого стека.
      args: function(env) {
        var r = [];
        for (var k in env) if (env.hasOwnProperty(k)) {
          r.push(s(env[k]));
        }
        return r;
      },
      result: function() { return s(0); },
    };
  }
  function makeConstantBuilder(varName, type, stringify) {
    function n1(i) { return varName + i; }
    function n2(v, i) { return type + ' ' + n1(i) + ' = ' + v + ';'; }
    var storage = [];
    return {
      add: function(value) {
        if (stringify) { value = stringify.apply(null, arguments); }
        var index = storage.indexOf(value);

        return n1(index < 0 ? storage.push(value) - 1 : index);
      },
      vars: function() { return storage.map(n2); },
    };
  }
  function makeUserCodeBuilder() {
    /// Пространства имен для действий в грамматике. Содержит отображение
    /// имени пространства имен на его инициализоватор.
    var namespaces = {};

    /// @varName Префикс имен функций, генерируемых данной функцией.
    /// @retType Тип возвращаемого значения генерируемых функций.
    /// @argType Тип аргументов, принимаемых генерируемой функцией.
    function makeFunctionBuilder(varName, retType, argType) {
      function n1(i, args) { return varName + i + '(' + args.join(', ') + ')'; }
      function n2(v, i) {
        var p = v.params.map(function(p) { return argType + ' ' + p; });
        p.unshift('struct Context* context');
        return retType + ' ' + n1(i, p);
      }
      function declare(v, i) { return n2(v, i) + ';'; }

      var storage = [];
      return {
        add: function(namespace, params, code, args) {
          args = args || [];
          var pList = params.join(',');
          var index = arrays.indexOf(storage, function(f) {
            return f.namespace === namespace
                && f.params.join(',') === pList
                && f.body === code;
          });
          args.unshift('ctx');
          // Если функции еще нет, добавляем ее и генерируем ее вызов.
          return n1(index < 0 ? storage.push({ namespace: namespace, params: params, body: code }) - 1 : index, args);
        },
        /// Получает предварительные объявления всех функций в указанном пространстве имен.
        /// @return Массив с предварительными объявлениями функций.
        declares: function(ns) {
          if (arguments.length < 1) {
            return storage.map(declare);
          }
          var r = [];
          for (var i = 0; i < storage.length; ++i) {
            var v = storage[i];
            if (ns === v.namespace) {
              r.push(declare(v, i));
            }
          }
          return r;
        },

        /// Получает определения всех функций в указанном пространстве имен.
        /// @return Массив с определениями функций.
        defines: function(ns) {
          var r = [];
          for (var i = 0; i < storage.length; ++i) {
            var v = storage[i];
            if (ns === v.namespace) {
              r.push(n2(v, i) + ' {' + v.body + '}');
            }
          }
          return r;
        },
      };
    }
    /// Пользовательские предикаты грамматики.
    var predicates  = makeFunctionBuilder('is', 'int', 'struct Result*');
    /// Пользовательские действия грамматики.
    var actions     = makeFunctionBuilder('f', 'void', 'struct Result*');

    return {
      addInitializer: function(namespace, code) {
        var ns = namespaces[namespace] || {};
        ns.initializer = code;
        namespaces[namespace] = ns;
      },
      addPredicate: function(namespace, params, code, args) {
        namespaces[namespace] = namespaces[namespace] || {};
        return predicates.add(namespace, params, code, args);
      },
      addAction: function(namespace, params, code, args) {
        namespaces[namespace] = namespaces[namespace] || {};
        return actions.add(namespace, params, code, args);
      },
      /// Генерирует массив с кодом файлов для каждого обнаруженного в грамматике
      /// пространства имен.
      buildFiles: function() {
        var r = [];
        for (var ns in namespaces) {
          var info = namespaces[ns];
          var b = new CodeBuilder([
            '/* Namespace: ' + ns + ' */',
            '#include "peg.h"',
          ]);
          b.push('/*~~~~~~~~~~~ PREDICATES FORWARD DECLARATIONS ~~~~~~~~~~~~*/');
          b.pushAll(predicates.declares(ns));
          b.push('/*~~~~~~~~~~~~~ ACTIONS FORWARD DECLARATIONS ~~~~~~~~~~~~~*/');
          b.pushAll(actions.declares(ns));
          b.push('/*~~~~~~~~~~~~~~~~~~~~~ INITIALIZER ~~~~~~~~~~~~~~~~~~~~~~*/');
          if (info.initializer) {
            b.push(info.initializer);
          }
          b.push('/*~~~~~~~~~~~~~~~~~~~~~~ PREDICATES ~~~~~~~~~~~~~~~~~~~~~~*/');
          b.pushAll(predicates.defines(ns));
          b.push('/*~~~~~~~~~~~~~~~~~~~~~~~~ ACTIONS ~~~~~~~~~~~~~~~~~~~~~~~*/');
          b.pushAll(actions.defines(ns));

          r.push(b.code.join('\n'));
        }
        return r;
      },
      /// Заполняет указанный CodeBuilder кодом предварительных объявлений функций
      /// для действий и предикатов.
      /// @b CodeBuilder
      declares: function(b) {
        b.push('/*~~~~~~~~~~~ PREDICATES FORWARD DECLARATIONS ~~~~~~~~~~~~*/');
        b.pushAll(predicates.declares());
        b.push('/*~~~~~~~~~~~~~ ACTIONS FORWARD DECLARATIONS ~~~~~~~~~~~~~*/');
        b.pushAll(actions.declares());
      }
    };
  }
  function makeContext(code) {
    var resultStack = makeStack('r', 'ResultPtr');
    var posStack    = makeStack('p', 'struct Location');

    var builder = new CodeBuilder(code);

    function pushPos() {
      // Эта функция сгенерирует некорректный код для C, поэтому ничего в нее
      // не передаем. Нам важно только то, что сейчас увеличится указатель стека.
      posStack.push();
      return 'memcpy(&' + posStack.top() + ', &ctx->current, sizeof(struct Location));';
    }
    function popPos() {
      return 'memcpy(&ctx->current, &' + posStack.pop() + ', sizeof(struct Location));';
    }

    function make(sp, env, action) {
      return {
        sp:     sp,    ///< Номер первой переменной для этого контекста.
        env:    env,   // mapping of label names to stack positions
        action: action,// action nodes pass themselves to children here

        resultStack: resultStack,
        posStack: posStack,

        pushCode: builder.push,
        indent: builder.indent,
        dedent: builder.dedent,

        child: make,

        pushPos: pushPos,
        popPos:  popPos,
      };
    }
    return make(-1, {}, null);
  }

  function generateSimplePredicate(expression, negative, context) {
    context.pushCode(
      context.pushPos(),
      '++ctx->failInfo.silent'
    );
    generate(expression, context.child(context.sp + 1, objects.clone(context.env), null));
    var r = context.resultStack.pop();
    var f = context.resultStack.push('&FAILED');
    var p = context.popPos();
    context.pushCode(
      '--ctx->failInfo.silent',
      'if (' + (negative ? '' : '!') + 'isFailed(' + r + ')) {'
    );
    if (negative) {
      context.pushCode(
        '  ' + r + ' = &NIL;',
        '} else {',
        '  freeResult(' + r + ');',
        '  ' + p,
        '  ' + f,
        '}'
      );
    } else {
      context.pushCode(
        '  freeResult(' + r + ');',
        '  ' + p,
        '  ' + r + ' = &NIL;',
        '} else {',
        '  ' + f,
        '}'
      );
    }
  }
  function generateSemanticPredicate(namespace, code, negative, context) {
    var f = context.resultStack.push('&FAILED');
    var n = context.resultStack.replace('&NIL');
    var params = objects.keys(context.env);
    var args = context.resultStack.args(context.env);
    context.pushCode(
      'if (' + (negative ? '!' : '') + ucb.addPredicate(namespace, params, code, args) + ') {',
      '  ' + (negative ? f : n),
      '} else {',
      '  ' + (negative ? n : f),
      '}'
    );
  }
  function generateRange(expression, context, min, max) {
    // Если задан минимум, то может понадобится откатится в начало правила, поэтому
    // запоминаем текущую позицию. Однако, если минимум равен 0, то фактически его нет
    // поэтому в этом случае никакого запоминания не требуется.
    var hasMin = min && min !== 0;
    if (hasMin) {
      context.pushCode(context.pushPos());
    }
    context.pushCode(context.resultStack.push('createArray()'));
    var arr = context.resultStack.top();
    context.indent('do {');
    // Если задан максимум, генерируем проверку максимума
    if (max) {
      context.pushCode('if (' + arr + '->count >= ' + max + ') { break; }');
    }
    generate(expression, context.child(context.sp + 1, objects.clone(context.env), null));
    context.pushCode('if (isFailed(' + context.resultStack.top() + ')) { break; }');
    context.pushCode('append(' + arr + ', ' + context.resultStack.pop() + ');');
    context.dedent('} while (1);');
    // Если задан максимум, генерируем проверку минимума
    if (hasMin) {
      context.resultStack.pop();
      context.pushCode(
        'if (' + arr + '->count < ' + min + ') {',
        '  ' + context.popPos(),
        '  freeResult(' + arr + ');',
        '  ' + context.resultStack.push('&FAILED'),
        '}'
      );
    }
  }
  /// Возвращает имя функции, разбирающей правило с указанным именем.
  function r(name) { return '_parse' + name; }
  function rDef(node) { return 'INTERNAL static struct Result* ' + r(node.name) + '(struct Context* ctx)'; }
  function hex(ch) { return ch.charCodeAt(0).toString(16).toUpperCase(); }
  function escape(s) {
    return s
      .replace(/\\/g,   '\\\\')   // backslash
      .replace(/"/g,    '\\"')    // closing double quote
      .replace(/\x07/g, '\\a')    // alarm
      .replace(/\x08/g, '\\b')    // backspace
      .replace(/\t/g,   '\\t')    // horizontal tab
      .replace(/\n/g,   '\\n')    // line feed
      .replace(/\x0B/g, '\\v')    // vertival tab
      .replace(/\f/g,   '\\f')    // form feed
      .replace(/\r/g,   '\\r')    // carriage return
      .replace(/[\x00-\x06\x0E\x0F]/g,  function(ch) { return '\\x0' + hex(ch); })
      .replace(/[\x10-\x1F\x80-\xFF]/g, function(ch) { return '\\x'  + hex(ch); });
  }

  function createLookupTable(ruleNames) {
    var entries = ruleNames.sort().map(function(n) {
      return '  { ' + n.length + ', "' + n + '", &' + r(n) + ' }';
    });
    return [
      'static struct ParseFunc funcs[] = {',
      entries.join(',\n'),
      '};',
    ];
  }

  var literals    = makeConstantBuilder('l', 'static struct Literal', function(v) {
    return '{ ' + v.length + ', "' + escape(v) + '" }';
  });
  var charClasses = makeConstantBuilder('c', 'static struct CharClass', function(parts) {
    var single = parts.filter(function(p){return !(p instanceof Array);}).join('');
    var ranges = parts.filter(function(p){return (p instanceof Array);}).map(function(p) { return p.join(''); });

    return [
      '{',
      '  MAKE_LENGTHS(' + single.length + ', ' + ranges.length + '),',
      '  "' + single + '",',
      '  "' + ranges.join('') + '"',
      '}',
    ].join('\n');
  });
  var expected    = makeConstantBuilder('e', 'static struct Expected', function(type, value, description) {
    return '{ MAKE_TYPEANDLEN(E_EX_TYPE_' + type + ', ' + description.length + '), "' + escape(description) + '" }';
  });

  var ucb = makeUserCodeBuilder();

  var generate = visitor.build({
    grammar: function(node) {
      node.initializers.forEach(generate);
      var rules = node.rules.map(function(r) {
        return generate(r).join('\n')
      });

      var b = new CodeBuilder([
        '/*Parser*/',
        '#include "peg-internal.h"',
        '',
      ]);
      // Предварительные объявления функций для вызова пользовательского кода.
      ucb.declares(b);

      b.push('/*~~~~~~~~~~~~~~~~~~~~~~ LITERALS ~~~~~~~~~~~~~~~~~~~~~~~*/');
      b.pushAll(literals.vars());
      b.push('/*~~~~~~~~~~~~~~~~~~~~ CHAR CLASSES ~~~~~~~~~~~~~~~~~~~~~*/');
      // Верхняя половина числа -- количество одиночных символов, нижняя -- количество диапазонов.
      b.push('#define MAKE_LENGTHS(_1, _2) (((_1) << (sizeof(((struct CharClass*)0)->counts)*4)) | (_2))');
      b.pushAll(charClasses.vars());
      b.push('#undef MAKE_LENGTHS');
      b.push('/*~~~~~~~~~~~~~~~~ EXPECTED DEFINITIONS ~~~~~~~~~~~~~~~~~*/');
      // Верхние 3 бита числа отводим под тип, остальное -- длина строки.
      b.push('#define MAKE_TYPEANDLEN(type, len) ((type << (sizeof(((struct Expected*)0)->typeAndLen)*8 - 3)) | len)');
      b.pushAll(expected.vars());
      b.push('#undef MAKE_TYPEANDLEN');
      b.push('/*~~~~~~~~~~~~~~ RULE FORWARD DECLARATIONS ~~~~~~~~~~~~~~*/');
      b.pushAll(node.rules.map(function(r) { return rDef(r) + ';'; }));
      b.push('/*~~~~~~~~~~~~~~~~~~~~~~~~ RULES ~~~~~~~~~~~~~~~~~~~~~~~~*/');
      b.pushAll(rules);
      b.push('/*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*/');
      b.indent('PARSER_API struct Result* parse(struct Range* input, struct Range* startRule, void* data) {');
      // Создаем таблицу для поиска правил разбора по имени.
      b.pushAll(createLookupTable(node.rules.map(function(r) { return r.name; })));
      b.push(
        'struct Context ctx = {',
        '  { 0, 0 },',// Range
        '  { 0, 0, 1, 1 },',// Location
        '  { 0, { 0, 0, 1, 1 }, 0, 0 },',// FailInfo
        '  0, 0',// FreeUserDataFunc и data
        '};',
        'ctx.input.begin = input->begin;',
        'ctx.input.end = input->end;',
        'ctx.current.data = input->begin;',
        'ctx.userData = data;',
        'if (startRule) {',
        '  const struct ParseFunc* func = findRule(funcs, sizeof(funcs) / sizeof(funcs[0]), startRule);',
        '  if (func == 0) { return 0; }',
        '  return (*func->func)(&ctx);',
        '}',
        'return ' + (node.rules.length > 0 ? (r(node.rules[0].name) + '(&ctx)') : '0')+ ';'
      );
      b.dedent('}');
      b.push(
        'PARSER_API struct Result* parse2(const char* input, unsigned int len, struct Range* startRule, void* data) {',
        '  struct Range r;',
        '  r.begin = input;',
        '  r.end   = input + len;',
        '  return parse(&r, startRule, data);',
        '}',
        'PARSER_API struct Result* parse3(struct Range* input, const char* startRule, unsigned int len, void* data) {',
        '  if (startRule) {',
        '    struct Range s;',
        '    s.begin = startRule;',
        '    s.end   = startRule + len;',
        '    return parse(input, &s, data);',
        '  }',
        '  return parse(input, 0, data);',
        '}',
        'PARSER_API struct Result* parse4(const char* input, unsigned int inputLen, const char* startRule, unsigned int startRuleLen, void* data) {',
        '  struct Range r;',
        '  r.begin = input;',
        '  r.end   = input + inputLen;',
        '  if (startRule) {',
        '    struct Range s;',
        '    s.begin = startRule;',
        '    s.end   = startRule + startRuleLen;',
        '    return parse(&r, &s, data);',
        '  }',
        '  return parse(&r, 0, data);',
        '}'
      );
      var result = ucb.buildFiles();
      result.push(b.code.join('\n'));
      return result;
    },

    initializer: function(node) {
      ucb.addInitializer(node.namespace, node.code);
    },

    rule: function(node) {
      var code = [
        rDef(node) + ' {',
        '  ',// зарезервировано для переменных из стека результатов
        '  ',// зарезервировано для переменных из стека позиций
        '',
      ];
      var context = makeContext(code);
      context.indent();
      generate(node.expression, context);
      context.dedent(
        '  return ' + context.resultStack.result() + ';',
        '}'
      );
      code[1] += context.resultStack.vars();
      code[2] += context.posStack.vars();
      return code;
    },

    named: function(node, context) {
      var e = expected.add('OTHER', null, node.name);

      context.pushCode('++ctx->failInfo.silent;');
      generate(node.expression, context),
      context.pushCode(
        '--ctx->failInfo.silent;',
        'if (isFailed(' + context.resultStack.top() + ')) {',
        '  ' + context.resultStack.push('fail(ctx, &' + e + ')'),
        '}'
      );
    },

    choice: function(node, context) {
      context.indent('do {/*choice*/');
      node.alternatives.forEach(function(n, i, a) {
        context.pushCode('/*alternative ' + (i+1) + '*/');
        // Для каждой альтернативы набор переменных свой
        generate(n, context.child(context.sp, objects.clone(context.env), null));
        // Если элемент не последний в массиве, то генерируем проверку
        if (i+1 < a.length) {
          context.pushCode('if (!isFailed(' + context.resultStack.pop() + ')) { break; }', '');
        }
      });
      context.dedent('} while (0);/*choice*/');
    },

    sequence: function(node, context) {
      context.pushCode(context.pushPos());
      context.indent('do {/*sequence*/');
      var first;
      node.elements.forEach(function(n, i) {
        context.pushCode('/*element ' + (i+1) + '*/');
        // Для всех элементов последовательности набор переменных одинаковый.
        generate(n, context.child(context.sp + i, context.env, null));
        if (i === 0) {
          first = context.resultStack.top();
        }
        // Если разбор очередного элемента не удался, восстанавливаем позицию
        // и прекращаем анализ прочих элементов последовательности.
        context.pushCode(
          'if (isFailed(' + context.resultStack.top() + ')) {'
        );
        context.pushCode.apply(context,
          context.resultStack.range(context.sp + 1).reverse().map(function(r) { return '  freeResult(' + r + ');'; })
        );
        context.pushCode(
          '  memcpy(&ctx->current, &' + context.posStack.top() + ', sizeof(struct Location));',
          '  ' + first + ' = &FAILED;',
          '  break;',
          '}',
          ''
        );
      });
      var args = context.resultStack.args(context.env);
      var elems = context.resultStack.pop(node.elements.length);
      var beginPos = context.posStack.pop();
      if (context.action) {
        context.pushCode(ucb.addAction(
          context.action.namespace,
          objects.keys(context.env),
          context.action.code,
          args
        ) + ';');
      }/* else */{// TODO: На данный момент изменение возвращаемого значения действиями не поддерживается.
        elems.unshift('ctx', beginPos + '.offset', elems.length);
        context.pushCode(context.resultStack.push('wrap(' + elems.join(', ') + ')')); 
      }
      context.dedent('} while (0);/*sequence*/');
    },

    labeled: function(node, context) {
      context.env[node.label] = context.sp + 1;

      return generate(node.expression, context.child(context.sp, objects.clone(context.env), null));
    },

    text: function(node, context) {
      context.pushCode(context.pushPos());
      // Внутри $ новый scope переменных.
      generate(node.expression, context.child(context.sp + 1, objects.clone(context.env), null));
      context.pushCode(
        'if (!isFailed(' + context.resultStack.pop() + ')) {',
        '  ' + context.resultStack.push('_text(ctx, ' + context.posStack.pop() + ')'),
        '}'
      );
    },

    optional: function(node, context) {
      generate(node.expression, context.child(context.sp, objects.clone(context.env), null));
      context.pushCode(
        'if (isFailed(' + context.resultStack.pop() + ')) { ' + context.resultStack.push('&NIL') + ' }'
      );
    },

    zero_or_more: function(node, context) {
      generateRange(node.expression, context, 0, null);
    },

    one_or_more: function(node, context) {
      generateRange(node.expression, context, 1, null);
    },

    range: function(node, context) {
      generateRange(node.expression, context, node.min, node.max, node.delimiter);
    },

    simple_and: function(node, context) {
      return buildSimplePredicate(node.expression, false, context);
    },

    simple_not: function(node, context) {
      return buildSimplePredicate(node.expression, true, context);
    },

    semantic_and: function(node, context) {
      return generateSemanticPredicate(node.namespace, node.code, false, context);
    },

    semantic_not: function(node, context) {
      return generateSemanticPredicate(node.namespace, node.code, true, context);
    },

    action: function(node, context) {
      var env = objects.clone(context.env);
      // Для того, чтобы не генерировать лишний вызов wrap у последовательности элементов, вызов
      // функции генерируется прямо в последовательности, ВМЕСТО wrap. А это значит, что здесь его
      // генерировать не надо.
      var emitCall = node.expression.type !== "sequence";

      // Если вызов генерируется, нужно сохранить позицию перед выполнением пользовательского кода,
      // чтобы он имел к ней доступ.
      if (emitCall) {
        context.pushCode(context.pushPos());
      }
      generate(node.expression, context.child(context.sp, env, node));
      if (emitCall) {
        var params = objects.keys(env);
        var args = context.resultStack.args(env);
        context.pushCode(
          'if (!isFailed(' + context.resultStack.top() + ')) {',
          '  ' + ucb.addAction(node.namespace, params, node.code, args) + ';',
          '}'
        );
        context.popPos();
      }
    },

    rule_ref: function(node, context) {
      // Помещаем результат разбора правила на вершину стека результатов.
      context.pushCode(context.resultStack.push(r(node.name) + '(ctx)'));
    },

    literal: function(node, context) {
      if (node.ignoreCase) {
        emitWarning("Case insensitive matching not supported", node.value, node.region);
      }
      if (/[^\x00-\xFF]/g.test(node.value)) {
        emitWarning("Unicode symbols not supported", node.value, node.region);
      }
      var v = literals.add(node.value);
      var e = expected.add(
        'LITERAL',
        node.ignoreCase ? node.value.toLowerCase() : node.value,
        '"' + escape(node.value) + '"'
      );
      // Помещаем результат разбора класса символов на вершину стека результатов.
      context.pushCode(context.resultStack.push('parseLiteral(ctx, &' + v + ', &' + e + ')'));
    },

    "class": function(node, context) {
      if (node.ignoreCase) {
        emitWarning("Case insensitive matching not supported", node.rawText, node.region);
      }
      var v = charClasses.add(node.parts);
      var e = expected.add('CLASS', node.rawText, node.rawText);
      // Помещаем результат разбора класса символов на вершину стека результатов.
      context.pushCode(context.resultStack.push(
        'parseCharClass(ctx, &' + v + ', &' + e + ', ' + (node.inverted ? '1' : '0')+ ')'
      ));
    },

    any: function(node, context) {
      // Помещаем результат разбора any на вершину стека результатов.
      context.pushCode(context.resultStack.push('parseAny(ctx)'));
    }
  });

  ast.files = generate(ast);
  return ast.files;
}

module.exports = generateCCode;
