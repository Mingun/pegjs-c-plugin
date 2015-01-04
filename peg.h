/** @file С89-совместимый заголовочный файл для генератора парсеров.
    `gcc -pedantic -ansi -std=c89` не должен выдавать никаких предупреждений.
*/

/* Для memcmp. */
#include <string.h>
/* Для malloc/calloc/free/bsearch. */
#include <stdlib.h>
/* Для va_*, используемых в функции wrap. */
#include <stdarg.h>
#include <assert.h>

#ifndef PARSER_API
#  define PARSER_API
#endif
#ifndef INTERNAL
#  define INTERNAL
#endif

#if !__cplusplus
#  define true 1
#  define false 0
#endif

/*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*/
/* Структуры парсера. */
/*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*/
/** Диапазон символов. */
struct Range {
  const char* begin;
  const char* end;
};
struct Result {
  /** Границы данного узла во входном потоке. */
  struct Range range;
  /** Количество потомков данного узла. */
  unsigned int count;
  /** Указатель на потомков данного узла. */
  struct Result** childs;
};
/** Содержит позицию в разбираемых данных, как в виде смещения в байтах от начала строки,
    так и в виде номеров строки и столбца.
*/
struct Pos {
  /** Смещение в байтах от начала разбираемых данных, нумерация с 0. */
  unsigned int offset;
  /** Номер строки в разбираемых данных, нумерация с 1. Новая строка начинается после символа
      '\r', '\n' или пары символов '\r\n'.
  */
  unsigned int line;
  /** Номер столбца в строке разбираемых данных, нумерация с 1. */
  unsigned int column;
};
enum E_EXPECTED_TYPE {
  /** Ожидается любой символ. */
  E_EX_TYPE_ANY,
  /** Ожидается класс символов. */
  E_EX_TYPE_CLASS,
  /** Ожидается указанная последовательность символов. */
  E_EX_TYPE_LITERAL,
  /** Ожидается окончание потока данных. */
  E_EX_TYPE_EOF,
  /** Пользовательское сообщение об ожидаемых данных. */
  E_EX_TYPE_USER
};
struct Expected {
  enum E_EXPECTED_TYPE type;
  const char* message;
};
struct FailInfo {
  unsigned int silent;
  /** Позиция, в которой необходимо сообщить о невозможности разбора. */
  struct Pos pos;
  /** Количество элементов Expected в массиве expected. */
  unsigned int count;
  /** Массив возможных ожидаемых значений в позиции failPos. */
  const struct Expected** expected;
};
struct Context {
  /** Разбираемые данные. */
  struct Range input;
  /** Текущая позиция в разбираемых данных. */
  struct Pos current;
  /** Информация об ошибках разбора. */
  struct FailInfo failInfo;
  /** Информация, передаваемая пользователем в парсер. Парсером не используется. */
  void* options;
};
struct Literal {
  /** Длина литерала (массива data). */
  unsigned int len;
  /** Массив символов литерала. */
  const char* data;
  /** Сообщение об ожидаемом элементе, если сопоставление с литералом пройдет неудачно. */
  /*struct Expected expected;*/
};
struct CharClass {
  /** Старшая половина -- количество элементов в массиве single, младшая -- количество пар
      в массиве range.
  */
  unsigned int counts;
  /** Массив одиночных символов, включенный в данный набор. */
  const char* single;
  /** Массив пар символов (т.е. длина массива всегда четная), представляющих в данном наборе
      поддиапазоны от первого до посленего символа (обе границы включительно).
  */
  const char* range;
  /** Сообщение об ожидаемом элементе, если сопоставление с классом символов пройдет неудачно. */
  /*struct Expected expected;*/
};
/*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*/
/* Вспомогательные структуры. */
/*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*/
typedef struct Result* ResultPtr;
typedef struct Result* (*RuleFunc)(struct Context*);
struct ParseFunc {
  /** Длина имени функции для разбора правила. */
  unsigned int len;
  /** Имя функции для разбора правила. */
  const char* name;
  /** Функция для разбора правила. */
  RuleFunc func;
};
static struct Result FAILED = {{0, 0}, 0, 0};
static struct Result NIL    = {{0, 0}, 0, 0};

/*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*/
/* Процедуры сопоставления. */
/*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*/
int matchLiteral(struct Context* context, const struct Literal* literal) {
  const char* begin;
  unsigned int inputLen;
  begin = context->input.begin + context->current.offset;
  inputLen = context->input.end - begin;
  /* Если входная строка короче, то она точно не равна литералу. */
  return inputLen < literal->len ? 0 : memcmp(begin, literal->data, literal->len) == 0;
}
/**
@param context Информация о разбираемом участке и текущей в нем позиции.
@param ranges Массив из @a count описателей диапазонов символов/списков символов.
@param count Количество элементов в массиве @a ranges.
*/
int matchCharClass(struct Context* context, struct CharClass* cls) {
  const char* begin;
  assert(context);
  assert(context->input.begin);
  assert(cls);
  assert(cls->single);
  assert(cls->range);

  begin = context->input.begin + context->current.offset;

  /* Если мы еще не в конце входных данных, то пытаемся сматчить текущий символ. */
  if (begin < context->input.end) {
    /* Выделяем нижнюю половину бит числа с помощью  маски. Верхнюю половину получаем, просто
    отодвинув ненужную нижнюю половину. */
    unsigned int countLO;
    unsigned int countHI;
    char ch;
    unsigned int i;

    countLO = cls->counts & ((~0u) >> (sizeof(cls->counts)*4));
    countHI = cls->counts >> (sizeof(cls->counts)*4);
    ch = begin[0];
    /* Класс символов является списком пар, задающих диапазоны символов. */
    for (i = 0; i < countLO; ++i) {
      char b;
      char e;

      b = cls->range[i*2];
      e = cls->range[i*2 + 1];
      /* Строгая проверка, т.к. если начало и конец совпадают, то это единственный символ
      и он должен быть в cls->single. */
      assert(b < e);
      if (b <= ch && ch <= e) {
        /* Текущий символ принадлежит диапазону символов. */
        return 1;
      }
    }
    /* Класс символов является просто списком символов, которые нужно проверить. */
    if (memchr(cls->single, ch, countHI) != 0) {
      /* Если текущий символ строки имеется в списке допустимых символов, сопоставление успешно. */
      return 1;
    }
  }
  return 0;
}
/*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*/
/* Работа с памятью. */
/*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*/
struct Result* allocResult(const char* begin, const char* end, unsigned int count) {
  struct Result* r = (struct Result*)malloc(sizeof(struct Result));
  assert(begin);
  assert(end);
  assert(r);
  r->range.begin = begin;
  r->range.end   = end;
  r->count = count;
  r->childs = count == 0 ? 0 : calloc(count, sizeof(struct Result));
  return r;
}
void freeResult(struct Result* result) {
  if (result == &FAILED || result == &NIL) {
    return;
  }
  /* Если есть потомки, чистим сначала их, а затем и массив, их хранящий. */
  if (result && result->childs != 0) {
    unsigned int i;
    /* Если есть потомки, их количество должно быть задано. */
    assert(result->count);
    for (i = 0; i < result->count; ++i) {
      freeResult(result->childs[i]);
    }
    free(result->childs);
  }
  free(result);
}
/*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*/
/* Работа с ожидаемыми элементами. */
/*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*/
void clonePos(struct Pos* dest, const struct Pos* src) {
  dest->offset = src->offset;
  dest->line   = src->line;
  dest->column = src->column;
}
void clearExpected(struct FailInfo* info) {
  free(info->expected);
  info->count = 0;
  info->expected = 0;
}
void pushExpected(struct FailInfo* info, struct Expected* expected) {
  unsigned int count = ++info->count;
  info->expected = (const struct Expected**)realloc(info->expected, count * sizeof(*info->expected));
  info->expected[count-1] = expected;
}
struct Result* fail(struct Context* context, struct Expected* expected) {
  assert(context);
  assert(expected);
  if (context->failInfo.silent == 0) {
    if (context->current.offset < context->failInfo.pos.offset) { return &FAILED; }

    if (context->current.offset > context->failInfo.pos.offset) {
      clonePos(&context->failInfo.pos, &context->current);
      clearExpected(&context->failInfo);
    }

    pushExpected(&context->failInfo, expected);
  }
  return &FAILED;
}
/*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*/
/* Работа с позицией. */
/*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*/
void movePos(struct Context* context, unsigned int count) {
  context->current.offset += count;
  
  /*TODO: Скорректировать line и column*/
}
/*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*/
/* Правила разбора примитивов. */
/*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*/
/** Если в разбираемых данных еще не достигнут конец, продвигает текущую позицию на один символ
    вперед и возвращает результат с границами от текущей позиции до текущей позиции плюс 1.
    В случае неудачи позиция остается неизменной и возвращается константа FAILED.

@param context Информация о разбираемом участке и текущей в нем позиции.

@return Результат разбора или константу FAILED, если разбор неудачен. Результат необходимо
        освободить функцией freeResult, когда он больше не будет нужен.
*/
struct Result* parseAny(struct Context* context) {
  static struct Expected expected = {
    E_EX_TYPE_ANY,
    "any character"
  };
  const char* begin = context->input.begin + context->current.offset;

  if (begin < context->input.end) {
    movePos(context, 1);
    return allocResult(begin, begin + 1, 0);
  } else {
    return fail(context, &expected);
  }
}
/** Если указанная строка @a literal является подстрокой разбираемых данных, начиная с текущей
    позиции разбора, то продвигает текущую позицию на величину @a len и возвращает результат с
    границами от текущей позиции до текущей позиции плюс @a len.
    В случае неудачи позиция остается неизменной и возвращается константа FAILED.

@param context Информация о разбираемом участке и текущей в нем позиции.
@param literal Литерал, с которым осуществляется сопоставление разбираемых данных.

@return Результат разбора или константу FAILED, если разбор неудачен. Результат необходимо
        освободить функцией freeResult, когда он больше не будет нужен.
*/
struct Result* parseLiteral(struct Context* context, struct Literal* literal, struct Expected* expected) {
  assert(context);
  assert(literal);
  assert(expected);
  if (matchLiteral(context, literal)) {
    const char* begin = context->input.begin + context->current.offset;
    movePos(context, literal->len);
    return allocResult(begin, begin + literal->len, 0);
  } else {
    return fail(context, expected);
  }
}
struct Result* parseCharClass(struct Context* context, struct CharClass* cls, struct Expected* expected) {
  assert(context);
  assert(cls);
  assert(expected);
  if (matchCharClass(context, cls)) {
    const char* begin = context->input.begin + context->current.offset;
    movePos(context, 1);
    return allocResult(begin, begin + 1, 0);
  } else {
    return fail(context, expected);
  }
}
/*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*/
struct Result* wrap(struct Context* context, unsigned int pos, unsigned int count, ...) {
  struct Result* r;
  unsigned int i;

  va_list results;
  va_start(results, count);

  r = allocResult(context->input.begin + pos, context->input.begin + context->current.offset, count);
  for (i = 0; i < count; ++i) {
    assert(r->childs);
    r->childs[i] = va_arg(results, struct Result*);
    assert(r->childs[i]);
  }

  va_end(results);
  return r;
}
static int findRuleCompatator(const struct Range* name, const struct ParseFunc* entry) {
  unsigned int len;
  assert(name);
  assert(name->begin);
  assert(name->end);
  assert(entry);
  len = name->end - name->begin;
  if (len < entry->len) { return -1; }
  if (len > entry->len) { return +1; }
  return memcmp(name->begin, entry->name, len);
}
const struct ParseFunc* findRule(const struct ParseFunc* table, size_t count, const struct Range* name) {
  typedef int (*Comparator)(const void*, const void*);
  assert(table);
  assert(name);
  return (const struct ParseFunc*)bsearch(
    name, table, count, sizeof(table[0]),
    (Comparator)&findRuleCompatator
  );
}