/* lisp-cheney.c Lisp with Cheney's copying GC and NaN boxing by Robert A. van Engelen 2022
        - double precision floating point, symbols, strings, lists, proper closures, and macros
        - over 40 built-in Lisp primitives
        - lexically-scoped locals in lambda, let, let*, letrec, letrec*
        - proper tail-recursion, including tail calls through begin, cond, if, let, let*, letrec, letrec*
        - exceptions and error handling with safe return to REPL after an error
        - break with CTRL-C to return to the REPL (compile: lisp.c -DHAVE_SIGNAL_H)
        - REPL with readline (compile: lisp-cheney.c -DHAVE_READLINE_H -lreadline)
        - load Lisp source code files
        - execution tracing to display Lisp evaluation steps
        - Cheney's compacting garbage collector to recycle unused cons pair cells, atoms and strings */

#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>             /* int64_t, uint64_t (or we can use e.g. unsigned long long instead) */
#include <stdarg.h>
#include <string.h>
#include <setjmp.h>

#ifdef HAVE_SIGNAL_H
#include <signal.h>             /* to catch CTRL-C and continue the REPL */
#define BREAK_ON  signal(SIGINT, (void(*)(int))err)
#define BREAK_OFF signal(SIGINT, SIG_IGN)
#else
#define BREAK_ON  (void)0
#define BREAK_OFF (void)0
#endif

#ifdef HAVE_READLINE_H
#include <readline/readline.h>  /* for convenient line editing ... */
#include <readline/history.h>   /* ... and a history of previous Lisp input */
#else
void using_history() { }
#endif

/* floating point output format */
#define FLOAT "%.17lg"

/* DEBUG: always run GC when allocating cells and atoms/strings on the heap */
#ifdef DEBUG
#define ALWAYS_GC 1
#else
#define ALWAYS_GC 0
#endif

/*----------------------------------------------------------------------------*\
 |      LISP EXPRESSION TYPES AND NAN BOXING                                  |
\*----------------------------------------------------------------------------*/

/* we only need three types to implement a Lisp interpreter with a copying garbage collector:
        L      Lisp expression (a double with NaN boxing)
        I      integer (a 64 bit unsigned integer)
        S      size of an atom string on the heap and atom forwarding index when negative
   L variables and function parameters are named as follows:
        x,y    any Lisp expression
        n      number
        t,s    list
        f      function or Lisp primitive
        p      pair, a cons of two Lisp expressions
        e,d    environment, a list of pairs, e.g. created with (define v x)
        v      the name of a variable (an atom) or a list of variables
   I variables and function parameters are named as follows:
        i,j,k  any unsigned integer, e.g. a NaN-boxed ordinal value
        t      a NaN-boxing tag
   S variables are named as follows:
        n      string length or negative forwarding index of an ATOM/STRG */
typedef double   L;                             /* Lisp expression type: NaN-boxed 64 bit double floating point */
typedef uint64_t I;                             /* unsigned 64 bit integer of a NaN-boxed double */
typedef int      S;                             /* signed size of an atom string on the heap, negative for forwarding */
typedef L       *P;                             /* pointer to a root variable with a value that is updated by GC */

/* T(x) returns the tag bits of a NaN-boxed Lisp expression x */
#define T(x) (*(I*)&x >> 48)

/* primitive, atom, string, cons, closure, macro, GC forward, GC var pointer and nil tags (reserve 0x7ff8 for nan) */
I PRIM=0x7ff9, ATOM=0x7ffa, STRG=0x7ffb, CONS=0x7ffc, CLOS=0x7ffe, MACR=0x7fff, FORW=0xfffd, VARP=0xfffe, NIL=0xffff;

/* NaN-boxing specific functions */
L box(I t, I i) { i |= t<<48; return *(P)&i; }          /* return NaN-boxed double with tag t and 48 bit ordinal i */
I ord(L x)      { return *(I*)&x & 0xffffffffffff; }    /* remove tag bits to return the 48 bit ordinal */ 
L num(L n)      { return n; }                           /* check for a valid number: return n == n ? n : err(5); */
I equ(L x, L y) { return *(I*)&x == *(I*)&y; }          /* return nonzero if x equals y */

/*----------------------------------------------------------------------------*\
 |      ERROR HANDLING AND ERROR MESSAGES                                     |
\*----------------------------------------------------------------------------*/

/* state of the setjump-longjmp exception handler with jump buffer jb and number of active root variables n */
struct State {
  jmp_buf jb;
  int n;
} state;

/* report and throw an exception */
#define ERR(n, ...) (fprintf(stderr, __VA_ARGS__), err(n))
L err(int n) { longjmp(state.jb, n); }

#define ERRORS 8
const char *errors[ERRORS+1] = {
  "",
  "not a pair",                                 /* 1 */
  "break",                                      /* 2 */
  "unbound symbol",                             /* 3 */
  "cannot apply",                               /* 4 */
  "arguments",                                  /* 5 */
  "stack over",                                 /* 6 */
  "out of memory",                              /* 7 */
  "syntax"                                      /* 8 */
};

/*----------------------------------------------------------------------------*\
 |      MEMORY MANAGEMENT AND RECYCLING                                       |
\*----------------------------------------------------------------------------*/

#define A (char*)cell                           /* address of the atom heap */
#define B (char*)from                           /* address of the atom "from" heap during garbage collection */
#define W sizeof(S)                             /* width of the size field of an atom string on the heap, in bytes */
#define N 8192                                  /* heap size */

/* hp: heap pointer, A+hp with hp=0 points to the first atom string in heap[]
   sp: stack pointer, the stack starts at the top of the primary heap cell[] with sp=N
   tr: 0 when tracing is off, 1 or 2 to trace Lisp evaluation steps */
I hp = 0, sp = N, tr = 0;

/* we use two heaps: a primary heap cell[] and a secondary heap for the copying garbage collector */
L heap[2][N], *cell = heap[0], *from;

/* the roots of the garbage collector is a Lisp list of VARP pointers to global and local variables */
L vars;

/* Lisp constant expressions () (nil), #t and the global environment env */
L nil, tru, env;

/* move ATOM/STRG/CONS/CLOS/MACR/VARP x from the 1st to the 2nd heap or use its forwarding index, return updated x */
L move(L x) {
  I t = T(x), i = ord(x);                       /* save the tag and ordinal of x */
  if (t == VARP) {                              /* if x is a VARP */
    *(P)i = move(*(P)i);                        /*   update the variable by moving its value to the "to" heap */
    return x;                                   /*   return VARP x */
  }
  if ((t & ~(ATOM^STRG)) == ATOM) {             /* if x is an ATOM or a STRG */
    I j = i-W;                                  /*   j is the index of the size field located before the string */
    S n = *(S*)(B+j);                           /*   get size n of the string at the "from" heap to move */
    if (n < 0)                                  /*   if the size is negative, it is a forwarding index */
      return box(t, -n);                        /*     return ATOM with forwarded index to the location on "to" heap */
    memcpy(A+hp, B+j, W+n);                     /*   move the size field and string from the "from" to the "to" heap */
    *(S*)(B+j) = -(S)(W+hp);                    /*   leave a negative forwarding index on the "from" heap */
    hp += W+n;                                  /*   increment heap pointer by the number of allocated bytes */
    return box(t, hp-n);                        /*   return ATOM/STRG with index of the string on the "to" heap */
  }
  if ((t & ~(CONS^MACR)) != CONS)               /* if x is not a CONS/CLOS/MACR pair */
    return x;                                   /*   return x */
  if (T(from[i]) == FORW)                       /* if x is a CONS/CLOS/MACR with forwarding index on the "from" heap */
    return box(t, ord(from[i]));                /*   return x with updated index pointing to "to" heap */
  cell[--sp] = from[i+1];                       /* move CONS/CLOS/MACR pair from the "from" to the "to" heap */
  cell[--sp] = from[i];
  from[i] = box(FORW, sp);                      /* leave a forwarding index on the "from" heap */
  return box(t, sp);                            /* return CONS/CLOS/MACR with index to the location on the "to" heap */
}

/* garbage collect with root p, returns (moved) p; p=1 forces garbage collection */
L gc(L p) {
  if (hp > (sp-2)<<3 || equ(p, 1) || ALWAYS_GC) {
    BREAK_OFF;                                  /* do not interrupt GC */
    I i = N;                                    /* scan pointer starts at the top of the 2nd heap */
    hp = 0;                                     /* heap pointer starts at the bottom of the 2nd heap */
    sp = N;                                     /* stack pointer starts at the top of the 2nd heap */
    from = cell;                                /* move cells from the original 1st "from" heap cell[] */
    cell = heap[cell == heap[0]];               /* ... to the 2nd heap, which becomes the 1st "to" heap cell[] */
    vars = move(vars);                          /* move the roots */
    p = move(p);                                /* move p */
    while (--i >= sp)                           /* while the scan pointer did not pass the stack pointer */
      cell[i] = move(cell[i]);                  /*   move the cell from the "from" heap to the "to" heap */
    BREAK_ON;                                   /* enable interrupt */
    if (hp > (sp-2)<<3)                         /* if the heap is still full after garbage collection */
      err(7);                                   /*   we ran out of memory */
  }
  return p;
}

/*----------------------------------------------------------------------------*\
 |      LISP EXPRESSION CONSTRUCTION AND INSPECTION                           |
\*----------------------------------------------------------------------------*/

/* allocate n bytes on the heap, returns NaN-boxed t=ATOM or t=STRG */
L alloc(I t, S n) {
  L x = box(t, W+hp);                           /* NaN-boxed ATOM or STRG points to bytes after the size field W */
  *(S*)(A+hp) = n;                              /* save size n field in front of the to-be-saved string on the heap */
  *(A+W+hp) = 0;                                /* make string empty, just in case */
  hp += W+n;                                    /* try to allocate W+n bytes on the heap */
  return gc(x);                                 /* check if space is allocatable, GC if necessary, returns updated x */
}

/* copy string s to the heap, returns NaN-boxed t=ATOM or t=STRG */
L dup(I t, const char *s) {
  S n = strlen(s)+1;                            /* size of n bytes to allocate, to save the atom string */
  L x = alloc(t, n);
  memcpy(A+ord(x), s, n);                       /* save the atom string after the size field on the heap */
  return x;
}

/* interning of atom names (Lisp symbols), returns a unique NaN-boxed ATOM */
L atom(const char *s) {
  I i = 0;
  while (i < hp && strcmp(A+W+i, s))            /* search for a matching atom name on the heap */
    i += W+*(S*)(A+i);
  return i < hp ? box(ATOM, W+i) : dup(ATOM, s);/* if found then return ATOM else copy string to the heap */
}

/* store string s on the heap, returns a NaN-boxed STRG with heap offset */
L string(const char *s) {
  return dup(STRG, s);                          /* copy string+\0 to the heap, return NaN-boxed STRG */
}

/* construct pair (x . y) returns a NaN-boxed CONS */
L cons(L x, L y) {
  cell[--sp] = x;                               /* push the car value x, this protects x from getting GC'ed */
  cell[--sp] = y;                               /* push the cdr value y, this protects y from getting GC'ed */
  return gc(box(CONS, sp));                     /* make sure we have enough space for the (next) new cons pair */
}

/* return the car of a pair or ERR if not a pair */
#define CAR(p) cell[ord(p)+1]
L car(L p) {
  return (T(p)&~(CONS^MACR)) == CONS ? CAR(p) : err(1);
}

/* return the cdr of a pair or ERR if not a pair */
#define CDR(p) cell[ord(p)]
L cdr(L p) {
  return (T(p)&~(CONS^MACR)) == CONS ? CDR(p) : err(1);
}

/* construct a pair to add to environment *e, returns the list ((v . x) . *e) */
L pair(L v, L x, P e) {
  L p = cons(v, x);                             /* construct the pair (v . x) first, may trigger GC */
  return cons(p, *e);                           /* construct the list ((v . x) . *e) with a GC-updated *e */
}

/* construct a closure, returns a NaN-boxed CLOS */
L closure(L v, L x, P e) {
  return box(CLOS, ord(pair(v, x, equ(*e, env) ? &nil : e)));
}

/* construct a macro, returns a NaN-boxed MACR */
L macro(L v, L x) {
  return box(MACR, ord(cons(v, x)));
}

/* look up a symbol in an environment, return its value or ERR if not found */
L assoc(L v, L e) {
  while (T(e) == CONS && !equ(v, car(car(e))))
    e = cdr(e);
  return T(e) == CONS ? cdr(car(e)) : T(v) == ATOM ? ERR(3, "unbound %s ", A+ord(v)) : err(3);
}

/* not(x) is nonzero if x is the Lisp () empty list */
int not(L x) {
  return T(x) == NIL;
}

/* more(x) is nonzero if x is not an () empty list and not a singleton list (x) */
int more(L x) {
  return T(x) != NIL && (x = cdr(x), T(x) != NIL);
}

/* register n variables as roots for garbage collection, all but the first should be nil */
void var(int n, ...) {
  va_list v;
  for (va_start(v, n); n--; ++state.n)
    vars = cons(box(VARP, (I)va_arg(v, P)), vars);
  va_end(v);
}

/* release n registered variables */
void unwind(int n) {
  state.n -= n;
  while (n--)
    vars = cdr(vars);
}

/* release n registered variables and return x */
L ret(int n, L x) {
  unwind(n);
  return x;
}

L eval(L, P), parse();
void print(L);

/*----------------------------------------------------------------------------*\
 |      READ                                                                  |
\*----------------------------------------------------------------------------*/

/* the file(s) we are reading or fin=0 when reading from the terminal */
I fin = 0;
FILE *in[10];

/* specify an input file to parse and try to open it */
FILE *input(const char *s) {
  return fin <= 9 && (in[fin] = fopen(s, "r")) ? in[fin++] : NULL;
}

/* tokenization buffer, the next character we're looking at, the readline line, prompt and input file */
char buf[256], see = '\n', *ptr = "", *line = NULL, ps[20];

/* advance to the next character */
void look() {
  int c;
  while (fin) {                                 /* if reading from a file */
    see = c = getc(in[fin-1]);                  /* read a character */
    if (c != EOF)
      return;
    fclose(in[--fin]);                          /* if end of file, then close the file and read previous open file */
    see = '\n';                                 /* pretend we see a newline at eof */
  }
#ifdef HAVE_READLINE_H
  if (see == '\n') {                            /* if looking at the end of the current readline line */
    BREAK_OFF;                                  /* disable interrupt to prevent free() without final line = NULL */
    if (line)                                   /* free the old line that was malloc'ed by readline */
      free(line);
    line = NULL;
    BREAK_ON;                                   /* enable interrupt */
    while (!(ptr = line = readline(ps)))        /* read new line and set ptr to start of the line */
      freopen("/dev/tty", "r", stdin);          /* try again when line is NULL after EOF by CTRL-D */
    add_history(line);                          /* make it part of the history */
    strcpy(ps, "?");                            /* change prompt to ? */
  }
  if (!(see = *ptr++))
    see = '\n';
#else
  if (see == '\n') {
    printf("%s", ps);
    strcpy(ps, "?");
  }
  if ((c = getchar()) == EOF) {
    freopen("/dev/tty", "r", stdin);
    c = '\n';
  }
  see = c;
#endif
}

/* return nonzero if we are looking at character c, ' ' means any white space */
I seeing(char c) {
  return c == ' ' ? see > 0 && see <= c : see == c;
}

/* return the look ahead character from standard input, advance to the next */
char get() {
  char c = see;
  look();
  return c;
}

/* tokenize into buf[], return first character of buf[] */
char scan() {
  int i = 0;
  while (seeing(' ') || seeing(';'))            /* skip white space and ;-comments */
    if (get() == ';')
      while (!seeing('\n'))                     /* skip ;-comment until newline */
        look();
  if (seeing('"')) {                            /* tokenize a quoted string */
    do {
      buf[i++] = get();
      while (seeing('\\') && i < sizeof(buf)-1) {
        static const char *abtnvfr = "abtnvfr"; /* \a, \b, \t, \n, \v, \f, \r escape codes */
        const char *esc;
        get();
        esc = strchr(abtnvfr, see);
        buf[i++] = esc ? esc-abtnvfr+7 : see;   /* replace \x with an escaped code or x itself */
        get();
      }
    }
    while (i < sizeof(buf)-1 && !seeing('"') && !seeing('\n'));
    if (get() != '"')
      ERR(8, "missing \" ");
  }
  else if (seeing('(') || seeing(')') || seeing('\''))
    buf[i++] = get();                           /* ( ) ' are single-character tokens */
  else                                          /* tokenize a symbol or a number */
    do
      buf[i++] = get();
    while (i < sizeof(buf)-1 && !seeing('(') && !seeing(')') && !seeing(' '));
  buf[i] = 0;
  return *buf;                                  /* return first character of token in buf[] */
}

/* return the Lisp expression parsed and read from input */
L readlisp() {
  scan();
  return parse();
}

/* return a parsed Lisp list */
L list() {
  L t = nil, p = nil, x;
  var(2, &t, &p);
  while (1) {
    if (scan() == ')')
      break;
    if (*buf == '.' && !buf[1]) {
      x = readlisp();
      if (scan() != ')')
        ERR(8, "expecing ) ");
      *(T(p) == CONS ? &CDR(p) : &t) = x;
      break;
    }
    x = cons(parse(), nil);
    p = *(T(p) == CONS ? &CDR(p) : &t) = x;
  }
  return ret(2, t);
}

/* return a parsed Lisp expression */
L parse() {
  L x;
  int i;
  if (*buf == '(')
    return list();
  if (*buf == '\'') {
    L y = cons(readlisp(), nil);
    var(1, &y);
    x = atom("quote");
    return ret(1, cons(x, y));
  }
  if (*buf == '"')                              /* if token is a string, then return a new string */
    return string(buf+1);
  if (sscanf(buf, "%lg%n", &x, &i) > 0 && !buf[i])
    return x;                                   /* return a number, including inf, -inf and nan */
  if (*buf != ')')
    return atom(buf);                           /* return an atom (a symbol) */
  return ERR(8, "unexpected ) ");
}

/*----------------------------------------------------------------------------*\
 |      PRIMITIVES -- SEE THE TABLE WITH COMMENTS FOR DETAILS                 |
\*----------------------------------------------------------------------------*/

/* the file we are writing to, stdout by default */
FILE *out;

/* construct a new list of evaluated expressions in list t, i.e. the arguments passed to a function or primitive */
L evlis(P t, P e) {
  L s = nil, p = nil;                           /* new list s = nil with tail pair p = nil */
  var(2, &s, &p);                               /* register s and p for GC updates */
  for (; T(*t) == CONS; *t = cdr(*t)) {         /* iterate over the list of arguments */
    L x = cons(eval(car(*t), e), nil);          /* evaluate argument */
    p = *(T(p) == CONS ? &CDR(p) : &s) = x;     /* build the evaluated list s */
  }
  if (T(*t) != NIL) {                           /* dot list arguments? */
    L x = eval(*t, e);                          /* evaluate the dotted argument */
    *(T(p) == CONS ? &CDR(p) : &s) = x;         /* build the evaluated list s */
  }
  return ret(2, s);                             /* return the list s of evaluated arguments */
}

L f_type(P t, P e) {
  L x = car(evlis(t, e));
  return T(x) == NIL ? -1.0 : T(x) >= PRIM && T(x) <= MACR ? T(x) - PRIM + 1 : 0.0;
}

L f_eval(P t, P e) {
  return car(evlis(t, e));
}

L f_quote(P t, P _) {
  return car(*t);
}

L f_cons(P t, P e) {
  L s = evlis(t, e);
  return cons(car(s), car(cdr(s)));
}

L f_car(P t, P e) {
  return car(car(evlis(t, e)));
}

L f_cdr(P t, P e) {
  return cdr(car(evlis(t, e)));
}

L f_add(P t, P e) {
  L s = evlis(t, e), n = car(s);
  while (!not(s = cdr(s)))
    n += car(s);
  return num(n);
}

L f_sub(P t, P e) {
  L s = evlis(t, e), n = not(cdr(s)) ? -car(s) : car(s);
  while (!not(s = cdr(s)))
    n -= car(s);
  return num(n);
}

L f_mul(P t, P e) {
  L s = evlis(t, e), n = car(s);
  while (!not(s = cdr(s)))
    n *= car(s);
  return num(n);
}

L f_div(P t, P e) {
  L s = evlis(t, e), n = not(cdr(s)) ? 1.0/car(s) : car(s);
  while (!not(s = cdr(s)))
    n /= car(s);
  return num(n);
}

L f_int(P t, P e) {
  L n = car(evlis(t, e));
  return n < 1e16 && n > -1e16 ? (int64_t)n : n;
}

L f_lt(P t, P e) {
  L s = evlis(t, e), x = car(s), y = car(cdr(s));
  return (T(x) == T(y) && (T(x) & ~(ATOM^STRG)) == ATOM ? strcmp(A+ord(x), A+ord(y)) < 0 :
      x == x && y == y ? x < y :
      T(x) < T(y)) ? tru : nil;
}

L f_eq(P t, P e) {
  L s = evlis(t, e), x = car(s), y = car(cdr(s));
  return (T(x) == STRG && T(y) == STRG ? !strcmp(A+ord(x), A+ord(y)) : equ(x, y)) ? tru : nil;
}

L f_not(P t, P e) {
  return not(car(evlis(t, e))) ? tru : nil;
}

L f_or(P t, P e) {
  L x = nil;
  while (T(*t) != NIL && not(x = eval(car(*t), e)))
    *t = cdr(*t);
  return x;
}

L f_and(P t, P e) {
  L x = nil;
  while (T(*t) != NIL && !not(x = eval(car(*t), e)))
    *t = cdr(*t);
  return x;
}

L f_begin(P t, P e) {
  for (; more(*t); *t = cdr(*t))
    eval(car(*t), e);
  return T(*t) == NIL ? nil : car(*t);
}

L f_while(P t, P e) {
  L s = nil, x = nil;
  var(2, &s, &x);
  while (!not(eval(car(*t), e)))
    for (s = cdr(*t); T(s) != NIL; s = cdr(s))
      x = eval(car(s), e);
  return ret(2, x);
}

L f_cond(P t, P e) {
  while (T(*t) != NIL && not(eval(car(car(*t)), e)))
    *t = cdr(*t);
  if (T(*t) != NIL)
    *t = cdr(car(*t));
  return f_begin(t, e);
}

L f_if(P t, P e) {
  return not(eval(car(*t), e)) ? (*t = cdr(cdr(*t)), f_begin(t, e)) : car(cdr(*t));
}

L f_lambda(P t, P e) {
  return closure(car(*t), car(cdr(*t)), e);
}

L f_macro(P t, P e) {
  return macro(car(*t), car(cdr(*t)));
}

L f_define(P t, P e) {
  L x = eval(car(cdr(*t)), e);
  env = pair(car(*t), x, &env);
  return car(*t);
}

L f_assoc(P t, P e) {
  L s = evlis(t, e);
  return assoc(car(s), car(cdr(s)));
}

L f_env(P _, P e) {
  return *e;
}

L f_let(P t, P e) {
  L d = *e, x = nil;
  var(2, &d, &x);
  for (; more(*t); *t = cdr(*t)) {
    x = cdr(car(*t));
    x = eval(f_begin(&x, e), &d);
    *e = pair(car(car(*t)), x, e);
  }
  return ret(2, car(*t));
}

L f_leta(P t, P e) {
  L s = nil, x;
  var(1, &s);
  for (; more(*t); *t = cdr(*t)) {
    s = cdr(car(*t));
    x = eval(f_begin(&s, e), e);
    *e = pair(car(car(*t)), x, e);
  }
  return ret(1, car(*t));
}

L f_letrec(P t, P e) {
  L s = nil, x = nil;
  var(2, &s, &x);
  for (s = *t; more(s); s = cdr(s))
    *e = pair(car(car(s)), nil, e);
  for (s = *e; more(*t); s = cdr(s), *t = cdr(*t)) {
    x = cdr(car(*t));
    x = eval(f_begin(&x, e), e);
    CDR(car(s)) = x;
  }
  return ret(2, T(*t) == NIL ? nil : car(*t));
}

L f_letreca(P t, P e) {
  L s = nil, x;
  var(1, &s);
  for (; more(*t); *t = cdr(*t)) {
    *e = pair(car(car(*t)), nil, e);
    s = cdr(car(*t));
    x = eval(f_begin(&s, e), e);
    CDR(car(*e)) = x;
  }
  return ret(1, T(*t) == NIL ? nil : car(*t));
}

L f_setq(P t, P e) {
  L x = eval(car(cdr(*t)), e), v = car(*t), d;
  for (d = *e; T(d) == CONS && !equ(v, car(car(d))); d = cdr(d))
    continue;
  return T(d) == CONS ? CDR(car(d)) = x : T(v) == ATOM ? ERR(3, "unbound %s ", A+ord(v)) : err(3);
}

L f_setcar(P t, P e) {
  L s = evlis(t, e), p = car(s);
  return (T(p) == CONS) ? CAR(p) = car(cdr(s)) : err(1);
}

L f_setcdr(P t, P e) {
  L s = evlis(t, e), p = car(s);
  return (T(p) == CONS) ? CDR(p) = car(cdr(s)) : err(1);
}

L f_read(P t, P _) {
  L x; char c = see;
  see = ' ';
  *ps = 0;
  x = readlisp();
  see = c;
  return x;
}

L f_print(P t, P e) {
  L s;
  for (s = evlis(t, e); T(s) != NIL; s = cdr(s))
    print(car(s));
  return nil;
}

L f_println(P t, P e) {
  f_print(t, e);
  putc('\n', out);
  return nil;
}

L f_write(P t, P e) {
  L s;
  for (s = evlis(t, e); T(s) != NIL; s = cdr(s)) {
    L x = car(s);
    if (T(x) == STRG)
      fprintf(out, "%s", A+ord(x));
    else
      print(x);
  }
  return nil;
}

L f_string(P t, P e) {
  L s, x; S n;
  for (n = 0, s = *t = evlis(t, e); T(s) != NIL; s = cdr(s)) {
    L y = car(s);
    if ((T(y) & ~(ATOM^STRG)) == ATOM)
      n += strlen(A+ord(y));
    else if (T(y) == CONS)
      for (; T(y) == CONS; y = cdr(y))
        ++n;
    else if (y == y)
      n += snprintf(buf, sizeof(buf), FLOAT, y);
  }
  x = alloc(STRG, n+1);
  n = ord(x);
  for (s = *t; T(s) != NIL; s = cdr(s)) {
    L y = car(s);
    if ((T(y) & ~(ATOM^STRG)) == ATOM)
      n += strlen(strcpy(A+n, A+ord(y)));
    else if (T(y) == CONS)
      for (; T(y) == CONS; y = cdr(y))
        *(A+n++) = car(y);
    else if (y == y)
      n += snprintf(A+n, sizeof(buf), FLOAT, y);
  }
  *(A+n) = 0;
  return x;
}

L f_load(P t, P e) {
  L x = f_string(t, e);
  return input(A+ord(x)) ? x : ERR(5, "cannot open %s ", A+ord(x));
}

L f_trace(P t, P e) {
  I savedtr = tr;
  tr = T(*t) == NIL ? 1 : car(*t);
  return more(*t) ? *t = eval(car(cdr(*t)), e), tr = savedtr, *t : tr;
}

L f_catch(P t, P e) {
  L x;
  struct State saved = state;
  if (!(x = setjmp(state.jb)))
    x = eval(car(*t), e);
  else {
    unwind(state.n-saved.n);
    x = cons(atom("ERR"), x);
  }
  state = saved;
  return x;
}

L f_throw(P t, P e) {
  longjmp(state.jb, num(car(*t)));
}

L f_quit(P t, P _) {
  exit(0);
}

/* table of Lisp primitives, each has a name s, a function pointer f, and a tail-recursive flag t */
struct {
  const char *s;
  L (*f)(P, P);
  short t;
} prim[] = {
  {"type",     f_type,    0},                   /* (type x) => <type> value between -1 and 7 */
  {"eval",     f_eval,    1},                   /* (eval <quoted-expr>) => <value-of-expr> */
  {"quote",    f_quote,   0},                   /* (quote <expr>) => <expr> -- protect <expr> from evaluation */
  {"cons",     f_cons,    0},                   /* (cons x y) => (x . y) -- construct a pair */
  {"car",      f_car,     0},                   /* (car <pair>) => x -- "deconstruct" <pair> (x . y) */
  {"cdr",      f_cdr,     0},                   /* (cdr <pair>) => y -- "deconstruct" <pair> (x . y) */
  {"+",        f_add,     0},                   /* (+ n1 n2 ... nk) => n1+n2+...+nk */
  {"-",        f_sub,     0},                   /* (- n1 n2 ... nk) => n1-n2-...-nk or -n1 if k=1 */
  {"*",        f_mul,     0},                   /* (* n1 n2 ... nk) => n1*n2*...*nk */
  {"/",        f_div,     0},                   /* (/ n1 n2 ... nk) => n1/n2/.../nk or 1/n1 if k=1 */
  {"int",      f_int,     0},                   /* (int <integer.frac>) => <integer> */
  {"<",        f_lt,      0},                   /* (< n1 n2) => #t if n1<n2 else () */
  {"eq?",      f_eq,      0},                   /* (eq? x y) => #t if x==y else () */
  {"not",      f_not,     0},                   /* (not x) => #t if x==() else ()t */
  {"or",       f_or,      0},                   /* (or x1 x2 ... xk) => #t if any x1 is not () else () */
  {"and",      f_and,     0},                   /* (and x1 x2 ... xk) => #t if all x1 are not () else () */
  {"begin",    f_begin,   1},                   /* (begin x1 x2 ... xk) => xk -- evaluates x1, x2 to xk */
  {"while",    f_while,   0},                   /* (while x y1 y2 ... yk) -- while x is not () evaluate y1, y2 ... yk */
  {"cond",     f_cond,    1},                   /* (cond (x1 y1) (x2 y2) ... (xk yk)) => yi for first xi!=() */
  {"if",       f_if,      1},                   /* (if x y z) => if x!=() then y else z */
  {"lambda",   f_lambda,  0},                   /* (lambda <parameters> <expr>) => {closure} */
  {"macro",    f_macro,   0},                   /* (macro <parameters> <expr>) => [macro] */
  {"define",   f_define,  0},                   /* (define <symbol> <expr>) -- globally defines <symbol> */
  {"assoc",    f_assoc,   0},                   /* (assoc <quoted-symbol> <environment>) => <value-of-symbol> */
  {"env",      f_env,     0},                   /* (env) => <environment> */
  {"let",      f_let,     1},                   /* (let (v1 x1) (v2 x2) ... (vk xk) y) => y with scope of bindings */
  {"let*",     f_leta,    1},                   /* (let* (v1 x1) (v2 x2) ... (vk xk) y) => y with scope of bindings */
  {"letrec",   f_letrec,  1},                   /* (letrec (v1 x1) (v2 x2) ... (vk xk) y) => y with recursive scope */
  {"letrec*",  f_letreca, 1},                   /* (letrec* (v1 x1) (v2 x2) ... (vk xk) y) => y with recursive scope */
  {"setq",     f_setq,    0},                   /* (setq <symbol> x) -- changes value of <symbol> in scope to x */
  {"set-car!", f_setcar,  0},                   /* (set-car! <pair> x) -- changes car of <pair> to x in memory */
  {"set-cdr!", f_setcdr,  0},                   /* (set-cdr! <pair> y) -- changes cdr of <pair> to y in memory */
  {"read",     f_read,    0},                   /* (read) => <value-of-input> */
  {"print",    f_print,   0},                   /* (print x1 x2 ... xk) => () -- prints the values x1 x2 ... xk */
  {"println",  f_println, 0},                   /* (println x1 x2 ... xk) => () -- prints with newline */
  {"write",    f_write,   0},                   /* (write x1 x2 ... xk) => () -- prints without quoting strings */
  {"string",   f_string,  0},                   /* (string x1 x2 ... xk) => <string> -- string of x1 x2 ... xk */
  {"load",     f_load,    0},                   /* (load <name>) -- loads file <name> (an atom or string name) */
  {"trace",    f_trace,   0},                   /* (trace flag [<expr>]) -- flag 0=off, 1=on, 2=keypress */
  {"catch",    f_catch,   0},                   /* (catch <expr>) => <value-of-expr> if no exception else (ERR . n) */
  {"throw",    f_throw,   0},                   /* (throw n) -- raise exception error code n (integer != 0) */
  {"quit",     f_quit,    0},                   /* (quit) -- bye! */
  {0}};                                         
                                                
/* evaluate x in environment e, returns value of x, tail-call optimized */
L step(L x, P e) {
  L f = nil, v = nil, d = nil, z = nil;
  var(5, &x, &f, &v, &d, &z);
  while (1) {
    if (T(x) == ATOM)
      return ret(5, assoc(x, *e));
    if (T(x) != CONS)
      return ret(5, x);
    f = eval(car(x), e);
    x = cdr(x);
    z = *e;
    e = &z;
    if (T(f) == PRIM) {
      x = prim[ord(f)].f(&x, e);
      if (prim[ord(f)].t)
        continue;
      return ret(5, x);
    }
    if (T(f) == CLOS) {
      v = car(car(f));
      d = cdr(f);
      if (T(d) == NIL)
        d = env;
      for (; T(v) == CONS && T(x) == CONS; v = cdr(v), x = cdr(x)) {
        L y = eval(car(x), e);
        d = pair(car(v), y, &d);
      }
      if (T(v) == CONS) {
        x = eval(x, e);
        for (; T(v) == CONS && T(x) == CONS; v = cdr(v), x = cdr(x))
          d = pair(car(v), car(x), &d);
        if (T(v) == CONS)
          return ret(5, err(5));
      }
      else if (T(x) == CONS)
        x = evlis(&x, e);
      else if (T(x) != NIL)
        x = eval(x, e);
      if (T(v) != NIL)
        d = pair(v, x, &d);
      x = cdr(car(f));
      e = &d;
    }
    else if (T(f) == MACR) {
      d = env;
      v = car(f);
      for (; T(v) == CONS && T(x) == CONS; v = cdr(v), x = cdr(x))
        d = pair(car(v), car(x), &d);
      if (T(v) == CONS)
        return ret(5, err(5));
      if (T(v) != NIL)
        d = pair(v, x, &d);
      x = eval(cdr(f), &d);
    }
    else
      return ret(5, err(4));
  }
}

/* trace the evaluation of x in environment e, returns its value */
L eval(L x, P e) {
  L y;
  if (!tr)
    return step(x, e);
  var(1, &x);                                   /* register var x to display later again */
  y = step(x, e);
  printf("%4d: ", state.n); print(x);           /* <vars>: unevaluated expression */
  printf(" => ");           print(y);           /* => value of the expression */
  if (tr > 1)                                   /* wait for ENTER key or other CTRL */
    while (getchar() >= ' ')
      continue;
  else
    putchar('\n');
  return ret(1, y);
}

/*----------------------------------------------------------------------------*\
 |      PRINT                                                                 |
\*----------------------------------------------------------------------------*/

/* output Lisp list t */
void printlist(L t) {
  putc('(', out);
  while (1) {
    print(car(t));
    if (not(t = cdr(t)))
      break;
    if (T(t) != CONS) {
      fprintf(out, " . ");
      print(t);
      break;
    }
    putc(' ', out);
  }
  putc(')', out);
}

/* output Lisp expression x */
void print(L x) {
  if (T(x) == NIL)
    fprintf(out, "()");
  else if (T(x) == ATOM)
    fprintf(out, "%s", A+ord(x));
  else if (T(x) == STRG)
    fprintf(out, "\"%s\"", A+ord(x));
  else if (T(x) == PRIM)
    fprintf(out, "<%s>", prim[ord(x)].s);
  else if (T(x) == CONS)
    printlist(x);
  else if (T(x) == CLOS)
    fprintf(out, "{%llu}", ord(x));
  else if (T(x) == MACR)
    fprintf(out, "[%llu]", ord(x));
  else
    fprintf(out, FLOAT, x);
}

/*----------------------------------------------------------------------------*\
 |      REPL                                                                  |
\*----------------------------------------------------------------------------*/

/* entry point with Lisp initialization, error handling and REPL */
int main(int argc, char **argv) {
  int i;
  printf("lisp");
  input(argc > 1 ? argv[1] : "init.lisp");      /* set input source to load when available */
  out = stdout;
  if (setjmp(state.jb))                         /* if something goes wrong before REPL, it is fatal */
    abort();
  vars = nil = box(NIL, 0);
  tru = atom("#t");
  var(1, &tru);                                 /* make tru a root var */
  env = pair(tru, tru, &nil);                   /* create environment with symbolic constant #t */
  var(1, &env);                                 /* make env a root var */
  for (i = 0; prim[i].s; ++i)                   /* expand environment with primitives */
    env = pair(atom(prim[i].s), box(PRIM, i), &env);
  using_history();
  BREAK_ON;                                     /* enable CTRL-C break to throw error 2 */
  i = setjmp(state.jb);
  if (i) {
    unwind(state.n-2);                          /* unwind all but the first two, env and tru */
    while (fin)                                 /* close all open files */
      fclose(in[--fin]);
    printf("ERR %d: %s", i, errors[i > 0 && i <= ERRORS ? i : 0]);
  }
  while (1) {
    putchar('\n');
    gc(1);
    snprintf(ps, sizeof(ps), "%llu>", sp-hp/8);
    out = stdout;
    print(eval(readlisp(), &env));
  }
}
