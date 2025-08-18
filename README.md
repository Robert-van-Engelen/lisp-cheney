# Lisp in 1k lines of C, explained

A quick glance at this small Lisp interpreter's features:

- Lisp with _floating point_, _strings_, proper _closures_, and _macros_
- over _40 built-in Lisp primitives_
- _lexically-scoped_ locals, like tinylisp
- proper _tail recursion_, including tail calls through `begin`, `cond`, `if`, `let`, `let*`, `letrec`, `letrec*`
- _exceptions_ and error handling with safe return to REPL after an error
- _break with CTRL-C_ to return to the REPL (optional)
- REPL with GNU _readline_ for convenient Lisp command line input (optional)
- _load Lisp_ source code files
- _execution tracing_ to display Lisp evaluation steps
- Cheney _copying garbage collector_ to recycle unused cons pair cells, atoms and strings
- Lisp memory is a _single `cell[]` array_, no `malloc()` and `free()` calls (except each `readline` requires a `free`)
- easily _customizable and extensible_ to add new special features
- _integrates with C (and C++)_ code by calling C (C++) functions for Lisp primitives, for example to embed a Lisp interpreter

I've documented this project's source code extensively to explain the inner workings of the Lisp interpreter, which should make it easy to use and to modify the code.  This small Lisp interpreter includes a copying garbage collector that is efficient.  Cheney's [copying garbage collector](https://en.wikipedia.org/wiki/Cheney%27s_algorithm) uses two heaps.  Cells, atoms and strings are moved between the heaps by the copying garbage collector to make space.  Because objects are moved, C variables that reference Lisp objects on the heap must be registered with the garbage collector.  To do so, a C function calls `var(n, &x1, &x2, ..., &xn)` to register `n` local variables `x1` to `xn` of type `L` (Lisp object).  The variables are automatically updated by the garbage collector to reference moved cells, atoms and strings on the heap.  The C function returns with `return ret(n, <ret-value>)` to de-register `n` variables and return `<ret-value>`.

Like [tinylisp](https://github.com/Robert-van-Engelen/tinylisp), this Lisp interpreter's memory is a `cell[N]` array of Lisp expressions `L`.  With a copying garbage collector we need two `heap[2]` of `N` cells each.  We let `cell` point to the `N` active cells in either `heap[0]` or in `heap[1]`.  A `from` pointer is used to move cells between the two heaps in the garbage collection phase:

    /* we use two heaps: a primary heap cell[] and a secondary heap for the copying garbage collector */
    L heap[2][N], *cell = heap[0], *from;

The atom and string heap pointer `hp` points to available heap space above the allocated atoms and strings.  The stack grows down from the top `cell[N]` towards the heap, starting with stack pointer `sp = N`.  We also define a `tr` tracing flag:

    /* hp: heap pointer, A+hp with hp=0 points to the first atom string in heap[]
       sp: stack pointer, the stack starts at the top of the primary heap cell[] with sp=N
       tr: 0 when tracing is off, 1 or 2 to trace Lisp evaluation steps */
    I hp = 0, sp = N, tr = 0;

A benefit of a copying garbage collector is that memory allocation is efficient.  We simply push data on a stack:

    /* construct pair (x . y) returns a NaN-boxed CONS */
    L cons(L x, L y) {
      cell[--sp] = x;                       /* push the car value x, this protects x from getting GC'ed */
      cell[--sp] = y;                       /* push the cdr value y, this protects y from getting GC'ed */
      return gc(box(CONS, sp));             /* make sure we have enough space for the (next) new cons pair */
    }

Allocating atoms (symbols and strings) of varying sizes is performed by pushing a space of `W+n` bytes upwards in the heap area pointed to by heap pointer `hp`, where `W` is the width of the symbol/string size field:

    /* allocate n bytes on the heap, returns NaN-boxed t=ATOM or t=STRG */
    L alloc(I t, S n) {
      L x = box(t, W+hp);                   /* NaN-boxed ATOM or STRG points to bytes after the size field W */
      *(S*)(A+hp) = n;                      /* save size n field in front of the to-be-saved string on the heap */
      *(A+W+hp) = 0;                        /* make string empty, just in case */
      hp += W+n;                            /* try to allocate W+n bytes on the heap */
      return gc(x);                         /* check if space is allocatable, GC if necessary, returns updated x */
    }

where:

    typedef double   L;                     /* Lisp expression type: NaN-boxed 64 bit double floating point */
    typedef uint64_t I;                     /* unsigned 64 bit integer of a NaN-boxed double */
    typedef int      S;                     /* signed size of an atom string on the heap, negative for forwarding */
    typedef L       *P;                     /* pointer to a root variable with a value that is updated by GC */
    #define A (char*)cell                   /* address of the atom heap */
    #define B (char*)from                   /* address of the atom "from" heap during garbage collection */
    #define W sizeof(S)                     /* width of the size field of an atom string on the heap, in bytes */

For this allocation strategy to work, we make sure to have at least `W` bytes and two cons cells (16 bytes) always available between the heap and the stack by ensuring the invariant `hp <= (sp-2)<<3` always holds, since `sp` is the `cell[]` index (cells are 8 bytes) and `hp` is a byte offset from the bottom of the heap.  If the invariant no longer holds, then garbage collection is performed to make space available.  If that fails then we ran out of memory.  The entire garbage collector fits in fewer than 50 lines of C:

    /* move ATOM/STRG/CONS/CLOS/MACR/VARP x from the 1st to the 2nd heap or use its forwarding index, return updated x */
    L move(L x) {
      I t = T(x), i = ord(x);               /* save the tag and ordinal of x */
      if (t == VARP) {                      /* if x is a VARP */
        *(P)i = move(*(P)i);                /*   update the variable by moving its value to the "to" heap */
        return x;                           /*   return VARP x */
      }
      if ((t & ~(ATOM^STRG)) == ATOM) {     /* if x is an ATOM or a STRG */
        I j = i-W;                          /*   j is the index of the size field located before the string */
        S n = *(S*)(B+j);                   /*   get size n of the string at the "from" heap to move */
        if (n < 0)                          /*   if the size is negative, it is a forwarding index */
          return box(t, -n);                /*     return ATOM with forwarded index to the location on "to" heap */
        memcpy(A+hp, B+j, W+n);             /*   move the size field and string from the "from" to the "to" heap */
        *(S*)(B+j) = -(S)(W+hp);            /*   leave a negative forwarding index on the "from" heap */
        hp += W+n;                          /*   increment heap pointer by the number of allocated bytes */
        return box(t, hp-n);                /*   return ATOM/STRG with index of the string on the "to" heap */
      }
      if ((t & ~(CONS^MACR)) != CONS)       /* if x is not a CONS/CLOS/MACR pair */
        return x;                           /*   return x */
      if (T(from[i]) == FORW)               /* if x is a CONS/CLOS/MACR with forwarding index on the "from" heap */
        return box(t, ord(from[i]));        /*   return x with updated index pointing to "to" heap */
      cell[--sp] = from[i+1];               /* move CONS/CLOS/MACR pair from the "from" to the "to" heap */
      cell[--sp] = from[i];
      from[i] = box(FORW, sp);              /* leave a forwarding index on the "from" heap */
      return box(t, sp);                    /* return CONS/CLOS/MACR with index to the location on the "to" heap */
    }

    /* the roots of the garbage collector is a Lisp list of VARP pointers to global and local variables */
    L vars;

    /* garbage collect with root p, returns (moved) p; p=1 forces garbage collection */
    L gc(L p) {
      if (hp > (sp-2)<<3 || equ(p, 1) || ALWAYS_GC) {
        BREAK_OFF;                          /* do not interrupt GC */
        I i = N;                            /* scan pointer starts at the top of the 2nd heap */
        hp = 0;                             /* heap pointer starts at the bottom of the 2nd heap */
        sp = N;                             /* stack pointer starts at the top of the 2nd heap */
        from = cell;                        /* move cells from the original 1st "from" heap cell[] */
        cell = heap[cell == heap[0]];       /* ... to the 2nd heap, which becomes the 1st "to" heap cell[] */
        vars = move(vars);                  /* move the roots */
        p = move(p);                        /* move p */
        while (--i >= sp)                   /* while the scan pointer did not pass the stack pointer */
          cell[i] = move(cell[i]);          /*   move the cell from the "from" heap to the "to" heap */
        BREAK_ON;                           /* enable interrupt */
        if (hp > (sp-2)<<3)                 /* if the heap is still full after garbage collection */
          err(7);                           /*   we ran out of memory */
      }
      return p;
    }

I've made the Cheney garbage collection routines more compact by placing all active `L`-typed C variables of the Lisp interpreter registered with `var()` in a linked list on the Lisp stack itself, rather than in a separate stack-like data structure.  After registering a C variable with `var()`, a pointer to the variable is added to the linked list and tagged with `VARP`.  The list of `VARP` pointers is `vars`, which serves as a root for garbage collection.  The garbage collector automatically updates the registered C variables in `move()` when the Lisp expression referenced by the registered variable is moved.  Active C variables are registered with `var()` and released with `ret()`:

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

For example, the `while` primitive traverses a list of expressions to evaluate, using a C variable `s` that runs over the list of arguments `*t`:

    L f_while(P t, P e) {
      L s = nil, x = nil;
      var(2, &s, &x);
      while (!not(eval(car(*t), e)))
        for (s = cdr(*t); T(s) != NIL; s = cdr(s))
          x = eval(car(s), e);
      return ret(2, x);
    }

Variable `s` must be registered with the garbage collector, because `eval()` may trigger garbage collection that causes list `*t` to move.  Furthermore, `*t` is already registered before `f_while()` is called, and that is why we pass a pointer `P t` to `f_while()` instead of a value `t` that may become stale after garbage collection.  Lisp expression pointer `P` arguments passed to a C function of the interpreter are already registered with the garbage collector and do not need to be registered again.

Note that `var()` and `ret()` update `state.n`.  The Lisp interpreter `state` is used by the `catch` primitive to save and restore the state after an exception, thereby unwinding the `vars` list "stack" to release all C variables that are no longer active after the exception was caught:

    /* state of the setjump-longjmp exception handler with jump buffer jb and number of active root variables n */
    struct State {
      jmp_buf jb;
      int n;
    } state;

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

## Is it really Lisp?

Like [tinylisp](https://github.com/Robert-van-Engelen/tinylisp), this Lisp preserves the original meaning and flavor of [John McCarthy](https://en.wikipedia.org/wiki/John_McCarthy_(computer_scientist))'s [Lisp](https://en.wikipedia.org/wiki/Lisp_(programming_language)) as much as possible:

    > (define curry
          (lambda (f x)
              (lambda args
                  (f x . args))))
    > ((curry + 1) 2 3)
    6

If your Lisp can't [curry](https://en.wikipedia.org/wiki/Currying) like this, it isn't classic Lisp!

## Proper tail recursive

Tail-recursive calls and tail calls in general are optimized.  For example, `(forever inf)` infinite recursion:

    > (define forever
          (lambda (n)
              (if (eq? 0 n)
                  'done
                  (write "forever\n") (forever (- n 1)))))
    > (forever inf)
    forever
    forever
    ...

Tail call optimization is applied to the last function evaluated when its return value is not used as an argument to another function to operate on.  Tail call optimization is also applied to the tail calls made through the `begin`, `cond`, `if`, `let`, `let*`, `letrec`, and `letrec*` special forms.

## Running Lisp

Initialization imports `init.lisp` first, when located in the working directory.  Otherwise this step is skipped.  You can load Lisp source files with `(load "name.lisp")`, for example

    $ ./lisp
    ...
    defun
    6209>(load "nqueens.lisp")
    ...
    (- - - - - - - @)
    (- - - @ - - - -)
    (@ - - - - - - -)
    (- - @ - - - - -)
    (- - - - - @ - -)
    (- @ - - - - - -)
    (- - - - - - @ -)
    (- - - - @ - - -)
    ()
    done
    5463>(quit)
    $

The prompt displays the number of free cons pair cells available.

To quit Lisp, type `(quit)`.

## Execution tracing

An execution trace displays each evaluation step:

    6209>(trace)
    1
    6209>((curry + 1) 2 3)
      15: curry => {8096}
      15: + => <+>
      15: 1 => 1
      15: lambda => <lambda>
       9: (curry + 1) => {6214}
      11: 2 => 2
      11: 3 => 3
       9: f => <+>
      11: x => 1
      11: args => (2 3)
       3: ((curry + 1) 2 3) => 6
    6

Note: the origin of a tail call may not be displayed.

## Compilation

Just one source code file [lisp-cheney.c](src/lisp-cheney.c) to compile:

    $ cc -o lisp lisp-cheney.c -O2 -DHAVE_SIGNAL_H -DHAVE_READLINE_H -lreadline

Without CTRL-C to break and without the [GNU readline](https://en.wikipedia.org/wiki/GNU_Readline) library:

    $ cc -o lisp lisp-cheney.c -O2

## Testing

    cd tests && ./runtests.sh

## Lisp language features

### Numbers

Double precision floating point numbers, including `inf`, `-inf` and `nan`.  Numbers may also be entered in hexadecimal `0xh...h` format.

### Symbols

Lisp symbols consist of a sequence of non-space characters, excluding `(`, `)` and quotes.  When used in a Lisp expression, a symbol is looked-up for its value, like a variable typically refers to its value.  Symbols can be '-quoted like `'foo` to use symbols literally and to pass them to functions.

### Booleans

Well, Lisp doesn't need Booleans.  An `()` empty list (called nil) is considered false and anything not `()` is considered true.  For convenience, `#t` is a symbol representing true (`#t` evaluates to itself, i.e. quoting is not needed.)

### Strings

Strings are "-quoted and may contain `\a`, `\b`, `\t`, `\n`, `\v`, `\f` and `\r` escapes.  Use `\"` to escape the quote and `\\` to escape the backslash.  For example, `"\"foo\tbar\"\n"` includes quotes at the start and end, a tab `\t` and a newline `\n`.

    (string x1 x2 ... xk)

returns a string concatenation of the specified symbols, strings and/or numbers.  Arguments can be lists containing a sequence of 8-bit character codes (ASCII/UTF-8) to construct a string.

### Lists

Lists are code and data in Lisp.  Syntactically, a dot may be used for the last list element to construct a pair rather than a list.  For example, `'(1 . 2)` is a pair, whereas `'(1 2)` is a list.  By the nature of linked lists, a list after a dot creates a list, not a pair.  For example, `'(1 . (2 . ()))` is the same as `'(1 2)`.  Note that lists form a chain of pairs ending in a `()` nil.  

### Function calls

    (<function> <expr1> <expr2> ... <exprn>)

applies a function to the rest of the list of expresssions as its arguments.  The following are all built-in functions, called "primitives" and "special forms".

### Quoting and unquoting

    '<expr>
    (quote <expr>)

protects `<expr>` from evaluation by quoting, same as `'<expr>`.  For example, `'(1 () foo (bar 7))` is a list containing unevaluated expressions protected by the quote.

    (eval <quoted-expr>)

evaluates a quoted expression and returns its value.  For example, `(eval '(+ 1 2))` is 3.

    `<expr>

backquotes `<expr>`, which quotes `<expr>`, but evaluates all `,<expr>` subexpressions therein before quoting i.e. unquotes.

### Constructing and deconstructing pairs and lists

    (cons x y)

constructs a pair `(x . y)` for expressions `x` and `y`.  Lists are formed by chaining sevaral cons pairs, with the empty list `()` as the last `y`.  For example, `(cons 1 (cons 2 ()))` is the same as `'(1 2)`.

    (list x1 x2 ... xn)

returns the list of evaluated `x1`, `x2`, ... `xn`, same as `(cons x1 (cons x2 (cons ... (cons xn ()))))`.

    (car <pair>)

returns the first part `x` of a pair `(x . y)` or list.

    (cdr <pair>)

returns the second part `y` of a pair `(x . y)`.  For lists this returns the rest of the list after the first part.

### Arithmetic

    (+ n1 n2 ... nk)
    (- n1 n2 ... nk)
    (* n1 n2 ... nk)
    (/ n1 n2 ... nk)

add, substract, multiply or divide the `n1` by `n2` to `nk`.  Subtraction and division with only one value are treated as special cases such that `(- 2)` is -2 and `(/ 2)` is 0.5.

    (int n)

returns the integer part of a number `n`.

### Logic

    (< x y)

returns `#t` (true) if `x` < `y`.  Otherwise, returns `()` (empty list means false).  The ordering among values of different types is as follows: () < number < primitive < symbol < string < pair/list < closure < macro.  Be warned that non-atomic pair/list, closure and macro values are not ordered by this primitive, due to the copying garbage collector moving cells between heaps, i.e. we cannot simply order by the cell index.

    (eq? x y)

returns `#t` (true) if values `x` and `y` are identical.  Otherwise, returns `()` (empty list means false).  Numbers, symbols and strings of the same value are always identical, but non-empty lists may or may not be identical even when their values are the same.

    (not x)

returns `#t` if `x` is not `()`.  Otherwise, returns `()` (empty list means false).

    (or x1 x2 ... xk)

returns the value of the first `x` that is not `()`.  Otherwise, returns `()` (empty list means false).  Only evaluates the `x` until the first is not `()`, i.e. the `or` is conditional.

    (and x1 x2 ... xk)

returns the value of the last `x` if all `x` are not `()`.  Otherwise, returns `()` (empty list means false).  Only evaluates the `x` until the first is `()`, i.e. the `and` is conditional.  When no arguments are specified `(and)` returns `#t`.

Note that `(or (and <test> <then>) <else>)` forms an if-then-else.  However, like Lua for example, this is not correct when the `<test>` evluates to true but `<then>` is nil (the `()` empty list.)  In that case `<else>` is evaluated.

### Conditionals

    (cond (x1 y1) (x2 y2) ... (xk yk))

returns the value of `y` corresponding to the first `x` that is not `()` (meaning not false, i.e. true.)  If an `y` is missing then `y` defaults to `()`.  If the `y` are multiple expressions, then all such expressions are evaluated and the value of the last expression is returned.

    (if x y z)

if `x` is not `()` (meaning not false, i.e. true), then return `y` else return `z`.  If `z` is missing then `()` is returned.  If `z` are multiple expressions, then all such expressions are evaluated and the value of the last expression is returned.

### Lambdas

    (lambda <variables> <expr>)

returns an anonymous function "closure" with a list of variables and an expression as its body.  For example, `(lambda (n) (* n n))` squares its argument.  The variables of a lambda may be a single name (not placed in a list) to pass all arguments as a named list.  For example, `(lambda args args)` returns its arguments as a list.  The pair dot may be used to indicate the rest of the arguments.  For example, `(lambda (f x . args) (f . args))` applies a function argument`f` to the arguments `args`, while ignoring `x`.  The closure includes the lexical scope of the lambda, i.e. local names defined in the outer scope can be used in the body.  For example, `(lambda (f x) (lambda args (f x . args)))` is a function that takes function `f` and argument `x` to return a [curried function](https://en.wikipedia.org/wiki/Currying).

### Macros

    (macro <variables> <expr>)

a macro is like a function, except that it does not evaluate its arguments.  Macros typically construct Lisp code that is evaluated when the macro is expanded.  For example, the `defun` macro (see init.lisp) simplifies function definitions `(define defun (macro (f v x) (list 'define f (list 'lambda v x))))` such that `(defun fun (vars...) body)` expands to `(define fun (lambda (vars...) body))` using the convenient Lisp `list` function (see init.lisp) to construct the Lisp code list.

    `<expr>

backquotes `<expr>`, which quotes `<expr>`, but evaluates all `,<expr>` subexpressions therein before quoting.  For example, the macro example above can also be written as ``(define defun (macro (f v x) `(define ,f (lambda ,v ,x))))`` without using `list` to construct lists and "down quotes" to replace variables with their values i.e. unquotes.

### Globals

    (define <symbol> <expr>)

globally defines a symbol associated with the value of an expression.  If the expression is a function or a macro, then this globally defines the function or macro.

    (assoc <quoted-symbol> <environment>)

returns the value associated with the quoted symbol in the given environment.

    (env)

returns the current environment.  When executed in the REPL, returns the global environment.

### Locals

Locals are declared with the following `let` special forms.  These forms differ slightly in syntax from other Lisp and Scheme implementations, with the aim to make let-forms more intuitive to use (I spent a lot of time debugging my student's Scheme programs as many of them mistakingly forgot to use a list of pairs in the let-forms, so it's time to get rid of that once and for all, but if you don't like it then change this Lisp implementation as you wish):

    (let (v1 x1) (v2 x2) ... (vk xk) y)
    (let* (v1 x1) (v2 x2) ... (vk xk) y)

evaluates `y` with a local scope of bindings for symbols `v` bound to the corresponding values of `x`.  The star versions sequentially bind the symbols from the first to the last, the non-star simultaneously bind.  Note that other Lisp implementations may require placing all `(v x)` in a list, but allow multiple `y` (you can use `begin` instead).

    (letrec (v1 x1) (v2 x2) ... (vk xk) y)
    (letrec* (v1 x1) (v2 x2) ... (vk xk) y)

evaluates `y` with a local scope of recursive bindings for symbols `v` bound to the corresponding values of `x`.  The star versions sequentially bind the symbols from the first to the last, the non-star simultaneously bind.  Note that other Lisp implementations may require placing all `(v x)` in a list, but allow multiple `y` (you can use `begin` instead).

If an `x` is missing then `x` defaults to `()`.  If the `x` are multiple expressions, then all such expressions are evaluated and the value of the last expression is bound to the corresponding `v`.

### Assignments

    (setq <symbol> x)

destructively assigns a globally or locally-bound symbol a new value.

    (set-car! <pair> x)
    (set-cdr! <pair> y)

destructively assigns a pair a new car or cdr value, respectively.

### Input and output

    (load <name>)

loads the specified file name (name is a string or a symbol.)

    (read)

returns the Lisp expression read from input.

    (print x1 x2 ... xk)
    (println x1 x2 ... xk)

prints the expressions.  Strings are quoted.

    (write x1 x2 ... xk)

prints the expressions.  Strings are not quoted.

### Debugging

    (trace <0|1|2>)
    (trace <0|1|2> <expr>)

disables tracing (0), enables tracing (1), and enables tracing with ENTER key press (2).  The first form enables or disables tracing of expression evaluation.  The second form enables or disables tracing of `<expr>` specifically.

### Exceptions

    (catch <expr>)

catch exceptions in the evaluation of an expression, returns the value of the expression or `(ERR . n)` for nonzero error code `n`.

    (throw n)

throws error `n`, where `n` is a nonzero integer.

### Statement sequencing and repetition

    (begin x1 x2 ... xk)

sequentially evaluates expressions, returns the value of the last expression.

    (while x y1 y2 ... yk)

while `x` is not `()` (meaning true), evaluates expressions `y`.  Returns the last value of `yk` or `()` when the loop never ran.

### Type checking

    (type <expr>)

returns a value -1 (nil), 0 (number), 1 (primitive), 2 (symbol), 3 (string), 4 (cons pair), 6 (closure) and 7 (macro) to identify the type of `<expr>`.

### Quit

    (quit)

exits Lisp.

## Library functions and macros

Additional Lisp functions and macros are defined in [init.lisp](src/init.lisp).

    (defun <symbol> <variables> <expr>)

defines a named function with variables and a function body.  A shorthand for `(define <symbol> (lambda <variables> <expr>))`.

    (defmacro <symbol> <variables> <expr>)

defines a named macro with variables and a body.  A shorthand for `(define <symbol> (macro <variables> <expr>))`.

    (null? x)
    (number? x)
    (symbol? x)
    (string? x)
    (pair? x)
    (atom? x)
    (list? x)

returns `#t` if `x` is of a specific type or structure.

    (equal? x y)

returns `#t` if values `x` and `y` are identical or structurally equal.

    (list x1 x2 ... xn)

returns the list of evaluated `x1`, `x2`, ... `xn`.

    (seq n1 n2)
    (range n1 n2 [n3])

returns a list of numbers `n1` up to but excluding `n2`, with an optional step `n3` when specified.

    (length t)
    (append t1 t2)
    (reverse t)
    (member x t)
    (foldr f x t)
    (foldl f x t)
    (min t)
    (max t)
    (filter f t)
    (all? f t)
    (any? f t)
    (mapcar f t)
    (map f t1 t2 ... tn)
    (zip t1 t2 ... tn)

which are the common non-destructive list operations on lists `t` with functions `f` and values `x`.

    (Y f)

is the fixed-point [Y combinator](https://en.wikipedia.org/wiki/Fixed-point_combinator#Fixed-point_combinators_in_lambda_calculus).

    (reveal f)

reveals the contents of `f` by displaying the `lambda` of a closure `f` and the body of a `macro` `f`.
