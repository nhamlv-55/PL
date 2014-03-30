#lang plai

(require (for-syntax racket/base) racket/match racket/list racket/string
         (only-in mzlib/string read-from-string-all))

;; build a regexp that matches restricted character expressions, can use only
;; {}s for lists, and limited strings that use '...' (normal racket escapes
;; like \n, and '' for a single ')
(define good-char "(?:[ \t\r\na-zA-Z0-9_{}!?*/<=>:+-]|[.][.][.])")
;; this would make it awkward for students to use \" for strings
;; (define good-string "\"[^\"\\]*(?:\\\\.[^\"\\]*)*\"")
(define good-string "[^\"\\']*(?:''[^\"\\']*)*")
(define expr-re
  (regexp (string-append "^"
                         good-char"*"
                         "(?:'"good-string"'"good-char"*)*"
                         "$")))
(define string-re
  (regexp (string-append "'("good-string")'")))

(define (string->sexpr str)
  (unless (string? str)
    (error 'string->sexpr "expects argument of type <string>"))
    (unless (regexp-match expr-re str)
      (error 'string->sexpr "syntax error (bad contents)"))
    (let ([sexprs (read-from-string-all
                 (regexp-replace*
                  "''" (regexp-replace* string-re str "\"\\1\"") "'"))])
    (if (= 1 (length sexprs))
      (car sexprs)
      (error 'string->sexpr "bad syntax (multiple expressions)"))))

;; MUWAEAE abstract syntax trees
(define-type MUWAE
  [num  (n (listof number?))]
  [add  (left MUWAE?) (right MUWAE?)]
  [sub  (left MUWAE?) (right MUWAE?)]
  [with (name symbol?) (init MUWAE?) (body MUWAE?)]
  [id   (name symbol?)]
  [Sqrt (muwae MUWAE?)])

;;FunDef abstract syntax trees
(define-type FunDef)

;;F1WAE abstract syntax trees
(define-type F1WAE
  [num (n number?)]
  [add (lhs F1WAE?) (rhs F1WAE?)]
  [sub (lhs F1WAE?) (rhs F1WAE?)]
  [with (name symbol?) (named-expr F1WAE?) (body F1WAE?) ]
  [id (name symbol?)]
  [app (ftn symbol?) (arg F1WAE)]
  )

; parse-sexpr : sexpr -> MUWAE
;; to convert s-expressions into MUWAEs
(define (parse-sexpr sexp)
  (match sexp
    [(? number?) (num (list sexp))]
    [(list '+ l r) (add (parse-sexpr l) (parse-sexpr r))]
    [(list '- l r) (sub (parse-sexpr l) (parse-sexpr r))]
    [(list 'with (list x i) b) (with x (parse-sexpr i) (parse-sexpr b))]
    [(list 'sqrt n) (Sqrt (parse-sexpr n))]
    [(? symbol?) (id sexp)]
    [else (error 'parse "bad syntax: ~a" sexp)]))

;; parses a string containing a MUWAE expression to a MUWAE AST
(define (parse str)
  (parse-sexpr (string->sexpr str)))

;; substitutes the second argument with the third argument in the
;; first argument, as per the rules of substitution; the resulting
;; expression contains no free instances of the second argument
(define (subst expr from to)
  (type-case MUWAE expr
    [num (n)   expr]
    [add (l r) (add (subst l from to) (subst r from to))]
    [sub (l r) (sub (subst l from to) (subst r from to))]
    [id (name) (if (symbol=? name from) (num to) expr)]
    [Sqrt (n) (Sqrt(subst n from to))]
    [with (bound-id named-expr bound-body)
          (with bound-id
                (subst named-expr from to)
                (if (symbol=? bound-id from)
                    bound-body
                    (subst bound-body from to)))]))

;; evaluates MUWAE expressions by reducing them to numbers
(define (eval expr)
  (type-case MUWAE expr
    [num (n) n]
    [add (l r) (bin-op + (eval l) (eval r))]
    [sub (l r) (bin-op - (eval l) (eval r))]
    [with (bound-id named-expr bound-body)
           (eval (subst bound-body
                       bound-id
                       (eval named-expr)))]
    [Sqrt (e)(sqrt+  (eval e))]
    [id (name) (error 'eval "free identifier: ~s" name)]))

; run : string -> listof number
;; evaluate a MUWAE program contained in a string
(define (run str)
  (eval (parse str)))

;; sqrt+ : listof number -> listof number
;; a version of `sqrt' that takes a list of numbers, and returns a list
;; with twice the elements, holding the two roots of each of the inputs;
;; throws an error if any input is negative.
(define (sqrt+ ns)
  (cond [(null? ns) empty]
	[(< (first ns) 0) (error 'sqrt+ "Negative number")]
	[else (append (list (sqrt (first ns)) (- (sqrt (first ns) ))) (sqrt+ (rest ns)) )]))


;bin-op : (number number -> number) (listof number) (listof number) -> (listof number))
;; applies a binary numeric function on all combinations of numbers from
;; the two input lists, and return the list of all of the results
(define (bin-op op ls rs)
  (define (helper l rs)
    ;; f : number -> number
    (define (f n) (op l n))
    (map f rs))
  (if (null? ls)
    null
    (append (helper (first ls) rs) (bin-op op (rest ls) rs))))

;; tests
(test (run "5") '(5))
(test (run "{+ 5 5}") '(10))
(test (run "{with {x {+ 5 5}} {+ x x}}") '(20))
(test (run "{with {x 5} {+ x x}}") '(10))
(test (run "{with {x {+ 5 5}} {with {y {- x 3}} {+ y y}}}") '(14))
(test (run "{with {x 5} {with {y {- x 3}} {+ y y}}}") '(4))
(test (run "{with {x 5} {+ x {with {x 3} 10}}}") '(15))
(test (run "{with {x 5} {+ x {with {x 3} x}}}") '(8))
(test (run "{with {x 5} {+ x {with {y 3} x}}}") '(10))
(test (run "{with {x 5} {with {y x} y}}") '(5))
(test (run "{with {x 5} {with {x x} x}}") '(5))
(test/exn (run "{with {x 1} y}") "free identifier")
(test/exn (run 5) "string->sexpr: expects argument of type <string>")
(test/exn (run "^") "string->sexpr: syntax error (bad contents)")
(test/exn (run "5 5") "string->sexpr: bad syntax (multiple expressions)")


;; additional tests for complete coverage
(test (run "{with {x 2} {- {+ x x} x}}") '(2))
(test/exn (run "{with x = 2 {+ x 3}}") "bad syntax")
(test/exn (run "{bleh}") "bad syntax")

(test (run "{sqrt 9}") '(3 -3))
(test (run "{sqrt 1}") '(1 -1))
(test (run "{sqrt 0}") '(0 0))
(test (run "{+ {sqrt 1} 3}") '(4 2))
(test (run "{+ {- {+ {sqrt 1} 3} 2} {sqrt 100}}") '(12 -8 10 -10))
(test (run "{sqrt {+ 16 {+ {sqrt {+ 1 -1}} {+ 7 2}}}}") '(5 -5 5 -5))
(test/exn (run "{+ {- {sqrt {with {x {sqrt 5}} x}} 3} 5}") "sqrt+: Negative number")
(test (run "{sqrt {+ {with {x 10} 10} {+ {sqrt {+ 1 -1}} {+ 7 2}}}}")
      '(4.358898943540674 -4.358898943540674 4.358898943540674 -4.358898943540674))

(test (run "{sqrt {+ {sqrt{with {x 0} x}} 4}}") '(2 -2 2 -2))
(test (run "{with 
                  {x {with {y 100} {sqrt y}}} {+ x x}
             }") '(20 0 0 -20))
