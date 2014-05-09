#lang plai

;;(print-only-errors #t)

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

(define-type KCFAE
  [num (n number?)]
  [add (lhs KCFAE?)
       (rhs KCFAE?)]
  [sub (lhs KCFAE?)
       (rhs KCFAE?)]
  [id (name symbol?)]
  [fun (param (listof symbol?))
       (body KCFAE?)]
  [app (fun-expr KCFAE?)
       (arg-expr (listof KCFAE?))]
  [if0 (test KCFAE?)
       (then KCFAE?)
       (else KCFAE?)]
  [withcc (name symbol?)
          (body KCFAE?)])

(define-type KCFAE-Value
  [numV (n number?)]
  [closureV (param (listof symbol?))
            (body KCFAE?)
            (sc DefrdSub?)]
  [contV (proc procedure?)])

(define-type DefrdSub
  [mtSub]
  [aSub (name symbol?)
        (value KCFAE-Value?)
        (rest DefrdSub?)])

(define (add-sub names values ds)
  (cond
    [(empty? names) ds]
    [else (
           add-sub (rest names) (rest values)
                   (aSub (first names) (first values) ds))]))

;; ----------------------------------------

;; parse-sexpr : S-expr -> KCFAE
(define (parse-sexpr sexp)
  (cond
    [(number? sexp) (num sexp)]
    [(symbol? sexp) (id sexp)]
    [(pair? sexp)
     (case (car sexp)
       [(+) (add (parse-sexpr (second sexp)) (parse-sexpr (third sexp)))]
       [(-) (sub (parse-sexpr (second sexp)) (parse-sexpr (third sexp)))]
       [(fun) (fun (second sexp) (parse-sexpr (third sexp)))]
       [(if0) (if0 (parse-sexpr (second sexp))
                   (parse-sexpr (third sexp))
                   (parse-sexpr (fourth sexp)))]
       ;[(withcc) (withcc (second sexp) ((parse-sexpr (third sexp))))]
       [(withcc) (withcc (second sexp) (parse-sexpr (third sexp)))]
       ;[else (app (parse-sexpr (first sexp)) (parse-sexpr (second sexp)))]
       [else (app (parse-sexpr (first sexp)) (parse-list (rest sexp)))]
       )]))

(define (parse-list list-of-sexpr)
  (cond
    [(empty? list-of-sexpr) empty]
    [else (cons (parse-sexpr (first list-of-sexpr))  (parse-list (rest list-of-sexpr))   )])
  )

;; parse: string -> BFAE
;; parses a string containing a BFAE expression to a BFAE AST
(define (parse str)
  (parse-sexpr (string->sexpr str)))

;(test (parse "3") (num 3))
;(test (parse "x") (id 'x))
;(test (parse "{+ 1 2}") (add (num 1) (num 2)))
;(test (parse "{- 1 2}") (sub (num 1) (num 2)))
(test (parse "{fun {x} x}") (fun '(x) (id 'x)))
(test (parse "{1 2}") (app (num 1) (list (num 2))))
(test (parse "{if0 0 1 2}") (if0 (num 0) (num 1) (num 2)))
(test (parse "{withcc x 2}") (withcc 'x (num 2)))

;; ----------------------------------------

;; interp : KCFAE DefrdSub (KCFAE-Value -> alpha) -> alpha
(define (interp a-fae ds k)
  (type-case KCFAE a-fae
    [num (n) (k (numV n))]
    [add (l r) (interp l ds
                       (lambda (v1)
                         (interp r ds
                                 (lambda (v2)
                                   (k (num+ v1 v2))))))]
    [sub (l r) (interp l ds
                       (lambda (v1)
                         (interp r ds
                                 (lambda (v2)
                                   (k (num- v1 v2))))))]
    [id (name) (k (lookup name ds))]
    [fun (param body-expr)
         (k (closureV param body-expr ds))]
    [app (fun-expr arg-expr)
         (interp fun-expr ds
                 (lambda (fun-val)
                   (interp-many arg-expr ds
                           (lambda (arg-vals)
                             (type-case KCFAE-Value fun-val
                               [closureV (params body ds)
                                         (interp body
                                                 (add-sub params
                                                       arg-vals
                                                       ds)
                                                 k)]
                               [contV (k)
                                      (k (first arg-vals))]
                               [else (error 'interp "not a function")])))))]
    [if0 (test-expr then-expr else-expr)
         (interp test-expr ds
                 (lambda (v)
                   (if (numzero? v)
                       (interp then-expr ds k)
                       (interp else-expr ds k))))]
    [withcc (id body-expr)
            (interp body-expr 
                    (aSub id
                          (contV k)
                          ds)
                    k)]))

(define (interp-many list_of_expr ds k)
  (cond
    [(empty? list_of_expr) (k empty)]
    [else (interp (first list_of_expr) ds 
                  (lambda (val) ;interp-many of the first element will return 1 value
                    (interp-many (rest list_of_expr) ds 
                                 (lambda (vals) (k (cons val vals))) ; interp many of the rest will return a list
                                 )
                    )
                  )
          ]
    )
  )

;; num-op : (number number -> number) -> (KCFAE-Value KCFAE-Value -> KCFAE-Value)
(define (num-op op)
  (lambda (x y)
    (numV (op (numV-n x) (numV-n y)))))

(define num+ (num-op +))
(define num- (num-op -))

;; numzero? : KCFAE-Value -> boolean
(define (numzero? x)
  (zero? (numV-n x)))

(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free variable")]
    [aSub (sub-name num rest-sc)
          (if (symbol=? sub-name name)
              num
              (lookup name rest-sc))]))

(test/exn (lookup 'x (mtSub)) "free variable")
(test (lookup 'x (aSub 'x (numV 9) (mtSub))) (numV 9))
(test (lookup 'x (aSub 'y (numV 10) (aSub 'x (numV 9) (mtSub)))) (numV 9))

;; interp-expr : KCFAE -> number-or-'function
(define (interp-expr a-fae)
  (type-case KCFAE-Value (interp a-fae (mtSub) (lambda (x) x))
    [numV (n) n]
    [closureV (param body ds) 'function]
    [contV (k) 'function]))

; run : string -> number-or-'function
;; evaluate a KCFAE program contained in a string
(define (run str)
  (interp-expr (parse str)))

(test (run "{{fun {x y} {- y x}} 10 12}") 2)
(test (run "{fun {} 12}") 'function)
(test (run "{fun {x} {fun {} x}}") 'function)
(test (run "{{{fun {x} {fun {} x}} 13}}") 13)
(test (run "{withcc esc {{fun {x y} x} 1 {esc 3}}}") 3)
;;old tests
 (test (run "10")
       10)
 (test (run "{fun {x} x}")
       'function)
 (test (run "{withcc x x}")
       'function)
 (test (run "{+ 10 7}")
       17)
 (test (run "{- 10 7}")
       3)
 (test (run "{{fun {x} {+ x 12}} {+ 1 17}}")
       30)
 (test (run "{{fun {x} {{fun {f} {+ {f 1} {{fun {x} {f 2}} 3}}}
                        {fun {y} {+ x y}}}}
              0}")
       3)
 (test (run "{withcc k {k 10}}")
       10)
 (test (run "{withcc k {+ {k 10} 17}}")
       10)
 
 


