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
;print: a helper function to print things nicely
(define (print comment x)
  (begin
    (display comment)
    (display x)
    (display "\n")))


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
          (body KCFAE?)]
  [try-catch (try KCFAE?)
             (catch KCFAE?)]
  [throw])

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
    [(symbol? sexp) (cond
                      [(symbol=? 'throw sexp) (throw)]
                      [else (id sexp)])
                    ]
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
       [(try) (try-catch (parse-sexpr (second sexp))
                         (parse-sexpr (fourth sexp)))]
       [else (app (parse-sexpr (first sexp)) (parse-list (rest sexp)))]
       )]))
;; parse-list: (listof sexpr) -> (listof KCFAE)
;; parse a list of sexpr to a list of KCFAE
(define (parse-list list-of-sexpr)
  (cond
    [(empty? list-of-sexpr) empty]
    [else (cons (parse-sexpr (first list-of-sexpr))  (parse-list (rest list-of-sexpr))   )])
  )
;(test (parse-list  '((+ 8 2) (- 16 4)) ) 
;      (list (add (num 8) (num 2)) (sub (num 16) (num 4))) )
;; parse: string -> BFAE
;; parses a string containing a BFAE expression to a BFAE AST
(define (parse str)
  (parse-sexpr (string->sexpr str)))

(test (parse "3") (num 3))
(test (parse "x") (id 'x))
(test (parse "{+ 1 2}") (add (num 1) (num 2)))
(test (parse "{- 1 2}") (sub (num 1) (num 2)))
(test (parse "{fun {x} x}") (fun '(x) (id 'x)))
(test (parse "{1 2}") (app (num 1) (list (num 2))))
(test (parse "{if0 0 1 2}") (if0 (num 0) (num 1) (num 2)))
(test (parse "{withcc x 2}") (withcc 'x (num 2)))

;; ----------------------------------------

;; interp : KCFAE DefrdSub (KCFAE-Value -> alpha) catcher -> alpha
;; return a procedure from calculating a procedure with its ds and exception handler
(define (interp a-fae ds k catcher)
  (type-case KCFAE a-fae
    [num (n) (k (numV n))]
    [add (l r) (interp l ds
                       (lambda (v1)
                         (interp r ds
                                 (lambda (v2)
                                   (k (num+ v1 v2)))
                                 catcher))
                       catcher)]
    [sub (l r) (interp l ds
                       (lambda (v1)
                         (interp r ds
                                 (lambda (v2)
                                   (k (num- v1 v2)))
                                 catcher))
                       catcher)]
    [id (name) (k (lookup name ds))]
    [fun (param body-expr)
         (k (closureV param body-expr ds))]
    [app (fun-expr arg-expr)
         ;(begin 
          ;(print "fun-expr" fun-expr) (print  "arg-expr" arg-expr)
           (interp fun-expr ds
                   (lambda (fun-val)
                     (interp-many arg-expr ds
                                  (lambda (arg-vals)
                                    (type-case KCFAE-Value fun-val
                                      [closureV (params body ds)
                                                (cond
                                                  [(not (= (length arg-vals) (length params)))
                                                   (error 'interp "Different number of args")]
                                                [else (interp body
                                                        (add-sub params
                                                                 arg-vals
                                                                 ds)
                                                        k catcher)]
                                                )]
                                      [contV (k)
                                             (k (first arg-vals))]
                                      [else (error 'interp "not a function")]))
                                  catcher))
                   catcher)
           
           ;)
         ]
    [if0 (test-expr then-expr else-expr)
         (interp test-expr ds
                 (lambda (v)
                   (if (numzero? v)
                       (interp then-expr ds k catcher)
                       (interp else-expr ds k catcher)))
                 catcher)]
    [withcc (id body-expr)
            (interp body-expr 
                    (aSub id
                          (contV k)
                          ds)
                    k catcher)]
    [try-catch (try-expr catch-expr) 
               (interp try-expr ds k
                       (lambda ()
                         (interp catch-expr ds k catcher))
                       )]
    [throw () (catcher)]))
;; interp-many: (listof KCFAE) DefrdSub (KCFAE-Value -> alpha) catcher -> alpha
;; return a procedure from calculating a procedure with a list of arguments and exception handler
(define (interp-many list_of_expr ds k catcher)
  (cond
    [(empty? list_of_expr) (k empty)]
    [else (interp (first list_of_expr) ds 
                  (lambda (val) ;interp-many of the first element will return 1 value
                    (interp-many (rest list_of_expr) ds 
                                 (lambda (vals) (k (cons val vals))) ; interp-many of the rest will return a list
                                 catcher))
                  catcher)
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
  (type-case KCFAE-Value (interp a-fae 
                                 (mtSub) 
                                 (lambda (x) x) 
                                 (lambda () (error 'interp "undefined")))
    [numV (n) n]
    [closureV (param body ds) 'function]
    [contV (k) 'function]))

; run : string -> number-or-'function
;; evaluate a KCFAE program contained in a string
(define (run str)
  (interp-expr (parse str)))

(test (run "{{fun {x y} {- y x}} 10 12}") 2)
(test (run "{{fun {x y} {- y x}} {+ 8 2} {- 16 4}}") 2)
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
(test (run "{{fun {x} {- x 12}} {+ 1 17}}")
      6)
(test (run "{{fun {x} {{fun {f} {+ {f 1} {{fun {x} {f 2}} 3}}}
                         {fun {y} {+ x y}}}}
               0}")
      3)
(test (run "{withcc k {k 10}}")
      10)
(test (run "{withcc k {+ {k 10} 17}}")
      10)

(test (run "{try 7 catch 8}")
      7)

(test (interp-expr (try-catch (num 7) (num 8)))
      7)
;;
(test (run "{try {throw} catch 8}")
      8)

(test (interp-expr (try-catch (throw) (num 8))) 
      8)


(test (run "{try {+ 1 {throw}} catch 8}")
      8)
(test (run "{{fun {f} {try {f 3} catch 8}}
               {fun {x} {throw}}}")
      8)
(test (run "{try {try {throw} catch 8} catch 9}")
      8)
(test (run "{try {try {throw} catch {throw}} catch 9}")
      9)
(test (run "{try {try 7 catch {throw}} catch 9}")
      7)
(test (run "{{withcc esc {try {{withcc k {esc k}} 0} catch {fun {x} 8}}}
               {fun {x} {throw}}}")
      8)

(test/exn (run "{try {+ 1 {throw}} catch {throw}}")
          "interp: undefined")

(test/exn (run 1) "ring->sexpr: expects argument of type <string>")
(test/exn (run "'") "syntax error (bad contents)")
(test/exn (run "{+ 1 1} {+ 2 2}") "bad syntax (multiple expressions)")
;; Test for checkig the number of args
(test/exn (run "{{fun {x y} {- y x}} 10 12 17}") "interp: Different number of args")
(test/exn (run "{{fun {x y} x} 10} ") "interp: Different number of args")
(test (run "{withcc esc {{fun {x y} x} {esc 3}}}" ) 3)
(test/exn (run "{withcc esc {{fun {x y} x} 1 {esc {{fun {x y} {- y x}} 10 12 17}} 10}}")
          "interp: Different number of args")
(test (run "{withcc esc {{fun {x y} x} 1 {esc {{fun {x y} {- y x}} 10 12}} 10}}") 2)
(test (run "{
        {fun {a} a}
              {withcc esc {{fun {x y} x} 1 {esc {{fun {x y} {- y x}} 10 12}} 10}}
        }") 2)

