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
;;----------Set debug mode-----------
(define debug 0)


;print: a helper function to print things nicely
;(define (print comment x)
;  (cond
;    [(= 1 debug)
;     (begin
;       (display comment)
;       (display x)
;       (display "\n"))]
;    [else (void)]))
  ;;--------------------------------------------------------

  (define-type WFAE 
    [num (n number?)]
    [add (lhs WFAE?)
         (rhs WFAE?)]
    [sub (lhs WFAE?)
         (rhs WFAE?)]
    [id (name symbol?)]
    [fun (param symbol?)
         (body WFAE?)]
    [with (name symbol?)
          (named-expr WFAE?)
          (body-expr WFAE?)]
    [app (fun-expr WFAE?)
         (arg-expr WFAE?)]
    )
 
  (define-type CWFAE 
    [cnum (n number?)]
    [cadd (lhs CWFAE?) (rhs CWFAE?)]
    [csub (lhs CWFAE?) (rhs CWFAE?)]
    [cwith (named-expr CWFAE?) (body-expr CWFAE?)]
    [cid (pos number?)]
    [cfun (body CWFAE?)]
    [capp (fun-expr CWFAE?) (arg-expr CWFAE?)]
    )
  ;;
  (define-type CWFAE-Value
    [numV (n number?)]
    [closureV (body CWFAE?) (ds DefrdSub?)])
  
  ;;
  (define-type CDefrdSub
    [mtCSub]
    [aCSub (name symbol?)
           (rest CDefrdSub?)])
  
  (define-type CWFAE-Cont
    [mtK]
    [addSecondK (r CWFAE?)
                (ds DefrdSub?)
                (k CWFAE-Cont?)]
    [doAddK (v1 CWFAE-Value?)
            (k CWFAE-Cont?)]
    [subSecondK (r CWFAE?)
                (ds DefrdSub?)
                (k CWFAE-Cont?)]
    [doSubK (v1 CWFAE-Value?)
            (k CWFAE-Cont?)]
    [appArgK (arg-expr CWFAE?)
             (ds DefrdSub?)
             (k CWFAE-Cont?)]
    [appNamedExprK (named-expr CWFAE?)
             (ds DefrdSub?)
             (k CWFAE-Cont?)]
    [doAppK (fun-val CWFAE-Value?)
            (k CWFAE-Cont?)]
    )
  (define (DefrdSub? x) true)
  ;;TODO: add with
  ;; parse-sexpr : S-expr -> WFAE
  (define (parse-sexpr sexp)
    (cond
      [(number? sexp) (num sexp)]
      [(symbol? sexp) (id sexp)]
      [(pair? sexp)
       (case (car sexp)
         [(+) (add (parse-sexpr (second sexp))
                   (parse-sexpr (third sexp)))]
         [(-) (sub (parse-sexpr (second sexp))
                   (parse-sexpr (third sexp)))]
         [(fun) (fun (first (second sexp))
                     (parse-sexpr (third sexp)))]
         
         [(with) 
          (begin
            ;(print "sexp" sexp)
            ;(print "first-sexp" (second sexp))
          (with (first (second sexp))
                       (parse-sexpr (second (second sexp)))
                       (parse-sexpr (third sexp))
                       )
          )]
         [else (app (parse-sexpr (first sexp))
                    (parse-sexpr (second sexp)))])]))
  
  
  
  ;; parse: string -> WFAE
  ;; parses a string containing a WFAE expression to a WFAE AST
  (define (parse str)
    (parse-sexpr (string->sexpr str)))
  

  ;; compile : WFAE CDefrdSub -> CWFAE
  (define (compile wfae ds)
    (type-case WFAE wfae
      [num (n) (cnum n)]
      [add (l r) (cadd (compile l ds) (compile r ds))]
      [sub (l r) (csub (compile l ds) (compile r ds))]
      [id (name) (cid (locate name ds))]
      [with (id named-expr body-expr)
            ;(print "with:cnamed-expr:" named-expr)
            (cwith (compile named-expr ds)
                   (compile body-expr (aCSub id ds)) )
            ]
      [fun (param body)
           (cfun (compile body (aCSub param ds)))]
      [app (fun-expr arg-expr)
           (capp (compile fun-expr ds) (compile arg-expr ds))]
      )
    )
  ;; locate : symbol CDefrdSub -> number
  ;; return the position of a symbol in the list
  (define (locate name ds)
    (type-case CDefrdSub ds
      [mtCSub () (error 'locate "free variable")]
      [aCSub (sub-name rest-ds)
             (if (symbol=? sub-name name)
                 0
                 (+ 1 (locate name rest-ds)))]))


  ;;helper function to deal with num op bullshit
  ;; num-op : (number number -> number) -> (KCFAE-Value KCFAE-Value -> KCFAE-Value)
  (define (num-op op)
    (lambda (x y)
      (numV (op (numV-n x) (numV-n y)))))
  
  (define num+ (num-op +))
  (define num- (num-op -))
  ;;--------------------------------------------------------------------
  ;;global register
  (define cwfae-reg (cnum 0))
  (define k-reg (mtK))
  (define v-reg (numV 0))
  (define ds-reg empty)
  ;;------something something dark side--------
  ;;temp register for search function
  (define ds2-reg 0)
  ;;search: Search the value at v-reg from the ds2-reg
  (define (search)
    (if (zero? v-reg)
        (begin
          ;(print "ds2" ds2-reg)
          (set! v-reg (first ds2-reg))
          (continue))
        (begin
          (set! ds2-reg (rest ds2-reg))
          (set! v-reg (- v-reg 1))
          (search))))
  ;;-----------------------------------------------
  ;;helper function to help debugging
;  (define (print-debug)
;    (begin
;      (print "----------interp" (void))
;      (print "cwfae" cwfae-reg)
;      (print "k-reg" k-reg)
;      (print "ds-reg" ds-reg)
;      (print "v-reg" v-reg)
;      )
;    )
  
  ;; interp : -> CWFAE-Value
  (define (interp)
    (begin
      ;(print "ds" ds-reg)
      ;(print-debug)
      (type-case CWFAE cwfae-reg
        [cnum (n) 
              (begin
                ;(print "cwfae" cwfae-reg)
                (set! v-reg (numV n))
                (continue))]
        [cadd (l r)
              (begin
                (set! cwfae-reg l)
                (set! k-reg (addSecondK r ds-reg k-reg))
                (interp)
                )
              ]
        [csub (l r)
              (begin
                (set! cwfae-reg l)
                (set! k-reg (subSecondK r ds-reg k-reg))
                (interp)
                )
              ]
        [cwith ( body-expr named-expr) 
               (begin
                 ;...              
                 (set! k-reg (appNamedExprK named-expr ds-reg k-reg))
                 (set! cwfae-reg body-expr)
                 
                 (interp))]
        [cid (pos) 
             (begin
               (set! ds2-reg ds-reg)
               (set! v-reg pos)
               (search))]
        [cfun (body-expr)
              (begin
                (set! v-reg (closureV body-expr ds-reg))
                (continue))]
        [capp (fun-expr arg-expr)
              (begin
                ;(print "fun-expr" fun-expr)
                ;(print "arg-expr" arg-expr)
                (set! k-reg (appArgK arg-expr ds-reg k-reg))
                (set! cwfae-reg fun-expr)
                
                (interp))]
        )
      )
    )
  
  ;; continue : -> CWFAE-Value
  (define (continue)
    (begin
      ;(display "continue\n")
      ;(print-debug)
      (type-case CWFAE-Cont k-reg
        [mtK ()
             v-reg]
        [addSecondK (r ds k)
                    (begin
                      (set! cwfae-reg r)
                      (set! ds-reg ds)
                      (set! k-reg (doAddK v-reg k))
                      (interp))]
        [doAddK (v1 k) 
                (begin
                  (set! v-reg (num+ v1 v-reg))
                  (set! k-reg k)
                  (continue))]
        [subSecondK (r ds k)
                    (begin
                      (set! cwfae-reg r)
                      (set! ds-reg ds)
                      (set! k-reg (doSubK v-reg k))
                      (interp))]
        [doSubK (v1 k) 
                (begin
                  (set! v-reg (num- v1 v-reg))
                  (set! k-reg k)
                  (continue))]
        [appArgK (arg-expr ds k)
                 (begin
                   ;...
                   (set! cwfae-reg arg-expr)
                   (set! ds-reg ds)
                   (set! k-reg (doAppK v-reg k))
                   (interp))]
        [appNamedExprK (named-expr ds k)
                 (begin
                   ;...
                   ;(print "appNamedExprK" 0)
                   (set! cwfae-reg named-expr)
                   (set! ds-reg (cons v-reg ds))
                   (set! k-reg k)
                   (interp))]
        [doAppK (fun-val k)
                (begin
                  ;...
                  ;(print "fun-val" fun-val)
                  
                  (set! cwfae-reg (closureV-body fun-val ))
                  (set! ds-reg (cons v-reg  (closureV-ds fun-val)))
                  (set! k-reg k)
                  (interp))]
        )
      ))
  
  ;; init : void -> void
  (define (init)
    (set! k-reg (mtK))
    (set! v-reg (numV 0))
    (set! ds-reg empty))
  ;; helper function to help running some tests
  (define (interp-with-default-init smt)
    (begin
      (init)
      (set! cwfae-reg smt)
      (interp)
      )
    )
  
  ;; run : string -> CWFAE-Value
  ;; evaluate a WFAE program contained in a string
  (define (run str)
    (begin
      (set! cwfae-reg (compile (parse str) (mtCSub)))
      (init)
      (interp)))
  ;;;...
  ;;passed tests
  (test (run "10") (numV 10))
  (test (run "{+ 10 7}") (numV 17))
  (test (run "{- 10 7}") (numV 3))
  (test (run "{{fun {x} {+ x 12}} {+ 1 17}}") (numV 30))
  (test (run "{{fun {x} {{fun {f} {+ {f 1} {{fun {x} {f 2}} 3}}}
                       {fun {y} {+ x y}}}} 0}") (numV 3))
  (test (interp-with-default-init (compile
                 (app (fun 'x (add (id 'x) (num 12)))
                      (add (num 1) (num 17)))
                 (mtCSub))
                )
       (numV 30))
(test (run "{with {x 5} {+ x x}}") (numV 10))
(test (run "{with {x {with {a 1} {+ a 4}}} {+ x x}}" ) (numV 10))
(test (run "{with {x 5} {+ x {with {x 3} x}}}") (numV 8))
(test (run "{with {y 5} {+ 3 {with {x 3} y}}}") (numV 8))
(test (run "5" ) (numV 5))
(test (run "{+ 5 5}" ) (numV 10))
(test (run "{with {x {+ 5 5}} {+ x x}}" ) (numV 20))
(test (run "{with {x 5} {+ x x}}" ) (numV 10))
(test (run "{with {x {+ 5 5}} {with {y {- x 3}} {+ y y}}}" ) (numV 14))
(test (run "{with {x 5} {with {y {- x 3}} {+ y y}}}" ) (numV 4))
(test (run "{with {x 5} {+ x {with {x 3} 10}}}" ) (numV 15))
(test (run "{with {x 5} {+ x {with {x 3} x}}}" ) (numV 8))
(test (run "{with {x 5} {+ x {with {y 3} x}}}" ) (numV 10))
(test (run "{with {x 5} {with {y x} y}}" ) (numV 5))
(test (run "{with {x 5} {with {x x} x}}" ) (numV 5))
(test (run "{{fun {x} {- x 12}} {+ 1 17}}")
      (numV 6))
(test (run "{with {x 5} {+ x {with {x 3} x}}}") (numV 8))
(test (run "{with {y 5} {+ 3 {with {x 3} y}}}") (numV 8))
(test (run "{with {x {+ 5 5}} {+ x x}}") (numV 20))
(test (run "{with {x 5} {+ x x}}") (numV 10))
(test (run "{with {x {+ 5 5}} {with {y {- x 3}} {+ y y}}}") (numV 14))
(test (run "{with {x 5} {with {y {- x 3}} {+ y y}}}") (numV 4))
(test (run "{with {x 5} {+ x {with {x 3} 10}}}") (numV 15))
(test (run "{with {x 5} {+ x {with {x 3} x}}}") (numV 8))
(test (run "{with {x 5} {+ x {with {y 3} x}}}") (numV 10))
(test (run "{with {x 5} {with {y x} y}}") (numV 5))
(test (run "{with {x 5} {with {x x} x}}") (numV 5))

(test (run "{{fun {x} {+ {with {x 32} x} 10}} 42}") (numV 42))
;(test (run "{{{fun {x} {fun {y} x}} 13}}") (numV 13)) 

(test/exn (run "{with {x 5} {with {x y} x}}") "free variable")
(test/exn (run 1) "ring->sexpr: expects argument of type <string>")
(test/exn (run "'") "syntax error (bad contents)")
(test/exn (run "{+ 1 1} {+ 2 2}") "bad syntax (multiple expressions)")