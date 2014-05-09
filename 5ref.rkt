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


;  <FunDef> = {deffun {<id> <id>*} <F1WAE>}
;  <F1WAE> = <number>
;          | {+ <F1WAE> <F1WAE>}
;          | {- <F1WAE> <F1WAE>}
;          | {with {<id> <F1WAE>} <F1WAE>}
;          | <id>
;          | {<id> <F1WAE>*}
;          | {rec {<id> <F1WAE>}*}
;          | {get <F1WAE> <id>
(define-type F1WAE
  [num (n number?)]
  [add (lhs F1WAE?)(rhs F1WAE?)]
  [sub (lhs F1WAE?)(rhs F1WAE?)]
  [with (name symbol?)(named-expr F1WAE?)(body F1WAE?)]
  [id (name symbol?)]
  [app (fun-name symbol?)(args (list-of? F1WAE?))]
  [rec (fields (list-of? SymExprPair?))]
  [get (r F1WAE?)(id symbol?)])

(define-type FunDef
  [fundef (name symbol?)
          (arg-names list?)
          (body F1WAE?)])

(define-type F1WAE-Val
  [num-val (n number?)]
  [rec-val (r rec?)])

;; ive chosen to represent records as an F1WAE containing 
;; a list of SymExprPair. 
(define-type SymExprPair [symExprPair (name symbol?)(expr F1WAE?)])

;; utility
(define (list-of? t) (lambda (l) (andmap t l)))

;; parse : sexpr -> F1WAE
(define (parse sexpr)
  (cond
    [(number? sexpr) (num sexpr)]
    [(symbol? sexpr) (id sexpr)]
    [(list? sexpr)
     (case (first sexpr)
       [(+) (add (parse (second sexpr)) (parse (third sexpr)))]
       [(-) (sub (parse (second sexpr)) (parse (third sexpr)))]
       [(with) (parse-with sexpr)]
       [(deffun) (parse-defn sexpr)]
       [(rec) (parse-rec sexpr)]
       [(get) (get (parse (second sexpr)) (third sexpr))]
       ;; assume any other symbols are function names, therefore application.
       [else (app (first sexpr) (map parse (cdr sexpr)))]
       )]
    [else (error "unexpected token")]
    ))

;; parse-with : sexpr -> rec
(define (parse-with sexpr)
  (with (first (second sexpr)) 
        (parse (second (second sexpr))) 
        (parse (third sexpr))))

;; parse-rec : sexpr -> rec
(define (parse-rec sexpr)
  (let ([dummy 
         (check-for-dups 
          (map (lambda (x) (first x)) (cdr sexpr)) "duplicate fields")])
    (rec (map (lambda (x) 
                (symExprPair (first x)(parse (second x)))) 
              (cdr sexpr)))))

;; parse-defn : sexpr -> FunDef
(define (parse-defn sexpr)
  (cond
    [(list? sexpr)
     (case (first sexpr)
       [(deffun) (fundef (first (second sexpr)) 
                         (check-for-dups (cdr (second sexpr)) "bad syntax")
                         (parse (third sexpr)))]
       )]
    [else (error "unexpected token")]))

(define (check-for-dups l error-message)
  (if (same-size l (remove-duplicates l symbol=?))
      l
      (error error-message)))

;; fundef-lookup : sym list-of-FunDef -> FunDef
(define (fundef-lookup fname l)
  (find-or-die
   (lambda (f) (symbol=? (fundef-name f) fname)) l 
   (string-append "undefined function: " (symbol->string fname))))
  
;; subst : F1WAE sym F1WAE-Val -> F1WAE
(define (subst expr sub-id val)
  (type-case F1WAE expr
    [num (n) expr]
    [add (l r) 
                (add (subst l sub-id val)(subst r sub-id val))]
    [sub (l r) (sub (subst l sub-id val)(subst r sub-id val))]
    [with (bound-id named-expr body-expr)
      (with bound-id 
        (subst named-expr sub-id val)
        (if (symbol=? bound-id sub-id)
            body-expr
            (subst body-expr sub-id val)))]
    ;; i dont really feel comfortable turning an already evaluated
    ;; expression back into an F1WAE that needs to be re-evaluated.
    ;; TODO - maybe i can find a way to avoid this.
    [id (name) (if (symbol=? name sub-id) (f1wae-val->f1wae val) expr)]
    [app (fname arg-exprs)
         (app fname (map (lambda (x) (subst x sub-id val)) arg-exprs))]
    [rec (fields) 
      (rec (map (lambda (x) 
                  (symExprPair (symExprPair-name x)
                               (subst (symExprPair-expr x) sub-id val))) 
                fields))]
    [get (rec id) (get (subst rec sub-id val) id)]
    )
  )

;; substN: F1WAE list-of-sym list-of-F1WAE-Val -> F1WAE
;; for each id in sub-ids, substitute in expr the corresponding val from vals
;; TODO - maybe this can be changed to use foldl
(define (subst-N expr sub-ids vals)
  (cond [(empty? sub-ids) expr]
        [else (subst-N (subst expr (first sub-ids)(first vals)) 
                      (cdr sub-ids) (cdr vals))]))

;; f1wae-val->f1wae : f1wae-val -> f1wae
;; turns an f1wae-val back into an f1wae
(define (f1wae-val->f1wae v)
  (type-case F1WAE-Val v
    [num-val (n) (num n)]
    [rec-val (r) r]))
  
;; math functions
(define (add-vals left right) (math-with-vals left right +))
(define (sub-vals left right) (math-with-vals left right -))
(define (math-with-vals left right op)
  (if (and (num-val? left)(num-val? right))
      (num-val (op (num-val-n left) (num-val-n right)))
      (error "cant do math on records")))

;; find-in-record : rec sym -> F1WAE
(define (find-in-record rec id)
  (symExprPair-expr 
   (find-or-die 
    (lambda (f) (symbol=? (symExprPair-name f) id)) 
    (rec-fields rec) 
    "no such field")))

;; utility types and functions
;; Scala's Option, Maybe in Haskell.
(define-type Option [none] [some (v (lambda (x) #t))])
  
;; Like findf, but returns the (some element) or (none) 
;; instead of the element or #f.
;; i did this because i don't feel comfortable with findf returning false
;; what if the very thing that you are looking for is #f ?
;; how would you know if #f was in the list or not?
;; find [T]: (T => Boolean) List[T] -> Option[T]
(define (findo p l)
  (cond [(empty? l) (none)]
        [(p (first l)) (some (first l))]
        [else (findo p (cdr l))]))
;; find-or-die: predicate list[T] string -> T
(define (find-or-die p l error-string)
  (type-case Option (findo p l) [some (v) v] [none () (error error-string)]))
;; same-size: list list -> boolean
(define (same-size l r) (= (length l)(length r)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; interp-expr : F1WAE list-of-FunDef -> num or 'record
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (interp-expr expr defs)
  (type-case F1WAE-Val (interp expr defs)
    [num-val (n) n]
    [rec-val (r) 'record]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; interp : F1WAE list-of-FunDef -> F1WAE-Val
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (interp expr defs)
  (type-case F1WAE expr
    [num (n) (num-val n)]
    [add (l r) (add-vals (interp l defs) (interp r defs))]
    [sub (l r) (sub-vals (interp l defs) (interp r defs))]
    [with (bound-id named-expr body-expr)
      (interp (subst body-expr bound-id (interp named-expr defs)) defs)]
    [id (name) (error 'interp "free identifier")]
    [app (fname arg-exprs)
         (local [(define f (fundef-lookup fname defs))]
           (if (= (length (fundef-arg-names f))(length arg-exprs))
               (case (length arg-exprs)
                 [(0) (interp (fundef-body f) defs)]
                 [else (interp 
                        (subst-N (fundef-body f) 
                                 (fundef-arg-names f) 
                                 (map (lambda (x) (interp x defs)) arg-exprs))
                        defs)])
               (error "wrong arity")))
         ]
    [rec (fields) (rec-val expr)]
    [get (rec id) 
         (interp (find-in-record (rec-val-r (interp rec defs)) id) defs)]
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; parser tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (run string list)
  (interp-expr
   (parse (string->sexpr string))
   list)
  )

(interp 
 (parse (string->sexpr "{f 1 2}"))
  (list (parse-defn '{deffun {f a b} {+ a b}})) )
(interp (parse (string->sexpr "{+ {f} {f}}"))
        (list (parse-defn '{deffun {f} 5})))
(test/exn (run "{bleh}" empty) "bad syntax")
(test (run "{with {x 2} {- {+ x x} x}}" empty) 2)
