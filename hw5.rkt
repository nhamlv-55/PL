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

(define (string->sexp str)
  (unless (string? str)
    (error 'string->sexp "expects argument of type <string>"))
    (unless (regexp-match expr-re str)
      (error 'string->sexp "syntax error (bad contents)"))
    (let ([sexps (read-from-string-all
                 (regexp-replace*
                  "''" (regexp-replace* string-re str "\"\\1\"") "'"))])
    (if (= 1 (length sexps))
      (car sexps)
      (error 'string->sexp "bad syntax (multiple expressions)"))))

;;FunDef abstract syntax trees
(define-type FunDef
  [fundef (fun-name symbol?)
          (arg-name (listof symbol?))
          (body FnWAE?)]
  )
;;A Tuple
(define-type Tuple
  [tuple (id symbol?) (sexp FnWAE?)])

;;FnWAE abstract syntax trees
(define-type FnWAE
  [num (n number?)]
  [add (lhs FnWAE?) (rhs FnWAE?)]
  [sub (lhs FnWAE?) (rhs FnWAE?)]
  [with (name symbol?) (named-expr FnWAE?) (body FnWAE?) ]
  [id (name symbol?)]
  [app (ftn symbol?) (arg (listof FnWAE?))]
  [rec (fields (listof Tuple?))]
  [get (r FnWAE?) (id symbol?)]
  )



(define (parse sexp)
  (cond
    [(number? sexp) (num sexp)]
    [(symbol? sexp) (id sexp)]
    [(list? sexp)
     (case (first sexp)
       [(+) (add (parse (second sexp)) (parse (third sexp)))]
       [(-) (sub (parse (second sexp)) (parse (third sexp)))]
       [(with) ((with (first (second sexp)) 
                      (parse (second (second sexp))) 
                      (parse (third sexp))))]
       [(rec) (parse-rec sexp)]
       [(get) (get (parse (second sexp)) (third sexp))]
       [else (app (first sexp) (map parse (rest sexp)))]
       )
     ]
    [else (error 'parse "bad syntax: ~a" sexp)]
    )
  )


;; parse-rec : sexp -> rec
(define (parse-rec sexp)
  (let ([dummy 
         (check-dup
          (map (lambda (x) (first x)) (rest sexp)) )])
    (rec (map (lambda (x) 
                (tuple (first x)(parse (second x)))) 
              (rest sexp)))))



;check-dup: check if there is duplicate in rec
(define (check-dup l)
  (if (= (length l) (length (remove-duplicates l symbol=?)))
      l
      (error "duplicate fields")))

;parse-defn: sexp -> FunDef
(define (parse-defn sexp)
  (match sexp
    ;change here
    [(list 'deffun (list f x ...) body)
    ;end change
     (unless (uniq? x)
       (error 'parse-defn "bad syntax"))
     (fundef f x (parse body))]))

;member?: element list ->bool
;a helper function to check whether an element is in the list
(define (member? element list)
  (cond
    [(null? list) false]
    [(symbol=? (first list) element) true]
    [else (member? element (rest list))])
  )
; uniq?: list-of-symbol -> bool
(define (uniq? l)
  (cond 
    [(null? l) true]
    [else (and (not (member? (first l) (rest l) ))
              (uniq? (rest l)))]
    ))
;test
;(define list1 (list 'x 'y))
;(uniq? list1)
; lookup-fundef : symbol list-of-FunDef -> FunDef
(define (lookup-fundef name fundefs)
  (cond
    [(empty? fundefs) (display name)]
    [else
      (if (symbol=? name (fundef-fun-name (first fundefs)))
      (first fundefs)
      (lookup-fundef name (rest fundefs)))]))

;; lookup-rec : rec sym -> F1WAE
(define (lookup-rec id rec)
  (tuple-sexp 
   (find-a-tuple 
    (lambda (f) (symbol=? (tuple-id f) id)) 
    (rec-fields rec) 
    )
   )
  )

; subst : FnWAE symbol number -> FnWAE
(define (subst fnwae x val)
  (type-case FnWAE fnwae
    [num (n) fnwae]
    [add (l r) (add (subst l x val) (subst r x val))]
    [sub (l r) (sub (subst l x val) (subst r x val))]
    [with (y i b) (with y (subst i x val)
                          (if (symbol=? y x) b
                          (subst b x val)))]
    [id (s) (if (symbol=? s x) (convert val) fnwae)]
    [app (f args) 
    ;(app f (subst a x val))]))
    ;subst each element e of the list args
                (app f (map (lambda (e) (subst e x val)) args))]
    [rec (fields) 
      (rec (map (lambda (e) 
                  (tuple (tuple-id e)
                               (subst (tuple-sexp e) x val))) 
                fields))]
    [get (rec id) (get (subst rec x val) id)]
  )
)
    
; substN: F1WAE list-of-sym list-of-FnWAE-Val -> FnWAE
; for each id in xs, substitute in expr the corresponding val from vals
(define (substN fnwae xs vals)
  (cond [(empty? xs) fnwae]
        [else (substN (subst fnwae (first xs)(first vals)) 
                      (rest xs) (rest vals))]))
; define the return type of interp 
(define-type Return-Val
  [numV (n number?)]
  [recV (r rec?)])

;; find-a-tuple: predicate list[Tuple] -> tuple
(define (find-a-tuple p l)
  (cond 
    [(findf p l) (findf p l)] 
    [else (error "no such field")])
  )

; operators on val
;+
(define (add-vals left right )
  (if (and (numV? left)(numV? right))
      (numV (+ (numV-n left) (numV-n right)))
      (error "cant do math on records")))
;-
(define (sub-vals left right )
  (if (and (numV? left)(numV? right))
      (numV (- (numV-n left) (numV-n right)))
      (error "cant do math on records")))
;convert: Return-Val -> num or record
;To convert a return value to its true type
(define (convert v)
  (type-case Return-Val v
    [numV (n) (num n)]
    [recV (r) r]))

; interp : FnWAE list-of-FunDef -> number
(define (interp fnwae fundefs)
  (type-case FnWAE fnwae
    [num (n) (numV n)]
    [add (l r) (add-vals (interp l fundefs) (interp r fundefs))]
    [sub (l r) (sub-vals (interp l fundefs) (interp r fundefs))]
    [with (x i b) (interp (subst b x (interp i fundefs))
                          fundefs)]
    [id (s) (error 'interp "free variable")]
    [app (f args)
          (local [(define a-fundef (lookup-fundef f fundefs))]
            ;TODO: check if there is no argument at all?
            (cond
              [(= (length args) (length (fundef-arg-name a-fundef)))
               (interp (substN  (fundef-body a-fundef) ;(add (id 'x) (id 'y))
                            (fundef-arg-name a-fundef) ;'(x y)
                            (map (lambda (e) (interp e fundefs)) args)) ;'
                    fundefs)]
              [else (error "wrong arity")])
            )]
    [rec (fields) (recV (rec (map (lambda (t) (interp-tuple t fundefs)) fields)))]
    [get (rec id)
         (interp (lookup-rec id (recV-r (interp rec fundefs)) ) fundefs)]
    )
  )

;interp-tuple: tuple list-of-function tuple
(define (interp-tuple t fundefs)
  ;(display t)
  (type-case Tuple t
    [tuple (idt sexpt) (tuple idt (convert (interp sexpt fundefs)))]
    )
  )
;test
;(define tup1 (tuple 'x (add (num 1) (num 2))))
;(interp-tuple tup1 empty)
;interp-expr
(define (interp-expr fnwae fundefs)
  (type-case Return-Val (interp fnwae fundefs)
    [numV (n) n]
    [recV (r) 'record]))

; run : string -> listof number
(define (run string list)
  (interp-expr
   (parse (string->sexp string))
   list)
  )
;; evaluate a MUWAE program contained in a string
;(parse (string->sexp "{f 1 2}"))
;(list (parse-defn '{deffun {f x y} {+ x y}}))

;(interp (num 1) (list (parse-defn '{deffun {f x y} {+ x y}})) )
;(map (lambda (e) (interp e (list (parse-defn '{deffun {f x y} {+ x y}})))) (list (num 1) (num 2)))


(test/exn (run "{rec {z {get {rec {a 0}} y}}}" empty)
          "no such field")
(test (run "{f 1 2}" (list (parse-defn '{deffun {f x y} {+ x y}}))) 3)
(test (run "{+ {f} {f}}" (list (parse-defn '{deffun {f} 5}))) 10)
(test/exn (run "{f 1}" (list (parse-defn '{deffun {f x y} {+ x y}})))
          "wrong arity")
(test (run "{rec {a 10} {b {+ 1 2}}}" empty)
      'record)
(test (run "{get {rec {a 10} {b {+ 1 2}}} b}" empty)
      3)
(test/exn (run "{get {rec {b 10} {b {+ 1 2}}} b}" empty)
          "duplicate fields")
(test/exn (run "{get {rec {a 10}} b}" empty)
          "no such field")
(test (run "{g {rec {a 0} {c 12} {b 7}}}"
           (list (parse-defn '{deffun {g r} {get r c}})))
      12)
(test (run "{get {rec {r {rec {z 0}}}} r}" empty)
      'record)
(test (run "{get {get {rec {r {rec {z 0}}}} r} z}" empty)          
      0)

(test (run "{+ 1 2}" (list (parse-defn '{deffun {f x y} { + x y}}) (parse-defn '{deffun {f x} {+ x x}}))) 3)