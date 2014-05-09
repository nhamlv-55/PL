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
    (let ([sexps (read-from-string-all
                 (regexp-replace*
                  "''" (regexp-replace* string-re str "\"\\1\"") "'"))])
    (if (= 1 (length sexps))
      (car sexps)
      (error 'string->sexpr "bad syntax (multiple expressions)"))))

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


;old-version of parse
; parse-sexpr : sexpr -> MUWAE
; to convert s-expressions into MUWAEs
(define (parse sexp)
  (match sexp
    [(? number?) (num sexp)]
    [(list '+ l r) (add (parse l) (parse r))]
    [(list '- l r) (sub (parse l) (parse r))]
    [(list 'with (list x i) b) (with x (parse i) (parse b))]
    [(list 'rec a ...) (parse-rec sexp)]
    [(list 'get a ...) (get (parse (second sexp)) (third sexp))]
    [(? symbol?) (id sexp)]
    [else (app (first sexp) (map parse (rest sexp)))]
    )
  )

; parse-rec : sexp -> rec
; to convert a s-expressions into a record
(define (parse-rec sexp)
  ;check duplication in the rec
  (let ([doge 
         (check-dup
          (map (lambda (x) (first x)) (rest sexp)) )])
    
    (rec (map (lambda (x) 
                (tuple (first x)(parse (second x)))) 
              (rest sexp)))
    
    )
  )
;parse-with
;(define (parse-with sexpr)
;  (with (first (second sexpr)) 
;        (parse (second (second sexpr))) 
;        (parse (third sexpr))))

;check-dup: list -> bool
;check if there is duplicate in rec
(define (check-dup l)
  (if (= (length l) (length (remove-duplicates l symbol=?)))
      l
      (error "duplicate fields")))

;parse-defn: sexp -> FunDef
; to convert a s-expressions into a FunDef
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
    [(empty? fundefs) (error 'lookup-fundef "unknown function")]
    [else
      (if (symbol=? name (fundef-fun-name (first fundefs)))
      (first fundefs)
      (lookup-fundef name (rest fundefs)))]))

; lookup-rec : rec sym -> FnWAE
; to find a tuple from the records
(define (lookup-rec id rec)
  (tuple-sexp 
   (find-a-tuple 
    (lambda (f) (symbol=? (tuple-id f) id)) 
    (rec-fields rec) 
    )
   )
  )

; subst : FnWAE symbol number -> FnWAE
; to substitute things
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
    
; substN: FnWAE list-of-sym list-of-FnWAE-Val -> FnWAE
; for each id in xs, substitute in expr the corresponding val from vals
; needed for app
(define (substN fnwae xs vals)
  (cond [(empty? xs) fnwae]
        [else (substN (subst fnwae (first xs)(first vals)) 
                      (rest xs) (rest vals))]))
; define the return type of interp 
(define-type Return-Val
  [numV (n number?)]
  [recV (r rec?)])

; find-a-tuple: predicate list[Tuple] -> tuple
; a helper function to find a tuple from the list of tuple. Needed in lookup-rec
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
      (error "I dont know what to do")))
;-
(define (sub-vals left right )
  (if (and (numV? left)(numV? right))
      (numV (- (numV-n left) (numV-n right)))
      (error "I dont know what to do")))

;convert: Return-Val -> num or record
;To convert a return value to its true type
(define (convert v)
  (type-case Return-Val v
    [numV (n) (num n)]
    [recV (r) r]))

; interp : FnWAE list-of-FunDef -> Return-Val
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
(define (run1 string list)
  (interp-expr
   (parse (string->sexpr string))
   list)
  )

(define (run body deffuncs)
    (if (equal? deffuncs "{}")
        (interp-expr (parse (string->sexpr body)) empty )
        (interp-expr (parse (string->sexpr body)) (list (parse-defn (string->sexpr deffuncs))))
    )
)

;; evaluate a MUWAE program contained in a string
;(parse (string->sexpr "{f 1 2}"))
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


(test (run "{with {x 2} {- {+ x x} x}}" empty) '2)
(test/exn (run "{with x = 2 {+ x 3}}" empty) "lookup-fundef: unknown function")
(test/exn (run "{bleh}" empty) "lookup-fundef: unknown function")

(test/exn (run "{with {x 1} y}" empty) "interp: free variable")
(test/exn (run 5 empty) "string->sexpr: expects argument of type <string>")
(test/exn (run "^" empty) "string->sexpr: syntax error (bad contents)")
(test/exn (run "5 5" empty) "string->sexpr: bad syntax (multiple expressions)")

(test/exn (parse-defn '(deffun (f y x y) (+ y 42))) "bad syntax")

(test (run "5" empty) 5)
(test (run "{+ 5 5}" empty) 10)
(test (run "{with {x {+ 5 5}} {+ x x}}" empty) '20)
(test (run "{with {x 5} {+ x x}}" empty) '10)
(test (run "{with {x {+ 5 5}} {with {y {- x 3}} {+ y y}}}" empty) '14)
(test (run "{with {x 5} {with {y {- x 3}} {+ y y}}}" empty) '4)
(test (run "{with {x 5} {+ x {with {x 3} 10}}}" empty) '15)
(test (run "{with {x 5} {+ x {with {x 3} x}}}" empty) '8)
(test (run "{with {x 5} {+ x {with {y 3} x}}}" empty) '10)
(test (run "{with {x 5} {with {y x} y}}" empty) '5)
(test (run "{with {x 5} {with {x x} x}}" empty) '5)

;additional lookup-fundef tests
(test (lookup-fundef 'f (list (fundef 'f (list 'x) (id 'x)))) 
      (fundef 'f (list 'x) (id 'x)))
(test (lookup-fundef 'f (list (fundef 'g '() (id 'x)) (fundef 'f '() (id 'x))   ))
      (fundef 'f '() (id 'x)))

;additional subst tests
(test (subst (app 'f (list (id 'x) (id 'y))) 'x (numV 42)) 
      (app 'f (list (num 42) (id 'y))))
(test (subst (parse '(rec (x y))) 'y (numV 42))
      (rec (list (tuple 'x (num 42)))))
;additional add-val and sub-val tests
(test/exn (interp (parse '(- (rec (x 42)) (rec (x 42)))) empty) 
          "I dont know what to do")
(test/exn (interp (parse '(+ (rec (x 42)) (rec (x 42)))) empty) 
          "I dont know what to do")

(test (run "{get {get {rec {r {rec {z 0}}}} r} z}"  empty) 0)
(test (run "{get {rec {a 1}} a}"                    empty) 1)
(test (run "{get {rec {a 1} {b 2} {c 3}} a}"        empty) 1)
(test (run "{rec {a 10} {b {+ 1 2}}}"               empty) 'record)
(test (run "{get {rec {a 10} {b {+ 1 2}}} b}"       empty) 3)
(test (run "{get {rec {r {rec {z 0}}}} r}"          empty) 'record)
(test (run "{g {rec {a 0}}}"                        "{deffun {g r} {get r a}}") 0)
(test (run "{g {rec {a 0} {c 12} {b 7}}}"           "{deffun {g r} {get r c}}") 12)

(test (run "{f 1 2}"        "{ deffun { f x y } { + x y }}") 3)
(test (run "{+ {f} {f} }"   "{ deffun { f } 5 }") 10)

(test (run "{f}"            "{ deffun { f } 5 }") 5)
(test (run "{+ 1 2}"        "{ deffun { f } 5}") 3)
(test (run "{ f 2 2 3}"     "{ deffun { f a b c} { + a {+ b c}}}") 7)
(test (run "{ f 1 {f 1 3}}" "{ deffun { f a b} {- b a}}") 1)

(test/exn (run "{ f 1 {f x 3}}" "{ deffun { f a b} {- b a}}") "free variable")
(test/exn (run "{ f 1 2 3}"     "{ deffun { f } 5}")    "interp: wrong arity")
(test/exn (run "{ x 1 2}"       "{ deffun { f x x} 5}") "parse-defn: bad syntax")
(test/exn (run "{ x 1 2}"       "{ deffun { y } 5}")    "lookup-deffun: unknown function")
(test/exn (run "{f 1}"      "{ deffun { f x y } { + x y }}") "interp: wrong arity")
(test/exn (run "{rec {z {get {rec {z 0}} y}}}"      empty) "interp: no such field")
(test/exn (run "{get {rec {b 10} {b {+ 1 2}}} b}"   empty) "parse: duplicate fields")
(test/exn (run "{get {rec {a 10}} b}"               empty) "no such field")

;; add.tests.0
(test/exn (run 1 empty) "ring->sexpr: expects argument of type <string>")
(test/exn (run "'" empty) "syntax error (bad contents)")
(test/exn (run "{+ 1 1} {+ 2 2}" empty) "bad syntax (multiple expressions)")

;; add.tests.1
(test (run "{with {x 5} {+ x x}}" empty) 10)
(test (run "{with {x {with {a 1} {+ a 4}}} {+ x x}}" empty) 10)
(test (run "{with {x 5} {+ x {with {x 3} x}}}" empty) 8)
(test (run "{with {y 5} {+ 3 {with {x 3} y}}}" empty) 8)
(test (run "{with {y 5} { f y }}" "{ deffun {f x } x}") 5)
(test (run "{with {x 4} {rec {a x}}}"  empty) 'record)
(test (run "{with {x 4} {get {rec {a x}} a}}"  empty) 4)

;; add.tests.2
;(define b (fromtorec (list (list 'a (list (list 'b (list (list 'numV 2))))))))
;(test b (parse (string->sexpr "{rec {a {rec {b 2}}}}")))

(test (run "{with {x {rec {a 0}}} {get x a}}" empty) 0)
;(define a (fromtorec (list (list 'a (list (list 'numV 2))))))
;(test a (parse (string->sexpr "{rec {a 2}}")))
