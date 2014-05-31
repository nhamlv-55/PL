#lang plai-typed

(define-type TFAE
  [num (n : number)]
  [bool (b : boolean)]
  [add (lhs : TFAE)
       (rhs : TFAE)]
  [sub (lhs : TFAE)
       (rhs : TFAE)]
  [id (name : symbol)]
  ;;changed fun
  [fun (params : (listof symbol))
       (paramtys : (listof TE))
       (body : TFAE)]
  ;;changed app
  [app (fun-expr : TFAE)
       (arg-exprs : (listof TFAE))]
  ;;added with
  [with (names : (listof symbol))
        (nametys : (listof TE))
        (inits : (listof TFAE))
        (body : TFAE)]
  ;;added try1
  [try1 (try-expr : TFAE)
        (catch-exprs : TFAE)]
  ;;added throw
  [throw]
  [eq (lhs : TFAE)
      (rhs : TFAE)]
  [ifthenelse (pred : TFAE)
              (if-true : TFAE)
              (if-false : TFAE)]
  [pair (first-ele : TFAE)
        (second-ele : TFAE)]
  [fst (pair : TFAE)]
  [snd (pair : TFAE)]
  )

(define-type TE
  [numTE]
  [boolTE]
  [arrowTE (args : (listof TE))
           (result : TE)]
  [crossTE (firstTE : TE)
           (secondTE : TE)]
  )
;------------------------------------------
(define-type TFAE-Value
  [numV (n : number)]
  [closureV (param : (listof symbol))
            (body : TFAE)
            (ds : DefrdSub)]
  [boolV (b : boolean)]
  [pairV (f : TFAE-Value) (s : TFAE-Value)]
  ;[contV (proc : procedure)]
  )
;------------------------------------------
(define-type DefrdSub
  [mtSub]
  [aSub (name : symbol)
        (value : TFAE-Value)
        (rest : DefrdSub)])
;------------------------------------------
(define-type Type
  [numT]
  [boolT]
  [arrowT (param : (listof Type))
          (result : Type)]
  [crossT (f : Type)
          (s : Type)]
  [anyT]
  )
;-------------------------------------------
(define-type TypeEnv
  [mtEnv]
  [aBind (name : symbol)
         (type : Type)
         (rest : TypeEnv)])
;; ----------------------------------------
;;add-bind
(define (add-bind names ts te)
  (cond
    [(empty? names) te]
    [else (
           add-bind (rest names) (rest ts)
                   (aBind (first names) (first ts) te))]))
;; length:
(define (length x)
  (cond
    [(empty? x) 0]
    [else (+ 1 (length (rest x)))])
  )
;;tests for length:

;;add-sub
(define (add-sub names vs ds)
  (cond
    [(empty? names) ds]
    [else (
           add-sub (rest names) (rest vs)
                   (aSub (first names) (first vs) ds))]))

;;----------------------------------------------------
;; interp : TFAE DefrdSub -> TFAE-Value
(define (interp tfae ds k catcher)
  (type-case TFAE tfae
    ;;done with num
    [num (n) (k (numV n))]
    ;;done with bool
    [bool (b) (k (boolV b))]
    ;;done with add
    [add (l r) (interp l ds
                       (lambda (v1)
                         (interp r ds
                                 (lambda (v2)
                                   (k (num+ v1 v2)))
                                 catcher))
                       catcher)]
    ;;done with sub
    [sub (l r) (interp l ds
                       (lambda (v1)
                         (interp r ds
                                 (lambda (v2)
                                   (k (num- v1 v2)))
                                 catcher))
                       catcher)]
    ;;done with id
    [id (name) (k (lookup name ds))]
    ;;done with fun
    [fun (param param-te body-expr)
         (k (closureV param body-expr ds))]
    ;; done with app
    [app (fun-expr arg-exprs)
         ;(begin 
          ;(print "fun-expr" fun-expr) (print  "arg-expr" arg-expr)
           (interp fun-expr ds
                   (lambda (fun-val)
                     (interp-many arg-exprs ds
                                  (lambda (arg-vals)
                                    (type-case TFAE-Value fun-val
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
                                      ;[contV (k)
                                      ;       (k (first arg-vals))]
                                      [else (error 'interp "not a function")]))
                                  catcher))
                   catcher)
           
           ;)
         ]
    ;[eq (l r) (num= (interp l ds) (interp r ds)) ]
    ;;done with eq
    [eq (l r) (interp l ds
                       (lambda (v1)
                         (interp r ds
                                 (lambda (v2)
                                   (k (num= v1 v2)))
                                 catcher))
                       catcher)]

    [ifthenelse (test-expr then-expr else-expr)
         (interp test-expr ds
                 (lambda (v)
                   (if (boolV-b v)
                       (interp then-expr ds k catcher)
                       (interp else-expr ds k catcher)))
                 catcher)]
    
    ;[pair (f s) (pairV (interp f ds) (interp s ds))]
    ;;done with pair
    [pair (l r) (interp l ds
                       (lambda (v1)
                         (interp r ds
                                 (lambda (v2)
                                   (k (pairV v1 v2)))
                                 catcher))
                       catcher)]
    [fst (expr) (type-case TFAE-Value (interp expr ds k catcher)
                  [pairV (f s) (k f)]
                  [else (error 'interp "not a pair")]
                  )]
    [snd (expr) (type-case TFAE-Value (interp expr ds k catcher)
                  [pairV (f s) (k s)]
                  [else (error 'interp "not a pair")]
                  )]

    [with (names nametys inits body) 
          (begin            
            (interp-many inits ds
                         (lambda (arg-vals)
                           (cond
                             [(not (= (length arg-vals) (length names)))
                              (error 'interp "Different number of args")]
                             [else (interp body
                                           (add-sub names
                                                    arg-vals
                                                    ds)
                                           k catcher)]
                             )
                           ) 
                         catcher)
            )
          ]
    [try1 (try-expr catch-expr) 
               (interp try-expr ds k
                       (lambda ()
                         (interp catch-expr ds k catcher))
                       )]
    [throw () (catcher)]
  ))
;---------------------------------------------------------------------
;;--------------------------------------------------------------------
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
;;typecheck-many
(define (typecheck-many list_of_expr te)
  (cond
    [(empty? list_of_expr) empty]
    [else 
     (cons (typecheck (first list_of_expr) te) (typecheck-many (rest list_of_expr) te))
     ]
    )
  )

;; num-op : (number number -> number) -> (TFAE-Value TFAE-Value -> TFAE-Value)
(define (num-op op x y)
  (numV (op (numV-n x) (numV-n y))))

(define (num+ x y) (num-op + x y))
(define (num- x y) (num-op - x y))
(define (num= x y) 
  (boolV (= (numV-n x) (numV-n y)))
  )

(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free variable")]
    [aSub (sub-name num rest-ds)
          (if (symbol=? sub-name name)
              num
              (lookup name rest-ds))]))

;; ----------------------------------------

(define (get-type name-to-find env)
  (type-case TypeEnv env
    [mtEnv () (error 'get-type "free variable, so no type")]
    [aBind (name ty rest)
           (if (symbol=? name-to-find name)
               ty
               (get-type name-to-find rest))]))

;; ----------------------------------------

(define (parse-type te)
  (type-case TE te
    [numTE () (numT)]
    [boolTE () (boolT)]
    ;(type1 type2 type3....) -> (type_result)
    [arrowTE (args r) (arrowT (parse-type-many args)
                           (parse-type r))]
    [crossTE (a b) (crossT (parse-type a)
                           (parse-type b))]
    ))

(define (parse-type-many aList)
  (cond
    [(empty? aList) empty]
    [else
     (cons (parse-type (first aList)) (parse-type-many (rest aList)))]))

(define (type-error tfae msg)
  (error 'typecheck (string-append
                     "no type: "
                     (string-append
                      (to-string tfae)
                      (string-append " not "
                                     msg)))))

(define typecheck : (TFAE TypeEnv -> Type)
  
  (lambda (tfae env)
    (type-case TFAE tfae
      [num (n) (numT)]
      [bool (b) (boolT)]
      [add (l r) (type-case Type (typecheck l env)
                   [numT ()
                         (type-case Type (typecheck r env)
                           [numT () (numT)]
                           [else (type-error r "num")])]
                   [else (type-error l "num")])]
      [sub (l r) (type-case Type (typecheck l env)
                   [numT ()
                         (type-case Type (typecheck r env)
                           [numT () (numT)]
                           [else (type-error r "num")])]
                   [else (type-error l "num")])]
      [id (name) (get-type name env)]
      [fun (names tes body)
           (local [(define param-types (parse-type-many tes))]
             (arrowT param-types
                     (typecheck body (add-bind names
                                            param-types
                                            env))))]
      [app (fn args)
           (type-case Type (typecheck fn env)
             [arrowT (param-types result-type)
                     ;;need to check if all the elements of param-types match all the 
                     ;;elements of the result of typecheck-many
                     (if (equal? param-types
                                 (typecheck-many args env))
                         result-type
                         (type-error args
                                     (to-string param-types)))]
             [else (type-error fn "function")])]
      ;;type-check for eq
      [eq (l r) 
          (type-case Type (typecheck l env)
            [numT ()
                  (type-case Type (typecheck r env)
                    [numT () (boolT)]
                    [else (type-error r "num")])]
            [else (type-error l "num")])]
      ;; type-check for ifthenelse
      [ifthenelse (pred-expr if-true-expr if-else-expr) 
                  (type-case Type (typecheck pred-expr env)
                    [boolT () 
                           (if (equal? (typecheck if-true-expr env) (typecheck if-else-expr env))
                               (typecheck if-true-expr env)
                               (type-error if-else-expr "not the same as the true branch")) ]
                    [else (type-error pred-expr "bool")])]
      [pair (fst snd)
            (crossT (typecheck fst env) (typecheck snd env))]
      [fst (expr)
           (type-case Type (typecheck expr env)
             [crossT (f s) f]
             [else (type-error expr "not a pair")])]
      [snd (expr)
           (type-case Type (typecheck expr env)
             [crossT (f s) s]
             [else (type-error expr "not a pair")])]

      [with (names nametys inits body)

            (begin
                     (if (equal? (parse-type-many nametys) (typecheck-many inits env))
                         (typecheck body 
                                    (add-bind names
                                              (parse-type-many nametys)
                                              env))
                         (error 'with "different types")
                         )
                     )
            ]
      
      [try1 (try-expr catch-expr) 
            (type-case Type (typecheck try-expr env)
              [anyT () (typecheck catch-expr env)]
              [else (typecheck try-expr env)]
              )
            ]
      [throw () (anyT)]
      
      )))

(define run : (TFAE -> TFAE-Value)
  (lambda (tmfae)
    (interp tmfae (mtSub) (lambda (x) x) (lambda () (error 'interp "unhandled")))))

(define eval : (TFAE -> TFAE-Value)
  (lambda (tmfae)
    (begin
      (try (typecheck tmfae (mtEnv))
           (lambda () (error 'type-error "typecheck")))
      (run tmfae))))

(test (typecheck (with (list 'x 'y 'z) (list (numTE) (numTE) (numTE)) (list (num 5) (num 6) (num 7)) 
                 (add (id 'x) (num 1))
                      ) (mtEnv)) (numT))
(test (typecheck (with (list 'x 'y 'z) (list (numTE) (numTE) (numTE)) (list (num 5) (num 6) (num 7)) 
                 (eq (id 'x) (num 1))
                      ) (mtEnv)) (boolT))
(test/exn (typecheck (with (list 'x 'y 'z) (list (boolTE) (boolTE) (boolTE)) (list (num 1) (bool #f) (bool #f) )
                 (eq (id 'x) (num 1))
                      ) (mtEnv)) "with: different types")
(test (typecheck (try1 (bool #t) (num 10)) (mtEnv)) (boolT))
(test (typecheck (try1 (try1 (num 7) (throw)) (num 9)) (mtEnv)) (numT))
(test (run (fst (pair (num 10) (num 8))) ) (numV 10))
(test (run (snd (pair (num 10) (num 8))) ) (numV 8))
(test (typecheck (pair (num 10) (num 8)) (mtEnv)) (crossT (numT) (numT)))
(test (typecheck (add (num 1) (snd (pair (num 10) (num 8)))) (mtEnv)) (numT))
;
;(run (pair (num 10) (num 8)) )
(test (run (app (fun (list) (list) (num 10)) (list))) (numV 10))
(test (run (app (fun (list 'x 'y) (list (numTE) (numTE))
                        (sub (id 'x) (id 'y))) (list (num 10) (num 20))))
      (numV -10))
(test (run (with (list 'x) (list (numTE)) (list (num 5)) (add (id 'x) (id 'x)))) (numV 10))
(test (run (with (list 'x) (list (numTE)) (list (num 5)) 
                 (add (id 'x) (with (list 'x) (list (numTE)) (list (num 3)) (num 10))
                      ))) (numV 15))
(test (typecheck (app (fun (list 'x 'y) (list (numTE) (boolTE))
                           (id 'y))
                      (list (num 10) (bool false)))
                 (mtEnv))
      (boolT))
(test/exn (typecheck (app (fun (list 'x 'y) (list (numTE) (boolTE))
                               (id 'y))
                          (list (num 10) (num 10)))
                     (mtEnv))
          "no type")
(test (typecheck (throw) (mtEnv)) (anyT))
(test (typecheck (try1 (num 8) (num 10)) (mtEnv)) (numT))
(test (typecheck (try1 (throw) (num 10)) (mtEnv)) (numT))
;(test (typecheck (fun 'x (numTE) (add (id 'x) (num 12))) (mtEnv))
;      (arrowT (numT) (numT)))
;(test (typecheck (fun 'x (crossTE (numTE) (boolTE))
;                      (ifthenelse (snd (id 'x)) (num 0) (fst (id 'x))))
;                 (mtEnv))
;      (arrowT (crossT (numT) (boolT)) (numT)))
;(test/exn (typecheck (fst (num 10)) (mtEnv)) "no type")
;(test/exn (typecheck (add (num 1) (fst (pair (bool false) (num 8)))) (mtEnv)) "no type")
;(test/exn (typecheck (fun 'x (crossTE (numTE) (boolTE))
;                          (ifthenelse (fst (id 'x)) (num 0) (fst (id 'x))))
;                     (mtEnv))
;          "no type")
;
;(test (interp (eq (num 13)
;                  (ifthenelse (eq (num 1) (add (num -1) (num 2)))
;                              (num 12)
;                              (num 13)))
;              (mtSub))
;      (boolV false))
;
;(test (typecheck (eq (num 13)
;                     (ifthenelse (eq (num 1) (add (num -1) (num 2)))
;                                 (num 12)
;                                 (num 13)))
;                 (mtEnv))
;      (boolT))
;
;(test/exn (typecheck (add (num 1)
;                          (ifthenelse (bool true)
;                                      (bool true)
;                                      (bool false)))
;                     (mtEnv))
;          "no type")
;; ----------------------------------------

;(test (interp (num 10)
;              (mtSub))
;      (numV 10))
;(test (interp (add (num 10) (num 17))
;              (mtSub))
;      (numV 27))
;(test (interp (sub (num 10) (num 7))
;              (mtSub))
;      (numV 3))
;(test (interp (app (fun 'x (numTE) (add (id 'x) (num 12)))
;                   (add (num 1) (num 17)))
;              (mtSub))
;      (numV 30))
;(test (interp (id 'x)
;              (aSub 'x (numV 10) (mtSub)))
;      (numV 10))
;
;(test (interp (app (fun 'x (numTE)
;                        (app (fun 'f (arrowTE (numTE) (numTE))
;                                  (add (app (id 'f) (num 1))
;                                       (app (fun 'x (numTE)
;                                                 (app (id 'f)
;                                                      (num 2)))
;                                            (num 3))))
;                             (fun 'y (numTE)
;                                  (add (id 'x) (id 'y)))))
;                   (num 0))
;              (mtSub))
;      (numV 3))
;
;(test/exn (interp (id 'x) (mtSub))
;          "free variable")
;
;(test (typecheck (num 10) (mtEnv))
;      (numT))
;
;(test (typecheck (add (num 10) (num 17)) (mtEnv))
;      (numT))
;(test (typecheck (sub (num 10) (num 7)) (mtEnv))
;      (numT))
;
;(test (typecheck (fun 'x (numTE) (add (id 'x) (num 12))) (mtEnv))
;      (arrowT (numT) (numT)))
;
;(test (typecheck (fun 'x (numTE) (fun 'y (boolTE) (id 'x))) (mtEnv))
;      (arrowT (numT) (arrowT (boolT)  (numT))))
;
;(test (typecheck (app (fun 'x (numTE) (add (id 'x) (num 12)))
;                      (add (num 1) (num 17)))
;                 (mtEnv))
;      (numT))
;
;(test (typecheck (app (fun 'x (numTE)
;                           (app (fun 'f (arrowTE (numTE) (numTE))
;                                     (add (app (id 'f) (num 1))
;                                          (app (fun 'x (numTE) (app (id 'f) (num 2)))
;                                               (num 3))))
;                                (fun 'y (numTE)
;                                     (add (id 'x)
;                                          (id' y)))))
;                      (num 0))
;                 (mtEnv))
;      (numT))
;
;(test/exn (typecheck (app (num 1) (num 2)) (mtEnv))
;          "no type")
;
;(test/exn (typecheck (add (fun 'x (numTE) (num 12))
;                          (num 2))
;                     (mtEnv))
;          "no type")