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
;;add-bind: (listof symbol) (listof types) TypeEnv -> TypeEnv
;;similar to add-sub, but for types
(define (add-bind names ts te)
  (cond
    [(empty? names) te]
    [else (
           add-bind (rest names) (rest ts)
                   (aBind (first names) (first ts) te))]))
;; length: List -> number
;; find the length of a list
(define (length x)
  (cond
    [(empty? x) 0]
    [else (+ 1 (length (rest x)))])
  )
;;tests for length:

;;add-sub: Listof Symbol Listof value DefrdSub -> DefredSub
;;add a list of pairs to the DefedSub
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
;;typecheck-many: (listof TFAE) TypeEnvironment -> (listof Type)
;;to check the types of a whole list
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
;;parse-type: TE -> Type
;;to parse a TE into a Type
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
;;parse-type-many: listof te ->listof type
;;to parse a list of te into a list of type
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
;;new-equal?: (listof Type) (listof Type) -> boolean
;;new-equal that can compare anyT
(define (new-equal? l1 l2)
  (cond
    [(not (= (length l1) (length l2))) 
     (error 'new-equal "different length" )]
    [(empty? l1) #t]
    [else
     (cond
       [(equal? (first l1) (first l2))
        (new-equal? (rest l1) (rest l2))]
       [(equal? (first l1 ) (anyT))
        (new-equal? (rest l1) (rest l2))        
        ]
       [(equal? (first l2) (anyT))
        (new-equal? (rest l1) (rest l2))
        ]
       [else
        ;;special treatment for comparring 2 arrowT
        (type-case Type (first l1) 
          [arrowT (arg1 b1) 
                 (type-case Type (first l2)
                   ;if first l2 is also an arrow
                   [arrowT (arg2 b2)
                           (cond
                             [(new-equal? arg1 arg2)
                              (new-equal? (rest l1) (rest l2))]
                             [else #f])]
                   ;if first l2 is just another anyT
                   [anyT () #t]
                   ;if first l2 is numT or boolT
                   [else #f])]
          ;if first l1 is not an arrowT or anyT, it should have been handled at the previous
          ;cases
          [else #f])]

       )]
  
    )
  )

(define typecheck : (TFAE TypeEnv -> Type)
  
  (lambda (tfae env)
    (type-case TFAE tfae
      [num (n) (numT)]
      [bool (b) (boolT)]
      [add (l r) (type-case Type (typecheck l env)
                   [numT ()
                         (type-case Type (typecheck r env)
                           [numT () (numT)]
                           [anyT () (anyT)]
                           [else (type-error r "num")])]
                   [anyT () (anyT)]
                   [else (type-error l "num")])]
      [sub (l r) (type-case Type (typecheck l env)
                   [numT ()
                         (type-case Type (typecheck r env)
                           [numT () (numT)]
                           [anyT () (anyT)]
                           [else (type-error r "num")])]
                   [anyT () (anyT)]
                   [else (type-error l "num")])]
      [id (name) (get-type name env)]
      [fun (names tes body)
           (local [(define param-types (parse-type-many tes))]
             ;-----------------
             (arrowT param-types
                                (typecheck body (add-bind names
                                                          param-types
                                                          env)))
             )]
      

      [app (fn args)
           (type-case Type (typecheck fn env)
             [arrowT (param-types result-type)
                     ;;need to check if all the elements of param-types match all the 
                     ;;elements of the result of typecheck-many
                     (begin 
                     (if (new-equal? param-types
                                 (typecheck-many args env))
                         result-type
                         (type-error args
                                     (to-string param-types)))
                     )
                     ]

             [anyT () (anyT) ]
             [else (type-error fn "function")])]
      ;;type-check for eq
      [eq (l r) 
          (type-case Type (typecheck l env)
            [numT ()
                  (type-case Type (typecheck r env)
                    [numT () (boolT)]
                    [anyT () (anyT)]
                    [else (type-error r "num")])]
            [anyT () (anyT)]
            [else (type-error l "num")])]
      ;; type-check for ifthenelse
      [ifthenelse (pred-expr if-true-expr if-else-expr) 
                  (type-case Type (typecheck pred-expr env)
                    [boolT () 
                           (if (equal? (typecheck if-true-expr env) (typecheck if-else-expr env))
                               (typecheck if-true-expr env)
                               (type-error if-else-expr "not the same as the true branch")) ]
                    [anyT () (anyT)]
                    [else (type-error pred-expr "bool")])]
      [pair (fst snd)
            (crossT (typecheck fst env) (typecheck snd env))]
      [fst (expr)
           (type-case Type (typecheck expr env)
             [crossT (f s) f]
             [anyT () (anyT)]
             [else (type-error expr "not a pair")])]
      [snd (expr)
           (type-case Type (typecheck expr env)
             [crossT (f s) s]
             [anyT () (anyT)]
             [else (type-error expr "not a pair")])]

      [with (names nametys inits body)
            (if (new-equal? (parse-type-many nametys) (typecheck-many inits env))
                (typecheck body 
                           (add-bind names
                                     (parse-type-many nametys)
                                     env))
                (error 'with "different types")
                )          
            ]
      
      [try1 (try-expr catch-expr) 
            (type-case Type (typecheck try-expr env)
              [anyT () (typecheck catch-expr env)]
              [else (cond
                      [(equal? (typecheck try-expr env) (typecheck catch-expr env) )
                       (typecheck catch-expr env)]
                      [(equal? (typecheck catch-expr env) (anyT)) (anyT)]
                      [else (type-error catch-expr "no type" )])]
              
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
;------------
(test (eval 
   (try1 (app 
          (fun (list 'x) (list (arrowTE (list (numTE)) (numTE))) 
               (app (id 'x) (list (num 11)))) 
          (list (fun (list 'x) (list (numTE)) (add (id 'x) (throw)))))
         (num 42))) (numV 42))
;--------------
(test (typecheck (with (list 'x 'y 'z) (list (numTE) (numTE) (numTE)) (list (num 5) (num 6) (num 7)) 
                 (add (id 'x) (num 1))
                      ) (mtEnv)) (numT))
(test (typecheck (with (list 'x 'y 'z) (list (numTE) (numTE) (numTE)) (list (num 5) (num 6) (num 7)) 
                 (eq (id 'x) (num 1))
                      ) (mtEnv)) (boolT))
(test/exn (typecheck (with (list 'x 'y 'z) (list (boolTE) (boolTE) (boolTE)) (list (num 1) (bool #f) (bool #f) )
                 (eq (id 'x) (num 1))
                      ) (mtEnv)) "with: different types")
(test/exn (typecheck (try1 (bool #t) (num 10)) (mtEnv)) "no type")
;(test/exn (typecheck (try1 (try1 (num 7) (throw)) (num 9)) (mtEnv)) "no type")
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
(test (typecheck (fun (list 'x) (list (numTE)) (add (id 'x) (num 12))) (mtEnv))
      (arrowT (list (numT)) (numT)))
;(test (typecheck (fun 'x (crossTE (numTE) (boolTE))
;                      (ifthenelse (snd (id 'x)) (num 0) (fst (id 'x))))
;                 (mtEnv))
;      (arrowT (crossT (numT) (boolT)) (numT)))
(test/exn (typecheck (fst (num 10)) (mtEnv)) "no type")
(test/exn (typecheck (add (num 1) (fst (pair (bool false) (num 8)))) (mtEnv)) "no type")
(test/exn (typecheck (fun (list 'x) (list (crossTE (numTE) (boolTE)))
                          (ifthenelse (fst (id 'x)) (num 0) (fst (id 'x))))
                     (mtEnv))
          "no type")
;
(test (run (eq (num 13)
                  (ifthenelse (eq (num 1) (add (num -1) (num 2)))
                              (num 12)
                              (num 13)))
              )
      (boolV false))
(test (eval (eq (num 13)
                  (ifthenelse (eq (num 1) (add (num -1) (num 2)))
                              (num 12)
                              (num 13))))
      (boolV false))

(test (typecheck (eq (num 13)
                     (ifthenelse (eq (num 1) (add (num -1) (num 2)))
                                 (num 12)
                                 (num 13)))
                 (mtEnv))
      (boolT))
(test/exn (typecheck (add (num 1)
                          (ifthenelse (bool true)
                                      (bool true)
                                      (bool false)))
                     (mtEnv))
          "no type")

;; my
(test/exn   (eval   (app (fun (list 'x 'y) (list (boolTE) (numTE))
                      (eq (id 'x) (id 'y)))
                    (list (bool false) (num 3))))
        "type-error: typecheck")
(test/exn   (eval   (app (fun (list 'x 'y) (list (boolTE) (boolTE))
                      (eq (id 'x) (id 'y)))
                    (list (bool false) (bool true))))
        "type-error: typecheck")
(test   (eval   (app (fun (list 'x 'y) (list (numTE) (numTE))
                      (eq (id 'x) (id 'y)))
                (list (num 4) (num 3))))
        (boolV false))
(test   (eval   (app (fun (list 'x 'y) (list (boolTE) (boolTE))
                      (ifthenelse (id 'x) (num 1) (num 2)))
                (list (bool false) (bool true))))
        (numV 2))
(test   (eval   (app (fun (list 'x 'y) (list (boolTE) (boolTE))
                      (ifthenelse (id 'y) (num 1) (num 2)))
                (list (bool false) (bool true))))
        (numV 1))
(test   (eval   (app (fun (list 'x 'y) (list (numTE) (numTE))
                      (eq (id 'x) (id 'y)))
                (list (num 3) (num 3))))
        (boolV true))
(test   (eval   (app (fun (list 'x 'y) (list (numTE) (numTE))
                      (eq (id 'x) (id 'y)))
                (list (num 3) (add (num 1) (num 2)))))
        (boolV true))
(test   (eval   (ifthenelse (bool false) (num 3) (num 4)))
        (numV 4))
(test   (eval   (ifthenelse (bool true) (num 3) (num 4)))
        (numV 3))
(test/exn   (eval   (ifthenelse (num 3) (num 4) (num 5)))
        "type-error: typecheck")
(test/exn   (eval   (ifthenelse (bool false) (bool false) (num 5)))
        "type-error: typecheck")


(test (eval (app (fun (list 'x 'y) (list (crossTE (boolTE) (numTE)) (numTE))
                      (fst (id 'x)))
                 (list (pair (bool false) (num 3)) (num 2))))
      (boolV false))

(test/exn (eval (app (fun (list 'x 'y) (list (crossTE (boolTE) (numTE)) (numTE))
                      (fst (id 'x)))
                 (list (pair (num 5) (num 3)) (num 2))))
      "type-error: typecheck")

;; my

(test/exn (eval (app 
        (fun (list 'x 'y 'z) (list (numTE) (numTE) (boolTE)) 
            (with (list 'x 'y) 
                  (list (numTE) (arrowTE (list (numTE)) (numTE))) 
                  (list 
                    (num 3)
                    (fun (list 'x) (list (boolTE)) 
                         (ifthenelse (eq (id 'z) (num 3))
                                (num 12)
                                (num 6)
                         )
                    )
                  )
                  (app (id 'y) (list (id 'x)))
        ))
        (list (num 5) (num 1) (bool false)))) "type-error: typecheck")

;; try1 - throw
(test   (eval   (try1   (app  (fun (list 'x) (list (numTE))
                                (add (num 32)
                                     (try1  (throw)
                                            (id 'x))
                                ))
                            (list (num 10)))
                        (num 5))
                )
        (numV 42))

(test   (eval   (try1   (add (num 32) (throw))
                        (num 5)))
        (numV 5))

(test   (eval   (try1   (app  (fun (list 'x) (list (numTE))
                                (add (num 32)
                                     (try1  (throw)
                                            (throw))
                                ))
                            (list (num 10)))
                        (num 5))
                )
        (numV 5))

(test   (eval   (app (fun (list 'x) (list (arrowTE (list (numTE)) (numTE)))
                        (app (id 'x) (list (num 10))))
                     (list (fun (list 'x) (list (numTE))
                                (add (id 'x) (num 10)))
                     )
        ))
        (numV 20))

(test   (eval   (try1 (app (fun (list 'x) (list (arrowTE (list (numTE)) (numTE)))
                            (app (id 'x) (list (throw))))
                         (list (fun (list 'x) (list (numTE))
                                    (add (id 'x) (num 10)))
                         ))
                      (num 42)
        ))
        (numV 42))

(test   (eval   (try1 (app (fun (list 'x) (list (arrowTE (list (numTE)) (numTE)))
                            (app (id 'x) (list (num 11))))
                         (list (fun (list 'x) (list (numTE))
                                    (add (id 'x) (throw)))
                         ))
                      (num 42)
        ))
        (numV 42))


;; additional
(test/exn (eval (ifthenelse (bool true) (num 3) (bool false))) "type-error: typecheck")
(test/exn (eval (app (fun (list 'x) (list (numTE)) (id 'x)) (list (bool false)))) "type-error: typecheck")
(test/exn (eval (app (fun (list 'x 'y) (list (numTE) (boolTE)) (num 23))
                     (list (bool false) (num 3)))) "type-error: typecheck")
(test/exn (eval (app (fun (list 'x 'y) (list (numTE) (boolTE)) (num 23))
                     (list (bool false)))) "type-error: typecheck")
(test/exn (eval (app (fun (list 'x) (list (numTE)) (num 23))
                     (list (bool false) (num 3)))) "type-error: typecheck")
(test (run (app (fun (list) (list) (num 10)) (list))) (numV 10))
(test (run (app (fun (list 'x 'y) (list (numTE) (numTE))
                        (sub (id 'x) (id 'y))) (list (num 10) (num 20))))
      (numV -10))
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
(test/exn (typecheck (try1 (num 8) (bool false)) (mtEnv)) "no type")