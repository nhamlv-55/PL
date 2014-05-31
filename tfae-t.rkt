#lang plai-typed

(define-type TFAE
  [num (n : number)]
  [bool (b : boolean)]
  [add (lhs : TFAE)
       (rhs : TFAE)]
  [sub (lhs : TFAE)
       (rhs : TFAE)]
  [id (name : symbol)]
  [fun (param : symbol)
       (paramty : TE)
       (body : TFAE)]
  [app (fun-expr : TFAE)
       (arg-expr : TFAE)]
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
  [arrowTE (param : TE)
           (result : TE)]
  [crossTE (firstTE : TE)
           (secondTE : TE)]
  )

(define-type TFAE-Value
  [numV (n : number)]
  [closureV (param : symbol)
            (body : TFAE)
            (ds : DefrdSub)]
  [boolV (b : boolean)]
  [pairV (f : TFAE-Value) (s : TFAE-Value)]
  )

(define-type DefrdSub
  [mtSub]
  [aSub (name : symbol)
        (value : TFAE-Value)
        (rest : DefrdSub)])

(define-type Type
  [numT]
  [boolT]
  [arrowT (param : Type)
          (result : Type)]
  [crossT (f : Type)
          (s : Type)]
  )

(define-type TypeEnv
  [mtEnv]
  [aBind (name : symbol)
         (type : Type)
         (rest : TypeEnv)])

;; ----------------------------------------

;; interp : TFAE DefrdSub -> TFAE-Value
(define (interp tfae ds)
  (type-case TFAE tfae
    [num (n) (numV n)]
    [bool (b) (boolV b)]
    [add (l r) (num+ (interp l ds) (interp r ds))]
    [sub (l r) (num- (interp l ds) (interp r ds))]
    [id (name) (lookup name ds)]
    [fun (param param-te body-expr)
         (closureV param body-expr ds)]
    [app (fun-expr arg-expr)
         (local [(define fun-val (interp fun-expr ds))
                 (define arg-val (interp arg-expr ds))]
           (interp (closureV-body fun-val)
                   (aSub (closureV-param fun-val)
                         arg-val
                         (closureV-ds fun-val))))]
    [eq (l r) (num= (interp l ds) (interp r ds)) ]
    [ifthenelse (pred-expr if-true-expr if-false-expr)
                (if (boolV-b (interp pred-expr ds))
                    (interp if-true-expr ds)
                    (interp if-false-expr ds))]
    [pair (f s) (pairV (interp f ds) (interp s ds))]
    [fst (expr) (type-case TFAE-Value (interp expr ds)
                  [pairV (f s) f]
                  [else (error 'interp "not a pair")]
                  )]
    [snd (expr) (type-case TFAE-Value (interp expr ds)
                  [pairV (f s) s]
                  [else (error 'interp "not a pair")]
                  )]
  ))

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
    [arrowTE (a b) (arrowT (parse-type a)
                           (parse-type b))]
    [crossTE (a b) (crossT (parse-type a)
                           (parse-type b))]
    ))

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
      [fun (name te body)
           (local [(define param-type (parse-type te))]
             (arrowT param-type
                     (typecheck body (aBind name
                                            param-type
                                            env))))]
      [app (fn arg)
           (type-case Type (typecheck fn env)
             [arrowT (param-type result-type)
                     (if (equal? param-type
                                 (typecheck arg env))
                         result-type
                         (type-error arg
                                     (to-string param-type)))]
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
      
      )))

(test (interp (fst (pair (num 10) (num 8))) (mtSub)) (numV 10))
(test (interp (snd (pair (num 10) (num 8))) (mtSub)) (numV 8))
(test (typecheck (pair (num 10) (num 8)) (mtEnv)) (crossT (numT) (numT)))
(test (typecheck (add (num 1) (snd (pair (num 10) (num 8)))) (mtEnv)) (numT))

(test (interp (id 'x)
              (aSub 'x (numV 10) (mtSub)))
      (numV 10))
(test (typecheck (fun 'x (numTE) (add (id 'x) (num 12))) (mtEnv))
      (arrowT (numT) (numT)))
(test (typecheck (fun 'x (crossTE (numTE) (boolTE))
                      (ifthenelse (snd (id 'x)) (num 0) (fst (id 'x))))
                 (mtEnv))
      (arrowT (crossT (numT) (boolT)) (numT)))
(test/exn (typecheck (fst (num 10)) (mtEnv)) "no type")
(test/exn (typecheck (add (num 1) (fst (pair (bool false) (num 8)))) (mtEnv)) "no type")
(test/exn (typecheck (fun 'x (crossTE (numTE) (boolTE))
                          (ifthenelse (fst (id 'x)) (num 0) (fst (id 'x))))
                     (mtEnv))
          "no type")

(test (interp (eq (num 13)
                  (ifthenelse (eq (num 1) (add (num -1) (num 2)))
                              (num 12)
                              (num 13)))
              (mtSub))
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