#lang plai-typed

(define-type TVRCFAE
  [num (n : number)]
  [bool (b : boolean)]
  [add (lhs : TVRCFAE)
       (rhs : TVRCFAE)]
  [sub (lhs : TVRCFAE)
       (rhs : TVRCFAE)]
  [id (name : symbol)]
  [fun (param : (listof symbol))
       (argty : (listof TE))
       (body : TVRCFAE)]
  [app (fun-expr : TVRCFAE)
       (arg-expr : (listof TVRCFAE))]
  [if0 (test-expr : TVRCFAE)
       (then-expr : TVRCFAE)
       (else-expr : TVRCFAE)]
  ;;maybe needed
  [rec (name : symbol)
    (ty : TE)
    (rhs-expr : TVRCFAE)
    (body-expr : TVRCFAE)]
  [with-type (name : symbol)
             (var1-name : symbol)
             (var1-ty : TE)
             (var2-name : symbol)
             (var2-ty : TE)
             (body-expr : TVRCFAE)]
  [cases (name : symbol)
    (dispatch-expr : TVRCFAE)
    (var1-name : symbol)
    (bind1-name : symbol)
    (rhs1-expr : TVRCFAE)
    (var2-name : symbol) 
    (bind2-name : symbol)
    (rhs2-expr : TVRCFAE)])


(define-type TE
  [numTE]
  [boolTE]
  [arrowTE (arg : (listof TE))
           (result : TE)]
  [idTE (name : symbol)])

(define-type TVRCFAE-Value
  [numV (n : number)]
  [boolV (b : boolean)]
  [closureV (param : (listof symbol))
            (body : TVRCFAE)
            (ds : DefrdSub)]
  [variantV (right? : boolean)
            (val : TVRCFAE-Value)]
  [constructorV (right? : boolean)])

(define-type DefrdSub
  [mtSub]
  [aSub (name : symbol)
        (value : TVRCFAE-Value)
        (rest : DefrdSub)]
  [aRecSub (name : symbol)
           (value-box : (boxof TVRCFAE-Value))
           (rest : DefrdSub)])

(define-type Type
  [numT]
  [boolT]
  [arrowT (arg : (listof Type))
          (result : Type)]
  [idT (name : symbol)])

(define-type TypeEnv
  [mtEnv]
  [aBind (name : symbol)
         (type : Type)
         (rest : TypeEnv)]
  [tBind (name : symbol)
         (var1-name : symbol)
         (var1-type : Type)
         (var2-name : symbol)
         (var2-type : Type)
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


;;add-sub: Listof Symbol Listof value DefrdSub -> DefredSub
;;add a list of pairs to the DefedSub
(define (add-sub names vs ds)
  (cond
    [(empty? names) ds]
    [else (
           add-sub (rest names) (rest vs)
                   (aSub (first names) (first vs) ds))]))

;;interp-many: blah blah blah
(define (interp-many list_of_expr ds)
  (cond
    [(empty? list_of_expr) empty]
    [else (cons
           (interp (first list_of_expr) ds)
           (interp-many (rest list_of_expr) ds))]))

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
;;parse-type-many: listof te ->listof type
;;to parse a list of te into a list of type
(define (parse-type-many aList)
  (cond
    [(empty? aList) empty]
    [else
     (cons (parse-type (first aList)) (parse-type-many (rest aList)))]))
;;------------------------------------------

;; interp : TVRCFAE DefrdSub -> TVRCFAE-Value
(define (interp a-tvrcfae ds)
  (type-case TVRCFAE a-tvrcfae
    [num (n) (numV n)]
    [bool (b) (boolV b)]
    [add (l r) (num+ (interp l ds) (interp r ds))]
    [sub (l r) (num- (interp l ds) (interp r ds))]
    [id (name) (lookup name ds)]
    [fun (param arg-te body-expr)
         (closureV param body-expr ds)]
    [app (fun-expr arg-exprs)
         (local [(define fun-val
                   (interp fun-expr ds))
                 (define arg-vals
                   ( interp-many arg-exprs ds))]
           (type-case TVRCFAE-Value fun-val 
             [closureV (params body ds)
                       (interp body
                               (add-sub params
                                     arg-vals
                                     ds))]
             [constructorV (right?)
                           (variantV right? (first arg-vals))]
             [else (error 'interp "not applicable")]))]
    [if0 (test-expr then-expr else-expr)
         (if (numzero? (interp test-expr ds))
             (interp then-expr ds)
             (interp else-expr ds))]
    [rec (bound-id type named-expr body-expr)
      (local [(define value-holder (box (numV 42)))
              (define new-ds (aRecSub bound-id
                                      value-holder
                                      ds))]
        (begin
          (set-box! value-holder (interp named-expr new-ds))
          (interp body-expr new-ds)))]
    [with-type (type-name var1-name var1-te var2-name var2-te body-expr)
               (interp body-expr
                       (aSub var1-name
                             (constructorV false)                               
                             (aSub var2-name
                                   (constructorV true)
                                   ds)))]
    [cases (ty dispatch-expr 
               var1-name var1-id var1-rhs
               var2-name var2-id var2-rhs)
      (type-case TVRCFAE-Value (interp dispatch-expr ds)
        [variantV (right? val)
                  (if (not right?)
                      (interp var1-rhs (aSub var1-id
                                             val
                                             ds))           
                      (interp var2-rhs (aSub var2-id
                                             val
                                             ds)))]
        [else (error 'interp "not a variant result")])]))

;; num-op : (number number -> number) -> (TVRCFAE-Value TVRCFAE-Value -> TVRCFAE-Value)
(define (num-op op op-name x y)
  (numV (op (numV-n x) (numV-n y))))

(define (num+ x y) (num-op + '+ x y))
(define (num- x y) (num-op - '- x y))

(define (numzero? x) (= 0 (numV-n x)))

(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free variable")]
    [aSub (sub-name val rest-ds)
          (if (symbol=? sub-name name)
              val
              (lookup name rest-ds))]
    [aRecSub (sub-name val-box rest-ds)
             (if (symbol=? sub-name name)
                 (unbox val-box)
                 (lookup name rest-ds))]))


;; ----------------------------------------

(define (get-type name-to-find env)
  (type-case TypeEnv env
    [mtEnv () (error 'get-type "free variable, so no type")]
    [aBind (name ty rest)
           (if (symbol=? name-to-find name)
               ty
               (get-type name-to-find rest))]
    [tBind (name var1-name var1-ty var2-name var2-ty rest)
           (get-type name-to-find rest)]))

(define (validtype ty env)
  (type-case Type ty
    [numT () (mtEnv)]
    [boolT () (mtEnv)]
    [arrowT (a b) (begin (validtype-many a env)
                         (validtype b env))]
    [idT (id) (find-type-id id env)]))

(define (validtype-many tys env)
  (cond
    [(empty? tys) (mtEnv)]
    [else (begin
            (validtype (first tys) env)
            (validtype-many (rest tys) env))])
  )

(define (find-type-id name-to-find env)
  (type-case TypeEnv env
    [mtEnv () (error 'get-type "free type name, so no type")]
    [aBind (name ty rest)
           (find-type-id name-to-find rest)]
    [tBind (name var1-name var1-ty var2-name var2-ty rest)
           (if (symbol=? name-to-find name)
               env
               (find-type-id name-to-find rest))]))
(test/exn (get-type 'x (mtEnv)) "free variable, so no type")
(test/exn (find-type-id 'x (mtEnv)) "free type name, so no type")
(test/exn (find-type-id 'x (tBind 'y 'z (numT) 'a (boolT) (mtEnv))) "free type name, so no type")
;; ----------------------------------------

(define (parse-type te)
  (type-case TE te
    [numTE () (numT)]
    [boolTE () (boolT)]
    [arrowTE (a b) (arrowT (parse-type-many a)
                           (parse-type b))]
    [idTE (name) (idT name)]))

(define (type-error TVRCFAE msg)
  (error 'typecheck (string-append
                     "no type: "
                     (string-append
                      (to-string TVRCFAE)
                      (string-append " not "
                                     msg)))))

(define typecheck : (TVRCFAE TypeEnv -> Type)
  (lambda (tvrcfae env)
    (type-case TVRCFAE tvrcfae
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
           (local [(define arg-type (parse-type-many te))]
             (begin
               (validtype-many arg-type env)
               (arrowT arg-type
                       (typecheck body (add-bind name
                                              arg-type
                                              env)))))]
      [app (fn arg)
           (type-case Type (typecheck fn env)
             [arrowT (arg-type result-type)
                     (if (equal? arg-type
                                 (typecheck-many arg env))
                         result-type
                         (type-error arg
                                     (to-string arg-type)))]
             [else (type-error fn "function")])]
      [if0 (test-expr then-expr else-expr)
           (type-case Type (typecheck test-expr env)
             [numT () (local [(define test-ty (typecheck then-expr env))]
                        (if (equal? test-ty (typecheck else-expr env))
                            test-ty
                            (type-error else-expr
                                        (to-string test-ty))))]
             [else (type-error test-expr "num")])]
      [rec (name ty rhs-expr body-expr)
        (local [(define rhs-ty (parse-type ty))
                (define new-env (aBind name
                                       rhs-ty
                                       env))]
          (begin
            (validtype rhs-ty env)
            (if (equal? rhs-ty (typecheck rhs-expr new-env))
                (typecheck body-expr new-env)
                (type-error rhs-expr (to-string rhs-ty)))))]
      [with-type (type-name var1-name var1-te var2-name var2-te body-expr)
                 (local [(define var1-ty (parse-type var1-te))
                         (define var2-ty (parse-type var2-te))
                         (define new-env (tBind type-name
                                                var1-name var1-ty
                                                var2-name var2-ty
                                                env))]
                   (begin
                     (validtype var1-ty new-env)
                     (validtype var2-ty new-env)
                     (typecheck body-expr
                                (aBind var1-name
                                       (arrowT (list var1-ty) (idT type-name))
                                       (aBind var2-name
                                              (arrowT (list var2-ty) (idT type-name))
                                              new-env)))))]
      [cases (type-name dispatch-expr 
                        var1-name var1-id var1-rhs
                        var2-name var2-id var2-rhs)
        (local [(define bind (find-type-id type-name env))]
          (if (and (equal? var1-name (tBind-var1-name bind))
                   (equal? var2-name (tBind-var2-name bind)))
              (type-case Type (typecheck dispatch-expr env)
                [idT (name) (if (equal? name type-name)
                                (local [(define rhs1-ty (typecheck var1-rhs
                                                                   (aBind var1-id
                                                                          (tBind-var1-type bind)
                                                                          env)))
                                        (define rhs2-ty  (typecheck var2-rhs
                                                                    (aBind var2-id
                                                                           (tBind-var2-type bind)
                                                                           env)))]
                                  (if (equal? rhs1-ty rhs2-ty)
                                      rhs1-ty
                                      (type-error var2-rhs (to-string rhs1-ty))))
                                (type-error dispatch-expr (to-string type-name)))]
                [else (type-error dispatch-expr (to-string type-name))])
              (type-error  tvrcfae "matching variant names")))])))

(define run : (TVRCFAE -> TVRCFAE-Value)
  (lambda (tmfae)
    (interp tmfae (mtSub) )))

(define eval : (TVRCFAE -> TVRCFAE-Value)
  (lambda (tmfae)
    (begin
      (try (typecheck tmfae (mtEnv))
           (lambda () (error 'type-error "typecheck")))
      (run tmfae))))

;; ----------------------------------------

(test (interp (num 10)
              (mtSub))
      (numV 10))
(test (interp (add (num 10) (num 17))
              (mtSub))
      (numV 27))
(test/exn (typecheck (add (num 10) (bool #t))
              (mtEnv))
      "num")
(test/exn (typecheck (sub (num 10) (bool #t))
              (mtEnv))
      "num")
(test/exn (typecheck (sub (bool #t) (bool #t))
              (mtEnv))
      "num")
(test (interp (sub (num 10) (num 7))
              (mtSub))
      (numV 3))
(test (interp (app (fun (list 'x 'y) (list (numTE) (numTE)) (add (id 'x) (id 'y)))
                   (list (add (num 1) (num 17)) (num 12))
                   )
              (mtSub))
      (numV 30))

(test (interp (id 'x)
              (aSub 'x (numV 10) (mtSub)))
      (numV 10))

(test (interp (app (fun (list 'x) (list (numTE))
                        (app (fun (list 'f) (list (arrowTE (list (numTE)) (numTE)))
                                  (add (app (id 'f) (list (num 1)) )
                                       (app (fun (list 'x) (list (numTE))
                                                 (app (id 'f)
                                                      (list (num 2)) ))
                                            (list (num 3)) )))
                             (list (fun (list 'y) (list (numTE))
                                  (add (id 'x) (id 'y))))))
                   (list (num 0)))
              (mtSub))
      (numV 3))

(test (interp (if0 (num 0) (num 1) (num 2))
              (mtSub))
      (numV 1))
(test (interp (if0 (num 1) (num 1) (num 2))
              (mtSub))
      (numV 2))
(test (interp (rec 'a (numTE)
                (num 10)
                (add (id 'a) (num 1)))
              (mtSub))
      (numV 11))
(test (interp (rec 'fib (arrowTE (list (numTE)) (numTE))
                (fun (list 'x) (list (numTE))
                     (if0 (id' x)
                          (num 1)
                          (if0 (sub (id 'x) (num 1))
                               (num 1)
                               (add (app (id 'fib) (list (sub (id 'x) (num 1))))
                                    (app (id 'fib) (list (sub (id 'x) (num 2))))))))
                (app (id 'fib) (list (num 4))))
              (mtSub))
      (numV 5))

;;ERROR
(test/exn (interp (app (num 1) (list (num 2))) (mtSub)) "not applicable")
 ;             (mtSub))
  ;    (variantV false (numV 10)))
;
(test (interp (with-type 'fruit 
                         'apple (numTE)
                         'banana (arrowTE (list (numTE)) (numTE))
                         (cases 'fruit (app (id 'apple) (list (num 10)))
                           'apple 'y (add (id 'y) (num 1))
                           'banana 'x (app (id 'x) (list (num 10)))))
              (mtSub))
      (numV 11))

(test/exn (interp (with-type 'fruit 
                         'apple (numTE)
                         'banana (arrowTE (list (numTE)) (numTE))
                         (cases 'fruit (add (num 1) (num 2))
                           'apple 'y (add (id 'y) (num 1))
                           'banana 'x (app (id 'x) (list (num 10)))))
              (mtSub))
      "interp: not a variant result")

(test (interp (with-type 'fruit 
                         'apple (numTE)
                         'banana (arrowTE (list (numTE)) (numTE))
                         (cases 
                             'fruit (app (id 'banana) (list (fun (list 'x) (list (numTE)) (sub (id 'x) (num 1)))))
                           'apple 'y (add (id 'y) (num 1))
                           'banana 'x (app (id 'x) (list (num 10)))))
              (mtSub))
      (numV 9))

(test/exn (interp (id 'x) (mtSub))
          "free variable")
;
(test (typecheck (num 10) (mtEnv))
      (numT))


;--------------------------
(test (eval (add (num 10) (num 17))) (numV 27))
(test (eval (sub (num 10) (num 7))) (numV 3))
(test (eval (app (fun (list 'x) (list (numTE)) (add (id 'x) (num 12))) (list (add (num 1) (num 17))))) (numV 30))

(test   (eval (app (fun (list 'x) (list (numTE))
                        (app (fun (list 'f) (list (arrowTE (list (numTE)) (numTE)))
                                  (add (app (id 'f) (list (num 1)))
                                       (app (fun (list 'x) (list (numTE))
                                                 (app (id 'f)
                                                      (list (num 2))))
                                            (list (num 3)))))
                             (list (fun (list 'y) (list (numTE))
                                  (add (id 'x) (id 'y))))))
                   (list (num 0)))
        )
        (numV 3))

(test (typecheck (num 10) (mtEnv)) (numT))
(test (typecheck (add (num 10) (num 17)) (mtEnv)) (numT))
(test (typecheck (sub (num 10) (num 7)) (mtEnv)) (numT))
(test (typecheck (fun (list 'x) (list (numTE)) (add (id 'x) (num 12))) (mtEnv)) (arrowT (list (numT)) (numT)))
(test (typecheck (app (fun (list 'x) (list (numTE)) (add (id 'x) (num 12))) (list (add (num 1) (num 17)))) (mtEnv)) (numT))

(test/exn (typecheck (app (num 1) (list (num 2))) (mtEnv)) "no type")
(test/exn (typecheck (add (fun (list 'x) (list (numTE)) (num 12)) (num 2)) (mtEnv)) "no type")

(test (run (app (fun (list) (list) (num 10)) (list))) (numV 10))
(test (run (app 
              (fun (list 'x 'y) (list (numTE) (numTE))
                (sub (id 'x) (id 'y)))
              (list (num 10) (num 20))))
      (numV -10))

(test (eval (if0  (sub (num 4) (num 4))
                  (num 42)
                  (num 10)
      )) (numV 42))

(test (eval (if0  (sub (num 4) (num 3))
                  (num 42)
                  (num 10)
      )) (numV 10))

(test (eval
        (rec 'x (arrowTE (list (numTE)) (numTE))
          (fun (list 'y) (list (numTE))
            (if0 (sub (id 'y) (num 1))
              (id 'y)
              (add (num 2) (app (id 'x) (list (sub (id 'y) (num 1)))))
            ))
          (app (id 'x) (list (num 10)))
        ))
      (numV 19))

(test (eval
        (app (fun (list 'z) (list (numTE))
            (rec 'x (arrowTE (list (numTE)) (numTE))
              (fun (list 'y) (list (numTE))
                (if0 (sub (id 'y) (num 1))
                  (id 'y)
                  (add (id 'z) (app (id 'x) (list (sub (id 'y) (num 1)))))
                ))
              (app (id 'x) (list (num 10)))
            ))
            (list (num 10)))
      )
      (numV 91))

(test (eval (bool false)) (boolV false))

(test   (eval
            (with-type 't1 'v1 (numTE)
                           'v2 (boolTE)
                (app (id 'v1) (list (num 42)))
            )
        )
        (variantV #f (numV 42))
)
(test   (eval
            (with-type 't1 'v1 (numTE)
                           'v2 (boolTE)
                (app (id 'v2) (list (bool false)))
            )
        )
        (variantV #t (boolV false))
)
(test/exn (eval
            (with-type 't1 'v1 (numTE)
                           'v2 (boolTE)
                (app (id 'v2) (list (num 3)))
            )
        )
        "typecheck"
)

(test   (eval
            (with-type 't1 'v1 (numTE)
                           'v2 (boolTE)
                (cases 't1 (app (id 'v1) (list (num 2)))
                    'v1 'x (add (id 'x) (num 1))
                    'v2 'y (num 2)
                )
            )
        )
        (numV 3)
)
(test   (eval
            (with-type 't1 'v1 (numTE)
                           'v2 (boolTE)
                (cases 't1 (app (id 'v2) (list (bool false)))
                    'v1 'x (add (id 'x) (num 1))
                    'v2 'y (num 2)
                )
            )
        )
        (numV 2)
)

(test   (eval
            (with-type 't1 'v1 (numTE)
                           'v2 (boolTE)
                (app
                  (fun (list 'x) (list (idTE 't1)) (num 10))
                  (list (app (id 'v1) (list (num 5))))
                )
            )
        )
        (numV 10)
)
(test   (eval
            (with-type 't1 'v1 (numTE)
                           'v2 (boolTE)
                (with-type 'q1 'z1 (boolTE)
                               'z2 (numTE)
                    (app (id 'v1) (list (num 42)))
                )
            )
        )
        (variantV #f (numV 42)))
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
;(test (typecheck (if0 (num 0) (num 1) (num 2))
;                 (mtEnv))
;      (numT))
;(test (typecheck (if0 (num 0) 
;                      (fun 'x (numTE) (id 'x))
;                      (fun 'y (numTE) (num 3)))
;                 (mtEnv))
;      (arrowT (numT) (numT)))
;(test (typecheck (rec 'a (numTE)
;                   (num 10)
;                   (add (id 'a) (num 1)))
;                 (mtEnv))
;      (numT))
;(test (typecheck (rec 'fib (arrowTE (numTE) (numTE))
;                   (fun 'x (numTE)
;                        (if0 (id' x)
;                             (num 1)
;                             (if0 (sub (id 'x) (num 1))
;                                  (num 1)
;                                  (add (app (id 'fib) (sub (id 'x) (num 1)))
;                                       (app (id 'fib) (sub (id 'x) (num 2)))))))
;                   (app (id 'fib) (num 4)))
;                 (mtEnv))
;      (numT))
;
;
;(test (typecheck (with-type 'fruit 'apple (numTE)
;                            'banana (arrowTE (numTE) (numTE))
;                            (app (id 'apple) (num 10)))
;                 (mtEnv))
;      (idT 'fruit))
;
;(test (typecheck (with-type 'fruit 'apple (numTE)
;                            'banana (arrowTE (numTE) (numTE))
;                            (fun 'x (idTE 'fruit) (num 10)))
;                 (mtEnv))
;      (arrowT (idT 'fruit) (numT)))
;
;(test (typecheck (with-type 'fruit 'apple (numTE)
;                            'banana (arrowTE (numTE) (numTE))
;                            (cases 'fruit (app (id 'apple) (num 10))
;                              'apple 'y (add (id 'y) (num 1))
;                              'banana 'x (app (id 'x) (num 10))))
;                 (mtEnv))
;      (numT))
;
;(test (typecheck (with-type 'fruit 'apple (numTE)
;                            'banana (arrowTE (numTE) (numTE))
;                            (cases 'fruit (app (id 'banana) (fun 'x (numTE) (sub (id 'x) (num 1))))
;                              'apple 'y (add (id 'y) (num 1))
;                              'banana 'x (app (id 'x) (num 10))))
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
(test/exn (typecheck (if0 (num 0) 
                          (num 7)
                          (fun (list 'y) (list (numTE)) (num 3)))
                     (mtEnv))
          "no type")
(test/exn (typecheck (rec 'x (numTE)
                       (fun (list 'y) (list (numTE)) (num 3))
                       (num 10))
                     (mtEnv))
          "no type")
;(test/exn (typecheck (rec 'x (arrowTE (numTE) (numTE))
;                       (fun 'y (numTE) (num 3))
;                       (add (num 1) (id 'x)))
;                     (mtEnv))
;          "no type")
;
;(test/exn (typecheck (fun 'x (idTE 'fruit) (id 'x))
;                     (mtEnv))
;          "no type")
;
;;; cases in wrong order:
;(test/exn (typecheck (with-type 'fruit 'apple (numTE)
;                                'banana (arrowTE (numTE) (numTE))
;                                (cases 'fruit (app (id 'apple) (num 10))
;                                  'banana 'y (add (id 'y) (num 1))
;                                  'apple 'x (app (id 'x) (num 10))))
;                     (mtEnv))
;          "no type")
;
;(test/exn (typecheck (with-type 'fruit 'apple (numTE)
;                                'banana (arrowTE (numTE) (numTE))
;                                (cases 'fruit (app (id 'apple) (num 10))
;                                  'apple 'y (app (id 'y) (num 1))
;                                  'banana 'x (app (id 'x) (num 10))))
;                     (mtEnv))
;          "no type")
;
;(test/exn (typecheck (with-type 'fruit 'apple (numTE)
;                                'banana (arrowTE (numTE) (numTE))
;                                (cases 'fruit (app (id 'apple) (num 10))
;                                  'apple 'y (add (id 'y) (num 1))
;                                  'banana 'x (add (id 'x) (num 10))))
;                     (mtEnv))
;          "no type")
;
;(test/exn (typecheck (with-type 'fruit 'apple (numTE)
;                                'banana (arrowTE (numTE) (numTE))
;                                (app (id 'apple) (fun 'x (numTE) (id 'x))))
;                     (mtEnv))
;          "no type")
;
;(test/exn (typecheck (with-type 'fruit 'apple (numTE)
;                                'banana (arrowTE (numTE) (numTE))
;                                (app (id 'banana) (num 10)))
;                     (mtEnv))
;          "no type")