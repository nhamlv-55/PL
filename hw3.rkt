#lang plai
(define (symbol<? a b) (string<? (symbol->string a) (symbol->string b)))

(define-type WAE
  [num (n number?)]
  [add (lhs WAE?) (rhs WAE?)]
  [sub (lhs WAE?) (rhs WAE?)]
  [with (name symbol?)
        (named-expr WAE?)
        (body WAE?)]
  [id (name symbol?)])

;search-and-destroy: list element -> list
;to search and remove all instance of an element in a list
;search-and-destroy x (list 'x 'y 'z 'a 's 'f 'b 'g 'z 'x 'x 'x 'x 'x 'a 'b 'x 'o)
;should return '(y z a s f b g z a b o)
(define (search-and-destroy x ls)
  (cond
   [(null? ls) '()]
   [(eqv? x (first ls)) (search-and-destroy x (rest ls))]
   [else (cons (first ls) (search-and-destroy x (rest ls)) )]
   )
)
(define list1 (list 'x 'y 'z 'a 's 'f 'b 'g 'z 'x 'x 'x 'x 'x 'a 'b 'x 'o))
(test (search-and-destroy 'x list1) '(y z a s f b g z a b o))
;wae1:
(define wae1 (with 'y (num 5) (add (num 8) (sub (id 'a) (num 2))))
  )

;wae2:
;{+ 
; {with {x {+ 1 2}} {+ x {+ y z}}
; {with {a {- 4 3}} {+ c y}}
; }

(define wae2
  (add
   (with 'x (add (num 1) (num 2) ) (add (id 'x) (add (id 'y) (id 'z))) )
   (with 'a (sub (num 4) (num 3) ) (add (id 'c) (id 'y)) )
   )
  )
;wae3:
;{+  {with {y 5}{
;                {with {x {+ 1 2}} {+ x y }}
;               }
;    }
; 6
; }

(define wae3
  (add
   (with 'y (num 5) 
         {with 'x (add (num 1) (num 2))  
               (add (id 'x) (id 'y))} 
   )
   (num 5)
  )
)
;wae5:
;{with {x 5}
;   {with {x x} {y}}
;}
(define wae5 
  (with 'x (num 5)
        (with 'x (id 'x) (id 'y))
   )
  )


;wae4:
;{+ 
; {with {x {+ 1 2}} {+ t {+ y z}}
; {with {x {- 4 3}} {+ c y}}
; }

(define wae4
  (add
   (with 'x (add (num 1) (num 2) ) (add (id 't) (add (id 'y) (id 'z))) )
   (with 'x (sub (num 4) (num 3) ) (add (id 'c) (id 'y)) )
   )
  )

;wae6:
;{+ 
; {with {x {with{a} {+ 2 3} {+a b}}} {+ x {+ y z}}
; {with {x {- 4 3}} {+ c y}}
; }

(define wae6
  (add
   (with 'x (with 'a (add (num 2) (num 3)) (add (id 'a) (id 'b)) )
         (add (id 'x) (add (id 'y) (id 'z))) )
   (with 'x (sub (num 4) (num 3) ) (add (id 'c) (id 'y)) )
   )
  )

;wae7:
;{+ 
; {with {x {with{x} {+ 2 3} {+a b}}} {+ x {+ y z}}
; {with {x {- 4 3}} {+ c y}}
; }

(define wae7
  (add
   (with 'x (with 'x (add (num 2) (num 3)) (add (id 'a) (id 'b)) )
         (add (id 'x) (add (id 'y) (id 'z))) )
   (with 'x (sub (num 4) (num 3) ) (add (id 'c) (id 'y)) )
   )
  )


;get-free-ids: WAE -> list
;to give an unsorted list of free ids in an wae
;get-free-ids wae1 should return '(a)
;get-free-ids wae2 should return '(y z c x)
;get-free-ids wae3 should return '()
;get-free-ids wae4 should return '(t y z c y)
;get-free-ids wae6 should return '(y z b c y)
(define (get-free-ids wae)
  (type-case WAE wae
    [num (n) empty]
    [add (l r)
         (append (get-free-ids l) (get-free-ids r) )]
    [sub (l r)
         (append (get-free-ids l) (get-free-ids r) )]
    [with (name expr body)
          (append
           (search-and-destroy name (get-free-ids body))
           (search-and-destroy name (get-free-ids expr))
           )]
    [id (x)
     (list x)]
    )
  )
(test (get-free-ids wae1) '(a))
(test (get-free-ids wae2) '(y z c y))
(test (get-free-ids wae3) '())
(test (get-free-ids wae4) '(t y z c y))
(test (get-free-ids wae6) '(y z b c y))
;free-ids: WAE -> list
;to give the list of free ids in WAE, sorted, no duplicates
;free-ids wae1 should return '(a)
;free-ids wae2 should return '(c y z)
;free-ids wae3 should return '()
;free-ids wae4 should return '(c t y z)
;free-ids wae6 should return '(b c y z)
(define (free-ids wae)
  (sort(remove-duplicates(get-free-ids wae)) symbol<?)
)

(test (free-ids wae1) '(a))
(test (free-ids wae2) '(c y z))
(test (free-ids wae3) '())
(test (free-ids wae4) '(c t y z))
(test (free-ids wae6) '(b c y z))

;get-binding-ids:WAE -> list
;to give an unsorted list of binding ids in an wae
;get-binding-ids wae1 should return '(y)
;get-binding-ids wae2 should return '(x a)
;get-binding-ids wae3 should return '(y x)
;get-binding-ids wae4 should return '(x x)
(define (get-binding-ids wae)
  (type-case WAE wae
    [num (n) empty]
    [add (l r)
         (append (get-binding-ids l) (get-binding-ids r))]
    [sub (l r)
         (append (get-binding-ids l) (get-binding-ids r))]
    [with (name expr body)
          (append (list name) (append (get-binding-ids body) (get-binding-ids expr)))]
    [id (x)
        empty]
   )
  )

(test (get-binding-ids wae1) '(y))
(test (get-binding-ids wae2) '(x a))
(test (get-binding-ids wae3) '(y x))
(test (get-binding-ids wae4) '(x x))
;binding-ids:WAE -> list
;to give the list of binding ids, sorted, no duplicates
;binding-ids wae1 should return '(y)
;binding-ids wae2 should return '(a x)
;binding-ids wae3 should return '(x y)
;binding-ids wae4 should return '(x)
(define (binding-ids wae)
  (sort(remove-duplicates(get-binding-ids wae)) symbol<?)
)

(test (binding-ids wae1) '(y))
(test (binding-ids wae2) '(a x))
(test (binding-ids wae3) '(x y))
(test (binding-ids wae4) '(x))

;
(define (all-ref wae)
  (type-case WAE wae
    [num (n) empty]
    [add (l r)
         (append (all-ref l) (all-ref r))]
    [sub (l r)
         (append (all-ref l) (all-ref r))]
    [with (name expr body)
          (append (all-ref expr) (all-ref body))
          ]
    [id (x) 
        (list x)]
    )
  )
(define (ref wae)
  (sort(remove-duplicates(all-ref wae)) symbol<?)
  )

;get-subtraction: list list -> list
;return the difference between 2 lists, knowing that 1 list will contain another
;get-subtraction l3 l4 should return '(a b e d)
(define (get-subtraction list1 list2)
  (cond
    [(null? list1) empty]
    [(not (member (first list1) list2))
     (append (list (first list1)) (get-subtraction (rest list1) list2))]
    [else (get-subtraction (rest list1) list2)]
    )
)
;subtraction: list list -> list
;sorted and remove-duplicates from get-subtraction
;subtraction l3 l4 should return '(a b d e)
(define (subtraction list1 list2)
  (sort(remove-duplicates(get-subtraction list1 list2)) symbol<?)
  )
(define l3 (list 'a 'b 'c 'e 'd 'z 'f))
(define l4 (list 'f 'z 'c ))
(test (get-subtraction l3 l4) '(a b e d))
(test (subtraction l3 l4) '(a b d e))

;get-bound-ids: WAE->list
;to give an unsorted list of bound ids in an wae
;get-bound-ids wae1 should return '()
;get-bound-ids wae2 should return '(x)
;get-bound-ids wae3 should return '(y x)
;get-bound-ids wae4 should return '()
;get-bound-ids wae6 should return '(x a)
(define (get-bound-ids wae)
  (type-case WAE wae
    [num (n) empty]
    [add (l r)
         (append (get-bound-ids l) (get-bound-ids r))]
    [sub (l r)
         (append (get-bound-ids l) (get-bound-ids r))]
    [with (name expr body)
          (cond
            [(member name (free-ids body)  )   
                (append (list name) (append (get-bound-ids expr)(get-bound-ids body) ))]
            [else (append (get-bound-ids expr) (get-bound-ids body))])
          ]
    [id (x) empty]
   )
  )

(test (get-bound-ids wae1) '())
(test (get-bound-ids wae2) '(x))
(test (get-bound-ids wae3) '(y x))
(test (get-bound-ids wae4) '())
(test (get-bound-ids wae6) '(x a))
;bound-ids: WAE -> list
;to give the list of bound ids, sorted, no duplicates
;bound-ids wae1 should return '()
;bound-ids wae2 should return '(x)
;bound-ids wae3 should return '(x y)
;bound-ids wae4 should return '()
;bound-ids wae6 should return '(a x)

(define (bound-ids wae)
  (sort(remove-duplicates(subtraction (ref wae) (free-ids wae))) symbol<?)
)

(test (bound-ids wae1) '())
(test (bound-ids wae2) '(x))
(test (bound-ids wae3) '(x y))
(test (bound-ids wae4) '())
(test (bound-ids wae6) '(a x))
(test (bound-ids wae5) '(x))
