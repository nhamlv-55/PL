;; run : string string -> number
(define (run body deffuncs)
    (if (equal? deffuncs "{}")
        (interp-wrapper (parse (string->sexpr body)) empty )
        (interp-wrapper (parse (string->sexpr body)) (list (parse-defn (string->sexpr deffuncs))))
    )
)

;; tests
(test (run "{get {get {rec {r {rec {z 0}}}} r} z}"  "{}") 0)
(test (run "{get {rec {a 1}} a}"                    "{}") 1)
(test (run "{get {rec {a 1} {b 2} {c 3}} a}"        "{}") 1)
(test (run "{rec {a 10} {b {+ 1 2}}}"               "{}") 'record)
(test (run "{get {rec {a 10} {b {+ 1 2}}} b}"       "{}") 3)
(test (run "{get {rec {r {rec {z 0}}}} r}"          "{}") 'record)
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
(test/exn (run "{rec {z {get {rec {z 0}} y}}}"      "{}") "interp: no such field")
(test/exn (run "{get {rec {b 10} {b {+ 1 2}}} b}"   "{}") "parse: duplicate fields")
(test/exn (run "{get {rec {a 10}} b}"               "{}") "no such field")

;; add.tests.0
(test/exn (run 1 "{}") "ring->sexpr: expects argument of type <string>")
(test/exn (run "'" "{}") "syntax error (bad contents)")
(test/exn (run "{+ 1 1} {+ 2 2}" "{}") "bad syntax (multiple expressions)")

;; add.tests.1
(test (run "{with {x 5} {+ x x}}" "{}") 10)
(test (run "{with {x {with {a 1} {+ a 4}}} {+ x x}}" "{}") 10)
(test (run "{with {x 5} {+ x {with {x 3} x}}}" "{}") 8)
(test (run "{with {y 5} {+ 3 {with {x 3} y}}}" "{}") 8)
(test (run "{with {y 5} { f y }}" "{ deffun {f x } x}") 5)
(test (run "{with {x 4} {rec {a x}}}"  "{}") 'record)
(test (run "{with {x 4} {get {rec {a x}} a}}"  "{}") 4)

;; add.tests.2
(define b (fromtorec (list (list 'a (list (list 'b (list (list 'numV 2))))))))
(test b (parse (string->sexpr "{rec {a {rec {b 2}}}}")))

(test (run "{with {x {rec {a 0}}} {get x a}}" "{}") 0)
(define a (fromtorec (list (list 'a (list (list 'numV 2))))))
(test a (parse (string->sexpr "{rec {a 2}}")))
