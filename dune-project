(lang dune 2.9)
(using coq 0.2)
(name coq-ctree)

(package
  (name coq-ctree)
  (synopsis "Library for representing recursive, non-deterministic and impure programs with equational reasoning")
  (depends
    (coq (>= 8.13))
    (coq-ext-lib (>= 0.11.3))
    (coq-paco (>= 4.1.1)))
)
