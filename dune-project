(lang dune 2.9)
(using coq 0.3)
(name coq-ctree)

(license "GPLv3")
(authors "REDACTED")
(maintainers "REDACTED")

(generate_opam_files true)

(package
 (name coq-ctree)
 (synopsis "Library for representing recursive, non-deterministic and impure programs with equational reasoning")
 (version 0.1)
 (depends
  (coq (>= 8.15))
  (coq-ext-lib (>= 0.11.3))
  (coq-coinduction (>= 1.3))
  (coq-relation-algebra (>= 1.7))
  (coq-equations (>= 1.2))
  (coq-itree (>= 5.0)))
)
