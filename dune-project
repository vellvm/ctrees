(lang dune 3.8)
(using coq 0.7)
(name coq-ctree)

(license "MIT")
(authors "Nicolas Chappe" "Paul He" "Ludovic Henrio" "Yannick Zakowski" "Steve Zdancewic")
(maintainers "Yannick Zakowski")
(source (github vellvm/ctrees))
(bug_reports "https://github.com/vellvm/ctrees/issues")

(generate_opam_files true)

(package
 (name coq-ctree)
 (synopsis "Library for representing recursive, non-deterministic and impure programs with equational reasoning")
 (version 0.1)
 (depends
  (coq (= 8.20.1))
  (coq-ext-lib (>= 0.11.3))
  (coq-coinduction (= 1.20))
  (coq-relation-algebra (>= 1.7.11))
  (coq-equations (>= 1.2))
  (coq-itree (>= 5.0)))
)
