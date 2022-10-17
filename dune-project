(lang dune 2.9)
(using coq 0.3)
(name coq-ctree)

(license "GPLv3")
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
  (coq (= 8.16.0))
  (coq-ext-lib (= 0.11.7))
  (coq-coinduction (= 1.6))
  (coq-mathcomp-ssreflect (= 1.15.0))
  (coq-aac-tactics (= 8.16.0))
  (coq-relation-algebra (= 1.7.8))
  (coq-equations (= 1.3+8.16))
  (coq-itree (= 5.0.0)))
)
