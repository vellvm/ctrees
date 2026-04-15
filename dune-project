(lang dune 3.8)
(using coq 0.7)
(name rocq-ctree)

(license "MIT")
(authors "Nicolas Chappe" "Paul He" "Ludovic Henrio" "Yannick Zakowski" "Steve Zdancewic")
(maintainers "Yannick Zakowski")
(source (github vellvm/ctrees))
(bug_reports "https://github.com/vellvm/ctrees/issues")

(generate_opam_files true)

(package
 (name rocq-ctree)
 (synopsis "Library for representing recursive, non-deterministic and impure programs with equational reasoning")
 (version 2.0-dev)
 (depends
  (rocq-core (>= 9.0))
  (rocq-stdlib (>= 9.0))
  (coq-ext-lib (>= 0.11.3))
  (rocq-coinduction (>= 1.21))
  (rocq-relation-algebra (>= 1.8.0))
  (rocq-equations (>= 1.3.1))
  (coq-itree (>= 5.0)))
 (tags (
   "category:CS/Semantics and Compilation/Semantics"
   "category:CS/Concurrency/Theory of concurrent systems"
   "keyword:simulation"
   "keyword:bisimilarity"
   "keyword:coinduction up-to"
   "keyword:process algebra"
   "keyword:cooperative multithreading"
   "logpath:CTree"
 ))
)
