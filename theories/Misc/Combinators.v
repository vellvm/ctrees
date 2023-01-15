From ITree Require Import
     Indexed.Sum.

From CTree Require Import
     CTree
     Head
     Take
     Fold
     Eq.

From ExtLib Require Import
     Monad.

Import CTreeNotations Monads.
Local Open Scope ctree_scope.

Module CTreeCombinators.
  
  (*| Empty ctree |*)
  Definition nil{E C X} `{B0 -< C}: ctree E C X := stuckS.

  (*| Repeat a process an infinite but countable number of times |*)
  (* LEF: This currently drops the return value [x: X] of [t],
     not sure if we can maintain this. |*)
  Definition kleene_star{E C X} `{BN -< C} `{B0 -< C}
             (t: ctree E C X): ctree E C X :=
    let fix ntimes (i: nat) (k: ctree E C X): ctree E C X :=
      match i with
      | 0 => nil
      | S n => k ;; ntimes n k
      end in
    n <- branch false (branchN);;
    ntimes n t.

  (*| p + := p ;; p* |*)
  Definition kleene_plus{E C X} `{BN -< C} `{B0 -< C}
             (t: ctree E C X) : ctree E C X := t ;; kleene_star t.

  (*| Base constructor -- prepend an event [a] to a tree [P] |*)
  Definition prefix {E C X Y} (a : E Y) (P: ctree E C X) : ctree E C X :=
    trigger a;; P.

  (*| Nondeterministic choice |*)
  Definition plus {E C X F} `{B2 -< C}(P: ctree E C X) (Q: ctree F C X): ctree (E +' F) C X :=
    brD2 (translate inl1 P) (translate inr1 Q).

  (*| Parallel composition, no synchronization |*)
  Definition para{E C X F} `{B0 -< C} `{B2 -< C}(a: ctree E C X)(b: ctree F C X): ctree (E +' F) C X :=
    let cofix F {E}(P : ctree E C X) (Q : ctree E C X) :=
      brD2
        (rP <- head P;;
         match rP with
         | ARet rP => stuckD
         | ABr c kP => BrS c (fun i => F (kP i) Q)
         | AVis e kP => Vis e (fun i => F (kP i) Q)
         end)

        (rQ <- head Q;;
         match rQ with
         | ARet rQ => stuckD
         | ABr c kQ => BrS c (fun i => F P (kQ i))
         | AVis e kQ => Vis e (fun i => F P (kQ i))
         end) in
    F (translate inl1 a) (translate inr1 b).

  (*| Fair parallel operator, warning: not associative |*)
  Definition fair{E C X F}`{B2 -< C}`{BN -< C}(a: ctree E C X)(b: ctree F C X):
    ctree (E +' F) C X :=
    let cofix F {E} (P : ctree E C X) (Q : ctree E C X) :=
      brD2 
        (n <- branch false (branchN) ;;      
         p <- take n P ;;
         q <- take 1 Q ;; (* this is equivalent to [head] *)
         F p q)
        (n <- branch false (branchN) ;;
         q <- take n Q ;;
         p <- take 1 P ;;
         F p q) in
    F (translate inl1 a) (translate inr1 b).          

  Declare Scope ctree_combinator_scope.
  Notation "p *" := (kleene_star p) (at level 40): ctree_combinator_scope.
  Notation "p +" := (kleene_plus p) (at level 40): ctree_combinator_scope.
  Notation "a ∥ b" := (para a b) (at level 40, left associativity): ctree_combinator_scope.
  Notation "a ➢ n" := (take n a) (at level 40, left associativity): ctree_combinator_scope.
  Notation "a ⋄ b" := (fair a b) (at level 40, left associativity): ctree_combinator_scope.

End CTreeCombinators.

