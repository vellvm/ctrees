From CTree Require Import 
	CTrees Equ Bisim.

From ITree Require Import 
	ITree.

(* TODO

[itrees] can be embedded into [ctrees] by simply translating
	[Tau] nodes into [Fork 1] nodes.
	We should have:

	eq_itree t u ->
	embed t ≅ embed u

	eutt t u ->
	embed t ≈ embed u

	We can define a (coinductive) predicate 
	_deterministic_ to check that a [ctree] does not 
	contain any other use of Fork than unary ones.
	These deterministic ctrees correspond to the ones
	we can embed back into itrees, and we should have
	similar equations.

*)

