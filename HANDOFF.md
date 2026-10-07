# Handoff: ctrees old/alt refactor (branch `askrcv`)

State as of 2026-10-06. Last commit `6b8d672`. Uncommitted: `theories/Eq/Trans.v` (new `inv_trans` cases, see §3) and `theories/Interp/FoldCTree.v` (the user is editing the counterexample; do not touch it).

## 1. Ground rules (from the user — follow exactly)

- Read `~/.claude/CLAUDE.md`. Proof work goes through a scratch copy `<Base>_scratch.v` next to the target (check it does not exist first), then copy back, targeted build, delete scratch. Never commit `*_scratch.v`. Never `dune build` the whole tree unless asked; use targeted `dune build path/File.vo`.
- Auto-memory lives in `~/.claude/projects/-Users-rogerab-home-research-coinduction-ctrees/memory/`. Read `MEMORY.md` first. Key rules there:
  - **No own writing in files**: no comments, docstrings or prose in `.v` files. If a comment seems needed, propose it in chat. (Error-message strings in tactics were explicitly approved.)
  - In chat, write chain elements as `elem R`, never the backtick notation (it breaks markdown).
  - **Flag dead code** (unused definitions, imports, commented-out code) whenever you see it; get review before removing.
  - `rereview-after-full-build.md`: items deliberately kept until the whole repo builds.
  - `queued-step4-folder-move.md`: the folder move, queued; do not start without the user's go.
- If a fix needs real proof/design work (not a rename or premise reshuffle), flag it and stop rather than invent machinery. The user decides.
- Commit only when asked. The user checkpoints often; suggest a commit before big moves.

## 2. Goal and architecture

Two parallel sides, sharing only `Equ`/`Shallow`, with per-layer bridges:

```
   old (theories/Eq)        bridges (theories/Eq/OldAltEquiv)      alt (theories/Eq)
   SBisim  <------------------  SBisimEquiv  ------------------>  SBisimAlt
     |                                                               |
   SSim    <------------------  SSimEquiv    ------------------>  SSimAlt
     |                                                               |
   Epsilon <------------------  EpsilonEquiv ------------------>  EpsilonAlt
     |                                                               |
   Trans   <------------------  TransEquiv   ------------------>  TransAlt
        \                                                          /
         +-------------------->  Equ  ->  Shallow  <--------------+
   Side modules (old only): CSSim -> SBisim, Visible, WBisim, Trace
```

- The alt side imports nothing from the old side. Only `OldAltEquiv/*` and clients (e.g. `IterFacts`, `examples/AltBisim`) see both.
- `theories/Eq.v` is the aggregator: it **exports** the old side and **privately imports** (`Require Import`, not `Export`) `SSimAlt`/`SBisimAlt` so its global tactic dispatchers (`step`, `step in`, `coinduction`, `upto_bind`, `upto_bind_eq`, `upto_bind with`) cover `equ`, `sbisim`, `ssim`, `cssim`, `sbisim'`, `ssim'`. Every per-file tactic override must stay `#[local]`; only `Eq.v` defines global ones.
- Why not export alt from `Eq.v`: `Trans` and `TransAlt` share ~171 names (`S`, `label`, `lrel`, `Leq`, `Seq`, `upd_rel`, `trans_*`, …). Exporting would silently shadow old names for every client.

Three "versions" of the old semantics exist; keep them straight:
1. Pre-refactor (deleted `SBisim_old.v`, branch `dev`): relations on trees, `obs e v` label (one step per `Vis`), label relations `rel (label E) (label F)`, `update_val_rel`, notation `~`.
2. Current old side: states `S = Active t | Passive e k` (coercion `α`), labels `τ | ask e | rcv e v | val v` (typed by return type), label relations as record `lrel E F X Y` (`RR`, `Rask`, `Rrcv`) with `build_rel`, `upd_rel`, `Leq`, `Lvrel`, `flipL`; `trans` up to `equ` over setoid `Seq`/`⩸`. Notation `≃`/`≲`. Step rules lost the `step_` prefix (`step_ss_br_r` → `ss_br_r`, `sb_guard` → `sbisim_guard`).
3. Alt side (`sbisim'`/`ssim'`): ε is a real label; proofs through `Br`/`Guard` loops become plain coinduction. Equivalences 2↔3: `ssim_ssim'` (SSimEquiv), `sbisim_sbisim'` (SBisimEquiv).

Clients written for version 1 are what is broken. Switching them to the alt side does not help: alt has the same state/`lrel` API.

## 3. Recently added infrastructure (know these)

- `sbisimT L t u := sbisim L (α t) (α u)` (SBisim.v), `ssimT` likewise (SSim.v). Notations `≃`, `≲`, `(≃ L)`, `(≃[Q])`, `(≲ L)`, `(≲[Q])` now mean the **tree-level** `sbisimT`/`ssimT`. State-level statements use `sbisimeq` / `sbisim L` explicitly (e.g. anything about a `trans` successor).
- Instances: `Equivalence (sbisimT Leq)`, `PreOrder (ssimT Leq)`, `equ` subrelation, `Active_sbisimT`/`Active_ssimT` (bridge tree→state so existing state-level `Proper` instances apply), `sbisimT_goal`, `sbisimT_ssimT_goal`, congruences `bind_*`, `GuardF_*`, `StepF_*`, `BrF_*`, `VisF_*` (through `going`, mirroring `Equ.v`). So `rewrite sbisim_guard` works under constructors and inside chain goals again.
- Tactics unfold `sbisimT`/`ssimT` first. When rewriting with a state-level lemma (e.g. `sbisim_sbisim'`, `ssim_ssim'`) on a tree-level goal, `unfold sbisimT` / `unfold ssimT` first.
- `ss_vis_eq`, `sb_vis_eq`: old-shape `vis` rules for `Leq` (discharge `Rask`/`Rrcv`).
- Old-`sbisim` bind: `sbisim_clo_bind_eq`, `sbisim_clo_bind_gen_eq`, tactics `__upto_bind_sbisim`, `__eupto_bind_sbisim`, `__upto_bind_sbisim_eq`.
- `ReflexiveL L` (TransAlt): reflexivity on non-ε labels (plain `Reflexive` is impossible since `build_rel` never relates ε). Used by the alt `refl_*` instances.
- `epsilon_det' := guard_alt^*` (EpsilonAlt) replaces the tree-level `epsilon_det` on the alt side. `use_steps` / `use n steps` live in EpsilonAlt.
- `step_ss'_passive(_id)`, `step_sb'_passive(_id)`: stepping two `Passive` states.
- Uncommitted in `Trans.v`: `inv_trans_one` gained cases for `α (CTree.bind _ _)` (via `trans_bind_inv`) and `α (CTree.trigger _)` (unfold to `Vis`). Core set builds with it.

## 4. Build status

Core set (all build): `theories/Eq.v`, `Eq/{Visible,Epsilon,SSim,SBisim,CSSim,TransAlt,EpsilonAlt,SSimAlt,SBisimAlt,IterFacts}`, `Eq/OldAltEquiv/*`, `Misc/Pure`, `Interp/Fold`, `examples/AltBisim/BisimExample`, `examples/SimpleSim/SimExample`. Re-check this set after every change.

Root failures (everything else failing is blocked behind these):

| Where | Cause | Status |
|---|---|---|
| `Interp/FoldCTree.v` CounterExample (~line 329) | `x <- trigger voidE;; …` is no longer stuck: `Vis` now takes an `ask` step before any answer, so `t1 ≃ t2` is false | **User is fixing this personally.** Do not touch. |
| `Interp/FoldCTree.v` `trans_obs_interp_step/_pure` | use removed `obs` label; unused anywhere | needs restating with `ask`/`rcv`, or deletion (ask user) |
| `Interp/FoldStateT.v` after `End InterpState.` | `ssim_interp_state_h`, `ssim_interp_h`, `interp_state_ssim/_sbisim(_eq)`, `trans_obs_interp_state_*` stated over version-1 label API (`update_val_rel`, `lift_val_rel`, `Lequiv_*`, `obs`, `sbt'_clo_bind`) | needs restatement over `lrel`/`upd_rel` (design: ask user). Blocks `ImpBr` (line 197), `Yield`, tests |
| `Interp/Refine.v` `refine_ctree_ssim` and next theorem | written against an older alt API (`step_ss'_vis_id … split`, `ss'_clo_bind with (R0 := …)`) | port to current alt API (`step_ss'_vis_id` + `step_ss'_passive_id`, `bind_chain_gen`/`ssim'_clo_bind`) |
| `Interp/ITree.v` `embed_trans_productive_aux` | inducts over old observe-based `trans_` internals | re-prove over `transR` |
| `Misc/Head.v` | ~400 lines built on `obs` (`desobs`, `trans_head`); `examples/CCS/Denotation.v` uses it ~20× and relies on one-step `obs` for synchronization | redesign; large |
| `Eq/WBisim.v` | `ws` must be redefined over states + `lrel` (draft: same shape as `ss` with `wtrans` on the answer side); 44 declarations follow | large; only `examples/Yield/Lang` uses it |
| `Eq/Trace.v:92` | half-ported proof (`erewrite (ActAct)`) | redo on top of §3 infrastructure |
| `examples/CCS/Denotation.v:315,497`, `examples/Yield/Util.v:56` | relate a state through `new c …` / use old `trans_` | part of the CCS/Yield ports |

Mechanical renames already applied in `ImpBr`, `Yield/*`, `CCS/*` (`~` → `≃`), unverified where the file is still blocked.

## 5. Next steps, in order

1. Wait for the user's counterexample fix in `FoldCTree.v`; suggest a commit (Trans.v `inv_trans` change is pending).
2. With the user, decide the `lrel` restatements for the second half of `FoldStateT.v` (and whether to delete the two unused `obs` lemmas in `FoldCTree.v`). Then port `FoldStateT`, then `ImpBr`, `Refine`, `ITree`, `Internalize`, tests.
3. Port `Refine.v`'s two alt-side theorems to the current alt API.
4. `Head` + `CCS` redesign, `WBisim` redefinition, `Trace` repair: each is a design task; propose a plan before writing proofs.
5. When the whole repo builds: raise the `rereview-after-full-build` list (TransAlt's ~873 lines of commented-out code, `lift_rel3`, `sss`, the alt weak-transition family, untested imports) for removal review.
6. Then, on the user's go: the queued step 4 (`queued-step4-folder-move.md`): move to `theories/Eq/Old/{Trans,Epsilon,SSim,SBisim}.v` and `theories/Eq/Alt/{Trans,Epsilon,SSim,SBisim}.v`, keep lemma names, update imports repo-wide, qualify shared names (`Old.Trans.S` / `Alt.Trans.S`); remove the CSSim-related header comments in `SBisim.v` (approved); fix `Eq.v` and `IterFacts`; report downstream breakage.

## 6. Tooling and pitfalls

- Targeted builds: `dune build theories/Eq/X.vo`. Filter noise with `grep -v -i "deprecated\|Hint: To disable\|warnings (dep\|Rocq Build"`. dune keeps going by default (no `--keep-going` flag).
- dune rebuilds by content hash; an mtime-newer `.v` with an older `.vo` is not necessarily stale.
- Shell is zsh: `$VAR:t…` in `"${B}:path"` must be braced (`"${B}:theories/…"`); `echo ====` errors (quote it); unquoted `$LIST` does not word-split (use arrays or `${=LIST}`).
- `rocq-mcp` (`rocq_start`/`rocq_check`/`rocq_query`) is registered and works for reading goals (start by file position, 0-indexed). `rocq-piler`'s `insert_tactics` fails on files with Unicode notations; use it only for `focus_proof`, and it cannot find `Instance`s by name.
- A file cannot use qualified references to its own module name under a different scratch name (e.g. `TransAlt.S` inside `TransAlt.v`); for such files, test additions in a probe file that imports the real module.
- To survey breakage below a blocked file without touching the real tree: `rsync -a --exclude .git ./ <scratchpad>/ctrees-copy/`, admit the blockers there, build downstream, port only verified fixes back.
- Notation leaks: alt files must `Require Import` (not `Export`) RelationAlgebra's `monoid kat kat_tac`; re-exporting them breaks ExtLib's `MonadNotation` in clients.
- `Guard t`, `Step t`, `Vis e k`, `Br c k` are notations for `go (…F …)`; `Proper` instances go on `GuardF`/`StepF`/`BrF`/`VisF` into `going R` (see `Equ.v`), not on the notations.
- `~` is also logical negation; never rename it blindly.
- Dependency-analysis scripts (glob-based, exact for names, approximate for tactics) were in a session scratchpad and are gone; `.glob` files under `_build/default` are the reliable source for "who uses what".
