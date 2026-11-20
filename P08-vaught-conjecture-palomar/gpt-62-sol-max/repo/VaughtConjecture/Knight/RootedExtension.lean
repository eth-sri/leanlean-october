/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RootedKarp
public import VaughtConjecture.Knight.PairedTrace

/-! # The core-rooted extension property and its back-and-forth consumer

Knight's Prop. 7.3.3 is a ONE-model, core-rooted extension theorem: over tuples containing a
finite core, every coface satisfying the forced characteristic-arity/anchor restrictions is
realized.  Prop. 10.2.1 then says "apply Prop. 7.3.3 and perform a back-and-forth".  This
module compiles that back-and-forth, generically:

* `RootedAdmissibility α` — a predicate on rooted extensions (root embedding, base label,
  extension label);
* `RootedExtensionOver W core Adm` — over every evaluated tuple containing `core`, every
  admissible rooted extension of the realized label is realized in `W`;
* `RealizedAdmissible W Adm` — every realized rooted extension is admissible;
* `restrictedStepSupply_of_rootedExtension` — the extension property for ONE shared
  admissibility predicate, with every realized extension admissible, yields the selected
  transfer step below every common chart containing the cores;
* `nonempty_iso_of_rootedExtension` — hence two exactly-consistent covering realizations on
  countable carriers with cores of equal label are isomorphic.

This is a SUFFICIENT ADAPTER for the pair-local interface of `TerminalParameterCode`
(`PairLocalTerminalData`): the seed's actual consumer (Prop. 10.2.1) only alternates
Prop. 7.3.3 in a back-and-forth, i.e. needs one selected transfer step at each reached
common chart, not a global one-model extension theory.

The proof is the restricted common-chart step supply below core-containing nodes, seeded by
the cores (`nonempty_iso_of_restrictedCommonChartStepSupply`): a scheduled new point is
absorbed by covering into a realized rooted extension, which is admissible, hence realized
over the other side's chart by the extension property.  No universal menu intersection
between arbitrary source models is involved. -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower KnightRealization

universe w

/-- An admissibility predicate on rooted extensions: root embedding, base label, extension
label. -/
abbrev RootedAdmissibility (α : LimitStage) : Type 1 :=
  ∀ {n N : ℕ}, (Fin n ↪ Fin N) → S α.1 n → S α.1 N → Prop

variable {α : LimitStage} {M : Type w}

/-- **The core-rooted extension property** (Prop. 7.3.3 shape): over every evaluated tuple
containing the core, every admissible rooted extension of the realized label is realized. -/
def RootedExtensionOver (W : KnightRealization α M) {c : ℕ} (core : Fin c ↪ M)
    (Adm : RootedAdmissibility α) : Prop :=
  ∀ {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n), (∃ e : Fin c ↪ Fin n, e.trans t = core) →
    W.eval t = some p →
    ∀ {N : ℕ} (f : Fin n ↪ Fin N) (P : S α.1 N), typeMap f P = some p → Adm f p P →
      ∃ u : Fin N ↪ M, f.trans u = t ∧ W.eval u = some P

/-- The rooted embedding of a chart into a covering of its one-point extension. -/
theorem trans_snoc_cover {n k : ℕ} {t : Fin n ↪ M} {x : M} {hx : x ∉ Set.range t}
    {s : Fin (n + 1 + k) ↪ M} (hst : (Fin.castAddEmb k).trans s = snoc t x hx) :
    (Fin.castSuccEmb.trans (Fin.castAddEmb k)).trans s = t := by
  ext i
  have h := DFunLike.congr_fun hst (Fin.castSucc i)
  simp only [Function.Embedding.trans_apply, Fin.castAddEmb_apply] at h
  change s (Fin.castAdd k (Fin.castSucc i)) = t i
  rw [h]
  exact snoc_apply_castSucc t x hx i

theorem cover_mem_range {n k : ℕ} {t : Fin n ↪ M} {x : M} {hx : x ∉ Set.range t}
    {s : Fin (n + 1 + k) ↪ M} (hst : (Fin.castAddEmb k).trans s = snoc t x hx) :
    ∃ i, s i = x := by
  refine ⟨Fin.castAdd k (Fin.last n), ?_⟩
  have h := DFunLike.congr_fun hst (Fin.last n)
  simp only [Function.Embedding.trans_apply, Fin.castAddEmb_apply] at h
  rw [h]
  exact snoc_apply_last t x hx

end VaughtConjecture.Knight
