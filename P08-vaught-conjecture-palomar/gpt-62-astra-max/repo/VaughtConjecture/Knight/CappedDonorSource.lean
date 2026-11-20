/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorFields

/-! # The synchronized source-profile family and its normalization (the source-family adapter)

The **source profiles** are the specialization of the receiving family of
`Knight/CappedDonorReceiving.lean` in which the two-component state is one field vector: the
persistent value of every *present* field is the `1`-visible rounding of its numerical value
(`Synchronized`), while the persistent values of *future* fields are retained as they are.  Such
a state is determined by its single source vector `State.sourceProfile` (numerical values at
present fields, persistent values at future fields): `persistent = R₁ ∘ sourceProfile`
(`Synchronized`, `synchronized_iff`).

This is a specialization of the source family only.  Arbitrary physical sections are **not**
required to satisfy it (a positive persistent shadow with a bottom numerical owner at an inactive
controller is a legitimate physical section but not a source profile); nothing here extracts a
source profile from a physical section, and no positive-continuability filtering is imposed.

* **Resynchronization** (`resync`): recompute the present persistent fields from the numerical
  values, retain the future ones.  It preserves admissibility (`Admissible.resync`) and makes any
  admissible state synchronized (`resync_synchronized`); when the numerical fields agree with a
  synchronized state below a permissible cap, the cap receipts of every persistent field survive
  resynchronization (`resync_capReceipts`).
* **Both same-grade fibres on source profiles** (`exists_private_lift_sync`,
  `exists_request_lift_sync`): the general fibres followed by resynchronization — the lifted
  state is admissible and synchronized, retains the prescription literally and the other section
  below the cap, and carries **complete cap receipts** for every persistent field, present or
  future.  At bottom cap the general fibres already resynchronize (`offState`).
* **Normalization preservation** (`mapState`, `Admissible.map`, `Synchronized.map`): applying a
  bottom-reflecting normalized witness `σ` with suppressor `gTop K`, `K` at least the grades
  currently present and at least `1` (the arity form `K ≥ J` is `Admissible.map_of_arity`), to
  every field —
  the shape of the incoming normalization maps (`FiniteOrbitEmbedding.interpolate`,
  `SourceBlockPadding.pad`; `Admissible.interpolate`, `Admissible.pad`) — preserves admissibility
  and synchronization.  The selector commutes with such maps (`cut_map`, `sel_map`), so the
  numerical relation is preserved exactly; supports are preserved because `σ` reflects bottom. -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd AmalgamationPlan

namespace CappedDonor

namespace Ref

variable {I : Type*} [Fintype I] {nP N J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}
  {R : Ref I nP N J P C}

/-! ## The source profile and synchronization -/

/-- A present private cell as a present field. -/
def privCell {j} d (h : C.scheme.grade d ≤ j) : C.ClippedCells j :=
  ⟨d, (present_priv_iff j d).mpr h⟩

/-! ## Resynchronization -/

/-! ## Both same-grade fibres on source profiles -/

/-! ## Normalization preservation -/

section Map

variable {K : ℕ} {σ : ExtOrd → ExtOrd} (hσ : Witness (gTop K) σ)

include hσ

theorem map_comm {k} (hk : k ≤ K) x {i} (hi : i ≤ k) :
    σ (extVisibilityReplace x k i) = extVisibilityReplace (σ x) k i :=
  hσ.clause5 x k (by rw [gTop_of_le hk]; exact le_top) i hi

theorem selfVis_map {k} (hk : k ≤ K) {x} (h : SelfVis k x) : SelfVis k (σ x) := by
  change extVisibilityReplace (σ x) k k = σ x
  rw [← map_comm hσ hk x le_rfl, h]

theorem map_ne_bot_iff (hbot : ∀ x, σ x = ⊥ → x = ⊥) x : σ x ≠ ⊥ ↔ x ≠ ⊥ :=
  not_congr ⟨hbot x, fun h => by rw [h, hσ.bot]⟩

theorem map_sup (f : I → ExtOrd) :
    σ (Finset.univ.sup f) = Finset.univ.sup fun i => σ (f i) :=
  Finset.apply_sup_eq_sup_comp σ (fun _ _ => hσ.mono.map_max) hσ.bot

/-- The cut commutes with a normalized witness through `N`. -/
theorem cut_map (hN : N ≤ K) v : R.cut (fun d => σ (v d)) = σ (R.cut v) := by
  unfold cut
  rw [hσ.mono.map_min, map_sup hσ]
  congr 2
  funext i
  exact (map_comm hσ hN _ le_rfl).symm

/-- The selector commutes with a normalized witness through `N`. -/
theorem sel_map (hN : N ≤ K) v d :
    R.sel (fun d => σ (v d)) d = σ (R.sel v d) := by
  by_cases h : R.p d ≠ ⊥ ∧ R.p d ≠ ⊤
  · rw [R.sel_of_proper h, R.sel_of_proper h, cut_map hσ hN, hσ.mono.map_min,
      map_comm hσ hN _ (R.poff_lt d h).le]
  by_cases hb : R.p d = ⊥
  · rw [R.sel_of_bot hb, R.sel_of_bot hb, hσ.bot]
  · have ht := not_not.mp fun ht => h ⟨hb, ht⟩
    rw [R.sel_of_top ht, R.sel_of_top ht, cut_map hσ hN]

end Map

end Ref

end CappedDonor

end VaughtConjecture.Knight
