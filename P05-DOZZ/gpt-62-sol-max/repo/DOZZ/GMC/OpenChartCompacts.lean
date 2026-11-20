/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Compactness.SigmaCompact

/-! Compact exhaustions in the ambient plane, shared by test and integral approximations. -/

@[expose] public section
open Set
namespace DOZZ.Proofs

noncomputable def chartCompacts (U : Set ℂ) (hU : IsOpen U) (n : ℕ) : Set ℂ :=
  letI : LocallyCompactSpace U := hU.locallyCompactSpace
  Subtype.val '' (CompactExhaustion.choice U) n

theorem chartCompacts_spec (U : Set ℂ) (hU : IsOpen U) :
    (∀ n, IsCompact (chartCompacts U hU n)) ∧ (∀ n, chartCompacts U hU n ⊆ U) ∧
      Monotone (chartCompacts U hU) ∧ (⋃ n, chartCompacts U hU n) = U ∧
      ∀ L, IsCompact L → L ⊆ U → ∃ n, L ⊆ chartCompacts U hU n := by
  letI : LocallyCompactSpace U := hU.locallyCompactSpace
  let E := CompactExhaustion.choice U
  change (∀ n, IsCompact (Subtype.val '' E n)) ∧ (∀ n, Subtype.val '' E n ⊆ U) ∧
    Monotone (fun n => Subtype.val '' E n) ∧ (⋃ n, Subtype.val '' E n) = U ∧ _
  refine ⟨fun n => (E.isCompact n).image continuous_subtype_val,
    fun n => image_subset_iff.mpr fun x _ => x.2,
    fun _ _ h => image_mono (E.subset h), ?_, ?_⟩
  · rw [← image_iUnion, E.iUnion_eq, image_univ, Subtype.range_val]
  · intro L hL hLU
    let j : L → U := fun x => ⟨x.1, hLU x.2⟩
    letI : CompactSpace L := isCompact_iff_compactSpace.mp hL
    obtain ⟨n, hn⟩ := E.exists_superset_of_isCompact (isCompact_range (show Continuous j by fun_prop))
    exact ⟨n, fun x hx => ⟨j ⟨x,hx⟩, hn (mem_range_self (f := j) (⟨x,hx⟩ : L)), rfl⟩⟩

end DOZZ.Proofs
