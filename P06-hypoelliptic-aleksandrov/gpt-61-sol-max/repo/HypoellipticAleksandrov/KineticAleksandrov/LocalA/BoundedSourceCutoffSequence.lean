module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.UniquenessMeasure
public import Mathlib.Topology.Compactness.SigmaCompact
public import PDEFoundation.Calculus.RegularityOrder


/-! # Smooth compact cutoffs exhausting an open source domain -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open Set Filter


/-- Every open finite-dimensional domain has bounded smooth cutoffs eventually equal to one
at each of its points. Their closed supports stay inside the literal domain. -/
theorem exists_boundedSourceCutoffSequence
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (U : Set E) (hU : IsOpen U) :
    ∃ χ : ℕ → E → ℝ,
      (∀ n, ContDiff ℝ PDE.smoothOrder (χ n) ∧ HasCompactSupport (χ n) ∧ tsupport (χ n) ⊆ U) ∧
      (∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1) ∧
      ∀ x ∈ U, ∀ᶠ n in atTop, χ n x = 1 := by
  classical
  let  := hU.locallyCompactSpace
  let C (n : ℕ) : Set E := Subtype.val '' compactCovering U n
  have hC (n : ℕ)  :=
    (isCompact_compactCovering U n).image continuous_subtype_val
  have hCU (n : ℕ) : C n ⊆ U := by
    rintro x ⟨y, _, rfl⟩
    exact y.2
  have hex (n : ℕ) := exists_smooth_cutoff (hC n) hU (hCU n)
  choose χ hs hc hsub hb he using hex
  refine ⟨χ, fun n => ⟨hs n, hc n, hsub n⟩, hb, ?_⟩
  intro x hx
  obtain ⟨n, hn⟩ := exists_mem_compactCovering (⟨x, hx⟩ : U)
  filter_upwards [eventually_ge_atTop n] with m hm
  exact he m x ⟨⟨x, hx⟩, compactCovering_subset U hm hn, rfl⟩

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
