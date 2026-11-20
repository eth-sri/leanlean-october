module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.Compactness.LocallyFinite

/-! # Smooth cutoffs on compact subsets of open sets -/

@[expose] public section

open Filter Function Set
open scoped ContDiff Manifold Topology

namespace HypoellipticAleksandrov.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

section
variable {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
include hK hU hKU

/-- A compact subset of an open set has a smooth `[0,1]`-valued cutoff, equal to one
on a neighborhood of the compact set and compactly supported in the open set. -/
theorem exists_smooth_cutoff_on_nhds :
    ∃ b : E → ℝ, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧ tsupport b ⊆ U ∧
      (∀ x, b x ∈ Icc (0 : ℝ) 1) ∧ ∀ᶠ x in 𝓝ˢ K, b x = 1 := by
  obtain ⟨W, hW, hKW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨b, hbOne, hbZero, hbRange⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (I := 𝓘(ℝ, E)) (n := (⊤ : ℕ∞)) hK.isClosed (by rwa [hW.interior_eq])
  have hbs : tsupport b ⊆ closure W := closure_mono (fun x hx => by
    by_contra h
    exact (mem_support.mp hx) (hbZero x h))
  exact ⟨b, b.contMDiff.contDiff, hWc.of_isClosed_subset (isClosed_tsupport _) hbs,
    hbs.trans hWU, hbRange, hbOne⟩

/-- Pointwise version of the smooth cutoff lemma. -/
theorem exists_smooth_cutoff :
    ∃ b : E → ℝ, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧ tsupport b ⊆ U ∧
      (∀ x, b x ∈ Icc (0 : ℝ) 1) ∧ ∀ x ∈ K, b x = 1 := by
  obtain ⟨b, hb, hc, hsub, hr, h1⟩ := exists_smooth_cutoff_on_nhds hK hU hKU
  exact ⟨b, hb, hc, hsub, hr, fun x hx => mem_of_mem_nhds (x := x) (s := {y | b y = 1}) (eventually_nhdsSet_iff_forall.mp h1 x hx)⟩

end

end HypoellipticAleksandrov.Analysis
