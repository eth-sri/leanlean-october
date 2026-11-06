module

public import RequestProject.PlanarTypes

public import RequestProject.WeakConstancy
public import RequestProject.Finite

/-!
# Weak compactness in `L²` and uniqueness of weak gradients

* `exists_weak_subseq`: a bounded sequence in a separable Hilbert space has a weakly convergent
  subsequence (sequential Banach–Alaoglu together with the Riesz representation).
* `separableSpace_L2`: `L²(Ω)` is separable.
* `IsWeakGradient.unique`: on an open set, the weak gradient of an `L²` function is unique.
* `neumannEnergy_eq_of_isWeakGradient`: the Neumann energy is `∑ ‖gᵢ‖²` for the weak gradient.
-/

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace PolyaNeumann

/-- **Weak sequential compactness of balls in a separable Hilbert space.** -/
theorem exists_weak_subseq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H] (x : ℕ → H) R
    (hx : ∀ n, ‖x n‖ ≤ R) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ y : H, ∀ z : H,
      Tendsto (fun n => inner ℂ z (x (φ n))) atTop (𝓝 (inner ℂ z y)) := by
  set s : Set (WeakDual ℂ H) := WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 R
  have hs := WeakDual.isSeqCompact_closedBall ℂ H 0 R
  have hmem : ∀ n, StrongDual.toWeakDual (InnerProductSpace.toDual ℂ H (x n)) ∈ s := by
    intro n
    simp [s, hx n]
  obtain ⟨a, -, φ, hφ, ht⟩ := hs hmem
  refine ⟨φ, hφ, (InnerProductSpace.toDual ℂ H).symm (WeakDual.toStrongDual a), fun z => ?_⟩
  have h1 := ((WeakDual.eval_continuous z).tendsto a).comp ht
  have h2 := (Complex.continuous_conj.tendsto _).comp h1
  convert h2 using 1
  · ext n
    simp_all
  · rw [← inner_conj_symm]
    simp 

/-- `L²(Ω)` is separable. -/
instance separableSpace_L2 (Ω : PlanarSet) : TopologicalSpace.SeparableSpace (L2 Ω) := by
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  infer_instance

section
variable {Ω : PlanarSet} (hΩ : IsOpen Ω)
include Ω hΩ

/-- A weak gradient of the zero function vanishes (on an open set). -/
theorem IsWeakGradient.eq_zero_of_zero 
    (hh : IsWeakGradient Ω 0 h) : h = 0 := by
  funext i
  have hloc := locallyIntegrable_indicator_L2 hΩ.measurableSet (h i)
  have h0 := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hloc.locallyIntegrableOn Ω)
    (fun ψ hψ hψc hψs => by
      have ht : TestFunction Ω (fun w => ((ψ w : ℝ) : ℂ)) :=
        ⟨Complex.ofRealCLM.contDiff.comp hψ, hψc.comp_left Complex.ofReal_zero,
          (tsupport_comp_subset Complex.ofReal_zero ψ).trans hψs⟩
      have e1 := hh _ ht i
      rw [← lpPair_apply (ht.memLp_fderiv (coordDir i)), map_zero,
        eq_comm, neg_eq_zero] at e1
      have e : ∀ w, ψ w • Ω.indicator (fun z => (h i : PlaneMap) z) w =
          Ω.indicator (fun w => (h i : PlaneMap) w * ((ψ w : ℝ) : ℂ)) w := by
        intro w
        by_cases hw : w ∈ Ω
        · simp [hw, Complex.real_smul, mul_comm]
        · simp [hw]
      simp_rw [e]
      rw [integral_indicator hΩ.measurableSet, e1])
  apply Lp.ext
  filter_upwards [(ae_restrict_iff' hΩ.measurableSet).mpr h0,
    Lp.coeFn_zero ℂ 2 (volume.restrict Ω), ae_restrict_mem hΩ.measurableSet] with w hw hz hwΩ
  simp_all

/-- **Uniqueness of weak gradients** on an open set. -/
theorem IsWeakGradient.unique  
    (hg : IsWeakGradient Ω u g) (hg' : IsWeakGradient Ω u g') : g = g' := by
  have h := hg.add (hg'.smul (-1))
  rw [neg_one_smul, add_neg_cancel, neg_one_smul, ← sub_eq_add_neg] at h
  exact sub_eq_zero.mp (IsWeakGradient.eq_zero_of_zero hΩ h)

/-- The Neumann energy of `u` is `∑ ‖gᵢ‖²` for its weak gradient `g` (on an open set). -/
theorem neumannEnergy_eq_of_isWeakGradient 
     (hg : IsWeakGradient Ω u g) :
    neumannEnergy Ω u = ∑ i, (‖g i‖₊ : ENNReal) ^ 2 := by
  apply le_antisymm
  · exact iInf₂_le g hg
  · exact le_iInf₂ fun g' hg' => by rw [hg.unique hΩ hg']

end


end PolyaNeumann

end
