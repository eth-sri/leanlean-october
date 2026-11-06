module

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

variable {Ω : Set ℂ}

/-- **Weak sequential compactness of balls in a separable Hilbert space.** -/
theorem exists_weak_subseq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H] (x : ℕ → H) (R : ℝ)
    (hx : ∀ n, ‖x n‖ ≤ R) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ y : H, ∀ z : H,
      Tendsto (fun n => inner ℂ z (x (φ n))) atTop (𝓝 (inner ℂ z y)) := by
  set s : Set (WeakDual ℂ H) := WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 R
  have hmem : ∀ n, StrongDual.toWeakDual (InnerProductSpace.toDual ℂ H (x n)) ∈ s := by
    intro n
    simp [s, hx n]
  obtain ⟨a, -, φ, hφ, ht⟩ := WeakDual.isSeqCompact_closedBall ℂ H 0 R hmem
  refine ⟨φ, hφ, (InnerProductSpace.toDual ℂ H).symm (WeakDual.toStrongDual a), fun z => ?_⟩
  convert (Complex.continuous_conj.tendsto _).comp (((WeakDual.eval_continuous z).tendsto a).comp ht) using 1
  · ext n
    norm_num
  · rw [← inner_conj_symm]
    simp 

/-- `L²(Ω)` is separable. -/
instance separableSpace_L2 (Ω : Set ℂ) : TopologicalSpace.SeparableSpace (L2 Ω) := by
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  haveI : SecondCountableTopology (L2 Ω) := Lp.SecondCountableTopology
  infer_instance

/-- A weak gradient of the zero function vanishes (on an open set). -/
theorem IsWeakGradient.eq_zero_of_zero (hΩ : IsOpen Ω) {h : Fin 2 → L2 Ω}
    (hh : IsWeakGradient Ω 0 h) : h = 0 := by
  funext i
  apply Lp.ext
  filter_upwards [(ae_restrict_iff' hΩ.measurableSet).mpr (hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero ((locallyIntegrable_indicator_L2 hΩ.measurableSet (h i)).locallyIntegrableOn Ω)
    (fun ψ hψ hψc hψs => by
      have ht : TestFunction Ω (fun w => ψ w) :=
        ⟨Complex.ofRealCLM.contDiff.comp hψ, hψc.comp_left Complex.ofReal_zero,
          (tsupport_comp_subset Complex.ofReal_zero ψ).trans hψs⟩
      have e1 := hh _ ht i
      have hz : ∫ w in Ω, (0 : L2 Ω) w * fderiv ℝ (fun w => (ψ w : ℂ)) w
          (coordDir i) = 0 := by
        rw [integral_congr_ae (g := fun _ => 0)]
        · simp
        · filter_upwards [Lp.coeFn_zero ℂ 2 (volume.restrict Ω)] with w hw
          simp_all
      rw [hz, eq_comm, neg_eq_zero] at e1
      have e : ∀ w, ψ w • Ω.indicator (h i) w =
          Ω.indicator (fun w => h i w * ψ w) w := by
        intro w
        by_cases hw : w ∈ Ω
        all_goals simp [hw, mul_comm]
      simp [e, integral_indicator hΩ.measurableSet, e1])),
    Lp.coeFn_zero ℂ 2 (volume.restrict Ω), ae_restrict_mem hΩ.measurableSet] with w hw hz hwΩ
  simp_all

/-- **Uniqueness of weak gradients** on an open set. -/
theorem IsWeakGradient.unique (hΩ : IsOpen Ω) {u : L2 Ω} {g g' : Fin 2 → L2 Ω}
    (hg : IsWeakGradient Ω u g) (hg' : IsWeakGradient Ω u g') : g = g' := by
  have h := hg.add (hg'.smul (-1))
  rw [neg_one_smul, add_neg_cancel, neg_one_smul, ← sub_eq_add_neg] at h
  exact sub_eq_zero.mp (IsWeakGradient.eq_zero_of_zero hΩ h)

/-- The Neumann energy of `u` is `∑ ‖gᵢ‖²` for its weak gradient `g` (on an open set). -/
theorem neumannEnergy_eq_of_isWeakGradient (hΩ : IsOpen Ω) {u : L2 Ω}
    {g : Fin 2 → L2 Ω} (hg : IsWeakGradient Ω u g) :
    neumannEnergy Ω u = ∑ i, (‖g i‖₊ : ENNReal) ^ 2 := by
  apply le_antisymm
  · exact iInf₂_le g hg
  · exact le_iInf₂ fun g' hg' => by rw [hg.unique hΩ hg']

end PolyaNeumann

end
