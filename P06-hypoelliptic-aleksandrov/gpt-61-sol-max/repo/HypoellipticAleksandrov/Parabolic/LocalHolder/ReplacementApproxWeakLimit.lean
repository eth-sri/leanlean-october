module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxWeakCompactness
public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxWeakFamily
public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyL2Norm
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import PDEFoundation.Calculus.RegularityOrder


/-! # Weak derivative families for strong L2 limits

A common weak subsequence of the derivative entries retains all successor identities;
strong convergence of the root identifies its zero entry with the prescribed limit.
-/

 public section

namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set
open scoped Topology ENNReal BigOperators

/-- Uniformly bounded weak derivative families survive strong L2 convergence of their roots. -/
theorem exists_weakDerivativeFamily_testing_limit_of_tendsto_toLp {d L : ℕ}
    (U : HypoellipticAleksandrov.Parabolic.Region d) (u : ℕ → HypoellipticAleksandrov.Parabolic.ScalarField d)
    (D : ∀ n, ParabolicWeakDerivativeFamily d L U (u n))
    (hu : ∀ n, ParabolicMemLpOn U 2 (u n))
    (v : HypoellipticAleksandrov.Parabolic.ScalarField d) (hv : ParabolicMemLpOn U 2 v)
    (hstrong : Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 (hv.toLp v)))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n, (D n).squaredL2Norm ≤ C ^ 2) :
    ∃ (E : ParabolicWeakDerivativeFamily d L U v) (σ : ℕ → ℕ),
      StrictMono σ ∧ ∀ β (φ : HypoellipticAleksandrov.Parabolic.ScalarField d),
        ContDiff ℝ PDE.smoothOrder φ → HasCompactSupport φ → tsupport φ ⊆ U →
        Tendsto (fun n => ∫ z in U, (D (σ n)).representative β z * φ z) atTop
          (𝓝 (∫ z in U, E.representative β z * φ z)) := by
  let μ  := timeVelocityVolumeOn U

  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let : IsSeparable μ := inferInstance
  let H := Lp ℝ (2 ) μ
  let q  := fun n β =>
    ((D n).memLp β).toLp ((D n).representative β)
  have hqbound (n : ℕ) : ∑ β, ‖q n β‖ ^ 2 ≤ C ^ 2 := by
    rw [← (D n).squaredL2Norm_eq_sum_norm_toLp_sq]
    exact hb n
  obtain ⟨g, σ, hσ, hweak⟩ :=
    exists_strictMono_tendsto_clm_family_of_sum_norm_sq_le q C hC hqbound
  have hgzero : g (ParabolicDerivativeIndex.zero d L) = hv.toLp v := by
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2
    intro ell
    have hlim := (ell.continuous.tendsto (hv.toLp v)).comp
      (hstrong.comp hσ.tendsto_atTop)
    have hqzero (n : ℕ) : q n (ParabolicDerivativeIndex.zero d L) =
        (hu n).toLp (u n) :=
      MemLp.toLp_congr _ _ (D n).zero_ae
    have hlim'  := hlim.congr'
        (Eventually.of_forall (fun n => congrArg ell (hqzero (σ n)).symm))
    exact tendsto_nhds_unique (hweak _ ell) hlim'
  let raw : ParabolicDerivativeIndex d L → HypoellipticAleksandrov.Parabolic.ScalarField d := fun β => g β

  have hpair (β : ParabolicDerivativeIndex d L) (φ : HypoellipticAleksandrov.Parabolic.ScalarField d)
      (hφ : ContDiff ℝ PDE.smoothOrder φ) (hc : HasCompactSupport φ)
      (_hsub : tsupport φ ⊆ U) :
      Tendsto (fun n => ∫ z in U, (D (σ n)).representative β z * φ z) atTop
        (𝓝 (∫ z in U, raw β z * φ z)) := by
    let φLp : H := (hφ.continuous.memLp_of_hasCompactSupport hc).toLp φ
    let ell : H →L[ℝ] ℝ := InnerProductSpace.toDual ℝ H φLp
    have hφae : (φLp : HypoellipticAleksandrov.Parabolic.ScalarField d) =ᵐ[μ] φ :=
      (hφ.continuous.memLp_of_hasCompactSupport hc).coeFn_toLp
    have hleft (n : ℕ) : ell (q n β) =
        ∫ z in U, (D n).representative β z * φ z := by
      change inner ℝ φLp (q n β) = _
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [((D n).memLp β).coeFn_toLp, hφae] with z hq hφz
      rw [hq, hφz]
      rfl
    have hright : ell (g β) = ∫ z in U, raw β z * φ z := by
      change inner ℝ φLp (g β) = _
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hφae] with z hφz
      rw [hφz]
      rfl
    rw [← hright]
    exact (hweak β ell).congr' (Eventually.of_forall (fun n => hleft (σ n)))
  exact ⟨weakDerivativeFamily_of_tendsto_integral_mul U (fun n => u (σ n))
    (fun n => D (σ n)) v raw (fun β => Lp.memLp (g β)) (by
        change (g (ParabolicDerivativeIndex.zero d L) : HypoellipticAleksandrov.Parabolic.ScalarField d) =ᵐ[μ] v
        rw [hgzero]
        exact hv.coeFn_toLp) hpair,
    σ, hσ, hpair⟩

end HypoellipticAleksandrov.Parabolic.LocalHolder
