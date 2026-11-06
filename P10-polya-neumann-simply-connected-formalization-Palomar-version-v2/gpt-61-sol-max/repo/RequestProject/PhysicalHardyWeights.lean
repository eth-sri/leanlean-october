module

public import RequestProject.KernelRows


public import RequestProject.PlanarTypes

public import RequestProject.CirclePeriod

public import RequestProject.PlanarGeometry

public import RequestProject.PhysicalHardySupport
public import RequestProject.CutFourier
public import RequestProject.ArcLength
public import RequestProject.HardyPrimitiveTrace

/-!
# Weighted Fourier coefficients of the supplied physical circle trace

Real C⁴ regularity near the closed disk implies the actual averaged Fourier
coefficients of `conj γ'` belong to weighted ℓ¹ of order one, and those of
`γ - γ 0` belong to weighted ℓ¹ of order two.  The estimates follow from
integration by parts and the periodic derivative summability theorem in
`CutFourier`; neither constant speed nor exterior holomorphicity is required.

The centered trace retains its actual average coefficient.  Absolute Fourier
reconstruction agrees with the physical function at every real parameter.
Holomorphicity in the open disk is used only for the support assertion imported
from `PhysicalHardySupport`, not as a substitute for the weighted estimates.
-/

public section

open scoped ContDiff



namespace PolyaNeumann

open MeasureTheory Set Metric
open scoped ComplexConjugate



/-- Periodic real C⁴ regularity gives the two weighted estimates needed for
the physical primitive multiplier and the centered boundary coordinate. -/
theorem periodic_contDiff_four_fourier_weights 
    (hf : ContDiff ℝ 4 f) (hp : Function.Periodic f circlePeriod) :
    IsWL1 1 (fourierCoeffOn Real.two_pi_pos (deriv f)) ∧
      IsWL1 2 (fourierCoeffOn Real.two_pi_pos f) := by
  have hf1  :=
    (show ContDiff ℝ (3 + 1) f from hf).deriv'
  have hf2  :=
    (show ContDiff ℝ (2 + 1) (deriv f) from hf1).deriv'
  have hf3  :=
    (show ContDiff ℝ (1 + 1) (deriv (deriv f)) from hf2).deriv'
  have d1  :=
    fun x => (hf.differentiable (by norm_num) x).hasDerivAt
  have d2  :=
    fun x => (hf1.differentiable (by norm_num) x).hasDerivAt
  have d3  :=
    fun x => (hf2.differentiable (by norm_num) x).hasDerivAt
  have d4  :=
    fun x => (hf3.differentiable_one x).hasDerivAt
  have hp1 := deriv_periodic hp
  have hp2 := deriv_periodic hp1
  have hp3 := deriv_periodic hp2
  have p0 : f 0 = f circlePeriod := by simpa only [zero_add] using (hp 0).symm
  have p1 : deriv f 0 = deriv f circlePeriod := by
    simpa only [zero_add] using (hp1 0).symm
  have p2 : deriv (deriv f) 0 = deriv (deriv f) circlePeriod := by
    simpa only [zero_add] using (hp2 0).symm
  have p3 : deriv (deriv (deriv f)) 0 = deriv (deriv (deriv f)) circlePeriod := by
    simpa only [zero_add] using (hp3 0).symm
  have hs1  :=
    summable_norm_fourierCoeffOn_deriv d1 d2 d3 hf3.continuous p0 p1 p2
  have hs2  :=
    summable_norm_fourierCoeffOn_deriv d2 d3 d4 hf3.continuous_deriv_one p1 p2 p3
  have e1 (n : ℤ)  :=
    fourierCoeffOn_deriv d1 hf1.continuous p0 n
  have e2 (n : ℤ)  :=
    fourierCoeffOn_deriv d2 hf2.continuous p1 n
  have hs0 : Summable (fun n => ‖fourierCoeffOn Real.two_pi_pos f n‖) := by
    refine (hs1.add ((hasSum_ite_eq 0
      ‖fourierCoeffOn Real.two_pi_pos f 0‖).summable)).of_nonneg_of_le
      (fun n => norm_nonneg _) (fun n => ?_)
    by_cases hn : n = 0
    · subst n
      simp
    · rw [if_neg hn, add_zero, e1]
      simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast]
      have hn' : (1 : ℝ) ≤ |(n : ℝ)| := by
        rw [← Int.cast_abs, ← Int.cast_one, Int.cast_le]
        exact Int.one_le_abs hn
      nlinarith [norm_nonneg (fourierCoeffOn Real.two_pi_pos f n)]
  constructor
  · change Summable (fun n => sobWeight n ^ 1 *
      ‖fourierCoeffOn Real.two_pi_pos (deriv f) n‖)
    refine (hs1.add hs2).congr fun n => ?_
    simp_all [sobWeight, PolyaNeumann.sobWeight] <;> ring
  · change Summable (fun n => sobWeight n ^ 2 *
      ‖fourierCoeffOn Real.two_pi_pos f n‖)
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (Real.rpow_nonneg (sobWeight_pos n).le _)
        (norm_nonneg _)) (fun n => ?_) ((hs0.mul_left 2).add (hs2.mul_left 2))
    rw [e2, e1]
    simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast,
      Real.rpow_two, sobWeight]
    have hnonneg : 0 ≤ (|(n : ℝ)| - 1) ^ 2 *
        ‖fourierCoeffOn Real.two_pi_pos f n‖ :=
      mul_nonneg (sq_nonneg _) (norm_nonneg _)
    nlinarith

/-- Conjugation reflects the Fourier indices and preserves the weighted ℓ¹ norm. -/
theorem isWL1_fourierCoeffOn_conj  
    (hg : IsWL1 s (fourierCoeffOn Real.two_pi_pos g)) :
    IsWL1 s (fourierCoeffOn Real.two_pi_pos (fun θ => conj (g θ))) := by
  have hs := hg.comp_injective
    neg_injective
  refine hs.congr fun n => ?_
  simp_all [fourierCoeffOn_conj, sobWeight]

section
variable {R : ℝ} (hR : 1 < R) (F : PlaneMap) (hFs : ContDiffOn ℝ 4 F (ball (0 : ℂ) R))

section
include R hR F hFs

/-- The supplied real C⁴ map is C⁴ along the actual circle. -/
theorem contDiff_physicalCircleTrace_four_of_neighborhood :
    ContDiff ℝ 4 (physicalCircleTrace F) := by
  apply contDiff_iff_contDiffAt.mpr
  intro θ
  have hz  :=
    closedBall_subset_ball hR (circleMap_mem_closedBall 0 (by norm_num) θ)
  exact (hFs.contDiffAt (isOpen_ball.mem_nhds hz)).comp θ
    (contDiff_circleMap 0 1).contDiffAt

/-- Actual physical coefficients satisfy both weighted hypotheses.  Real
smoothness near the closure suffices; no boundary parametrization is assumed. -/
theorem physicalCircleTrace_fourier_weights_of_neighborhood :
    IsWL1 1 (fourierCoeffOn Real.two_pi_pos
      (fun θ => conj (deriv (physicalCircleTrace F) θ))) ∧
      IsWL1 2 (fourierCoeffOn Real.two_pi_pos
        (fun θ => physicalCircleTrace F θ - physicalCircleTrace F 0)) := by
  have hγ := contDiff_physicalCircleTrace_four_of_neighborhood hR F hFs
  have hp := physicalCircleTrace_periodic F
  refine ⟨isWL1_fourierCoeffOn_conj
    (periodic_contDiff_four_fourier_weights hγ hp).1, ?_⟩
  exact (periodic_contDiff_four_fourier_weights
    (hγ.sub contDiff_const) (hp.comp (fun z => z - physicalCircleTrace F 0))).2

end


/-- Smooth supplied coordinates give the same finite weighted hypotheses. -/
theorem physicalCircleTrace_fourier_weights_of_smooth_neighborhood
     (hR : 1 < R) F
    (hFs : RealSmoothOnBall F R) :
    IsWL1 1 (fourierCoeffOn Real.two_pi_pos
      (fun θ => conj (deriv (physicalCircleTrace F) θ))) ∧
      IsWL1 2 (fourierCoeffOn Real.two_pi_pos
        (fun θ => physicalCircleTrace F θ - physicalCircleTrace F 0)) :=
  physicalCircleTrace_fourier_weights_of_neighborhood hR F
    (hFs.of_le (WithTop.coe_le_coe.mpr le_top))

/-- Absolutely convergent averaged Fourier reconstruction of a continuous
periodic physical function, at every real parameter. -/
theorem hardyFourierTrace_fourierCoeffOn_of_periodic 
    (hf : Continuous f) (hp : Function.Periodic f circlePeriod)
    (hs : Summable (fun n => ‖fourierCoeffOn Real.two_pi_pos f n‖)) θ :
    hardyFourierTrace (fourierCoeffOn Real.two_pi_pos f) θ = f θ := by
  let u := AddCircle.equivIco circlePeriod 0 θ
  have hu : ((u : ℝ) : AddCircle circlePeriod) = (θ : AddCircle circlePeriod) :=
    (AddCircle.equivIco circlePeriod 0).left_inv _
  have hut : (u : ℝ) ∈ Ico 0 circlePeriod := by
    simpa   using u.property
  have huv : f (u : ℝ) = f θ := by
    calc
      f u = hp.lift ((u : ℝ)) := (hp.lift_coe _).symm
      _ = hp.lift θ := congrArg hp.lift hu
      _ = f θ := hp.lift_coe θ
  have p0 : f 0 = f circlePeriod := by simpa   using (hp 0).symm
  have hsum := hasSum_fourierCoeffOn hf p0 hs.of_norm hut
  have hsum' : HasSum (fun n : ℤ => fourierCoeffOn Real.two_pi_pos f n *
      fourier (T := 2 * Real.pi) n (θ : AddCircle circlePeriod)) (f θ) := by
    simpa  [← fourier_coe_two_pi, hu, huv] using hsum
  exact hsum'.tsum_eq

include R hR F hFs in
/-- Reconstruction of the actual conjugated velocity from its weighted data. -/
theorem hardyFourierTrace_physical_conj_deriv_of_neighborhood θ :
    hardyFourierTrace (fourierCoeffOn Real.two_pi_pos
      (fun s => conj (deriv (physicalCircleTrace F) s))) θ =
      conj (deriv (physicalCircleTrace F) θ) := by
  have hγ := contDiff_physicalCircleTrace_four_of_neighborhood hR F hFs
  have hc  :=
    Complex.continuous_conj.comp (hγ.continuous_deriv (by norm_num))
  have hp  := (deriv_periodic (physicalCircleTrace_periodic F)).comp conj
  have hw := (physicalCircleTrace_fourier_weights_of_neighborhood hR F hFs).1
  have hs : Summable (fun n => ‖fourierCoeffOn Real.two_pi_pos
      (fun s => conj (deriv (physicalCircleTrace F) s)) n‖) := by
    have hw' : Summable (fun n => sobWeight n * ‖fourierCoeffOn Real.two_pi_pos
        (fun s => conj (deriv (physicalCircleTrace F) s)) n‖) := by
      simpa  [IsWL1] using hw
    exact hw'.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n =>
      le_mul_of_one_le_left (norm_nonneg _) (one_le_sobWeight n))
  exact hardyFourierTrace_fourierCoeffOn_of_periodic hc hp hs θ

end


end PolyaNeumann
