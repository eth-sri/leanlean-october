module

public import NearlyMinimax.GammaTailBounds
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

@[expose] public section

/-! Genuine Euclidean exponential spatial-kernel integrals. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- The exact Euclidean distance in the source's actual coordinate space. -/
def exactEuclideanDistance {d : ℕ} (x y : Covariate d) : ℝ :=
  Real.sqrt (spatialSquaredDistance x y)

section
variable {d : ℕ}

section
variable (x y : Covariate d)

theorem exactEuclideanDistance_nonneg :
    0 ≤ exactEuclideanDistance x y := Real.sqrt_nonneg _

theorem exactEuclideanDistance_eq_norm :
    exactEuclideanDistance x y = ‖WithLp.toLp 2 (y-x)‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold exactEuclideanDistance spatialSquaredDistance
  simp [Real.norm_eq_abs, sq_abs]

end

theorem exactEuclideanDistance_continuous :
    Continuous (fun xy : CovariatePair d => exactEuclideanDistance xy.1 xy.2) := by
  unfold exactEuclideanDistance spatialSquaredDistance
  fun_prop

end

/-- Surface normalization times the Gamma moment of the residual radial power. -/
def radialExponentialConstant (d k : ℕ) : ℝ :=
  (d : ℝ) * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) * ((d-k-1).factorial : ℝ)

def spatialExponentialConstant (d : ℕ) : ℝ := radialExponentialConstant d 0

/-- The radial formula covers both the exponential and the inverse-four
Laplace envelope. The integrability condition is exactly `k < d`. -/
theorem euclidean_radial_exponential {d k : ℕ} (hk : k < d) {N : ℝ} (hN : 0 < N) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => Real.exp (-(N*‖x‖))/‖x‖^k) volume ∧
    (∫ x : EuclideanSpace ℝ (Fin d), Real.exp (-(N*‖x‖))/‖x‖^k) =
      radialExponentialConstant d k / N^(d-k) := by
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
  have he (r : ℝ) (hr : r ∈ Ioi 0) :
      r^(d-1) * (Real.exp (-(N*r))/r^k) = r^(d-k-1) * Real.exp (-(N*r)) := by
    have hn : d-1 = d-k-1+k := by omega
    rw [hn, pow_add]
    field_simp [ne_of_gt hr]
  refine ⟨(integrable_fun_norm_addHaar volume (f := fun r => Real.exp (-(N*r))/r^k)).2 ?_, ?_⟩
  · simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
    exact ((gamma_monomial_integrable hN (d-k-1)).mono_set Ioi_subset_Ici_self).congr_fun
      (fun r hr => (he r hr).symm) measurableSet_Ioi
  · rw [integral_fun_norm_addHaar volume (fun r => Real.exp (-(N*r))/r^k)]
    simp only [finrank_euclideanSpace, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul]
    rw [setIntegral_congr_fun measurableSet_Ioi he, ← integral_Ici_eq_integral_Ioi,
      gamma_monomial_integral hN, show d-k-1+1=d-k by omega, radialExponentialConstant]
    ring

/-- Passage between the actual coordinates and translated Euclidean coordinates. -/
theorem radial_spatial_transport {d : ℕ} (x : Covariate d) (f : ℝ → ℝ)
    (hi : Integrable (fun y : EuclideanSpace ℝ (Fin d) => f ‖y‖) volume) :
    Integrable (fun y => f (exactEuclideanDistance x y)) volume ∧
    (∫ y, f (exactEuclideanDistance x y)) = ∫ y : EuclideanSpace ℝ (Fin d), f ‖y‖ := by
  let e := (MeasurableEquiv.addRight (-x)).trans (MeasurableEquiv.toLp 2 (Covariate d))
  have hp : MeasurePreserving e volume volume :=
    (PiLp.volume_preserving_toLp (Fin d)).comp (measurePreserving_add_right volume (-x))
  have he : (fun y => f ‖y‖) ∘ e = fun y => f (exactEuclideanDistance x y) := by
    funext y
    rw [exactEuclideanDistance_eq_norm, sub_eq_add_neg]
    rfl
  rw [← he]
  exact ⟨hp.integrable_comp_of_integrable hi,
    hp.integral_comp e.measurableEmbedding (fun y => f ‖y‖)⟩

section
variable {d : ℕ} (hd : 0 < d) {T : ℝ} (hT : 0 < T)
include hd hT

theorem exactEuclideanDistance_exponential_moment (x : Covariate d) :
    Integrable (fun y => Real.exp (-(T * exactEuclideanDistance x y))) volume ∧
    (∫ y, Real.exp (-(T * exactEuclideanDistance x y))) = spatialExponentialConstant d / T^d := by
  have h := euclidean_radial_exponential (k := 0) hd hT
  simp only [pow_zero, div_one, Nat.sub_zero] at h
  have g := radial_spatial_transport x (fun r => Real.exp (-(T*r))) h.1
  exact ⟨g.1, g.2.trans h.2⟩

end

/-- A true exponential-series estimate absorbs the quadratic pair defect. -/
theorem pair_defect_exponential_absorption (t : ℝ) (ht : 0 ≤ t) :
    (1+t)^2 * Real.exp (-(2*t)) ≤ 6 * Real.exp (-t) := by
  have hp := Real.pow_div_factorial_le_exp t ht 2
  norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.cast_one, mul_one] at hp
  have h1 := Real.one_le_exp_iff.mpr ht
  have hpoly : (1+t)^2 ≤ 6 * Real.exp t := by nlinarith [sq_nonneg (t-1)]
  have hh := mul_le_mul_of_nonneg_right hpoly (Real.exp_nonneg (-(2*t)))
  simp_all [mul_assoc, ← Real.exp_add, show t + -(2*t) = -t by ring]

section
variable (d : ℕ)

theorem spatialExponentialConstant_nonneg : 0 ≤ spatialExponentialConstant d := by
  unfold spatialExponentialConstant radialExponentialConstant
  positivity

theorem spatialPatchBox_volume : volume (spatialPatchBox d) = (2 : ℝ≥0∞)^d := by
  simp only [spatialPatchBox, Real.volume_Icc_pi, sub_neg_eq_add, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  norm_num

theorem spatialPatchBox_real_volume : volume.real (spatialPatchBox d) = (2 : ℝ)^d := by
  simp [measureReal_def, spatialPatchBox_volume, ENNReal.toReal_pow]

end

/-- A nonnegative whole-space kernel with a uniform true section bound has
an actual finite-domain product integral bound. -/
theorem finite_pair_kernel_integrable_and_integral_le {X : Type*}
    [MeasurableSpace X] (ν : Measure X) [SigmaFinite ν] (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : μ ≤ ν) (f : X × X → ℝ) (hm : Measurable f) (hn : ∀ z, 0 ≤ f z) (K : ℝ)
    (hi : ∀ x, Integrable (fun y => f (x,y)) ν)
    (hb : ∀ x, (∫ y, f (x,y) ∂ν) ≤ K) :
    Integrable f (μ.prod μ) ∧ (∫ z, f z ∂μ.prod μ) ≤ μ.real univ * K := by
  have hsection (x : X) := (hi x).mono_measure hμ
  have hsectionBound (x : X) :=
    (integral_mono_measure hμ (Filter.Eventually.of_forall fun y => hn (x,y)) (hi x)).trans (hb x)
  have hinner : Integrable (fun x => ∫ y, ‖f (x,y)‖ ∂μ) μ := by
    have hmin : AEStronglyMeasurable (fun x => ∫ y, ‖f (x,y)‖ ∂μ) μ :=
      hm.norm.stronglyMeasurable.integral_prod_right.aestronglyMeasurable
    apply (integrable_const K).mono' hmin
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (hn _)]
    exact hsectionBound x
  have hf :=
    (integrable_prod_iff hm.aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall hsection, hinner⟩
  refine ⟨hf, ?_⟩
  rw [integral_prod _ hf]
  simpa only [integral_const, smul_eq_mul] using
    integral_mono hf.integral_prod_left (integrable_const K) hsectionBound

section
variable {d : ℕ} (hd : 0 < d) {T : ℝ} (hT : 0 < T)
include hd hT

/-- Product integration with any finite design dominated by Lebesgue measure. -/
theorem spatial_pair_exponential_moments (μ : Measure (Covariate d)) [IsFiniteMeasure μ]
    (hμ : μ ≤ volume) :
    Integrable (fun xy : CovariatePair d => Real.exp (-(T*exactEuclideanDistance xy.1 xy.2))) (μ.prod μ) ∧
    (∫ xy : CovariatePair d, Real.exp (-(T*exactEuclideanDistance xy.1 xy.2)) ∂μ.prod μ) ≤
      μ.real univ * (spatialExponentialConstant d / T^d) :=
  finite_pair_kernel_integrable_and_integral_le volume μ hμ _
    (exactEuclideanDistance_continuous.const_mul T |>.neg |>.rexp).measurable
    (fun _ => Real.exp_nonneg _) _
    (fun x => (exactEuclideanDistance_exponential_moment hd hT x).1)
    (fun x => (exactEuclideanDistance_exponential_moment hd hT x).2.le)

end
end NearlyMinimax
