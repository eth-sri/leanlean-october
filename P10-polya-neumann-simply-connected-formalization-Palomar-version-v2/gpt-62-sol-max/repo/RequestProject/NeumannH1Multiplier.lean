module

public import RequestProject.NeumannSobolev
public import RequestProject.LpBoundedMultiplier
public import RequestProject.ReconBasic

/-! # The weak product rule for smooth coefficients bounded on the domain -/

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter
open scoped Topology

/-- A smooth coefficient whose value and first derivatives have a common bound on `Ω`. -/
structure H1Coefficient (Ω : Set ℂ) where
  toFun : ℂ → ℂ
  smooth : ContDiff ℝ (⊤ : ℕ∞) toFun
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  value_bound : ∀ z ∈ Ω, ‖toFun z‖ ≤ bound
  derivative_bound : ∀ (i : Fin 2), ∀ z ∈ Ω, ‖fderiv ℝ toFun z (coordDir i)‖ ≤ bound

instance {Ω : Set ℂ} : CoeFun (H1Coefficient Ω) (fun _ => ℂ → ℂ) := ⟨H1Coefficient.toFun⟩

/-- Reuse a coefficient on a smaller set without changing its bound. -/
def H1Coefficient.restrict {Ω D : Set ℂ} (a : H1Coefficient Ω) (h : D ⊆ Ω) :
    H1Coefficient D :=
  ⟨a, a.smooth, a.bound, a.bound_nonneg, fun z hz => a.value_bound z (h hz),
    fun i z hz => a.derivative_bound i z (h hz)⟩

theorem ae_le_bound {Ω : Set ℂ} {f : ℂ → ℂ} {B : ℝ} (hf : Continuous f)
    (h : ∀ z ∈ Ω, ‖f z‖ ≤ B) : ∀ᵐ z ∂volume.restrict Ω, ‖f z‖ ≤ B :=
  (ae_restrict_iff (isClosed_le hf.norm continuous_const).measurableSet).2 (.of_forall h)

theorem coefficient_derivative_continuous {Ω : Set ℂ} (a : H1Coefficient Ω) (i : Fin 2) :
    Continuous (fun z => fderiv ℝ (a : ℂ → ℂ) z (coordDir i)) :=
  ((a.smooth.fderiv_right (m := (⊤ : ℕ∞)) le_rfl).clm_apply contDiff_const).continuous

def h1CoefficientL2 (Ω : Set ℂ) (a : H1Coefficient Ω) : L2 Ω →L[ℂ] L2 Ω :=
  lpBoundedMultiplier (a : ℂ → ℂ) a.smooth.continuous.aestronglyMeasurable
    (ae_le_bound a.smooth.continuous a.value_bound)

def h1CoefficientDerivativeL2 (Ω : Set ℂ) (a : H1Coefficient Ω) (i : Fin 2) :
    L2 Ω →L[ℂ] L2 Ω :=
  lpBoundedMultiplier (fun z => fderiv ℝ (a : ℂ → ℂ) z (coordDir i))
    (coefficient_derivative_continuous a i).aestronglyMeasurable
    (ae_le_bound (coefficient_derivative_continuous a i) (a.derivative_bound i))

theorem h1CoefficientL2_ae (Ω : Set ℂ) (a : H1Coefficient Ω) (u : L2 Ω) :
    (h1CoefficientL2 Ω a u : ℂ → ℂ) =ᵐ[volume.restrict Ω] fun z => a z * u z :=
  lpBoundedMultiplier_ae (a : ℂ → ℂ) a.smooth.continuous.aestronglyMeasurable
    (ae_le_bound a.smooth.continuous a.value_bound) u

theorem h1CoefficientDerivativeL2_ae (Ω : Set ℂ) (a : H1Coefficient Ω)
    (i : Fin 2) (u : L2 Ω) :
    (h1CoefficientDerivativeL2 Ω a i u : ℂ → ℂ) =ᵐ[volume.restrict Ω]
      fun z => fderiv ℝ (a : ℂ → ℂ) z (coordDir i) * u z :=
  lpBoundedMultiplier_ae (fun z => fderiv ℝ (a : ℂ → ℂ) z (coordDir i))
    (coefficient_derivative_continuous a i).aestronglyMeasurable
    (ae_le_bound (coefficient_derivative_continuous a i) (a.derivative_bound i)) u

theorem norm_h1CoefficientL2_apply_le (Ω : Set ℂ) (a : H1Coefficient Ω)
    (u : L2 Ω) : ‖h1CoefficientL2 Ω a u‖ ≤ a.bound * ‖u‖ :=
  norm_lpBoundedMulLin_le (a : ℂ → ℂ) a.smooth.continuous.aestronglyMeasurable
    (ae_le_bound a.smooth.continuous a.value_bound) u

theorem norm_h1CoefficientDerivativeL2_apply_le (Ω : Set ℂ)
    (a : H1Coefficient Ω) (i : Fin 2) (u : L2 Ω) :
    ‖h1CoefficientDerivativeL2 Ω a i u‖ ≤ a.bound * ‖u‖ :=
  norm_lpBoundedMulLin_le (fun z => fderiv ℝ (a : ℂ → ℂ) z (coordDir i))
    (coefficient_derivative_continuous a i).aestronglyMeasurable
    (ae_le_bound (coefficient_derivative_continuous a i) (a.derivative_bound i)) u

theorem coefficient_test_mul {Ω D : Set ℂ} (a : H1Coefficient Ω)
    {φ : ℂ → ℂ} (hφ : TestFunction D φ) : TestFunction D (fun z => a z * φ z) :=
  ⟨a.smooth.mul hφ.1, hφ.2.1.mul_left, tsupport_mul_subset_right.trans hφ.2.2⟩

private theorem coefficient_test_mul_fderiv {Ω : Set ℂ} (a : H1Coefficient Ω) {φ : ℂ → ℂ} (hφ : TestFunction Ω φ) (z : ℂ) (i : Fin 2) :
    fderiv ℝ (fun w => a w * φ w) z (coordDir i) =
      fderiv ℝ (a : ℂ → ℂ) z (coordDir i) * φ z +
        a z * fderiv ℝ φ z (coordDir i) := by
  rw [fderiv_fun_mul (a.smooth.differentiable (by simp) z)
    (hφ.1.differentiable (by simp) z)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  ring

/-- The genuine weak product rule, with both derivative terms in actual L². -/
theorem isWeakGradient_h1CoefficientL2 {Ω : Set ℂ} (a : H1Coefficient Ω)
    {u : L2 Ω} {g : Fin 2 → L2 Ω} (hu : IsWeakGradient Ω u g) :
    IsWeakGradient Ω (h1CoefficientL2 Ω a u)
      (fun i => h1CoefficientL2 Ω a (g i) +
        h1CoefficientDerivativeL2 Ω a i u) := by
  intro φ hφ i
  have hweak := hu (fun z => a z * φ z) (coefficient_test_mul a hφ) i
  have hid :=
    (Lp.memLp (h1CoefficientDerivativeL2 Ω a i u)).integrable_mul hφ.memLp
  have hif :=
    (Lp.memLp (h1CoefficientL2 Ω a u)).integrable_mul (hφ.memLp_fderiv (coordDir i))
  have hig :=
    (Lp.memLp (h1CoefficientL2 Ω a (g i))).integrable_mul hφ.memLp
  have hleft : (∫ z in Ω, u z * fderiv ℝ (fun w => a w * φ w) z (coordDir i)) =
      (∫ z in Ω, h1CoefficientDerivativeL2 Ω a i u z * φ z) +
        ∫ z in Ω, h1CoefficientL2 Ω a u z * fderiv ℝ φ z (coordDir i) := by
    calc
      _ = ∫ z in Ω, h1CoefficientDerivativeL2 Ω a i u z * φ z +
          h1CoefficientL2 Ω a u z * fderiv ℝ φ z (coordDir i) := by
        apply integral_congr_ae
        filter_upwards [h1CoefficientL2_ae Ω a u,
          h1CoefficientDerivativeL2_ae Ω a i u] with z hz hdz
        rw [coefficient_test_mul_fderiv a hφ z i, hz, hdz]
        ring
      _ = _ := integral_add hid hif
  have hright : (∫ z in Ω, (g i) z * (a z * φ z)) =
      ∫ z in Ω, h1CoefficientL2 Ω a (g i) z * φ z := by
    apply integral_congr_ae
    filter_upwards [h1CoefficientL2_ae Ω a (g i)] with z hz
    rw [hz]
    ring
  have hout : (∫ z in Ω,
      ((h1CoefficientL2 Ω a (g i) + h1CoefficientDerivativeL2 Ω a i u : L2 Ω) :
        ℂ → ℂ) z * φ z) =
      (∫ z in Ω, h1CoefficientL2 Ω a (g i) z * φ z) +
        ∫ z in Ω, h1CoefficientDerivativeL2 Ω a i u z * φ z := by
    calc
      _ = ∫ z in Ω, h1CoefficientL2 Ω a (g i) z * φ z +
          h1CoefficientDerivativeL2 Ω a i u z * φ z := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add (h1CoefficientL2 Ω a (g i))
          (h1CoefficientDerivativeL2 Ω a i u)] with z hz
        rw [hz]
        simp  [Pi.add_apply, add_mul]
      _ = _ := integral_add hig hid
  rw [hleft, hright] at hweak
  rw [hout]
  linear_combination hweak

theorem neumannH1_ext {Ω : Set ℂ} {u v : NeumannH1 Ω}
    (hv : h1Value Ω u = h1Value Ω v)
    (hg : ∀ i : Fin 2, h1Gradient Ω i u = h1Gradient Ω i v) : u = v := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hv
  tauto

def coefficientH1Vector (Ω : Set ℂ) (a : H1Coefficient Ω)
    (u : NeumannH1 Ω) : NeumannH1 Ω :=
  h1Vector (isWeakGradient_h1CoefficientL2 a (h1Value_weakGradient Ω u))

theorem coefficientH1Vector_value (Ω : Set ℂ) (a : H1Coefficient Ω)
    (u : NeumannH1 Ω) :
    h1Value Ω (coefficientH1Vector Ω a u) = h1CoefficientL2 Ω a (h1Value Ω u) :=
  h1Value_h1Vector (isWeakGradient_h1CoefficientL2 a (h1Value_weakGradient Ω u))

theorem coefficientH1Vector_gradient (Ω : Set ℂ) (a : H1Coefficient Ω)
    (u : NeumannH1 Ω) (i : Fin 2) :
    h1Gradient Ω i (coefficientH1Vector Ω a u) =
      h1CoefficientL2 Ω a (h1Gradient Ω i u) +
        h1CoefficientDerivativeL2 Ω a i (h1Value Ω u) :=
  h1Gradient_h1Vector (isWeakGradient_h1CoefficientL2 a (h1Value_weakGradient Ω u)) i

def coefficientH1Lin (Ω : Set ℂ) (a : H1Coefficient Ω) :
    NeumannH1 Ω →ₗ[ℂ] NeumannH1 Ω where
  toFun := coefficientH1Vector Ω a
  map_add' u v := by
    apply neumannH1_ext
    · simp  [coefficientH1Vector_value, map_add]
    · intro i
      simp  [coefficientH1Vector_gradient, map_add]
      abel
  map_smul' c u := by
    apply neumannH1_ext
    · simp  [coefficientH1Vector_value, map_smul, RingHom.id_apply]
    · intro i
      simp  [coefficientH1Vector_gradient, map_smul, smul_add, RingHom.id_apply]

private theorem coefficientH1Lin_value (Ω : Set ℂ) (a : H1Coefficient Ω)
    (u : NeumannH1 Ω) :
    h1Value Ω (coefficientH1Lin Ω a u) = h1CoefficientL2 Ω a (h1Value Ω u) :=
  coefficientH1Vector_value Ω a u

private theorem coefficientH1Lin_gradient (Ω : Set ℂ) (a : H1Coefficient Ω)
    (u : NeumannH1 Ω) (i : Fin 2) :
    h1Gradient Ω i (coefficientH1Lin Ω a u) =
      h1CoefficientL2 Ω a (h1Gradient Ω i u) +
        h1CoefficientDerivativeL2 Ω a i (h1Value Ω u) :=
  coefficientH1Vector_gradient Ω a u i

private theorem h1_component_norm_le {Ω : Set ℂ} (u : NeumannH1 Ω) :
    ‖h1Value Ω u‖ ≤ ‖u‖ ∧ ∀ i, ‖h1Gradient Ω i u‖ ≤ ‖u‖ := by
  have hs := h1_norm_sq Ω u
  constructor
  · exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by
      linarith [Finset.sum_nonneg (s := Finset.univ) fun i _ => sq_nonneg ‖h1Gradient Ω i u‖])
  · intro i
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    linarith [Finset.single_le_sum (fun j _ => sq_nonneg ‖h1Gradient Ω j u‖)
      (Finset.mem_univ i), sq_nonneg ‖h1Value Ω u‖]

private theorem h1_norm_le_of_components {Ω : Set ℂ} (u : NeumannH1 Ω) {A : ℝ}
    (hA : 0 ≤ A) (hv : ‖h1Value Ω u‖ ≤ A) (hg : ∀ i, ‖h1Gradient Ω i u‖ ≤ A) :
    ‖u‖ ≤ Real.sqrt 3 * A := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [h1_norm_sq, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Fin.sum_univ_two]
  linarith [pow_le_pow_left₀ (norm_nonneg _) hv 2,
    pow_le_pow_left₀ (norm_nonneg _) (hg 0) 2, pow_le_pow_left₀ (norm_nonneg _) (hg 1) 2]

theorem coefficientH1Lin_norm_le (Ω : Set ℂ) (a : H1Coefficient Ω)
    (u : NeumannH1 Ω) :
    ‖coefficientH1Lin Ω a u‖ ≤ (2 * Real.sqrt 3 * a.bound) * ‖u‖ := by
  have hc := h1_component_norm_le u
  have hv : ‖h1Value Ω (coefficientH1Lin Ω a u)‖ ≤ 2 * a.bound * ‖u‖ := by
    rw [coefficientH1Lin_value]
    exact (norm_h1CoefficientL2_apply_le Ω a _).trans
      ((mul_le_mul_of_nonneg_left hc.1 a.bound_nonneg).trans
        (by nlinarith [norm_nonneg u, a.bound_nonneg]))
  have hg (i : Fin 2) :
      ‖h1Gradient Ω i (coefficientH1Lin Ω a u)‖ ≤ 2 * a.bound * ‖u‖ := by
    rw [coefficientH1Lin_gradient]
    calc
      _ ≤ ‖h1CoefficientL2 Ω a (h1Gradient Ω i u)‖ +
          ‖h1CoefficientDerivativeL2 Ω a i (h1Value Ω u)‖ := norm_add_le _ _
      _ ≤ a.bound * ‖h1Gradient Ω i u‖ + a.bound * ‖h1Value Ω u‖ :=
        add_le_add (norm_h1CoefficientL2_apply_le Ω a _)
          (norm_h1CoefficientDerivativeL2_apply_le Ω a i _)
      _ ≤ a.bound * ‖u‖ + a.bound * ‖u‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (hc.2 i) a.bound_nonneg)
          (mul_le_mul_of_nonneg_left hc.1 a.bound_nonneg)
      _ = _ := by ring
  have hn := h1_norm_le_of_components (coefficientH1Lin Ω a u)
    (mul_nonneg (mul_nonneg (by norm_num) a.bound_nonneg) (norm_nonneg u)) hv hg
  convert hn using 1; ring

/-- Actual bounded multiplication in H¹, with no regularity premise on the input. -/
def neumannH1CoefficientMultiplier (Ω : Set ℂ) (a : H1Coefficient Ω) :
    NeumannH1 Ω →L[ℂ] NeumannH1 Ω :=
  (coefficientH1Lin Ω a).mkContinuous (2 * Real.sqrt 3 * a.bound)
    (coefficientH1Lin_norm_le Ω a)

theorem h1Value_neumannH1CoefficientMultiplier (Ω : Set ℂ) (a : H1Coefficient Ω)
    (u : NeumannH1 Ω) :
    h1Value Ω (neumannH1CoefficientMultiplier Ω a u) = h1CoefficientL2 Ω a (h1Value Ω u) :=
  coefficientH1Vector_value Ω a u

theorem h1Gradient_neumannH1CoefficientMultiplier (Ω : Set ℂ) (a : H1Coefficient Ω)
    (u : NeumannH1 Ω) (i : Fin 2) :
    h1Gradient Ω i (neumannH1CoefficientMultiplier Ω a u) =
      h1CoefficientL2 Ω a (h1Gradient Ω i u) +
        h1CoefficientDerivativeL2 Ω a i (h1Value Ω u) :=
  coefficientH1Vector_gradient Ω a u i

end PolyaNeumann

end
