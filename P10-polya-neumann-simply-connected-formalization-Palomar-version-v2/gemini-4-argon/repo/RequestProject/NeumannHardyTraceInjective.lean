module

public import RequestProject.NeumannTraceInjective
public import RequestProject.NeumannConstantTrace
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Uniqueness from the actual Hardy trace

The first-order conjugate Green identity is extended from compact smooth
restrictions to the genuine weak-gradient H¹ space. A zero actual trace
therefore makes the Cauchy--Riemann equation valid against global compact
tests. Its distributional Laplacian vanishes across the boundary. The
existing second-order Green identity then gives the zero-energy form
equation, whose genuine constants have injective actual trace.

No smoothness, Neumann equation, or spectral premise is imposed on the
input H¹ vector. Boundary measure is ordinary dθ and the boundary direction
in the first-order identity is the actual conjugate velocity.

This module is part of the verified dependency chain.
-/

@[expose] public section


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Topology
open scoped Real InnerProductSpace ComplexConjugate ContDiff

variable {Ω : Set ℂ} {φ : ℂ → ℂ} {γ : ℝ → ℂ}

def hardyL2TestPair Ω 
    (hφ : TestFunction univ φ) : L2 Ω →L[ℂ] ℂ :=
  innerSL ℂ ((hφ.conj.memLp' 2).toLp (fun z => conj (φ z)))

private theorem hardyL2TestPair_apply (Ω : Set ℂ) 
    (hφ : TestFunction univ φ) u :
    hardyL2TestPair Ω hφ u = ∫ z in Ω, u z * φ z := by
  change ⟪(hφ.conj.memLp' 2).toLp (fun z => conj (φ z)), u⟫_ℂ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hφ.conj.memLp' 2 (μ := volume.restrict Ω)).coeFn_toLp] with z hz
  simp [hz]

theorem hardyConjugateVelocityTest_memLp  
    (hγ : IsBoundaryParam Ω γ)  (hφ : TestFunction univ φ) :
    MemLp (fun θ => conj (φ (γ θ) * conj (deriv γ θ))) 2
      (volume.restrict (Ioc 0 (2 * π))) := by
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  obtain ⟨C, hC⟩ := hφ.2.1.exists_bound_of_continuous hφ.1.continuous
  apply MemLp.of_bound
    (Complex.continuous_conj.comp_aestronglyMeasurable ((hφ.1.continuous.comp hKγ.continuous).aestronglyMeasurable.mul (Complex.continuous_conj.comp_aestronglyMeasurable (measurable_deriv γ).aestronglyMeasurable))).restrict (C * Kγ)
  apply Eventually.of_forall
  intro θ
  simp [Complex.norm_conj]
  exact mul_le_mul (hC (γ θ)) (norm_deriv_le_of_lipschitz hKγ)
    (norm_nonneg _) ((norm_nonneg (φ 0)).trans (hC 0))

/-- The actual conjugate-velocity boundary test is an L² class. -/
def hardyConjugateVelocityTestL2  
    (hγ : IsBoundaryParam Ω γ)  (hφ : TestFunction univ φ) : BoundaryL2 :=
  (hardyConjugateVelocityTest_memLp hγ hφ).toLp
    (fun θ => conj (φ (γ θ) * conj (deriv γ θ)))

/-- A continuous first-order boundary functional on the actual H¹ space. -/
def h1FirstOrderConjugateBoundaryTest  (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω)  (hγ : IsBoundaryParam Ω γ)
     (hφ : TestFunction univ φ) : NeumannH1 Ω →L[ℂ] ℂ :=
  (innerSL ℂ (hardyConjugateVelocityTestL2 hγ hφ)).comp (h1BoundaryTrace hb hL hγ)

/-- The two genuine weak derivatives and the smooth test derivatives
give a continuous first-order interior functional. -/
def h1FirstOrderConjugateInteriorTest Ω 
    (hφ : TestFunction univ φ) : NeumannH1 Ω →L[ℂ] ℂ :=
  (-Complex.I) • ((hardyL2TestPair Ω hφ).comp (h1Gradient Ω 0) +
      (hardyL2TestPair Ω (hφ.dirD 1)).comp (h1Value Ω)) -
    ((hardyL2TestPair Ω hφ).comp (h1Gradient Ω 1) +
      (hardyL2TestPair Ω (hφ.dirD Complex.I)).comp (h1Value Ω))

theorem h1FirstOrderConjugateBoundaryTest_apply 
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) 
    (hγ : IsBoundaryParam Ω γ)  (hφ : TestFunction univ φ)
    u :
    h1FirstOrderConjugateBoundaryTest hb hL hγ hφ u =
      ∫ θ in Ioc 0 (2 * π), h1BoundaryTrace hb hL hγ u θ *
        (φ (γ θ) * conj (deriv γ θ)) := by
  change ⟪hardyConjugateVelocityTestL2 hγ hφ, h1BoundaryTrace hb hL hγ u⟫_ℂ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hardyConjugateVelocityTest_memLp hγ hφ).coeFn_toLp] with θ hθ
  simp only [hardyConjugateVelocityTestL2, RCLike.inner_apply, hθ, Complex.conj_conj]

private theorem smooth_conjugate_firstOrder_green 
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) 
    (hγ : IsBoundaryParam Ω γ)  (hp : TestFunction univ p) :
    (∫ θ in Ioc 0 (2 * π), p (γ θ) * conj (deriv γ θ)) =
      -Complex.I * (∫ z in Ω, dirD p 1 z) - ∫ z in Ω, dirD p Complex.I z := by
  obtain ⟨Kp, hKp⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    hp.conj.2.1 hp.conj.1 (by simp)
  have hdbar z :
      conj (dbar (fun w => conj (p w)) z) = (dirD p 1 z - Complex.I * dirD p Complex.I z) / 2 := by
    change conj ((dirD (fun w => conj (p w)) 1 z +
      Complex.I * dirD (fun w => conj (p w)) Complex.I z) / 2) = _
    rw [dirD_conj (hp.1.of_le (by simp)), dirD_conj (hp.1.of_le (by simp))]
    simp only [map_div₀, map_add, map_mul, Complex.conj_conj, Complex.conj_I, map_ofNat]
    ring
  calc
    _ = conj (∫ θ in Ioc 0 (2 * π), conj (p (γ θ)) * deriv γ θ) := by
      rw [← integral_conj]
      simp only [map_mul, Complex.conj_conj]
    _ = _ := congrArg conj (by
      simpa only [intervalIntegral.integral_of_le (by positivity : 0 ≤ 2 * π)]
        using integral_boundary_eq_dbar hb hL hγ hKp hp.conj.2.1)
    _ = -2 * Complex.I * ∫ z in Ω, conj (dbar (fun w => conj (p w)) z) := by
      rw [map_mul, ← integral_conj]
      simp only [map_mul, map_ofNat, Complex.conj_I]
      ring
    _ = ∫ z in Ω, (-Complex.I * dirD p 1 z - dirD p Complex.I z) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      apply Eventually.of_forall
      intro z
      change -2 * Complex.I * conj (dbar (fun w => conj (p w)) z) = _
      rw [hdbar]
      ring_nf; simp only [Complex.I_sq]; ring
    _ = _ := by rw [integral_sub ((memLp_one_iff_integrable.mp ((hp.dirD 1).memLp' 1)).const_mul _) (memLp_one_iff_integrable.mp ((hp.dirD Complex.I).memLp' 1)), integral_const_mul]

private theorem hardyL2TestPair_smooth_value (Ω : Set ℂ) 
    (hφ : TestFunction univ φ) f :
    hardyL2TestPair Ω hφ (h1Value Ω (smoothTraceH1 Ω f)) = ∫ z in Ω, f z * φ z := by
  rw [hardyL2TestPair_apply]
  apply integral_congr_ae
  filter_upwards [(smoothTraceTests_memLp Ω f).coeFn_toLp] with z hz
  rw [h1Value_smoothTraceH1, hz]

private theorem hardyL2TestPair_smooth_gradient (Ω : Set ℂ) 
    (hφ : TestFunction univ φ) f i :
    hardyL2TestPair Ω hφ (h1Gradient Ω i (smoothTraceH1 Ω f)) =
      ∫ z in Ω, dirD (f : ℂ → ℂ) (coordDir i) z * φ z := by
  rw [hardyL2TestPair_apply]
  apply integral_congr_ae
  filter_upwards [(smoothTraceTests_memLp_deriv Ω f i).coeFn_toLp] with z hz
  simpa [dirD] using
    congrArg (fun w => w * φ z) hz

/-- The raw first-order formula uses the genuine value, weak gradients,
and actual trace, with the unnormalized boundary measure dθ. -/
local notation "Φ0" => h1Gradient Ω 1

local notation "Φ1" => h1Gradient Ω 0

local notation "Φ2" => h1Value Ω

local notation "Φ3" => dirD φ Complex.I

local notation "Φ4" => dirD φ 1

theorem h1_firstOrder_conjugate_green 
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) 
    (hγ : IsBoundaryParam Ω γ)  (hφ : TestFunction univ φ)
    (u : NeumannH1 Ω) :
    -Complex.I * ((∫ z in Ω, Φ1 u z * φ z) +
      ∫ z in Ω, Φ2 u z * Φ4 z) -
      ((∫ z in Ω, Φ0 u z * φ z) +
        ∫ z in Ω, Φ2 u z * Φ3 z) =
      ∫ θ in Ioc 0 (2 * π), h1BoundaryTrace hb hL hγ u θ *
        (φ (γ θ) * conj (deriv γ θ)) := by
  rw [← (show h1FirstOrderConjugateInteriorTest Ω hφ u = -Complex.I * ((∫ z in Ω, Φ1 u z * φ z) + ∫ z in Ω, Φ2 u z * Φ4 z) - ((∫ z in Ω, Φ0 u z * φ z) + ∫ z in Ω, Φ2 u z * Φ3 z) by
    simp only [h1FirstOrderConjugateInteriorTest, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, smul_eq_mul, hardyL2TestPair_apply]),
    ← (show h1FirstOrderConjugateBoundaryTest hb hL hγ hφ = h1FirstOrderConjugateInteriorTest Ω hφ by
      apply DFunLike.coe_injective
      apply (denseRange_smoothTraceH1Lin hb hL).equalizer
        (h1FirstOrderConjugateBoundaryTest hb hL hγ hφ).continuous
        (h1FirstOrderConjugateInteriorTest Ω hφ).continuous
      funext f
      rw [Function.comp_apply, Function.comp_apply, smoothTraceH1Lin_apply]
      exact (by
        let p : ℂ → ℂ := fun z => f z * φ z
        have hproduct (v z : ℂ) :
            dirD p v z = dirD f v z * φ z + f z * dirD φ v z := by
          rw [dirD, fderiv_fun_mul (f.property.1.differentiable (by simp) z)
            (hφ.1.differentiable (by simp) z)]
          simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
          dsimp only [dirD]
          ring
        have hproduct_integral v :
            (∫ z in Ω, dirD p v z) = (∫ z in Ω, dirD f v z * φ z) +
              ∫ z in Ω, f z * dirD φ v z := by
          simp_rw [hproduct]
          exact integral_add (integrable_mul_test ((f.property.dirD v).memLp' 2) hφ)
            (integrable_mul_test (f.property.memLp' 2) (hφ.dirD v))
        rw [show h1FirstOrderConjugateBoundaryTest hb hL hγ hφ (smoothTraceH1 Ω f) = ∫ θ in Ioc 0 (2 * π), p (γ θ) * conj (deriv γ θ) by
          rw [h1FirstOrderConjugateBoundaryTest_apply]
          apply integral_congr_ae
          filter_upwards [h1BoundaryTrace_smooth_ae hb hL hγ f] with θ hθ
          rw [hθ]
          dsimp [p]
          ring, smooth_conjugate_firstOrder_green hb hL hγ ⟨f.property.1.mul hφ.1, f.property.2.1.mul_right, subset_univ _⟩,
          hproduct_integral, hproduct_integral]
        have hdir0 : coordDir 0 = 1 := rfl
        have hdir1 : coordDir 1 = Complex.I := rfl
        simp only [h1FirstOrderConjugateInteriorTest, ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.comp_apply, smul_eq_mul, hardyL2TestPair_smooth_gradient,
          hardyL2TestPair_smooth_value, hdir0, hdir1])),
    h1FirstOrderConjugateBoundaryTest_apply]

private theorem hardy_zeroTrace_boundary_test 
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) 
    (hγ : IsBoundaryParam Ω γ) (u : NeumannH1 Ω)
    (ht : h1BoundaryTrace hb hL hγ u = 0) (a : ℝ → ℂ) :
    (∫ θ in Ioc 0 (2 * π), h1BoundaryTrace hb hL hγ u θ * a θ) = 0 := by
  apply integral_eq_zero_of_ae
  rw [ht]
  filter_upwards [Lp.coeFn_zero ℂ 2 (volume.restrict (Ioc 0 (2 * π)))] with θ hθ
  simp only [hθ, Pi.zero_apply, zero_mul]

private theorem hardy_gradient_test_factor  (u : NeumannH1 Ω)
    (hCR : Φ1 u = Complex.I • Φ0 u) (ψ : ℂ → ℂ) :
    (∫ z in Ω, Φ1 u z * ψ z) =
      Complex.I * ∫ z in Ω, Φ0 u z * ψ z := by
  rw [hCR]
  calc
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul Complex.I (Φ0 u)] with z hz
      rw [hz]
      exact mul_assoc _ _ _
    _ = _ := integral_const_mul _ _

private theorem hardy_firstOrder_algebra A B G
    (h : -Complex.I * (Complex.I * G + A) - (G + B) = 0) : A = Complex.I * B := by
  rw [show -Complex.I * (Complex.I * G + A) - (G + B) = -Complex.I * A - B by
    ring_nf; simp only [Complex.I_sq]; ring] at h
  apply sub_eq_zero.mp
  calc
    _ = Complex.I * (-Complex.I * A - B) := by
      ring_nf; simp only [Complex.I_sq]; ring
    _ = 0 := by rw [h, mul_zero]

/-- CR and zero physical trace give the first-order distribution identity
against global compact tests, rather than only tests supported inside Ω. -/
theorem h1_antiholomorphic_global_test_of_zero_trace 
    (hb : Bornology.IsBounded Ω) hL 
    (hγ : IsBoundaryParam Ω γ) (u : NeumannH1 Ω)
    (hCR : Φ1 u = Complex.I • Φ0 u)
    (ht : h1BoundaryTrace hb hL hγ u = 0)
     (hφ : TestFunction univ φ) :
    (∫ z in Ω, Φ2 u z * Φ4 z) =
      Complex.I * ∫ z in Ω, Φ2 u z * dirD φ Complex.I z := by
  have h := h1_firstOrder_conjugate_green hb hL hγ hφ u
  rw [hardy_zeroTrace_boundary_test hb hL hγ u ht,
    hardy_gradient_test_factor u hCR] at h
  exact hardy_firstOrder_algebra _ _ _ h

theorem h1_antiholomorphic_global_lap_test_of_zero_trace 
    hb hL 
    (hγ : IsBoundaryParam Ω γ) u
    (hCR : Φ1 u = Complex.I • Φ0 u)
    (ht : h1BoundaryTrace hb hL hγ u = 0)
     (hφ : TestFunction univ φ) :
    (∫ z in Ω, Φ2 u z * lap φ z) = 0 := by
  have hc : (∫ z in Ω, Φ2 u z * dirD (Φ4) Complex.I z) =
      ∫ z in Ω, Φ2 u z * dirD (Φ3) 1 z := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun z => by
      change Φ2 u z * dirD (Φ4) Complex.I z = _
      have h_inl v w z : dirD (dirD φ v) w z = dirD (dirD φ w) v z := by
        have hd :=
          (hφ.1.fderiv_right (m := (⊤ : ℕ∞)) le_rfl).differentiable (by simp) z
        change fderiv ℝ (dirD φ v) z w = fderiv ℝ (dirD φ w) z v
        rw [show fderiv ℝ (dirD φ v) z w = fderiv ℝ (fderiv ℝ φ) z w v by
          change fderiv ℝ (fun x => fderiv ℝ φ x v) z w = _
          rw [fderiv_clm_apply hd (differentiableAt_const _)]
          simp, show fderiv ℝ (dirD φ w) z v = fderiv ℝ (fderiv ℝ φ) z v w by
          change fderiv ℝ (fun x => fderiv ℝ φ x w) z v = _
          rw [fderiv_clm_apply hd (differentiableAt_const _)]
          simp]
        exact (hφ.1.contDiffAt.isSymmSndFDerivAt (by
          simpa using
            (WithTop.coe_le_coe.mpr le_top))).eq w v
      rw [h_inl])
  calc
    _ = (∫ z in Ω, Φ2 u z * dirD (Φ4) 1 z) +
        ∫ z in Ω, Φ2 u z * dirD (Φ3) Complex.I z := by
      simp [lap, mul_add]
      exact integral_add (integrable_mul_test (Lp.memLp (Φ2 u)) ((hφ.dirD 1).dirD 1)) (integrable_mul_test (Lp.memLp (Φ2 u)) ((hφ.dirD Complex.I).dirD Complex.I))
    _ = Complex.I * (Complex.I * ∫ z in Ω,
        Φ2 u z * dirD (Φ3) Complex.I z) +
        ∫ z in Ω, Φ2 u z * dirD (Φ3) Complex.I z := by
      rw [h1_antiholomorphic_global_test_of_zero_trace hb hL hγ u hCR ht (hφ.dirD 1), hc, h1_antiholomorphic_global_test_of_zero_trace hb hL hγ u hCR ht (hφ.dirD Complex.I)]
    _ = 0 := by rw [← mul_assoc, Complex.I_mul_I]; ring

theorem neumannH1_eq_zero_of_antiholomorphic_zero_trace 
    hb hL 
    (hγ : IsBoundaryParam Ω γ) u
    (hCR : Φ1 u = Complex.I • Φ0 u)
    (ht : h1BoundaryTrace hb hL hγ u = 0) : u = 0 := by
  haveI : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  obtain ⟨c, hcu⟩ := (h1HelmholtzForm_zero_eq_zero_iff_constant hb hL.1 u).mp (by
    apply ext_inner_left ℂ
    intro v
    rw [inner_zero_right]
    exact congrFun (show (fun v : NeumannH1 Ω => ⟪v, h1HelmholtzForm Ω 0 u⟫_ℂ) = (fun _ => 0) by
      apply (denseRange_smoothTraceH1Lin hb hL).equalizer
        (continuous_id.inner continuous_const) continuous_const
      funext f
      change ⟪smoothTraceH1 Ω f, h1HelmholtzForm Ω 0 u⟫_ℂ = 0
      rw [h1HelmholtzForm_inner]
      simp only [Complex.ofReal_zero, zero_mul, sub_zero]
      have h_inl Ω u f i : ⟪h1Gradient Ω i (smoothTraceH1 Ω f), h1Gradient Ω i u⟫_ℂ = ∫ z in Ω, h1Gradient Ω i u z * dirD (fun w => conj (f w)) (coordDir i) z := by
        rw [h1Gradient_smoothTraceH1, L2.inner_def]
        apply integral_congr_ae
        filter_upwards [(smoothTraceTests_memLp_deriv Ω f i).coeFn_toLp] with z hz
        simp only [RCLike.inner_apply', hz]
        rw [dirD_conj (f.property.1.of_le (by simp))]
        exact mul_comm _ _
      simp_rw [h_inl]
      exact (by
        have hg := h1_doubleLayer_green hb hL hγ f.property.conj u
        rw [h1_antiholomorphic_global_lap_test_of_zero_trace hb hL hγ u hCR ht f.property.conj,
          zero_add, hardy_zeroTrace_boundary_test hb hL hγ u ht] at hg
        exact hg)) v)
  apply h1Value_injective hL.1.1
  simp [hcu, show c = 0 by
    apply (boundaryLpConst_eq_zero_iff c).mp
    rw [← h1BoundaryTrace_h1Constant hb hL hγ c, ← hcu]
    exact ht]

/-- Equal actual traces identify actual weak antiholomorphic H¹ vectors. -/
theorem neumannH1_eq_of_antiholomorphic_same_trace 
    hb hL 
    (hγ : IsBoundaryParam Ω γ) u v
    (hu : Φ1 u = Complex.I • Φ0 u)
    (hv : Φ1 v = Complex.I • Φ0 v)
    (ht : h1BoundaryTrace hb hL hγ u = h1BoundaryTrace hb hL hγ v) : u = v := by
  apply sub_eq_zero.mp
  apply neumannH1_eq_zero_of_antiholomorphic_zero_trace hb hL hγ (u - v)
  · rw [map_sub, map_sub, hu, hv, smul_sub]
  · rw [map_sub, ht, sub_self]

end PolyaNeumann

end
