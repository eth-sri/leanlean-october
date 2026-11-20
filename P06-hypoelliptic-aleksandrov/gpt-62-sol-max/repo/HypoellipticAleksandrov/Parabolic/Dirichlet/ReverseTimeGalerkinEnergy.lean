module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinWeakForm
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormBounds
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialBounds
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Reverse-time finite Galerkin energy bounds

This module derives the finite-dimensional primal energy estimates from the
reverse-time Galerkin ODE.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open scoped BigOperators ENNReal Matrix Matrix.Norms.Elementwise MatrixOrder RealInnerProductSpace

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (N : ℕ) (x : ℝ → GalerkinCoordinates hΩ N)
include d Ω hΩ N x

def galerkinEnergy (t : ℝ) : ℝ :=
  ‖valueCLM hΩ (galerkinReconstruct hΩ N (x t) : H10HilbertGraph hΩ)‖ ^ 2

private def galerkinEnergyDeriv
    (xdot : GalerkinCoordinates hΩ N) (t : ℝ) : ℝ :=
  2 * inner ℝ
    (valueCLM hΩ (galerkinReconstruct hΩ N (x t) : H10HilbertGraph hΩ))
    (valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ))

def galerkinGradientEnergy (t : ℝ) : ℝ :=
  ‖gradientCLM hΩ (galerkinReconstruct hΩ N (x t) : H10HilbertGraph hΩ)‖ ^ 2

end

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)}

private theorem hasDerivWithinAt_value_reconstruct
    (hΩ : IsOpen Ω) (N : ℕ) (x : ℝ → GalerkinCoordinates hΩ N)
    (xdot : GalerkinCoordinates hΩ N)
    {s : Set ℝ} {τ : ℝ}
    (hx : HasDerivWithinAt x xdot s τ) :
    HasDerivWithinAt
      (fun t => valueCLM hΩ (galerkinReconstruct hΩ N (x t) : H10HilbertGraph hΩ))
      (valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ)) s τ := by
  let V :=
    (valueCLM hΩ).comp (galerkinReconstructCLM hΩ N)
  have hV := (V.hasFDerivAt).comp_hasDerivWithinAt τ hx
  simpa only [V, galerkinReconstructCLM_apply, ContinuousLinearMap.comp_apply,
    Function.comp_def, Pi.pow_def] using! hV

end

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)}

private theorem hasDerivWithinAt_energy_reconstruct
    (hΩ : IsOpen Ω) (N : ℕ) (x : ℝ → GalerkinCoordinates hΩ N)
    (xdot : GalerkinCoordinates hΩ N)
    {s : Set ℝ} {τ : ℝ}
    (hx : HasDerivWithinAt x xdot s τ) :
    HasDerivWithinAt
      (fun t => ‖valueCLM hΩ (galerkinReconstruct hΩ N (x t) : H10HilbertGraph hΩ)‖ ^ 2)
      (2 * inner ℝ
        (valueCLM hΩ (galerkinReconstruct hΩ N (x τ) : H10HilbertGraph hΩ))
        (valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ))) s τ := (hasDerivWithinAt_value_reconstruct hΩ N x xdot hx).norm_sq

private theorem energy_differential_algebra
    (lam K M : ℝ) (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ)
    (w f : PDE.ScalarLp Ω (2 : ℝ≥0∞)) (B : ℝ)
    (hidentity : inner ℝ w (valueCLM hΩ u) + B = -inner ℝ (valueCLM hΩ u) f)
    (hgarding : (lam / 2) * ‖gradientCLM hΩ u‖ ^ 2 - K * ‖valueCLM hΩ u‖ ^ 2 ≤ B)
    (hsource : ‖f‖ ≤ M) :
    2 * inner ℝ (valueCLM hΩ u) w ≤
      (2 * K + 1) * ‖valueCLM hΩ u‖ ^ 2 + M ^ 2 -
        lam * ‖gradientCLM hΩ u‖ ^ 2 := by
  have hforcing : -inner ℝ (valueCLM hΩ u) f ≤ ‖valueCLM hΩ u‖ * M := by
    calc
      -inner ℝ (valueCLM hΩ u) f ≤ |inner ℝ (valueCLM hΩ u) f| := neg_le_abs _
      _ ≤ ‖valueCLM hΩ u‖ * ‖f‖ := abs_real_inner_le_norm (valueCLM hΩ u) f
      _ ≤ ‖valueCLM hΩ u‖ * M :=
        mul_le_mul_of_nonneg_left hsource (norm_nonneg _)
  have hyoung : 2 * ‖valueCLM hΩ u‖ * M ≤ ‖valueCLM hΩ u‖ ^ 2 + M ^ 2 := by
    nlinarith [sq_nonneg (‖valueCLM hΩ u‖ - M)]
  rw [real_inner_comm]
  nlinarith

section
variable (hΩ : IsOpen Ω) (N : ℕ)

private theorem continuousOn_galerkinEnergy
    (x : ℝ → GalerkinCoordinates hΩ N) (s : Set ℝ)
    (hx : ContinuousOn x s) :
    ContinuousOn (galerkinEnergy hΩ N x) s := by
  let V : GalerkinCoordinates hΩ N →L[ℝ]
      PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
    (valueCLM hΩ).comp (galerkinReconstructCLM hΩ N)
  have hV : ContinuousOn (fun t => V (x t)) s :=
    V.continuous.continuousOn.comp hx (fun _ _ => Set.mem_univ _)
  simpa only [galerkinEnergy, V, galerkinReconstructCLM_apply, ContinuousLinearMap.comp_apply,
    Function.comp_def, Pi.pow_def] using! hV.norm.pow 2

private theorem galerkinEnergy_zero_le_initial
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (x : ℝ → GalerkinCoordinates hΩ N)
    (hx0 : x 0 = (galerkinSpaceBasis hΩ N).equivFun
      (galerkinInitialProjection hΩ N initial)) :
    galerkinEnergy hΩ N x 0 ≤ ‖initial‖ ^ 2 := by
  have hrec : (galerkinReconstruct hΩ N (x 0) : H10HilbertGraph hΩ) =
      (galerkinInitialProjection hΩ N initial : H10HilbertGraph hΩ) := by
    calc
      (galerkinReconstruct hΩ N (x 0) : H10HilbertGraph hΩ) =
          (galerkinReconstruct hΩ N ((galerkinSpaceBasis hΩ N).equivFun
            (galerkinInitialProjection hΩ N initial)) : H10HilbertGraph hΩ) :=
        congrArg (fun z => (galerkinReconstruct hΩ N z : H10HilbertGraph hΩ)) hx0
      _ = (galerkinInitialProjection hΩ N initial : H10HilbertGraph hΩ) :=
        congrArg (fun v : galerkinSpace hΩ N => (v : H10HilbertGraph hΩ))
          (galerkinReconstruct_equivFun hΩ N (galerkinInitialProjection hΩ N initial))
  rw [galerkinEnergy, hrec]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (norm_value_galerkinInitialProjection_le hΩ N initial)

private theorem continuousOn_galerkinGradientEnergy
    (x : ℝ → GalerkinCoordinates hΩ N) (s : Set ℝ)
    (hx : ContinuousOn x s) :
    ContinuousOn (galerkinGradientEnergy hΩ N x) s := by
  let W := (gradientCLM hΩ).comp (galerkinReconstructCLM hΩ N)
  have hW :=
    W.continuous.continuousOn.comp hx (fun _ _ => Set.mem_univ _)
  simpa only [galerkinGradientEnergy, W, galerkinReconstructCLM_apply, ContinuousLinearMap.comp_apply,
    Function.comp_def, Pi.pow_def] using! hW.norm.pow 2

end

end

private theorem continuousOn_two_mul_inner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {s : Set ℝ} (v w : ℝ → E)
    (hv : ContinuousOn v s) (hw : ContinuousOn w s) :
    ContinuousOn (fun t => 2 * inner ℝ (v t) (w t)) s := continuousOn_const.mul (hv.inner hw)

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)}

private theorem galerkin_energy_deriv_ineq
    {r₀ r₁ lam : ℝ} (P : ReverseTimeGalerkinProblem Ω r₀ r₁ lam) (K M : ℝ)
    (hGarding : ∀ τ, τ ∈ Set.Icc 0 (r₁ - r₀) → ∀ u : H10HilbertGraph P.hΩ,
      (lam / 2) * ‖gradientCLM P.hΩ u‖ ^ 2 - K * ‖valueCLM P.hΩ u‖ ^ 2 ≤
        reverseTimeSpatialForm P.hΩ r₁ τ P.a P.b P.c u u)
    (hsource : ∀ τ, τ ∈ Set.Icc 0 (r₁ - r₀) →
      ∀ hτLp : MeasureTheory.MemLp (fun y : PDE.Vec d => P.F (r₁ - τ) y)
        (2 : ℝ≥0∞) (PDE.volumeOn Ω),
        ‖hτLp.toLp (fun y : PDE.Vec d => P.F (r₁ - τ) y)‖ ≤ M)
    (N : ℕ) (x : ℝ → GalerkinCoordinates P.hΩ N)
    (τ : Set.Icc 0 (r₁ - r₀))
    (hdx : HasDerivWithinAt x (galerkinRate P N τ (x τ))
      (Set.Icc 0 (r₁ - r₀)) τ) :
    HasDerivWithinAt (galerkinEnergy P.hΩ N x)
      (galerkinEnergyDeriv P.hΩ N x (galerkinRate P N τ (x τ)) τ) (Set.Icc 0 (r₁ - r₀)) τ ∧
    galerkinEnergyDeriv P.hΩ N x (galerkinRate P N τ (x τ)) τ +
      lam * galerkinGradientEnergy P.hΩ N x τ ≤ (2 * K + 1) * galerkinEnergy P.hΩ N x τ + M ^ 2 := by
  let xdot := galerkinRate P N τ (x τ)
  let u : H10HilbertGraph P.hΩ := galerkinReconstruct P.hΩ N (x τ)
  let f : PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
    reverseTimeSourceSlice r₁ τ.1 P.F
      (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood r₀ r₁ P.hΩ P.hΩbounded P.F P.hFSmooth
        τ.1 τ.2)
  have hderiv : HasDerivWithinAt (galerkinEnergy P.hΩ N x)
      (galerkinEnergyDeriv P.hΩ N x xdot τ) (Set.Icc 0 (r₁ - r₀)) τ := by
    simpa only [galerkinEnergy, galerkinEnergyDeriv] using!
      hasDerivWithinAt_energy_reconstruct P.hΩ N x xdot hdx
  refine ⟨hderiv, ?_⟩
  have hid := galerkinRate_weak P N τ (x τ) (galerkinReconstruct P.hΩ N (x τ))
  have hid' : inner ℝ
      (valueCLM P.hΩ (galerkinReconstruct P.hΩ N xdot : H10HilbertGraph P.hΩ))
      (valueCLM P.hΩ u) +
      reverseTimeSpatialForm P.hΩ r₁ τ.1 P.a P.b P.c u u =
      -inner ℝ (valueCLM P.hΩ u) f := by
    rw [ReverseTimeGalerkinProblem.sourceRaw, reverseTimeNegativeSourceRaw_eq_sourceFunctional_of_mem_Icc
      r₀ r₁ P.h₀₁ P.hΩ P.hΩbounded P.F P.hFSmooth τ.1 τ.2] at hid
    simpa only [u, f, reverseTimeSourceFunctional_apply] using hid
  have hbound := energy_differential_algebra lam K M P.hΩ u
    (valueCLM P.hΩ (galerkinReconstruct P.hΩ N xdot : H10HilbertGraph P.hΩ)) f
    (reverseTimeSpatialForm P.hΩ r₁ τ.1 P.a P.b P.c u u) hid'
    (hGarding τ.1 τ.2 u)
    (hsource τ.1 τ.2
      (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood r₀ r₁ P.hΩ P.hΩbounded P.F P.hFSmooth
        τ.1 τ.2))
  simpa only [galerkinEnergyDeriv, galerkinGradientEnergy, galerkinEnergy, xdot, u] using
    (le_sub_iff_add_le.mp hbound)

private theorem continuousOn_galerkinEnergyDeriv
    (hΩ : IsOpen Ω) (N : ℕ)
    (x xdot : ℝ → GalerkinCoordinates hΩ N) (s : Set ℝ)
    (hx : ContinuousOn x s) (hxdot : ContinuousOn xdot s) :
    ContinuousOn (fun t => galerkinEnergyDeriv hΩ N x (xdot t) t) s := by
  let V : GalerkinCoordinates hΩ N →L[ℝ]
      PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
    (valueCLM hΩ).comp (galerkinReconstructCLM hΩ N)
  have hVx : ContinuousOn (fun t => V (x t)) s :=
    V.continuous.continuousOn.comp hx (fun _ _ => Set.mem_univ _)
  have hVxdot : ContinuousOn (fun t => V (xdot t)) s :=
    V.continuous.continuousOn.comp hxdot (fun _ _ => Set.mem_univ _)
  simpa only [galerkinEnergyDeriv, V, galerkinReconstructCLM_apply, ContinuousLinearMap.comp_apply,
    Function.comp_def, Pi.pow_def] using!
    continuousOn_two_mul_inner _ _ hVx hVxdot

end

/-- Smooth finite Galerkin systems have uniform primal energy bounds. -/
theorem exists_reverseTimeGalerkin_uniform_energy_solution
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    {r₀ r₁ lam : ℝ} (P : ReverseTimeGalerkinProblem Ω r₀ r₁ lam) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ (N : ℕ) (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)),
        ∃ x : ℝ → GalerkinCoordinates P.hΩ N,
          IsGalerkinTrajectory P N initial x ∧
            (∀ t ∈ Set.Icc 0 (r₁ - r₀),
              galerkinEnergy P.hΩ N x t ≤ gronwallBound (‖initial‖ ^ 2) (2 * K + 1) (M ^ 2) t) ∧
            ∀ t ∈ Set.Icc 0 (r₁ - r₀),
              lam * (∫ τ in Set.Ioc 0 t, galerkinGradientEnergy P.hΩ N x τ) ≤
                ‖initial‖ ^ 2 + (2 * K + 1) * t *
                  gronwallBound (‖initial‖ ^ 2) (2 * K + 1) (M ^ 2) (r₁ - r₀) + M ^ 2 * t := by
  obtain ⟨K, hK, hGarding⟩ :=
    reverseTimeSpatialForm_garding_of_smoothOnNeighborhood r₀ r₁ lam P.h₀₁ P.hlam P.hΩ P.hΩbounded
      P.a P.b P.c P.haSmooth P.hbSmooth P.hcSmooth P.hLower P.hcNonpos
  obtain ⟨M, hM, hsource⟩ :=
    exists_reverseTimeSourceSlice_L2_bound_of_smoothOnNeighborhood r₀ r₁ P.hΩ P.hΩbounded P.F P.hFSmooth
  refine ⟨K, hK, M, hM, ?_⟩
  intro N initial
  obtain ⟨x, hspec⟩ := exists_reverseTimeGalerkin_solution P N initial
  have hxcont := hspec.continuousOn
  let T : ℝ := r₁ - r₀
  have hT : 0 ≤ T := sub_nonneg.mpr P.h₀₁.le
  let xdot : ℝ → GalerkinCoordinates P.hΩ N := fun t => galerkinRate P N (Set.projIcc 0 T hT t) (x t)
  have hxdot : ContinuousOn xdot (Set.Icc 0 T) := continuousOn_galerkinRate P N hxcont
  let D : ℝ → ℝ := fun t => galerkinEnergyDeriv P.hΩ N x (xdot t) t
  have hDcont : ContinuousOn D (Set.Icc 0 T) :=
    continuousOn_galerkinEnergyDeriv P.hΩ N x xdot _ hxcont hxdot
  have hEcont := continuousOn_galerkinEnergy P.hΩ N x (Set.Icc 0 T) hxcont
  have hGcont := continuousOn_galerkinGradientEnergy P.hΩ N x (Set.Icc 0 T) hxcont
  have hED (t) (ht : t ∈ Set.Icc 0 T) :
      HasDerivWithinAt (galerkinEnergy P.hΩ N x) (D t) (Set.Icc 0 T) t ∧
      D t + lam * galerkinGradientEnergy P.hΩ N x t ≤
        (2 * K + 1) * galerkinEnergy P.hΩ N x t + M ^ 2 := by
    let τ : Set.Icc 0 (r₁ - r₀) := ⟨t, ht⟩
    have hp : Set.projIcc 0 T hT t = τ := Set.projIcc_of_mem hT ht
    simpa only [D, xdot, hp] using
      galerkin_energy_deriv_ineq P K M hGarding hsource N x τ (hspec.deriv τ)
  have hEicc t ht := (hED t ht).1
  have hEineq t ht := (hED t ht).2
  have hE0 := galerkinEnergy_zero_le_initial P.hΩ N initial x hspec.initial_eq
  have hEbound : ∀ t ∈ Set.Icc 0 T,
      galerkinEnergy P.hΩ N x t ≤ gronwallBound (‖initial‖ ^ 2) (2 * K + 1) (M ^ 2) t := by
    have hbound : ∀ t ∈ Set.Icc 0 T,
        galerkinEnergy P.hΩ N x t ≤
          gronwallBound (‖initial‖ ^ 2) (2 * K + 1) (M ^ 2) (t - 0) := by
      apply le_gronwallBound_of_liminf_deriv_right_le hEcont
      · intro t ht r hr
        have hgrad : 0 ≤ lam * galerkinGradientEnergy P.hΩ N x t :=
          mul_nonneg P.hlam.le (sq_nonneg _)
        have hDle : D t ≤ (2 * K + 1) * galerkinEnergy P.hΩ N x t + M ^ 2 :=
          (le_add_of_nonneg_right hgrad).trans (hEineq t (Set.Ico_subset_Icc_self ht))
        exact ((hEicc t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem ht)).liminf_right_slope_le (hDle.trans_lt hr)
      · simpa only [T] using hE0
      · intro t ht
        have hg : 0 ≤ galerkinGradientEnergy P.hΩ N x t := sq_nonneg _
        linarith [hEineq t (Set.Ico_subset_Icc_self ht)]
    simpa only [sub_zero] using hbound
  refine ⟨x, hspec, hEbound, ?_⟩
  intro t ht
  have htT : t ∈ Set.Icc 0 T := by simpa only [T] using ht
  let R := gronwallBound (‖initial‖ ^ 2) (2 * K + 1) (M ^ 2) T
  have hA0 : 0 ≤ 2 * K + 1 := by linarith
  have hconst : ∀ s ∈ Set.Icc 0 t,
      D s + lam * galerkinGradientEnergy P.hΩ N x s ≤ (2 * K + 1) * R + M ^ 2 := by
    intro s hs
    have hsT : s ∈ Set.Icc 0 T := ⟨hs.1, hs.2.trans htT.2⟩
    have hER : galerkinEnergy P.hΩ N x s ≤ R := (hEbound s hsT).trans
      (gronwallBound_mono (sq_nonneg _) (sq_nonneg _) hA0 (hs.2.trans htT.2))
    have hmult := mul_le_mul_of_nonneg_left hER hA0
    linarith [hEineq s hsT]
  have hleft : IntervalIntegrable (fun s => D s + lam * galerkinGradientEnergy P.hΩ N x s)
      MeasureTheory.volume 0 t := ((hDcont.add (continuousOn_const.mul hGcont)).mono
        (Set.Icc_subset_Icc le_rfl htT.2)).intervalIntegrable_of_Icc ht.1
  have hDint : IntervalIntegrable D MeasureTheory.volume 0 t :=
    (hDcont.mono (Set.Icc_subset_Icc le_rfl htT.2)).intervalIntegrable_of_Icc ht.1
  have hGint : IntervalIntegrable (galerkinGradientEnergy P.hΩ N x)
      MeasureTheory.volume 0 t :=
    (hGcont.mono (Set.Icc_subset_Icc le_rfl htT.2)).intervalIntegrable_of_Icc ht.1
  have hLGint : IntervalIntegrable (fun s => lam * galerkinGradientEnergy P.hΩ N x s)
      MeasureTheory.volume 0 t := hGint.const_mul lam
  have hint := intervalIntegral.integral_mono_on ht.1 hleft
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => (2 * K + 1) * R + M ^ 2) MeasureTheory.volume 0 t)
    (by
      intro s hs
      exact hconst s hs)
  have hFTC : (∫ s in 0..t, D s) = galerkinEnergy P.hΩ N x t - galerkinEnergy P.hΩ N x 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1
      (hEcont.mono (Set.Icc_subset_Icc le_rfl htT.2))
    · intro s hs
      have hsIcc : s ∈ Set.Icc 0 T := ⟨hs.1.le, hs.2.le.trans htT.2⟩
      have hsIco : s ∈ Set.Ico 0 T := ⟨hs.1.le, hs.2.trans_le htT.2⟩
      exact (hEicc s hsIcc).mono_of_mem_nhdsWithin (Icc_mem_nhdsGT_of_mem hsIco)
    · exact (hDcont.mono (Set.Icc_subset_Icc le_rfl htT.2)).intervalIntegrable_of_Icc ht.1
  rw [intervalIntegral.integral_add hDint hLGint, intervalIntegral.integral_const_mul, hFTC,
    intervalIntegral.integral_const] at hint
  have hEt : 0 ≤ galerkinEnergy P.hΩ N x t := sq_nonneg _
  have hrhs : t * ((2 * K + 1) * R + M ^ 2) =
      (2 * K + 1) * t * R + M ^ 2 * t := by
    ring
  rw [sub_zero, smul_eq_mul, hrhs] at hint
  have hgrad : lam * (∫ s in 0..t, galerkinGradientEnergy P.hΩ N x s) ≤
      ‖initial‖ ^ 2 + (2 * K + 1) * t * R + M ^ 2 * t := by
    linarith [hint, hE0]
  simpa only [R, T, intervalIntegral.integral_of_le ht.1] using
    hgrad


end HypoellipticAleksandrov.Parabolic.Dirichlet
