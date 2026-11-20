module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.SphericalFractionalIntegrals.Smoothness
public import Mathlib.Data.Set.Finite.List

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.RotationCalculus
open MeasureTheory Set
open scoped RealInnerProductSpace Pointwise

noncomputable def rawRotationVector (i : Fin 3) (x : Ambient) : Ambient :=
  WithLp.toLp 2 (fun j : Fin 3 =>
    if j = i + 1 then -x (i + 2) else if j = i + 2 then x (i + 1) else 0)

noncomputable def rawRotationDeriv (i : Fin 3) (F : Sphere → ℂ) (x : Sphere) : ℂ :=
  fderiv ℝ (rawRadialExtension F) (x : Ambient) (rawRotationVector i x)

private alias rawSphere_norm := Smoothness.sphere_norm

private alias rawSphere_ne_zero := Smoothness.sphere_ne

alias rawRadialExtension_sphere := Smoothness.radial_sphere

private theorem rawPuncture_open : IsOpen {x : Ambient | x ≠ 0} := isOpen_ne

alias RotationDerivatives.rawPuncture_open := rawPuncture_open

private theorem rawNormalize_smooth :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Ambient => ‖x‖⁻¹ • x) {x | x ≠ 0} := fun x hx => (((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id).contDiffWithinAt

alias RotationDerivatives.rawNormalize_smooth := rawNormalize_smooth

private theorem restrict_raw_smooth (G : Ambient → ℂ)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G {x | x ≠ 0}) :
    RawSphereSmooth (fun x : Sphere => G x) := by
  have h := hG.comp rawNormalize_smooth (fun x hx => by
    exact smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hx)) hx)
  apply h.congr
  intro x hx
  simp_all [rawRadialExtension]

alias RotationDerivatives.restrict_raw_smooth := restrict_raw_smooth

private theorem rawRotationVector_smooth (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (rawRotationVector i) := by
  unfold rawRotationVector
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff.comp
  apply contDiff_pi.mpr
  intro j
  simp only [rawRotationVector]
  split_ifs
  · fun_prop
  · fun_prop
  fun_prop

alias RotationDerivatives.rawRotationVector_smooth := rawRotationVector_smooth

private theorem rawRotationDeriv_smooth (i : Fin 3) {F : Sphere → ℂ} (hF : RawSphereSmooth F) :
    RawSphereSmooth (rawRotationDeriv i F) := by
  apply restrict_raw_smooth
    (fun x : Ambient => fderiv ℝ (rawRadialExtension F) x (rawRotationVector i x))
  exact (hF.fderiv_of_isOpen rawPuncture_open (by simp)).clm_apply
    (rawRotationVector_smooth i).contDiffOn

alias RotationDerivatives.rawRotationDeriv_smooth := rawRotationDeriv_smooth

theorem RawSphereSmooth.continuous {F : Sphere → ℂ} (hF : RawSphereSmooth F) :
    Continuous F := by
  have h : Continuous (fun x : Sphere => rawRadialExtension F x) :=
    hF.continuousOn.comp_continuous continuous_subtype_val (fun x => rawSphere_ne_zero x)
  simp_all [rawRadialExtension_sphere]

section

variable (e : Ambient ≃ₗᵢ[ℝ] Ambient)

noncomputable def rawSphereOrthogonal : Sphere ≃ₜ Sphere :=
  e.toHomeomorph.subtype (fun x => by
    simp)

@[simp] theorem rawSphereOrthogonal_coe (x : Sphere) :
    (rawSphereOrthogonal e x : Ambient) = e x := rfl

theorem rawSphereOrthogonal_measurePreserving :
    MeasurePreserving (rawSphereOrthogonal e) sphereArea sphereArea := by exact Smoothness.ortho_mp e

end

section

variable (α : ℝ) (e : Ambient ≃ₗᵢ[ℝ] Ambient)

theorem fractionalKernel_rawSphereOrthogonal
    (x y : Sphere) :
    fractionalKernel α (rawSphereOrthogonal e x) (rawSphereOrthogonal e y) =
      fractionalKernel α x y := by
  simp [fractionalKernel]

theorem fractionalIntegral_rawSphereOrthogonal
    (F : Sphere → ℂ) (x : Sphere) :
    fractionalIntegral α F (rawSphereOrthogonal e x) =
      fractionalIntegral α (fun y => F (rawSphereOrthogonal e y)) x := by apply @Smoothness.integral_ortho <;> assumption

end

section

variable (i : Fin 3) (t : ℝ)

noncomputable def rawRotationFlowMap : Ambient →ₗ[ℝ] Ambient where
  toFun x := WithLp.toLp 2 (fun j : Fin 3 =>
    if j = i then x i else if j = i + 1 then
      Real.cos t * x (i+1) - Real.sin t * x (i+2)
    else Real.sin t * x (i+1) + Real.cos t * x (i+2))
  map_add' x y := by
    ext j; simp only [PiLp.toLp_apply, PiLp.add_apply]; split_ifs <;> ring
  map_smul' c x := by
    ext j; simp only [PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem rawRotationFlowMap_inverse (x : Ambient) :
    rawRotationFlowMap i (-t) (rawRotationFlowMap i t x) = x := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.rotationFlowMap_inverse <;> assumption

theorem rawRotationFlowMap_norm (x : Ambient) :
    ‖rawRotationFlowMap i t x‖ = ‖x‖ := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.rotationFlowMap_norm <;> assumption

noncomputable def rawRotationFlow : Ambient ≃ₗᵢ[ℝ] Ambient where
  toLinearEquiv :=
    { rawRotationFlowMap i t with
      invFun := rawRotationFlowMap i (-t)
      left_inv := rawRotationFlowMap_inverse i t
      right_inv := fun x => by
        change rawRotationFlowMap i t (rawRotationFlowMap i (-t) x) = x
        simpa only [neg_neg] using rawRotationFlowMap_inverse i (-t) x }
  norm_map' := rawRotationFlowMap_norm i t

@[simp] theorem rawRotationFlow_apply (x : Ambient) :
    rawRotationFlow i t x = rawRotationFlowMap i t x := rfl

end

section

variable (i : Fin 3)

@[simp] theorem rawRotationFlow_zero (x : Ambient) : rawRotationFlow i 0 x = x := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [rawRotationFlowMap, rawRotationFlow, Fin.reduceAdd]

theorem rawRotationFlow_hasDerivAt (x : Ambient) (t : ℝ) :
    HasDerivAt (fun t => rawRotationFlow i t x) (rawRotationVector i (rawRotationFlow i t x)) t := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.rotationFlow_hasDerivAt <;> assumption

theorem rawSphereOrthogonal_rawRotationFlow_hasDerivAt {F : Sphere → ℂ}
    (hF : RawSphereSmooth F) (x : Sphere) (t : ℝ) :
    HasDerivAt (fun t => F (rawSphereOrthogonal (rawRotationFlow i t) x))
      (rawRotationDeriv i F (rawSphereOrthogonal (rawRotationFlow i t) x)) t := by
  have hn : (rawSphereOrthogonal (rawRotationFlow i t) x : Ambient) ≠ 0 := by
    intro hz
    have hs := (rawSphereOrthogonal (rawRotationFlow i t) x).property
    simp [Metric.mem_sphere, hz] at hs
  simpa [Function.comp_def, ← rawSphereOrthogonal_coe, rawRadialExtension_sphere, rawRotationDeriv] using ((((hF _ hn).contDiffAt (isOpen_ne.mem_nhds hn)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t (rawRotationFlow_hasDerivAt i (x : Ambient) t))

end

variable (α : ℝ) (hα : 0 < α) (i : Fin 3)

include hα in
theorem fractionalIntegral_rawRotationFlow_hasDerivAt
    {F : Sphere → ℂ} (hF : RawSphereSmooth F) (x : Sphere) (t : ℝ) :
    HasDerivAt (fun t => fractionalIntegral α F (rawSphereOrthogonal (rawRotationFlow i t) x))
      (fractionalIntegral α (rawRotationDeriv i F)
        (rawSphereOrthogonal (rawRotationFlow i t) x)) t := by
  let K : Sphere → ℂ := fun y => fractionalKernel α x y
  let P : ℝ → Sphere → ℂ := fun t y => K y * F (rawSphereOrthogonal (rawRotationFlow i t) y)
  let P' : ℝ → Sphere → ℂ :=
    fun t y => K y * rawRotationDeriv i F (rawSphereOrthogonal (rawRotationFlow i t) y)
  have hK := (fractionalKernel_mass α hα).2 x
  have hKi : Integrable K sphereArea := hK.1.ofReal
  letI : CompactSpace Sphere :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Ambient) 1)
  obtain ⟨C0, hC0⟩ : ∃ C : ℝ, ∀ y : Sphere, ‖F y‖ ≤ C := by
    have hbdd : BddAbove ((fun y : Sphere => ‖F y‖) '' Set.univ) :=
      isCompact_univ.bddAbove_image hF.continuous.norm.continuousOn
    exact ⟨_, fun y => le_csSup hbdd ⟨y, Set.mem_univ y, rfl⟩⟩
  obtain ⟨C1, hC1⟩ : ∃ C : ℝ, ∀ y : Sphere, ‖rawRotationDeriv i F y‖ ≤ C := by
    have hbdd : BddAbove ((fun y : Sphere => ‖rawRotationDeriv i F y‖) '' Set.univ) :=
      isCompact_univ.bddAbove_image (rawRotationDeriv_smooth i hF).continuous.norm.continuousOn
    exact ⟨_, fun y => le_csSup hbdd ⟨y, Set.mem_univ y, rfl⟩⟩
  have hmeas : ∀ t, AEStronglyMeasurable (P t) sphereArea := by
    intro t
    exact hKi.aestronglyMeasurable.mul
      (hF.continuous.comp (rawSphereOrthogonal (rawRotationFlow i t)).continuous).aestronglyMeasurable
  have hmeas' : ∀ t, AEStronglyMeasurable (P' t) sphereArea := by
    intro t
    exact hKi.aestronglyMeasurable.mul
      ((rawRotationDeriv_smooth i hF).continuous.comp
        (rawSphereOrthogonal (rawRotationFlow i t)).continuous).aestronglyMeasurable
  have hPi : Integrable (P t) sphereArea := by
    apply hKi.mul_bdd
      (hF.continuous.comp (rawSphereOrthogonal (rawRotationFlow i t)).continuous).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun y => by
      apply hC0)
  have hb : ∀ y t, ‖P' t y‖ ≤ fractionalKernel α x y * C1 := by
    intro y t
    dsimp only [P', K]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK.2.1 y)]
    exact mul_le_mul_of_nonneg_left (hC1 _) (hK.2.1 y)
  have hder : ∀ y t, HasDerivAt (fun t => P t y) (P' t y) t := by
    intro y t
    exact (rawSphereOrthogonal_rawRotationFlow_hasDerivAt i hF y t).const_mul (K y)
  have hi := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := sphereArea) (s := univ) (F := P) (F' := P')
    (bound := fun y => fractionalKernel α x y * C1)
    (x₀ := t) (Filter.univ_mem) (Filter.Eventually.of_forall hmeas) hPi (hmeas' t)
    (Filter.Eventually.of_forall (fun y x _ => hb y x)) (hK.1.mul_const _)
    (Filter.Eventually.of_forall (fun y x _ => hder y x))
  have heq (u : ℝ) : (∫ y, P u y ∂sphereArea) =
      fractionalIntegral α F (rawSphereOrthogonal (rawRotationFlow i u) x) :=
    (fractionalIntegral_rawSphereOrthogonal α (rawRotationFlow i u) F x).symm
  have heq' : (∫ y, P' t y ∂sphereArea) =
      fractionalIntegral α (rawRotationDeriv i F)
        (rawSphereOrthogonal (rawRotationFlow i t) x) :=
    (fractionalIntegral_rawSphereOrthogonal α (rawRotationFlow i t)
      (rawRotationDeriv i F) x).symm
  simpa [heq, heq'] using hi.2

include hα in
theorem fractionalIntegral_raw_rotationDeriv (F : Sphere → ℂ) (hF : RawSphereSmooth F) :
    rawRotationDeriv i (fractionalIntegral α F) =
      fractionalIntegral α (rawRotationDeriv i F) := by
  funext x
  have hf : HasFDerivAt (rawRadialExtension (fractionalIntegral α F))
      (fderiv ℝ (rawRadialExtension (fractionalIntegral α F)) (x : Ambient))
      (rawRotationFlow i 0 (x : Ambient)) := by
    simpa only [rawRotationFlow_zero] using ((((fractionalIntegral_raw_smooth α hα F hF) x (rawSphere_ne_zero x)).contDiffAt
      (rawPuncture_open.mem_nhds (rawSphere_ne_zero x))).differentiableAt (by simp)).hasFDerivAt
  have he : rawSphereOrthogonal (rawRotationFlow i 0) x = x := by
    apply Subtype.ext
    exact rawRotationFlow_zero i x
  have hd' : HasDerivAt
      (fun t => fractionalIntegral α F (rawSphereOrthogonal (rawRotationFlow i t) x))
      (rawRotationDeriv i (fractionalIntegral α F) x) 0 := by
    simpa only [Function.comp_def, ← rawSphereOrthogonal_coe, rawRadialExtension_sphere,
      he, rawRotationFlow_zero, rawRotationDeriv] using (hf.comp_hasDerivAt 0 (rawRotationFlow_hasDerivAt i (x : Ambient) 0))
  have hc := fractionalIntegral_rawRotationFlow_hasDerivAt α hα i hF x 0
  rw [he] at hc
  exact hd'.unique hc

end DedekindZetaZeroFree.ComplexFractionalInverse.RotationCalculus
