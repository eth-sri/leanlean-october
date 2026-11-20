module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import RequestProject.SmallEnergyForm
public import RequestProject.ObservationDual
public import RequestProject.BoundaryChart
public import RequestProject.ArcLength
public import RequestProject.SmoothDomain
public import RequestProject.ReconChordArc
public import RequestProject.ReducedForm
public import RequestProject.KernelIdentity
public import RequestProject.HerglotzForm
public import RequestProject.PeriodicForm
public import RequestProject.ConormalNormalization
public import RequestProject.Reparam

/-!
# Concrete Herglotz inputs for the normalized boundary reduction

The chart reduction acts on `L2Z`, whereas the eventual boundary bound is stated on
direction densities. We construct the normalized Fourier coordinates of the actual
Herglotz conormal trace and identify their projected observation. The construction uses
the given constant-speed parametrization; it makes no conformal-coordinate assumption.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Topology
open scoped Real ComplexConjugate InnerProductSpace

lemma herglotzConormal_add_density {a b : ℝ → ℂ} (ha : IsDirDensity a)
    (hb : IsDirDensity b) (k : ℝ) (γ : ℝ → ℂ) :
    herglotzConormal k (a + b) γ = herglotzConormal k a γ + herglotzConormal k b γ := by
  funext θ
  simp  [Pi.add_apply]
  rw [herglotzConormal_eq (IsDirDensity.intervalIntegrable (ha.add hb)),
    herglotzConormal_eq ha.intervalIntegrable, herglotzConormal_eq hb.intervalIntegrable]
  simp  [herglotzCoeff_add_density ha hb]
  ring

lemma herglotzConormal_smul_density {a : ℝ → ℂ} (ha : IsDirDensity a)
    (c : ℂ) (k : ℝ) (γ : ℝ → ℂ) :
    herglotzConormal k (c • a) γ = c • herglotzConormal k a γ := by
  funext θ
  simp  [Pi.smul_apply]
  rw [herglotzConormal_eq (IsDirDensity.intervalIntegrable (ha.const_smul c)),
    herglotzConormal_eq ha.intervalIntegrable]
  simp only [herglotzCoeff_smul_density]
  ring

/-- The actual conormal trace is in `L²` of the parameter interval for every
Lipschitz curve. Neither a constant-speed nor a conformal parametrization is needed. -/
theorem memLp_herglotzConormal {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ)
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) :
    MemLp (herglotzConormal k a γ) 2 (volume.restrict (Ioc 0 (2 * π))) := by
  obtain ⟨hgm, B, hgB⟩ := herglotzConormal_bounded ha.intervalIntegrable k hK
  exact MemLp.of_bound hgm.restrict B (Eventually.of_forall hgB)






/-- Exact correction identity on genuine Herglotz conormal traces. This supplies the
form-splitting hypothesis of the abstract lower-bound argument from actual integrals. -/
theorem herglotzForm_eq_periodicP_sub_cutBE {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) (hclosed : γ (2 * π) = γ 0) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    {a : ℝ → ℂ} (ha : IsDirDensity a) :
    herglotzForm W γ E a =
      (l2Inner (herglotzConormal (Real.sqrt E) a γ)
        (periodicP W (fun θ => herglotzWave (Real.sqrt E) a (γ θ))
          (herglotzConormal (Real.sqrt E) a γ))).re -
      (⟪observationAdj W (herglotzConormal (Real.sqrt E) a γ),
        cutBE W (observationAdj W (herglotzConormal (Real.sqrt E) a γ))⟫_ℂ).re := by
  let v := (Real.sqrt 2 : ℂ) •
    (herglotzVec ha (Real.sqrt E) (γ 0) +
      ContinuousLinearMap.adjoint (W (2 * π)) (herglotzVec ha (Real.sqrt E) (γ 0)))
  let x := observationAdj W (herglotzConormal (Real.sqrt E) a γ)
  have hP : l2Inner (herglotzConormal (Real.sqrt E) a γ)
      (periodicP W (fun θ => herglotzWave (Real.sqrt E) a (γ θ))
        (herglotzConormal (Real.sqrt E) a γ)) = ⟪x, v + cutBE W x⟫_ℂ := by
    rw [inner_observationAdj hW.1 (intervalIntegrable_herglotzConormal ha.intervalIntegrable _ hK _ _)]
    unfold l2Inner
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    rw [uIcc_of_le Real.two_pi_pos.le] at hθ
    rw [periodicP, (herglotz_cayley_factorization hK hclosed hW ha).2 hθ]
    simp only [v, x, cutBE, observation, map_add, inner_add_right]
  rw [hP, inner_add_right, Complex.add_re, add_sub_cancel_right]
  exact (herglotzForm_eq hK hclosed hW ha).2

/-- The actual finite-rank correction converts a bound on the corrected form into
the requested Herglotz bound; its norm and projection estimates need no hypotheses. -/
theorem herglotzForm_lower_of_periodicP_lower {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) (hclosed : γ (2 * π) = γ 0) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    {a : ℝ → ℂ} (ha : IsDirDensity a) {A₀ : ℝ} (hA₀ : 0 ≤ A₀)
    (hbound : -(A₀ * ‖cutProj (cutC (W (2 * π)) (basisVec 0))
      (observationAdj W (herglotzConormal (Real.sqrt E) a γ))‖ ^ 2) ≤
      (l2Inner (herglotzConormal (Real.sqrt E) a γ)
        (periodicP W (fun θ => herglotzWave (Real.sqrt E) a (γ θ))
          (herglotzConormal (Real.sqrt E) a γ))).re) :
    -((A₀ + ‖cutBE W‖) * ‖observationAdj W
      (herglotzConormal (Real.sqrt E) a γ)‖ ^ 2) ≤ herglotzForm W γ E a := by
  let x := observationAdj W (herglotzConormal (Real.sqrt E) a γ)
  have hproj :=
    pow_le_pow_left₀ (norm_nonneg _)
      (norm_cutProj_apply_le (cutC (W (2 * π)) (basisVec 0)) x) 2
  have hcorr : (⟪x, cutBE W x⟫_ℂ).re ≤ ‖cutBE W‖ * ‖x‖ ^ 2 := by
    calc (⟪x, cutBE W x⟫_ℂ).re ≤ ‖⟪x, cutBE W x⟫_ℂ‖ := Complex.re_le_norm _
      _ ≤ ‖x‖ * ‖cutBE W x‖ := norm_inner_le_norm _ _
      _ ≤ ‖x‖ * (‖cutBE W‖ * ‖x‖) := by gcongr; exact (cutBE W).le_opNorm x
      _ = ‖cutBE W‖ * ‖x‖ ^ 2 := by ring
  rw [herglotzForm_eq_periodicP_sub_cutBE hK hclosed hW ha]
  change -(A₀ * ‖cutProj (cutC (W (2 * π)) (basisVec 0)) x‖ ^ 2) ≤ _ at hbound
  change -((A₀ + ‖cutBE W‖) * ‖x‖ ^ 2) ≤ _ - (⟪x, cutBE W x⟫_ℂ).re
  nlinarith [mul_le_mul_of_nonneg_left hproj hA₀]




end PolyaNeumann
