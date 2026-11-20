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
public import RequestProject.PolynomialTransmutation
public import RequestProject.ConormalNormalization
public import RequestProject.Reparam
public import RequestProject.PlanarNotation

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

lemma herglotzCoeff_add_density {a b : ℝ → ℂ} (ha : IsDirDensity a)
    (hb : IsDirDensity b) (k : ℝ) (m : ℤ) (z : ℂ) :
    herglotzCoeff k (a + b) m z = herglotzCoeff k a m z + herglotzCoeff k b m z := by
  unfold herglotzCoeff
  simp only [Pi.add_apply, add_mul, mul_add]
  rw [intervalIntegral.integral_add
    (intervalIntegrable_herglotz ha.intervalIntegrable k m z)
    (intervalIntegrable_herglotz hb.intervalIntegrable k m z), mul_add]

lemma herglotzCoeff_smul_density (a : ℝ → ℂ) (c : ℂ) (k : ℝ) (m : ℤ) (z : ℂ) :
    herglotzCoeff k (c • a) m z = c * herglotzCoeff k a m z := by
  unfold herglotzCoeff
  simp only [Pi.smul_apply, smul_eq_mul]
  have h : (fun φ : ℝ => Complex.exp (-((m : ℂ) * φ * Complex.I)) *
      (c * a φ * planeWave k z φ)) = fun φ : ℝ => c *
        (Complex.exp (-((m : ℂ) * φ * Complex.I)) * (a φ * planeWave k z φ)) := by
    grind
  rw [h, intervalIntegral.integral_const_mul]
  ring

lemma herglotzConormal_add_density {a b : ℝ → ℂ} (ha : IsDirDensity a)
    (hb : IsDirDensity b) (k : ℝ) (γ : ℝ → ℂ) :
    herglotzConormal k (a + b) γ = herglotzConormal k a γ + herglotzConormal k b γ := by
  funext θ
  simp
  rw [herglotzConormal_eq (IsDirDensity.intervalIntegrable (ha.add hb)),
    herglotzConormal_eq ha.intervalIntegrable, herglotzConormal_eq hb.intervalIntegrable]
  simp [herglotzCoeff_add_density ha hb]
  ring

lemma herglotzConormal_smul_density {a : ℝ → ℂ} (ha : IsDirDensity a)
    (c : ℂ) (k : ℝ) (γ : ℝ → ℂ) :
    herglotzConormal k (c • a) γ = c • herglotzConormal k a γ := by
  funext θ
  simp
  rw [herglotzConormal_eq (IsDirDensity.intervalIntegrable (ha.const_smul c)),
    herglotzConormal_eq ha.intervalIntegrable]
  simp [herglotzCoeff_smul_density, smul_eq_mul]
  ring

/-- The actual conormal trace is in `L²` of the parameter interval for every
Lipschitz curve. Neither a constant-speed nor a conformal parametrization is needed. -/
theorem memLp_herglotzConormal {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ)
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) :
    MemLp (herglotzConormal k a γ) 2 angleMeasure := by
  obtain ⟨hgm, B, hgB⟩ := herglotzConormal_bounded ha.intervalIntegrable k hK
  exact MemLp.of_bound hgm.restrict B (Eventually.of_forall hgB)

/-- The pointwise Cayley factorization of the uncorrected boundary expression.
It supplies the actual boundary expression, not merely its integral quadratic form. -/
theorem periodicA_herglotz_eq_observation {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) (hclosed : γ anglePeriod = γ 0) {E : ℝ}
    {W : TransportPath} (hW : IsTransport γ E W)
    {a : ℝ → ℂ} (ha : IsDirDensity a) {θ : ℝ} (hθ : θ ∈ angleInterval) :
    periodicA W (fun θ => herglotzWave (Real.sqrt E) a (γ θ))
        (herglotzConormal (Real.sqrt E) a γ) θ =
      observation W (vacuumWeight •
        (herglotzVec ha (Real.sqrt E) (γ 0) +
          ContinuousLinearMap.adjoint (W anglePeriod)
            (herglotzVec ha (Real.sqrt E) (γ 0)))) θ := by
  obtain ⟨hgm, B, hgB⟩ := herglotzConormal_bounded ha.intervalIntegrable (Real.sqrt E) hK
  have hy : ContinuousOn (fun s => herglotzVec ha (Real.sqrt E) (γ s)) angleInterval :=
    ((continuous_herglotzVec ha _).comp hK.continuous).continuousOn
  
  have htr := driven_trace hK hW hgm hgB hy (fun θ (_ : θ ∈ angleInterval) => herglotz_driven ha hK E θ) θ hθ
  have hadd := volterraOp_add_adj hW.1 hgm hgB hθ
  rw [(herglotzForm_eq hK hclosed hW ha).1] at hadd
  
  have hw : herglotzWave (Real.sqrt E) a (γ θ) =
      vacuumWeight * inner ℂ (basisVec 0) (herglotzVec ha (Real.sqrt E) (γ θ)) := by
    simp only [basisVec, inner_single, herglotzVec_apply, herglotzSeq, if_true,
      herglotzWave_eq]
    field_simp
  rw [periodicA, hw]
  simp only [observation, map_smul, map_add, map_sub, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, inner_smul_right, inner_add_right, inner_sub_right]
    at htr hadd ⊢
  linear_combination 2 * htr - Complex.I * hadd +
    (vacuumWeight * (inner ℂ (basisVec 0)
      ((W θ) (herglotzVec ha (Real.sqrt E) (γ 0))) -
      inner ℂ (basisVec 0) ((W θ) ((ContinuousLinearMap.adjoint (W anglePeriod))
        (herglotzVec ha (Real.sqrt E) (γ 0)))))) * Complex.I_sq

/-- Exact correction identity on genuine Herglotz conormal traces. This supplies the
form-splitting hypothesis of the abstract lower-bound argument from actual integrals. -/
theorem herglotzForm_eq_periodicP_sub_cutBE {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) (hclosed : γ anglePeriod = γ 0) {E : ℝ}
    {W : TransportPath} (hW : IsTransport γ E W)
    {a : ℝ → ℂ} (ha : IsDirDensity a) :
    herglotzForm W γ E a =
      (l2Inner (herglotzConormal (Real.sqrt E) a γ)
        (periodicP W (fun θ => herglotzWave (Real.sqrt E) a (γ θ))
          (herglotzConormal (Real.sqrt E) a γ))).re -
      (⟪observationAdj W (herglotzConormal (Real.sqrt E) a γ),
        cutBE W (observationAdj W (herglotzConormal (Real.sqrt E) a γ))⟫_ℂ).re := by
  obtain ⟨hgm, B, hgB⟩ := herglotzConormal_bounded ha.intervalIntegrable (Real.sqrt E) hK
  let v := vacuumWeight •
    (herglotzVec ha (Real.sqrt E) (γ 0) +
      ContinuousLinearMap.adjoint (W anglePeriod) (herglotzVec ha (Real.sqrt E) (γ 0)))
  let x := observationAdj W (herglotzConormal (Real.sqrt E) a γ)
  have hP : l2Inner (herglotzConormal (Real.sqrt E) a γ)
      (periodicP W (fun θ => herglotzWave (Real.sqrt E) a (γ θ))
        (herglotzConormal (Real.sqrt E) a γ)) = ⟪x, v + cutBE W x⟫_ℂ := by
    rw [inner_observationAdj hW.1 hgm hgB]
    
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    rw [uIcc_of_le Real.two_pi_pos.le] at hθ
    rw [periodicP, periodicA_herglotz_eq_observation hK hclosed hW ha hθ]
    simp [v, x, cutBE, observation, inner_add_right]
  rw [hP, inner_add_right, Complex.add_re, add_sub_cancel_right]
  exact (herglotzForm_eq hK hclosed hW ha).2

/-- The actual finite-rank correction converts a bound on the corrected form into
the requested Herglotz bound; its norm and projection estimates need no hypotheses. -/
theorem herglotzForm_lower_of_periodicP_lower {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) (hclosed : γ anglePeriod = γ 0) {E : ℝ}
    {W : TransportPath} (hW : IsTransport γ E W)
    {a : ℝ → ℂ} (ha : IsDirDensity a) {A₀ : ℝ} (hA₀ : 0 ≤ A₀)
    (hbound : -(A₀ * ‖cutProj (cutVector W)
      (observationAdj W (herglotzConormal (Real.sqrt E) a γ))‖ ^ 2) ≤
      (l2Inner (herglotzConormal (Real.sqrt E) a γ)
        (periodicP W (fun θ => herglotzWave (Real.sqrt E) a (γ θ))
          (herglotzConormal (Real.sqrt E) a γ))).re) :
    -((A₀ + ‖cutBE W‖) * ‖observationAdj W
      (herglotzConormal (Real.sqrt E) a γ)‖ ^ 2) ≤ herglotzForm W γ E a := by
  let x := observationAdj W (herglotzConormal (Real.sqrt E) a γ)
  have hproj  :=
    pow_le_pow_left₀ (norm_nonneg _)
      (norm_cutProj_apply_le (cutVector W) x) 2
  have hcorr : (⟪x, cutBE W x⟫_ℂ).re ≤ ‖cutBE W‖ * ‖x‖ ^ 2 := by
    calc (⟪x, cutBE W x⟫_ℂ).re ≤ ‖⟪x, cutBE W x⟫_ℂ‖ := Complex.re_le_norm _
      _ ≤ ‖x‖ * ‖cutBE W x‖ := norm_inner_le_norm _ _
      _ ≤ ‖x‖ * (‖cutBE W‖ * ‖x‖) := by gcongr; exact (cutBE W).le_opNorm x
      _ = ‖cutBE W‖ * ‖x‖ ^ 2 := by ring
  rw [herglotzForm_eq_periodicP_sub_cutBE hK hclosed hW ha]
  nlinarith [mul_le_mul_of_nonneg_left hproj hA₀]

section

variable (k : ℝ) (z : ℂ) (s : Finset ℕ) (c : ℕ → ℂ)
include c k s z

/-- Polynomial transmutation densities centered at the actual boundary base point.
This avoids imposing `γ 0 = 0` on the given parametrization. -/
def centeredPolyDensity : ℝ → ℂ :=
  fun φ => polyDensity k s c φ * planeWave k (-z) φ

lemma isDirDensity_centeredPolyDensity :
    IsDirDensity (centeredPolyDensity k z s c) := by
  have ha := isDirDensity_polyDensity k s c
  exact ha.of_le ((MemLp.aestronglyMeasurable ha).mul (continuous_planeWave k (-z)).aestronglyMeasurable)
    (Eventually.of_forall fun φ => by
      simp [centeredPolyDensity, norm_mul, norm_planeWave])

theorem herglotzVec_centeredPolyDensity :
    herglotzVec (isDirDensity_centeredPolyDensity k z s c) k z =
      (antiPoly s c 0 / vacuumWeight) • basisVec 0 := by
  rw [← herglotzVec_polyDensity_zero (k := k) s c]
  apply lp.ext
  funext n
  have hcoeff (m : ℤ) : herglotzCoeff k (centeredPolyDensity k z s c) m z =
      herglotzCoeff k (polyDensity k s c) m 0 := by
    exact herglotzCoeff_shift k (polyDensity k s c) m z
  simp [herglotzSeq, hcoeff]

end

end PolyaNeumann
