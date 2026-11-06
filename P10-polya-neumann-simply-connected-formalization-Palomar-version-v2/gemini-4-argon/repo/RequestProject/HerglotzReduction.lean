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

variable {a : ℝ → ℂ}

lemma herglotzCoeff_smul_density a c k m z :
    herglotzCoeff k (c • a) m z = c * herglotzCoeff k a m z := by
  unfold herglotzCoeff
  simp
  rw [show (fun φ : ℝ => Complex.exp (-(m * φ * Complex.I)) * (c * a φ * planeWave k z φ)) = fun φ : ℝ => c * (Complex.exp (-((m : ℂ) * φ * Complex.I)) * (a φ * planeWave k z φ)) by
    funext φ; ring, intervalIntegral.integral_const_mul]
  ring

lemma herglotzConormal_add_density  (ha : IsDirDensity a)
    (hb : IsDirDensity b) k γ :
    herglotzConormal k (a + b) γ = herglotzConormal k a γ + herglotzConormal k b γ := by
  funext θ
  simp
  rw [herglotzConormal_eq (IsDirDensity.intervalIntegrable (ha.add hb)),
    herglotzConormal_eq ha.intervalIntegrable, herglotzConormal_eq hb.intervalIntegrable]
  have h_inl k m z : herglotzCoeff k (a + b) m z = herglotzCoeff k a m z + herglotzCoeff k b m z := by
    unfold herglotzCoeff
    simp [add_mul, mul_add]
    rw [intervalIntegral.integral_add
      (intervalIntegrable_herglotz ha.intervalIntegrable k m z)
      (intervalIntegrable_herglotz hb.intervalIntegrable k m z), mul_add]
  simp [h_inl]
  ring

lemma herglotzConormal_smul_density  (ha : IsDirDensity a)
    (c : ℂ) k γ :
    herglotzConormal k (c • a) γ = c • herglotzConormal k a γ := by
  funext θ
  simp
  rw [herglotzConormal_eq (IsDirDensity.intervalIntegrable (ha.const_smul c)),
    herglotzConormal_eq ha.intervalIntegrable]
  simp [herglotzCoeff_smul_density]
  ring

/-- The actual conormal trace is in `L²` of the parameter interval for every
Lipschitz curve. Neither a constant-speed nor a conformal parametrization is needed. -/
theorem memLp_herglotzConormal  (ha : IsDirDensity a) k
      (hK : LipschitzWith K γ) :
    MemLp (herglotzConormal k a γ) 2 (volume.restrict (Ioc 0 (2 * π))) := by
  obtain ⟨hgm, B, hgB⟩ := herglotzConormal_bounded ha.intervalIntegrable k hK
  exact MemLp.of_bound hgm.restrict B (Eventually.of_forall hgB)












/-- The pointwise Cayley factorization of the uncorrected boundary expression.
It supplies the actual boundary expression, not merely its integral quadratic form. -/
theorem periodicA_herglotz_eq_observation {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) (hclosed : γ (2 * π) = γ 0) 
     (hW : IsTransport γ E W)
     (ha : IsDirDensity a)  (hθ : θ ∈ Icc 0 (2 * π)) :
    periodicA W (fun θ => herglotzWave (Real.sqrt E) a (γ θ))
        (herglotzConormal (Real.sqrt E) a γ) θ =
      observation W ((Real.sqrt 2 : ℂ) •
        (herglotzVec ha (Real.sqrt E) (γ 0) +
          ContinuousLinearMap.adjoint (W (2 * π))
            (herglotzVec ha (Real.sqrt E) (γ 0)))) θ := by
  obtain ⟨hgm, B, hgB⟩ := herglotzConormal_bounded ha.intervalIntegrable (Real.sqrt E) hK
  have hy : ContinuousOn (fun s => herglotzVec ha (Real.sqrt E) (γ s)) (Icc 0 (2 * π)) :=
    ((continuous_herglotzVec ha _).comp hK.continuous).continuousOn
  have ey := fun θ (_ : θ ∈ Icc 0 (2 * π)) => herglotz_driven ha hK E θ
  have htr := driven_trace hK hW hgm hgB hy ey θ hθ
  have hadd := volterraOp_add_adj hW.1 hgm hgB hθ
  rw [(herglotzForm_eq hK hclosed hW ha).1] at hadd
  have hr : Real.sqrt 2 ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hw : herglotzWave (Real.sqrt E) a (γ θ) =
      Real.sqrt 2 * inner ℂ (basisVec 0) (herglotzVec ha (Real.sqrt E) (γ θ)) := by
    simp [basisVec, inner_single, herglotzSeq, herglotzWave_eq]
    field_simp
  rw [periodicA, hw]
  simp only [observation, map_smul, map_add, map_sub, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, inner_smul_right, inner_add_right, inner_sub_right]
    at htr hadd ⊢
  linear_combination 2 * htr - Complex.I * hadd +
    ((Real.sqrt 2) * (inner ℂ (basisVec 0)
      ((W θ) (herglotzVec ha (Real.sqrt E) (γ 0))) -
      inner ℂ (basisVec 0) ((W θ) ((ContinuousLinearMap.adjoint (W (2 * π)))
        (herglotzVec ha (Real.sqrt E) (γ 0)))))) * Complex.I_sq

/-- The actual finite-rank correction converts a bound on the corrected form into
the requested Herglotz bound; its norm and projection estimates need no hypotheses. -/
theorem herglotzForm_lower_of_periodicP_lower  
    (hK : LipschitzWith K γ) (hclosed : γ (2 * π) = γ 0) 
     (hW : IsTransport γ E W)
     (ha : IsDirDensity a)  (hA₀ : 0 ≤ A₀)
    (hbound : -(A₀ * ‖cutProj (cutC (W (2 * π)) (basisVec 0))
      (observationAdj W (herglotzConormal (Real.sqrt E) a γ))‖ ^ 2) ≤
      (l2Inner (herglotzConormal (Real.sqrt E) a γ)
        (periodicP W (fun θ => herglotzWave (Real.sqrt E) a (γ θ))
          (herglotzConormal (Real.sqrt E) a γ))).re) :
    -((A₀ + ‖cutBE W‖) * ‖observationAdj W
      (herglotzConormal (Real.sqrt E) a γ)‖ ^ 2) ≤ herglotzForm W γ E a := by
  let x := observationAdj W (herglotzConormal (Real.sqrt E) a γ)
  have hcorr : (⟪x, cutBE W x⟫_ℂ).re ≤ ‖cutBE W‖ * ‖x‖ ^ 2 := by
    calc _ ≤ _ := Complex.re_le_norm _
      _ ≤ _ := norm_inner_le_norm _ _
      _ ≤ ‖x‖ * (‖cutBE W‖ * ‖x‖) := by gcongr; exact (cutBE W).le_opNorm x
      _ = ‖cutBE W‖ * ‖x‖ ^ 2 := by ring
  rw [show herglotzForm W γ E a = (l2Inner (herglotzConormal (Real.sqrt E) a γ) (periodicP W (fun θ => herglotzWave (Real.sqrt E) a (γ θ)) (herglotzConormal (Real.sqrt E) a γ))).re - (⟪observationAdj W (herglotzConormal (Real.sqrt E) a γ), cutBE W (observationAdj W (herglotzConormal (Real.sqrt E) a γ))⟫_ℂ).re by
    obtain ⟨hgm, B, hgB⟩ := herglotzConormal_bounded ha.intervalIntegrable (Real.sqrt E) hK
    let v := (Real.sqrt 2 : ℂ) •
      (herglotzVec ha (Real.sqrt E) (γ 0) +
        ContinuousLinearMap.adjoint (W (2 * π)) (herglotzVec ha (Real.sqrt E) (γ 0)))
    let x := observationAdj W (herglotzConormal (Real.sqrt E) a γ)
    rw [(show l2Inner (herglotzConormal (Real.sqrt E) a γ) (periodicP W (fun θ => herglotzWave (Real.sqrt E) a (γ θ)) (herglotzConormal (Real.sqrt E) a γ)) = ⟪x, v + cutBE W x⟫_ℂ by
      rw [inner_observationAdj hW.1 hgm hgB]
      unfold l2Inner
      refine intervalIntegral.integral_congr fun θ hθ => ?_
      rw [uIcc_of_le Real.two_pi_pos.le] at hθ
      rw [periodicP, periodicA_herglotz_eq_observation hK hclosed hW ha hθ]
      simp only [v, x, cutBE, observation, map_add, inner_add_right]), inner_add_right, Complex.add_re, add_sub_cancel_right]
    exact (herglotzForm_eq hK hclosed hW ha).2]
  change -(A₀ * ‖cutProj (cutC (W (2 * π)) (basisVec 0)) x‖ ^ 2) ≤ _ at hbound
  change -((A₀ + ‖cutBE W‖) * ‖x‖ ^ 2) ≤ _
  nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_cutProj_apply_le (cutC (W (2 * π)) (basisVec 0)) x) 2) hA₀]

/-- Polynomial transmutation densities centered at the actual boundary base point.
This avoids imposing `γ 0 = 0` on the given parametrization. -/
def centeredPolyDensity (k : ℝ) (z : ℂ) (s : Finset ℕ) (c : ℕ → ℂ) : ℝ → ℂ :=
  fun φ => polyDensity k s c φ * planeWave k (-z) φ

lemma isDirDensity_centeredPolyDensity k z s c :
    IsDirDensity (centeredPolyDensity k z s c) := by
  have ha := isDirDensity_polyDensity k s c
  exact ha.of_le ((MemLp.aestronglyMeasurable ha).mul (continuous_planeWave k (-z)).aestronglyMeasurable)
    (Eventually.of_forall fun φ => by
      rw [centeredPolyDensity, norm_mul, norm_planeWave, mul_one])

theorem herglotzVec_centeredPolyDensity k z s c :
    herglotzVec (isDirDensity_centeredPolyDensity k z s c) k z =
      (antiPoly s c 0 / (Real.sqrt 2 : ℂ)) • basisVec 0 := by
  rw [← herglotzVec_polyDensity_zero (k := k) s c]
  apply lp.ext
  funext n
  have hcoeff m : herglotzCoeff k (centeredPolyDensity k z s c) m z =
      herglotzCoeff k (polyDensity k s c) m 0 := by
    exact herglotzCoeff_shift k (polyDensity k s c) m z
  simp [herglotzSeq, hcoeff]

end PolyaNeumann
