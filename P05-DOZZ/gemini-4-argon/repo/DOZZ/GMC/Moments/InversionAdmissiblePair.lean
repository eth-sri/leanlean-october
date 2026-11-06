/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.InversionCompatibility
public import DOZZ.Brownian.Lateral.CutoffLaw

/-! Actual compatible admissible pairs for inversion on bounded annular charts. -/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology Distributions ENNReal

namespace DOZZ.Proofs


/-- On any bounded open annular chart the transformed local field has an actual admissible
regularization compatible with the pulled source-circle regularization. -/
theorem exists_equatorGFF_inversion_admissible_pair
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    X (hX : IsEquatorGFF P X)
    Xc (hXc : IsCircleAverage P X Xc)
    U (hUopen : IsOpen U) {m R} (hm : 0 < m) (hR : 0 ≤ R)
    (hU : ∀ x ∈ U, 2 * m ≤ ‖x‖ ∧ ‖x‖ ≤ R) :
    ∃ f : (ℂ × ℝ) → ℕ → TestFn,
    ∃ hf : ∀ p n, tsupport (f p n : ℂ → ℝ) ⊆ inversionChart,
    ∃ Z : Ω → ℂ → ℝ → ℝ,
      (∀ p, Tendsto (fun n => circleEnergyGap p.1 p.2 (f p n)) atTop (𝓝 0)) ∧
      (∀ x r, MemLp (fun ω => Z ω x r) 2 P) ∧
      (∀ p, Tendsto (fun n => eLpNorm (fun ω =>
        X ω (inversionTest (f p n) (hf p n)) - Z ω p.1 p.2) 2 P) atTop (𝓝 0)) ∧
      IsAdmissibleLogRegularization P U (fun x => normPlus x ^ (-4 : ℝ)) 1
        (fun ω ε x => Xc ω x⁻¹ (Real.log (1 / ε))) ∧
      IsAdmissibleLogRegularization P U (fun x => normPlus x ^ (-4 : ℝ)) (min (m / 2) 1)
        (fun ω ε x => Z ω x (Real.log (1 / ε))) ∧
      IsCompatibleAdmissibleRegularizations P U 1 (min (m / 2) 1)
        (fun ω ε x => Xc ω x⁻¹ (Real.log (1 / ε)))
        (fun ω ε x => Z ω x (Real.log (1 / ε))) := by
  have isAdmissibleLogRegularization_on_subchart {P : Measure Ω} {U} {V} {dens : ℂ → ℝ} {ε₀ : ℝ} {Y} (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (hV : IsOpen V) (hVU : V ⊆ U) : IsAdmissibleLogRegularization P V dens ε₀ Y := by
    refine
      { measurableAtScale := hY.measurableAtScale
        openChart := hV
        densityContinuous := hY.densityContinuous.mono hVU
        densityPositive := fun x hx => hY.densityPositive x (hVU hx)
        cutoffPositive := hY.cutoffPositive
        gaussian := hY.gaussian
        covarianceBound := fun K hK hKV => hY.covarianceBound K hK (hKV.trans hVU)
        coarseVarianceBound := fun K hK hKV => hY.coarseVarianceBound K hK (hKV.trans hVU)
        coarseMixedBound := fun K hK hKV => hY.coarseMixedBound K hK (hKV.trans hVU)
        offDiagonalLimit := ?_
        fixedCoarseLimit := ?_ }
    · obtain ⟨H, hH, hb⟩ := hY.offDiagonalLimit
      exact ⟨H, hH.mono (Set.prod_mono hVU hVU), fun K hK hKV => hb K hK (hKV.trans hVU)⟩
    · obtain ⟨C, hb⟩ := hY.fixedCoarseLimit
      exact ⟨C, fun K hK hKV => hb K hK (hKV.trans hVU)⟩
  obtain ⟨f, hf, Z, hgap, hmeas, hmem, hlim, hproc, hmean, hcov⟩ :=
    exists_equatorGFF_inversion_circle_joint_version X hX
  refine ⟨f, hf, Z, hgap, hmem, hlim,
    isAdmissibleLogRegularization_on_subchart (isAdmissibleLogRegularization_complexInv P (fun x => normPlus x ^ (-4 : ℝ)) 1 (fun ω ε x => Xc ω x (Real.log (1 / ε))) (isCircleAverage_admissible P X hX Xc hXc inversionChart isOpen_compl_singleton)) hUopen (by intro x hx; change x ≠ 0; exact norm_pos_iff.mp (by linarith only [hm, (hU x hx).1])),
    isAdmissibleLogRegularization_smaller_cutoff P U _ 1 (min (m / 2) 1) _ (inversionCircle_admissible_of_geometry X hX Z hmeas hproc hmean hcov U hUopen)
      (lt_min (by positivity) one_pos) (min_le_right _ _), ?_⟩
  exact inversionCircle_compatible_of_coupled_limits X hX Xc hXc f hf Z hgap hmem hlim
    (fun x y r s => by rw [(show gaussianCovariance P (fun ω => Z ω x r) (fun ω => Z ω y s) = covariance (fun ω => Z ω x r) (fun ω => Z ω y s) P by simp only [gaussianCovariance, covariance, hmean (x, r), hmean (y, s), sub_zero]), covariance_comm]; exact hcov (y, s) (x, r)) U hm hR hU

end DOZZ.Proofs
