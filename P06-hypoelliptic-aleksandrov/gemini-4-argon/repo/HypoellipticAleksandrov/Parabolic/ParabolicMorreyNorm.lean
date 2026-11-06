module

public import HypoellipticAleksandrov.Parabolic.Derivatives
public import HypoellipticAleksandrov.Parabolic.ScalingMeasure
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Selected parabolic smooth-jet norms

This module defines the selected smooth-jet `L^(d + 1)` norm used by the
parabolic Morrey program.  Its authoritative form is an `ENNReal` sum of the
value, time derivative, all velocity-gradient components, and all ordered
velocity-Hessian components.

## Main definitions

* `parabolicMorreyExponent` is the dimension-dependent excess
  `d / (d + 1)`.
* `parabolicSmoothJetELpNorm` is the authoritative extended-real selected-jet
  norm.
* `ParabolicSmoothJetMemLp` records componentwise finite `L^(d + 1)` norms.

## Main results

* Compactly supported `C²` functions satisfy `ParabolicSmoothJetMemLp`.
* `velocityGradient_pullbackScalar` gives the exact first-velocity scaling.

The module proves no Morrey, Poincare, Campanato, weak-jet, representative,
or PDE result.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped ENNReal

/- The order-two parabolic Morrey excess in velocity dimension `d`. -/
def parabolicMorreyExponent (d : ℕ) : ℝ :=
  (d : ℝ) / ((d : ℝ) + 1)

/- The authoritative extended-real selected smooth-jet `L^(d + 1)` norm.

The summands occur in the fixed order: value, time derivative, all velocity
gradients, then all ordered velocity Hessians. -/
def parabolicSmoothJetELpNorm (d ) (u : TimeVelocity d → ℝ) : ℝ≥0∞ :=
  parabolicELpNorm d u
    + parabolicELpNorm d (timeDerivative u)
    + ∑ i : Fin d, parabolicELpNorm d (fun z ↦ velocityGradient u z i)
    + ∑ i : Fin d, ∑ j : Fin d,
        parabolicELpNorm d (fun z ↦ velocityHessian u z i j)

/- Componentwise finite selected smooth-jet `L^(d + 1)` membership. -/
def ParabolicSmoothJetMemLp (d ) (u : TimeVelocity d → ℝ) : Prop :=
  MemLp u (parabolicExponent d) volume ∧
  MemLp (timeDerivative u) (parabolicExponent d) volume ∧
  (∀ i : Fin d, MemLp (fun z ↦ velocityGradient u z i)
    (parabolicExponent d) volume) ∧
  (∀ i j : Fin d, MemLp (fun z ↦ velocityHessian u z i j)
    (parabolicExponent d) volume)

/- The real presentation of `parabolicSmoothJetELpNorm`.

It is quantitative only when an actual `ParabolicSmoothJetMemLp` certificate
ensures that the authoritative extended-real norm is finite. -/
def parabolicSmoothJetLpNorm (d ) (u : TimeVelocity d → ℝ) : ℝ :=
  (parabolicSmoothJetELpNorm d u).toReal

private theorem timeDerivative_hasCompactSupport {d } {u : TimeVelocity d → ℝ}
    (hu : HasCompactSupport u) : HasCompactSupport (timeDerivative u) := by
  unfold timeDerivative
  simpa using hu.fderiv_apply (𝕜 := ℝ) ((1, 0) : TimeVelocity d)

private theorem velocityGradient_hasCompactSupport {d u}
    {i : Fin d} (hu : HasCompactSupport u) :
    HasCompactSupport (fun z ↦ velocityGradient u z i) := by
  unfold velocityGradient
  simpa using hu.fderiv_apply (𝕜 := ℝ) ((0, Pi.single i 1) : TimeVelocity d)

theorem parabolicSmoothJetELpNorm_ne_top {d u}
    (hu : ParabolicSmoothJetMemLp d u) : parabolicSmoothJetELpNorm d u ≠ ⊤ := by
  unfold parabolicSmoothJetELpNorm
  apply ENNReal.add_ne_top.mpr
  constructor
  · apply ENNReal.add_ne_top.mpr
    constructor
    · exact ENNReal.add_ne_top.mpr ⟨hu.1.eLpNorm_ne_top, hu.2.1.eLpNorm_ne_top⟩
    · exact ENNReal.sum_ne_top.mpr fun i _ ↦ (hu.2.2.1 i).eLpNorm_ne_top
  · apply ENNReal.sum_ne_top.mpr
    intro i _
    exact ENNReal.sum_ne_top.mpr fun j _ ↦ (hu.2.2.2 i j).eLpNorm_ne_top

/- A compactly supported `C²` function has finite selected smooth-jet
`L^(d + 1)` norms, including every ordered velocity Hessian component. -/
theorem parabolicSmoothJetMemLp_of_contDiff_hasCompactSupport
    {d u} (hu : ContDiff ℝ 2 u)
    (huc : HasCompactSupport u) : ParabolicSmoothJetMemLp d u := by
  have _h_inl_14 : Continuous (timeDerivative u) := by
    unfold timeDerivative
    exact ((hu.contDiff_fderiv_apply (m := 0) (by norm_num)).comp
      (contDiff_id.prodMk contDiff_const)).continuous
  refine ⟨hu.continuous.memLp_of_hasCompactSupport huc,
    _h_inl_14.memLp_of_hasCompactSupport
      (timeDerivative_hasCompactSupport huc), ?_, ?_⟩
  · intro i
    have _h_inl_16 : Continuous (fun z ↦ velocityGradient u z i) := by
      unfold velocityGradient
      exact ((hu.contDiff_fderiv_apply (m := 0) (by norm_num)).comp
        (contDiff_id.prodMk contDiff_const)).continuous
    exact _h_inl_16.memLp_of_hasCompactSupport
      (velocityGradient_hasCompactSupport huc)
  · intro i j
    have _h_inl_18 : Continuous (fun z ↦ velocityHessian u z i j) := by
      unfold velocityHessian
      have hfirst :=
        hu.fderiv_right (m := 1) (by norm_num)
      simpa using (hfirst.continuous_fderiv (by norm_num)).clm_apply continuous_const |>.clm_apply
        continuous_const
    have _h_inl_17 : HasCompactSupport (fun z ↦ velocityHessian u z i j) := by
      unfold velocityHessian
      have hfirst := huc.fderiv ℝ
      simpa only [Function.comp_def] using (hfirst.fderiv ℝ).comp_left
        (g := fun H : TimeVelocity d →L[ℝ] TimeVelocity d →L[ℝ] ℝ ↦
          H ((0, Pi.single i 1) : TimeVelocity d) ((0, Pi.single j 1) : TimeVelocity d)) rfl
    exact _h_inl_18.memLp_of_hasCompactSupport
      _h_inl_17

/- The velocity gradient of a scalar pullback has the exact first-order
parabolic scaling factor. -/
theorem velocityGradient_pullbackScalar {d q z t₀ r} {v₀ : PDE.Vec d}
    (hq : ContDiffAt ℝ 1 q (parabolicAffine t₀ v₀ r z)) :
    velocityGradient (pullbackScalar q t₀ v₀ r) z =
      r • velocityGradient q (parabolicAffine t₀ v₀ r z) := by
  ext i
  unfold velocityGradient
  rw [show fderiv ℝ (pullbackScalar q t₀ v₀ r) z =
      (fderiv ℝ q (parabolicAffine t₀ v₀ r z)).comp (parabolicLinear (d := d) r) by
    exact (hq.differentiableAt (by norm_num)).hasFDerivAt.comp z
      (hasFDerivAt_parabolicAffine t₀ v₀ r z) |>.fderiv]
  simp only [ContinuousLinearMap.comp_apply, parabolicLinear_apply]
  simpa [smul_eq_mul] using
    (fderiv ℝ q (parabolicAffine t₀ v₀ r z)).map_smul r
      ((0 : ℝ), Pi.single i (1 : ℝ))

end HypoellipticAleksandrov.Parabolic
