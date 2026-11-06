module

public import HypoellipticAleksandrov.Parabolic.Derivatives
public import HypoellipticAleksandrov.Parabolic.ScalingMeasure
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import HypoellipticAleksandrov.Parabolic.ContactMap
import all HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra
import all HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
import all HypoellipticAleksandrov.Parabolic.WeakJetProduct

open private HypoellipticAleksandrov.Parabolic.velocityHessian_compact from HypoellipticAleksandrov.Parabolic.WeakJetProduct
open private HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_hasCompactSupport from HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
open private HypoellipticAleksandrov.Parabolic.timeDerivative_compact from HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra


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

variable (d : ℕ)

/-- The order-two parabolic Morrey excess in velocity dimension `d`. -/
def parabolicMorreyExponent  : ℝ :=
  (d : ℝ) / ((d : ℝ) + 1)

variable (u : HypoellipticAleksandrov.Parabolic.ScalarField d)

/-- The authoritative extended-real selected smooth-jet `L^(d + 1)` norm.

The summands occur in the fixed order: value, time derivative, all velocity
gradients, then all ordered velocity Hessians. -/
def parabolicSmoothJetELpNorm   : ℝ≥0∞ :=
  parabolicELpNorm d u
    + parabolicELpNorm d (timeDerivative u)
    + ∑ i : Fin d, parabolicELpNorm d (fun z ↦ velocityGradient u z i)
    + ∑ i : Fin d, ∑ j : Fin d,
        parabolicELpNorm d (fun z ↦ velocityHessian u z i j)

/-- Componentwise finite selected smooth-jet `L^(d + 1)` membership. -/
def ParabolicSmoothJetMemLp   : Prop :=
  MemLp u (parabolicExponent d)  ∧
  MemLp (timeDerivative u) (parabolicExponent d)  ∧
  (∀ i : Fin d, MemLp (fun z ↦ velocityGradient u z i)
    (parabolicExponent d) ) ∧
  (∀ i j : Fin d, MemLp (fun z ↦ velocityHessian u z i j)
    (parabolicExponent d) )

/-- The real presentation of `parabolicSmoothJetELpNorm`.

It is quantitative only when an actual `ParabolicSmoothJetMemLp` certificate
ensures that the authoritative extended-real norm is finite. -/
def parabolicSmoothJetLpNorm   : ℝ :=
  (parabolicSmoothJetELpNorm d u).toReal

variable {d : ℕ}

variable {u : HypoellipticAleksandrov.Parabolic.ScalarField d}

private theorem timeDerivative_continuous
    (hu : ContDiff ℝ 2 u) : Continuous (timeDerivative u) := (continuous_timeDerivative hu)




variable {i : Fin d}

private theorem velocityGradient_continuous
     (hu : ContDiff ℝ 2 u) :
    Continuous (fun z ↦ velocityGradient u z i) := by
  unfold velocityGradient
  exact ((hu.contDiff_fderiv_apply (m := 0) (by norm_num)).comp
    (contDiff_id.prodMk contDiff_const)).continuous



variable {i j : Fin d}

private theorem velocityHessian_continuous
     (hu : ContDiff ℝ 2 u) :
    Continuous (fun z ↦ velocityHessian u z i j) := by
  unfold velocityHessian

  simpa using ((hu.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).clm_apply continuous_const |>.clm_apply
    continuous_const




/-- Componentwise finite selected-jet membership makes the extended norm finite. -/
theorem parabolicSmoothJetELpNorm_ne_top
    (hu : ParabolicSmoothJetMemLp d u) : parabolicSmoothJetELpNorm d u ≠ ⊤ := (id
  (ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr
        ⟨ENNReal.add_ne_top.mpr ⟨MemLp.eLpNorm_ne_top hu.left, MemLp.eLpNorm_ne_top hu.right.left⟩,
          ENNReal.sum_ne_top.mpr fun i x => MemLp.eLpNorm_ne_top (hu.right.right.left i)⟩,
      ENNReal.sum_ne_top.mpr fun i a =>
        ENNReal.sum_ne_top.mpr fun j x => MemLp.eLpNorm_ne_top (hu.right.right.right i j)⟩))

/-- A compactly supported `C²` function has finite selected smooth-jet
`L^(d + 1)` norms, including every ordered velocity Hessian component. -/
theorem parabolicSmoothJetMemLp_of_contDiff_hasCompactSupport
      (hu : ContDiff ℝ 2 u)
    (huc : HasCompactSupport u) : ParabolicSmoothJetMemLp d u := by
  refine ⟨hu.continuous.memLp_of_hasCompactSupport huc,
    (timeDerivative_continuous hu).memLp_of_hasCompactSupport
      (_root_.HypoellipticAleksandrov.Parabolic.timeDerivative_compact huc), ?_, ?_⟩
  · intro i
    exact (velocityGradient_continuous hu).memLp_of_hasCompactSupport
      (_root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_hasCompactSupport huc)
  · intro i j
    exact (velocityHessian_continuous hu).memLp_of_hasCompactSupport
      (_root_.HypoellipticAleksandrov.Parabolic.velocityHessian_compact huc)

/-- The velocity gradient of a scalar pullback has the exact first-order
parabolic scaling factor. -/
theorem velocityGradient_pullbackScalar  {q : HypoellipticAleksandrov.Parabolic.ScalarField d}
    {z : TimeVelocity d} {t₀ r : ℝ} {v₀ : PDE.Vec d}
    (hq : ContDiffAt ℝ 1 q (parabolicAffine t₀ v₀ r z)) :
    velocityGradient (pullbackScalar q t₀ v₀ r) z =
      r • velocityGradient q (parabolicAffine t₀ v₀ r z) := by
  let sharedTerm_9f995f9e78 := ((fderiv ℝ q (parabolicAffine t₀ v₀ r z)))
  ext i
  unfold velocityGradient
  rw [show fderiv ℝ (pullbackScalar q t₀ v₀ r) z =
      sharedTerm_9f995f9e78.comp (parabolicLinear  r) from (hq.differentiableAt (by norm_num)).hasFDerivAt.comp z
      (hasFDerivAt_parabolicAffine t₀ v₀ r z) |>.fderiv]
  simp only [ContinuousLinearMap.comp_apply, parabolicLinear_apply]
  simpa [smul_eq_mul] using
    sharedTerm_9f995f9e78.map_smul r
      ((0 ), Pi.single i (1 ))

end HypoellipticAleksandrov.Parabolic
