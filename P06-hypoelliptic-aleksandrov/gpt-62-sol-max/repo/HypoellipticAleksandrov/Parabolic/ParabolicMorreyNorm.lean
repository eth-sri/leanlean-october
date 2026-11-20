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

/-- The order-two parabolic Morrey excess in velocity dimension `d`. -/
def parabolicMorreyExponent (d : ℕ) : ℝ :=
  (d : ℝ) / ((d : ℝ) + 1)

/-- Indices of the value, time derivative, gradient and Hessian of a parabolic jet. -/
abbrev ParabolicJetIndex (d : ℕ) := Unit ⊕ Unit ⊕ Fin d ⊕ (Fin d × Fin d)

/-- The scalar component selected by a parabolic jet index. -/
def parabolicJetComponent {d : ℕ} (u : TimeVelocity d → ℝ) :
    ParabolicJetIndex d → TimeVelocity d → ℝ
  | .inl _ => u
  | .inr (.inl _) => timeDerivative u
  | .inr (.inr (.inl i)) => fun z => velocityGradient u z i
  | .inr (.inr (.inr (i, j))) => fun z => velocityHessian u z i j

lemma sum_parabolicJetComponent {d : ℕ} {A : Type*} [AddCommMonoid A]
    (N : (TimeVelocity d → ℝ) → A) (u : TimeVelocity d → ℝ) :
    (∑ k, N (parabolicJetComponent u k)) =
      N u + N (timeDerivative u) + (∑ i, N (fun z => velocityGradient u z i)) +
        ∑ i, ∑ j, N (fun z => velocityHessian u z i j) := by
  simp [ParabolicJetIndex, parabolicJetComponent, Fintype.sum_prod_type, add_assoc]

section
variable (d : ℕ) (u : TimeVelocity d → ℝ)
include d u

/-- The authoritative extended-real selected smooth-jet `L^(d + 1)` norm.

The summands occur in the fixed order: value, time derivative, all velocity
gradients, then all ordered velocity Hessians. -/
def parabolicSmoothJetELpNorm : ℝ≥0∞ :=
  parabolicELpNorm d u
    + parabolicELpNorm d (timeDerivative u)
    + ∑ i : Fin d, parabolicELpNorm d (fun z ↦ velocityGradient u z i)
    + ∑ i : Fin d, ∑ j : Fin d,
        parabolicELpNorm d (fun z ↦ velocityHessian u z i j)

/-- Componentwise finite selected smooth-jet `L^(d + 1)` membership. -/
def ParabolicSmoothJetMemLp : Prop :=
  MemLp u (parabolicExponent d) volume ∧
  MemLp (timeDerivative u) (parabolicExponent d) volume ∧
  (∀ i : Fin d, MemLp (fun z ↦ velocityGradient u z i)
    (parabolicExponent d) volume) ∧
  (∀ i j : Fin d, MemLp (fun z ↦ velocityHessian u z i j)
    (parabolicExponent d) volume)

/-- The real presentation of `parabolicSmoothJetELpNorm`.

It is quantitative only when an actual `ParabolicSmoothJetMemLp` certificate
ensures that the authoritative extended-real norm is finite. -/
def parabolicSmoothJetLpNorm : ℝ :=
  (parabolicSmoothJetELpNorm d u).toReal

end

lemma ParabolicSmoothJetMemLp.component {d : ℕ} {u : TimeVelocity d → ℝ}
    (hu : ParabolicSmoothJetMemLp d u) (k : ParabolicJetIndex d) :
    MemLp (parabolicJetComponent u k) (parabolicExponent d) volume := by
  rcases k with (_ | (_ | (i | ⟨i, j⟩)))
  exacts [hu.1, hu.2.1, hu.2.2.1 i, hu.2.2.2 i j]

lemma parabolicSmoothJetELpNorm_eq_sum {d : ℕ} (u : TimeVelocity d → ℝ) :
    parabolicSmoothJetELpNorm d u = ∑ k, parabolicELpNorm d (parabolicJetComponent u k) :=
  (sum_parabolicJetComponent (parabolicELpNorm d) u).symm

section
variable {d : ℕ} {u : TimeVelocity d → ℝ}

lemma parabolicSmoothJetLpNorm_eq_components
    (hu : ParabolicSmoothJetMemLp d u) :
    parabolicSmoothJetLpNorm d u =
      parabolicLpNorm d u + parabolicLpNorm d (timeDerivative u) +
        (∑ i, parabolicLpNorm d (fun z => velocityGradient u z i)) +
        ∑ i, ∑ j, parabolicLpNorm d (fun z => velocityHessian u z i j) := by
  rw [parabolicSmoothJetLpNorm, parabolicSmoothJetELpNorm_eq_sum,
    ENNReal.toReal_sum (fun k _ => show parabolicELpNorm d (parabolicJetComponent u k) ≠ ⊤ from (hu.component k).eLpNorm_ne_top)]
  exact sum_parabolicJetComponent (parabolicLpNorm d) u

/-- Componentwise finite selected-jet membership makes the extended norm finite. -/
theorem parabolicSmoothJetELpNorm_ne_top
    (hu : ParabolicSmoothJetMemLp d u) : parabolicSmoothJetELpNorm d u ≠ ⊤ := by
  rw [parabolicSmoothJetELpNorm_eq_sum]
  exact ENNReal.sum_ne_top.mpr fun k _ => (hu.component k).eLpNorm_ne_top

/-- A compactly supported `C²` function has finite selected smooth-jet
`L^(d + 1)` norms, including every ordered velocity Hessian component. -/
theorem parabolicSmoothJetMemLp_of_contDiff_hasCompactSupport (hu : ContDiff ℝ 2 u)
    (huc : HasCompactSupport u) : ParabolicSmoothJetMemLp d u := by
  have h₁ := hu.continuous_fderiv (by norm_num)
  have h₂ := (hu.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  refine ⟨hu.continuous.memLp_of_hasCompactSupport huc,
    (h₁.clm_apply continuous_const).memLp_of_hasCompactSupport (timeDerivative_compact huc),
    fun i => (h₁.clm_apply continuous_const).memLp_of_hasCompactSupport
      (velocityGradient_compact (i := i) huc),
    fun i j => ((h₂.clm_apply continuous_const).clm_apply continuous_const).memLp_of_hasCompactSupport
      (velocityHessian_compact (i := i) (j := j) huc)⟩

end

/-- The velocity gradient of a scalar pullback has the exact first-order
parabolic scaling factor. -/
theorem velocityGradient_pullbackScalar {d : ℕ} {q : TimeVelocity d → ℝ}
    {z : TimeVelocity d} {t₀ r : ℝ} {v₀ : PDE.Vec d}
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
