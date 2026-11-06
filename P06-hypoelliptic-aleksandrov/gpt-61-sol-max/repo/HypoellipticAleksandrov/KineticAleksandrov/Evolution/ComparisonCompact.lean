module

import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonLinear
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Comparison on compact regions

This module proves the abstract maximum argument behind
Proposition 2.1.  On a compact region `K` with an active part `D`
(on which `w` has anisotropic slice regularity and the viscous operator is signed),
a bound `w ≤ 0` on `K \ D` propagates to `K`.  Absolute coordinates are used: no
straightening of the moving boundary, hence no derivative of the boundary curve,
enters the argument.

## Main results

* `le_zero_of_strict_viscous_compact`: strictly positive operator version.
* `le_zero_of_viscous_nonneg_compact`: nonnegative operator version, proved by the
  tilt `w + δ (σ - T)`, where `T` bounds the times of the region.
-/

 public section



namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov.Parabolic Set
open scoped MatrixOrder Topology

variable {n : ℕ}

/-- Maximum principle on a compact region, strict version. -/
theorem le_zero_of_strict_viscous_compact  {B : FullKineticCoefficient n}
    {b : PDE.VectorField n} {ε : ℝ} {K D : Set (KineticPoint n)}
    {w : HypoellipticAleksandrov.KineticScalarField n} (hε : 0 ≤ ε) (hKc : IsCompact K)
    (hwc : ContinuousOn w K)
    (hfut : ∀ p ∈ D, ∀ᶠ q in 𝓝 p, p.time ≤ q.time → q ∈ K)
    (hreg : ∀ p ∈ D, IsSliceRegularAt w p)
    (hB : ∀ p ∈ D, (B p.time p.position p.velocity).PosSemidef)
    (hpos : ∀ p ∈ D, 0 < viscousTransportedOperator B b ε w p)
    (hbdry : ∀ p ∈ K, p ∉ D → w p ≤ 0) :
    ∀ p ∈ K, w p ≤ 0 := by
  intro p₀ hp₀
  by_contra hneg'

  obtain ⟨p, hpK, hpmax⟩ := hKc.exists_isMaxOn ⟨p₀, hp₀⟩ hwc

  have hpD : p ∈ D := by
    by_contra h
    exact absurd (hbdry p hpK h) (not_le.mpr (lt_of_lt_of_le (not_le.mp hneg') (hpmax hp₀)))

  exact absurd
    (viscousTransportedOperator_nonpos_of_future_localMax hε (hreg p hpD) (by
        filter_upwards [hfut p hpD] with q hq hqt using hpmax (hq hqt)) (hB p hpD))
    (not_le.mpr (hpos p hpD))

/-- The time coordinate has `L_ε (σ - T) = 1`. -/
theorem viscousTransportedOperator_time_sub  (B : FullKineticCoefficient n)
    (b : PDE.VectorField n) (ε T : ℝ) (p : KineticPoint n) :
    viscousTransportedOperator B b ε (fun q => q.time - T) p = 1 := by
  have hh : ∀ x : PDE.Vec n, sliceHessian (fun _ : PDE.Vec n => p.time - T) x = 0 := by
    intro x
    have hz : ((PDE.classicalGradient (fun _ : PDE.Vec n => p.time - T))) =
        fun _ => (0 : PDE.Vec n) := by
      funext y
      ext i
      simp [PDE.classicalGradient]
    ext i j
    simp only [sliceHessian, hz]
    simp
  have hg : kineticVelocityGradient (fun q : KineticPoint n => q.time - T) p = 0 := by
    ext i
    simp [kineticVelocityGradient, PDE.classicalGradient]
  rw [viscousTransportedOperator_apply, transportedForwardOperator_apply]
  have h1 : kineticTimeDerivative (fun q : KineticPoint n => q.time - T) p = 1 := by
    unfold kineticTimeDerivative
    simp
  have h2 : diffusedHessian (fun q : KineticPoint n => q.time - T) p = 0 := by
    rw [diffusedHessian_eq_sliceHessian]
    exact hh _
  have h3 : kineticVelocityHessian (fun q : KineticPoint n => q.time - T) p = 0 := by
    rw [kineticVelocityHessian_eq_sliceHessian]
    exact hh _
  rw [h1, h2, h3, hg]
  simp [PDE.vecDot]

/-- The time coordinate `σ - T` is slice regular everywhere. -/
theorem isSliceRegularAt_time_sub  (T : ℝ) (p : KineticPoint n) :
    IsSliceRegularAt (fun q : KineticPoint n => q.time - T) p :=
  ⟨differentiableAt_id.sub_const T,
    (show ContDiffAt ℝ 2 (fun _ : PDE.Vec n => p.time - T) p.position from contDiffAt_const),
    (show ContDiffAt ℝ 2 (fun _ : PDE.Vec n => p.time - T) p.velocity from contDiffAt_const)⟩

/-- Maximum principle on a compact region for a subsolution `L_ε w ≥ 0`. -/
theorem le_zero_of_viscous_nonneg_compact  {B : FullKineticCoefficient n}
    {b : PDE.VectorField n} {ε : ℝ} {K D : Set (KineticPoint n)}
    {w : HypoellipticAleksandrov.KineticScalarField n} {T : ℝ} (hε : 0 ≤ ε) (hKc : IsCompact K)
    (hKT : ∀ p ∈ K, p.time ≤ T) (hwc : ContinuousOn w K)
    (hfut : ∀ p ∈ D, ∀ᶠ q in 𝓝 p, p.time ≤ q.time → q ∈ K)
    (hreg : ∀ p ∈ D, IsSliceRegularAt w p)
    (hB : ∀ p ∈ D, (B p.time p.position p.velocity).PosSemidef)
    (hsub : ∀ p ∈ D, 0 ≤ viscousTransportedOperator B b ε w p)
    (hbdry : ∀ p ∈ K, p ∉ D → w p ≤ 0) :
    ∀ p ∈ K, w p ≤ 0 := by

  have hregT := isSliceRegularAt_time_sub (n := n) T

  intro p hp
  by_contra hneg'
  have hneg := not_le.mp hneg'
  have hTp  := sub_nonneg.mpr (hKT p hp)

  have := (show ∀ δ : ℝ, 0 < δ → ∀ p ∈ K, w p + δ * (p.time - T) ≤ 0 by
      intro δ hδ
      refine le_zero_of_strict_viscous_compact (B := B) (b := b) (ε := ε) (K := K) (D := D)
        (w := fun q => w q + δ * (q.time - T)) hε hKc ?_ hfut ?_ hB ?_ ?_
      · exact hwc.add ((continuous_const.mul (continuous_time.sub continuous_const)).continuousOn)
      · intro p hp
        exact (hreg p hp).add ((hregT p).const_mul δ)
      · intro p hp
        rw [viscousTransportedOperator_add (hreg p hp) ((hregT p).const_mul δ),
          viscousTransportedOperator_const_mul δ (hregT p),
          viscousTransportedOperator_time_sub]
        have := hsub p hp
        linarith
      · intro p hp hpD
        have h1 := hbdry p hp hpD
        have h2  :=
          mul_nonpos_of_nonneg_of_nonpos hδ.le (sub_nonpos.mpr (hKT p hp))
        linarith) _ (show 0 < w p / (2 * (T - p.time + 1)) by positivity) p hp
  have hden : 0 < 2 * (T - p.time + 1) := by positivity
  have hmul : w p / (2 * (T - p.time + 1)) * (p.time - T) =
      -(w p * (T - p.time) / (2 * (T - p.time + 1))) := by
    field_simp
    ring
  rw [hmul] at this
  have hfrac : w p * (T - p.time) / (2 * (T - p.time + 1)) < w p := by
    rw [div_lt_iff₀ hden]
    nlinarith
  linarith

end HypoellipticAleksandrov.KineticAleksandrov
