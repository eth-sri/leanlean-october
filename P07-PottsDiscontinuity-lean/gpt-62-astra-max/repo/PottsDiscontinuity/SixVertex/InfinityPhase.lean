module

public import Mathlib
public import PottsDiscontinuity.SixVertex.InfinitySlater

/-! # Exact phase of the centered Slater determinant -/

@[expose] public section

open Finset Matrix

namespace PottsDiscontinuity.SixVertex

variable {k : ℕ} (r : ℕ) (L : ℝ) {q : ℂ} (hq : q ≠ 0) (x : Fin k → ℤ) (t : ℝ)

include hq in
/-- The projective Vandermonde formula cancels the position-dependent phase exactly. -/
theorem slater_centered_eq_pair_product :
    slater (centeredMomenta (k := k) q) x =
      ∏ a, ∏ b ∈ Ioi a, (q ^ (x b - x a) - q ^ (x a - x b)) := by
  have he : planeWaveMatrix (centeredMomenta q) x =
      Matrix.projVandermonde (fun a => q ^ x a) (fun a => (q ^ x a)⁻¹) := by
    ext b a
    have hr : a.rev.val = (k : ℤ) - 1 - a.val := by
      grind
    simp only [planeWaveMatrix, centeredMomenta, Matrix.projVandermonde_apply]
    rw [← zpow_natCast, ← zpow_natCast, ← _root_.zpow_neg_one,
      ← _root_.zpow_mul, ← _root_.zpow_mul, ← _root_.zpow_mul,
      ← _root_.zpow_mul, ← zpow_add₀ hq, hr]
    congr 1
    ring
  rw [slater, he, Matrix.det_projVandermonde]
  apply prod_congr rfl
  intro a _
  apply prod_congr rfl
  intro b _
  rw [zpow_sub₀ hq, zpow_sub₀ hq]
  rfl

include t in
/-- The unit complex wave with real phase. -/
noncomputable def unitWave : ℂ := Complex.exp (t * Complex.I)

theorem unitWave_ne_zero : unitWave t ≠ 0 := Complex.exp_ne_zero _

theorem unitWave_zpow (a : ℤ) : unitWave t ^ a = unitWave (t * a) := by
  rw [unitWave, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem unitWave_sub_neg :
    unitWave t - unitWave (-t) = 2 * Complex.I * (Real.sin t) := by
  unfold unitWave
  rw [show (-t : ℝ) * Complex.I = -(t * Complex.I) by push_cast; ring]
  rw [Complex.exp_mul_I]
  rw [show -(t * Complex.I) = (- t) * Complex.I by ring,
    Complex.exp_mul_I]
  simp only [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_sin]
  ring

include L x in
/-- The sine Vandermonde on arbitrary integer lifts. -/
noncomputable def sineLiftWeight : ℝ :=
  ∏ a, ∏ b ∈ Ioi a,
    Real.sin (Real.pi * ((x b) - x a) / L)

/-- The fixed, position-independent phase multiplier. -/
noncomputable def slaterPhase (k : ℕ) : ℂ :=
  ∏ a : Fin k, ∏ _b ∈ Ioi a, (2 * Complex.I)

theorem slaterPhase_ne_zero (k : ℕ) : slaterPhase k ≠ 0 := by
  apply prod_ne_zero_iff.mpr
  simp_all

/-- Exact equality with the real sine product; there is no residual position phase. -/
theorem slater_centered_unitWave :
    slater (centeredMomenta (k := k) (unitWave (Real.pi / L))) x =
      slaterPhase k * (sineLiftWeight L x) := by
  rw [slater_centered_eq_pair_product (unitWave_ne_zero _)]
  have he : ∀ a b : Fin k,
      unitWave (Real.pi / L) ^ (x b - x a) -
        unitWave (Real.pi / L) ^ (x a - x b) =
      (2 * Complex.I) * (Real.sin (Real.pi * ((x b : ℝ) - x a) / L)) := by
    intro a b
    rw [unitWave_zpow, unitWave_zpow]
    have h1 : Real.pi / L * (x b - x a : ℤ) =
        Real.pi * ((x b) - x a) / L := by push_cast; ring
    have h2 : Real.pi / L * (x a - x b : ℤ) =
        -(Real.pi * ((x b) - x a) / L) := by push_cast; ring
    rw [h1, h2, unitWave_sub_neg]
  simp_rw [he]
  simp only [prod_mul_distrib, slaterPhase, sineLiftWeight, Complex.ofReal_prod]

end PottsDiscontinuity.SixVertex
