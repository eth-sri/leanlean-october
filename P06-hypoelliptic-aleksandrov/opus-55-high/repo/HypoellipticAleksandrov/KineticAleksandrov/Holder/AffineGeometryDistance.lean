module

public import HypoellipticAleksandrov.KineticAleksandrov.Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Elementary separation properties of the literal kinetic quasi-distance -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

variable {d : ℕ} (P Q : KineticPoint d)

/-- The source kinetic quasi-distance is nonnegative. -/
theorem quasiDistance_nonneg  : 0 ≤ quasiDistance P Q := add_nonneg (add_nonneg (Real.sqrt_nonneg _)
    (PDE.vecEuclideanNorm_nonneg _))
    (Real.rpow_nonneg (le_max_of_le_left (PDE.vecEuclideanNorm_nonneg _)) _)

/-- The source maximum of the two transported displacements makes the distance symmetric. -/
theorem quasiDistance_symm  :
    quasiDistance P Q = quasiDistance Q P := by
  unfold quasiDistance
  rw [abs_sub_comm, PDE.vecEuclideanNorm_sub_comm,
    max_comm]

/-- The source quasi-distance separates points, including in dimension zero. -/
theorem quasiDistance_eq_zero_iff  :
    quasiDistance P Q = 0 ↔ P = Q := by
  constructor
  · intro h
    let B := max
      (PDE.vecEuclideanNorm (Q.position - P.position - (Q.time - P.time) • P.velocity))
      (PDE.vecEuclideanNorm (P.position - Q.position - (P.time - Q.time) • Q.velocity))
    have hB : 0 ≤ B := le_max_of_le_left (PDE.vecEuclideanNorm_nonneg _)
    have hroot := Real.sqrt_nonneg |P.time - Q.time|
    have hvel := PDE.vecEuclideanNorm_nonneg (P.velocity - Q.velocity)
    have hrpow := Real.rpow_nonneg hB (1 / 3 : ℝ)
    change 0 ≤ Real.rpow B (1 / 3 : ℝ) at hrpow
    change Real.sqrt |P.time - Q.time| +
      PDE.vecEuclideanNorm (P.velocity - Q.velocity) + Real.rpow B (1 / 3 : ℝ) = 0 at h
    have ht0 : Real.sqrt |P.time - Q.time| = 0 := by linarith
    have hv0 : PDE.vecEuclideanNorm (P.velocity - Q.velocity) = 0 := by
      linarith
    have hb0 : Real.rpow B (1 / 3 : ℝ) = 0 := by simp_all
    have ht : P.time = Q.time := by
      grind
    have hv : P.velocity = Q.velocity :=
      sub_eq_zero.mp (PDE.vecEuclideanNorm_eq_zero_iff.mp hv0)
    have hB0 : B = 0 := (Real.rpow_eq_zero hB (by norm_num : (1 / 3 : ℝ) ≠ 0)).mp hb0
    have hxle := le_max_left
      (PDE.vecEuclideanNorm (Q.position - P.position - (Q.time - P.time) • P.velocity))
      (PDE.vecEuclideanNorm (P.position - Q.position - (P.time - Q.time) • Q.velocity))
    change _ ≤ B at hxle
    rw [hB0, ht, sub_self, zero_smul, sub_zero] at hxle
    have hx : P.position = Q.position :=
      (sub_eq_zero.mp (PDE.vecEuclideanNorm_eq_zero_iff.mp
        (le_antisymm hxle (PDE.vecEuclideanNorm_nonneg _)))).symm
    aesop
  · rintro rfl
    have hz : PDE.vecEuclideanNorm (0 : PDE.Vec d) = 0 :=
      PDE.vecEuclideanNorm_eq_zero_iff.mpr rfl
    simp [quasiDistance, hz]

end HypoellipticAleksandrov.KineticAleksandrov.Holder
