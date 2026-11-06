module

public import RequestProject.DiskHarmonicModes

/-!
# The physical area Gram matrix of harmonic disk monomials

The already proved gradient Green identity determines the area Gram
matrix by differentiation of the powers with exponents increased by one.
This is the physical area integral, without an assumed polar integration
formula. It supplies the monomials used for the regular Neumann mass
forcing estimates.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Real
open scoped ComplexConjugate

variable (m n : ℕ)

theorem disk_gradient_pair_succ_eq_area_monomial (z : ℂ) :
    (∑ i : Fin 2, dirD (diskHolomorphicMode (m + 1)) (coordDir i) z *
      dirD (diskAntiholomorphicMode (n + 1)) (coordDir i) z) =
      2 * (m + 1 : ℕ) * (n + 1 : ℕ) * (z ^ m * conj z ^ n) := by
  rw [Fin.sum_univ_two]
  simp only [show coordDir 0 = 1 from rfl,
    show coordDir 1 = Complex.I from rfl, dirD_diskHolomorphicMode, dirD_diskAntiholomorphicMode,
    Nat.add_sub_cancel, map_one, Complex.conj_I]
  calc
    _ = (m + 1 : ℕ) * (n + 1 : ℕ) * (z ^ m * conj z ^ n) *
        (1 - Complex.I ^ 2) := by ring
    _ = _ := by rw [Complex.I_sq]; ring

theorem integral_disk_area_monomials :
    (∫ z in ball 0 1, z ^ m * conj z ^ n) =
      if m = n then (π : ℂ) / (m + 1 : ℕ) else 0 := by
  let c : ℂ := 2 * (m + 1 : ℕ) * (n + 1 : ℕ)
  have hc : c ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num)
      (Nat.cast_ne_zero.mpr (by omega))) (Nat.cast_ne_zero.mpr (by omega))
  have hgreen : c * (∫ z in ball 0 1, z ^ m * conj z ^ n) =
      if m + 1 = n + 1 then (2 * π : ℂ) * (n + 1 : ℕ) else 0 := by
    calc
      _ = ∫ z in ball 0 1, ∑ i : Fin 2,
          dirD (diskHolomorphicMode (m + 1)) (coordDir i) z *
            dirD (diskAntiholomorphicMode (n + 1)) (coordDir i) z := by
        rw [← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_ball
        intro z _
        exact (disk_gradient_pair_succ_eq_area_monomial m n z).symm
      _ = _ := integral_disk_holomorphic_antiholomorphic_gradients (m + 1) (n + 1)
  grind

end PolyaNeumann

end
