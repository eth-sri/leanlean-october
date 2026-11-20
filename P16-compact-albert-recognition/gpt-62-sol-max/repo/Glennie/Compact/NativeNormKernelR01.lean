module
public import Glennie.Diagonalization
public import Glennie.UnitShifts
public import Glennie.Hilbert
/- Native norm kernel. -/
@[expose] public section
namespace Glennie.Compact.NativeNormKernel
open Glennie
noncomputable section
set_option autoImplicit false

 theorem diagonal_norm_sq (a b c : ℝ) :
    ‖diagonalAlbert a b c‖ ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
  rw [native_norm_sq, inner_self_coordinates]
  simp [diagonalAlbert, octNormSq_zero]

 /-- Six orthogonal native coordinate blocks, with positive octonion weights. -/
 theorem diagonal_multiplier_sq (y : Albert) (t0 t1 t2 t01 t02 t12 q : ℝ)
    (h0 : t0^2 ≤ q) (h1 : t1^2 ≤ q) (h2 : t2^2 ≤ q)
    (h01 : t01^2 ≤ q) (h02 : t02^2 ≤ q) (h12 : t12^2 ≤ q) :
    ‖(⟨t0*y.d0,t1*y.d1,t2*y.d2,t01 • y.o01,
        t02 • y.o02,t12 • y.o12⟩ : Albert)‖ ^ 2 ≤ q * ‖y‖ ^ 2 := by
  simp only [native_norm_sq, inner_self_coordinates, octNormSq_smul, mul_pow, mul_add,
    ← mul_assoc, mul_comm q (2 : ℝ)]
  gcongr <;> exact octNormSq_nonneg _

 theorem diagonal_jordan_norm (a b c : ℝ) (y : Albert) :
    ‖jordan (diagonalAlbert a b c) y‖ ≤ ‖diagonalAlbert a b c‖ * ‖y‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, diagonal_norm_sq, diagonal_jordan]
  apply diagonal_multiplier_sq <;> nlinarith only
    [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg (a-b), sq_nonneg (a-c), sq_nonneg (b-c)]

 theorem diagonal_U_norm (a b c : ℝ) (y : Albert) :
    ‖U (diagonalAlbert a b c) y‖ ≤ ‖diagonalAlbert a b c‖ ^ 2 * ‖y‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (sq_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, diagonal_norm_sq, U_diagonal]
  apply diagonal_multiplier_sq
  all_goals
    first | apply pow_le_pow_left₀ (by positivity) | rw [mul_pow, pow_two (a^2+b^2+c^2)]; gcongr
    all_goals linarith only [sq_nonneg a, sq_nonneg b, sq_nonneg c]

local macro "diagonal_bound " x:ident y:ident F:term : tactic => `(tactic|
  (obtain ⟨g, hg⟩ := native_diagonalization $x
   simpa only [diagonalAlbert_eq (g.equiv $x) hg, ← g.map_jordan, ← g.map_U, g.norm_map] using
     $F (g.equiv $x).d0 (g.equiv $x).d1 (g.equiv $x).d2 (g.equiv $y)))

 theorem jordan_norm (x y : Albert) : ‖jordan x y‖ ≤ ‖x‖ * ‖y‖ := by
  diagonal_bound x y diagonal_jordan_norm

 theorem U_norm (x y : Albert) : ‖U x y‖ ≤ ‖x‖ ^ 2 * ‖y‖ := by
  diagonal_bound x y diagonal_U_norm

end
end Glennie.Compact.NativeNormKernel
