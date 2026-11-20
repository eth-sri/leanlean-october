module
public import Glennie.Diagonalization
public import Glennie.Sector
public import Glennie.Hilbert

/- Native norm kernel. -/
@[expose] public section
namespace Glennie.Compact.NativeNormKernel
open Glennie
noncomputable section
set_option autoImplicit false

 theorem norm_map (g : CompactAutomorphism) (x : Albert) : ‖g.equiv x‖ = ‖x‖ := by
  apply le_antisymm
  · apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [native_norm_sq, g.inner_map]
  · apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [native_norm_sq, g.inner_map]

 theorem octNormSq_smul (r : ℝ) (v : Octonion) :
    octNormSq (r • v) = r ^ 2 * octNormSq v := by
  simp [octNormSq, Quaternion.normSq_def', smul_eq_mul]
  <;> ring

 theorem diagonal_norm_sq (a b c : ℝ) :
    ‖diagonalAlbert a b c‖ ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
  simp [diagonalAlbert, native_norm_sq, inner_self_coordinates, octNormSq]

 theorem diagonal_jordan (a b c : ℝ) (y : Albert) :
    jordan (diagonalAlbert a b c) y =
      ⟨a*y.d0, b*y.d1, c*y.d2,
        ((a+b)/2) • y.o01, ((a+c)/2) • y.o02, ((b+c)/2) • y.o12⟩ := by
  ext
  all_goals simp [diagonalAlbert, jordan_d0, jordan_d1, jordan_d2,
    jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul,
    octConj, smul_smul, smul_eq_mul]
  all_goals ring
  all_goals simp

 /-- Six orthogonal native coordinate blocks, with positive octonion weights. -/
 theorem diagonal_multiplier_sq (y : Albert) (t0 t1 t2 t01 t02 t12 q : ℝ)
    (h0 : t0^2 ≤ q) (h1 : t1^2 ≤ q) (h2 : t2^2 ≤ q)
    (h01 : t01^2 ≤ q) (h02 : t02^2 ≤ q) (h12 : t12^2 ≤ q) :
    ‖(⟨t0*y.d0,t1*y.d1,t2*y.d2,t01 • y.o01,
        t02 • y.o02,t12 • y.o12⟩ : Albert)‖ ^ 2 ≤ q * ‖y‖ ^ 2 := by
  have H0 := mul_le_mul_of_nonneg_right h0 (sq_nonneg y.d0)
  have H1 := mul_le_mul_of_nonneg_right h1 (sq_nonneg y.d1)
  have H2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg y.d2)
  have H01 := mul_le_mul_of_nonneg_right h01 (octNormSq_nonneg y.o01)
  have H02 := mul_le_mul_of_nonneg_right h02 (octNormSq_nonneg y.o02)
  have H12 := mul_le_mul_of_nonneg_right h12 (octNormSq_nonneg y.o12)
  simp [native_norm_sq, inner_self_coordinates, octNormSq_smul] <;> linarith

 theorem diagonal_jordan_norm (a b c : ℝ) (y : Albert) :
    ‖jordan (diagonalAlbert a b c) y‖ ≤ ‖diagonalAlbert a b c‖ * ‖y‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, diagonal_norm_sq, diagonal_jordan]
  apply diagonal_multiplier_sq
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  nlinarith

 theorem diagonal_U_norm (a b c : ℝ) (y : Albert) :
    ‖U (diagonalAlbert a b c) y‖ ≤ ‖diagonalAlbert a b c‖ ^ 2 * ‖y‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (sq_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, diagonal_norm_sq, U_diagonal]
  apply diagonal_multiplier_sq
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  nlinarith

 theorem diagonal_reconstruct (x : Albert) (hx : IsDiagonal x) :
    x = diagonalAlbert x.d0 x.d1 x.d2 := by
  apply Albert.ext <;> simp [diagonalAlbert, hx.1, hx.2.1, hx.2.2]

 theorem jordan_norm (x y : Albert) : ‖jordan x y‖ ≤ ‖x‖ * ‖y‖ := by
  obtain ⟨g,hg⟩ := native_diagonalization x
  have H := diagonal_jordan_norm (g.equiv x).d0 (g.equiv x).d1
    (g.equiv x).d2 (g.equiv y)
  simp_all [← diagonal_reconstruct (g.equiv x) hg, ← g.map_jordan, norm_map]

 theorem U_norm (x y : Albert) : ‖U x y‖ ≤ ‖x‖ ^ 2 * ‖y‖ := by
  obtain ⟨g,hg⟩ := native_diagonalization x
  have H := diagonal_U_norm (g.equiv x).d0 (g.equiv x).d1
    (g.equiv x).d2 (g.equiv y)
  simp_all [← diagonal_reconstruct (g.equiv x) hg, ← g.map_U, norm_map]

end
end Glennie.Compact.NativeNormKernel
