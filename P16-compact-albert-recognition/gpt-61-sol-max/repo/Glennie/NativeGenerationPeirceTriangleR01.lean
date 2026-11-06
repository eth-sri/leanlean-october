/- Second coordinate stage toward native unital generation.
No full generation result is assumed here. -/
module
public import Glennie.Native.CoordinateSimp
public import Glennie.NativeGenerationCoordinatesR01
public import Mathlib.LinearAlgebra.Complex.Module

@[expose] public section
namespace Glennie.NativeGenerationPeirceTriangleR01
section
open Glennie.NativeGenerationCoordinatesR01



variable (K : Submodule ℝ Albert) (h1 : (1 : Albert) ∈ K)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (a b c : ℝ) (hx : diagonalAlbert a b c ∈ K)

include K h1 hJ a b c hx in
theorem diagonal_projector_middle_mem

    (hg1 : b - a ≠ 0) (hg2 : b - c ≠ 0) :
    diagonalAlbert 0 1 0 ∈ K := by
  apply (K.smul_mem_iff (mul_ne_zero hg1 hg2)).mp
  convert K.add_mem (K.sub_mem (hJ _ hx _ hx) (K.smul_mem (a + c) hx))
    (K.smul_mem (a * c) h1) using 1
  ext <;> simp [albert_coords, diagonalAlbert, octDot] <;> ring



include K h1 hJ a b c hx in
theorem diagonal_projector_last_mem

    (hg1 : c - a ≠ 0) (hg2 : c - b ≠ 0) :
    diagonalAlbert 0 0 1 ∈ K := by
  apply (K.smul_mem_iff (mul_ne_zero hg1 hg2)).mp
  convert K.add_mem (K.sub_mem (hJ _ hx _ hx) (K.smul_mem (a + b) hx))
    (K.smul_mem (a * b) h1) using 1
  ext <;> simp [albert_coords, diagonalAlbert, octDot] <;> ring



theorem peirce02_mem (K : Submodule ℝ Albert)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (h0 : diagonalAlbert 1 0 0 ∈ K) (h1 : diagonalAlbert 0 0 1 ∈ K)
    (z : Albert) (hz : z ∈ K) : (⟨0, 0, 0, 0, z.o02, 0⟩ : Albert) ∈ K := by
  convert K.smul_mem 4 (hJ _ h0 _ (hJ _ h1 _ hz)) using 1
  apply Albert.ext
  all_goals norm_num [albert_coords, diagonalAlbert, octDot, smul_smul]
  all_goals apply Prod.ext <;> apply Quaternion.ext <;> norm_num



theorem peirce12_mem (K : Submodule ℝ Albert)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (h0 : diagonalAlbert 0 1 0 ∈ K) (h1 : diagonalAlbert 0 0 1 ∈ K)
    (z : Albert) (hz : z ∈ K) : (⟨0, 0, 0, 0, 0, z.o12⟩ : Albert) ∈ K := by
  convert K.smul_mem 4 (hJ _ h0 _ (hJ _ h1 _ hz)) using 1
  apply Albert.ext
  all_goals norm_num [albert_coords, diagonalAlbert, octDot, smul_smul]
  all_goals apply Prod.ext <;> apply Quaternion.ext <;> norm_num

/-- Division-free real inversion in the complex plane. -/
theorem complex_real_det_expansion (u v z : ℂ) :
    (u.re * v.im - u.im * v.re) • z =
      (z.re * v.im - z.im * v.re) • u +
      (u.re * z.im - u.im * z.re) • v := by
  apply Complex.ext <;>
    simp [] <;> ring

/-- Two complex coordinates with nonzero real determinant fill a real-linear
image, without imposing a complex module structure on the ambient submodule. -/
theorem complex_line_mem_of_real_det_ne_zero
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (K : Submodule ℝ V) (T : ℂ →ₗ[ℝ] V) (u v : ℂ)
    (hu : T u ∈ K) (hv : T v ∈ K)
    (hd : u.re * v.im - u.im * v.re ≠ 0) (z : ℂ) : T z ∈ K := by
  apply (K.smul_mem_iff hd).mp
  rw [← map_smul, complex_real_det_expansion, map_add, map_smul, map_smul]
  exact K.add_mem (K.smul_mem _ hu) (K.smul_mem _ hv)

theorem triangle_real_det01 (u v w : ℂ) :
    u.re * (v * star w).im - u.im * (v * star w).re =
      -(u * w * star v).im := by
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem triangle_real_det12 (u v w : ℂ) :
    w.re * (star u * v).im - w.im * (star u * v).re =
      -(u * w * star v).im := by
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem triangle_real_det02 (u v w : ℂ) :
    v.re * (u * w).im - v.im * (u * w).re =
      (u * w * star v).im := by
  simp [Complex.mul_re, Complex.mul_im]
  ring

end
end Glennie.NativeGenerationPeirceTriangleR01
