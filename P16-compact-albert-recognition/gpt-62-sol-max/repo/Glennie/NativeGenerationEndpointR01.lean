module
public import Glennie.UnitShifts
public import Glennie.Theorems.ComplexSectorProbes
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Matrix.Basis
@[expose] public section
namespace Glennie.NativeGenerationEndpointR01
noncomputable section
open Compact.NativeNormKernel PeirceSlots
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false

set_option quotPrecheck false in
/-- Closure of a native real subspace under the Jordan product. -/
notation "JordanClosed " K:arg => (∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)

private def gap (d : Fin 3 → ℝ) (i : Fin 3) := (d i - d (i+1)) * (d i - d (i+2))

private theorem diag_projector (d : Fin 3 → ℝ) (i : Fin 3) :
    jordan (diag d) (diag d) - (d (i+1) + d (i+2)) • diag d + (d (i+1) * d (i+2)) • (1 : Albert) =
      gap d i • e i := by
  fin_cases i <;> rw [diag, diagonal_jordan] <;>
    apply Albert.ext <;> norm_num [diag, e, gap, diagonalAlbert, Pi.single_apply] <;> ring

private theorem projector_mem {K : Submodule ℝ Albert} (h1 : (1 : Albert) ∈ K)
    (hJ : JordanClosed K) {d : Fin 3 → ℝ} (hx : diag d ∈ K)
    (hd : Function.Injective d) (i : Fin 3) : e i ∈ K := by
  have hn : gap d i ≠ 0 := mul_ne_zero
    (sub_ne_zero.mpr fun h => by have := hd h; omega)
    (sub_ne_zero.mpr fun h => by have := hd h; omega)
  rw [← K.smul_mem_iff hn, ← diag_projector]
  exact K.add_mem (K.sub_mem (hJ _ hx _ hx) (K.smul_mem _ hx)) (K.smul_mem _ h1)

variable {K : Submodule ℝ Albert}
variable (hJ : JordanClosed K)

local notation "Mat" => SectorMatrix

/- The Hermitian part acts on the hidden columns by right multiplication. -/
include hJ in
private theorem eq_top_of_hidden (hC : complexSector ≤ K) (z : Albert) (hz : z ∈ K)
    (hd : (hiddenMatrix z).det ≠ 0) : K = ⊤ := by
  let hide : Mat →ₗ[ℝ] Albert := compactSectorEquiv.symm.toLinearMap.comp (LinearMap.inr ℝ _ _)
  let L := K.comap hide
  have hhide (N : Mat) : hide N = hiddenAlbert N := by
    change complexAlbertLinear 0 + hiddenAlbert N = _
    rw [map_zero, zero_add]
  have proj (x : Albert) (hx : x ∈ K) : hiddenMatrix x ∈ L := by
    change hide (hiddenMatrix x) ∈ K
    rw [hhide, eq_sub_of_add_eq' (complex_hidden_decomposition x)]
    exact K.sub_mem hx (hC (complexProjection_mem x))
  have act (N : Mat) (hN : N ∈ L) (T : Mat) (hT : T.IsHermitian) : N*T ∈ L := by
    let B := T.trace • (1 : Mat) - (2 : ℂ) • T
    have ht := sectorHermitian_trace hT
    have hB : B.IsHermitian := by
      show B.conjTranspose = B
      simp [B, Matrix.conjTranspose_smul, hT.eq, ht]
    have hb : sectorComplement B = (2 : ℂ) • T := by
      simp only [sectorComplement, B, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, Nat.cast_ofNat]
      module
    let b := complexAlbertLinear (matrixComplexCoordinates B)
    have h := proj _ (hJ (hide N) hN b (hC ⟨_, rfl⟩))
    simpa only [hiddenMatrix_jordan, hhide, hiddenMatrix_hiddenAlbert, b, hiddenMatrix_complexAlbert,
      sectorComplexMatrix, complexCoordinates_albert, complexHermitianMatrix_inverse B hB,
      sectorProductHidden, sectorPolarAdjugate, sectorAdjointAdjugate, Matrix.adjugate_zero,
      zero_mul, add_zero, sub_self, sub_zero, Matrix.conjTranspose_zero, hb,
      Matrix.mul_smul, smul_smul, show (1/2:ℂ)*2=1 by norm_num, one_smul] using h
  let D (i : Fin 3) : Mat := Matrix.single i i 1
  have hD (i : Fin 3) : (D i).IsHermitian := by
    show (D i).conjTranspose = D i
    simp [D, Matrix.conjTranspose_single]
  have single (i j : Fin 3) (c : ℂ) (N : Mat) (hN : N ∈ L) : N * Matrix.single i j c ∈ L := by
    obtain ⟨k, hik, hjk⟩ : ∃ k : Fin 3, i ≠ k ∧ j ≠ k := by
      fin_cases i <;> fin_cases j <;> decide
    let A : Mat := Matrix.single i k c
    let B : Mat := Matrix.single k j 1
    have h := act _ (act _ (act _ hN (D i) (hD i)) (A + A.conjTranspose)
      (Matrix.isHermitian_add_transpose_self A)) (B + B.conjTranspose)
      (Matrix.isHermitian_add_transpose_self B)
    rw [Matrix.mul_assoc N, Matrix.mul_assoc N] at h
    simpa [D, A, B, Matrix.conjTranspose_single, Matrix.mul_add, Matrix.add_mul, hik, hik.symm,
      hjk, hjk.symm] using h
  let M := hiddenMatrix z
  have hall (T : Mat) : M*T ∈ L := by
    rw [Matrix.matrix_eq_sum_single T, Finset.mul_sum]
    refine L.sum_mem fun i _ => ?_
    rw [Finset.mul_sum]
    exact L.sum_mem fun j _ => single i j (T i j) M (proj z hz)
  refine top_unique fun x _ => ?_
  have hh := hall (M⁻¹ * hiddenMatrix x)
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hd), one_mul] at hh
  change hide (hiddenMatrix x) ∈ K at hh
  rw [hhide] at hh
  rw [← complex_hidden_decomposition x]
  exact K.add_mem (hC (complexProjection_mem x)) hh

/-- Nonzero response for a diagonal/complex pair forces the complete native algebra. -/
theorem eq_top_of_phi_ne_zero_diagonal_complex
    (K : Submodule ℝ Albert) (h1 : (1 : Albert) ∈ K)
    (hJ : JordanClosed K)
    (x y z : Albert) (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K)
    (hxd : IsDiagonal x) (hyc : InComplexSector y)
    (hphi : phi x y z ≠ 0) : K = ⊤ := by
  rw [phi_of_diagonal_complex x y z hxd hyc] at hphi
  simp only [mul_ne_zero_iff,   sub_ne_zero] at hphi
  obtain ⟨⟨⟨⟨h01,h12⟩,h20⟩,ht⟩,hd⟩ := hphi
  let d : Fin 3 → ℝ := ![x.d0,x.d1,x.d2]
  have hinj : Function.Injective d := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [d, eq_comm]
  have he := projector_mem h1 hJ (by simpa [diag, d, diagonalAlbert_eq _ hxd] using hx) hinj
  have hC := sector_le_of_probes K y hyc ht he (fun i => hJ _ (he i) _ hy)
    (fun i => hJ _ (he i) _ (hJ _ hy _ hy))
  refine eq_top_of_hidden hJ hC z hz ?_
  intro h
  simp [h] at hd

/-- Nonzero Phi implies full generation in the original coordinates. -/
theorem eq_top_of_phi_ne_zero
    (K : Submodule ℝ Albert) (h1 : (1 : Albert) ∈ K)
    (hJ : JordanClosed K)
    (x y z : Albert) (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K)
    (hphi : phi x y z ≠ 0) : K = ⊤ := by
  obtain ⟨g, hxd, hyc⟩ := universal_pair_reduction x y
  let L : Submodule ℝ Albert := K.map g.equiv.toLinearMap
  have hLJ : JordanClosed L := by
    rintro _ ⟨p,hp,rfl⟩ _ ⟨q,hq,rfl⟩
    exact ⟨jordan p q, hJ p hp q hq, g.map_jordan p q⟩
  apply (Submodule.map_eq_top_iff (e := g.equiv)).mp
  exact eq_top_of_phi_ne_zero_diagonal_complex L ⟨1,h1,g.map_unit⟩ hLJ
    (g.equiv x) (g.equiv y) (g.equiv z) ⟨x,hx,rfl⟩ ⟨y,hy,rfl⟩ ⟨z,hz,rfl⟩ hxd hyc
    (by rwa [g.phi_map])

end
end Glennie.NativeGenerationEndpointR01
