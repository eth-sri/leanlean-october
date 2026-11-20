module

public import GS.Core

public import Mathlib.Tactic.NoncommRing

public import GS.Shared.BlockCoordinates

public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Exact m=4 example from the manuscript

Polynomial certificates are expressed as
Lean `linear_combination` proofs, not accepted as external numerical oracles.

The generic necessity proof and non-membership theorem are in M4Necessary.lean.
-/

noncomputable section
open Matrix GS.Shared
open scoped BigOperators
namespace GS.M4
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

def P : Mat 6 := !![1, 0, 0, 0, 0, 0;
  0, 0, 1, 0, 0, 0;
  0, 0, 0, 0, 1, 0;
  0, 1, 0, 0, 0, 0;
  0, 0, 0, 1, 0, 0;
  0, 0, 0, 0, 0, 1]

abbrev index : Fin 3 × Fin 2 ≃ Fin 6 := finProdFinEquiv

def assemble {𝕜 : Type*} [RCLike 𝕜] (D : Fin 3 → M 𝕜 2) : M 𝕜 6 := packBlocks index D

/-- The small numerical certificates use this explicit inverse index table. -/
theorem sixIndices (i : Fin 6) : index.symm i = ![(0,0),(0,1),(1,0),(1,1),(2,0),(2,1)] i := by
  fin_cases i <;> rfl

def middleBlock (t : ℝ) : Mat 2 := !![1,1;1,t]
def shuffle6 : Equiv.Perm (Fin 6) :=
  ⟨![0,3,1,4,2,5], ![0,2,4,1,3,5], by decide,
    by decide⟩

theorem P_eq_perm : P = GS.Shared.permMatrix shuffle6 := by
  ext i j
  fin_cases i, j <;> rfl

/-- Evaluate the three shuffles by reindexing instead of multiplying them out. -/
theorem core_apply {𝕜 : Type*} [RCLike 𝕜] (B C : M 𝕜 6) (i j : Fin 6) :
    let S : M 𝕜 6 := GS.Shared.permMatrix shuffle6
    (S*B*S*C*S) i j = ∑ k, B (shuffle6.symm i) k * C (shuffle6.symm k) (shuffle6 j) := by
  dsimp only
  rw [GS.Shared.mul_perm_apply, show _ * B * _ * C = GS.Shared.permMatrix shuffle6 *
    (B * (GS.Shared.permMatrix shuffle6 * C)) by simp only [Matrix.mul_assoc], GS.Shared.perm_mul_apply,
    Matrix.mul_apply]
  simp only [GS.Shared.perm_mul_apply]

def middleLeft : Fin 3 → Mat 2 := ![middleBlock (1/3),middleBlock (-1/3),middleBlock (-3)]
def middleRight : Fin 3 → Mat 2 := ![middleBlock (-3),middleBlock (-1/3),middleBlock (1/3)]

abbrev B2 := assemble middleRight
abbrev B3 := assemble middleLeft

def C : Mat 6 := P * B3 * P * B2 * P

def H : Mat 6 := assemble ![!![7/4, -3; -3, 21/4], !![1/4, 1/3; 1/3, 1/2], !![3/4, -1; -1, 3/2]]

def G : Mat 6 := assemble ![!![2, -8/3; -8/3, 4], !![4/3, 8/9; 8/9, 2/3], !![28/9, -16/3; -16/3, 28/3]]

def B1Blocks : Fin 3 → Mat 2 :=
  let s2 := Real.sqrt 2; let s3 := Real.sqrt 3; let s7 := Real.sqrt 7
  ![!![s7/2, 0; -6*s7/7, s3*s7/14], !![1/2,0; 2/3,s2/6], !![s3/2,0; -2*s3/3, s2*s3/6]]

def B4Blocks : Fin 3 → Mat 2 :=
  let s2 := Real.sqrt 2; let s3 := Real.sqrt 3; let s7 := Real.sqrt 7
  ![!![s2/2,0;2,3/2], !![s3/2,0; -s2*s3, 3*s2*s3/2], !![3*s7/14,0; 6*s3*s7/7,s3*s7/2]]

abbrev B1 := assemble B1Blocks
abbrev B4 := assemble B4Blocks
def Q : Mat 6 := B4*C*B1

theorem metric_identity : C*H*Cᵀ = G := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply (M := C) (N := H), Matrix.transpose_apply]
  simp only [C, P_eq_perm, core_apply]
  fin_cases i, j <;>
    norm_num [middleLeft, middleRight, middleBlock, H, G, assemble, sixIndices, shuffle6, Fin.sum_univ_succ]

theorem gram_B1 : B1 * B1ᵀ = H := by
  ext i j
  fin_cases i, j <;>
    norm_num [B1Blocks, H, assemble, sixIndices, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> norm_num [Real.sq_sqrt]

theorem normalize_B4 : B4 * G * B4ᵀ = 1 := by
  ext i j
  fin_cases i, j <;>
    norm_num [B4Blocks, G, assemble, sixIndices, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> norm_num [Real.sq_sqrt]

theorem Q_orthogonal : Orthogonal Q := Orthogonal.of_mul_transpose <| calc
  Q * Qᵀ = B4 * (C * (B1 * B1ᵀ) * Cᵀ) * B4ᵀ := by simp [Q, Matrix.transpose_mul, Matrix.mul_assoc]
  _ = 1 := by rw [gram_B1, metric_identity, normalize_B4]

theorem assemble_supported {𝕜 : Type*} [RCLike 𝕜] (D : Fin 3 → M 𝕜 2) :
    GS.Shared.BlockDiagonal 2 (assemble D) := packBlocks_supported index standard_block_label D

theorem Q_mem_A4 : InA4 2 2 2 2 P P P Q :=
  ⟨B1,B2,B3,B4,assemble_supported _,assemble_supported _,assemble_supported _,assemble_supported _,
    by grind [Q, C, product4]⟩

theorem index_apply (i : Fin 3) (a : Fin 2) : index (i,a) = ⟨2*i.val+a.val, by omega⟩ := by
  apply Fin.ext
  exact Nat.add_comm ..

/-- The four block determinants used in the counterexample. -/
def minorIndex : Fin 4 → Fin 3 × Fin 3 := ![(0,0),(0,2),(1,1),(2,2)]

def minors {𝕜 : Type*} [RCLike 𝕜] (A : M 𝕜 6) (i : Fin 4) : 𝕜 :=
  (blockView index A (minorIndex i).1 (minorIndex i).2).det

def coreDet {𝕜 : Type*} [RCLike 𝕜] (W Y : Fin 3 → M 𝕜 2) : Fin 4 → 𝕜 :=
  ![-W 0 0 1*W 1 0 1*Y 1 0 1*Y 0 1 0,
    W 1 0 0*W 0 0 1*Y 1 0 0*Y 2 0 1,
    -W 2 0 1*W 0 1 0*Y 0 0 1*Y 2 1 0,
    -W 1 1 0*W 2 1 0*Y 2 0 1*Y 1 1 0]

theorem core_det {𝕜 : Type*} [RCLike 𝕜] (W Y : Fin 3 → M 𝕜 2) :
    let p := GS.Shared.permMatrix (𝕜 := 𝕜) shuffle6
    minors (p*assemble W*p*assemble Y*p) = coreDet W Y := by
  dsimp only
  funext i
  simp only [minors, Matrix.det_fin_two, blockView_apply, core_apply]
  fin_cases i <;>
    norm_num [minorIndex, index_apply, shuffle6, assemble, packBlocks_apply, sixIndices,
      coreDet, Fin.sum_univ_succ] <;> ring

theorem minors_Q : minors Q =
    ![-(3/16 : ℝ) * Real.sqrt 2 * Real.sqrt 3, 3/8, -3/8,
      -(3/16 : ℝ) * Real.sqrt 2 * Real.sqrt 3] := by
  funext i
  simp only [Q, minors, assemble, blockView_pack_sandwich, Matrix.det_mul]
  have hc : minors C = coreDet middleLeft middleRight := by simpa only [C, P_eq_perm] using core_det middleLeft middleRight
  change (B4Blocks (minorIndex i).1).det * minors C i * (B1Blocks (minorIndex i).2).det = _
  rw [hc]
  have h3 : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by
    rw [show (Real.sqrt 3)^3 = (Real.sqrt 3)^2 * Real.sqrt 3 by ring, Real.sq_sqrt (by norm_num)]
  fin_cases i <;>
    norm_num [minorIndex, B1Blocks, B4Blocks, Matrix.det_fin_two, coreDet, middleLeft, middleRight, middleBlock] <;>
    ring_nf <;> norm_num [h3, Real.sq_sqrt] <;> ring

end GS.M4
