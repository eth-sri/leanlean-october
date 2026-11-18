module

public import GS.Unitary.RealEmbedding
public import GS.Unitary.Factorization
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Matrix GS GS.UnitaryGeometry
open scoped BigOperators

namespace GS.UnitaryGeometry
def product4 {n : ℕ} (B₄ P₃ B₃ P₂ B₂ P₁ B₁ : CMat n) : CMat n :=
  B₄ * P₃ * B₃ * P₂ * B₂ * P₁ * B₁

def CInA4 {n : ℕ} (b₁ b₂ b₃ b₄ : ℕ) (P₁ P₂ P₃ A : CMat n) : Prop :=
  ∃ B₁ B₂ B₃ B₄, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    CBlockDiagonal b₃ B₃ ∧ CBlockDiagonal b₄ B₄ ∧ A = product4 B₄ P₃ B₃ P₂ B₂ P₁ B₁

def CInA4Unitary {n : ℕ} (b₁ b₂ b₃ b₄ : ℕ) (P₁ P₂ P₃ A : CMat n) : Prop :=
  ∃ B₁ B₂ B₃ B₄, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    CBlockDiagonal b₃ B₃ ∧ CBlockDiagonal b₄ B₄ ∧
    Unitary B₁ ∧ Unitary B₂ ∧ Unitary B₃ ∧ Unitary B₄ ∧ A = product4 B₄ P₃ B₃ P₂ B₂ P₁ B₁
end GS.UnitaryGeometry

namespace GS.M4
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def P : Mat 6 := !![1, 0, 0, 0, 0, 0;
  0, 0, 1, 0, 0, 0;
  0, 0, 0, 0, 1, 0;
  0, 1, 0, 0, 0, 0;
  0, 0, 0, 1, 0, 0;
  0, 0, 0, 0, 0, 1]

def assem {R : Type*} [Zero R] (A : Fin 3 → Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 6) (Fin 6) R :=
  !![A 0 0 0, A 0 0 1, 0, 0, 0, 0;
     A 0 1 0, A 0 1 1, 0, 0, 0, 0;
     0, 0, A 1 0 0, A 1 0 1, 0, 0;
     0, 0, A 1 1 0, A 1 1 1, 0, 0;
     0, 0, 0, 0, A 2 0 0, A 2 0 1;
     0, 0, 0, 0, A 2 1 0, A 2 1 1]

private theorem assem_supp (A : Fin 3 → Mat 2) : BlockDiagonal 2 (assem A) := by
  intro i j hij; fin_cases i <;> fin_cases j <;> simp [assem] <;> norm_num at hij

def B2 : Mat 6 := assem ![!![1, 1; 1, -3], !![1, 1; 1, -1/3], !![1, 1; 1, 1/3]]
def B3 : Mat 6 := assem ![!![1, 1; 1, 1/3], !![1, 1; 1, -1/3], !![1, 1; 1, -3]]
def B1p (s2 s3 s7 : ℝ) : Mat 6 :=
  assem ![!![s7/2, 0; -6*s7/7, s3*s7/14], !![1/2, 0; 2/3, s2/6], !![s3/2, 0; -2*s3/3, s2*s3/6]]
def B4p (s2 s3 s7 : ℝ) : Mat 6 :=
  assem ![!![s2/2, 0; 2, 3/2], !![s3/2, 0; -s2*s3, 3*s2*s3/2], !![3*s7/14, 0; 6*s3*s7/7, s3*s7/2]]

def C : Mat 6 := !![1, 1, 1, 0, 1, 0;
  1, 0, -3, 1, 0, 1;
  0, -1/3, 0, 1, 1, 1/3;
  1, 1/3, 1, 0, 1/3, 0;
  -1/3, 0, 1, 1, 0, 1;
  0, -1/3, 0, -3, 1, -1]

def cell (i : Fin 3) (a : Fin 2) : Fin 6 := ⟨2 * i.val + a.val, by omega⟩
def detB {R : Type*} [CommRing R] (M : Matrix (Fin 6) (Fin 6) R) (i j : Fin 3) : R :=
  (M.submatrix (cell i) (cell j)).det

private theorem core_id : P * B3 * P * B2 * P = C := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [P, B2, B3, C, assem, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem Qp_certs (s2 s3 s7 : ℝ) (h2 : s2^2 = 2) (h3 : s3^2 = 3) (h7 : s7^2 = 7) :
    let Qp := B4p s2 s3 s7 * C * B1p s2 s3 s7
    Qp * Qpᵀ = 1 ∧
    (detB Qp 0 0)^2 = 27/128 ∧ (detB Qp 0 2)^2 = 9/64 ∧
    (detB Qp 1 0)^2 = 27/128 ∧ (detB Qp 1 1)^2 = 9/64 ∧
    (detB Qp 2 1)^2 = 27/128 ∧ (detB Qp 2 2)^2 = 27/128 := by
  have h23 : s2^3 = 2 * s2 := by linear_combination s2 * h2
  have h24 : s2^4 = 4 := by linear_combination (s2^2 + 2) * h2
  have h33 : s3^3 = 3 * s3 := by linear_combination s3 * h3
  have h34 : s3^4 = 9 := by linear_combination (s3^2 + 3) * h3
  have h36 : s3^6 = 27 := by linear_combination (s3^4 + 3*s3^2 + 9) * h3
  have h73 : s7^3 = 7 * s7 := by linear_combination s7 * h7
  have h74 : s7^4 = 49 := by linear_combination (s7^2 + 7) * h7
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      (norm_num [B4p, B1p, C, assem, Matrix.mul_apply, Fin.sum_univ_succ]; ring_nf;
       simp only [h2, h3, h7, h23, h24, h33, h34, h73, h74]; ring)
  all_goals
    norm_num [detB, Matrix.det_fin_two, cell, B4p, B1p, C, assem, Matrix.mul_apply, Fin.sum_univ_succ]
    ring_nf; simp only [h2, h3, h24, h34, h36, h74]; ring

def Q : Mat 6 := B4p (Real.sqrt 2) (Real.sqrt 3) (Real.sqrt 7) * C *
  B1p (Real.sqrt 2) (Real.sqrt 3) (Real.sqrt 7)

theorem Q_orthogonal : Orthogonal Q :=
  Orthogonal.of_mul_transpose (Qp_certs (Real.sqrt 2) (Real.sqrt 3) (Real.sqrt 7)
    (Real.sq_sqrt (by norm_num)) (Real.sq_sqrt (by norm_num)) (Real.sq_sqrt (by norm_num))).1

theorem Q_mem_A4 : InA4 2 2 2 2 P P P Q :=
  ⟨B1p (Real.sqrt 2) (Real.sqrt 3) (Real.sqrt 7), B2, B3,
    B4p (Real.sqrt 2) (Real.sqrt 3) (Real.sqrt 7),
    assem_supp _, assem_supp _, assem_supp _, assem_supp _,
    by simp only [Q, ← core_id, GS.product4, Matrix.mul_assoc]⟩

private theorem cblock_eq (A : CMat 6) (hA : CBlockDiagonal 2 A) :
    A = assem fun r => A.submatrix (cell r) (cell r) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [assem, cell] <;> exact hA _ _ (by decide)

private theorem sub_outer (A C₀ B : CMat 6) (hA : CBlockDiagonal 2 A) (hB : CBlockDiagonal 2 B)
    (i j : Fin 3) :
    (A * C₀ * B).submatrix (cell i) (cell j) =
      A.submatrix (cell i) (cell i) * C₀.submatrix (cell i) (cell j) *
        B.submatrix (cell j) (cell j) := by
  conv_lhs => rw [cblock_eq A hA, cblock_eq B hB]
  ext a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [assem, cell, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ] <;> ring

private theorem sub_unitary (A : CMat 6) (hA : CBlockDiagonal 2 A) (hu : Unitary A) (r : Fin 3) :
    Unitary (A.submatrix (cell r) (cell r)) := by
  have ha := cblock_eq A hA
  constructor <;> ext a b
  · have h := ha ▸ congrFun (congrFun hu.1 (cell r a)) (cell r b)
    fin_cases r <;> fin_cases a <;> fin_cases b <;>
      simpa [assem, cell, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ] using h
  · have h := ha ▸ congrFun (congrFun hu.2 (cell r a)) (cell r b)
    fin_cases r <;> fin_cases a <;> fin_cases b <;>
      simpa [assem, cell, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ] using h

private theorem normSq_det_u {U : CMat 2} (hU : Unitary U) : Complex.normSq U.det = 1 := by
  have h := congrArg (Complex.normSq ∘ Matrix.det) hU.1
  simp only [Function.comp_apply, Matrix.det_mul, Matrix.det_conjTranspose, map_mul,
    Complex.star_def, Complex.normSq_conj, Matrix.det_one, map_one] at h
  nlinarith [Complex.normSq_nonneg U.det]

private theorem u2_nsq (W : CMat 2) (hW : Unitary W) :
    let u := Complex.normSq (W 0 0)
    0 ≤ u ∧ u ≤ 1 ∧ Complex.normSq (W 0 1) = 1 - u ∧
    Complex.normSq (W 1 0) = 1 - u ∧ Complex.normSq (W 1 1) = u := by
  have hc0 : Complex.normSq (W 0 0) + Complex.normSq (W 1 0) = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, Complex.mul_re, Complex.normSq_apply] using
      congrArg Complex.re (congrFun (congrFun hW.1 0) 0)
  have hc1 : Complex.normSq (W 0 1) + Complex.normSq (W 1 1) = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, Complex.mul_re, Complex.normSq_apply] using
      congrArg Complex.re (congrFun (congrFun hW.1 1) 1)
  have hr0 : Complex.normSq (W 0 0) + Complex.normSq (W 0 1) = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, Complex.mul_re, Complex.normSq_apply] using
      congrArg Complex.re (congrFun (congrFun hW.2 0) 0)
  dsimp only
  refine ⟨Complex.normSq_nonneg _, ?_, by linarith, by linarith, by linarith⟩
  linarith [Complex.normSq_nonneg (W 0 1)]

theorem Qc_not_unitary4 :
    ¬ CInA4Unitary 2 2 2 2 (ofRealMatrix P) (ofRealMatrix P) (ofRealMatrix P) (ofRealMatrix Q) := by
  have Q_certs := Qp_certs (Real.sqrt 2) (Real.sqrt 3) (Real.sqrt 7)
    (Real.sq_sqrt (by norm_num)) (Real.sq_sqrt (by norm_num)) (Real.sq_sqrt (by norm_num))
  let Pc := ofRealMatrix P
  let Qc := ofRealMatrix Q
  rintro ⟨B₁, B₂, B₃, B₄, hb₁, hb₂, hb₃, hb₄, ho₁, ho₂, ho₃, ho₄, he⟩
  let W (r : Fin 3) := B₃.submatrix (cell r) (cell r)
  let Y (r : Fin 3) := B₂.submatrix (cell r) (cell r)
  let C₀ := Pc * assem W * Pc * assem Y * Pc
  have he' : Qc = B₄ * C₀ * B₁ := by
    dsimp [Qc]; rw [he]; dsimp [C₀, GS.UnitaryGeometry.product4]
    conv_lhs => rw [cblock_eq B₂ hb₂, cblock_eq B₃ hb₃]
    simp only [Matrix.mul_assoc]; rfl
  have h6 (i j : Fin 3) : (detB Q i j)^2 = Complex.normSq (detB C₀ i j) := by
    have h1 : Complex.normSq (detB Qc i j) = (detB Q i j)^2 := by
      simp only [Qc, detB, Matrix.det_fin_two, submatrix_apply, ofRealMatrix_apply,
        ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.normSq_ofReal, sq]
    rw [← h1]; dsimp [detB]
    rw [he', sub_outer B₄ C₀ B₁ hb₄ hb₁ i j, Matrix.det_mul, Matrix.det_mul, map_mul, map_mul,
      normSq_det_u (sub_unitary B₄ hb₄ ho₄ i), normSq_det_u (sub_unitary B₁ hb₁ ho₁ j)]
    ring
  have hdets :
      detB C₀ 0 0 = -(W 0 0 1 * W 1 0 1 * Y 1 0 1 * Y 0 1 0) ∧
      detB C₀ 0 2 = W 1 0 0 * W 0 0 1 * Y 1 0 0 * Y 2 0 1 ∧
      detB C₀ 1 0 = -(W 2 0 0 * W 0 1 0 * Y 0 0 0 * Y 1 1 1) ∧
      detB C₀ 1 1 = -(W 2 0 1 * W 0 1 0 * Y 0 0 1 * Y 2 1 0) ∧
      detB C₀ 2 1 = W 1 1 1 * W 2 1 1 * Y 2 1 0 * Y 0 1 1 ∧
      detB C₀ 2 2 = -(W 1 1 0 * W 2 1 0 * Y 2 0 1 * Y 1 1 0) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals
      norm_num [detB, Matrix.det_fin_two, C₀, Pc, P, ofRealMatrix, assem, cell,
        Matrix.mul_apply, Fin.sum_univ_succ]; ring
  rcases hdets with ⟨d00, d02, d10, d11, d21, d22⟩
  have hw (r : Fin 3) := u2_nsq (W r) (sub_unitary B₃ hb₃ ho₃ r)
  have hy (r : Fin 3) := u2_nsq (Y r) (sub_unitary B₂ hb₂ ho₂ r)
  let u (r : Fin 3) := Complex.normSq (W r 0 0)
  let v (r : Fin 3) := Complex.normSq (Y r 0 0)
  dsimp only [Q] at h6
  have e00 : (1 - u 0) * (1 - u 1) * (1 - v 1) * (1 - v 0) = 27 / 128 := by
    have := h6 0 0; rw [Q_certs.2.1, d00] at this
    simpa only [Complex.normSq_neg, map_mul, (hw _).2.2.1, (hy _).2.2.1, (hy _).2.2.2.1] using this.symm
  have e02 : u 1 * (1 - u 0) * v 1 * (1 - v 2) = 9 / 64 := by
    have := h6 0 2; rw [Q_certs.2.2.1, d02] at this
    simpa only [map_mul, (hw _).2.2.1, (hy _).2.2.1] using this.symm
  have e10 : u 2 * (1 - u 0) * v 0 * v 1 = 27 / 128 := by
    have := h6 1 0; rw [Q_certs.2.2.2.1, d10] at this
    simpa only [Complex.normSq_neg, map_mul, (hw _).2.2.2.1, (hy _).2.2.2.2] using this.symm
  have e11 : (1 - u 2) * (1 - u 0) * (1 - v 0) * (1 - v 2) = 9 / 64 := by
    have := h6 1 1; rw [Q_certs.2.2.2.2.1, d11] at this
    simpa only [Complex.normSq_neg, map_mul, (hw _).2.2.1, (hw _).2.2.2.1, (hy _).2.2.1, (hy _).2.2.2.1] using this.symm
  have e21 : u 1 * u 2 * (1 - v 2) * v 0 = 27 / 128 := by
    have := h6 2 1; rw [Q_certs.2.2.2.2.2.1, d21] at this
    simpa only [map_mul, (hw _).2.2.2.2, (hy _).2.2.2.1, (hy _).2.2.2.2] using this.symm
  have e22 : (1 - u 1) * (1 - u 2) * (1 - v 2) * (1 - v 1) = 27 / 128 := by
    have := h6 2 2; rw [Q_certs.2.2.2.2.2.2, d22] at this
    simpa only [Complex.normSq_neg, map_mul, (hw _).2.2.2.1, (hy _).2.2.1, (hy _).2.2.2.1] using this.symm
  have m1 : 27 / 128 * ((1 - u 0) * v 1)^2 = 9 / 64 * (27 / 128) := by
    linear_combination (27 / 128) * e02 + (u 1 * (1 - u 0) * v 1 * (1 - v 2)) * e10 -
      ((1 - u 0) * v 1)^2 * e21
  have m2 : 27 / 128 * (u 1 * (1 - v 2))^2 = 9 / 64 * (27 / 128) := by
    linear_combination (27 / 128) * e02 + (u 1 * (1 - u 0) * v 1 * (1 - v 2)) * e21 -
      (u 1 * (1 - v 2))^2 * e10
  have m3 : 9 / 64 * ((1 - u 1) * (1 - v 1))^2 = (27 / 128)^2 := by
    linear_combination (27 / 128) * e00 +
      ((1 - u 0) * (1 - u 1) * (1 - v 1) * (1 - v 0)) * e22 -
      ((1 - u 1) * (1 - v 1))^2 * e11
  have hu0 := (hw 0).1; have hu0' := (hw 0).2.1
  have hu1 := (hw 1).1; have hu1' := (hw 1).2.1
  have hv1 := (hy 1).1; have hv1' := (hy 1).2.1
  have hv2 := (hy 2).1; have hv2' := (hy 2).2.1
  have p1 : 0 ≤ (1 - u 0) * v 1 := mul_nonneg (by linarith) hv1
  have p2 : 0 ≤ u 1 * (1 - v 2) := mul_nonneg hu1 (by linarith)
  have p3 : 0 ≤ (1 - u 1) * (1 - v 1) := mul_nonneg (by linarith) (by linarith)
  have r1 : (1 - u 0) * v 1 = 3 / 8 := by nlinarith only [m1, p1]
  have r2 : u 1 * (1 - v 2) = 3 / 8 := by nlinarith only [m2, p2]
  have r3 : (1 - u 1) * (1 - v 1) = 9 / 16 := by nlinarith only [m3, p3]
  have hv1_lb : 3 / 8 ≤ v 1 := by nlinarith only [r1, hu0, hv1]
  have hu1_lb : 3 / 8 ≤ u 1 := by nlinarith only [r2, hv2, hu1]
  nlinarith only [r3, hv1_lb, hu1_lb, hv1', hu1']

theorem counterexample : InA4 2 2 2 2 P P P Q ∧ Orthogonal Q ∧ ¬ InA4Orth 2 2 2 2 P P P Q := by
  refine ⟨Q_mem_A4, Q_orthogonal, fun ⟨B₁, B₂, B₃, B₄, hb₁, hb₂, hb₃, hb₄, ho₁, ho₂, ho₃, ho₄, he⟩ =>
    Qc_not_unitary4 ⟨ofRealMatrix B₁, ofRealMatrix B₂, ofRealMatrix B₃, ofRealMatrix B₄,
      ofRealMatrix_blockDiagonal hb₁, ofRealMatrix_blockDiagonal hb₂,
      ofRealMatrix_blockDiagonal hb₃, ofRealMatrix_blockDiagonal hb₄,
      ofRealMatrix_unitary ho₁, ofRealMatrix_unitary ho₂,
      ofRealMatrix_unitary ho₃, ofRealMatrix_unitary ho₄, ?_⟩⟩
  simpa only [GS.product4, GS.UnitaryGeometry.product4, ofRealMatrix_mul] using congrArg ofRealMatrix he

end GS.M4

namespace GS.UnitaryFour
open GS.UnitaryGeometry

def Q : CMat 6 := ofRealMatrix GS.M4.Q

theorem counterexample :
    let Pc : CMat 6 := fun i j => (GS.M4.P i j : ℂ)
    CInA4 2 2 2 2 Pc Pc Pc Q ∧ Unitary Q ∧ ¬ CInA4Unitary 2 2 2 2 Pc Pc Pc Q := by
  change CInA4 2 2 2 2 (ofRealMatrix GS.M4.P) (ofRealMatrix GS.M4.P) (ofRealMatrix GS.M4.P) Q ∧ _
  rcases GS.M4.Q_mem_A4 with ⟨B₁, B₂, B₃, B₄, hb₁, hb₂, hb₃, hb₄, he⟩
  refine ⟨⟨ofRealMatrix B₁, ofRealMatrix B₂, ofRealMatrix B₃, ofRealMatrix B₄,
    ofRealMatrix_blockDiagonal hb₁, ofRealMatrix_blockDiagonal hb₂,
    ofRealMatrix_blockDiagonal hb₃, ofRealMatrix_blockDiagonal hb₄, ?_⟩,
    ofRealMatrix_unitary GS.M4.Q_orthogonal, GS.M4.Qc_not_unitary4⟩
  simpa only [Q, GS.product4, GS.UnitaryGeometry.product4, ofRealMatrix_mul] using congrArg ofRealMatrix he

end GS.UnitaryFour
