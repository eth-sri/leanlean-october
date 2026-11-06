module

public import GS.UnitaryTopology.MatrixNonmanifold
public import GS.SharedGeometry.GradientSection
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Tactic.Choose

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
open Matrix
open scoped BigOperators Manifold ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GS.M4
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

def P : Mat 6 := !![1, 0, 0, 0, 0, 0;
  0, 0, 1, 0, 0, 0;
  0, 0, 0, 0, 1, 0;
  0, 1, 0, 0, 0, 0;
  0, 0, 0, 1, 0, 0;
  0, 0, 0, 0, 0, 1]

def B2 : Mat 6 := !![1, 1, 0, 0, 0, 0;
  1, -3, 0, 0, 0, 0;
  0, 0, 1, 1, 0, 0;
  0, 0, 1, (-1/3 : ℝ), 0, 0;
  0, 0, 0, 0, 1, 1;
  0, 0, 0, 0, 1, (1/3 : ℝ)]

def B3 : Mat 6 := !![1, 1, 0, 0, 0, 0;
  1, (1/3 : ℝ), 0, 0, 0, 0;
  0, 0, 1, 1, 0, 0;
  0, 0, 1, (-1/3 : ℝ), 0, 0;
  0, 0, 0, 0, 1, 1;
  0, 0, 0, 0, 1, -3]

def C : Mat 6 := !![1, 1, 1, 0, 1, 0;
  1, 0, -3, 1, 0, 1;
  0, (-1/3 : ℝ), 0, 1, 1, (1/3 : ℝ);
  1, (1/3 : ℝ), 1, 0, (1/3 : ℝ), 0;
  (-1/3 : ℝ), 0, 1, 1, 0, 1;
  0, (-1/3 : ℝ), 0, -3, 1, -1]

def H : Mat 6 := !![(7/4 : ℝ), -3, 0, 0, 0, 0;
  -3, (21/4 : ℝ), 0, 0, 0, 0;
  0, 0, (1/4 : ℝ), (1/3 : ℝ), 0, 0;
  0, 0, (1/3 : ℝ), (1/2 : ℝ), 0, 0;
  0, 0, 0, 0, (3/4 : ℝ), -1;
  0, 0, 0, 0, -1, (3/2 : ℝ)]

def G : Mat 6 := !![2, (-8/3 : ℝ), 0, 0, 0, 0;
  (-8/3 : ℝ), 4, 0, 0, 0, 0;
  0, 0, (4/3 : ℝ), (8/9 : ℝ), 0, 0;
  0, 0, (8/9 : ℝ), (2/3 : ℝ), 0, 0;
  0, 0, 0, 0, (28/9 : ℝ), (-16/3 : ℝ);
  0, 0, 0, 0, (-16/3 : ℝ), (28/3 : ℝ)]

def B1Param (s2 s3 s7 : ℝ) : Mat 6 := !![((1/2 : ℝ) * s7), 0, 0, 0, 0, 0;
  ((-6/7 : ℝ) * s7), ((1/14 : ℝ) * s3 * s7), 0, 0, 0, 0;
  0, 0, (1/2 : ℝ), 0, 0, 0;
  0, 0, (2/3 : ℝ), ((1/6 : ℝ) * s2), 0, 0;
  0, 0, 0, 0, ((1/2 : ℝ) * s3), 0;
  0, 0, 0, 0, ((-2/3 : ℝ) * s3), ((1/6 : ℝ) * s2 * s3)]

def B4Param (s2 s3 s7 : ℝ) : Mat 6 := !![((1/2 : ℝ) * s2), 0, 0, 0, 0, 0;
  2, (3/2 : ℝ), 0, 0, 0, 0;
  0, 0, ((1/2 : ℝ) * s3), 0, 0, 0;
  0, 0, (-1 * s2 * s3), ((3/2 : ℝ) * s2 * s3), 0, 0;
  0, 0, 0, 0, ((3/14 : ℝ) * s7), 0;
  0, 0, 0, 0, ((6/7 : ℝ) * s3 * s7), ((1/2 : ℝ) * s3 * s7)]

theorem core_identity : P * B3 * P * B2 * P = C := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [P, B2, B3, C, Matrix.mul_apply, Fin.sum_univ_succ]

theorem metric_identity : C * H * Cᵀ = G := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [C, H, G, Matrix.mul_apply, Fin.sum_univ_succ]

theorem gram_B1 (s2 s3 s7 : ℝ) (h2 : s2 ^ 2 = 2) (h3 : s3 ^ 2 = 3) (h7 : s7 ^ 2 = 7) :
    B1Param s2 s3 s7 * (B1Param s2 s3 s7)ᵀ = H := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [B1Param, H, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring_nf <;> norm_num [h2, h3, h7]

theorem normalize_B4 (s2 s3 s7 : ℝ) (h2 : s2 ^ 2 = 2) (h3 : s3 ^ 2 = 3) (h7 : s7 ^ 2 = 7) :
    B4Param s2 s3 s7 * G * (B4Param s2 s3 s7)ᵀ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [B4Param, G, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;> ring_nf <;> norm_num [h2, h3, h7]

def B1 : Mat 6 := B1Param (Real.sqrt 2) (Real.sqrt 3) (Real.sqrt 7)
def B4 : Mat 6 := B4Param (Real.sqrt 2) (Real.sqrt 3) (Real.sqrt 7)
def Q : Mat 6 := B4 * C * B1

theorem sqrt2_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
theorem sqrt3_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
theorem sqrt7_sq : (Real.sqrt 7) ^ 2 = (7 : ℝ) := Real.sq_sqrt (by norm_num)

theorem Q_orthogonal : Orthogonal Q :=
  gram_completion C H G B1 B4 metric_identity
    (gram_B1 _ _ _ sqrt2_sq sqrt3_sq sqrt7_sq)
    (normalize_B4 _ _ _ sqrt2_sq sqrt3_sq sqrt7_sq)

theorem Q_mem_A4 : InA4 2 2 2 2 P P P Q :=
  ⟨B1, B2, B3, B4,
    fun i j hij => by fin_cases i <;> fin_cases j <;> norm_num [B1, B1Param] at *,
    fun i j hij => by fin_cases i <;> fin_cases j <;> norm_num [B2] at *,
    fun i j hij => by fin_cases i <;> fin_cases j <;> norm_num [B3] at *,
    fun i j hij => by fin_cases i <;> fin_cases j <;> norm_num [B4, B4Param] at *,
    by unfold Q product4; rw [← core_identity]; simp only [Matrix.mul_assoc]⟩

def cell (i : Fin 3) (a : Fin 2) : Fin 6 := ⟨2 * i.val + a.val, by omega⟩
def detBlock (M : Mat 6) (i j : Fin 3) : ℝ :=
  M (cell i 0) (cell j 0) * M (cell i 1) (cell j 1) -
  M (cell i 0) (cell j 1) * M (cell i 1) (cell j 0)

def detTable (s2 s3 : ℝ) : Mat 3 := !![((-3/16 : ℝ) * s2 * s3), (1/8 : ℝ), (3/8 : ℝ);
  ((3/16 : ℝ) * s2 * s3), (-3/8 : ℝ), (-1/8 : ℝ);
  (1/16 : ℝ), ((-3/16 : ℝ) * s2 * s3), ((-3/16 : ℝ) * s2 * s3)]

theorem detTable_Q : (fun i j => detBlock Q i j) = detTable (Real.sqrt 2) (Real.sqrt 3) := by
  have h2 := sqrt2_sq; have h3 := sqrt3_sq; have h7 := sqrt7_sq
  have h33 : (Real.sqrt 3) ^ 3 = 3 * Real.sqrt 3 := by linear_combination Real.sqrt 3 * h3
  have h34 : (Real.sqrt 3) ^ 4 = 9 := by nlinarith [h3]
  have h74 : (Real.sqrt 7) ^ 4 = 49 := by nlinarith [h7]
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [Q, B1, B4, detBlock, cell, B4Param, B1Param, C, detTable, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> norm_num [h2, h3, h7, h33, h34, h74] <;> ring

theorem scalar_obstruction (a b e f c g : ℝ)
    (ha : a ^ 2 + c ^ 2 = 1) (he : e ^ 2 + g ^ 2 = 1) (hb : b ^ 2 ≤ 1) (hf : f ^ 2 ≤ 1) :
    0 ≤ (1 - b ^ 2 * e ^ 2) * (1 - a ^ 2 * f ^ 2) - c ^ 2 * g ^ 2 := by
  have ha' : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg c]
  have he' : e ^ 2 ≤ 1 := by nlinarith [sq_nonneg g]
  have haf : 0 ≤ 1 - a ^ 2 * f ^ 2 := by nlinarith [mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hf)]
  have h1 := mul_nonneg (mul_nonneg (sq_nonneg e) (sub_nonneg.mpr hb)) haf
  have h2 := mul_nonneg (mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hf)) (sub_nonneg.mpr he')
  nlinarith [h1, h2]

end GS.M4

namespace GS.UnitaryGeometry

def product4 {n : ℕ} (B₄ P₃ B₃ P₂ B₂ P₁ B₁ : CMat n) : CMat n :=
  B₄ * P₃ * B₃ * P₂ * B₂ * P₁ * B₁

def CInA4 {n : ℕ} (b₁ b₂ b₃ b₄ : ℕ) (P₁ P₂ P₃ A : CMat n) : Prop :=
  ∃ B₁ B₂ B₃ B₄, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    CBlockDiagonal b₃ B₃ ∧ CBlockDiagonal b₄ B₄ ∧
    A = product4 B₄ P₃ B₃ P₂ B₂ P₁ B₁

def CInA4Unitary {n : ℕ} (b₁ b₂ b₃ b₄ : ℕ) (P₁ P₂ P₃ A : CMat n) : Prop :=
  ∃ B₁ B₂ B₃ B₄, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    CBlockDiagonal b₃ B₃ ∧ CBlockDiagonal b₄ B₄ ∧
    Unitary B₁ ∧ Unitary B₂ ∧ Unitary B₃ ∧ Unitary B₄ ∧
    A = product4 B₄ P₃ B₃ P₂ B₂ P₁ B₁

end GS.UnitaryGeometry

namespace GS.UnitaryFour
open GS.UnitaryGeometry
set_option maxRecDepth 4096
set_option maxHeartbeats 500000

def P : CMat 6 := ofRealMatrix GS.M4.P
def cell (i : Fin 3) (a : Fin 2) : Fin 6 := ⟨2 * i.val + a.val, by omega⟩

def detBlock (M : CMat 6) (i j : Fin 3) : ℂ :=
  M (cell i 0) (cell j 0) * M (cell i 1) (cell j 1) -
  M (cell i 0) (cell j 1) * M (cell i 1) (cell j 0)

def normDetBlock (A : CMat 6) (i j : Fin 3) : ℝ := ‖detBlock A i j‖

def determinantObstruction (A : CMat 6) : Prop :=
  let d := normDetBlock A
  0 ≤ (d 2 1 - d 0 2 * d 1 0) * (d 1 0 - d 0 2 * d 2 1) * d 1 1 - d 0 0 * d 2 2 * d 2 1 * d 1 0

def block2 (A : CMat 6) (i j : Fin 3) : CMat 2 := A.submatrix (cell i) (cell j)

def assemble (A : Fin 3 → CMat 2) : CMat 6 :=
  !![A 0 0 0, A 0 0 1, 0, 0, 0, 0;
     A 0 1 0, A 0 1 1, 0, 0, 0, 0;
     0, 0, A 1 0 0, A 1 0 1, 0, 0;
     0, 0, A 1 1 0, A 1 1 1, 0, 0;
     0, 0, 0, 0, A 2 0 0, A 2 0 1;
     0, 0, 0, 0, A 2 1 0, A 2 1 1]

theorem block_diagonal_decompose (A : CMat 6) (hA : CBlockDiagonal 2 A) :
    A = assemble (fun i => block2 A i i) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [assemble, block2, cell] <;> apply hA <;> decide

theorem block2_outer (A C B : CMat 6) (hA : CBlockDiagonal 2 A)
    (hB : CBlockDiagonal 2 B) (i j : Fin 3) :
    block2 (A * C * B) i j = block2 A i i * block2 C i j * block2 B j j := by
  have hL (X : Fin 3 → CMat 2) (M : CMat 6) (u v : Fin 3) :
      block2 (assemble X * M) u v = X u * block2 M u v := by
    ext a b; fin_cases u <;> fin_cases v <;> fin_cases a <;> fin_cases b <;>
      simp [block2, cell, assemble, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  have hR (M : CMat 6) (Y : Fin 3 → CMat 2) (u v : Fin 3) :
      block2 (M * assemble Y) u v = block2 M u v * Y v := by
    ext a b; fin_cases u <;> fin_cases v <;> fin_cases a <;> fin_cases b <;>
      simp [block2, cell, assemble, Matrix.mul_apply, Fin.sum_univ_succ]
  conv_lhs => rw [block_diagonal_decompose A hA, block_diagonal_decompose B hB]
  rw [hR, hL]

theorem block2_unitary (A : CMat 6) (hA : CBlockDiagonal 2 A)
    (ho : Unitary A) (r : Fin 3) : Unitary (block2 A r r) := by
  suffices hh : (block2 A r r)ᴴ * block2 A r r = 1 from ⟨hh, mul_eq_one_comm.mp hh⟩
  have ha := block_diagonal_decompose A hA
  ext i j
  have h := congrFun (congrFun ho.1 (cell r i)) (cell r j)
  rw [ha] at h
  fin_cases r <;> fin_cases i <;> fin_cases j <;>
    simpa [block2, cell, assemble, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fin.sum_univ_succ] using h

theorem norm_det_unitary {n : ℕ} (U : CMat n) (hU : Unitary U) : ‖U.det‖ = 1 := by
  have hs : ‖U.det‖ ^ 2 = (1 : ℝ) := by
    simpa [Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, pow_two] using
      congrArg (fun A : CMat n => ‖A.det‖) hU.1
  nlinarith [norm_nonneg U.det]

theorem normDetBlock_outer (A C B : CMat 6)
    (hA : CBlockDiagonal 2 A) (hB : CBlockDiagonal 2 B)
    (hoA : Unitary A) (hoB : Unitary B) (i j : Fin 3) :
    normDetBlock (A * C * B) i j = normDetBlock C i j := by
  have hdet (M : CMat 6) : detBlock M i j = (block2 M i j).det := by rw [Matrix.det_fin_two]; rfl
  unfold normDetBlock
  rw [hdet (A * C * B), hdet C, block2_outer A C B hA hB i j,
    Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul,
    norm_det_unitary _ (block2_unitary A hA hoA i),
    norm_det_unitary _ (block2_unitary B hB hoB j)]
  ring

theorem unitary2_norm (W : CMat 2) (hW : Unitary W) :
    ‖W 1 0‖ = ‖W 0 1‖ ∧ ‖W 1 1‖ = ‖W 0 0‖ ∧ ‖W 0 0‖ ^ 2 + ‖W 0 1‖ ^ 2 = 1 := by
  have hc (k : Fin 2) : ‖W 0 k‖ ^ 2 + ‖W 1 k‖ ^ 2 = 1 := by
    simp only [Complex.sq_norm]
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      Fin.sum_univ_succ, Complex.mul_re, Complex.normSq_apply] using
      congrArg Complex.re (congrFun (congrFun hW.1 k) k)
  have hr0 : ‖W 0 0‖ ^ 2 + ‖W 0 1‖ ^ 2 = 1 := by
    simp only [Complex.sq_norm]
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      Fin.sum_univ_succ, Complex.mul_re, Complex.normSq_apply] using
      congrArg Complex.re (congrFun (congrFun hW.2 0) 0)
  have hc0 := hc 0; have hc1 := hc 1
  exact ⟨(sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by linarith),
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by linarith), hr0⟩

def coreDetTable (W Y : Fin 3 → CMat 2) : CMat 3 :=
  !![-W 0 0 1*W 1 0 1*Y 1 0 1*Y 0 1 0,
      W 0 0 0*W 1 0 0*Y 2 0 0*Y 0 0 1,
      W 1 0 0*W 0 0 1*Y 1 0 0*Y 2 0 1;
     -W 2 0 0*W 0 1 0*Y 0 0 0*Y 1 1 1,
     -W 2 0 1*W 0 1 0*Y 0 0 1*Y 2 1 0,
     -W 2 0 1*W 0 1 1*Y 1 0 0*Y 2 1 1;
      W 2 1 0*W 1 1 1*Y 0 1 0*Y 1 1 1,
      W 1 1 1*W 2 1 1*Y 2 1 0*Y 0 1 1,
     -W 1 1 0*W 2 1 0*Y 2 0 1*Y 1 1 0]

def canonicalDetTable (a b e f : Fin 3 → ℝ) : Mat 3 :=
  !![b 0*b 1*f 1*f 0, a 0*a 1*e 2*f 0, a 1*b 0*e 1*f 2;
     a 2*b 0*e 0*e 1, b 2*b 0*f 0*f 2, b 2*a 0*e 1*e 2;
     b 2*a 1*f 0*e 1, a 1*a 2*f 2*e 0, b 1*b 2*f 2*f 1]

theorem core_normDetTable (W Y : Fin 3 → CMat 2)
    (hW : ∀ i, Unitary (W i)) (hY : ∀ i, Unitary (Y i)) :
    normDetBlock (P * assemble W * P * assemble Y * P) =
      canonicalDetTable (fun i => ‖W i 0 0‖) (fun i => ‖W i 0 1‖)
        (fun i => ‖Y i 0 0‖) (fun i => ‖Y i 0 1‖) := by
  have h_core : (fun i j => detBlock (P * assemble W * P * assemble Y * P) i j) = coreDetTable W Y := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [detBlock, cell, GS.M4.cell, P, GS.M4.P, ofRealMatrix, assemble, coreDetTable,
        Matrix.mul_apply, Fin.sum_univ_succ] <;> ring
  ext i j
  have hw0 := unitary2_norm (W 0) (hW 0); have hw1 := unitary2_norm (W 1) (hW 1); have hw2 := unitary2_norm (W 2) (hW 2)
  have hy0 := unitary2_norm (Y 0) (hY 0); have hy1 := unitary2_norm (Y 1) (hY 1); have hy2 := unitary2_norm (Y 2) (hY 2)
  unfold normDetBlock
  rw [congrFun (congrFun h_core i) j]
  fin_cases i <;> fin_cases j <;>
    simp [coreDetTable, canonicalDetTable,
      hw0.1, hw0.2.1, hw1.1, hw1.2.1, hw2.1, hw2.2.1,
      hy0.1, hy0.2.1, hy1.1, hy1.2.1, hy2.1, hy2.2.1]

theorem necessaryCondition (A : CMat 6) (h : CInA4Unitary 2 2 2 2 P P P A) :
    determinantObstruction A := by
  rcases h with ⟨B₁, B₂, B₃, B₄, hb₁, hb₂, hb₃, hb₄, ho₁, ho₂, ho₃, ho₄, he⟩
  let W := fun i => block2 B₃ i i
  let Y := fun i => block2 B₂ i i
  let C₀ := P * assemble W * P * assemble Y * P
  have he' : A = B₄ * C₀ * B₁ := by
    rw [he, block_diagonal_decompose B₃ hb₃, block_diagonal_decompose B₂ hb₂]
    simp only [GS.UnitaryGeometry.product4, C₀, W, Y, Matrix.mul_assoc]
  have hd : normDetBlock A = canonicalDetTable (fun i => ‖W i 0 0‖) (fun i => ‖W i 0 1‖)
      (fun i => ‖Y i 0 0‖) (fun i => ‖Y i 0 1‖) := by
    rw [← core_normDetTable W Y (block2_unitary B₃ hb₃ ho₃) (block2_unitary B₂ hb₂ ho₂)]
    funext i j; rw [he']; exact normDetBlock_outer B₄ C₀ B₁ hb₄ hb₁ ho₄ ho₁ i j
  let d := canonicalDetTable (fun i => ‖W i 0 0‖) (fun i => ‖W i 0 1‖)
    (fun i => ‖Y i 0 0‖) (fun i => ‖Y i 0 1‖)
  have hd_nonneg (i j : Fin 3) : 0 ≤ d i j := by
    rw [show d = normDetBlock A from hd.symm]; exact norm_nonneg _
  unfold determinantObstruction
  rw [hd]
  change 0 ≤ (d 2 1 - d 0 2 * d 1 0) * (d 1 0 - d 0 2 * d 2 1) * d 1 1 - d 0 0 * d 2 2 * d 2 1 * d 1 0
  have h_poly : (d 2 1 - d 0 2 * d 1 0) * (d 1 0 - d 0 2 * d 2 1) * d 1 1 - d 0 0 * d 2 2 * d 2 1 * d 1 0 =
      d 2 1 * d 1 0 * d 1 1 * ((1 - ‖W 0 0 1‖ ^ 2 * ‖Y 1 0 0‖ ^ 2) * (1 - ‖W 1 0 0‖ ^ 2 * ‖Y 2 0 1‖ ^ 2) -
        ‖W 1 0 1‖ ^ 2 * ‖Y 1 0 1‖ ^ 2) := by
    simp [d, canonicalDetTable]; ring
  rw [h_poly]
  have hW_n (i : Fin 3) := (unitary2_norm (W i) (block2_unitary B₃ hb₃ ho₃ i)).2.2
  have hY_n (i : Fin 3) := (unitary2_norm (Y i) (block2_unitary B₂ hb₂ ho₂ i)).2.2
  exact mul_nonneg (mul_nonneg (mul_nonneg (hd_nonneg 2 1) (hd_nonneg 1 0)) (hd_nonneg 1 1))
    (GS.M4.scalar_obstruction _ _ _ _ _ _ (hW_n 1) (hY_n 1)
      (by nlinarith [hW_n 0, sq_nonneg ‖W 0 0 0‖]) (by nlinarith [hY_n 2, sq_nonneg ‖Y 2 0 0‖]))

theorem ofRealMatrix_inA4 {n : ℕ} {b₁ b₂ b₃ b₄ : ℕ} {P₁ P₂ P₃ A : Mat n}
    (h : InA4 b₁ b₂ b₃ b₄ P₁ P₂ P₃ A) :
    CInA4 b₁ b₂ b₃ b₄ (ofRealMatrix P₁) (ofRealMatrix P₂)
      (ofRealMatrix P₃) (ofRealMatrix A) := by
  rcases h with ⟨B₁, B₂, B₃, B₄, hb₁, hb₂, hb₃, hb₄, he⟩
  refine ⟨ofRealMatrix B₁, ofRealMatrix B₂, ofRealMatrix B₃, ofRealMatrix B₄,
    ofRealMatrix_blockDiagonal hb₁, ofRealMatrix_blockDiagonal hb₂,
    ofRealMatrix_blockDiagonal hb₃, ofRealMatrix_blockDiagonal hb₄, ?_⟩
  simpa only [GS.product4, GS.UnitaryGeometry.product4, ofRealMatrix_mul] using
    congrArg ofRealMatrix he

def Q : CMat 6 := ofRealMatrix GS.M4.Q

theorem Q_unitary : Unitary Q := ofRealMatrix_unitary GS.M4.Q_orthogonal

theorem Q_mem_A4 : CInA4 2 2 2 2 P P P Q :=
  ofRealMatrix_inA4 GS.M4.Q_mem_A4

theorem Q_not_mem_A4Unitary : ¬ CInA4Unitary 2 2 2 2 P P P Q := by
  intro h
  have hn := necessaryCondition Q h
  have h_abs (i j : Fin 3) : normDetBlock Q i j = |GS.M4.detTable (Real.sqrt 2) (Real.sqrt 3) i j| := by
    rw [← congrFun (congrFun GS.M4.detTable_Q i) j]
    simp only [Q, normDetBlock, detBlock, GS.M4.detBlock, cell, GS.M4.cell,
      ofRealMatrix_apply, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  unfold determinantObstruction at hn
  simp only [h_abs, GS.M4.detTable] at hn
  norm_num [abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2), abs_of_nonneg (Real.sqrt_nonneg 3)] at hn
  have h6 : (Real.sqrt 2 * Real.sqrt 3) ^ 2 = 6 := by
    rw [mul_pow, GS.M4.sqrt2_sq, GS.M4.sqrt3_sq]; norm_num
  nlinarith [h6]

theorem counterexample : CInA4 2 2 2 2 P P P Q ∧ Unitary Q ∧
    ¬ CInA4Unitary 2 2 2 2 P P P Q :=
  ⟨Q_mem_A4, Q_unitary, Q_not_mem_A4Unitary⟩

theorem real_counterexample : InA4 2 2 2 2 GS.M4.P GS.M4.P GS.M4.P GS.M4.Q ∧
    Orthogonal GS.M4.Q ∧ ¬ InA4Orth 2 2 2 2 GS.M4.P GS.M4.P GS.M4.P GS.M4.Q :=
  ⟨GS.M4.Q_mem_A4, GS.M4.Q_orthogonal, fun ⟨B₁, B₂, B₃, B₄, hb₁, hb₂, hb₃, hb₄, ho₁, ho₂, ho₃, ho₄, he⟩ =>
    Q_not_mem_A4Unitary ⟨ofRealMatrix B₁, ofRealMatrix B₂, ofRealMatrix B₃, ofRealMatrix B₄,
      ofRealMatrix_blockDiagonal hb₁, ofRealMatrix_blockDiagonal hb₂,
      ofRealMatrix_blockDiagonal hb₃, ofRealMatrix_blockDiagonal hb₄,
      ofRealMatrix_unitary ho₁, ofRealMatrix_unitary ho₂,
      ofRealMatrix_unitary ho₃, ofRealMatrix_unitary ho₄,
      by simpa only [Q, P, GS.product4, GS.UnitaryGeometry.product4, ofRealMatrix_mul] using
        congrArg ofRealMatrix he⟩⟩

end GS.UnitaryFour

open InnerProductSpace GS.NonmanifoldCompletion
open scoped BigOperators ComplexConjugate

namespace GS.UnitaryCS

variable {𝕂 : Type} [RCLike 𝕂]

abbrev KMat (𝕂 : Type) (n : ℕ) := Matrix (Fin n) (Fin n) 𝕂

def IsUnitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι 𝕂) : Prop := Aᴴ * A = 1 ∧ A * Aᴴ = 1

namespace IsUnitary
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι 𝕂}
theorem of_conjTranspose_mul (h : Aᴴ * A = 1) : IsUnitary A :=
  ⟨h, mul_eq_one_comm.mp h⟩
theorem one : IsUnitary (1 : Matrix ι ι 𝕂) := ⟨by simp, by simp⟩
theorem conjTranspose (h : IsUnitary A) : IsUnitary Aᴴ := ⟨by simpa using h.2, by simpa using h.1⟩
theorem mul (hA : IsUnitary A) (hB : IsUnitary B) : IsUnitary (A * B) :=
  ⟨by calc (A * B)ᴴ * (A * B) = Bᴴ * (Aᴴ * A) * B := by simp [Matrix.mul_assoc]
        _ = 1 := by rw [hA.1, Matrix.mul_one, hB.1],
   by calc (A * B) * (A * B)ᴴ = A * (B * Bᴴ) * Aᴴ := by simp [Matrix.mul_assoc]
        _ = 1 := by rw [hB.2, Matrix.mul_one, hA.2]⟩
end IsUnitary

theorem exists_unitary_mul_diagonal {n : ℕ} (A : KMat 𝕂 n) (d : Fin n → ℝ)
    (hA : Aᴴ * A = diagonal (fun i => (d i : 𝕂) ^ 2)) :
    ∃ U : KMat 𝕂 n, IsUnitary U ∧ A = U * diagonal (fun i => (d i : 𝕂)) := by
  classical
  let e₀ := EuclideanSpace.basisFun (Fin n) 𝕂
  let f : Fin n → EuclideanSpace 𝕂 (Fin n) := fun j => ∑ k, A k j • e₀ k
  have hcoords (i j : Fin n) : ⟪e₀ i, f j⟫_𝕂 = A i j := by
    simp [f, inner_sum, inner_smul_right, orthonormal_iff_ite.mp e₀.orthonormal]
  have hgram (i j : Fin n) : ⟪f i, f j⟫_𝕂 = if i = j then (d i : 𝕂) ^ 2 else 0 := by
    calc ⟪f i, f j⟫_𝕂 = ∑ k, star (A k i) * A k j := by
          rw [← e₀.sum_inner_mul_inner (f i) (f j)]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← inner_conj_symm (f i) (e₀ k), hcoords, hcoords, RCLike.star_def]
      _ = (Aᴴ * A) i j := rfl
      _ = _ := by rw [hA]; simp [Matrix.diagonal_apply]
  let v : Fin n → EuclideanSpace 𝕂 (Fin n) := fun j => ((d j : 𝕂))⁻¹ • f j
  let s : Set (Fin n) := {i | d i ≠ 0}
  have hv : Orthonormal 𝕂 (s.restrict v) := by
    rw [orthonormal_iff_ite]; intro i j
    change ⟪((d i : 𝕂))⁻¹ • f i, ((d j : 𝕂))⁻¹ • f j⟫_𝕂 = _
    rw [inner_smul_left, inner_smul_right, hgram]
    by_cases hij : i = j
    · subst j; simp only [ite_true]
      have hd : (d i : 𝕂) ≠ 0 := by exact_mod_cast i.property
      simp [hd, pow_two]
    · simp [hij, show (i : Fin n) ≠ (j : Fin n) from fun h => hij (Subtype.ext h)]
  obtain ⟨e, he⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp : Module.finrank 𝕂 (EuclideanSpace 𝕂 (Fin n)) = Fintype.card (Fin n))
  let U : KMat 𝕂 n := fun i j => ⟪e₀ i, e j⟫_𝕂
  have hU : IsUnitary U := by
    apply IsUnitary.of_conjTranspose_mul; ext i j
    calc (Uᴴ * U) i j = ∑ k, ⟪e i, e₀ k⟫_𝕂 * ⟪e₀ k, e j⟫_𝕂 := by
          change (∑ k, star (⟪e₀ k, e i⟫_𝕂) * ⟪e₀ k, e j⟫_𝕂) = _
          simp only [RCLike.star_def, inner_conj_symm]
      _ = ⟪e i, e j⟫_𝕂 := e₀.sum_inner_mul_inner _ _
      _ = (1 : KMat 𝕂 n) i j := by simpa only [Matrix.one_apply] using orthonormal_iff_ite.mp e.orthonormal i j
  refine ⟨U, hU, ?_⟩
  ext i j; rw [Matrix.mul_diagonal]
  by_cases hd : d j = 0
  · have hf : f j = 0 := (inner_self_eq_zero (𝕜 := 𝕂)).mp ((hgram j j).trans (by simp [hd]))
    rw [hd]; simp [← hcoords, hf]
  · change A i j = ⟪e₀ i, e j⟫_𝕂 * (d j : 𝕂)
    rw [he j hd]
    change A i j = ⟪e₀ i, ((d j : 𝕂))⁻¹ • f j⟫_𝕂 * (d j : 𝕂)
    rw [inner_smul_right, hcoords]
    have hd' : (d j : 𝕂) ≠ 0 := by exact_mod_cast hd
    field_simp

theorem gram_diagonal_nonneg {n : ℕ} (A : KMat 𝕂 n) (d : Fin n → ℝ)
    (h : Aᴴ * A = diagonal (fun i => (d i : 𝕂))) (i : Fin n) : 0 ≤ d i := by
  have hi := congrArg RCLike.re (congrFun (congrFun h i) i)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq,
    RCLike.ofReal_re, map_sum] at hi
  rw [← hi]
  refine Finset.sum_nonneg fun j _ => ?_
  rw [show star (A j i) = (starRingEnd 𝕂) (A j i) from congrFun RCLike.star_def _,
    RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  positivity

theorem exists_thin_cs {n : ℕ} (A B : KMat 𝕂 n) (h : Aᴴ * A + Bᴴ * B = 1) :
    ∃ (U₁ U₂ V : KMat 𝕂 n) (c s : Fin n → ℝ),
      IsUnitary U₁ ∧ IsUnitary U₂ ∧ IsUnitary V ∧ (∀ i, c i ^ 2 + s i ^ 2 = 1) ∧
      A * V = U₁ * diagonal (fun i => (c i : 𝕂)) ∧
      B * V = U₂ * diagonal (fun i => (s i : 𝕂)) := by
  have hH : (Aᴴ * A).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self A
  let V : KMat 𝕂 n := hH.eigenvectorUnitary
  let d : Fin n → ℝ := hH.eigenvalues
  have hV : IsUnitary V := IsUnitary.of_conjTranspose_mul
    (by simpa only [V, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self hH.eigenvectorUnitary)
  have hAV : (A * V)ᴴ * (A * V) = diagonal (fun i => (d i : 𝕂)) := by
    simpa [Function.comp_def, Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose, V, d, Matrix.conjTranspose_mul, Matrix.mul_assoc] using
      hH.conjStarAlgAut_star_eigenvectorUnitary
  have hsum : (A * V)ᴴ * (A * V) + (B * V)ᴴ * (B * V) = 1 := by
    calc _ = Vᴴ * (Aᴴ * A + Bᴴ * B) * V := by simp [Matrix.conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 1 := by rw [h, Matrix.mul_one, hV.1]
  have hBV : (B * V)ᴴ * (B * V) = diagonal (fun i => ((1 - d i : ℝ) : 𝕂)) := by
    rw [hAV] at hsum; rw [eq_sub_of_add_eq' hsum]
    ext i j; by_cases hij : i = j <;> simp [hij]
  let c : Fin n → ℝ := fun i => Real.sqrt (d i)
  let s : Fin n → ℝ := fun i => Real.sqrt (1 - d i)
  have hc (i) : c i ^ 2 = d i := Real.sq_sqrt (gram_diagonal_nonneg _ _ hAV i)
  have hs (i) : s i ^ 2 = 1 - d i := Real.sq_sqrt (gram_diagonal_nonneg _ _ hBV i)
  obtain ⟨U₁, hU₁, he₁⟩ := exists_unitary_mul_diagonal (A * V) c (by simpa only [show ∀ i, (c i : 𝕂) ^ 2 = (d i : 𝕂) from fun i => by exact_mod_cast hc i] using hAV)
  obtain ⟨U₂, hU₂, he₂⟩ := exists_unitary_mul_diagonal (B * V) s (by simpa only [show ∀ i, (s i : 𝕂) ^ 2 = ((1 - d i : ℝ) : 𝕂) from fun i => by exact_mod_cast hs i] using hBV)
  exact ⟨U₁, U₂, V, c, s, hU₁, hU₂, hV, fun i => by rw [hc, hs]; ring, he₁, he₂⟩

@[simp] theorem star_real_function {n : ℕ} (d : Fin n → ℝ) :
    star (fun i => (d i : 𝕂)) = fun i => (d i : 𝕂) := by
  ext i; simp [RCLike.star_def]

def split {n : ℕ} (A B : KMat 𝕂 n) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) 𝕂 :=
  fromBlocks A 0 0 B

@[simp] theorem split_mul {n : ℕ} (A B C D : KMat 𝕂 n) :
    split A B * split C D = split (A * C) (B * D) := by
  simp [split, Matrix.fromBlocks_multiply]

@[simp] theorem split_conjTranspose {n : ℕ} (A B : KMat 𝕂 n) :
    (split A B)ᴴ = split Aᴴ Bᴴ := by simp [split, Matrix.fromBlocks_conjTranspose]

@[simp] theorem split_one (n : ℕ) : split (1 : KMat 𝕂 n) 1 = 1 := Matrix.fromBlocks_one

theorem split_unitary {n : ℕ} {A B : KMat 𝕂 n}
    (hA : IsUnitary A) (hB : IsUnitary B) : IsUnitary (split A B) :=
  ⟨by simp [hA.1, hB.1], by simp [hA.2, hB.2]⟩

def csMatrix (𝕂 : Type) [RCLike 𝕂] {n : ℕ} (c s : Fin n → ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) 𝕂 :=
  fromBlocks (diagonal (fun i => (c i : 𝕂))) (-diagonal (fun i => (s i : 𝕂)))
    (diagonal (fun i => (s i : 𝕂))) (diagonal (fun i => (c i : 𝕂)))

theorem csMatrix_unitary {n : ℕ} (c s : Fin n → ℝ)
    (h : ∀ i, c i ^ 2 + s i ^ 2 = 1) : IsUnitary (csMatrix 𝕂 c s) := by
  apply IsUnitary.of_conjTranspose_mul
  rw [csMatrix, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> by_cases hij : i = j
  all_goals simp [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.one_apply, hij]
  all_goals try ring1
  · exact_mod_cast (by linear_combination h j : c j * c j + s j * s j = 1)
  · exact_mod_cast (by linear_combination h j : s j * s j + c j * c j = 1)

theorem exists_square_cs {n : ℕ}
    (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) 𝕂) (hQ : IsUnitary Q) :
    ∃ (U₁ U₂ V₁ V₂ : KMat 𝕂 n) (c s : Fin n → ℝ),
      IsUnitary U₁ ∧ IsUnitary U₂ ∧ IsUnitary V₁ ∧ IsUnitary V₂ ∧
      (∀ i, c i ^ 2 + s i ^ 2 = 1) ∧
      Q = split U₁ U₂ * csMatrix 𝕂 c s * split V₁ V₂ := by
  let A := Q.toBlocks₁₁; let B := Q.toBlocks₁₂; let C := Q.toBlocks₂₁; let D := Q.toBlocks₂₂
  have hblocks : Q = fromBlocks A B C D := (Matrix.fromBlocks_toBlocks Q).symm
  have hfirst : Aᴴ * A + Cᴴ * C = 1 := by
    simpa [hblocks, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      ← Matrix.fromBlocks_one] using congrArg Matrix.toBlocks₁₁ hQ.1
  obtain ⟨U₁, U₂, V, c, s, hU₁, hU₂, hV, hcs, he₁, he₂⟩ := exists_thin_cs A C hfirst
  let L := split U₁ U₂; let T := split V (1 : KMat 𝕂 n); let K := csMatrix 𝕂 c s
  let E := U₁ᴴ * B; let F := U₂ᴴ * D
  let R := fromBlocks (diagonal (fun i => (c i : 𝕂))) E (diagonal (fun i => (s i : 𝕂))) F
  have hL : IsUnitary L := split_unitary hU₁ hU₂
  have hT : IsUnitary T := split_unitary hV IsUnitary.one
  have hK : IsUnitary K := csMatrix_unitary c s hcs
  have hleft₁ : U₁ᴴ * (A * V) = diagonal (fun i => (c i : 𝕂)) := by
    rw [he₁, ← Matrix.mul_assoc, hU₁.1, Matrix.one_mul]
  have hleft₂ : U₂ᴴ * (C * V) = diagonal (fun i => (s i : 𝕂)) := by
    rw [he₂, ← Matrix.mul_assoc, hU₂.1, Matrix.one_mul]
  have hR : R = Lᴴ * Q * T := by
    rw [hblocks]
    simp [R, L, T, split, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply, Matrix.mul_assoc, hleft₁, hleft₂, E, F]
  have hHo : IsUnitary (Kᴴ * R) := hK.conjTranspose.mul (hR ▸ (hL.conjTranspose.mul hQ).mul hT)
  let X := diagonal (fun i => (c i : 𝕂)) * E + diagonal (fun i => (s i : 𝕂)) * F
  let W := -diagonal (fun i => (s i : 𝕂)) * E + diagonal (fun i => (c i : 𝕂)) * F
  have hH : Kᴴ * R = fromBlocks 1 X 0 W := by
    simp [K, R, csMatrix, X, W, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Pi.star_def, RCLike.star_def]
    exact ⟨by ext i; simp; exact_mod_cast (by linear_combination hcs i : c i * c i + s i * s i = 1),
      by ext; simp; ring⟩
  have hX : X = 0 := by
    simpa [hH, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      ← Matrix.fromBlocks_one] using congrArg Matrix.toBlocks₁₂ hHo.1
  have hH' : Kᴴ * R = split 1 W := by simpa [split, hX] using hH
  have hW : IsUnitary W := IsUnitary.of_conjTranspose_mul (by
    simpa [hH', split, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      ← Matrix.fromBlocks_one] using congrArg Matrix.toBlocks₂₂ hHo.1)
  have hKR : R = K * split 1 W := by rw [← hH', ← Matrix.mul_assoc, hK.2, Matrix.one_mul]
  refine ⟨U₁, U₂, Vᴴ, W, c, s, hU₁, hU₂, hV.conjTranspose, hW, hcs, ?_⟩
  calc Q = (L * Lᴴ) * Q * (T * Tᴴ) := by rw [hL.2, hT.2]; simp
    _ = L * R * Tᴴ := by rw [hR]; simp only [Matrix.mul_assoc]
    _ = L * K * (split (1 : KMat 𝕂 n) W * Tᴴ) := by rw [hKR]; simp only [Matrix.mul_assoc]
    _ = _ := by simp [T, L, K]

def KBlockDiagonal {n : ℕ} (b : ℕ) (A : KMat 𝕂 n) : Prop :=
  ∀ i j, i.val / b ≠ j.val / b → A i j = 0

def kPermMatrix (𝕂 : Type) [RCLike 𝕂] {n : ℕ} (σ : Equiv.Perm (Fin n)) : KMat 𝕂 n :=
  fun i j => if i = σ j then 1 else 0

theorem kPerm_unitary {n : ℕ} (σ : Equiv.Perm (Fin n)) : IsUnitary (kPermMatrix 𝕂 σ) := by
  apply IsUnitary.of_conjTranspose_mul; ext i j
  simp [kPermMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm]

theorem kPerm_conjugate_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (A : KMat 𝕂 n) (i j : Fin n) :
    (kPermMatrix 𝕂 σ * A * (kPermMatrix 𝕂 σ)ᴴ) i j = A (σ.symm i) (σ.symm j) := by
  simp only [kPermMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, ← σ.symm_apply_eq]; simp

def KInA3Unitary {n : ℕ} (b₁ b₂ b₃ : ℕ) (P₁ P₂ A : KMat 𝕂 n) : Prop :=
  ∃ B₁ B₂ B₃, KBlockDiagonal b₁ B₁ ∧ KBlockDiagonal b₂ B₂ ∧ KBlockDiagonal b₃ B₃ ∧
    IsUnitary B₁ ∧ IsUnitary B₂ ∧ IsUnitary B₃ ∧ A = B₃ * P₂ * B₂ * P₁ * B₁

def twoProdSumEquiv (p : ℕ) : (Fin 2 × Fin p) ≃ (Fin p ⊕ Fin p) where
  toFun x := if x.1 = 0 then Sum.inl x.2 else Sum.inr x.2
  invFun x := Sum.elim (fun i => (0, i)) (fun i => (1, i)) x
  left_inv := by rintro ⟨a, i⟩; fin_cases a <;> simp
  right_inv := by intro x; cases x <;> simp

def squareFlatten {p : ℕ} (A : Matrix (Fin p ⊕ Fin p) (Fin p ⊕ Fin p) 𝕂) : KMat 𝕂 (2 * p) :=
  A.submatrix (finProdFinEquiv.symm.trans (twoProdSumEquiv p))
    (finProdFinEquiv.symm.trans (twoProdSumEquiv p))

theorem squareFlatten_mul {p : ℕ} (A B : Matrix (Fin p ⊕ Fin p) (Fin p ⊕ Fin p) 𝕂) :
    squareFlatten (A * B) = squareFlatten A * squareFlatten B :=
  (Matrix.submatrix_mul_equiv A B _ _ _).symm

theorem submatrix_unitary {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) {A : Matrix κ κ 𝕂} (hA : IsUnitary A) : IsUnitary (A.submatrix e e) :=
  IsUnitary.of_conjTranspose_mul <| by
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hA.1]
    exact Matrix.submatrix_one_equiv _

theorem squareFlatten_split_blockDiagonal {p : ℕ} (A B : KMat 𝕂 p) :
    KBlockDiagonal p (squareFlatten (split A B)) := by
  intro i j hij
  let x := finProdFinEquiv.symm i; let y := finProdFinEquiv.symm j
  have hxy : x.1 ≠ y.1 := fun h => by
    have hi := flat_block_label x; have hj := flat_block_label y
    simp only [x, y, Equiv.apply_symm_apply] at hi hj
    exact hij (hi.trans ((congrArg Fin.val h).trans hj.symm))
  change (split A B) (twoProdSumEquiv p x) (twoProdSumEquiv p y) = 0
  rcases x with ⟨a, u⟩; rcases y with ⟨b, v⟩
  fin_cases a <;> fin_cases b <;> simp [split, twoProdSumEquiv] at hxy ⊢

theorem shuffled_square_cs_blockDiagonal {p : ℕ} (c s : Fin p → ℝ) :
    KBlockDiagonal 2
      (kPermMatrix 𝕂 (scalarShuffle 2 p) * squareFlatten (csMatrix 𝕂 c s) *
        (kPermMatrix 𝕂 (scalarShuffle 2 p))ᴴ) := by
  have h_lbl (k : Fin (2 * p)) : (scalarShuffle 2 p k).val / 2 = (finProdFinEquiv.symm k).2.val := by
    have hcast {m n : ℕ} (h : m = n) (a : Fin m) : (cast (congrArg Fin h) a).val = a.val := by cases h; rfl
    exact (hcast (Nat.mul_comm p 2) _).symm ▸ flat_block_label ((finProdFinEquiv.symm k).2, (finProdFinEquiv.symm k).1)
  intro i j hij
  let σ := scalarShuffle 2 p
  let x := finProdFinEquiv.symm (σ.symm i); let y := finProdFinEquiv.symm (σ.symm j)
  have hxy : x.2 ≠ y.2 := fun h => hij <| by
    simpa [σ, x, y] using (h_lbl (σ.symm i)).trans ((congrArg Fin.val h).trans (h_lbl (σ.symm j)).symm)
  rw [kPerm_conjugate_apply]
  change (csMatrix 𝕂 c s) (twoProdSumEquiv p x) (twoProdSumEquiv p y) = 0
  rcases x with ⟨a, u⟩; rcases y with ⟨b, v⟩
  change u ≠ v at hxy
  fin_cases a <;> fin_cases b <;> simp [csMatrix, twoProdSumEquiv, hxy]

theorem inA3Unitary_scalar_two_iff {p : ℕ} {M : KMat 𝕂 (2 * p)} :
    KInA3Unitary p 2 p (kPermMatrix 𝕂 (scalarShuffle 2 p))
      (kPermMatrix 𝕂 (scalarShuffle 2 p))ᴴ M ↔ IsUnitary M := by
  let P := kPermMatrix 𝕂 (scalarShuffle 2 p)
  have hP : IsUnitary P := kPerm_unitary _
  refine ⟨fun ⟨B₁, B₂, B₃, _, _, _, h₁, h₂, h₃, hM⟩ => hM ▸ (((h₃.mul hP.conjTranspose).mul h₂).mul hP).mul h₁,
    fun hM => ?_⟩
  let e := (finProdFinEquiv.symm.trans (twoProdSumEquiv p)).symm
  obtain ⟨U₁, U₂, V₁, V₂, c, s, hU₁, hU₂, hV₁, hV₂, hcs, hfactor⟩ :=
    exists_square_cs (M.submatrix e e) (submatrix_unitary e hM)
  have he : squareFlatten (M.submatrix e e) = M := by
    ext i j; exact congrArg₂ M (e.right_inv i) (e.right_inv j)
  let L := squareFlatten (split U₁ U₂)
  let R := squareFlatten (split V₁ V₂)
  let K := squareFlatten (csMatrix 𝕂 c s)
  refine ⟨R, P * K * Pᴴ, L, squareFlatten_split_blockDiagonal _ _,
    shuffled_square_cs_blockDiagonal c s, squareFlatten_split_blockDiagonal _ _,
    submatrix_unitary _ (split_unitary hV₁ hV₂),
    (hP.mul (submatrix_unitary _ (csMatrix_unitary c s hcs))).mul hP.conjTranspose,
    submatrix_unitary _ (split_unitary hU₁ hU₂), ?_⟩
  rw [← he, hfactor, squareFlatten_mul, squareFlatten_mul]
  calc L * K * R = L * (Pᴴ * P) * K * (Pᴴ * P) * R := by rw [hP.1, Matrix.mul_one, Matrix.mul_one]
    _ = L * Pᴴ * (P * K * Pᴴ) * P * R := by simp only [Matrix.mul_assoc]

end GS.UnitaryCS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GS.Results.OriginalCellRank

variable {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]

theorem exists_rank_factorization (A : Matrix ι κ ℝ) :
    ∃ U : Matrix ι (Fin A.rank) ℝ, ∃ V : Matrix (Fin A.rank) κ ℝ, A = U * V := by
  classical
  let S : Submodule ℝ (ι → ℝ) := LinearMap.range A.mulVecLin
  let b : Module.Basis (Fin A.rank) ℝ S := Module.finBasis ℝ S
  let x : κ → S := fun j => A.mulVecLin.rangeRestrict (Pi.single j 1)
  refine ⟨fun i k => (b k : ι → ℝ) i, fun k j => b.repr (x j) k, ?_⟩
  ext i j
  have h := congrArg (fun y : S => (y : ι → ℝ) i) (b.sum_repr (x j))
  simpa only [x, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.mulVecLin_apply,
    LinearMap.rangeRestrict, LinearMap.codRestrict_apply, Matrix.mulVec_single_one,
    Matrix.col_apply, mul_comm] using h.symm

theorem rank_le_card_iff_factorization (A : Matrix ι κ ℝ) :
    A.rank ≤ Fintype.card τ ↔ ∃ U : Matrix ι τ ℝ, ∃ V : Matrix τ κ ℝ, A = U * V := by
  classical
  constructor
  · intro h
    obtain ⟨U, V, hA⟩ := exists_rank_factorization A
    let e : Fin A.rank → τ := fun k => (Fintype.equivFin τ).symm (Fin.castLE h k)
    have he : Function.Injective e :=
      (Fintype.equivFin τ).symm.injective.comp (Fin.castLE_injective h)
    refine ⟨fun i => Function.extend e (U i) 0,
      fun t j => Function.extend e (fun k => V k j) 0 t, hA.trans ?_⟩
    ext i j
    apply Fintype.sum_of_injective e he
    · intro t ht; simp [Function.extend_apply', show ¬∃ k, e k = t from ht]
    · intro k; simp [he.extend_apply]
  · rintro ⟨U, V, rfl⟩
    exact (Matrix.rank_mul_le_left U V).trans (Matrix.rank_le_card_width U)

def block {n : ℕ} (b₁ b₂ : ℕ) (A : Mat n) (a b : ℕ) : Mat n :=
  fun i j => if a = i.val / b₂ ∧ b = j.val / b₁ then A i j else 0

abbrev Slots {n : ℕ} (b₁ b₂ : ℕ) (σ : Equiv.Perm (Fin n)) (a b : ℕ) :=
  {t : Fin n // a = (σ t).val / b₂ ∧ b = t.val / b₁}

theorem inA2_iff_block_rank {n : ℕ} (b₁ b₂ : ℕ)
    (σ : Equiv.Perm (Fin n)) (A : Mat n) :
    InA2 b₁ b₂ (permMatrix σ) A ↔
      ∀ a b, (block b₁ b₂ A a b).rank ≤ Fintype.card (Slots b₁ b₂ σ a b) := by
  simp only [rank_le_card_iff_factorization]
  constructor
  · rintro ⟨B₁, B₂, hb₁, hb₂, rfl⟩ a b
    refine ⟨fun i t => if a = i.val / b₂ then B₂ i (σ t.val) else 0,
      fun t j => if b = j.val / b₁ then B₁ t.val j else 0, ?_⟩
    ext i j
    by_cases hij : a = i.val / b₂ ∧ b = j.val / b₁
    · rcases hij with ⟨ha, hb⟩
      change (if a = i.val / b₂ ∧ b = j.val / b₁ then (B₂ * permMatrix σ * B₁) i j else 0) =
        ∑ t : Slots b₁ b₂ σ a b, (if a = i.val / b₂ then B₂ i (σ t.val) else 0) *
          (if b = j.val / b₁ then B₁ t.val j else 0)
      simp only [ha, hb, and_self, ↓reduceIte]; rw [Matrix.mul_apply]; symm
      apply Fintype.sum_of_injective (Subtype.val : Slots b₁ b₂ σ a b → Fin n) Subtype.val_injective
      · intro t ht; rw [mul_perm_apply]
        by_cases h1 : a = (σ t).val / b₂
        · rw [hb₁ t j (Ne.symm (hb.symm.trans_ne fun h2 => ht ⟨⟨t, h1, h2⟩, rfl⟩)), mul_zero]
        · rw [hb₂ i (σ t) (ha.symm.trans_ne h1), zero_mul]
      · intro t; rw [mul_perm_apply]
    · simp only [block, hij, ↓reduceIte, Matrix.mul_apply]
      symm; refine Finset.sum_eq_zero fun t _ => ?_
      by_cases ha : a = i.val / b₂
      · simp [ha, show b ≠ j.val / b₁ from fun hb => hij ⟨ha, hb⟩]
      · simp [ha]
  · intro h
    choose U V hUV using h
    let L : Mat n := fun i t =>
      if i.val / b₂ = (σ t).val / b₂ then U ((σ t).val / b₂) (t.val / b₁) i ⟨t, rfl, rfl⟩ else 0
    let B₁ : Mat n := fun t j =>
      if j.val / b₁ = t.val / b₁ then V ((σ t).val / b₂) (t.val / b₁) ⟨t, rfl, rfl⟩ j else 0
    refine ⟨B₁, L * (permMatrix σ)ᵀ, fun t j htj => by simp [B₁, Ne.symm htj],
      fun i j hij => by rw [perm_transpose, mul_perm_apply]; simp [L, hij], ?_⟩
    have hLP : L * (permMatrix σ)ᵀ * permMatrix σ = L := by
      rw [Matrix.mul_assoc, (perm_orthogonal σ).1, Matrix.mul_one]
    simp only [product2, hLP]; ext i j
    have hbij := congrFun (congrFun (hUV (i.val / b₂) (j.val / b₁)) i) j
    simp only [block, true_and, ↓reduceIte, Matrix.mul_apply] at hbij ⊢
    rw [hbij]
    have hterm (a b : ℕ) (ha : i.val / b₂ = a) (hb : j.val / b₁ = b) (t : Slots b₁ b₂ σ a b) :
        U a b i t * V a b t j = L i t.val * B₁ t.val j := by
      rcases t with ⟨t, rfl, rfl⟩; simp [L, B₁, ha, hb]
    apply Fintype.sum_of_injective
      (Subtype.val : Slots b₁ b₂ σ (i.val / b₂) (j.val / b₁) → Fin n) Subtype.val_injective
    · intro t ht
      by_cases h1 : i.val / b₂ = (σ t).val / b₂
      · simp [L, B₁, h1, show j.val / b₁ ≠ t.val / b₁ from fun h2 => ht ⟨⟨t, h1, h2⟩, rfl⟩]
      · simp [L, h1]
    · exact hterm _ _ rfl rfl

end GS.Results.OriginalCellRank

namespace GSPalomar

/-- Every orthogonal matrix in the two-layer class admits orthogonal layers. -/
theorem two_factor (n : ℕ) (s₁ s₂ : GS.BlockSpec n)
    (σ : Equiv.Perm (Fin n)) (A : GS.Mat n) :
    GS.InA2 s₁.size s₂.size (GS.permMatrix σ) A ∧ GS.Orthogonal A ↔
      GS.InA2Orth s₁.size s₂.size (GS.permMatrix σ) A :=
  GS.UnitaryGeometry.twoFactorUnitarization (𝕂 := ℝ) s₁.size s₂.size σ A

/-- The same equality holds for three layers and arbitrary fixed permutations. -/
theorem three_factor (n : ℕ) (s₁ s₂ s₃ : GS.BlockSpec n)
    (σ₁ σ₂ : Equiv.Perm (Fin n)) (A : GS.Mat n) :
    GS.InA3 s₁.size s₂.size s₃.size (GS.permMatrix σ₁) (GS.permMatrix σ₂) A ∧
      GS.Orthogonal A ↔
    GS.InA3Orth s₁.size s₂.size s₃.size (GS.permMatrix σ₁) (GS.permMatrix σ₂) A :=
  GS.UnitaryGeometry.threeFactorUnitarization (𝕂 := ℝ) s₁.size s₂.size s₃.size σ₁ σ₂ A

/-- Four 2-by-2-block layers need not admit an orthogonal-layer realization. -/
theorem four_factor_counterexample :
    ∃ A : GS.Mat 6,
      GS.InA4 2 2 2 2 GS.M4.P GS.M4.P GS.M4.P A ∧ GS.Orthogonal A ∧
      ¬ GS.InA4Orth 2 2 2 2 GS.M4.P GS.M4.P GS.M4.P A :=
  ⟨GS.M4.Q, GS.UnitaryFour.real_counterexample⟩

open GS GS.UnitaryGeometry

/-- Unrestricted two-layer unitary matrices admit unitary layers. -/
theorem unitary_two_factor {n : ℕ} (b₁ b₂ : ℕ)
    (σ : Equiv.Perm (Fin n)) (A : CMat n) :
    CInA2 b₁ b₂ (cPermMatrix σ) A ∧ Unitary A ↔
      CInA2Unitary b₁ b₂ (cPermMatrix σ) A := GS.UnitaryGeometry.twoFactorUnitarization (𝕂 := ℂ) b₁ b₂ σ A

/-- Unrestricted three-layer unitary matrices admit unitary layers. -/
theorem unitary_three_factor {n : ℕ} (b₁ b₂ b₃ : ℕ)
    (σ₁ σ₂ : Equiv.Perm (Fin n)) (A : CMat n) :
    CInA3 b₁ b₂ b₃ (cPermMatrix σ₁) (cPermMatrix σ₂) A ∧ Unitary A ↔
      CInA3Unitary b₁ b₂ b₃ (cPermMatrix σ₁) (cPermMatrix σ₂) A := GS.UnitaryGeometry.threeFactorUnitarization (𝕂 := ℂ) b₁ b₂ b₃ σ₁ σ₂ A

/-- Allowing complex unitary layers does not remove the four-layer obstruction. -/
theorem unitary_four_factor_counterexample :
    ∃ A : CMat 6, let P : CMat 6 := fun i j => (GS.M4.P i j : ℂ)
      CInA4 2 2 2 2 P P P A ∧ Unitary A ∧ ¬CInA4Unitary 2 2 2 2 P P P A := ⟨GS.UnitaryFour.Q, GS.UnitaryFour.counterexample⟩

/-- The scalar (p,2,p) family fills the orthogonal group (including p=0). -/
theorem real_cs_exhaustion {p : ℕ} {A : Mat (2*p)} :
    InA3Orth p 2 p (permMatrix (scalarShuffle 2 p))
      (permMatrix (scalarShuffle 2 p))ᵀ A ↔ Orthogonal A := GS.UnitaryCS.inA3Unitary_scalar_two_iff (𝕂 := ℝ)

/-- Complex cosine-sine decomposition gives the entire unitary group. -/
theorem unitary_cs_exhaustion {p : ℕ} {A : CMat (2*p)} :
    CInA3Unitary p 2 p (cPermMatrix (scalarShuffle 2 p))
      (cPermMatrix (scalarShuffle 2 p))ᴴ A ↔ Unitary A := GS.UnitaryCS.inA3Unitary_scalar_two_iff (𝕂 := ℂ)

/-- A rank-one determinantal singularity survives any Euclidean factor. -/
theorem rank_one_cone_singularity (d e : ℕ) (hd : 2 ≤ d) :
    ¬ EuclideanAtSubset
      {p : (Fin e → ℝ) × Matrix (Fin 2) (Fin d) ℝ | p.2.rank ≤ 1} (0, 0) := GS.Results.cone_rankOne_not_euclidean d e hd

/-- Every all-nonzero orthogonal base gives a genuine topological singularity. -/
theorem real_three_factor_singularity {q : ℕ} (hq : 3 ≤ q)
    (Q : Mat q) (hQ : Orthogonal Q) (hne : ∀ i j, Q i j ≠ 0) :
    ¬ EuclideanAtSubset (localFamily q) (basePoint Q) := GS.Results.gs_not_euclidean_at hq Q hQ hne

/-- There is a singular point for every q≥3, with no conditional base assumption. -/
theorem real_singular_point (q : ℕ) (hq : 3 ≤ q) :
    ∃ A : Mat (q*2), A ∈ localFamily q ∧ ¬ EuclideanAtSubset (localFamily q) A := GS.Results.exists_nonEuclidean_point q hq

/-- The unitary topological result is restricted to odd q. -/
theorem unitary_singular_point (q : ℕ) (hq : 3 ≤ q) (hodd : Odd q) :
    let P := cPermMatrix (scalarShuffle q 2)
    let S : Set (CMat (q*2)) := {A | CInA3Unitary 2 q 2 P Pᴴ A}
    ∃ A : CMat (q*2), A ∈ S ∧ ¬ EuclideanAtSubset S A := GS.UnitaryTopology.exists_unitary_nonEuclidean_point q hq hodd

/-- A finite-dimensional atlas on the given matrix subtype, an injective
inclusion differential with exactly the prescribed tangent image, a jointly
smooth orthogonal projector, a smooth whole-tangent-bundle retraction, and
smooth gradient sections for every smooth ambient loss. The topology of the
subtype is fixed before the atlas is chosen. -/
def EmbeddedGeometry {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (pairing : A → A → ℝ) (S : Set A) (D : A → A → Prop) : Prop :=
  ∃ E : Type, ∃ normE : NormedAddCommGroup E, letI := normE
  ∃ spaceE : NormedSpace ℝ E, letI := spaceE
  FiniteDimensional ℝ E ∧
  ∃ cs : ChartedSpace E S, letI := cs
  ∃ hm : IsManifold (𝓘(ℝ, E)) ⊤ S, letI := hm
  ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, A)) ⊤ (fun X : S => X.val) ∧
  (∀ X : S, Function.Injective (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, A))
    (fun Y : S => Y.val) X)) ∧
  (∀ (X : S) (Z : A), D X.val Z ↔ ∃ v : E,
    mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, A)) (fun Y : S => Y.val) X v = Z) ∧
  (∃ π : S × A → A,
    ContMDiff ((𝓘(ℝ, E)).prod (𝓘(ℝ, A))) (𝓘(ℝ, A)) ⊤ π ∧
    ∀ (X : S) (Z : A), D X.val (π (X, Z)) ∧
      ∀ Y : A, D X.val Y → pairing (Z - π (X, Z)) Y = 0) ∧
  (∃ R : TangentBundle (𝓘(ℝ, E)) S → S,
    ContMDiff (𝓘(ℝ, E)).tangent (𝓘(ℝ, E)) ⊤ R ∧
    (∀ X : S, R ⟨X, 0⟩ = X) ∧
    ∀ X : S, mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E))
      (fun v : E => R ⟨X, v⟩) 0 = ContinuousLinearMap.id ℝ E) ∧
  (∀ f : A → ℝ, ContDiff ℝ ∞ f → ∃ g : S → E,
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)).tangent ∞
      (fun X : S => (⟨X, g X⟩ : TangentBundle (𝓘(ℝ, E)) S)) ∧
    ∀ (X : S) (v : E),
      pairing (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, A)) (fun Y : S => Y.val) X (g X))
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, A)) (fun Y : S => Y.val) X v) =
      mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) (fun Y : S => f Y.val) X v)

/-- Exact real tangent directions with the prescribed layer supports and ties. -/
def RealDirections {n : ℕ} (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (X Z : Mat n) : Prop :=
  ∃ C Ω : Mat n,
    (BlockDiagonal b₂ C ∧ Cᵀ = -C ∧ GS.GlobalGeometry.TiedEntries b₂ τ₂ C) ∧
    (BlockDiagonal b₁ Ω ∧ Ωᵀ = -Ω ∧ GS.GlobalGeometry.TiedEntries b₁ τ₁ Ω) ∧
    Z = C * X + X * Ω

/-- Exact real tangent directions in the unitary case; phases are retained. -/
def ComplexDirections {n : ℕ} (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (X Z : CMat n) : Prop :=
  ∃ C Ω : CMat n,
    (CBlockDiagonal b₂ C ∧ Cᴴ = -C ∧ GS.UnitarySharing.TiedEntries b₂ τ₂ C) ∧
    (CBlockDiagonal b₁ Ω ∧ Ωᴴ = -Ω ∧ GS.UnitarySharing.TiedEntries b₁ τ₁ Ω) ∧
    Z = C * X + X * Ω

theorem shared_geometry {𝕂 : Type} [RCLike 𝕂]
    {n : ℕ} (b₁ b₂ : ℕ) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hd₁ : b₁ ∣ n) (hd₂ : b₂ ∣ n)
    (τ₁ τ₂ : ℕ → ℕ) (P : GS.SharedGeometry.KMat 𝕂 n) :
    EmbeddedGeometry GS.SharedGeometry.kfrobInner
      {X | GS.SharedGeometry.KInSharedA2 b₁ b₂ τ₁ τ₂ P X}
      (fun X Z => ∃ C Ω : GS.SharedGeometry.KMat 𝕂 n,
        (GS.SharedGeometry.KSupported (fun i => i.val / b₂) C ∧ Cᴴ = -C ∧ GS.SharedGeometry.KTiedEntries b₂ τ₂ C) ∧
        (GS.SharedGeometry.KSupported (fun i => i.val / b₁) Ω ∧ Ωᴴ = -Ω ∧ GS.SharedGeometry.KTiedEntries b₁ τ₁ Ω) ∧
        Z = C * X + X * Ω) := by
  let right : GS.SharedGeometry.Pattern 𝕂 n := ⟨b₁, hb₁, hd₁, τ₁⟩
  let left : GS.SharedGeometry.Pattern 𝕂 n := ⟨b₂, hb₂, hd₂, τ₂⟩
  rw [(GS.SharedGeometry.orbit_set_eq_inShared (right := right) (left := left) P).symm]
  let E := GS.SharedGeometry.HorizontalModel right left P
  let : NormedSpace ℝ E := Submodule.normedSpace _
  let : ChartedSpace E (GS.SharedGeometry.MatrixOrbit right left P) :=
    GS.SharedGeometry.sharedOrbitChartedSpace right left P
  let : IsManifold (𝓘(ℝ, E)) ⊤ (GS.SharedGeometry.MatrixOrbit right left P) :=
    GS.SharedGeometry.sharedOrbitIsManifold right left P
  have hdir (X Z : GS.SharedGeometry.KMat 𝕂 n) :
      (∃ C Ω : GS.SharedGeometry.KMat 𝕂 n,
        (GS.SharedGeometry.KSupported (fun i => i.val / b₂) C ∧ Cᴴ = -C ∧ GS.SharedGeometry.KTiedEntries b₂ τ₂ C) ∧
        (GS.SharedGeometry.KSupported (fun i => i.val / b₁) Ω ∧ Ωᴴ = -Ω ∧ GS.SharedGeometry.KTiedEntries b₁ τ₁ Ω) ∧
        Z = C * X + X * Ω) ↔
      Z ∈ GS.SharedGeometry.pointDirections right left X := by
    rw [GS.SharedGeometry.mem_pointDirections_iff]
    exact ⟨fun ⟨C, Ω, hC, hΩ, he⟩ => ⟨C, hC, Ω, hΩ, he⟩,
           fun ⟨C, hC, Ω, hΩ, he⟩ => ⟨C, Ω, hC, hΩ, he⟩⟩
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    GS.SharedGeometry.sharedOrbit_val_contMDiff right left P,
    GS.SharedGeometry.sharedOrbit_val_mfderiv_injective right left P,
    fun X Z => (hdir X.val Z).trans (GS.SharedGeometry.orbit_tangent_image_iff right left P X Z).symm,
    ⟨fun p => GS.SharedGeometry.pointProjection right left p.1.val p.2,
      GS.SharedGeometry.pointProjection_contMDiff right left P, fun X Z =>
        ⟨(hdir _ _).mpr (GS.SharedGeometry.pointProjection_mem X.val Z),
         fun Y hY => GS.SharedGeometry.pointProjection_normal X.val Z Y ((hdir _ _).mp hY)⟩⟩,
    ⟨GS.SharedGeometry.cayleyRetraction right left P,
      GS.SharedGeometry.cayleyRetraction_contMDiff right left P,
      GS.SharedGeometry.cayleyRetraction_zero_section right left P,
      GS.SharedGeometry.cayleyRetraction_fibre_mfderiv_zero right left P⟩,
    fun f hf => ⟨GS.SharedGeometry.intrinsicGradient right left P f,
      GS.SharedGeometry.intrinsicGradientSection_smooth right left P f hf,
      fun X v => GS.SharedGeometry.intrinsicGradient_characterization right left P f X
        ((hf.differentiable (by simp)) X) v⟩⟩

/-- Smooth geometry of the actual orthogonal image, including arbitrary overlap,
complete within-layer sharing, and arbitrary fixed carriers. -/
theorem orthogonal_shared_geometry {n : ℕ} (b₁ b₂ : ℕ)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hd₁ : b₁ ∣ n) (hd₂ : b₂ ∣ n)
    (τ₁ τ₂ : ℕ → ℕ) (P : Mat n) :
    EmbeddedGeometry (fun A B : Mat n => ∑ i, ∑ j, A i j * B i j)
      {X | GS.GlobalGeometry.InSharedA2Orth b₁ b₂ τ₁ τ₂ P X}
      (RealDirections b₁ b₂ τ₁ τ₂) := by
  have hp : (fun A B : Mat n => ∑ i, ∑ j, A i j * B i j) = GS.SharedGeometry.kfrobInner := by
    ext A B; rw [GS.SharedGeometry.kfrobInner_eq_sum]; simp
  rw [hp]; exact shared_geometry (𝕂 := ℝ) b₁ b₂ hb₁ hb₂ hd₁ hd₂ τ₁ τ₂ P

/-- The same real differential geometry for shared unitary layers, with the
full continuous stabilizer allowed. No special-unitary restriction is imposed. -/
theorem unitary_shared_geometry {n : ℕ} (b₁ b₂ : ℕ)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hd₁ : b₁ ∣ n) (hd₂ : b₂ ∣ n)
    (τ₁ τ₂ : ℕ → ℕ) (P : CMat n) :
    EmbeddedGeometry (fun A B : CMat n =>
      ∑ i, ∑ j, ((A i j).re * (B i j).re + (A i j).im * (B i j).im))
      {X | GS.UnitarySharing.InSharedA2Unitary b₁ b₂ τ₁ τ₂ P X}
      (ComplexDirections b₁ b₂ τ₁ τ₂) := by
  have hp : (fun A B : CMat n => ∑ i, ∑ j, ((A i j).re * (B i j).re + (A i j).im * (B i j).im)) =
      GS.SharedGeometry.kfrobInner := by
    ext A B; rw [GS.SharedGeometry.kfrobInner_eq_sum]; rfl
  rw [hp]; exact shared_geometry (𝕂 := ℂ) b₁ b₂ hb₁ hb₂ hd₁ hd₂ τ₁ τ₂ P

/-- Exact cell-rank criterion, including singular matrices and empty cells. -/
theorem two_factor_rank_criterion {n : ℕ} (b₁ b₂ : ℕ)
    (σ : Equiv.Perm (Fin n)) (A : GS.Mat n) :
    GS.InA2 b₁ b₂ (GS.permMatrix σ) A ↔
      ∀ a b : ℕ,
        (Matrix.of fun i j : Fin n =>
          if a = i.val / b₂ ∧ b = j.val / b₁ then A i j else 0).rank ≤
        Fintype.card {t : Fin n // a = (σ t).val / b₂ ∧ b = t.val / b₁} :=
  GS.Results.OriginalCellRank.inA2_iff_block_rank b₁ b₂ σ A

/-- With no off-diagonal overlap, the explicit shared block exponentials stay
in the actual image and have normal ambient acceleration and constant speed.
The normality test ranges over the entire tangent image given above. -/
theorem orthogonal_shared_block_geodesic {n : ℕ} (b₁ b₂ : ℕ)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hd₁ : b₁ ∣ n) (hd₂ : b₂ ∣ n)
    (τ₁ τ₂ : ℕ → ℕ) (σ : Equiv.Perm (Fin n))
    (hno : Function.Injective (fun i : Fin n => (i.val / b₁, (σ i).val / b₂)))
    (L R C Ω : Mat n)
    (hL : GS.GlobalGeometry.SharedOrthogonalFactor b₂ τ₂ L)
    (hR : GS.GlobalGeometry.SharedOrthogonalFactor b₁ τ₁ R)
    (hC : BlockDiagonal b₂ C ∧ Cᵀ = -C ∧ GS.GlobalGeometry.TiedEntries b₂ τ₂ C)
    (hΩ : BlockDiagonal b₁ Ω ∧ Ωᵀ = -Ω ∧ GS.GlobalGeometry.TiedEntries b₁ τ₁ Ω) :
    let γ : ℝ → Mat n := fun t =>
      L * NormedSpace.exp (t • C) * permMatrix σ * (NormedSpace.exp (t • Ω) * R)
    ∀ t : ℝ,
      GS.GlobalGeometry.InSharedA2Orth b₁ b₂ τ₁ τ₂ (permMatrix σ) (γ t) ∧
      HasDerivAt γ (deriv γ t) t ∧
      HasDerivAt (deriv γ) (deriv (deriv γ) t) t ∧
      (∀ Z : Mat n, RealDirections b₁ b₂ τ₁ τ₂ (γ t) Z →
        (∑ i, ∑ j, deriv (deriv γ) t i j * Z i j) = 0) ∧
      (∑ i, ∑ j, (deriv γ t i j)^2) =
        (∑ i, ∑ j, (C i j)^2) + (∑ i, ∑ j, (Ω i j)^2) := by
  intro γ
  let v := GS.Continuation.gsExpVelocity L (permMatrix σ) R C Ω
  let a := GS.Continuation.gsExpAcceleration L (permMatrix σ) R C Ω
  have he : GS.Continuation.gsExpCurve L (permMatrix σ) R C Ω = γ := by
    funext t
    simp only [GS.Continuation.gsExpCurve, GS.Continuation.gsExpLeft,
      GS.Continuation.gsExpRight, GS.Continuation.expLine, GS.matrixExp_eq_exp,
      GS.product2, γ]
  have hv (t : ℝ) : HasDerivAt γ (v t) t := by
    rw [← he]; exact GS.Continuation.gsExpCurve_hasDerivAt L _ R C Ω (perm_orthogonal σ) t
  have heV : deriv γ = v := funext fun t => (hv t).deriv
  have ha (t : ℝ) : HasDerivAt v (a t) t :=
    GS.Continuation.gsExpVelocity_hasDerivAt L _ R C Ω (perm_orthogonal σ) t
  have heA : deriv (deriv γ) = a := by rw [heV]; exact funext fun t => (ha t).deriv
  have hdisj : GS.Extensions.OffDiagonalDisjoint (fun i : Fin n => i.val / b₂) ((fun i : Fin n => i.val / b₁) ∘ σ.symm) :=
    fun i j h₂ h₁ => σ.symm.injective (hno (Prod.ext h₁ (by simpa using h₂)))
  intro t
  have hLt := GS.GlobalGeometry.gsExpLeft_shared b₂ τ₂ hb₂ hd₂ L C hL hC t
  have hRt := GS.GlobalGeometry.gsExpRight_shared b₁ τ₁ hb₁ hd₁ R Ω hR hΩ t
  refine ⟨⟨_, _, hLt, hRt, by rw [← he]; rfl⟩, heV ▸ hv t, heA ▸ heV ▸ ha t, ?_, ?_⟩
  · rintro Z ⟨A, B, hA, hB, hZ⟩
    rw [heA]
    rw [← he] at hZ
    let L' := GS.Continuation.gsExpLeft L C t
    let R' := GS.Continuation.gsExpRight R Ω t
    have hA' := GS.SharedGeometry.sharedSkew_conjugate_conjTranspose (𝕂 := ℝ) hb₂ hd₂ hLt hA
    have hB' := GS.SharedGeometry.sharedSkew_conjugate (𝕂 := ℝ) hb₁ hd₁ hRt hB
    refine GS.Continuation.gsExpCurve_acceleration_normal
      (fun i => i.val / b₁) (fun i => i.val / b₂) σ L R C Ω hdisj
      hL.2.1 hR.2.1 hC.1 hΩ.1 hC.2.1 hΩ.2.1 t Z ⟨L'ᵀ * A * L', R' * B * R'ᵀ,
        hA'.1, hA'.2.1, hB'.1, hB'.2.1, ?_⟩
    rw [hZ]
    change A * (L' * permMatrix σ * R') + (L' * permMatrix σ * R') * B =
      L' * (L'ᵀ * A * L') * permMatrix σ * R' + L' * permMatrix σ * (R' * B * R'ᵀ) * R'
    have hl : L' * (L'ᵀ * A * L') * permMatrix σ * R' = A * (L' * permMatrix σ * R') := by
      calc _ = (L' * L'ᵀ) * A * (L' * permMatrix σ * R') := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [show L' * L'ᵀ = 1 from hLt.2.1.2, Matrix.one_mul]
    have hr : L' * permMatrix σ * (R' * B * R'ᵀ) * R' = (L' * permMatrix σ * R') * B := by
      calc _ = (L' * permMatrix σ * R') * B * (R'ᵀ * R') := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [show R'ᵀ * R' = 1 from hRt.2.1.1, Matrix.mul_one]
    rw [hl, hr]
  · rw [heV]
    simpa only [GS.frobSq, GS.frobInner, sq, v] using
      GS.Continuation.gsExpCurve_constant_speed (fun i => i.val / b₁) (fun i => i.val / b₂)
        σ L R C Ω hdisj hL.2.1 hR.2.1 hC.1 hΩ.1 hC.2.1 hΩ.2.1 t

end GSPalomar
