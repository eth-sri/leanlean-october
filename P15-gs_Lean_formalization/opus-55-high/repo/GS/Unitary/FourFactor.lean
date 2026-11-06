module

public import GS.M4Obstruction
public import GS.Unitary.RealEmbedding

@[expose] public section


/-!
# Unitary four-factor insufficiency

The exact real counterexample remains a counterexample when arbitrary complex
unitary blocks are permitted. This does not follow merely from its real
nonfactorization: we prove the determinant-modulus obstruction for all complex
unitary factors, then transfer the exact real certificate through ℝ → ℂ.
-/

noncomputable section

namespace GS.UnitaryGeometry

def product4 {n : ℕ} (B₄ P₃ B₃ P₂ B₂ P₁ B₁ : CMat n) : CMat n :=
  B₄ * P₃ * B₃ * P₂ * B₂ * P₁ * B₁

section
variable {n : ℕ} (b₁ b₂ b₃ b₄ : ℕ) (P₁ P₂ P₃ A : CMat n)
def CInA4 : Prop :=
  ∃ B₁ B₂ B₃ B₄, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    CBlockDiagonal b₃ B₃ ∧ CBlockDiagonal b₄ B₄ ∧
    A = product4 B₄ P₃ B₃ P₂ B₂ P₁ B₁

def CInA4Unitary : Prop :=
  ∃ B₁ B₂ B₃ B₄, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    CBlockDiagonal b₃ B₃ ∧ CBlockDiagonal b₄ B₄ ∧
    Unitary B₁ ∧ Unitary B₂ ∧ Unitary B₃ ∧ Unitary B₄ ∧
    A = product4 B₄ P₃ B₃ P₂ B₂ P₁ B₁

end

end GS.UnitaryGeometry

namespace GS.UnitaryFour
open GS.UnitaryGeometry

def P : CMat 6 := ofRealMatrix GS.M4.P
open GS.M4 (cell)

def detBlock (M : CMat 6) (i j : Fin 3) : ℂ :=
  M (cell i 0) (cell j 0) * M (cell i 1) (cell j 1) -
  M (cell i 0) (cell j 1) * M (cell i 1) (cell j 0)

def block2 (A : CMat 6) (i j : Fin 3) : CMat 2 := A.submatrix (cell i) (cell j)

theorem detBlock_eq_det (M : CMat 6) (i j : Fin 3) :
    detBlock M i j = (block2 M i j).det := by
  rw [Matrix.det_fin_two]
  rfl

section
variable (A : CMat 6)
def normDetBlock (i j : Fin 3) : ℝ := ‖detBlock A i j‖

def determinantObstruction : Prop :=
  let d := normDetBlock A
  (1-d 0 2*d 1 0/d 2 1)*(1-d 0 2*d 2 1/d 1 0) ≥ d 0 0*d 2 2/d 1 1


end

def assemble (A : Fin 3 → CMat 2) : CMat 6 :=
  !![A 0 0 0,A 0 0 1,0,0,0,0;
     A 0 1 0,A 0 1 1,0,0,0,0;
     0,0,A 1 0 0,A 1 0 1,0,0;
     0,0,A 1 1 0,A 1 1 1,0,0;
     0,0,0,0,A 2 0 0,A 2 0 1;
     0,0,0,0,A 2 1 0,A 2 1 1]

theorem block_diagonal_decompose (A : CMat 6) (hA : CBlockDiagonal 2 A) :
    A = assemble (fun i => block2 A i i) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [assemble,block2,cell] <;> apply hA <;> decide

theorem block2_left_assembled (A : Fin 3 → CMat 2) (C : CMat 6) (i j : Fin 3) :
    block2 (assemble A*C) i j = A i * block2 C i j := by
  ext a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [block2,cell,assemble,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ]

theorem block2_right_assembled (C : CMat 6) (B : Fin 3 → CMat 2) (i j : Fin 3) :
    block2 (C*assemble B) i j = block2 C i j * B j := by
  ext a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [block2,cell,assemble,Matrix.mul_apply,Fin.sum_univ_succ]

theorem block2_outer (A C B : CMat 6) (hA : CBlockDiagonal 2 A)
    (hB : CBlockDiagonal 2 B) (i j : Fin 3) :
    block2 (A*C*B) i j = block2 A i i * block2 C i j * block2 B j j := by
  have ha := block_diagonal_decompose A hA
  have hb := block_diagonal_decompose B hB
  conv_lhs => rw [ha,hb,block2_right_assembled, block2_left_assembled]

theorem block2_unitary (A : CMat 6) (hA : CBlockDiagonal 2 A)
    (ho : Unitary A) (r : Fin 3) : Unitary (block2 A r r) := by
  rw [block_diagonal_decompose A hA] at ho
  constructor <;> ext i j <;> [have h := congr_fun₂ ho.1 (cell r i) (cell r j);
    have h := congr_fun₂ ho.2 (cell r i) (cell r j)] <;>
    fin_cases r <;> fin_cases i <;> fin_cases j <;>
      simpa [block2,cell,assemble,Matrix.mul_apply,Matrix.one_apply,Fin.sum_univ_succ] using h

theorem norm_det_unitary {n : ℕ} (U : CMat n) (hU : Unitary U) : ‖U.det‖=1 := by
  have hs : ‖U.det‖^2 = (1 : ℝ) := by
    simpa [Matrix.det_mul, Matrix.det_conjTranspose, pow_two] using congrArg (‖·.det‖) hU.1
  nlinarith [norm_nonneg U.det]

theorem normDetBlock_outer (A C B : CMat 6)
    (hA : CBlockDiagonal 2 A) (hB : CBlockDiagonal 2 B)
    (hoA : Unitary A) (hoB : Unitary B) (i j : Fin 3) :
    normDetBlock (A*C*B) i j = normDetBlock C i j := by
  simp [normDetBlock, detBlock_eq_det, block2_outer A C B hA hB i j, norm_det_unitary _ (block2_unitary A hA hoA i),
    norm_det_unitary _ (block2_unitary B hB hoB j)]

/-- The entry-modulus identities hold for all complex unitary 2×2 blocks. -/
theorem unitary2_norm (W : CMat 2) (hW : Unitary W) :
    ‖W 1 0‖=‖W 0 1‖ ∧ ‖W 1 1‖=‖W 0 0‖ ∧ ‖W 0 0‖^2+‖W 0 1‖^2=1 := by
  have h k := congrArg Complex.re (congr_fun₂ hW.1 k k)
  have h' := congrArg Complex.re (congr_fun₂ hW.2 0 0)
  simp [Matrix.mul_apply, Fin.sum_univ_succ, Fin.forall_fin_two] at h h'
  refine ⟨?_, ?_, ?_⟩ <;> try apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  all_goals simp only [Complex.sq_norm, Complex.normSq_apply]; linarith

def canonicalDetTable (a b e f : Fin 3 → ℝ) : Mat 3 :=
  !![b 0*b 1*f 1*f 0, a 0*a 1*e 2*f 0, a 1*b 0*e 1*f 2;
     a 2*b 0*e 0*e 1, b 2*b 0*f 0*f 2, b 2*a 0*e 1*e 2;
     b 2*a 1*f 0*e 1, a 1*a 2*f 2*e 0, b 1*b 2*f 2*f 1]

theorem core_normDetTable (W Y : Fin 3 → CMat 2)
    (hW : ∀ i, Unitary (W i)) (hY : ∀ i, Unitary (Y i)) :
    normDetBlock (P*assemble W*P*assemble Y*P) =
      canonicalDetTable (fun i => ‖W i 0 0‖) (fun i => ‖W i 0 1‖)
        (fun i => ‖Y i 0 0‖) (fun i => ‖Y i 0 1‖) := by
  ext i j
  have hw i := unitary2_norm (W i) (hW i)
  have hy i := unitary2_norm (Y i) (hY i)
  fin_cases i <;> fin_cases j <;>
    norm_num [normDetBlock, detBlock,cell,P,GS.M4.P,ofRealMatrix,assemble,Matrix.mul_apply,
      Fin.sum_univ_succ, canonicalDetTable]
  all_goals (try simp only [(hw _).1,(hw _).2.1,(hy _).1,(hy _).2.1]); ring

theorem canonical_obstruction (a b e f : Fin 3 → ℝ)
    (hW : ∀ i, (a i)^2+(b i)^2=1) (hY : ∀ i, (e i)^2+(f i)^2=1)
    (hden : canonicalDetTable a b e f 2 1 * canonicalDetTable a b e f 1 0 *
      canonicalDetTable a b e f 1 1 ≠ 0) :
    let d := canonicalDetTable a b e f
    (1-d 0 2*d 1 0/d 2 1)*(1-d 0 2*d 2 1/d 1 0) ≥ d 0 0*d 2 2/d 1 1 := by
  have key := GS.M4.scalar_obstruction (a 1) (b 0) (e 1) (f 2) (b 1) (f 1) (hW 1) (hY 1)
    (by nlinarith [hW 0, sq_nonneg (a 0)]) (by nlinarith [hY 2, sq_nonneg (e 2)])
  simp [canonicalDetTable] at hden ⊢
  casesm* _ ∧ _
  convert key using 3 <;> field_simp

/-- Universal necessity for the precise m=4 class in the manuscript. -/
theorem necessaryCondition (A : CMat 6) (h : CInA4Unitary 2 2 2 2 P P P A)
    (hden : normDetBlock A 2 1 * normDetBlock A 1 0 * normDetBlock A 1 1 ≠ 0) :
    determinantObstruction A := by
  rcases h with ⟨B₁,B₂,B₃,B₄,hb₁,hb₂,hb₃,hb₄,ho₁,ho₂,ho₃,ho₄,he⟩
  have hd : normDetBlock A=normDetBlock (P*B₃*P*B₂*P) := by
    funext i j
    simpa only [he, GS.UnitaryGeometry.product4, Matrix.mul_assoc] using
      normDetBlock_outer B₄ (P*B₃*P*B₂*P) B₁ hb₄ hb₁ ho₄ ho₁ i j
  unfold determinantObstruction
  have h₃ := block2_unitary B₃ hb₃ ho₃
  have h₂ := block2_unitary B₂ hb₂ ho₂
  rw [hd, block_diagonal_decompose B₂ hb₂, block_diagonal_decompose B₃ hb₃, core_normDetTable _ _ h₃ h₂] at hden ⊢
  exact canonical_obstruction _ _ _ _ (fun i => (unitary2_norm _ (h₃ i)).2.2) (fun i => (unitary2_norm _ (h₂ i)).2.2) hden

end GS.UnitaryFour
