import Mathlib.Tactic

import GS.MatrixFactor.Factorization
import GS.MatrixCS.ColumnGram
import GS.OriginalLocalModel




/-!
# Exact scalar perfect-shuffle description of the unitary block family

This file identifies the block description with the original three-factor
family using its prescribed scalar shuffle, including degenerate entries.
-/
open Matrix
namespace GS.MatrixBlocks
open GS.MatrixFactor GS.MatrixBase
variable {𝕜 : Type} [RCLike 𝕜]

variable (B C : Fin k → KMat 𝕜 b)

def diagTwo (a b : 𝕜) : KMat 𝕜 2 := Matrix.diagonal ![a,b]

def blockMatrix  :
    Matrix (Fin k × Fin b) (Fin k × Fin b) 𝕜 :=
  fun i j => if i.1 = j.1 then B i.1 i.2 j.2 else 0

@[fun_prop] theorem continuous_blockMatrix :
    Continuous (fun B : Fin k → KMat 𝕜 b => blockMatrix B) := by
  apply continuous_pi; intro i
  apply continuous_pi; intro j
  by_cases h : i.1 = j.1 <;> simp only [blockMatrix, h, ite_true, ite_false] <;> fun_prop
@[fun_prop] theorem continuous_diagTwo :
    Continuous (fun p : 𝕜 × 𝕜 => diagTwo p.1 p.2) := by fun_prop [diagTwo]

def localFamily (q : ℕ) : Set (KMat 𝕜 (q*2)) :=
  let P := cPermMatrix (𝕜 := 𝕜) (scalarShuffle q 2)
  {M | CInA3Unitary 2 q 2 P Pᴴ M}

section Relabel
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
variable (e : β ≃ α)

/-- Pull back both matrix indices along an equivalence. -/
def pullMatrix (A : Matrix α α 𝕜) : Matrix β β 𝕜 :=
  fun i j => A (e i) (e j)

theorem pullMatrix_mul (A B : Matrix α α 𝕜) :
    pullMatrix e (A*B) = pullMatrix e A * pullMatrix e B := (Matrix.submatrix_mul_equiv A B e e e).symm

theorem pullMatrix_unitary {A : Matrix α α 𝕜} (hA : Unitary A) :
    Unitary (pullMatrix e A) := Unitary.submatrix e hA

end Relabel

/-- Flatten the pair-indexed matrix using the SAME equivalence as originalF. -/
def flattenBlocks (A : Matrix (Fin k × Fin b) (Fin k × Fin b) 𝕜) := pullMatrix finProdFinEquiv.symm A

@[simp] theorem flattenBlocks_apply (A : Matrix (Fin k × Fin b) (Fin k × Fin b) 𝕜)
    (i j : Fin k × Fin b) :
    flattenBlocks A (finProdFinEquiv i) (finProdFinEquiv j) = A i j := by
  simp [flattenBlocks,pullMatrix]

theorem flattenBlocks_mul (A B : Matrix (Fin k × Fin b) (Fin k × Fin b) 𝕜) :
    flattenBlocks (A*B) = flattenBlocks A * flattenBlocks B :=
  pullMatrix_mul _ A B

/-- Blocks are indexed by the quotient in the original CBlockDiagonal predicate. -/
theorem flat_block_label (p : Fin k × Fin b) :
    (finProdFinEquiv p).val / b = p.1.val :=
  congrArg (fun x => x.1.val) (finProdFinEquiv.symm_apply_apply p)

theorem flatten_blockDiagonal  :
    CBlockDiagonal b (flattenBlocks (blockMatrix B)) := by
  intro i j hij
  let x := finProdFinEquiv.symm i
  let y := finProdFinEquiv.symm j
  have hxy : x.1 ≠ y.1 := by exact?
  exact if_neg hxy

@[simp] theorem blockMatrix_conjTranspose  :
    (blockMatrix B)ᴴ = blockMatrix (fun i => (B i)ᴴ) :=
  congrArg (pullMatrix (Equiv.prodComm _ _)) (Matrix.blockDiagonal_conjTranspose B)

@[simp] theorem blockMatrix_mul  :
    blockMatrix B * blockMatrix C = blockMatrix (fun i => B i * C i) :=
  (pullMatrix_mul (Equiv.prodComm _ _) _ _).symm.trans
    (congrArg (pullMatrix (Equiv.prodComm _ _)) (Matrix.blockDiagonal_mul B C).symm)

@[simp] theorem blockMatrix_one (k b : ℕ) :
    blockMatrix (fun _ : Fin k => (1 : KMat 𝕜 b)) = 1 := by
  ext ⟨i,a⟩ ⟨j,c⟩
  simp [blockMatrix,Matrix.one_apply,Prod.ext_iff,← ite_and]

theorem blockMatrix_unitary 
    (hB : ∀ i, Unitary (B i)) : Unitary (blockMatrix B) := by
  apply GS.MatrixBase.Unitary.of_conjTranspose_mul
  rw [blockMatrix_conjTranspose,blockMatrix_mul,
    show (fun i => (B i)ᴴ * B i) = (fun _ => (1 : KMat 𝕜 b)) from
      funext fun i => (hB i).1, blockMatrix_one]

section Central
variable (A B : KMat 𝕜 q)

/-- The central conjugate, displayed in q-by-q blocks of size two. -/
def centralPair  :
    Matrix (Fin q × Fin 2) (Fin q × Fin 2) 𝕜 :=
  fun i j => diagTwo (A i.1 j.1) (B i.1 j.1) i.2 j.2

theorem centralPair_as_blocks  :
    centralPair A B = pullMatrix (Equiv.prodComm _ _) (blockMatrix ![A,B]) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  fin_cases a,b <;> simp [centralPair,pullMatrix,blockMatrix,diagTwo]

theorem centralPair_unitary 
    (hA : Unitary A) (hB : Unitary B) : Unitary (centralPair A B) := by
  rw [centralPair_as_blocks]
  apply pullMatrix_unitary
  apply blockMatrix_unitary
  intro i
  fin_cases i
  · exact hA
  · exact hB

/-- Scalar middle factor, constructed by conjugation with the specified shuffle. -/
def shuffledMiddle  : KMat 𝕜 (q*2) :=
  let P := cPermMatrix (𝕜 := 𝕜) (scalarShuffle q 2)
  P * flattenBlocks (centralPair A B) * Pᴴ

end Central

/-- The shuffle makes the inner coordinate the consecutive block label. -/
theorem shuffle_block_label (i : Fin (q*b)) :
    (scalarShuffle q b i).val / q = (finProdFinEquiv.symm i).2.val := by
  change (cast (congrArg Fin (Nat.mul_comm b q))
    (finProdFinEquiv ((finProdFinEquiv.symm i).2,(finProdFinEquiv.symm i).1))).val / q = _
  rw [← Fin.cast_eq_cast (Nat.mul_comm b q)]
  exact flat_block_label _

theorem shuffledMiddle_blockDiagonal (A B : KMat 𝕜 q) :
    CBlockDiagonal q (shuffledMiddle A B) := by
  intro i j hij
  let σ := scalarShuffle q 2
  let x := finProdFinEquiv.symm (σ.symm i)
  let y := finProdFinEquiv.symm (σ.symm j)
  have hxy : x.2 ≠ y.2 := by
    intro h
    have hi := shuffle_block_label (σ.symm i)
    have hj := shuffle_block_label (σ.symm j)
    simp only [σ,Equiv.apply_symm_apply] at hi hj
    exact hij (hi.trans ((congrArg Fin.val h).trans hj.symm))
  change (cPermMatrix (𝕜 := 𝕜) σ * flattenBlocks (centralPair A B) * (cPermMatrix (𝕜 := 𝕜) σ)ᴴ) i j = 0
  rw [cPerm_conjugate_apply]
  
  have hdiag (a b : Fin 2) (hab : a ≠ b) (s t : 𝕜) : diagTwo s t a b = 0 := by simp_all [diagTwo]
  exact hdiag x.2 y.2 hxy _ _

variable (U V : Fin q → KMat 𝕜 2)

theorem small_block_sandwich  (A B : KMat 𝕜 q)
    (i j : Fin q) (a b : Fin 2) :
    (blockMatrix U * centralPair A B * blockMatrix V) (i,a) (j,b) =
      (U i * diagTwo (A i j) (B i j) * V j) a b := by simp_all [blockMatrix,centralPair,Fintype.sum_prod_type,Matrix.mul_apply]

/-- Every unitary small-block sandwich belongs to the original scalar family. -/
theorem block_sandwich_mem_localFamily 
    (A B : KMat 𝕜 q) (hU : ∀ i, Unitary (U i)) (hV : ∀ j, Unitary (V j))
    (hA : Unitary A) (hB : Unitary B) :
    flattenBlocks (blockMatrix U * centralPair A B * blockMatrix V) ∈ localFamily q := by
  let P := cPermMatrix (𝕜 := 𝕜) (scalarShuffle q 2)
  let C := flattenBlocks (centralPair A B)
  have hP : Unitary P := cPerm_unitary (𝕜 := 𝕜) _
  have hC : Unitary C := pullMatrix_unitary _ (centralPair_unitary A B hA hB)
  refine ⟨flattenBlocks (blockMatrix V), shuffledMiddle A B,
    flattenBlocks (blockMatrix U), flatten_blockDiagonal V,
    shuffledMiddle_blockDiagonal A B, flatten_blockDiagonal U,
    pullMatrix_unitary _ (blockMatrix_unitary V hV),
    (hP.mul hC).mul hP.conjTranspose,
    pullMatrix_unitary _ (blockMatrix_unitary U hU), ?_⟩
  change flattenBlocks (blockMatrix U * centralPair A B * blockMatrix V) =
    flattenBlocks (blockMatrix U) * Pᴴ * (P*C*Pᴴ) * P * flattenBlocks (blockMatrix V)
  rw [flattenBlocks_mul,flattenBlocks_mul]
  change flattenBlocks (blockMatrix U) * C * flattenBlocks (blockMatrix V) = _
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Pᴴ P, hP.1, Matrix.one_mul]

section Relabel
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

@[simp] theorem pullMatrix_symm (e : β ≃ α) (A : Matrix α α 𝕜) :
    pullMatrix e.symm (pullMatrix e A) = A := by ext <;> simp_all [pullMatrix]

end Relabel

def unflattenBlocks (A : KMat 𝕜 (k*b)) := pullMatrix finProdFinEquiv A

@[simp] theorem flatten_unflatten (A : KMat 𝕜 (k*b)) :
    flattenBlocks (unflattenBlocks A) = A := pullMatrix_symm finProdFinEquiv A



/-- Extract the consecutive diagonal blocks without any choice. -/
def flatBlocks (A : KMat 𝕜 (k*b)) (i : Fin k) := fun a c => A (finProdFinEquiv (i,a)) (finProdFinEquiv (i,c))

theorem unflatten_supported (A : KMat 𝕜 (k*b)) (hA : CBlockDiagonal b A) :
    unflattenBlocks A = blockMatrix (flatBlocks A) := by
  ext ⟨i,a⟩ ⟨j,c⟩
  by_cases hij : i=j
  · simp_all [blockMatrix,flatBlocks,pullMatrix,unflattenBlocks]
  · change A (finProdFinEquiv (i,a)) (finProdFinEquiv (j,c)) =
      (if i=j then _ else 0)
    rw [if_neg hij]
    apply hA
    change (finProdFinEquiv (i,a)).val / b ≠ (finProdFinEquiv (j,c)).val / b
    rw [flat_block_label,flat_block_label]
    exact fun h => hij (Fin.ext h)

theorem flatten_extracted_blocks (A : KMat 𝕜 (k*b))
    (hA : CBlockDiagonal b A) : flattenBlocks (blockMatrix (flatBlocks A)) = A := by
  rw [← unflatten_supported A hA,flatten_unflatten]

theorem blockMatrix_unitary_component 
    (hB : Unitary (blockMatrix B)) (i : Fin k) : Unitary (B i) := by
  apply GS.MatrixBase.Unitary.of_conjTranspose_mul
  have he := hB.1
  rw [blockMatrix_conjTranspose,blockMatrix_mul] at he
  ext a c
  simpa [blockMatrix,Matrix.one_apply] using congrFun (congrFun he (i,a)) (i,c)

theorem flatBlocks_unitary (A : KMat 𝕜 (k*b))
    (hs : CBlockDiagonal b A) (hA : Unitary A) (i : Fin k) :
    Unitary (flatBlocks A i) := by
  have h := pullMatrix_unitary finProdFinEquiv hA
  change Unitary (unflattenBlocks A) at h
  rw [unflatten_supported A hs] at h
  exact blockMatrix_unitary_component _ h i

theorem centralPair_unitary_components (A B : KMat 𝕜 q)
    (h : Unitary (centralPair A B)) : Unitary A ∧ Unitary B := by
  rw [centralPair_as_blocks] at h
  have hh := pullMatrix_unitary (Equiv.prodComm (Fin q) (Fin 2)).symm h
  
  exact ⟨blockMatrix_unitary_component _ hh 0,
    blockMatrix_unitary_component _ hh 1⟩

theorem inverse_conjugate_apply {n : ℕ} (σ : Equiv.Perm (Fin n))
    (D : KMat 𝕜 n) (i j : Fin n) :
    ((cPermMatrix (𝕜 := 𝕜) σ)ᴴ * D * cPermMatrix (𝕜 := 𝕜) σ) i j = D (σ i) (σ j) := by aesop

/-- Recover the two q-by-q middle blocks from the scalar supported factor. -/
theorem extract_middle_pair (D : KMat 𝕜 (q*2))
    (hs : CBlockDiagonal q D) (hD : Unitary D) :
    ∃ A B : KMat 𝕜 q, Unitary A ∧ Unitary B ∧
      flattenBlocks (centralPair A B) =
        (cPermMatrix (𝕜 := 𝕜) (scalarShuffle q 2))ᴴ * D * cPermMatrix (𝕜 := 𝕜) (scalarShuffle q 2) := by
  let σ := scalarShuffle q 2
  let P := cPermMatrix (𝕜 := 𝕜) σ
  let C := unflattenBlocks (Pᴴ * D * P)
  have hentry (i j : Fin q) (a b : Fin 2) :
      C (i,a) (j,b) = D (σ (finProdFinEquiv (i,a))) (σ (finProdFinEquiv (j,b))) :=
    inverse_conjugate_apply σ D _ _
  have hcross (i j : Fin q) (a b : Fin 2) (hab : a≠b) : C (i,a) (j,b)=0 := by
    rw [hentry]
    apply hs
    have hi := shuffle_block_label (finProdFinEquiv (i,a))
    have hj := shuffle_block_label (finProdFinEquiv (j,b))
    simp only [Equiv.symm_apply_apply] at hi hj
    change (scalarShuffle q 2 (finProdFinEquiv (i,a))).val/q ≠
      (scalarShuffle q 2 (finProdFinEquiv (j,b))).val/q
    rw [hi,hj]
    exact fun h => hab (Fin.ext h)
  let A : KMat 𝕜 q := fun i j => C (i,0) (j,0)
  let B : KMat 𝕜 q := fun i j => C (i,1) (j,1)
  have he : C = centralPair A B := by
    ext ⟨i,a⟩ ⟨j,b⟩
    fin_cases a,b <;>
      simp [centralPair,diagTwo,A,B,hcross]
  have hP : Unitary P := cPerm_unitary (𝕜 := 𝕜) _
  have hC : Unitary C := pullMatrix_unitary _ ((hP.conjTranspose.mul hD).mul hP)
  rw [he] at hC
  obtain ⟨hA,hB⟩ := centralPair_unitary_components A B hC
  refine ⟨A,B,hA,hB,?_⟩
  rw [← he]
  exact flatten_unflatten _

/-- Exact block description of the original scalar-shuffle family. -/
theorem mem_localFamily_iff_block_sandwich (M : KMat 𝕜 (q*2)) :
    M ∈ localFamily q ↔
      ∃ (U V : Fin q → KMat 𝕜 2) (A B : KMat 𝕜 q),
        (∀ i, Unitary (U i)) ∧ (∀ j, Unitary (V j)) ∧
        Unitary A ∧ Unitary B ∧
        M = flattenBlocks (blockMatrix U * centralPair A B * blockMatrix V) := by
  constructor
  · rintro ⟨B₁,B₂,B₃,hs₁,hs₂,hs₃,ho₁,ho₂,ho₃,hM⟩
    obtain ⟨A,B,hA,hB,hAB⟩ := extract_middle_pair B₂ hs₂ ho₂
    refine ⟨flatBlocks B₃,flatBlocks B₁,A,B,flatBlocks_unitary B₃ hs₃ ho₃,
      flatBlocks_unitary B₁ hs₁ ho₁,hA,hB,?_⟩
    rw [flattenBlocks_mul,flattenBlocks_mul,flatten_extracted_blocks B₃ hs₃,
      flatten_extracted_blocks B₁ hs₁,hAB,hM]
    simp only [GS.MatrixFactor.product3,Matrix.mul_assoc]
  · simp_all [block_sandwich_mem_localFamily]

end GS.MatrixBlocks
