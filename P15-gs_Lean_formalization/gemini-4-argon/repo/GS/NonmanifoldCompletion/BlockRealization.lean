module

public import GS.Continuation.ExponentialCurves
public import GS.GlobalGeometry.SharedAlgebra
public import GS.Unitary.Factorization

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Matrix GS GS.Extensions GS.Continuation GS.UnitaryGeometry
open scoped BigOperators

namespace GS.NonmanifoldCompletion

def diagTwo {R : Type*} [Zero R] (a b : R) : Matrix (Fin 2) (Fin 2) R := Matrix.diagonal ![a, b]

variable {𝕂 : Type} [RCLike 𝕂]

abbrev MatrixUnitary {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α 𝕂) : Prop := Aᴴ * A = 1 ∧ A * Aᴴ = 1

namespace MatrixUnitary
variable {α : Type*} [Fintype α] [DecidableEq α] {A B : Matrix α α 𝕂}
theorem conjTranspose (h : MatrixUnitary A) : MatrixUnitary Aᴴ :=
  ⟨by simpa using h.2, by simpa using h.1⟩
theorem mul (hA : MatrixUnitary A) (hB : MatrixUnitary B) : MatrixUnitary (A * B) :=
  ⟨by calc (A * B)ᴴ * (A * B) = Bᴴ * (Aᴴ * A) * B := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = 1 := by rw [hA.1]; simpa using hB.1,
   by calc (A * B) * (A * B)ᴴ = A * (B * Bᴴ) * Aᴴ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = 1 := by rw [hB.2]; simpa using hA.2⟩
end MatrixUnitary

def kLocalFamily (𝕂 : Type) [RCLike 𝕂] (q : ℕ) : Set (KMat 𝕂 (q * 2)) :=
  let P := kPermMatrix 𝕂 (scalarShuffle q 2)
  {M | KInA3Unitary 2 q 2 P Pᴴ M}

section Relabel
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

def pullMatrix (e : β ≃ α) (A : Matrix α α 𝕂) : Matrix β β 𝕂 :=
  fun i j => A (e i) (e j)

@[simp] theorem pullMatrix_conjTranspose (e : β ≃ α) (A : Matrix α α 𝕂) :
    pullMatrix e Aᴴ = (pullMatrix e A)ᴴ := rfl
alias pullMatrix_transpose := pullMatrix_conjTranspose

@[simp] theorem pullMatrix_one (e : β ≃ α) :
    pullMatrix e (1 : Matrix α α 𝕂) = 1 := by
  ext i j; simp [pullMatrix, Matrix.one_apply, e.injective.eq_iff]

theorem pullMatrix_mul (e : β ≃ α) (A B : Matrix α α 𝕂) :
    pullMatrix e (A * B) = pullMatrix e A * pullMatrix e B := by
  classical
  ext i j
  exact (Fintype.sum_equiv e (fun k => A (e i) (e k) * B (e k) (e j))
    (fun k => A (e i) k * B k (e j)) (fun _ => rfl)).symm

theorem pullMatrix_unitary (e : β ≃ α) {A : Matrix α α 𝕂}
    (hA : MatrixUnitary A) : MatrixUnitary (pullMatrix e A) :=
  ⟨by rw [← pullMatrix_conjTranspose, ← pullMatrix_mul, hA.1, pullMatrix_one],
   by rw [← pullMatrix_conjTranspose, ← pullMatrix_mul, hA.2, pullMatrix_one]⟩
alias pullMatrix_orthogonal := pullMatrix_unitary

@[simp] theorem pullMatrix_symm (e : β ≃ α) (A : Matrix α α 𝕂) :
    pullMatrix e.symm (pullMatrix e A) = A := by
  ext i j; simp [pullMatrix]

end Relabel

def flattenBlocks {k b : ℕ}
    (A : Matrix (Fin k × Fin b) (Fin k × Fin b) 𝕂) : KMat 𝕂 (k * b) :=
  pullMatrix finProdFinEquiv.symm A

@[simp] theorem flattenBlocks_apply {k b : ℕ}
    (A : Matrix (Fin k × Fin b) (Fin k × Fin b) 𝕂) (i j : Fin k × Fin b) :
    flattenBlocks A (finProdFinEquiv i) (finProdFinEquiv j) = A i j := by
  simp [flattenBlocks, pullMatrix]

theorem flattenBlocks_mul {k b : ℕ}
    (A B : Matrix (Fin k × Fin b) (Fin k × Fin b) 𝕂) :
    flattenBlocks (A * B) = flattenBlocks A * flattenBlocks B :=
  pullMatrix_mul _ A B

theorem flat_block_label {k b : ℕ} (p : Fin k × Fin b) :
    (finProdFinEquiv p).val / b = p.1.val := by
  have hb : 0 < b := lt_of_le_of_lt (Nat.zero_le _) p.2.isLt
  change (p.2.val + b * p.1.val) / b = p.1.val
  rw [Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt p.2.isLt, Nat.zero_add]

theorem flatten_blockDiagonal {k b : ℕ} (B : Fin k → KMat 𝕂 b) :
    KBlockDiagonal b (flattenBlocks (blockMatrix B)) := by
  intro i j hij
  let x := finProdFinEquiv.symm i
  let y := finProdFinEquiv.symm j
  have hxy : x.1 ≠ y.1 := by
    intro h
    have hi := flat_block_label x
    have hj := flat_block_label y
    simp only [x, y, Equiv.apply_symm_apply] at hi hj
    exact hij (hi.trans ((congrArg Fin.val h).trans hj.symm))
  exact if_neg hxy

@[simp] theorem blockMatrix_conjTranspose {k b : ℕ} (B : Fin k → KMat 𝕂 b) :
    (blockMatrix B)ᴴ = blockMatrix (fun i => (B i)ᴴ) := by
  ext ⟨i, a⟩ ⟨j, c⟩
  by_cases h : i = j
  · subst j; simp [blockMatrix]
  · simp [blockMatrix, h, Ne.symm h]
alias blockMatrix_transpose := blockMatrix_conjTranspose

@[simp] theorem blockMatrix_mul {k b : ℕ} (B C : Fin k → KMat 𝕂 b) :
    blockMatrix B * blockMatrix C = blockMatrix (fun i => B i * C i) := by
  classical
  ext ⟨i, a⟩ ⟨j, c⟩
  by_cases h : i = j
  · subst j; simp [Matrix.mul_apply, blockMatrix, Fintype.sum_prod_type]
  · simp [Matrix.mul_apply, blockMatrix, Fintype.sum_prod_type, h]

@[simp] theorem blockMatrix_one (k b : ℕ) :
    blockMatrix (fun _ : Fin k => (1 : KMat 𝕂 b)) = 1 := by
  ext ⟨i, a⟩ ⟨j, c⟩
  by_cases hi : i = j <;> by_cases ha : a = c <;>
    simp [blockMatrix, Matrix.one_apply, hi, ha]

theorem blockMatrix_unitary {k b : ℕ} (B : Fin k → KMat 𝕂 b)
    (hB : ∀ i, MatrixUnitary (B i)) : MatrixUnitary (blockMatrix B) := by
  constructor
  · rw [blockMatrix_conjTranspose, blockMatrix_mul,
      show (fun i => (B i)ᴴ * B i) = fun _ => (1 : KMat 𝕂 b) from funext fun i => (hB i).1,
      blockMatrix_one]
  · rw [blockMatrix_conjTranspose, blockMatrix_mul,
      show (fun i => B i * (B i)ᴴ) = fun _ => (1 : KMat 𝕂 b) from funext fun i => (hB i).2,
      blockMatrix_one]
alias blockMatrix_orthogonal := blockMatrix_unitary

def centralPair {q : ℕ} (A B : KMat 𝕂 q) :
    Matrix (Fin q × Fin 2) (Fin q × Fin 2) 𝕂 :=
  fun i j => diagTwo (A i.1 j.1) (B i.1 j.1) i.2 j.2

theorem centralPair_as_blocks {q : ℕ} (A B : KMat 𝕂 q) :
    centralPair A B = pullMatrix (Equiv.prodComm _ _) (blockMatrix ![A, B]) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases a <;> fin_cases b <;> simp [centralPair, pullMatrix, blockMatrix, diagTwo]

theorem centralPair_unitary {q : ℕ} (A B : KMat 𝕂 q)
    (hA : MatrixUnitary A) (hB : MatrixUnitary B) : MatrixUnitary (centralPair A B) := by
  rw [centralPair_as_blocks]
  refine pullMatrix_unitary _ (blockMatrix_unitary _ fun i => ?_)
  fin_cases i
  · exact hA
  · exact hB
alias centralPair_orthogonal := centralPair_unitary

def shuffledMiddle {q : ℕ} (A B : KMat 𝕂 q) : KMat 𝕂 (q * 2) :=
  let P := kPermMatrix 𝕂 (scalarShuffle q 2)
  P * flattenBlocks (centralPair A B) * Pᴴ

theorem shuffle_block_label {q : ℕ} (i : Fin (q * 2)) :
    (scalarShuffle q 2 i).val / q = (finProdFinEquiv.symm i).2.val := by
  let p := finProdFinEquiv.symm i
  have hcast {m n : ℕ} (h : m = n) (a : Fin m) : (cast (congrArg Fin h) a).val = a.val := by
    cases h; rfl
  change (cast (congrArg Fin (Nat.mul_comm 2 q)) (finProdFinEquiv (p.2, p.1))).val / q = p.2.val
  rw [hcast (Nat.mul_comm 2 q)]
  exact flat_block_label (p.2, p.1)

theorem shuffledMiddle_blockDiagonal {q : ℕ} (A B : KMat 𝕂 q) :
    KBlockDiagonal q (shuffledMiddle A B) := by
  intro i j hij
  let σ := scalarShuffle q 2
  let x := finProdFinEquiv.symm (σ.symm i)
  let y := finProdFinEquiv.symm (σ.symm j)
  have hxy : x.2 ≠ y.2 := by
    intro h
    have hi := shuffle_block_label (σ.symm i)
    have hj := shuffle_block_label (σ.symm j)
    simp only [σ, Equiv.apply_symm_apply] at hi hj
    exact hij (hi.trans ((congrArg Fin.val h).trans hj.symm))
  change (kPermMatrix 𝕂 σ * flattenBlocks (centralPair A B) * (kPermMatrix 𝕂 σ)ᴴ) i j = 0
  rw [kPerm_conjugate_apply]
  change diagTwo (A x.1 y.1) (B x.1 y.1) x.2 y.2 = 0
  have hdiag (a b : Fin 2) (hab : a ≠ b) (s t : 𝕂) : diagTwo s t a b = 0 := by
    fin_cases a <;> fin_cases b <;> simp_all [diagTwo]
  exact hdiag x.2 y.2 hxy _ _

theorem small_block_sandwich {q : ℕ} (U V : Fin q → KMat 𝕂 2) (A B : KMat 𝕂 q)
    (i j : Fin q) (a b : Fin 2) :
    (blockMatrix U * centralPair A B * blockMatrix V) (i, a) (j, b) =
      (U i * diagTwo (A i j) (B i j) * V j) a b := by
  classical
  simp [Matrix.mul_apply, blockMatrix, centralPair, Fintype.sum_prod_type]

theorem block_sandwich_mem_localFamily {q : ℕ} (U V : Fin q → KMat 𝕂 2)
    (A B : KMat 𝕂 q) (hU : ∀ i, MatrixUnitary (U i)) (hV : ∀ j, MatrixUnitary (V j))
    (hA : MatrixUnitary A) (hB : MatrixUnitary B) :
    flattenBlocks (blockMatrix U * centralPair A B * blockMatrix V) ∈ kLocalFamily 𝕂 q := by
  let P := kPermMatrix 𝕂 (scalarShuffle q 2)
  let C := flattenBlocks (centralPair A B)
  have hP : IsUnitary P := kPerm_unitary _
  have hC : IsUnitary C := pullMatrix_unitary _ (centralPair_unitary A B hA hB)
  refine ⟨flattenBlocks (blockMatrix V), shuffledMiddle A B,
    flattenBlocks (blockMatrix U), flatten_blockDiagonal V,
    shuffledMiddle_blockDiagonal A B, flatten_blockDiagonal U,
    pullMatrix_unitary _ (blockMatrix_unitary V hV),
    (hP.mul hC).mul hP.conjTranspose,
    pullMatrix_unitary _ (blockMatrix_unitary U hU), ?_⟩
  change flattenBlocks (blockMatrix U * centralPair A B * blockMatrix V) =
    flattenBlocks (blockMatrix U) * Pᴴ * (P * C * Pᴴ) * P * flattenBlocks (blockMatrix V)
  rw [flattenBlocks_mul, flattenBlocks_mul]
  symm
  calc flattenBlocks (blockMatrix U) * Pᴴ * (P * C * Pᴴ) * P * flattenBlocks (blockMatrix V) =
        flattenBlocks (blockMatrix U) * (Pᴴ * P) * C * (Pᴴ * P) * flattenBlocks (blockMatrix V) := by
          simp only [Matrix.mul_assoc]
    _ = _ := by rw [hP.1, Matrix.mul_one, Matrix.mul_one]

def unflattenBlocks {k b : ℕ} (A : KMat 𝕂 (k * b)) :
    Matrix (Fin k × Fin b) (Fin k × Fin b) 𝕂 := pullMatrix finProdFinEquiv A

@[simp] theorem flatten_unflatten {k b : ℕ} (A : KMat 𝕂 (k * b)) :
    flattenBlocks (unflattenBlocks A) = A :=
  pullMatrix_symm finProdFinEquiv A

def flatBlocks {k b : ℕ} (A : KMat 𝕂 (k * b)) (i : Fin k) : KMat 𝕂 b :=
  fun a c => A (finProdFinEquiv (i, a)) (finProdFinEquiv (i, c))

theorem unflatten_supported {k b : ℕ} (A : KMat 𝕂 (k * b)) (hA : KBlockDiagonal b A) :
    unflattenBlocks A = blockMatrix (flatBlocks A) := by
  ext ⟨i, a⟩ ⟨j, c⟩
  by_cases hij : i = j
  · subst j; simp [unflattenBlocks, pullMatrix, blockMatrix, flatBlocks]
  · change A (finProdFinEquiv (i, a)) (finProdFinEquiv (j, c)) = (if i = j then _ else 0)
    rw [if_neg hij]
    apply hA
    change (finProdFinEquiv (i, a)).val / b ≠ (finProdFinEquiv (j, c)).val / b
    rw [flat_block_label, flat_block_label]
    exact fun h => hij (Fin.ext h)

theorem flatten_extracted_blocks {k b : ℕ} (A : KMat 𝕂 (k * b))
    (hA : KBlockDiagonal b A) : flattenBlocks (blockMatrix (flatBlocks A)) = A := by
  rw [← unflatten_supported A hA, flatten_unflatten]

theorem blockMatrix_unitary_component {k b : ℕ} (B : Fin k → KMat 𝕂 b)
    (hB : MatrixUnitary (blockMatrix B)) (i : Fin k) : MatrixUnitary (B i) := by
  constructor
  · have he := hB.1
    rw [blockMatrix_conjTranspose, blockMatrix_mul] at he
    ext a c
    simpa [blockMatrix, Matrix.one_apply] using congrFun (congrFun he (i, a)) (i, c)
  · have he := hB.2
    rw [blockMatrix_conjTranspose, blockMatrix_mul] at he
    ext a c
    simpa [blockMatrix, Matrix.one_apply] using congrFun (congrFun he (i, a)) (i, c)
alias blockMatrix_orthogonal_component := blockMatrix_unitary_component

theorem flatBlocks_unitary {k b : ℕ} (A : KMat 𝕂 (k * b))
    (hs : KBlockDiagonal b A) (hA : MatrixUnitary A) (i : Fin k) :
    MatrixUnitary (flatBlocks A i) := by
  have h : MatrixUnitary (unflattenBlocks A) := pullMatrix_unitary finProdFinEquiv hA
  rw [unflatten_supported A hs] at h
  exact blockMatrix_unitary_component _ h i
alias flatBlocks_orthogonal := flatBlocks_unitary

theorem centralPair_unitary_components {q : ℕ} (A B : KMat 𝕂 q)
    (h : MatrixUnitary (centralPair A B)) : MatrixUnitary A ∧ MatrixUnitary B := by
  have hh := pullMatrix_unitary (Equiv.prodComm (Fin 2) (Fin q)) h
  have he : pullMatrix (Equiv.prodComm (Fin 2) (Fin q)) (centralPair A B) =
      blockMatrix ![A, B] := by
    ext ⟨a, i⟩ ⟨b, j⟩
    fin_cases a <;> fin_cases b <;> simp [pullMatrix, centralPair, blockMatrix, diagTwo]
  rw [he] at hh
  exact ⟨blockMatrix_unitary_component _ hh 0, blockMatrix_unitary_component _ hh 1⟩
alias centralPair_orthogonal_components := centralPair_unitary_components

theorem inverse_conjugate_apply {n : ℕ} (σ : Equiv.Perm (Fin n))
    (D : KMat 𝕂 n) (i j : Fin n) :
    ((kPermMatrix 𝕂 σ)ᴴ * D * kPermMatrix 𝕂 σ) i j = D (σ i) (σ j) := by
  rw [kPerm_conjTranspose]
  simpa only [Matrix.mul_assoc, kPerm_conjTranspose, Equiv.symm_symm] using
    kPerm_conjugate_apply σ.symm D i j

theorem extract_middle_pair {q : ℕ} (D : KMat 𝕂 (q * 2))
    (hs : KBlockDiagonal q D) (hD : MatrixUnitary D) :
    ∃ A B : KMat 𝕂 q, MatrixUnitary A ∧ MatrixUnitary B ∧
      flattenBlocks (centralPair A B) =
        (kPermMatrix 𝕂 (scalarShuffle q 2))ᴴ * D * kPermMatrix 𝕂 (scalarShuffle q 2) := by
  let σ := scalarShuffle q 2
  let P := kPermMatrix 𝕂 σ
  let C := unflattenBlocks (Pᴴ * D * P)
  have hentry (i j : Fin q) (a b : Fin 2) :
      C (i, a) (j, b) = D (σ (finProdFinEquiv (i, a))) (σ (finProdFinEquiv (j, b))) :=
    inverse_conjugate_apply σ D _ _
  have hcross (i j : Fin q) (a b : Fin 2) (hab : a ≠ b) : C (i, a) (j, b) = 0 := by
    rw [hentry]
    apply hs
    have hi := shuffle_block_label (finProdFinEquiv (i, a))
    have hj := shuffle_block_label (finProdFinEquiv (j, b))
    simp only [Equiv.symm_apply_apply] at hi hj
    change (scalarShuffle q 2 (finProdFinEquiv (i, a))).val / q ≠
      (scalarShuffle q 2 (finProdFinEquiv (j, b))).val / q
    rw [hi, hj]
    exact fun h => hab (Fin.ext h)
  let A : KMat 𝕂 q := fun i j => C (i, 0) (j, 0)
  let B : KMat 𝕂 q := fun i j => C (i, 1) (j, 1)
  have he : C = centralPair A B := by
    ext ⟨i, a⟩ ⟨j, b⟩
    fin_cases a <;> fin_cases b <;> simp [centralPair, diagTwo, A, B, hcross]
  have hP : IsUnitary P := kPerm_unitary _
  have hC : MatrixUnitary C := pullMatrix_unitary _ ((hP.conjTranspose.mul hD).mul hP)
  rw [he] at hC
  obtain ⟨hA, hB⟩ := centralPair_unitary_components A B hC
  refine ⟨A, B, hA, hB, ?_⟩
  rw [← he]
  exact flatten_unflatten _

theorem mem_localFamily_iff_block_sandwich {q : ℕ} (M : KMat 𝕂 (q * 2)) :
    M ∈ kLocalFamily 𝕂 q ↔
      ∃ (U V : Fin q → KMat 𝕂 2) (A B : KMat 𝕂 q),
        (∀ i, MatrixUnitary (U i)) ∧ (∀ j, MatrixUnitary (V j)) ∧
        MatrixUnitary A ∧ MatrixUnitary B ∧
        M = flattenBlocks (blockMatrix U * centralPair A B * blockMatrix V) := by
  constructor
  · rintro ⟨B₁, B₂, B₃, hs₁, hs₂, hs₃, ho₁, ho₂, ho₃, hM⟩
    obtain ⟨A, B, hA, hB, hAB⟩ := extract_middle_pair B₂ hs₂ ho₂
    refine ⟨flatBlocks B₃, flatBlocks B₁, A, B, flatBlocks_unitary B₃ hs₃ ho₃,
      flatBlocks_unitary B₁ hs₁ ho₁, hA, hB, ?_⟩
    rw [flattenBlocks_mul, flattenBlocks_mul, flatten_extracted_blocks B₃ hs₃,
      flatten_extracted_blocks B₁ hs₁, hAB, hM]
    simp only [GS.UnitaryGeometry.kProduct3, Matrix.mul_assoc]
  · rintro ⟨U, V, A, B, hU, hV, hA, hB, rfl⟩
    exact block_sandwich_mem_localFamily U V A B hU hV hA hB

abbrev KSmallBlockParameters (𝕂 : Type) (q : ℕ) :=
  (Fin q → KMat 𝕂 2) × KMat 𝕂 q × KMat 𝕂 q × (Fin q → KMat 𝕂 2)

def kSmallFactorSet (𝕂 : Type) [RCLike 𝕂] (q : ℕ) : Set (KSmallBlockParameters 𝕂 q) :=
  {p | (∀ i, MatrixUnitary (p.1 i)) ∧ MatrixUnitary p.2.1 ∧ MatrixUnitary p.2.2.1 ∧
    (∀ j, MatrixUnitary (p.2.2.2 j))}

def smallFactorMap {q : ℕ} (p : KSmallBlockParameters 𝕂 q) : KMat 𝕂 (q * 2) :=
  flattenBlocks (blockMatrix p.1 * centralPair p.2.1 p.2.2.1 * blockMatrix p.2.2.2)

theorem smallFactorMap_block {q : ℕ} (p : KSmallBlockParameters 𝕂 q)
    (i j : Fin q) (a b : Fin 2) :
    smallFactorMap p (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b)) =
      (p.1 i * diagTwo (p.2.1 i j) (p.2.2.1 i j) * p.2.2.2 j) a b := by
  rw [smallFactorMap, flattenBlocks_apply, small_block_sandwich]

theorem continuous_smallFactorMap (q : ℕ) : Continuous (@smallFactorMap 𝕂 _ q) := by
  have he : (@smallFactorMap 𝕂 _ q) = fun p i j =>
      let x : Fin q × Fin 2 := finProdFinEquiv.symm i
      let y : Fin q × Fin 2 := finProdFinEquiv.symm j
      (p.1 x.1 * diagTwo (p.2.1 x.1 y.1) (p.2.2.1 x.1 y.1) * p.2.2.2 y.1) x.2 y.2 := by
    funext p i j
    exact small_block_sandwich _ _ _ _ _ _ _ _
  rw [he]
  have hdiag (i j : Fin q) : Continuous (fun p : KSmallBlockParameters 𝕂 q =>
      diagTwo (p.2.1 i j) (p.2.2.1 i j)) := by
    apply continuous_pi; intro a; apply continuous_pi; intro b
    fin_cases a <;> fin_cases b <;> simp [diagTwo] <;> fun_prop
  fun_prop

theorem isCompact_unitary_set (n : ℕ) : IsCompact {A : KMat 𝕂 n | MatrixUnitary A} := by
  have h : IsCompact {A : KMat 𝕂 n | GS.SharedGeometry.KSupported (fun _ : Fin n => 0) A ∧ GS.SharedGeometry.KUnitary A} :=
    isCompact_iff_compactSpace.mpr
      (inferInstanceAs (CompactSpace (GS.SharedGeometry.BlockK 𝕂 (fun _ : Fin n => 0))))
  simpa [GS.SharedGeometry.KSupported, GS.SharedGeometry.KUnitary] using h

theorem isCompact_kSmallFactorSet (q : ℕ) : IsCompact (kSmallFactorSet 𝕂 q) := by
  have houter : IsCompact {U : Fin q → KMat 𝕂 2 | ∀ i, MatrixUnitary (U i)} :=
    isCompact_pi_infinite (fun _ => isCompact_unitary_set 2)
  exact houter.prod ((isCompact_unitary_set q).prod ((isCompact_unitary_set q).prod houter))

theorem image_kSmallFactorMap (q : ℕ) :
    (@smallFactorMap 𝕂 _ q) '' kSmallFactorSet 𝕂 q = kLocalFamily 𝕂 q := by
  ext M
  constructor
  · rintro ⟨⟨U, A, B, V⟩, ⟨hU, hA, hB, hV⟩, rfl⟩
    exact block_sandwich_mem_localFamily U V A B hU hV hA hB
  · intro hM
    obtain ⟨U, V, A, B, hU, hV, hA, hB, he⟩ := (mem_localFamily_iff_block_sandwich M).mp hM
    exact ⟨(U, A, B, V), ⟨hU, hA, hB, hV⟩, he.symm⟩

abbrev SmallBlockParameters (q : ℕ) := KSmallBlockParameters ℝ q
abbrev smallFactorSet (q : ℕ) := kSmallFactorSet ℝ q
theorem isCompact_smallFactorSet (q : ℕ) : IsCompact (smallFactorSet q) :=
  isCompact_kSmallFactorSet (𝕂 := ℝ) q
theorem image_smallFactorMap (q : ℕ) :
    (@smallFactorMap ℝ _ q) '' smallFactorSet q = localFamily q :=
  image_kSmallFactorMap (𝕂 := ℝ) q

theorem smallFactorMap_eq_base_blocks {q : ℕ} (Q₀ : Mat q)
    (p : SmallBlockParameters q) (he : smallFactorMap p = basePoint Q₀) (i j : Fin q) :
    p.1 i * diagTwo (p.2.1 i j) (p.2.2.1 i j) * p.2.2.2 j = Q₀ i j • (1 : Mat 2) := by
  ext a b
  have hh := congrFun (congrFun he (finProdFinEquiv (i, a))) (finProdFinEquiv (j, b))
  rw [smallFactorMap_block] at hh
  have hi : finProdFinEquiv.symm (finProdFinEquiv (i, a)) = (i, a) := Equiv.symm_apply_apply _ _
  have hj : finProdFinEquiv.symm (finProdFinEquiv (j, b)) = (j, b) := Equiv.symm_apply_apply _ _
  dsimp only [basePoint] at hh
  rw [hi, hj] at hh
  exact hh

end GS.NonmanifoldCompletion

namespace GS.UnitaryNonmanifold
export GS (blockMatrix)
export GS.NonmanifoldCompletion (
  diagTwo MatrixUnitary pullMatrix pullMatrix_conjTranspose pullMatrix_one
  pullMatrix_mul pullMatrix_unitary pullMatrix_symm flattenBlocks
  flattenBlocks_apply flattenBlocks_mul flat_block_label flatten_blockDiagonal
  blockMatrix_conjTranspose blockMatrix_mul blockMatrix_one blockMatrix_unitary
  centralPair centralPair_as_blocks centralPair_unitary shuffledMiddle
  shuffle_block_label shuffledMiddle_blockDiagonal small_block_sandwich
  block_sandwich_mem_localFamily unflattenBlocks flatten_unflatten flatBlocks
  unflatten_supported flatten_extracted_blocks blockMatrix_unitary_component
  flatBlocks_unitary centralPair_unitary_components inverse_conjugate_apply
  extract_middle_pair mem_localFamily_iff_block_sandwich
)
abbrev localFamily (q : ℕ) : Set (CMat (q * 2)) :=
  GS.NonmanifoldCompletion.kLocalFamily ℂ q
end GS.UnitaryNonmanifold

namespace GS.UnitaryLocalModel
open GS.NonmanifoldCompletion

abbrev SmallBlockParameters (q : ℕ) := KSmallBlockParameters ℂ q
abbrev smallFactorSet (q : ℕ) := kSmallFactorSet ℂ q
export GS.NonmanifoldCompletion (smallFactorMap smallFactorMap_block continuous_smallFactorMap isCompact_unitary_set)

theorem isCompact_smallFactorSet (q : ℕ) : IsCompact (smallFactorSet q) :=
  isCompact_kSmallFactorSet (𝕂 := ℂ) q

theorem image_smallFactorMap (q : ℕ) :
    (@smallFactorMap ℂ _ q) '' smallFactorSet q = GS.UnitaryNonmanifold.localFamily q :=
  image_kSmallFactorMap (𝕂 := ℂ) q

abbrev SmallFactorSpace (q : ℕ) := {p : SmallBlockParameters q // p ∈ smallFactorSet q}

instance smallFactorSpace_compactSpace (q : ℕ) : CompactSpace (SmallFactorSpace q) :=
  isCompact_iff_compactSpace.mp (isCompact_smallFactorSet q)

def smallFactorValue (q : ℕ) (p : SmallFactorSpace q) : CMat (q * 2) :=
  smallFactorMap p.val

theorem continuous_smallFactorValue (q : ℕ) : Continuous (smallFactorValue q) :=
  (continuous_smallFactorMap q).comp continuous_subtype_val

theorem range_smallFactorValue (q : ℕ) :
    Set.range (smallFactorValue q) = GS.UnitaryNonmanifold.localFamily q := by
  rw [← image_smallFactorMap]
  ext M; constructor
  · rintro ⟨p, rfl⟩; exact ⟨p.val, p.property, rfl⟩
  · rintro ⟨p, hp, rfl⟩; exact ⟨⟨p, hp⟩, rfl⟩

end GS.UnitaryLocalModel
