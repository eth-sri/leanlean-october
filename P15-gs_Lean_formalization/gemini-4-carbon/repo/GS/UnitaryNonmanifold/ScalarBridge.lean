module

public import GS.Unitary.Factorization
public import GS.OriginalLocalModel

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Matrix GS GS.UnitaryGeometry
open scoped BigOperators

namespace GS.UnitaryNonmanifold

def diagTwo {𝕂 : Type*} [Zero 𝕂] (a b : 𝕂) : Matrix (Fin 2) (Fin 2) 𝕂 := !![a, 0; 0, b]

def blockMatrix {𝕂 : Type*} [Zero 𝕂] {k b : ℕ} (B : Fin k → KMat 𝕂 b) :
    Matrix (Fin k × Fin b) (Fin k × Fin b) 𝕂 :=
  fun i j => if i.1 = j.1 then B i.1 i.2 j.2 else 0

def pullMatrix {𝕂 α β : Type*} (e : β ≃ α) (A : Matrix α α 𝕂) : Matrix β β 𝕂 :=
  fun i j => A (e i) (e j)

section Generic
variable {𝕂 : Type*} [RCLike 𝕂]

@[simp] theorem pullMatrix_conjTranspose {α β : Type*} (e : β ≃ α) (A : Matrix α α 𝕂) :
    pullMatrix e Aᴴ = (pullMatrix e A)ᴴ := rfl

@[simp] theorem pullMatrix_one {α β : Type*} [DecidableEq α] [DecidableEq β] (e : β ≃ α) :
    pullMatrix e (1 : Matrix α α 𝕂) = 1 := by
  ext i j; simp [pullMatrix, Matrix.one_apply, e.injective.eq_iff]

theorem pullMatrix_mul {α β : Type*} [Fintype α] [Fintype β] (e : β ≃ α) (A B : Matrix α α 𝕂) :
    pullMatrix e (A * B) = pullMatrix e A * pullMatrix e B := by
  ext i j; exact (Fintype.sum_equiv e _ _ fun _ => rfl).symm

@[simp] theorem pullMatrix_symm {α β : Type*} (e : β ≃ α) (A : Matrix α α 𝕂) :
    pullMatrix e.symm (pullMatrix e A) = A := by ext i j; simp [pullMatrix]

theorem pullMatrix_kUni {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : β ≃ α) {A : Matrix α α 𝕂} (hA : KUni A) : KUni (pullMatrix e A) :=
  ⟨by rw [← pullMatrix_conjTranspose, ← pullMatrix_mul, hA.1, pullMatrix_one],
   by rw [← pullMatrix_conjTranspose, ← pullMatrix_mul, hA.2, pullMatrix_one]⟩

def flattenBlocks {k b : ℕ} (A : Matrix (Fin k × Fin b) (Fin k × Fin b) 𝕂) : KMat 𝕂 (k * b) :=
  pullMatrix finProdFinEquiv.symm A

def unflattenBlocks {k b : ℕ} (A : KMat 𝕂 (k * b)) : Matrix (Fin k × Fin b) (Fin k × Fin b) 𝕂 :=
  pullMatrix finProdFinEquiv A

@[simp] theorem flattenBlocks_apply {k b : ℕ} (A : Matrix (Fin k × Fin b) (Fin k × Fin b) 𝕂)
    (i j : Fin k × Fin b) : flattenBlocks A (finProdFinEquiv i) (finProdFinEquiv j) = A i j := by
  simp [flattenBlocks, pullMatrix]

theorem flattenBlocks_mul {k b : ℕ} (A B : Matrix (Fin k × Fin b) (Fin k × Fin b) 𝕂) :
    flattenBlocks (A * B) = flattenBlocks A * flattenBlocks B := pullMatrix_mul _ A B

@[simp] theorem flatten_unflatten {k b : ℕ} (A : KMat 𝕂 (k * b)) :
    flattenBlocks (unflattenBlocks A) = A := pullMatrix_symm finProdFinEquiv A

theorem flat_block_label {k b : ℕ} (p : Fin k × Fin b) : (finProdFinEquiv p).val / b = p.1.val := by
  have hb : 0 < b := lt_of_le_of_lt (Nat.zero_le _) p.2.isLt
  change (p.2.val + b * p.1.val) / b = p.1.val
  rw [Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt p.2.isLt, Nat.zero_add]

theorem flatten_kSupported {k b : ℕ} (B : Fin k → KMat 𝕂 b) :
    KSupported (fun i : Fin (k * b) => i.val / b) (flattenBlocks (blockMatrix B)) := fun i j hij => by
  refine ite_eq_right_iff.mpr fun h => (hij ?_).elim
  have hi := flat_block_label (finProdFinEquiv.symm i)
  have hj := flat_block_label (finProdFinEquiv.symm j)
  simp only [Equiv.apply_symm_apply] at hi hj
  exact hi.trans ((congrArg Fin.val h).trans hj.symm)

@[simp] theorem blockMatrix_conjTranspose {k b : ℕ} (B : Fin k → KMat 𝕂 b) :
    (blockMatrix B)ᴴ = blockMatrix fun i => (B i)ᴴ := by
  ext ⟨i, a⟩ ⟨j, c⟩; by_cases h : i = j <;> simp [blockMatrix, h, Ne.symm]

@[simp] theorem blockMatrix_mul {k b : ℕ} (B C : Fin k → KMat 𝕂 b) :
    blockMatrix B * blockMatrix C = blockMatrix fun i => B i * C i := by
  classical
  ext ⟨i, a⟩ ⟨j, c⟩; by_cases h : i = j
  · subst h; simp [Matrix.mul_apply, blockMatrix, Fintype.sum_prod_type]
  · simp [Matrix.mul_apply, blockMatrix, Fintype.sum_prod_type, h]

@[simp] theorem blockMatrix_one (k b : ℕ) : blockMatrix (fun _ : Fin k => (1 : KMat 𝕂 b)) = 1 := by
  ext ⟨i, a⟩ ⟨j, c⟩; by_cases hi : i = j <;> by_cases ha : a = c <;> simp [blockMatrix, Matrix.one_apply, hi, ha]

theorem blockMatrix_kUni {k b : ℕ} (B : Fin k → KMat 𝕂 b) (hB : ∀ i, KUni (B i)) : KUni (blockMatrix B) :=
  ⟨by rw [blockMatrix_conjTranspose, blockMatrix_mul, show (fun i => (B i)ᴴ * B i) = fun _ => 1 from funext fun i => (hB i).1, blockMatrix_one],
   by rw [blockMatrix_conjTranspose, blockMatrix_mul, show (fun i => B i * (B i)ᴴ) = fun _ => 1 from funext fun i => (hB i).2, blockMatrix_one]⟩

theorem blockMatrix_kUni_component {k b : ℕ} (B : Fin k → KMat 𝕂 b) (hB : KUni (blockMatrix B)) (i : Fin k) : KUni (B i) := by
  refine ⟨?_, ?_⟩
  · have he := hB.1; rw [blockMatrix_conjTranspose, blockMatrix_mul] at he
    ext a c; simpa [blockMatrix, Matrix.one_apply] using congrFun (congrFun he (i, a)) (i, c)
  · have he := hB.2; rw [blockMatrix_conjTranspose, blockMatrix_mul] at he
    ext a c; simpa [blockMatrix, Matrix.one_apply] using congrFun (congrFun he (i, a)) (i, c)

def flatBlocks {k b : ℕ} (A : KMat 𝕂 (k * b)) (i : Fin k) : KMat 𝕂 b :=
  fun a c => A (finProdFinEquiv (i, a)) (finProdFinEquiv (i, c))

theorem unflatten_kSupported {k b : ℕ} (A : KMat 𝕂 (k * b))
    (hA : KSupported (fun i : Fin (k * b) => i.val / b) A) :
    unflattenBlocks A = blockMatrix (flatBlocks A) := by
  ext ⟨i, a⟩ ⟨j, c⟩; by_cases hij : i = j
  · subst hij; simp [unflattenBlocks, pullMatrix, blockMatrix, flatBlocks]
  · change A (finProdFinEquiv (i, a)) (finProdFinEquiv (j, c)) = if i = j then _ else 0
    rw [if_neg hij]; apply hA; dsimp only
    rw [flat_block_label, flat_block_label]; exact fun h => hij (Fin.ext h)

theorem flatten_extracted_blocks {k b : ℕ} (A : KMat 𝕂 (k * b))
    (hA : KSupported (fun i : Fin (k * b) => i.val / b) A) :
    flattenBlocks (blockMatrix (flatBlocks A)) = A := by
  rw [← unflatten_kSupported A hA, flatten_unflatten]

theorem flatBlocks_kUni {k b : ℕ} (A : KMat 𝕂 (k * b))
    (hs : KSupported (fun i : Fin (k * b) => i.val / b) A) (hA : KUni A) (i : Fin k) :
    KUni (flatBlocks A i) := by
  have h : KUni (unflattenBlocks A) := pullMatrix_kUni finProdFinEquiv hA
  rw [unflatten_kSupported A hs] at h
  exact blockMatrix_kUni_component _ h i

def centralPair {q : ℕ} (A B : KMat 𝕂 q) : Matrix (Fin q × Fin 2) (Fin q × Fin 2) 𝕂 :=
  fun i j => diagTwo (A i.1 j.1) (B i.1 j.1) i.2 j.2

theorem centralPair_as_blocks {q : ℕ} (A B : KMat 𝕂 q) :
    centralPair A B = pullMatrix (Equiv.prodComm _ _) (blockMatrix ![A, B]) := by
  ext ⟨i, a⟩ ⟨j, b⟩; fin_cases a <;> fin_cases b <;> simp [centralPair, pullMatrix, blockMatrix, diagTwo]

theorem centralPair_kUni {q : ℕ} (A B : KMat 𝕂 q) (hA : KUni A) (hB : KUni B) : KUni (centralPair A B) := by
  rw [centralPair_as_blocks]; exact pullMatrix_kUni _ (blockMatrix_kUni _ fun i => by fin_cases i <;> assumption)

theorem centralPair_kUni_components {q : ℕ} (A B : KMat 𝕂 q) (h : KUni (centralPair A B)) : KUni A ∧ KUni B := by
  have hh := pullMatrix_kUni (Equiv.prodComm (Fin 2) (Fin q)) h
  rw [show pullMatrix (Equiv.prodComm (Fin 2) (Fin q)) (centralPair A B) = blockMatrix ![A, B] by
    ext ⟨a, i⟩ ⟨b, j⟩; fin_cases a <;> fin_cases b <;> simp [pullMatrix, centralPair, blockMatrix, diagTwo]] at hh
  exact ⟨blockMatrix_kUni_component _ hh 0, blockMatrix_kUni_component _ hh 1⟩

theorem shuffle_block_label {q : ℕ} (i : Fin (q * 2)) :
    (scalarShuffle q 2 i).val / q = (finProdFinEquiv.symm i).2.val := by
  let p := finProdFinEquiv.symm i
  have hcast {m n : ℕ} (h : m = n) (a : Fin m) : (cast (congrArg Fin h) a).val = a.val := by cases h; rfl
  change (cast (congrArg Fin (Nat.mul_comm 2 q)) (finProdFinEquiv (p.2, p.1))).val / q = p.2.val
  rw [hcast (Nat.mul_comm 2 q)]; exact flat_block_label (p.2, p.1)

def shuffledMiddle {q : ℕ} (A B : KMat 𝕂 q) : KMat 𝕂 (q * 2) :=
  let P : KMat 𝕂 (q * 2) := kPerm (scalarShuffle q 2)
  P * flattenBlocks (centralPair A B) * Pᴴ

theorem shuffledMiddle_kSupported {q : ℕ} (A B : KMat 𝕂 q) :
    KSupported (fun i : Fin (q * 2) => i.val / q) (shuffledMiddle A B) := by
  intro i j hij
  let σ := scalarShuffle q 2
  let x := finProdFinEquiv.symm (σ.symm i)
  let y := finProdFinEquiv.symm (σ.symm j)
  have hxy : x.2 ≠ y.2 := fun h => hij <| by
    have hi := shuffle_block_label (σ.symm i); have hj := shuffle_block_label (σ.symm j)
    simp only [σ, Equiv.apply_symm_apply] at hi hj
    exact hi.trans ((congrArg Fin.val h).trans hj.symm)
  change (kPerm (𝕂 := 𝕂) σ * flattenBlocks (centralPair A B) * (kPerm (𝕂 := 𝕂) σ)ᴴ) i j = 0
  simp only [kPerm_conj, mul_kPerm_apply, kPerm_mul_apply]
  change diagTwo (A x.1 y.1) (B x.1 y.1) x.2 y.2 = 0
  rcases x with ⟨_, a⟩; rcases y with ⟨_, b⟩
  fin_cases a <;> fin_cases b <;> simp_all [diagTwo]

theorem small_block_sandwich {q : ℕ} (U V : Fin q → KMat 𝕂 2) (A B : KMat 𝕂 q)
    (i j : Fin q) (a b : Fin 2) :
    (blockMatrix U * centralPair A B * blockMatrix V) (i, a) (j, b) =
      (U i * diagTwo (A i j) (B i j) * V j) a b := by
  classical
  simp [Matrix.mul_apply, blockMatrix, centralPair, Fintype.sum_prod_type]

theorem kExtract_middle_pair {q : ℕ} (D : KMat 𝕂 (q * 2))
    (hs : KSupported (fun i : Fin (q * 2) => i.val / q) D) (hD : KUni D) :
    ∃ A B : KMat 𝕂 q, KUni A ∧ KUni B ∧
      flattenBlocks (centralPair A B) =
        (kPerm (𝕂 := 𝕂) (scalarShuffle q 2))ᴴ * D * kPerm (𝕂 := 𝕂) (scalarShuffle q 2) := by
  let σ := scalarShuffle q 2
  let P : KMat 𝕂 (q * 2) := kPerm σ
  let C := unflattenBlocks (Pᴴ * D * P)
  have hcross (i j : Fin q) (a b : Fin 2) (hab : a ≠ b) : C (i, a) (j, b) = 0 := by
    change ((kPerm (𝕂 := 𝕂) σ)ᴴ * D * kPerm (𝕂 := 𝕂) σ) (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b)) = 0
    simp only [kPerm_conj, mul_kPerm_apply, kPerm_mul_apply, Equiv.symm_symm]
    apply hs
    have hi := shuffle_block_label (finProdFinEquiv (i, a))
    have hj := shuffle_block_label (finProdFinEquiv (j, b))
    simp only [Equiv.symm_apply_apply] at hi hj
    change (σ (finProdFinEquiv (i, a))).val / q ≠ (σ (finProdFinEquiv (j, b))).val / q
    rw [hi, hj]; exact fun h => hab (Fin.ext h)
  let A : KMat 𝕂 q := fun i j => C (i, 0) (j, 0)
  let B : KMat 𝕂 q := fun i j => C (i, 1) (j, 1)
  have he : C = centralPair A B := by
    ext ⟨i, a⟩ ⟨j, b⟩; fin_cases a <;> fin_cases b <;> simp [centralPair, diagTwo, A, B, hcross]
  have hP := kPerm_unitary (𝕂 := 𝕂) σ
  have hC : KUni C := pullMatrix_kUni _ (kUnitary_mul (kUnitary_mul (kUnitary_conj hP) hD) hP)
  rw [he] at hC
  obtain ⟨hA, hB⟩ := centralPair_kUni_components A B hC
  exact ⟨A, B, hA, hB, by rw [← he, flatten_unflatten]⟩

theorem kBlock_sandwich_iff {q : ℕ} (M : KMat 𝕂 (q * 2)) :
    (let P : KMat 𝕂 (q * 2) := kPerm (scalarShuffle q 2)
     ∃ B₁ B₂ B₃ : KMat 𝕂 (q * 2),
       KSupported (fun i => i.val / 2) B₁ ∧ KSupported (fun i => i.val / q) B₂ ∧ KSupported (fun i => i.val / 2) B₃ ∧
       KUni B₁ ∧ KUni B₂ ∧ KUni B₃ ∧ M = B₃ * Pᴴ * B₂ * P * B₁) ↔
    ∃ (U V : Fin q → KMat 𝕂 2) (A B : KMat 𝕂 q),
      (∀ i, KUni (U i)) ∧ (∀ j, KUni (V j)) ∧ KUni A ∧ KUni B ∧
      M = flattenBlocks (blockMatrix U * centralPair A B * blockMatrix V) := by
  constructor
  · rintro ⟨B₁, B₂, B₃, hs₁, hs₂, hs₃, ho₁, ho₂, ho₃, hM⟩
    obtain ⟨A, B, hA, hB, hAB⟩ := kExtract_middle_pair B₂ hs₂ ho₂
    refine ⟨flatBlocks B₃, flatBlocks B₁, A, B, flatBlocks_kUni B₃ hs₃ ho₃, flatBlocks_kUni B₁ hs₁ ho₁, hA, hB, ?_⟩
    rw [flattenBlocks_mul, flattenBlocks_mul, flatten_extracted_blocks B₃ hs₃, flatten_extracted_blocks B₁ hs₁, hAB, hM]
    simp only [Matrix.mul_assoc]
  · rintro ⟨U, V, A, B, hU, hV, hA, hB, rfl⟩
    let P : KMat 𝕂 (q * 2) := kPerm (scalarShuffle q 2)
    let C := flattenBlocks (centralPair A B)
    have hP := kPerm_unitary (𝕂 := 𝕂) (scalarShuffle q 2)
    have hC := pullMatrix_kUni finProdFinEquiv.symm (centralPair_kUni A B hA hB)
    refine ⟨flattenBlocks (blockMatrix V), shuffledMiddle A B, flattenBlocks (blockMatrix U),
      flatten_kSupported V, shuffledMiddle_kSupported A B, flatten_kSupported U,
      pullMatrix_kUni finProdFinEquiv.symm (blockMatrix_kUni V hV),
      kUnitary_mul (kUnitary_mul hP hC) (kUnitary_conj hP),
      pullMatrix_kUni finProdFinEquiv.symm (blockMatrix_kUni U hU), ?_⟩
    rw [flattenBlocks_mul, flattenBlocks_mul]
    calc flattenBlocks (blockMatrix U) * C * flattenBlocks (blockMatrix V)
      _ = flattenBlocks (blockMatrix U) * (Pᴴ * P) * C * (Pᴴ * P) * flattenBlocks (blockMatrix V) := by
        rw [hP.1, Matrix.mul_one, Matrix.mul_one]
      _ = flattenBlocks (blockMatrix U) * Pᴴ * shuffledMiddle A B * P * flattenBlocks (blockMatrix V) := by
        simp only [shuffledMiddle, P, C, Matrix.mul_assoc]

end Generic

def localFamily (q : ℕ) : Set (CMat (q * 2)) :=
  let P := cPermMatrix (scalarShuffle q 2)
  {M | CInA3Unitary 2 q 2 P Pᴴ M}

theorem mem_localFamily_iff_block_sandwich {q : ℕ} (M : CMat (q * 2)) :
    M ∈ localFamily q ↔
      ∃ (U V : Fin q → CMat 2) (A B : CMat q),
        (∀ i, GS.Unitary (U i)) ∧ (∀ j, GS.Unitary (V j)) ∧
        GS.Unitary A ∧ GS.Unitary B ∧
        M = flattenBlocks (blockMatrix U * centralPair A B * blockMatrix V) :=
  kBlock_sandwich_iff (𝕂 := ℂ) M

theorem block_sandwich_mem_localFamily {q : ℕ} (U V : Fin q → CMat 2)
    (A B : CMat q) (hU : ∀ i, GS.Unitary (U i)) (hV : ∀ j, GS.Unitary (V j))
    (hA : GS.Unitary A) (hB : GS.Unitary B) :
    flattenBlocks (blockMatrix U * centralPair A B * blockMatrix V) ∈ localFamily q :=
  (mem_localFamily_iff_block_sandwich _).mpr ⟨U, V, A, B, hU, hV, hA, hB, rfl⟩

end GS.UnitaryNonmanifold

namespace GS.NonmanifoldCompletion
export GS.UnitaryNonmanifold (diagTwo blockMatrix flattenBlocks flattenBlocks_apply centralPair small_block_sandwich)

theorem mem_localFamily_iff_block_sandwich {q : ℕ} (M : Mat (q * 2)) :
    M ∈ GS.localFamily q ↔
      ∃ (U V : Fin q → Mat 2) (A B : Mat q),
        (∀ i, Orthogonal (U i)) ∧ (∀ j, Orthogonal (V j)) ∧
        Orthogonal A ∧ Orthogonal B ∧
        M = flattenBlocks (blockMatrix U * centralPair A B * blockMatrix V) := by
  have hk := GS.UnitaryNonmanifold.kBlock_sandwich_iff (𝕂 := ℝ) M
  have hu {n : ℕ} (X : Mat n) : KUni X ↔ Orthogonal X := by simp [KUni, Orthogonal]
  simpa only [GS.localFamily, Set.mem_ofPred_eq, InA3Orth, GS.product3, BlockDiagonal, Supported, KSupported, hu,
    show kPerm (𝕂 := ℝ) (scalarShuffle q 2) = permMatrix (scalarShuffle q 2) from rfl,
    Matrix.conjTranspose_eq_transpose_of_trivial] using hk

theorem block_sandwich_mem_localFamily {q : ℕ} (U V : Fin q → Mat 2)
    (A B : Mat q) (hU : ∀ i, Orthogonal (U i)) (hV : ∀ j, Orthogonal (V j))
    (hA : Orthogonal A) (hB : Orthogonal B) :
    flattenBlocks (blockMatrix U * centralPair A B * blockMatrix V) ∈ GS.localFamily q :=
  (mem_localFamily_iff_block_sandwich _).mpr ⟨U, V, A, B, hU, hV, hA, hB, rfl⟩

end GS.NonmanifoldCompletion
