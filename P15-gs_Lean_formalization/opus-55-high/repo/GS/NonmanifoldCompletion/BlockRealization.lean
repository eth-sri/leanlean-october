module

public import GS.NonmanifoldCompletion.SpectralTwo
public import GS.Shared.Factorization

@[expose] public section


/-!
# The original scalar perfect-shuffle family and its small-block coordinates

All equivalences concern the exact GS.localFamily and GS.scalarShuffle already
present in the project.  This file does not redefine the family by its desired
block formula.  Coordinate relabellings and the block factors are constructed.

-/
noncomputable section
open Matrix GS GS.Shared GS.UnitaryCS
namespace GS.NonmanifoldCompletion

section Relabel
variable {R α β : Type*} [Semiring R] [Star R] [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

section
variable (e : β ≃ α) (A : Matrix α α R)
/-- Pull back both matrix indices along an equivalence. -/
def pullMatrix : Matrix β β R :=
  fun i j => A (e i) (e j)

@[simp] theorem pullMatrix_transpose :
    pullMatrix e Aᵀ = (pullMatrix e A)ᵀ := rfl

@[simp] theorem pullMatrix_conjTranspose :
    pullMatrix e Aᴴ = (pullMatrix e A)ᴴ := rfl

end

section
variable (e : β ≃ α)
@[simp] theorem pullMatrix_one :
    pullMatrix e (1 : Matrix α α R) = 1 :=
  submatrix_one_equiv e

theorem pullMatrix_mul (A B : Matrix α α R) :
    pullMatrix e (A*B) = pullMatrix e A * pullMatrix e B :=
  (submatrix_mul_equiv A B e e e).symm

@[simp] theorem pullMatrix_symm (A : Matrix α α R) :
    pullMatrix e.symm (pullMatrix e A) = A := by
  ext i j
  simp [pullMatrix]

end

end Relabel


section Blocks
variable {R : Type*} [Semiring R] [Star R] {k b : ℕ}

section
variable (A : Matrix (Fin k × Fin b) (Fin k × Fin b) R)
/-- Flatten the pair-indexed matrix using the SAME equivalence as originalF. -/
def flattenBlocks : Matrix (Fin (k*b)) (Fin (k*b)) R :=
  pullMatrix finProdFinEquiv.symm A

@[simp] theorem flattenBlocks_apply (i j : Fin k × Fin b) :
    flattenBlocks A (finProdFinEquiv i) (finProdFinEquiv j) = A i j := by
  simp [flattenBlocks,pullMatrix]

end

theorem flattenBlocks_mul (A B : Matrix (Fin k × Fin b) (Fin k × Fin b) R) :
    flattenBlocks (A*B) = flattenBlocks A * flattenBlocks B :=
  pullMatrix_mul _ A B

section
variable (A : Matrix (Fin (k*b)) (Fin (k*b)) R)
def unflattenBlocks :
    Matrix (Fin k × Fin b) (Fin k × Fin b) R := pullMatrix finProdFinEquiv A

@[simp] theorem flatten_unflatten :
    flattenBlocks (unflattenBlocks A) = A :=
  pullMatrix_symm finProdFinEquiv A

/-- Extract the consecutive diagonal blocks without any choice. -/
def flatBlocks (i : Fin k) : Matrix (Fin b) (Fin b) R :=
  fun a c => A (finProdFinEquiv (i,a)) (finProdFinEquiv (i,c))

end

/-- Blocks are indexed by the quotient in the original BlockDiagonal predicate. -/
theorem flat_block_label (p : Fin k × Fin b) :
    (finProdFinEquiv p).val / b = p.1.val := by
  simp [Nat.add_mul_div_left _ _ p.2.pos, Nat.div_eq_of_lt]

section
variable (A : Matrix (Fin (k*b)) (Fin (k*b)) R)
theorem unflatten_supported (hA : ∀ i j : Fin (k*b), i.val / b ≠ j.val / b → A i j = 0) :
    unflattenBlocks A = blockMatrix (flatBlocks A) := by
  ext ⟨i,a⟩ ⟨j,c⟩
  by_cases hij : i=j
  · subst j
    simp [unflattenBlocks,pullMatrix,blockMatrix,flatBlocks]
  · exact (hA _ _ (by simp only [flat_block_label]; grind)).trans (if_neg hij).symm

theorem flatten_extracted_blocks (hA : ∀ i j : Fin (k*b), i.val / b ≠ j.val / b → A i j = 0) : flattenBlocks (blockMatrix (flatBlocks A)) = A := by
  rw [← unflatten_supported A hA,flatten_unflatten]


end

@[simp] theorem blockMatrix_conjTranspose {R : Type*} [Ring R] [StarRing R] (B : Fin k → Matrix (Fin b) (Fin b) R) :
    (blockMatrix B)ᴴ = blockMatrix (fun i => (B i)ᴴ) := by
  ext ⟨i,a⟩ ⟨j,c⟩
  by_cases h : i=j <;> simp [blockMatrix, h, eq_comm]

@[simp] theorem blockMatrix_mul (B C : Fin k → Matrix (Fin b) (Fin b) R) :
    blockMatrix B * blockMatrix C = blockMatrix (fun i => B i * C i) := by
  ext ⟨i,a⟩ ⟨j,c⟩
  by_cases h : i=j <;> simp [Matrix.mul_apply,blockMatrix,Fintype.sum_prod_type,h]

@[simp] theorem blockMatrix_one (k b : ℕ) :
    blockMatrix (fun _ : Fin k => (1 : Matrix (Fin b) (Fin b) R)) = 1 := by
  ext ⟨i,a⟩ ⟨j,c⟩
  by_cases hi : i=j <;> by_cases ha : a=c <;>
    simp [blockMatrix, Matrix.one_apply, hi, ha]

end Blocks

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

theorem pullMatrix_unitary {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : β ≃ α) {A : Matrix α α 𝕜} (hA : IsUnitary A) : IsUnitary (pullMatrix e A) := by
  constructor <;> simp [← pullMatrix_conjTranspose, ← pullMatrix_mul, hA.1, hA.2]

section
variable {k b : ℕ} (B : Fin k → Matrix (Fin b) (Fin b) 𝕜)
theorem flatten_blockDiagonal :
    Supp (fun i : Fin (k*b) => i.val / b) (flattenBlocks (blockMatrix B)) := by
  intro i j hij
  have := flat_block_label (finProdFinEquiv.symm i)
  have := flat_block_label (finProdFinEquiv.symm j)
  exact if_neg (by grind)

theorem blockMatrix_unitary (hB : ∀ i, IsUnitary (B i)) : IsUnitary (blockMatrix B) := by
  constructor <;> simp [fun i => (hB i).1, fun i => (hB i).2]

theorem blockMatrix_unitary_component (hB : IsUnitary (blockMatrix B)) (i : Fin k) : IsUnitary (B i) := by
  constructor <;> ext a c
  · simpa [blockMatrix, one_apply] using congr_fun₂ hB.1 (i,a) (i,c)
  · simpa [blockMatrix, one_apply] using congr_fun₂ hB.2 (i,a) (i,c)

end

section
variable (A B : 𝕄)
/-- The central conjugate, displayed in n-by-n blocks of size two. -/
def centralPair : Matrix (Fin n × Fin 2) (Fin n × Fin 2) 𝕜 :=
  fun i j => diagTwo (A i.1 j.1) (B i.1 j.1) i.2 j.2

theorem centralPair_as_blocks :
    centralPair A B = pullMatrix (Equiv.prodComm _ _) (blockMatrix ![A,B]) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  fin_cases a <;> fin_cases b <;> simp [centralPair,pullMatrix,blockMatrix,diagTwo]

end

theorem centralPair_unitary {A B : 𝕄} : IsUnitary (centralPair A B) ↔ IsUnitary A ∧ IsUnitary B := by
  rw [centralPair_as_blocks]
  refine ⟨fun h => ?_, fun h => pullMatrix_unitary _ (blockMatrix_unitary _ (by simp_all))⟩
  have hh := pullMatrix_unitary (Equiv.prodComm (Fin n) (Fin 2)).symm h
  exact ⟨blockMatrix_unitary_component _ hh 0, blockMatrix_unitary_component _ hh 1⟩

/-- The shuffle makes the inner pair coordinate the consecutive block label. -/
theorem shuffle_block_label {q b : ℕ} (i : Fin (q*b)) :
    (scalarShuffle q b i).val / q = (finProdFinEquiv.symm i).2.val := by
  rw [← flat_block_label ((finProdFinEquiv.symm i).2, (finProdFinEquiv.symm i).1)]
  exact congrArg (·/q) ((Fin.heq_ext_iff (by ring)).1 (cast_heq _ _))

theorem small_block_sandwich (U V : Fin n → Matrix (Fin 2) (Fin 2) 𝕜) (A B : 𝕄)
    (i j : Fin n) (a b : Fin 2) :
    (blockMatrix U * centralPair A B * blockMatrix V) (i,a) (j,b) =
      (U i * diagTwo (A i j) (B i j) * V j) a b := by
  classical
  simp [Matrix.mul_apply, blockMatrix, centralPair, Fintype.sum_prod_type]

variable (𝕜) in
/-- The scalar-shuffle three-factor family over `𝕜`. -/
def sFamily (n : ℕ) : Set (Matrix (Fin (n*2)) (Fin (n*2)) 𝕜) :=
  {M | ∃ B₁ B₂ B₃, Supp (fun i : Fin (n*2) => i.val / 2) B₁ ∧ Supp (fun i : Fin (n*2) => i.val / n) B₂ ∧
    Supp (fun i : Fin (n*2) => i.val / 2) B₃ ∧ IsUnitary B₁ ∧ IsUnitary B₂ ∧ IsUnitary B₃ ∧
    M = B₃ * (perm (scalarShuffle n 2))ᴴ * B₂ * perm (scalarShuffle n 2) * B₁}

/-- Exact block description of the original scalar-shuffle family. -/
theorem mem_localFamily_iff_block_sandwich (M : Matrix (Fin (n*2)) (Fin (n*2)) 𝕜) :
    M ∈ sFamily 𝕜 n ↔
      ∃ (U V : Fin n → Matrix (Fin 2) (Fin 2) 𝕜) (A B : 𝕄),
        (∀ i, IsUnitary (U i)) ∧ (∀ j, IsUnitary (V j)) ∧ IsUnitary A ∧ IsUnitary B ∧
        M = flattenBlocks (blockMatrix U * centralPair A B * blockMatrix V) := by
  have hP := perm_uni (𝕜 := 𝕜) (scalarShuffle n 2)
  constructor
  · rintro ⟨B₁,D,B₃,hs₁,hs,hs₃,ho₁,hD,ho₃,rfl⟩
    let σ := scalarShuffle n 2
    let C := unflattenBlocks ((perm σ)ᴴ * D * perm σ)
    have hcross (i j : Fin n) (a b : Fin 2) (hab : a≠b) : C (i,a) (j,b)=0 := by
      have := shuffle_block_label (finProdFinEquiv (i,a))
      have := shuffle_block_label (finProdFinEquiv (j,b))
      simpa [C, σ, unflattenBlocks, pullMatrix] using hs _ _ (by grind)
    let A : 𝕄 := fun i j => C (i,0) (j,0)
    let B : 𝕄 := fun i j => C (i,1) (j,1)
    have he : C = centralPair A B := by
      ext ⟨i,a⟩ ⟨j,b⟩
      fin_cases a <;> fin_cases b <;> simp [centralPair,diagTwo,A,B,hcross]
    have hC : IsUnitary C := pullMatrix_unitary _ ((hP.conjTranspose.mul hD).mul hP)
    rw [he, centralPair_unitary] at hC
    have hb {k : ℕ} {b : ℕ} (A : Matrix (Fin (k*b)) (Fin (k*b)) 𝕜) (hs : Supp (fun i : Fin (k*b) => i.val / b) A)
        (hA : IsUnitary A) (i : Fin k) : IsUnitary (flatBlocks A i) :=
      blockMatrix_unitary_component _ (unflatten_supported A hs ▸ pullMatrix_unitary finProdFinEquiv hA) i
    refine ⟨flatBlocks B₃,flatBlocks B₁,A,B,by grind, by grind,hC.1,hC.2,?_⟩
    rw [flattenBlocks_mul,flattenBlocks_mul,flatten_extracted_blocks B₃ hs₃,
      flatten_extracted_blocks B₁ hs₁, ← he, flatten_unflatten]
    grind
  · rintro ⟨U,V,A,B,hU,hV,hA,hB,rfl⟩
    let P : Matrix (Fin (n*2)) (Fin (n*2)) 𝕜 := perm (scalarShuffle n 2)
    let C := flattenBlocks (centralPair A B)
    refine ⟨flattenBlocks (blockMatrix V), P * C * Pᴴ,
      flattenBlocks (blockMatrix U), flatten_blockDiagonal V, fun i j hij => ?_, flatten_blockDiagonal U,
      pullMatrix_unitary _ (blockMatrix_unitary V hV),
      (hP.mul (pullMatrix_unitary _ (centralPair_unitary.2 (by grind)))).mul hP.conjTranspose,
      pullMatrix_unitary _ (blockMatrix_unitary U hU), ?_⟩
    · have := shuffle_block_label ((scalarShuffle n 2).symm i)
      have := shuffle_block_label ((scalarShuffle n 2).symm j)
      simp_all [P, C, flattenBlocks, pullMatrix, centralPair, diagTwo, Fin.ext_iff]
    rw [flattenBlocks_mul,flattenBlocks_mul]
    grind [hP.1]

variable (𝕜) in
/-- Parameters are ordered as left blocks, two middle blocks, and right blocks. -/
abbrev SmallBlockParameters (n : ℕ) :=
  (Fin n → Matrix (Fin 2) (Fin 2) 𝕜) × 𝕄 × 𝕄 × (Fin n → Matrix (Fin 2) (Fin 2) 𝕜)

variable (𝕜) in
def smallFactorSet (n : ℕ) : Set (SmallBlockParameters 𝕜 n) :=
  {p | (∀ i, IsUnitary (p.1 i)) ∧ IsUnitary p.2.1 ∧ IsUnitary p.2.2.1 ∧ ∀ j, IsUnitary (p.2.2.2 j)}

section
variable (p : SmallBlockParameters 𝕜 n)
def smallFactorMap : Matrix (Fin (n*2)) (Fin (n*2)) 𝕜 :=
  flattenBlocks (blockMatrix p.1 * centralPair p.2.1 p.2.2.1 * blockMatrix p.2.2.2)

theorem smallFactorMap_block (i j : Fin n) (a b : Fin 2) :
    smallFactorMap p (finProdFinEquiv (i,a)) (finProdFinEquiv (j,b)) =
      (p.1 i * diagTwo (p.2.1 i j) (p.2.2.1 i j) * p.2.2.2 j) a b := by
  rw [smallFactorMap,flattenBlocks_apply,small_block_sandwich]

end

section
variable (n : ℕ)
theorem continuous_smallFactorMap : Continuous (@smallFactorMap 𝕜 _ n) := by
  unfold smallFactorMap flattenBlocks pullMatrix blockMatrix centralPair diagTwo
  fun_prop

theorem isCompact_smallFactorSet : IsCompact (smallFactorSet 𝕜 n) := by
  have hO (n : ℕ) : IsCompact {A : 𝕄 | IsUnitary A} :=
    (isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => isCompact_closedBall (0 : 𝕜) 1).of_isClosed_subset
      ((isClosed_eq (by fun_prop) (by fun_prop)).inter (isClosed_eq (by fun_prop) (by fun_prop)))
      fun A hA i j => by simpa using entry_norm_bound_of_unitary (mem_unitaryGroup_iff.2 hA.2) i j
  have houter := isCompact_pi_infinite fun _ : Fin n => hO 2
  exact houter.prod ((hO n).prod ((hO n).prod houter))

/-- Every factorization in the scalar family is retained in the compact parameter space. -/
theorem image_smallFactorMap : (@smallFactorMap 𝕜 _ n) '' smallFactorSet 𝕜 n = sFamily 𝕜 n := by
  ext M
  rw [mem_localFamily_iff_block_sandwich]
  aesop (add simp [smallFactorSet, smallFactorMap])

end

end GS.NonmanifoldCompletion
