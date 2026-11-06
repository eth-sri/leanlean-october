module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.Complex.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.FunProp

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Matrix
open scoped BigOperators

namespace GS

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def Orthogonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : Prop := Aᵀ * A = 1 ∧ A * Aᵀ = 1

namespace Orthogonal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A B : Matrix ι ι ℝ}

@[simp] theorem one : Orthogonal (1 : Matrix ι ι ℝ) := ⟨by simp, by simp⟩

theorem transpose (hA : Orthogonal A) : Orthogonal Aᵀ :=
  ⟨by simpa using hA.2, by simpa using hA.1⟩

theorem mul (hA : Orthogonal A) (hB : Orthogonal B) : Orthogonal (A * B) :=
  ⟨by calc (A * B)ᵀ * (A * B) = Bᵀ * (Aᵀ * A) * B := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = 1 := by rw [hA.1]; simpa using hB.1,
   by calc (A * B) * (A * B)ᵀ = A * (B * Bᵀ) * Aᵀ := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = 1 := by rw [hB.2]; simpa using hA.2⟩

theorem of_transpose_mul (hA : Aᵀ * A = 1) : Orthogonal A := ⟨hA, mul_eq_one_comm.mp hA⟩

theorem of_mul_transpose (hA : A * Aᵀ = 1) : Orthogonal A := ⟨mul_eq_one_comm.mp hA, hA⟩

end Orthogonal

def Supported {ι : Type*} (block : ι → ℕ) (A : Matrix ι ι ℝ) : Prop :=
  ∀ i j, block i ≠ block j → A i j = 0

def BlockDiagonal {n : ℕ} (b : ℕ) (A : Mat n) : Prop :=
  Supported (fun i : Fin n => i.val / b) A

structure BlockSpec (n : ℕ) where
  size : ℕ
  count : ℕ
  size_pos : 0 < size
  dimension : count * size = n

namespace Supported
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {block : ι → ℕ} {A B : Matrix ι ι ℝ}

@[simp] theorem zero : Supported block (0 : Matrix ι ι ℝ) := fun _ _ _ => rfl

@[simp] theorem one : Supported block (1 : Matrix ι ι ℝ) := fun i j hij => by
  have hne : i ≠ j := fun h => hij (congrArg block h)
  simp [Matrix.one_apply, hne]

theorem transpose (hA : Supported block A) : Supported block Aᵀ :=
  fun i j hij => hA j i (Ne.symm hij)

theorem add (hA : Supported block A) (hB : Supported block B) :
    Supported block (A + B) := fun i j hij => by
  change A i j + B i j = 0; rw [hA i j hij, hB i j hij, add_zero]

theorem smul (a : ℝ) (hA : Supported block A) : Supported block (a • A) := fun i j hij => by
  change a * A i j = 0; rw [hA i j hij, mul_zero]

theorem mul (hA : Supported block A) (hB : Supported block B) :
    Supported block (A * B) := fun i j hij => by
  change (∑ t, A i t * B t j) = 0
  refine Finset.sum_eq_zero fun t _ => ?_
  by_cases hit : block i = block t
  · rw [hB t j (fun h => hij (hit.trans h)), mul_zero]
  · rw [hA i t hit, zero_mul]

end Supported

def permMatrix {ι : Type*} [DecidableEq ι] (σ : Equiv.Perm ι) : Matrix ι ι ℝ :=
  fun i j => if i = σ j then 1 else 0

section Permutations
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[simp] theorem mul_perm_apply (A : Matrix ι ι ℝ) (σ : Equiv.Perm ι) (i j : ι) :
    (A * permMatrix σ) i j = A i (σ j) := by
  classical simp [Matrix.mul_apply, permMatrix]

@[simp] theorem perm_mul_apply (σ : Equiv.Perm ι) (A : Matrix ι ι ℝ) (i j : ι) :
    (permMatrix σ * A) i j = A (σ.symm i) j := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ.symm i)]
  · simp [permMatrix]
  · intro k _ hki
    have hik : i ≠ σ k := fun h => hki (by simpa using (congrArg σ.symm h).symm)
    simp [permMatrix, hik]
  · simp

@[simp] theorem perm_transpose (σ : Equiv.Perm ι) :
    (permMatrix σ)ᵀ = permMatrix σ.symm := by
  ext i j; simp [permMatrix, Matrix.transpose_apply, σ.eq_symm_apply, eq_comm]

theorem perm_orthogonal (σ : Equiv.Perm ι) : Orthogonal (permMatrix σ) := by
  constructor <;> ext i j <;> simp [perm_transpose, perm_mul_apply, permMatrix, Matrix.one_apply]

theorem supported_perm_conjugate_iff (block : ι → ℕ) (σ : Equiv.Perm ι)
    (A : Matrix ι ι ℝ) :
    Supported (block ∘ σ.symm) (permMatrix σ * A * (permMatrix σ)ᵀ) ↔
      Supported block A :=
  ⟨fun h i j hij => by simpa using h (σ i) (σ j) (by simpa using hij),
   fun h i j hij => by simpa using h (σ.symm i) (σ.symm j) hij⟩

end Permutations

def product2 {n} (B₂ P B₁ : Mat n) : Mat n := B₂ * P * B₁

def product3 {n} (B₃ P₂ B₂ P₁ B₁ : Mat n) : Mat n := B₃ * P₂ * B₂ * P₁ * B₁

def product4 {n} (B₄ P₃ B₃ P₂ B₂ P₁ B₁ : Mat n) : Mat n :=
  B₄ * P₃ * B₃ * P₂ * B₂ * P₁ * B₁

def InA2 {n} (b₁ b₂ : ℕ) (P A : Mat n) : Prop :=
  ∃ B₁ B₂, BlockDiagonal b₁ B₁ ∧ BlockDiagonal b₂ B₂ ∧ A = product2 B₂ P B₁

def InA2Orth {n} (b₁ b₂ : ℕ) (P A : Mat n) : Prop :=
  ∃ B₁ B₂, BlockDiagonal b₁ B₁ ∧ BlockDiagonal b₂ B₂ ∧
    Orthogonal B₁ ∧ Orthogonal B₂ ∧ A = product2 B₂ P B₁

def InA3 {n} (b₁ b₂ b₃ : ℕ) (P₁ P₂ A : Mat n) : Prop :=
  ∃ B₁ B₂ B₃, BlockDiagonal b₁ B₁ ∧ BlockDiagonal b₂ B₂ ∧ BlockDiagonal b₃ B₃ ∧
    A = product3 B₃ P₂ B₂ P₁ B₁

def InA3Orth {n} (b₁ b₂ b₃ : ℕ) (P₁ P₂ A : Mat n) : Prop :=
  ∃ B₁ B₂ B₃, BlockDiagonal b₁ B₁ ∧ BlockDiagonal b₂ B₂ ∧ BlockDiagonal b₃ B₃ ∧
    Orthogonal B₁ ∧ Orthogonal B₂ ∧ Orthogonal B₃ ∧ A = product3 B₃ P₂ B₂ P₁ B₁

def InA4 {n} (b₁ b₂ b₃ b₄ : ℕ) (P₁ P₂ P₃ A : Mat n) : Prop :=
  ∃ B₁ B₂ B₃ B₄, BlockDiagonal b₁ B₁ ∧ BlockDiagonal b₂ B₂ ∧
    BlockDiagonal b₃ B₃ ∧ BlockDiagonal b₄ B₄ ∧ A = product4 B₄ P₃ B₃ P₂ B₂ P₁ B₁

def InA4Orth {n} (b₁ b₂ b₃ b₄ : ℕ) (P₁ P₂ P₃ A : Mat n) : Prop :=
  ∃ B₁ B₂ B₃ B₄, BlockDiagonal b₁ B₁ ∧ BlockDiagonal b₂ B₂ ∧
    BlockDiagonal b₃ B₃ ∧ BlockDiagonal b₄ B₄ ∧
    Orthogonal B₁ ∧ Orthogonal B₂ ∧ Orthogonal B₃ ∧ Orthogonal B₄ ∧
    A = product4 B₄ P₃ B₃ P₂ B₂ P₁ B₁

section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def frobInner (A B : Matrix ι κ ℝ) : ℝ := ∑ i, ∑ j, A i j * B i j

def frobSq (A : Matrix ι κ ℝ) : ℝ := frobInner A A

theorem frobInner_comm (A B : Matrix ι κ ℝ) : frobInner A B = frobInner B A :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem frobInner_add_left (A B C : Matrix ι κ ℝ) :
    frobInner (A + B) C = frobInner A C + frobInner B C := by
  simp [frobInner, add_mul, Finset.sum_add_distrib]

theorem frobInner_add_right (A B C : Matrix ι κ ℝ) :
    frobInner A (B + C) = frobInner A B + frobInner A C := by
  simp [frobInner, mul_add, Finset.sum_add_distrib]

theorem frobInner_sub_left (A B C : Matrix ι κ ℝ) :
    frobInner (A - B) C = frobInner A C - frobInner B C := by
  simp [frobInner, sub_mul, Finset.sum_sub_distrib]

theorem frobInner_sub_right (A B C : Matrix ι κ ℝ) :
    frobInner A (B - C) = frobInner A B - frobInner A C := by
  simp [frobInner, mul_sub, Finset.sum_sub_distrib]

theorem frobInner_neg_left (A B : Matrix ι κ ℝ) :
    frobInner (-A) B = -frobInner A B := by
  simp [frobInner, Finset.sum_neg_distrib]

theorem frobInner_smul_left (a : ℝ) (A B : Matrix ι κ ℝ) :
    frobInner (a • A) B = a * frobInner A B := by
  simp [frobInner, mul_assoc, Finset.mul_sum]

theorem frobSq_nonneg (A : Matrix ι κ ℝ) : 0 ≤ frobSq A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_self_nonneg _

theorem frobSq_eq_zero_iff (A : Matrix ι κ ℝ) : frobSq A = 0 ↔ A = 0 := by
  refine ⟨fun h => ?_, fun h => by subst h; simp [frobSq, frobInner]⟩
  have hrows (i) : (∑ j, A i j * A i j) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_self_nonneg _).mp h i (Finset.mem_univ i)
  ext i j
  exact mul_self_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg fun j _ => mul_self_nonneg (A i j)).mp (hrows i) j (Finset.mem_univ j))

theorem frobSq_add (A B : Matrix ι κ ℝ) :
    frobSq (A + B) = frobSq A + 2 * frobInner A B + frobSq B := by
  unfold frobSq
  rw [frobInner_add_left, frobInner_add_right, frobInner_add_right, frobInner_comm B A]; ring

theorem frobSq_sub (A B : Matrix ι κ ℝ) :
    frobSq (A - B) = frobSq A - 2 * frobInner A B + frobSq B := by
  unfold frobSq
  rw [frobInner_sub_left, frobInner_sub_right, frobInner_sub_right, frobInner_comm B A]; ring

theorem frobInner_transpose (A B : Matrix ι κ ℝ) :
    frobInner Aᵀ Bᵀ = frobInner A B := by
  unfold frobInner; simp only [Matrix.transpose_apply]; exact Finset.sum_comm

theorem frobInner_eq_zero_of_disjoint (A B : Matrix ι κ ℝ)
    (h : ∀ i j, A i j = 0 ∨ B i j = 0) : frobInner A B = 0 :=
  Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ =>
    (h i j).elim (fun hA => by rw [hA, zero_mul]) (fun hB => by rw [hB, mul_zero])

theorem frobInner_mul_left {ν : Type*} [Fintype ν]
    (A : Matrix ι κ ℝ) (B : Matrix κ ν ℝ) (C : Matrix ι ν ℝ) :
    frobInner (A * B) C = frobInner B (Aᵀ * C) := by
  classical
  simp only [frobInner, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  calc (∑ i, ∑ j, ∑ k, (A i k * B k j) * C i j) =
        ∑ i, ∑ k, ∑ j, B k j * (A i k * C i j) :=
      Finset.sum_congr rfl fun _ _ => by rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ = ∑ k, ∑ j, ∑ i, B k j * (A i k * C i j) := by
      rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem frobInner_left_orthogonal [DecidableEq ι]
    (U : Matrix ι ι ℝ) (hU : Orthogonal U) (A B : Matrix ι κ ℝ) :
    frobInner (U * A) (U * B) = frobInner A B := by
  rw [frobInner_mul_left, ← Matrix.mul_assoc, hU.1]; simp

theorem frobInner_right_orthogonal [DecidableEq κ]
    (V : Matrix κ κ ℝ) (hV : Orthogonal V) (A B : Matrix ι κ ℝ) :
    frobInner (A * V) (B * V) = frobInner A B := by
  calc frobInner (A * V) (B * V) = frobInner (Vᵀ * Aᵀ) (Vᵀ * Bᵀ) := by
        simpa [Matrix.transpose_mul] using (frobInner_transpose (A * V) (B * V)).symm
    _ = frobInner A B := (frobInner_left_orthogonal _ hV.transpose _ _).trans (frobInner_transpose _ _)

def IsSkew (A : Matrix ι ι ℝ) : Prop := Aᵀ = -A

theorem isSkew_diagonal_zero {A : Matrix ι ι ℝ} (hA : IsSkew A) (i : ι) :
    A i i = 0 := by
  have he : A i i = -A i i := congrFun (congrFun hA i) i
  linarith
end

def blockMatrix {R : Type*} [Zero R] {k b : ℕ} (B : Fin k → Matrix (Fin b) (Fin b) R) :
    Matrix (Fin k × Fin b) (Fin k × Fin b) R :=
  fun i j => if i.1 = j.1 then B i.1 i.2 j.2 else 0

variable {n : ℕ}

def tangentParam (B₂ P B₁ C Ω : Mat n) : Mat n :=
  B₂ * C * P * B₁ + B₂ * P * Ω * B₁

theorem conjugate_skew (B C : Mat n) (hC : IsSkew C) : IsSkew (B * C * Bᵀ) := by
  unfold IsSkew at *
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hC, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

theorem tangentParam_factored (B₂ P B₁ C Ω : Mat n) (hP : Orthogonal P) :
    tangentParam B₂ P B₁ C Ω = B₂ * (C + P * Ω * Pᵀ) * (P * B₁) := by
  symm
  calc B₂ * (C + P * Ω * Pᵀ) * (P * B₁) = B₂ * C * P * B₁ + B₂ * P * Ω * (Pᵀ * P) * B₁ := by noncomm_ring
    _ = tangentParam B₂ P B₁ C Ω := by rw [hP.1]; simp [tangentParam]

theorem tangentParam_frobSq (B₂ P B₁ C Ω : Mat n)
    (h₂ : Orthogonal B₂) (hP : Orthogonal P) (h₁ : Orthogonal B₁)
    (hcross : frobInner C (P * Ω * Pᵀ) = 0) :
    frobSq (tangentParam B₂ P B₁ C Ω) = frobSq C + frobSq Ω := by
  rw [tangentParam_factored _ _ _ _ _ hP]
  have hbase : frobSq (B₂ * (C + P * Ω * Pᵀ) * (P * B₁)) = frobSq (C + P * Ω * Pᵀ) := by
    unfold frobSq; rw [frobInner_right_orthogonal _ (hP.mul h₁), frobInner_left_orthogonal _ h₂]
  have hΩ : frobSq (P * Ω * Pᵀ) = frobSq Ω := by
    unfold frobSq; rw [frobInner_right_orthogonal _ hP.transpose, frobInner_left_orthogonal _ hP]
  rw [hbase, frobSq_add, hcross, hΩ]; ring

theorem gram_completion (C H G L W : Mat n)
    (hC : C * H * Cᵀ = G) (hL : L * Lᵀ = H) (hW : W * G * Wᵀ = 1) :
    Orthogonal (W * C * L) := by
  apply Orthogonal.of_mul_transpose
  calc (W * C * L) * (W * C * L)ᵀ = W * (C * (L * Lᵀ) * Cᵀ) * Wᵀ := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [hL, hC, hW]

abbrev CircleVector := Fin 2 → ℝ

def OnCircle (u : CircleVector) : Prop := u 0 ^ 2 + u 1 ^ 2 = 1

def outer {ι κ : Type*} (u : ι → ℝ) (z : κ → ℝ) : Matrix ι κ ℝ :=
  fun i j => u i * z j

def UnitSq {ι : Type*} [Fintype ι] (u : ι → ℝ) : Prop := ∑ i, u i ^ 2 = 1

theorem OnCircle.unitSq {u : CircleVector} (hu : OnCircle u) : UnitSq u := by
  simpa [OnCircle, UnitSq, Fin.sum_univ_two] using hu

section GenOuter
variable {ι κ : Type*} [Fintype ι]

theorem unitSq_has_nonzero {u : ι → ℝ} (hu : UnitSq u) : ∃ i, u i ≠ 0 := by
  by_contra! h
  have hz : (∑ i, u i ^ 2) = 0 := Finset.sum_eq_zero fun i _ => by simp [h i]
  linarith [hu.symm.trans hz]

theorem outer_simultaneous_neg (u : ι → ℝ) (z : κ → ℝ) :
    outer (-u) (-z) = outer u z := by ext i j; simp [outer]

theorem outer_zero_iff {u : ι → ℝ} (hu : UnitSq u) (z : κ → ℝ) :
    outer u z = 0 ↔ z = 0 := by
  refine ⟨fun h => ?_, fun h => by subst h; ext i j; simp [outer]⟩
  obtain ⟨i, hi⟩ := unitSq_has_nonzero hu
  exact funext fun j => (mul_eq_zero.mp (congrFun (congrFun h i) j)).resolve_left hi

theorem outer_col_sq {u : ι → ℝ} (hu : UnitSq u) (z : κ → ℝ) (j : κ) :
    (∑ i, (outer u z i j) ^ 2) = z j ^ 2 := by
  calc (∑ i, (u i * z j) ^ 2) = (∑ i, u i ^ 2) * z j ^ 2 := by simp_rw [mul_pow, ← Finset.sum_mul]
    _ = z j ^ 2 := by rw [hu, one_mul]

theorem frobSq_outer_unitSq [Fintype κ] {u : ι → ℝ} (hu : UnitSq u) (z : κ → ℝ) :
    frobSq (outer u z) = ∑ j, z j ^ 2 := by
  unfold frobSq frobInner; rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => by simpa only [← pow_two] using outer_col_sq hu z j

theorem outer_unique_of_column {u v : ι → ℝ} {z w : κ → ℝ}
    (hu : UnitSq u) (h : outer u z = outer v w)
    (j : κ) (hzj : z j ≠ 0) (hj : z j = w j) : u = v ∧ z = w := by
  have huv : u = v := funext fun i => mul_right_cancel₀ hzj
    (by simpa [outer, ← hj] using congrFun (congrFun h i) j)
  obtain ⟨i, hi⟩ := unitSq_has_nonzero hu
  exact ⟨huv, funext fun k => mul_left_cancel₀ hi
    (by simpa [outer, ← huv] using congrFun (congrFun h i) k)⟩

theorem outer_fibres_nonzero_unitSq {u v : ι → ℝ} {z w : κ → ℝ}
    (hu : UnitSq u) (hv : UnitSq v) (hz : z ≠ 0) :
    outer u z = outer v w ↔ (u = v ∧ z = w) ∨ (u = -v ∧ z = -w) := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨j, hj⟩ : ∃ j, z j ≠ 0 := by by_contra! h0; exact hz (funext h0)
    have he : z j ^ 2 = w j ^ 2 := by rw [← outer_col_sq hu z j, h, outer_col_sq hv w j]
    rcases mul_eq_zero.mp (show (z j - w j) * (z j + w j) = 0 by nlinarith [he]) with hp | hp
    · exact Or.inl (outer_unique_of_column hu h j hj (sub_eq_zero.mp hp))
    · refine Or.inr (outer_unique_of_column hu ?_ j hj (by change z j = -w j; linarith))
      rwa [outer_simultaneous_neg]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact outer_simultaneous_neg v w

theorem outer_fibres_unitSq {u v : ι → ℝ} {z w : κ → ℝ}
    (hu : UnitSq u) (hv : UnitSq v) :
    outer u z = outer v w ↔
      (z = 0 ∧ w = 0) ∨ (u = v ∧ z = w) ∨ (u = -v ∧ z = -w) := by
  by_cases hz : z = 0
  · subst z; rw [(outer_zero_iff hu 0).mpr rfl]
    refine ⟨fun h => Or.inl ⟨rfl, (outer_zero_iff hv w).mp h.symm⟩, ?_⟩
    rintro (⟨_, rfl⟩ | ⟨_, hw⟩ | ⟨_, hw⟩)
    · exact ((outer_zero_iff hv 0).mpr rfl).symm
    · exact ((outer_zero_iff hv w).mpr hw.symm).symm
    · exact ((outer_zero_iff hv w).mpr (neg_eq_zero.mp hw.symm)).symm
  · rw [outer_fibres_nonzero_unitSq hu hv hz]; simp [hz]

theorem rank_outer_le_one [Fintype κ] [DecidableEq κ]
    (u : ι → ℝ) (z : κ → ℝ) : Matrix.rank (outer u z) ≤ 1 := by
  let U : Matrix ι (Fin 1) ℝ := fun i _ => u i
  let Z : Matrix (Fin 1) κ ℝ := fun _ j => z j
  have h : outer u z = U * Z := by ext i j; simp [outer, U, Z, Matrix.mul_apply]
  rw [h]; exact (Matrix.rank_mul_le_left U Z).trans (by simpa using Matrix.rank_le_card_width U)

end GenOuter

theorem frobSq_outer {κ : Type*} [Fintype κ] {u : CircleVector}
    (hu : OnCircle u) (z : κ → ℝ) :
    frobSq (outer u z) = ∑ j, z j ^ 2 := frobSq_outer_unitSq hu.unitSq z

theorem outer_fibres {κ : Type*} {u v : CircleVector} {z w : κ → ℝ}
    (hu : OnCircle u) (hv : OnCircle v) :
    outer u z = outer v w ↔
      (z = 0 ∧ w = 0) ∨ (u = v ∧ z = w) ∨ (u = -v ∧ z = -w) :=
  outer_fibres_unitSq hu.unitSq hv.unitSq

def T (u : CircleVector) : Mat 2 := !![u 0, u 1; u 1, -u 0]

theorem continuous_T : Continuous T := by
  apply continuous_pi; intro i; apply continuous_pi; intro j
  fin_cases i <;> fin_cases j <;> simp [T] <;> fun_prop

theorem T_transpose (u : CircleVector) : (T u)ᵀ = T u := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem T_sq {u : CircleVector} (hu : OnCircle u) : T u * T u = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [T, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] <;>
    dsimp [OnCircle] at hu <;> nlinarith [hu]

theorem T_orthogonal {u : CircleVector} (hu : OnCircle u) : Orthogonal (T u) := by
  constructor <;> rw [T_transpose, T_sq hu]

def middleBlock (a b : ℝ) (u : CircleVector) : Mat 2 :=
  ((a + b) / 2) • (1 : Mat 2) + ((a - b) / 2) • T u

theorem middleBlock_swap (a b : ℝ) (u : CircleVector) :
    middleBlock b a (-u) = middleBlock a b u := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [middleBlock, T] <;> ring

theorem middleBlock_equal (a : ℝ) (u : CircleVector) :
    middleBlock a a u = a • (1 : Mat 2) := by
  ext i j; simp [middleBlock] <;> ring

theorem middleBlock_trace (a b : ℝ) (u : CircleVector) :
    middleBlock a b u 0 0 + middleBlock a b u 1 1 = a + b := by
  simp [middleBlock, T]; ring

theorem middleBlock_eq_sum_and_difference
    (a b a' b' : ℝ) (u v : CircleVector)
    (h : middleBlock a b u = middleBlock a' b' v) :
    a + b = a' + b' ∧ (a - b) • T u = (a' - b') • T v := by
  have hs : a + b = a' + b' := by rw [← middleBlock_trace a b u, h, middleBlock_trace]
  refine ⟨hs, ?_⟩
  ext i j
  have he := congrFun (congrFun h i) j
  change ((a + b) / 2) * (1 : Mat 2) i j + ((a - b) / 2) * T u i j =
    ((a' + b') / 2) * (1 : Mat 2) i j + ((a' - b') / 2) * T v i j at he
  change (a - b) * T u i j = (a' - b') * T v i j
  rw [hs] at he; linarith

theorem continuous_descend_compact
    {K X Y : Type*} [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    (f : K → X) (g : K → Y) (e : X → Y)
    (hf : Continuous f) (hg : Continuous g) (hs : Function.Surjective f)
    (he : ∀ k, e (f k) = g k) : Continuous e := by
  refine continuous_iff_isClosed.mpr fun s hclosed => ?_
  have hset : e ⁻¹' s = f '' (g ⁻¹' s) := by
    ext x; refine ⟨fun hx => ?_, fun ⟨k, hk, hfk⟩ => by simpa only [Set.mem_preimage, ← hfk, he k] using hk⟩
    obtain ⟨k, rfl⟩ := hs x
    exact ⟨k, by simpa only [Set.mem_preimage, he k] using hx, rfl⟩
  rw [hset]
  exact ((hclosed.preimage hg).isCompact.image hf).isClosed

theorem exists_homeomorph_ranges_of_same_fibres
    {K Y Z : Type*} [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace Y] [T2Space Y] [TopologicalSpace Z] [T2Space Z]
    (f : K → Y) (g : K → Z) (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ a b, f a = f b ↔ g a = g b) :
    ∃ h : Set.range f ≃ₜ Set.range g,
      ∀ k, h ⟨f k, ⟨k, rfl⟩⟩ = ⟨g k, ⟨k, rfl⟩⟩ := by
  classical
  let f' : K → Set.range f := fun k => ⟨f k, ⟨k, rfl⟩⟩
  let g' : K → Set.range g := fun k => ⟨g k, ⟨k, rfl⟩⟩
  have hf' : Continuous f' := hf.subtype_mk _
  have hg' : Continuous g' := hg.subtype_mk _
  have hsf : Function.Surjective f' := fun ⟨_, k, hk⟩ => ⟨k, Subtype.ext hk⟩
  have hsg : Function.Surjective g' := fun ⟨_, k, hk⟩ => ⟨k, Subtype.ext hk⟩
  let forward : Set.range f → Set.range g := fun y => g' (Classical.choose y.property)
  let inv : Set.range g → Set.range f := fun z => f' (Classical.choose z.property)
  have hto (k) : forward (f' k) = g' k := Subtype.ext ((hfg _ _).mp (Classical.choose_spec (f' k).property))
  have hinv (k) : inv (g' k) = f' k := Subtype.ext ((hfg _ _).mpr (Classical.choose_spec (g' k).property))
  exact ⟨{
    toFun := forward
    invFun := inv
    left_inv := fun y => by obtain ⟨k, rfl⟩ := hsf y; rw [hto, hinv]
    right_inv := fun z => by obtain ⟨k, rfl⟩ := hsg z; rw [hinv, hto]
    continuous_toFun := continuous_descend_compact f' g' forward hf' hg' hsf hto
    continuous_invFun := continuous_descend_compact g' f' inv hg' hf' hsg hinv
  }, hto⟩

def matrixExp {n : ℕ} (A : Mat n) : Mat n :=
  ∑' k : ℕ, ((k.factorial : ℝ)⁻¹) • A ^ k

theorem matrixExp_eq_exp {n : ℕ} (A : Mat n) :
    matrixExp A = NormedSpace.exp A := by
  rw [NormedSpace.exp_eq_tsum (𝕂 := ℝ)]; rfl

theorem matrixExp_hasSum {n : ℕ} (A : Mat n) :
    HasSum (fun k : ℕ => ((k.factorial : ℝ)⁻¹) • A ^ k) (matrixExp A) := by
  let : SeminormedRing (Mat n) := Matrix.linftyOpSemiNormedRing
  let : NormedRing (Mat n) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℝ (Mat n) := Matrix.linftyOpNormedAlgebra
  rw [matrixExp_eq_exp]
  exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A

theorem continuous_matrixExp (n : ℕ) : Continuous (@matrixExp n) := by
  let : SeminormedRing (Mat n) := Matrix.linftyOpSemiNormedRing
  let : NormedRing (Mat n) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℝ (Mat n) := Matrix.linftyOpNormedAlgebra
  have he : @matrixExp n = NormedSpace.exp := funext matrixExp_eq_exp
  rw [he]
  exact continuous_iff_continuousAt.mpr fun A => (NormedSpace.exp_analytic (𝕂 := ℝ) A).continuousAt

def rotation (t : ℝ) : Mat 2 :=
  !![Real.cos t, -Real.sin t; Real.sin t, Real.cos t]

theorem continuous_rotation : Continuous rotation := by
  apply continuous_pi; intro i; apply continuous_pi; intro j
  fin_cases i <;> fin_cases j <;> simp [rotation] <;> fun_prop

theorem rotation_orthogonal (t : ℝ) : Orthogonal (rotation t) := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [rotation, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ] <;>
    nlinarith [Real.sin_sq_add_cos_sq t]

abbrev OriginalParameters (q : ℕ) :=
  (Fin q → ℝ) × (Fin q → ℝ) × Mat q × Mat q × CircleVector

def originalK (q : ℕ) (η : ℝ) : Set (OriginalParameters q) :=
  {p | let (ell, r, c, z, u) := p
       (∀ i, |ell i| ≤ η) ∧ (∀ j, |r j| ≤ η) ∧
       (∀ j : Fin q, j.val = 0 → r j = 0) ∧
       IsSkew c ∧ IsSkew z ∧ frobSq c ≤ η ^ 2 ∧ frobSq z ≤ η ^ 2 ∧ OnCircle u}

def originalPsi {q : ℕ} (Q₀ c : Mat q) : Mat q := Q₀ * matrixExp c

theorem continuous_originalPsi {q : ℕ} (Q₀ : Mat q) :
    Continuous (originalPsi Q₀) := continuous_const.mul (continuous_matrixExp q)

def originalF {q : ℕ} (Q₀ : Mat q) (p : OriginalParameters q) : Mat (q * 2) :=
  let (ell, r, c, z, u) := p
  let A := originalPsi Q₀ (c + z)
  let B := originalPsi Q₀ (c - z)
  fun i j =>
    let ri : Fin q × Fin 2 := finProdFinEquiv.symm i
    let rj : Fin q × Fin 2 := finProdFinEquiv.symm j
    (rotation (ell ri.1) * middleBlock (A ri.1 rj.1) (B ri.1 rj.1) u *
      rotation (r rj.1)) ri.2 rj.2

theorem continuous_originalF {q : ℕ} (Q₀ : Mat q) :
    Continuous (originalF Q₀) := by
  have hpsi := continuous_originalPsi Q₀
  have hrot := continuous_rotation
  have ht := continuous_T
  unfold originalF middleBlock; fun_prop

def originalG {q : ℕ} (p : OriginalParameters q) :
    (Fin q → ℝ) × (Fin q → ℝ) × Mat q × Matrix (Fin 2) (Fin q × Fin q) ℝ :=
  let (ell, r, c, z, u) := p
  (ell, r, c, outer u (fun ij => z ij.1 ij.2))

theorem continuous_originalG (q : ℕ) : Continuous (@originalG q) := by
  unfold originalG outer; fun_prop

theorem matrix_entries_injective {q : ℕ} :
    Function.Injective (fun z : Mat q => fun ij : Fin q × Fin q => z ij.1 ij.2) :=
  fun _ _ h => funext fun i => funext fun j => congrFun h (i, j)

theorem originalG_fibres {q : ℕ}
    (ell r ell' r' : Fin q → ℝ) (c z c' w : Mat q) (u v : CircleVector)
    (hu : OnCircle u) (hv : OnCircle v) :
    originalG (ell, r, c, z, u) = originalG (ell', r', c', w, v) ↔
      ell = ell' ∧ r = r' ∧ c = c' ∧
        ((z = 0 ∧ w = 0) ∨ (u = v ∧ z = w) ∨ (u = -v ∧ z = -w)) := by
  have heq (x y : Mat q) : (fun ij : Fin q × Fin q => x ij.1 ij.2) =
      (fun ij : Fin q × Fin q => y ij.1 ij.2) ↔ x = y :=
    matrix_entries_injective.eq_iff
  have hz0 : (fun ij : Fin q × Fin q => z ij.1 ij.2) = 0 ↔ z = 0 := heq z 0
  have hw0 : (fun ij : Fin q × Fin q => w ij.1 ij.2) = 0 ↔ w = 0 := heq w 0
  have hneg : (fun ij : Fin q × Fin q => z ij.1 ij.2) = -(fun ij : Fin q × Fin q => w ij.1 ij.2) ↔ z = -w := heq z (-w)
  simp only [originalG, Prod.mk.injEq, outer_fibres hu hv, hz0, hw0, heq z w, hneg]

def scalarShuffle (k b : ℕ) : Equiv.Perm (Fin (k * b)) :=
  (finProdFinEquiv.symm.trans (Equiv.prodComm (Fin k) (Fin b))).trans
    (finProdFinEquiv.trans (Equiv.cast (congrArg Fin (Nat.mul_comm b k))))

def localFamily (q : ℕ) : Set (Mat (q * 2)) :=
  let P := permMatrix (scalarShuffle q 2)
  {M | InA3Orth 2 q 2 P Pᵀ M}

def basePoint {q : ℕ} (Q₀ : Mat q) : Mat (q * 2) := fun i j =>
  let ri : Fin q × Fin 2 := finProdFinEquiv.symm i
  let rj : Fin q × Fin 2 := finProdFinEquiv.symm j
  Q₀ ri.1 rj.1 * (1 : Mat 2) ri.2 rj.2

def EuclideanAtSubset {X : Type*} [TopologicalSpace X] (S : Set X) (x : X) : Prop :=
  x ∈ S ∧ ∃ (U : Set X), IsOpen U ∧ x ∈ U ∧
    ∃ (d : ℕ) (V : Set (EuclideanSpace ℝ (Fin d))), IsOpen V ∧
      Nonempty (↥(S ∩ U) ≃ₜ ↥V)

abbrev CMat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def Unitary {n : ℕ} (A : CMat n) : Prop := Aᴴ * A = 1 ∧ A * Aᴴ = 1

def IsSkewHermitian {n : ℕ} (A : CMat n) : Prop := Aᴴ = -A

namespace Unitary
variable {n : ℕ} {A B : CMat n}

theorem one : Unitary (1 : CMat n) := ⟨by simp, by simp⟩

theorem conjTranspose (h : Unitary A) : Unitary Aᴴ :=
  ⟨by simpa using h.2, by simpa using h.1⟩

theorem mul (hA : Unitary A) (hB : Unitary B) : Unitary (A * B) :=
  ⟨by calc (A * B)ᴴ * (A * B) = Bᴴ * (Aᴴ * A) * B := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = 1 := by rw [hA.1]; simpa using hB.1,
   by calc (A * B) * (A * B)ᴴ = A * (B * Bᴴ) * Aᴴ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = 1 := by rw [hB.2]; simpa using hA.2⟩

end Unitary

end GS
