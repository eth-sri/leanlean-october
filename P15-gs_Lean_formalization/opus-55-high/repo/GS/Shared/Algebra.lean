module

public import GS.Shared.Base

@[expose] public section

/-! Complete-block sharing as a real star algebra, over an arbitrary `RCLike` field. -/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix
namespace GS.Shared
variable {𝕜 : Type*} [RCLike 𝕜] {n b : ℕ} {τ : ℕ → ℕ} {A B C : 𝕄}

section
variable (hb : 0 < b) (hbn : b ∣ n) (i : Fin n) (k : Fin b)
/-- The index with prescribed local coordinate in the physical block of `i`. -/
def localBlockIndex : Fin n :=
  ⟨i.val / b * b + k.val, by
    have hin : i.val / b < n / b := (Nat.div_lt_iff_lt_mul hb).mpr (by
      simpa only [Nat.div_mul_cancel hbn] using i.isLt)
    calc
      i.val / b * b + k.val < i.val / b * b + b := by simp
      _ = (i.val / b + 1) * b := by grind
      _ ≤ n / b * b := by simp_all
      _ = n := Nat.div_mul_cancel hbn⟩

@[simp] theorem localBlockIndex_div : (localBlockIndex hb hbn i k).val / b = i.val / b := by
  change (i.val / b * b + k.val) / b = i.val / b
  rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ hb,
    Nat.div_eq_of_lt k.isLt, Nat.zero_add]

@[simp] theorem localBlockIndex_mod : (localBlockIndex hb hbn i k).val % b = k.val := by
  simp [localBlockIndex, Nat.add_mod, Nat.mod_eq_of_lt k.isLt]

end

/-- Labels tie full blocks within one layer, never across layers. -/
def Tied (b : ℕ) (τ : ℕ → ℕ) (A : 𝕄) : Prop :=
  ∀ i j i' j' : Fin n,
    i.val / b = j.val / b → i'.val / b = j'.val / b →
    τ (i.val / b) = τ (i'.val / b) →
    i.val % b = i'.val % b → j.val % b = j'.val % b → A i j = A i' j'

namespace Tied
theorem one (b : ℕ) (τ : ℕ → ℕ) : Tied b τ (1 : 𝕄) := by
  intro i j i' j' hij hij' _ hi hj
  have he : i = j ↔ i' = j' := by
    have := Nat.mod_add_div i'.val b
    have := Nat.mod_add_div j'.val b
    have := Nat.mod_add_div i.val b
    have := Nat.mod_add_div j.val b
    grind
  simp only [Matrix.one_apply, he]

theorem add (hA : Tied b τ A) (hB : Tied b τ B) : Tied b τ (A + B) := by
  intro i j i' j' h h' hτ hi hj
  simp only [Matrix.add_apply, hA i j i' j' h h' hτ hi hj, hB i j i' j' h h' hτ hi hj]

theorem conjTranspose (hA : Tied b τ A) : Tied b τ Aᴴ := fun i j i' j' h h' _ hi hj =>
  congrArg star (hA j i j' i' h.symm h'.symm (by grind) hj hi)
end Tied

/-- Matrix multiplication within a full physical block is a sum over its local coordinates. -/
theorem mul_apply_localBlockIndex (hb : 0 < b) (hbn : b ∣ n)
    (hA : Supp (fun i => i.val / b) A) (i j : Fin n) :
    (A * B) i j = ∑ k : Fin b,
      A i (localBlockIndex hb hbn i k) * B (localBlockIndex hb hbn i k) j := by
  classical
  rw [Matrix.mul_apply, ← Finset.sum_subset (Finset.filter_subset (fun k : Fin n => k.val / b = i.val / b) _)
    (by aesop)]
  apply Finset.sum_bij (fun k _ => (⟨k.val % b, Nat.mod_lt _ hb⟩ : Fin b))
  · simp
  · intro k hk l hl he
    have := Nat.mod_add_div k.val b
    have := Nat.mod_add_div l.val b
    grind
  · exact fun k _ => ⟨localBlockIndex hb hbn i k, by simp, by simp⟩
  · intro k hk
    rw [show localBlockIndex hb hbn i ⟨k.val % b, Nat.mod_lt _ hb⟩ = k from Fin.ext <| by
      simp only [localBlockIndex, ← (Finset.mem_filter.mp hk).2]; exact Nat.div_add_mod' _ _]

theorem Tied.mul (hb : 0 < b) (hbn : b ∣ n) (hAs : Supp (fun i => i.val / b) A)
    (hA : Tied b τ A) (hB : Tied b τ B) : Tied b τ (A * B) := by
  intro i j i' j' hij hij' hτ hi hj
  rw [mul_apply_localBlockIndex hb hbn hAs, mul_apply_localBlockIndex hb hbn hAs]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : A i (localBlockIndex hb hbn i k) = A i' (localBlockIndex hb hbn i' k) := by aesop
  aesop

section
variable (b : ℕ) (τ : ℕ → ℕ)
/-- Supported tied matrices form a concrete real submodule. -/
def sharedMatrixSpace : Submodule ℝ 𝕄 where
  carrier := {A | Supp (fun i => i.val / b) A ∧ Tied b τ A}
  zero_mem' := ⟨by tauto, by tauto⟩
  add_mem' hA hB := ⟨hA.1.add hB.1, hA.2.add hB.2⟩
  smul_mem' a _ hA := ⟨hA.1.smul a, fun i j i' j' h h' hτ hi hj => by simp [hA.2 i j i' j' h h' hτ hi hj]⟩

def sharedSkewSpace : Submodule ℝ 𝕄 where
  carrier := {A | Supp (fun i => i.val / b) A ∧ Aᴴ = -A ∧ Tied b τ A}
  zero_mem' := ⟨by tauto, by simp, by tauto⟩
  add_mem' hA hB := ⟨hA.1.add hB.1, by simp [hA.2.1, hB.2.1, add_comm], hA.2.2.add hB.2.2⟩
  smul_mem' a _ hA := ⟨hA.1.smul a, skew_smul a hA.2.1, ((sharedMatrixSpace b τ).smul_mem a ⟨hA.1, hA.2.2⟩).2⟩

theorem isClosed_sharedMatrixSpace : IsClosed (sharedMatrixSpace (𝕜 := 𝕜) (n := n) b τ : Set 𝕄) :=
  Submodule.closed_of_finiteDimensional _

theorem one_mem_sharedMatrixSpace :
    (1 : 𝕄) ∈ sharedMatrixSpace b τ := ⟨Supp.one, Tied.one b τ⟩

end

theorem mul_mem_sharedMatrixSpace (hb : 0 < b) (hbn : b ∣ n)
    (hA : A ∈ sharedMatrixSpace b τ) (hB : B ∈ sharedMatrixSpace b τ) :
    A * B ∈ sharedMatrixSpace b τ :=
  ⟨hA.1.mul hB.1, Tied.mul hb hbn hA.1 hA.2 hB.2⟩

def SharedFactor (b : ℕ) (τ : ℕ → ℕ) (A : 𝕄) : Prop :=
  Supp (fun i => i.val / b) A ∧ Uni A ∧ Tied b τ A

/-- Inverse closure from finite-dimensional linear algebra. -/
theorem sharedMatrixSpace_inverse (hb : 0 < b) (hbn : b ∣ n)
    (hA : A ∈ sharedMatrixSpace b τ) (hdet : A.det ≠ 0) :
    A⁻¹ ∈ sharedMatrixSpace b τ := by
  let S := sharedMatrixSpace (𝕜 := 𝕜) (n := n) b τ
  let m : S →ₗ[ℝ] S :=
    { toFun X := ⟨A * X, mul_mem_sharedMatrixSpace hb hbn hA X.2⟩
      map_add' X Y := Subtype.ext (Matrix.mul_add A X.1 Y.1)
      map_smul' := by simp }
  obtain ⟨X, hX⟩ := (LinearMap.injective_iff_surjective (f := m)).mp (fun X Y h =>
    Subtype.ext (cancel_left hdet (by aesop))) ⟨1, one_mem_sharedMatrixSpace b τ⟩
  rw [← cancel_left hdet ((congrArg Subtype.val hX).trans (mul_nonsing_inv A (isUnit_iff_ne_zero.2 hdet)).symm)]
  simp

/-- The rational Cayley transform preserves all physical block ties. -/
theorem cayley_mem_sharedMatrixSpace (hb : 0 < b) (hbn : b ∣ n)
    (hA : A ∈ sharedMatrixSpace b τ) (ha : admissible A) :
    cayley A ∈ sharedMatrixSpace b τ :=
  mul_mem_sharedMatrixSpace hb hbn (sub_mem (one_mem_sharedMatrixSpace b τ) hA)
    (sharedMatrixSpace_inverse hb hbn (add_mem (one_mem_sharedMatrixSpace b τ) hA) ha)

theorem cayley_shared (hb : 0 < b) (hbn : b ∣ n) (hC : C ∈ sharedSkewSpace b τ) :
    SharedFactor b τ (cayley C) :=
  have hm := cayley_mem_sharedMatrixSpace hb hbn ⟨hC.1, hC.2.2⟩ (admissible_of_isSkew hC.2.1)
  ⟨hm.1, cayley_unitary hC.2.1 (admissible_of_isSkew hC.2.1), hm.2⟩

theorem cayley_sharedSkew (hb : 0 < b) (hbn : b ∣ n)
    (hA : SharedFactor b τ A) (ha : admissible A) : cayley A ∈ sharedSkewSpace b τ :=
  have hm := cayley_mem_sharedMatrixSpace hb hbn ⟨hA.1, hA.2.2⟩ ha
  ⟨hm.1, cayley_isSkew hA.2.1 ha, hm.2⟩

theorem shared_factor_conjTranspose (hA : SharedFactor b τ A) : SharedFactor b τ Aᴴ :=
  ⟨hA.1.conjTranspose, hA.2.1.conjTranspose, hA.2.2.conjTranspose⟩

theorem shared_factor_mul (hb : 0 < b) (hbn : b ∣ n)
    (hA : SharedFactor b τ A) (hB : SharedFactor b τ B) : SharedFactor b τ (A * B) :=
  ⟨hA.1.mul hB.1, hA.2.1.mul hB.2.1, Tied.mul hb hbn hA.1 hA.2.2 hB.2.2⟩

/-- Conjugation by a shared factor preserves the generator space. -/
theorem sharedSkew_conjugate (hb : 0 < b) (hbn : b ∣ n)
    (hA : SharedFactor b τ A) (hC : C ∈ sharedSkewSpace b τ) :
    A * C * Aᴴ ∈ sharedSkewSpace b τ :=
  have hm := mul_mem_sharedMatrixSpace hb hbn
    (mul_mem_sharedMatrixSpace hb hbn ⟨hA.1, hA.2.2⟩ ⟨hC.1, hC.2.2⟩)
    ⟨hA.1.conjTranspose, hA.2.2.conjTranspose⟩
  ⟨hm.1, by simp [hC.2.1, Matrix.mul_assoc], hm.2⟩

theorem sharedSkew_conjugate_conjTranspose (hb : 0 < b) (hbn : b ∣ n)
    (hA : SharedFactor b τ A) (hC : C ∈ sharedSkewSpace b τ) :
    Aᴴ * C * A ∈ sharedSkewSpace b τ := by
  simpa using sharedSkew_conjugate hb hbn (shared_factor_conjTranspose hA) hC

end GS.Shared
