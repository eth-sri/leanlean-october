import GS.MatrixGeometry.Base

import GS.MatrixGeometry.BlockGroup
import GS.MatrixGeometry.Cayley
import GS.MatrixGeometry.Inner
import GS.MatrixGeometry.Dual
import GS.MatrixGeometry.Indices






/-!
# Complex complete-block sharing as a real star algebra

The equality predicate is imposed on actual complex entries. Positive complete
physical blocks have the same finite local index set, so products preserve all
within-layer ties. Inverse closure is derived by finite-dimensional real linear
algebra. Neither skew-Hermitian generators nor the Cayley chart discard phases.
-/
open Matrix GS.MatrixBase
open GS.GlobalGeometry (localBlockIndex localBlockIndex_div localBlockIndex_mod)
namespace GS.MatrixGeometry
variable {𝕜 : Type} [RCLike 𝕜]
variable  {τ : ℕ → ℕ} {A B C : KMat 𝕜 n}

/-- Labels tie full complex blocks within one layer, never across layers. -/
def TiedEntries (b : ℕ) (τ : ℕ → ℕ) (A : KMat 𝕜 n) : Prop :=
  ∀ i j i' j' : Fin n,
    i.val / b = j.val / b → i'.val / b = j'.val / b →
    τ (i.val / b) = τ (i'.val / b) →
    i.val % b = i'.val % b → j.val % b = j'.val % b → A i j = A i' j'

namespace TiedEntries
theorem zero (b : ℕ) (τ : ℕ → ℕ) : TiedEntries b τ (0 : KMat 𝕜 n) := by tauto

theorem one (b : ℕ) (τ : ℕ → ℕ) : TiedEntries b τ (1 : KMat 𝕜 n) := by
  intro i j i' j' hij hij' _ hi hj
  have he : i = j ↔ i' = j' := by grind [Nat.ext_div_mod_iff]
  simp only [Matrix.one_apply, he]

theorem add (hA : TiedEntries b τ A) (hB : TiedEntries b τ B) :
    TiedEntries b τ (A + B) := by
  intro i j i' j' h h' hτ hi hj
  simp only [Matrix.add_apply, hA i j i' j' h h' hτ hi hj,
    hB i j i' j' h h' hτ hi hj]

theorem smul (a : ℝ) (hA : TiedEntries b τ A) : TiedEntries b τ (a • A) := by
  intro i j i' j' h h' hτ hi hj
  simp only [Matrix.smul_apply, hA i j i' j' h h' hτ hi hj]

theorem conjTranspose (hA : TiedEntries b τ A) : TiedEntries b τ Aᴴ := by
  intro i j i' j' h h' hτ hi hj
  exact congrArg star (hA j i j' i' h.symm h'.symm
    (by aesop) hj hi)

end TiedEntries

/-- Matrix multiplication within a full physical block is a sum over its local
coordinates. -/
theorem mul_apply_localBlockIndex (hb : 0 < b) (hbn : b ∣ n)
    (hA : CSupported (fun i => i.val / b) A) (i j : Fin n) :
    (A * B) i j = ∑ k : Fin b,
      A i (localBlockIndex hb hbn i k) * B (localBlockIndex hb hbn i k) j := by

  rw [Matrix.mul_apply]
  symm
  apply Fintype.sum_of_injective (localBlockIndex hb hbn i)
  · intro x y he
    apply Fin.ext
    simpa using congrArg (fun j : Fin n => j.val % b) he
  · intro k hk
    have hki : i.val / b ≠ k.val / b := by
      intro h
      apply hk
      refine ⟨⟨k.val % b, Nat.mod_lt _ hb⟩, Fin.ext ?_⟩
      simp only [localBlockIndex, h]
      exact Nat.div_add_mod' _ _
    rw [hA i k hki, zero_mul]
  · intro k; rfl

namespace TiedEntries

theorem mul (hb : 0 < b) (hbn : b ∣ n)
    (hAs : CSupported (fun i => i.val / b) A)
    (hA : TiedEntries b τ A) (hB : TiedEntries b τ B) :
    TiedEntries b τ (A * B) := by
  intro i j i' j' hij hij' hτ hi hj
  rw [mul_apply_localBlockIndex hb hbn hAs, mul_apply_localBlockIndex hb hbn hAs]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  · apply hA <;> simp_all
  · apply hB <;> simp_all

end TiedEntries

theorem isClosed_tiedEntries (b : ℕ) (τ : ℕ → ℕ) :
    IsClosed {A : KMat 𝕜 n | TiedEntries b τ A} := by
  simp only [TiedEntries, Set.setOf_forall]
  repeat' (apply isClosed_iInter; intro)
  exact isClosed_eq (by fun_prop) (by fun_prop)

/-- Expanded physical matrices, with their real vector space structure. -/
def sharedMatrixSpace (b : ℕ) (τ : ℕ → ℕ) : Submodule ℝ (KMat 𝕜 n) where
  carrier := {A | CSupported (fun i => i.val / b) A ∧ TiedEntries b τ A}
  zero_mem' := ⟨GS.MatrixBase.CSupported.zero, TiedEntries.zero b τ⟩
  add_mem' := fun hA hB => ⟨hA.1.add hB.1, hA.2.add hB.2⟩
  smul_mem' := fun a _ hA => ⟨GS.MatrixBase.CSupported.real_smul a hA.1, hA.2.smul a⟩

noncomputable def sharedSkewSpace (b : ℕ) (τ : ℕ → ℕ) : Submodule ℝ (KMat 𝕜 n) :=
  (sharedMatrixSpace b τ ⊓ skewAdjoint.submodule ℝ (KMat 𝕜 n)).copy
    {A | CSupported (fun i => i.val / b) A ∧ GS.MatrixBase.IsSkewHermitian A ∧ TiedEntries b τ A}
    (by ext A; exact and_assoc.symm.trans and_right_comm)

theorem one_mem_sharedMatrixSpace (b : ℕ) (τ : ℕ → ℕ) :
    (1 : KMat 𝕜 n) ∈ sharedMatrixSpace b τ := ⟨GS.MatrixBase.CSupported.one, TiedEntries.one b τ⟩

theorem mul_mem_sharedMatrixSpace (hb : 0 < b) (hbn : b ∣ n)
    (hA : A ∈ sharedMatrixSpace b τ) (hB : B ∈ sharedMatrixSpace b τ) :
    A * B ∈ sharedMatrixSpace b τ :=
  ⟨hA.1.mul hB.1, TiedEntries.mul hb hbn hA.1 hA.2 hB.2⟩

def SharedUnitaryFactor (b : ℕ) (τ : ℕ → ℕ) (A : KMat 𝕜 n) : Prop :=
  CSupported (fun i => i.val / b) A ∧ GS.MatrixBase.Unitary A ∧ TiedEntries b τ A

/-- Inverse closure is derived from finite-dimensional linear algebra, not
postulated as a property of the sharing predicate. -/
theorem sharedMatrixSpace_inverse (hb : 0 < b) (hbn : b ∣ n)
    (hA : A ∈ sharedMatrixSpace b τ) (hdet : A.det ≠ 0) :
    A⁻¹ ∈ sharedMatrixSpace b τ := by
  let S := sharedMatrixSpace (𝕜 := 𝕜) (n := n) b τ
  let m :=
    ((LinearMap.mulLeft ℝ A).comp S.subtype).codRestrict S
      (fun X => mul_mem_sharedMatrixSpace hb hbn hA X.property)
  have hm : Function.Injective m := by
    intro X Y h
    apply Subtype.ext
    exact GS.MatrixBase.cancel_left A X.val Y.val hdet (congrArg Subtype.val h)
  obtain ⟨X, hX⟩ := (LinearMap.injective_iff_surjective.mp hm)
    (⟨1, one_mem_sharedMatrixSpace b τ⟩ : S)
  rw [Matrix.inv_eq_right_inv (congrArg Subtype.val hX)]
  exact X.property

/-- The original rational Cayley transform preserves all physical block ties. -/
theorem cayley_mem_sharedMatrixSpace (hb : 0 < b) (hbn : b ∣ n)
    (hA : A ∈ sharedMatrixSpace b τ) (ha : admissible A) :
    cayley A ∈ sharedMatrixSpace b τ :=
  mul_mem_sharedMatrixSpace hb hbn
    ((sharedMatrixSpace (𝕜 := 𝕜) b τ).sub_mem (one_mem_sharedMatrixSpace b τ) hA)
    (sharedMatrixSpace_inverse hb hbn
      ((sharedMatrixSpace (𝕜 := 𝕜) b τ).add_mem (one_mem_sharedMatrixSpace b τ) hA) ha)

/-- Every shared skew generator gives an actual shared unitary factor. -/
theorem cayley_shared (hb : 0 < b) (hbn : b ∣ n)
    (hC : C ∈ sharedSkewSpace b τ) :
    SharedUnitaryFactor b τ (cayley C) := by
  have ha := admissible_of_isSkew C hC.2.1
  have hm := cayley_mem_sharedMatrixSpace hb hbn ⟨hC.1, hC.2.2⟩ ha
  exact ⟨hm.1, cayley_unitary C hC.2.1 ha, hm.2⟩



theorem shared_factor_conjTranspose (hA : SharedUnitaryFactor b τ A) :
    SharedUnitaryFactor b τ Aᴴ :=
  ⟨hA.1.conjTranspose, hA.2.1.conjTranspose, hA.2.2.conjTranspose⟩

theorem shared_factor_mul (hb : 0 < b) (hbn : b ∣ n)
    (hA : SharedUnitaryFactor b τ A) (hB : SharedUnitaryFactor b τ B) :
    SharedUnitaryFactor b τ (A * B) :=
  ⟨hA.1.mul hB.1, hA.2.1.mul hB.2.1,
    TiedEntries.mul hb hbn hA.1 hA.2.2 hB.2.2⟩

/-- Conjugation by an actual shared factor preserves the generator space. -/
theorem sharedSkew_conjugate (hb : 0 < b) (hbn : b ∣ n)
    (hA : SharedUnitaryFactor b τ A) (hC : C ∈ sharedSkewSpace b τ) :
    A * C * Aᴴ ∈ sharedSkewSpace b τ := by
  have hm :=
    mul_mem_sharedMatrixSpace hb hbn
      (mul_mem_sharedMatrixSpace hb hbn ⟨hA.1, hA.2.2⟩ ⟨hC.1, hC.2.2⟩)
      ⟨hA.1.conjTranspose, hA.2.2.conjTranspose⟩
  refine ⟨hm.1, ?_, hm.2⟩
  exact skewAdjoint.conjugate hC.2.1 A

/-- The reverse conjugation is a separate useful form of the same result. -/
theorem sharedSkew_conjugate_conjTranspose (hb : 0 < b) (hbn : b ∣ n)
    (hA : SharedUnitaryFactor b τ A) (hC : C ∈ sharedSkewSpace b τ) :
    Aᴴ * C * A ∈ sharedSkewSpace b τ := by grind [sharedSkew_conjugate,shared_factor_conjTranspose,Matrix.conjTranspose_conjTranspose]

end GS.MatrixGeometry
