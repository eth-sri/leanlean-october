module

public import GS.Shared.BlockCoordinates
public import GS.Shared.Cayley
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Matrix
open scoped BigOperators

namespace GS.Shared
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

variable {b : ℕ} {τ : ℕ → ℕ} {A B C : M 𝕜 n}

def TiedEntries (b : ℕ) (τ : ℕ → ℕ) (A : M 𝕜 n) : Prop :=
  ∀ i j i' j' : Fin n,
    i.val / b = j.val / b → i'.val / b = j'.val / b →
    τ (i.val / b) = τ (i'.val / b) →
    i.val % b = i'.val % b → j.val % b = j'.val % b → A i j = A i' j'

namespace TiedEntries
theorem zero (b : ℕ) (τ : ℕ → ℕ) : TiedEntries b τ (0 : M 𝕜 n) := by
  intro i j i' j' _ _ _ _ _
  rfl

theorem one (b : ℕ) (τ : ℕ → ℕ) : TiedEntries b τ (1 : M 𝕜 n) := by
  intro i j i' j' hij hij' _ hi hj
  have he : i = j ↔ i' = j' := by
    constructor <;> grind [Nat.mod_add_div]
  simp only [Matrix.one_apply, he]

theorem add (hA : TiedEntries b τ A) (hB : TiedEntries b τ B) :
    TiedEntries b τ (A + B) := by
  grind [TiedEntries, Matrix.add_apply]

theorem smul (a : ℝ) (hA : TiedEntries b τ A) : TiedEntries b τ (a • A) := by
  grind [TiedEntries, Matrix.smul_apply]

theorem conjTranspose (hA : TiedEntries b τ A) : TiedEntries b τ Aᴴ := by
  intro i j i' j' h h' hτ hi hj
  exact congrArg star (hA j i j' i' h.symm h'.symm
    (by simpa only [← h, ← h'] using hτ) hj hi)

end TiedEntries

private theorem standard_block_coord {k b : ℕ} (x : Fin k × Fin b) :
    (finProdFinEquiv x).val % b = x.2.val := by
  change (x.2.val + b * x.1.val) % b = _
  simp [Nat.add_mod, Nat.mod_eq_of_lt x.2.isLt]

/-- After reindexing, the entrywise sharing conditions simply identify diagonal blocks. -/
theorem tiedEntries_blockView {k : ℕ} {A : M 𝕜 (k*b)} : TiedEntries b τ A ↔
    ∀ i j : Fin k, τ i.val = τ j.val →
      blockView finProdFinEquiv A i i = blockView finProdFinEquiv A j j := by
  constructor
  · intro h i j hij
    ext a c
    simp only [blockView_apply]
    apply h <;> simp only [standard_block_label, standard_block_coord, hij]
  · intro h
    simp_rw [TiedEntries, ← (finProdFinEquiv : Fin k × Fin b ≃ _).forall_congr_right,
      Prod.forall, standard_block_label, standard_block_coord, Fin.val_inj]
    rintro i a j c i' a' j' c' rfl rfl hτ rfl rfl
    exact congrFun (congrFun (h i i' hτ) a) c

namespace TiedEntries

theorem mul (hbn : b ∣ n) (hAs : CSupported (fun i => i.val / b) A)
    (hA : TiedEntries b τ A) (hB : TiedEntries b τ B) : TiedEntries b τ (A * B) := by
  obtain ⟨k,hk⟩ := hbn
  rw [Nat.mul_comm] at hk
  subst n
  rw [tiedEntries_blockView] at hA hB ⊢
  intro i j h
  rw [map_mul, blockView_diagonal finProdFinEquiv standard_block_label hAs]
  simp only [Matrix.diagonal_mul]
  rw [hA i j h, hB i j h]

end TiedEntries

/-- The algebra of supported matrices with the specified block ties. -/
def sharedAlgebra (hbn : b ∣ n) (τ : ℕ → ℕ) : Subalgebra ℝ (M 𝕜 n) where
  carrier := {A | CSupported (fun i => i.val / b) A ∧ TiedEntries b τ A}
  mul_mem' := fun hA hB => ⟨hA.1.mul hB.1, TiedEntries.mul hbn hA.1 hA.2 hB.2⟩
  add_mem' := fun hA hB => ⟨hA.1.add hB.1, hA.2.add hB.2⟩
  algebraMap_mem' r := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact ⟨CSupported.one.real_smul r, (TiedEntries.one b τ).smul r⟩

def sharedSkewSpace (b : ℕ) (τ : ℕ → ℕ) : Submodule ℝ (M 𝕜 n) where
  carrier := {A | CSupported (fun i => i.val / b) A ∧ IsSkewHermitian A ∧ TiedEntries b τ A}
  zero_mem' := ⟨CSupported.zero, by simp [IsSkewHermitian], TiedEntries.zero b τ⟩
  add_mem' := fun hA hB =>
    ⟨hA.1.add hB.1, skewHermitian_add hA.2.1 hB.2.1, hA.2.2.add hB.2.2⟩
  smul_mem' := fun a _ hA =>
    ⟨CSupported.real_smul a hA.1, skewHermitian_real_smul a hA.2.1, hA.2.2.smul a⟩

def SharedUnitaryFactor (b : ℕ) (τ : ℕ → ℕ) (A : M 𝕜 n) : Prop :=
  CSupported (fun i => i.val / b) A ∧ Unitary A ∧ TiedEntries b τ A


private theorem sharedAlgebra_inverse (hbn : b ∣ n)
    (hA : A ∈ sharedAlgebra hbn τ) (hAu : IsUnit A) : A⁻¹ ∈ sharedAlgebra hbn τ := by
  let S := sharedAlgebra (𝕜 := 𝕜) hbn τ
  let m : S →ₗ[ℝ] S := LinearMap.mulLeft ℝ ⟨A,hA⟩
  have hm : Function.Injective m := fun X Y h =>
    Subtype.ext (hAu.mul_left_cancel (congrArg Subtype.val h))
  obtain ⟨X, hX⟩ := LinearMap.injective_iff_surjective.mp hm 1
  rw [Matrix.inv_eq_right_inv (show A * X.val = 1 from congrArg Subtype.val hX)]
  exact X.prop

private theorem cayley_mem_sharedAlgebra (hbn : b ∣ n)
    (hA : A ∈ sharedAlgebra hbn τ) (ha : admissible A) : cayley A ∈ sharedAlgebra hbn τ := by
  let S := sharedAlgebra (𝕜 := 𝕜) hbn τ
  have h := sharedAlgebra_inverse hbn (S.add_mem S.one_mem hA) ha
  simpa only [cayley, two_smul, Matrix.nonsing_inv_eq_ringInverse] using S.sub_mem (S.add_mem h h) S.one_mem

/-- Every shared skew generator gives an actual shared unitary factor. -/
theorem cayley_shared (hbn : b ∣ n)
    (hC : C ∈ sharedSkewSpace b τ) :
    SharedUnitaryFactor b τ (cayley C) := by
  have ha := admissible_of_isSkew C hC.2.1
  have hm := cayley_mem_sharedAlgebra hbn ⟨hC.1, hC.2.2⟩ ha
  exact ⟨hm.1, (cayley_unitary_iff _ ha).mpr hC.2.1, hm.2⟩

/-- Inverse Cayley coordinates of a shared unitary factor obey the same ties. -/
theorem cayley_sharedSkew (hbn : b ∣ n)
    (hA : SharedUnitaryFactor b τ A) (ha : admissible A) :
    cayley A ∈ sharedSkewSpace b τ := by
  have hm := cayley_mem_sharedAlgebra hbn ⟨hA.1, hA.2.2⟩ ha
  exact ⟨hm.1, (cayley_unitary_iff _ (admissible_cayley _ ha)).mp (by rw [cayley_involutive _ ha]; exact hA.2.1), hm.2⟩

theorem shared_factor_conjTranspose (hA : SharedUnitaryFactor b τ A) :
    SharedUnitaryFactor b τ Aᴴ :=
  ⟨hA.1.conjTranspose, hA.2.1.conjTranspose, hA.2.2.conjTranspose⟩

theorem shared_factor_mul (hbn : b ∣ n)
    (hA : SharedUnitaryFactor b τ A) (hB : SharedUnitaryFactor b τ B) :
    SharedUnitaryFactor b τ (A * B) :=
  ⟨hA.1.mul hB.1, hA.2.1.mul hB.2.1,
    TiedEntries.mul hbn hA.1 hA.2.2 hB.2.2⟩

/-- Conjugation by an actual shared factor preserves the generator space. -/
theorem sharedSkew_conjugate (hbn : b ∣ n)
    (hA : SharedUnitaryFactor b τ A) (hC : C ∈ sharedSkewSpace b τ) :
    A * C * Aᴴ ∈ sharedSkewSpace b τ := by
  let S := sharedAlgebra (𝕜 := 𝕜) hbn τ
  have hm : A * C * Aᴴ ∈ S := S.mul_mem (S.mul_mem ⟨hA.1,hA.2.2⟩ ⟨hC.1,hC.2.2⟩)
    ⟨hA.1.conjTranspose,hA.2.2.conjTranspose⟩
  exact ⟨hm.1, IsSkewHermitian.conjugate hC.2.1 A, hm.2⟩

/-! Compact groups of supported, tied unitary matrices with the inherited topology. -/

/-- A valid complete-block layout and arbitrary within-layer sharing labels.
Unused labels are allowed; different layers have independent patterns. -/
structure Pattern (𝕜 : Type*) (n : ℕ) where
  size : ℕ
  divides : size ∣ n
  label : ℕ → ℕ

abbrev Factor (s : Pattern 𝕜 n) := {A : M 𝕜 n // SharedUnitaryFactor s.size s.label A}
abbrev Generator (s : Pattern 𝕜 n) := ↥(sharedSkewSpace (𝕜 := 𝕜) (n := n) s.size s.label)

instance (s : Pattern 𝕜 n) : Group (Factor s) where
  one := ⟨1, CSupported.one, Unitary.one, TiedEntries.one _ _⟩
  mul A B := ⟨A.val * B.val, shared_factor_mul s.divides A.property B.property⟩
  inv A := ⟨A.valᴴ, shared_factor_conjTranspose A.property⟩
  mul_assoc A B C := Subtype.ext (Matrix.mul_assoc A.val B.val C.val)
  one_mul A := Subtype.ext (Matrix.one_mul A.val)
  mul_one A := Subtype.ext (Matrix.mul_one A.val)
  inv_mul_cancel A := Subtype.ext A.property.2.1.1

instance (s : Pattern 𝕜 n) : IsTopologicalGroup (Factor s) where
  continuous_mul := ((continuous_subtype_val.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  continuous_inv := continuous_subtype_val.matrix_conjTranspose.subtype_mk _

instance factorCompactSpace (s : Pattern 𝕜 n) : CompactSpace (Factor s) := by
  apply isCompact_iff_compactSpace.mp (compact_unitary_of_closed ?_ fun _ h => h.2.1)
  let S := sharedAlgebra (𝕜 := 𝕜) s.divides s.label
  convert S.toSubmodule.closed_of_finiteDimensional.inter isClosed_unitary using 1
  ext A
  change (_ ∧ _ ∧ _) ↔ (_ ∧ _) ∧ _
  tauto

namespace Factor
variable {s : Pattern 𝕜 n}

abbrev matrix (A : Factor s) : M 𝕜 n := A.val

@[simp] theorem matrix_one : matrix (1 : Factor s) = 1 := rfl

theorem matrix_shared (A : Factor s) : SharedUnitaryFactor s.size s.label (matrix A) := A.property

theorem matrix_unitary (A : Factor s) : Unitary (matrix A) := A.property.2.1

theorem matrix_injective : Function.Injective (matrix : Factor s → M 𝕜 n) := Subtype.val_injective

theorem continuous_matrix : Continuous (matrix : Factor s → M 𝕜 n) := continuous_subtype_val

abbrev ofMatrix (A : M 𝕜 n) (hA : SharedUnitaryFactor s.size s.label A) : Factor s := ⟨A,hA⟩

@[simp] theorem matrix_ofMatrix (A : M 𝕜 n) (hA : SharedUnitaryFactor s.size s.label A) :
    matrix (ofMatrix A hA) = A := rfl

end Factor

/-- The two layers can use unrelated sharing maps and block sizes. -/
abbrev Factors (right left : Pattern 𝕜 n) := Factor left × Factor right

end GS.Shared
