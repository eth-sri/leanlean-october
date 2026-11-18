module

public import GS.UnitaryManifold.CayleySmooth
public import GS.UnitaryManifold.BlockGroup
public import GS.UnitaryManifold.Action
public import GS.Unitary.FrobeniusProjection
public import Mathlib.Topology.Constructions.SumProd

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.UnitaryManifold
open scoped BigOperators Topology

namespace GS.UnitarySharing
abbrev SMat (𝕂 : Type) (n : ℕ) := Matrix (Fin n) (Fin n) 𝕂
variable {𝕂 : Type} [RCLike 𝕂] {n b : ℕ} {τ : ℕ → ℕ} {A B C : SMat 𝕂 n}

def localBlockIndex (hb : 0 < b) (hbn : b ∣ n) (i : Fin n) (k : Fin b) : Fin n :=
  ⟨i.val / b * b + k.val, by
    have hin : i.val / b < n / b := (Nat.div_lt_iff_lt_mul hb).mpr
      (by simpa only [Nat.div_mul_cancel hbn] using i.isLt)
    calc i.val / b * b + k.val < (i.val / b + 1) * b := by rw [Nat.add_mul, Nat.one_mul]; omega
      _ ≤ n / b * b := Nat.mul_le_mul_right b hin
      _ = n := Nat.div_mul_cancel hbn⟩

@[simp] theorem localBlockIndex_div (hb : 0 < b) (hbn : b ∣ n) (i : Fin n) (k : Fin b) :
    (localBlockIndex hb hbn i k).val / b = i.val / b := by
  change (i.val / b * b + k.val) / b = i.val / b
  rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt k.isLt, Nat.zero_add]

@[simp] theorem localBlockIndex_mod (hb : 0 < b) (hbn : b ∣ n) (i : Fin n) (k : Fin b) :
    (localBlockIndex hb hbn i k).val % b = k.val := by
  simp [localBlockIndex, Nat.add_mod, Nat.mod_eq_of_lt k.isLt]

def KTiedEntries (b : ℕ) (τ : ℕ → ℕ) (A : SMat 𝕂 n) : Prop :=
  ∀ i j i' j' : Fin n,
    i.val / b = j.val / b → i'.val / b = j'.val / b →
    τ (i.val / b) = τ (i'.val / b) →
    i.val % b = i'.val % b → j.val % b = j'.val % b → A i j = A i' j'

namespace KTiedEntries
theorem zero (b : ℕ) (τ : ℕ → ℕ) : KTiedEntries b τ (0 : SMat 𝕂 n) := fun _ _ _ _ _ _ _ _ _ => rfl

theorem one (b : ℕ) (τ : ℕ → ℕ) : KTiedEntries b τ (1 : SMat 𝕂 n) := by
  have heq {i j i' j' : Fin n} (hij' : i'.val / b = j'.val / b)
      (hi : i.val % b = i'.val % b) (hj : j.val % b = j'.val % b) (h : i = j) : i' = j' := by
    subst h; apply Fin.ext
    have h1 := Nat.mod_add_div i'.val b; have h2 := Nat.mod_add_div j'.val b
    rw [hi.symm.trans hj, hij'] at h1; omega
  intro i j i' j' hij hij' _ hi hj
  have he : i = j ↔ i' = j' := ⟨heq hij' hi hj, heq hij hi.symm hj.symm⟩
  simp only [Matrix.one_apply, he]

theorem add (hA : KTiedEntries b τ A) (hB : KTiedEntries b τ B) : KTiedEntries b τ (A + B) :=
  fun i j i' j' h h' hτ hi hj => by simp [hA i j i' j' h h' hτ hi hj, hB i j i' j' h h' hτ hi hj]

theorem smul (a : ℝ) (hA : KTiedEntries b τ A) : KTiedEntries b τ (a • A) :=
  fun i j i' j' h h' hτ hi hj => by simp [hA i j i' j' h h' hτ hi hj]

theorem conjTranspose (hA : KTiedEntries b τ A) : KTiedEntries b τ Aᴴ :=
  fun i j i' j' h h' hτ hi hj => congrArg star (hA j i j' i' h.symm h'.symm (by simpa [← h, ← h'] using hτ) hj hi)

theorem mul (hb : 0 < b) (hbn : b ∣ n)
    (hAs : KSSupported (fun i => i.val / b) A) (_hBs : KSSupported (fun i => i.val / b) B)
    (hA : KTiedEntries b τ A) (hB : KTiedEntries b τ B) : KTiedEntries b τ (A * B) := by
  have hloc (X Y : SMat 𝕂 n) (hXs : KSSupported (fun i => i.val / b) X) (i j : Fin n) :
      (X * Y) i j = ∑ k : Fin b, X i (localBlockIndex hb hbn i k) * Y (localBlockIndex hb hbn i k) j := by
    classical
    rw [Matrix.mul_apply, ← Finset.sum_subset (s₁ := Finset.univ.filter fun k => k.val / b = i.val / b)
      (Finset.filter_subset _ _) fun k _ hk => by
        rw [hXs i k (by simpa [eq_comm] using hk), zero_mul]]
    refine Finset.sum_bij (fun k _ => ⟨k.val % b, Nat.mod_lt _ hb⟩) (fun _ _ => Finset.mem_univ _)
      (fun k hk l hl he => Fin.ext <| by
        have he' : k.val % b = l.val % b := congrArg Fin.val he
        have h1 := Nat.mod_add_div k.val b; have h2 := Nat.mod_add_div l.val b
        rw [(Finset.mem_filter.mp hk).2, he'] at h1
        rw [(Finset.mem_filter.mp hl).2] at h2; omega)
      (fun k _ => ⟨localBlockIndex hb hbn i k, by simp, Fin.ext (localBlockIndex_mod hb hbn i k)⟩)
      fun k hk => by
        have he : localBlockIndex hb hbn i ⟨k.val % b, Nat.mod_lt _ hb⟩ = k := by
          apply Fin.ext; simp only [localBlockIndex, ← (Finset.mem_filter.mp hk).2]; exact Nat.div_add_mod' _ _
        rw [he]
  intro i j i' j' hij hij' hτ hi hj
  rw [hloc A B hAs, hloc A B hAs]
  exact Finset.sum_congr rfl fun k _ => by
    rw [hA i (localBlockIndex hb hbn i k) i' (localBlockIndex hb hbn i' k) (by simp) (by simp) hτ hi (by simp),
        hB (localBlockIndex hb hbn i k) j (localBlockIndex hb hbn i' k) j'
          (by simpa using hij) (by simpa using hij') (by simpa using hτ) (by simp) hj]
end KTiedEntries

theorem isClosed_tiedEntries (b : ℕ) (τ : ℕ → ℕ) : IsClosed {A : SMat 𝕂 n | KTiedEntries b τ A} := by
  simp only [KTiedEntries, Set.setOf_forall]
  exact isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
    isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => isClosed_eq (by fun_prop) (by fun_prop)

def sharedMatrixSpace (𝕂 : Type) [RCLike 𝕂] (b : ℕ) (τ : ℕ → ℕ) : Submodule ℝ (SMat 𝕂 n) where
  carrier := {A | KSSupported (fun i => i.val / b) A ∧ KTiedEntries b τ A}
  zero_mem' := ⟨KSSupported.zero, KTiedEntries.zero (𝕂 := 𝕂) b τ⟩
  add_mem' hA hB := ⟨hA.1.add hB.1, hA.2.add hB.2⟩
  smul_mem' a _ hA := ⟨KSSupported.real_smul a hA.1, hA.2.smul a⟩

def sharedSkewSpace (𝕂 : Type) [RCLike 𝕂] (b : ℕ) (τ : ℕ → ℕ) : Submodule ℝ (SMat 𝕂 n) where
  carrier := {A | KSSupported (fun i => i.val / b) A ∧ IsSkewHermitian A ∧ KTiedEntries b τ A}
  zero_mem' := ⟨KSSupported.zero, by simp [IsSkewHermitian], KTiedEntries.zero (𝕂 := 𝕂) b τ⟩
  add_mem' hA hB := ⟨hA.1.add hB.1, skewHermitian_add hA.2.1 hB.2.1, hA.2.2.add hB.2.2⟩
  smul_mem' a _ hA := ⟨KSSupported.real_smul a hA.1, skewHermitian_real_smul a hA.2.1, hA.2.2.smul a⟩

theorem one_mem_sharedMatrixSpace (𝕂 : Type) [RCLike 𝕂] (b : ℕ) (τ : ℕ → ℕ) :
    (1 : SMat 𝕂 n) ∈ sharedMatrixSpace 𝕂 b τ := ⟨KSSupported.one, KTiedEntries.one (𝕂 := 𝕂) b τ⟩

theorem mul_mem_sharedMatrixSpace (hb : 0 < b) (hbn : b ∣ n)
    (hA : A ∈ sharedMatrixSpace 𝕂 b τ) (hB : B ∈ sharedMatrixSpace 𝕂 b τ) :
    A * B ∈ sharedMatrixSpace 𝕂 b τ :=
  ⟨hA.1.mul hB.1, KTiedEntries.mul hb hbn hA.1 hB.1 hA.2 hB.2⟩

def KSharedFactor (b : ℕ) (τ : ℕ → ℕ) (A : SMat 𝕂 n) : Prop :=
  KSSupported (fun i => i.val / b) A ∧ GS.KUnitary A ∧ KTiedEntries b τ A

theorem sharedMatrixSpace_inverse (hb : 0 < b) (hbn : b ∣ n)
    (hA : A ∈ sharedMatrixSpace 𝕂 b τ) (hdet : A.det ≠ 0) : A⁻¹ ∈ sharedMatrixSpace 𝕂 b τ := by
  let S := sharedMatrixSpace 𝕂 (n := n) b τ
  let m : S →ₗ[ℝ] S :=
    { toFun := fun X => ⟨A * X.val, mul_mem_sharedMatrixSpace hb hbn hA X.property⟩
      map_add' := fun X Y => Subtype.ext (Matrix.mul_add A X.val Y.val)
      map_smul' := fun a X => Subtype.ext (Matrix.mul_smul A a X.val) }
  have hm : Function.Injective m := fun X Y h =>
    Subtype.ext (GS.UnitaryManifold.cancel_left A X.val Y.val hdet (congrArg Subtype.val h))
  obtain ⟨X, hX⟩ := LinearMap.injective_iff_surjective.mp hm ⟨1, one_mem_sharedMatrixSpace 𝕂 b τ⟩
  have he : X.val = A⁻¹ := GS.UnitaryManifold.cancel_left A X.val A⁻¹ hdet
    ((congrArg Subtype.val hX).trans (GS.UnitaryManifold.mul_inv A hdet).symm)
  exact he ▸ X.property

theorem cayley_mem_sharedMatrixSpace (hb : 0 < b) (hbn : b ∣ n)
    (hA : A ∈ sharedMatrixSpace 𝕂 b τ) (ha : admissible A) : cayley A ∈ sharedMatrixSpace 𝕂 b τ :=
  mul_mem_sharedMatrixSpace hb hbn ((sharedMatrixSpace 𝕂 b τ).sub_mem (one_mem_sharedMatrixSpace 𝕂 b τ) hA)
    (sharedMatrixSpace_inverse hb hbn ((sharedMatrixSpace 𝕂 b τ).add_mem (one_mem_sharedMatrixSpace 𝕂 b τ) hA) ha)

theorem cayley_shared (hb : 0 < b) (hbn : b ∣ n) (hC : C ∈ sharedSkewSpace 𝕂 b τ) :
    KSharedFactor b τ (cayley C) :=
  let ha := admissible_of_isSkew C hC.2.1
  let hm := cayley_mem_sharedMatrixSpace hb hbn ⟨hC.1, hC.2.2⟩ ha
  ⟨hm.1, cayley_unitary C hC.2.1 ha, hm.2⟩

theorem cayley_sharedSkew (hb : 0 < b) (hbn : b ∣ n) (hA : KSharedFactor b τ A) (ha : admissible A) :
    cayley A ∈ sharedSkewSpace 𝕂 b τ :=
  let hm := cayley_mem_sharedMatrixSpace hb hbn ⟨hA.1, hA.2.2⟩ ha
  ⟨hm.1, cayley_isSkew A hA.2.1 ha, hm.2⟩

theorem shared_factor_conjTranspose (hA : KSharedFactor b τ A) : KSharedFactor b τ Aᴴ :=
  ⟨hA.1.conjTranspose, hA.2.1.conjTranspose, hA.2.2.conjTranspose⟩

theorem shared_factor_mul (hb : 0 < b) (hbn : b ∣ n)
    (hA : KSharedFactor b τ A) (hB : KSharedFactor b τ B) : KSharedFactor b τ (A * B) :=
  ⟨hA.1.mul hB.1, hA.2.1.mul hB.2.1, KTiedEntries.mul hb hbn hA.1 hB.1 hA.2.2 hB.2.2⟩

theorem sharedSkew_conjugate (hb : 0 < b) (hbn : b ∣ n)
    (hA : KSharedFactor b τ A) (hC : C ∈ sharedSkewSpace 𝕂 b τ) :
    A * C * Aᴴ ∈ sharedSkewSpace 𝕂 b τ := by
  have hm := mul_mem_sharedMatrixSpace hb hbn
    (mul_mem_sharedMatrixSpace hb hbn ⟨hA.1, hA.2.2⟩ ⟨hC.1, hC.2.2⟩)
    ⟨hA.1.conjTranspose, hA.2.2.conjTranspose⟩
  refine ⟨hm.1, ?_, hm.2⟩
  have hskew : Cᴴ = -C := hC.2.1
  simp only [IsSkewHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hskew,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

theorem sharedSkew_conjugate_conjTranspose (hb : 0 < b) (hbn : b ∣ n)
    (hA : KSharedFactor b τ A) (hC : C ∈ sharedSkewSpace 𝕂 b τ) :
    Aᴴ * C * A ∈ sharedSkewSpace 𝕂 b τ := by
  simpa using sharedSkew_conjugate hb hbn (shared_factor_conjTranspose hA) hC

structure Pattern (𝕂 : Type) (n : ℕ) where
  size : ℕ
  positive : 0 < size
  divides : size ∣ n
  label : ℕ → ℕ

namespace Pattern
def block (s : Pattern 𝕂 n) (i : Fin n) : ℕ := i.val / s.size

def subgroup (s : Pattern 𝕂 n) : Subgroup (GS.UnitaryManifold.KBlockU 𝕂 s.block) where
  carrier := {A | KTiedEntries s.size s.label A.val}
  one_mem' := KTiedEntries.one s.size s.label
  mul_mem' {A B} hA hB := KTiedEntries.mul s.positive s.divides A.property.1 B.property.1 hA hB
  inv_mem' {_} hA := hA.conjTranspose

theorem subgroup_isClosed (s : Pattern 𝕂 n) :
    IsClosed (s.subgroup : Set (GS.UnitaryManifold.KBlockU 𝕂 s.block)) :=
  (isClosed_tiedEntries s.size s.label).preimage continuous_subtype_val
end Pattern

abbrev Factor (s : Pattern 𝕂 n) := ↥s.subgroup
abbrev Generator (s : Pattern 𝕂 n) := ↥(sharedSkewSpace 𝕂 (n := n) s.size s.label)

namespace Factor
variable {s : Pattern 𝕂 n}
def matrix (A : Factor s) : SMat 𝕂 n := A.val.val
@[simp] theorem matrix_one : matrix (1 : Factor s) = 1 := rfl
@[simp] theorem matrix_mul (A B : Factor s) : matrix (A * B) = matrix A * matrix B := rfl
@[simp] theorem matrix_inv (A : Factor s) : matrix A⁻¹ = (matrix A)ᴴ := rfl
theorem matrix_shared (A : Factor s) : KSharedFactor s.size s.label (matrix A) :=
  ⟨A.val.property.1, A.val.property.2, A.property⟩
theorem matrix_unitary (A : Factor s) : GS.KUnitary (matrix A) := A.val.property.2
theorem matrix_injective : Function.Injective (matrix : Factor s → SMat 𝕂 n) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)
theorem continuous_matrix : Continuous (matrix : Factor s → SMat 𝕂 n) :=
  continuous_subtype_val.comp continuous_subtype_val
def ofMatrix (A : SMat 𝕂 n) (hA : KSharedFactor s.size s.label A) : Factor s :=
  ⟨⟨A, hA.1, hA.2.1⟩, hA.2.2⟩
@[simp] theorem matrix_ofMatrix (A : SMat 𝕂 n) (hA : KSharedFactor s.size s.label A) :
    matrix (ofMatrix A hA) = A := rfl
end Factor

instance factorCompactSpace (s : Pattern 𝕂 n) : CompactSpace (Factor s) :=
  isCompact_iff_compactSpace.mp s.subgroup_isClosed.isCompact

abbrev Factors (right left : Pattern 𝕂 n) := Factor left × Factor right

section OrbitAndProjection
variable {right left : Pattern 𝕂 n}

def KInSharedA2 (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P X : SMat 𝕂 n) : Prop :=
  ∃ L R : SMat 𝕂 n, KSharedFactor b₂ τ₂ L ∧ KSharedFactor b₁ τ₁ R ∧ X = GS.UnitaryGeometry.kProduct2 L P R

instance factorsMulAction (right left : Pattern 𝕂 n) : MulAction (Factors right left) (SMat 𝕂 n) where
  smul g X := Factor.matrix g.1 * X * (Factor.matrix g.2)ᴴ
  one_smul X := by change (1 : SMat 𝕂 n) * X * (1 : SMat 𝕂 n)ᴴ = X; simp
  mul_smul g h X := by
    change (Factor.matrix g.1 * Factor.matrix h.1) * X * (Factor.matrix g.2 * Factor.matrix h.2)ᴴ =
      Factor.matrix g.1 * (Factor.matrix h.1 * X * (Factor.matrix h.2)ᴴ) * (Factor.matrix g.2)ᴴ
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

@[simp] theorem action_apply (g : Factors right left) (X : SMat 𝕂 n) :
    g • X = Factor.matrix g.1 * X * (Factor.matrix g.2)ᴴ := rfl

instance factorsContinuousSMul (right left : Pattern 𝕂 n) : ContinuousSMul (Factors right left) (SMat 𝕂 n) where
  continuous_smul := GS.UnitaryManifold.continuous_matrix_product
    (GS.UnitaryManifold.continuous_matrix_product
      (Factor.continuous_matrix.comp (continuous_fst.comp continuous_fst)) continuous_snd)
    (GS.UnitaryManifold.continuous_matrix_conjTranspose
      (Factor.continuous_matrix.comp (continuous_snd.comp continuous_fst)))

abbrev MatrixOrbit (right left : Pattern 𝕂 n) (P : SMat 𝕂 n) := ↥(MulAction.orbit (Factors right left) P)

theorem orbit_set_eq_inShared (P : SMat 𝕂 n) :
    MulAction.orbit (Factors right left) P = {X | KInSharedA2 right.size left.size right.label left.label P X} := by
  ext X; constructor
  · rintro ⟨g, hg⟩
    exact ⟨Factor.matrix g.1, (Factor.matrix g.2)ᴴ, Factor.matrix_shared g.1,
      shared_factor_conjTranspose (Factor.matrix_shared g.2), hg.symm⟩
  · rintro ⟨L, R, hL, hR, hX⟩
    refine ⟨(Factor.ofMatrix L hL, Factor.ofMatrix Rᴴ (shared_factor_conjTranspose hR)), ?_⟩
    simpa [GS.UnitaryGeometry.kProduct2] using hX.symm

def orbitMapToOrbit (right left : Pattern 𝕂 n) (P : SMat 𝕂 n) :
    Factors right left → MatrixOrbit right left P := fun g => ⟨g • P, ⟨g, rfl⟩⟩

theorem orbitMapToOrbit_isOpenMap (P : SMat 𝕂 n) : IsOpenMap (orbitMapToOrbit right left P) := by
  let π := orbitMapToOrbit right left P
  have hcont : Continuous π := (continuous_id.smul continuous_const).subtype_mk _
  have hsurj : Function.Surjective π := fun ⟨X, g, hg⟩ => ⟨g, Subtype.ext hg⟩
  intro s hs
  have hsat : π ⁻¹' (π '' s) =
      ⋃ h : MulAction.stabilizer (Factors right left) P, (fun g => g * h.val) ⁻¹' s := by
    ext g; constructor
    · rintro ⟨h, hh, he⟩
      have hf : (g⁻¹ * h) • P = P := by
        rw [mul_smul, ← show g • P = h • P from (congrArg Subtype.val he).symm, inv_smul_smul]
      exact Set.mem_iUnion.mpr ⟨⟨g⁻¹ * h, hf⟩, by simpa [mul_inv_cancel_left] using hh⟩
    · intro hg
      obtain ⟨h, hh⟩ := Set.mem_iUnion.mp hg
      exact ⟨g * h.val, hh, Subtype.ext (by change (g * h.val) • P = g • P; rw [mul_smul, show h.val • P = P from h.property])⟩
  have ho : IsOpen (π ⁻¹' (π '' s)) := hsat ▸ isOpen_iUnion fun _ => hs.preimage (continuous_id.mul continuous_const)
  have he : (π '' s)ᶜ = π '' (π ⁻¹' (π '' s)ᶜ) := (Set.image_preimage_eq _ hsurj).symm
  have hc : IsClosed (π '' s)ᶜ := he ▸ ((by simpa using ho.isClosed_compl : IsClosed _).isCompact.image hcont).isClosed
  simpa using hc.isOpen_compl

theorem action_cFrobInner (g : Factors right left) (X Y : SMat 𝕂 n) :
    cFrobInner (g • X) (g • Y) = cFrobInner X Y :=
  GS.UnitaryManifold.action_cFrobInner (g.1.val, g.2.val) X Y

def actionLinearEquiv (g : Factors right left) : SMat 𝕂 n ≃ₗ[ℝ] SMat 𝕂 n :=
  GS.UnitaryManifold.actionLinearEquiv (g.1.val, g.2.val)

abbrev PairGenerator (right left : Pattern 𝕂 n) := Generator left × Generator right

def pointMap (right left : Pattern 𝕂 n) (X : SMat 𝕂 n) : PairGenerator right left →ₗ[ℝ] SMat 𝕂 n where
  toFun v := v.1.val * X + X * v.2.val
  map_add' v w := by simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Matrix.add_mul, Matrix.mul_add]; abel
  map_smul' a v := by simp [Matrix.smul_mul, Matrix.mul_smul, smul_add]

def pointDirections (right left : Pattern 𝕂 n) (X : SMat 𝕂 n) : Submodule ℝ (SMat 𝕂 n) :=
  LinearMap.range (pointMap right left X)

theorem mem_pointDirections_iff (X Y : SMat 𝕂 n) :
    Y ∈ pointDirections right left X ↔
      ∃ A ∈ sharedSkewSpace 𝕂 left.size left.label,
        ∃ B ∈ sharedSkewSpace 𝕂 right.size right.label, Y = A * X + X * B :=
  ⟨fun ⟨⟨A, B⟩, h⟩ => ⟨A.val, A.property, B.val, B.property, h.symm⟩,
   fun ⟨A, hA, B, hB, h⟩ => ⟨(⟨A, hA⟩, ⟨B, hB⟩), h.symm⟩⟩

theorem sharedDirection_iff_pointDirections (P L R Y : SMat 𝕂 n)
    (hL : KSharedFactor left.size left.label L) (hR : KSharedFactor right.size right.label R) :
    (∃ C ∈ sharedSkewSpace 𝕂 left.size left.label, ∃ Ω ∈ sharedSkewSpace 𝕂 right.size right.label,
      Y = L * C * P * R + L * P * Ω * R) ↔
    Y ∈ pointDirections right left (GS.UnitaryGeometry.kProduct2 L P R) := by
  rw [mem_pointDirections_iff]; constructor
  · rintro ⟨C, hC, Ω, hΩ, rfl⟩
    refine ⟨L * C * Lᴴ, sharedSkew_conjugate left.positive left.divides hL hC,
      Rᴴ * Ω * R, sharedSkew_conjugate_conjTranspose right.positive right.divides hR hΩ, ?_⟩
    have hl : (L * C * Lᴴ) * (L * P * R) = L * C * P * R := by
      calc (L * C * Lᴴ) * (L * P * R) = L * C * (Lᴴ * L) * P * R := by simp [Matrix.mul_assoc]
        _ = L * C * P * R := by rw [hL.2.1.1, Matrix.mul_one]
    have hr : (L * P * R) * (Rᴴ * Ω * R) = L * P * Ω * R := by
      calc (L * P * R) * (Rᴴ * Ω * R) = L * P * (R * Rᴴ) * Ω * R := by simp [Matrix.mul_assoc]
        _ = L * P * Ω * R := by rw [hR.2.1.2, Matrix.mul_one]
    simp [GS.UnitaryGeometry.kProduct2, hl, hr]
  · rintro ⟨A, hA, B, hB, rfl⟩
    refine ⟨Lᴴ * A * L, sharedSkew_conjugate_conjTranspose left.positive left.divides hL hA,
      R * B * Rᴴ, sharedSkew_conjugate right.positive right.divides hR hB, ?_⟩
    have hl : L * (Lᴴ * A * L) * P * R = A * (L * P * R) := by
      calc L * (Lᴴ * A * L) * P * R = (L * Lᴴ) * A * (L * P * R) := by simp [Matrix.mul_assoc]
        _ = A * (L * P * R) := by rw [hL.2.1.2, Matrix.one_mul]
    have hr : L * P * (R * B * Rᴴ) * R = (L * P * R) * B := by
      calc L * P * (R * B * Rᴴ) * R = (L * P * R) * B * (Rᴴ * R) := by simp [Matrix.mul_assoc]
        _ = (L * P * R) * B := by rw [hR.2.1.1, Matrix.mul_one]
    simp [GS.UnitaryGeometry.kProduct2, hl, hr]

theorem action_mem_pointDirections (g : Factors right left) (X Y : SMat 𝕂 n)
    (hY : Y ∈ pointDirections right left X) : g • Y ∈ pointDirections right left (g • X) := by
  obtain ⟨A, hA, B, hB, rfl⟩ := (mem_pointDirections_iff X Y).mp hY
  let L := Factor.matrix g.1; let R := Factor.matrix g.2
  have hL := Factor.matrix_shared g.1; have hR := Factor.matrix_shared g.2
  refine (mem_pointDirections_iff _ _).mpr ⟨L * A * Lᴴ, sharedSkew_conjugate left.positive left.divides hL hA,
    R * B * Rᴴ, sharedSkew_conjugate right.positive right.divides hR hB, ?_⟩
  have hl : (L * A * Lᴴ) * (L * X * Rᴴ) = L * (A * X) * Rᴴ := by
    calc (L * A * Lᴴ) * (L * X * Rᴴ) = L * A * (Lᴴ * L) * X * Rᴴ := by simp [Matrix.mul_assoc]
      _ = L * (A * X) * Rᴴ := by rw [hL.2.1.1]; simp [Matrix.mul_assoc]
  have hr : (L * X * Rᴴ) * (R * B * Rᴴ) = L * (X * B) * Rᴴ := by
    calc (L * X * Rᴴ) * (R * B * Rᴴ) = L * X * (Rᴴ * R) * B * Rᴴ := by simp [Matrix.mul_assoc]
      _ = L * (X * B) * Rᴴ := by rw [hR.2.1.1]; simp [Matrix.mul_assoc]
  change L * (A * X + X * B) * Rᴴ = (L * A * Lᴴ) * (L * X * Rᴴ) + (L * X * Rᴴ) * (R * B * Rᴴ)
  rw [hl, hr, Matrix.mul_add, Matrix.add_mul]

def pointProjection (right left : Pattern 𝕂 n) (X : SMat 𝕂 n) : SMat 𝕂 n →L[ℝ] SMat 𝕂 n :=
  cFrobProjection (pointDirections right left X)

theorem pointProjection_mem (X Z : SMat 𝕂 n) : pointProjection right left X Z ∈ pointDirections right left X :=
  cFrobProjection_mem _ _

theorem pointProjection_of_mem (X Y : SMat 𝕂 n) (hY : Y ∈ pointDirections right left X) :
    pointProjection right left X Y = Y := cFrobProjection_of_mem _ _ hY

theorem pointProjection_normal (X Z Y : SMat 𝕂 n) (hY : Y ∈ pointDirections right left X) :
    cFrobInner (Z - pointProjection right left X Z) Y = 0 := cFrobProjection_normal _ _ _ hY

theorem pointProjection_self_adjoint (X Z Y : SMat 𝕂 n) :
    cFrobInner (pointProjection right left X Z) Y = cFrobInner Z (pointProjection right left X Y) :=
  cFrobProjection_self_adjoint _ _ _

@[simp] theorem pointProjection_idempotent (X Z : SMat 𝕂 n) :
    pointProjection right left X (pointProjection right left X Z) = pointProjection right left X Z :=
  pointProjection_of_mem X _ (pointProjection_mem X Z)

theorem pointProjection_equivariant (g : Factors right left) (X Z : SMat 𝕂 n) :
    pointProjection right left (g • X) (g • Z) = g • pointProjection right left X Z := by
  refine cFrobProjection_unique_normal (pointDirections right left (g • X)) (g • Z) _
    (action_mem_pointDirections g X _ (pointProjection_mem X Z)) fun Y hY => ?_
  have hback : g⁻¹ • Y ∈ pointDirections right left X := by
    simpa only [inv_smul_smul] using action_mem_pointDirections g⁻¹ (g • X) Y hY
  have he := action_cFrobInner g (Z - pointProjection right left X Z) (g⁻¹ • Y)
  rw [show g • (Z - pointProjection right left X Z) = g • Z - g • pointProjection right left X Z from
    (actionLinearEquiv g).map_sub _ _, smul_inv_smul] at he
  rw [he]; exact pointProjection_normal X Z _ hback

end OrbitAndProjection

def TiedEntries {n : ℕ} (b : ℕ) (τ : ℕ → ℕ) (A : GS.CMat n) : Prop :=
  ∀ i j i' j' : Fin n,
    i.val / b = j.val / b → i'.val / b = j'.val / b →
    τ (i.val / b) = τ (i'.val / b) →
    i.val % b = i'.val % b → j.val % b = j'.val % b → A i j = A i' j'

def SharedUnitaryFactor {n : ℕ} (b : ℕ) (τ : ℕ → ℕ) (A : GS.CMat n) : Prop :=
  GS.UnitaryGeometry.CSupported (fun i => i.val / b) A ∧ GS.Unitary A ∧ TiedEntries b τ A

def InSharedA2Unitary {n : ℕ} (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P X : GS.CMat n) : Prop :=
  ∃ L R, SharedUnitaryFactor b₂ τ₂ L ∧ SharedUnitaryFactor b₁ τ₁ R ∧ X = GS.UnitaryGeometry.product2 L P R

end GS.UnitarySharing
