module

public import GS.Continuation.ExponentialCurves
public import GS.Unitary.Factorization
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Topology.MetricSpace.ProperSpace.Real

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions GS.Continuation InnerProductSpace Filter Set
open scoped BigOperators Topology ComplexOrder

namespace GS.SharedGeometry

abbrev KMat (𝕂 : Type) (n : ℕ) := Matrix (Fin n) (Fin n) 𝕂
def KSupported {𝕂 : Type} [Zero 𝕂] {n : ℕ} (block : Fin n → ℕ) (A : KMat 𝕂 n) : Prop :=
  ∀ i j, block i ≠ block j → A i j = 0
def KUnitary {𝕂 : Type} [RCLike 𝕂] {n : ℕ} (A : KMat 𝕂 n) : Prop := Aᴴ * A = 1 ∧ A * Aᴴ = 1
def KIsSkew {𝕂 : Type} [RCLike 𝕂] {n : ℕ} (A : KMat 𝕂 n) : Prop := Aᴴ = -A
def KTiedEntries {𝕂 : Type} {n : ℕ} (b : ℕ) (τ : ℕ → ℕ) (A : KMat 𝕂 n) : Prop :=
  ∀ i j i' j' : Fin n,
    i.val / b = j.val / b → i'.val / b = j'.val / b →
    τ (i.val / b) = τ (i'.val / b) →
    i.val % b = i'.val % b → j.val % b = j'.val % b → A i j = A i' j'
def KSharedFactor {𝕂 : Type} [RCLike 𝕂] {n : ℕ} (b : ℕ) (τ : ℕ → ℕ) (A : KMat 𝕂 n) : Prop :=
  KSupported (fun i => i.val / b) A ∧ KUnitary A ∧ KTiedEntries b τ A
def KInSharedA2 {𝕂 : Type} [RCLike 𝕂] {n : ℕ} (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P X : KMat 𝕂 n) : Prop :=
  ∃ L R, KSharedFactor b₂ τ₂ L ∧ KSharedFactor b₁ τ₁ R ∧ X = L * P * R
abbrev BlockK (𝕂 : Type) [RCLike 𝕂] {n : ℕ} (block : Fin n → ℕ) :=
  {A : KMat 𝕂 n // KSupported block A ∧ KUnitary A}

def kcayley {𝕂 : Type} [RCLike 𝕂] {n : ℕ} (A : KMat 𝕂 n) : KMat 𝕂 n := (1 - A) * (1 + A)⁻¹
def kadmissible {𝕂 : Type} [RCLike 𝕂] {n : ℕ} (A : KMat 𝕂 n) : Prop := (1 + A).det ≠ 0
def kunitCayley {𝕂 : Type} [RCLike 𝕂] {n : ℕ} (A : KMat 𝕂 n) : KMat 𝕂 n := kcayley ((-1 / 2 : ℝ) • A)
def kproduct2 {𝕂 : Type} [RCLike 𝕂] {n : ℕ} (B₂ P B₁ : KMat 𝕂 n) : KMat 𝕂 n := B₂ * P * B₁
def ktangentParam {𝕂 : Type} [RCLike 𝕂] {n : ℕ} (B₂ P B₁ C Ω : KMat 𝕂 n) : KMat 𝕂 n :=
  B₂ * C * P * B₁ + B₂ * P * Ω * B₁

variable {𝕂 : Type} [RCLike 𝕂] {n b : ℕ} {τ : ℕ → ℕ} {A B C : KMat 𝕂 n}

theorem KUnitary.conjTranspose (hA : KUnitary A) : KUnitary Aᴴ := by
  simpa [KUnitary] using hA.symm

theorem KUnitary.mul (hA : KUnitary A) (hB : KUnitary B) : KUnitary (A * B) :=
  ⟨by calc (A * B)ᴴ * (A * B) = Bᴴ * (Aᴴ * A) * B := by simp [Matrix.mul_assoc]
        _ = 1 := by rw [hA.1, Matrix.mul_one, hB.1],
   by calc (A * B) * (A * B)ᴴ = A * (B * Bᴴ) * Aᴴ := by simp [Matrix.mul_assoc]
        _ = 1 := by rw [hB.2, Matrix.mul_one, hA.2]⟩

theorem KSupported.one {block : Fin n → ℕ} : KSupported block (1 : KMat 𝕂 n) :=
  fun i j h => by simp [show i ≠ j from fun he => h (he ▸ rfl)]

theorem KSupported.add {block : Fin n → ℕ} (hA : KSupported block A) (hB : KSupported block B) :
    KSupported block (A + B) := fun i j h => by simp [hA i j h, hB i j h]

theorem KSupported.mul {block : Fin n → ℕ} (hA : KSupported block A) (hB : KSupported block B) :
    KSupported block (A * B) := by
  intro i j hij; rw [Matrix.mul_apply]; apply Finset.sum_eq_zero; intro k _
  by_cases h : block i = block k
  · rw [hB k j (h ▸ hij), mul_zero]
  · rw [hA i k h, zero_mul]

theorem KSupported.conjTranspose {block : Fin n → ℕ} (hA : KSupported block A) :
    KSupported block Aᴴ := fun i j h => by simp [Matrix.conjTranspose_apply, hA j i h.symm]

theorem kisSkew_smul (a : ℝ) {A : KMat 𝕂 n} (hA : KIsSkew A) : KIsSkew (a • A) := by
  change (a • A)ᴴ = -(a • A)
  rw [Matrix.conjTranspose_smul, star_trivial, hA, smul_neg]

def ksharedSkewSpace (b : ℕ) (τ : ℕ → ℕ) : Submodule ℝ (KMat 𝕂 n) where
  carrier := {A | KSupported (fun i => i.val / b) A ∧ KIsSkew A ∧ KTiedEntries b τ A}
  zero_mem' := ⟨fun _ _ _ => rfl, by simp [KIsSkew], fun _ _ _ _ _ _ _ _ _ => rfl⟩
  add_mem' := fun hA hB =>
    ⟨hA.1.add hB.1,
     by change (_ + _)ᴴ = _; rw [Matrix.conjTranspose_add, hA.2.1, hB.2.1, neg_add],
     fun i j i' j' h1 h2 h3 h4 h5 => by simp [hA.2.2 i j i' j' h1 h2 h3 h4 h5, hB.2.2 i j i' j' h1 h2 h3 h4 h5]⟩
  smul_mem' := fun a _ hA =>
    ⟨fun i j h => by simp [hA.1 i j h], kisSkew_smul a hA.2.1,
     fun i j i' j' h1 h2 h3 h4 h5 => by simp [hA.2.2 i j i' j' h1 h2 h3 h4 h5]⟩

def KSharedDirection (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P L R Y : KMat 𝕂 n) : Prop :=
  ∃ C ∈ ksharedSkewSpace b₂ τ₂, ∃ Ω ∈ ksharedSkewSpace b₁ τ₁,
    Y = L * C * P * R + L * P * Ω * R

theorem TiedEntries_one (b : ℕ) (τ : ℕ → ℕ) : KTiedEntries b τ (1 : KMat 𝕂 n) := by
  intro i j i' j' hij hij' _ hi hj
  have he : i = j ↔ i' = j' := by
    constructor
    · intro h; subst j; apply Fin.ext
      have hm : i'.val % b = j'.val % b := hi.symm.trans hj
      have hdi := Nat.mod_add_div i'.val b; have hdj := Nat.mod_add_div j'.val b
      rw [hm, hij'] at hdi; omega
    · intro h; subst j'; apply Fin.ext
      have hm : i.val % b = j.val % b := hi.trans hj.symm
      have hdi := Nat.mod_add_div i.val b; have hdj := Nat.mod_add_div j.val b
      rw [hm, hij] at hdi; omega
  simp only [Matrix.one_apply, he]

theorem TiedEntries_conjTranspose (hA : KTiedEntries b τ A) : KTiedEntries b τ Aᴴ :=
  fun i j i' j' h h' hτ hi hj => congrArg star (hA j i j' i' h.symm h'.symm (by simpa only [← h, ← h'] using hτ) hj hi)

def localBlockIndex (hb : 0 < b) (hbn : b ∣ n) (i : Fin n) (k : Fin b) : Fin n :=
  ⟨i.val / b * b + k.val, by
    have hin : i.val / b < n / b := (Nat.div_lt_iff_lt_mul hb).mpr (by
      simpa only [Nat.div_mul_cancel hbn] using i.isLt)
    calc i.val / b * b + k.val < i.val / b * b + b := Nat.add_lt_add_left k.isLt _
      _ = (i.val / b + 1) * b := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ n / b * b := Nat.mul_le_mul_right b hin
      _ = n := Nat.div_mul_cancel hbn⟩

@[simp] theorem localBlockIndex_div (hb : 0 < b) (hbn : b ∣ n)
    (i : Fin n) (k : Fin b) : (localBlockIndex hb hbn i k).val / b = i.val / b := by
  change (i.val / b * b + k.val) / b = i.val / b
  rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ hb,
    Nat.div_eq_of_lt k.isLt, Nat.zero_add]

@[simp] theorem localBlockIndex_mod (hb : 0 < b) (hbn : b ∣ n)
    (i : Fin n) (k : Fin b) : (localBlockIndex hb hbn i k).val % b = k.val := by
  simp [localBlockIndex, Nat.add_mod, Nat.mod_eq_of_lt k.isLt]

theorem mul_apply_localBlockIndex (hb : 0 < b) (hbn : b ∣ n)
    (hA : KSupported (fun i => i.val / b) A) (i j : Fin n) :
    (A * B) i j = ∑ k : Fin b,
      A i (localBlockIndex hb hbn i k) * B (localBlockIndex hb hbn i k) j := by
  classical
  rw [Matrix.mul_apply]
  let s : Finset (Fin n) := Finset.univ.filter (fun k => k.val / b = i.val / b)
  have hrestrict : (∑ k : Fin n, A i k * B k j) = ∑ k ∈ s, A i k * B k j := by
    symm; apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k _ hk
    rw [hA i k (by simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, eq_comm] using hk), zero_mul]
  rw [hrestrict]
  apply Finset.sum_bij (fun k _ => (⟨k.val % b, Nat.mod_lt _ hb⟩ : Fin b))
  · intro _ _; exact Finset.mem_univ _
  · intro k hk l hl he
    have hk' : k.val / b = i.val / b := (Finset.mem_filter.mp hk).2
    have hl' : l.val / b = i.val / b := (Finset.mem_filter.mp hl).2
    have he' : k.val % b = l.val % b := congrArg Fin.val he
    apply Fin.ext
    have hkd := Nat.mod_add_div k.val b; have hld := Nat.mod_add_div l.val b
    rw [hk', he'] at hkd; rw [hl'] at hld; omega
  · intro k _
    exact ⟨localBlockIndex hb hbn i k, by simp [s], Fin.ext (localBlockIndex_mod hb hbn i k)⟩
  · intro k hk
    have hk' : k.val / b = i.val / b := (Finset.mem_filter.mp hk).2
    have he : localBlockIndex hb hbn i ⟨k.val % b, Nat.mod_lt _ hb⟩ = k := by
      apply Fin.ext; simp only [localBlockIndex, ← hk']; exact Nat.div_add_mod' _ _
    rw [he]

theorem TiedEntries_mul (hb : 0 < b) (hbn : b ∣ n)
    (hAs : KSupported (fun i => i.val / b) A) (_hBs : KSupported (fun i => i.val / b) B)
    (hA : KTiedEntries b τ A) (hB : KTiedEntries b τ B) :
    KTiedEntries b τ (A * B) := by
  intro i j i' j' hij hij' hτ hi hj
  rw [mul_apply_localBlockIndex hb hbn hAs, mul_apply_localBlockIndex hb hbn hAs]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hl : A i (localBlockIndex hb hbn i k) = A i' (localBlockIndex hb hbn i' k) :=
    hA _ _ _ _ (by simp) (by simp) hτ hi (by simp)
  have hr : B (localBlockIndex hb hbn i k) j = B (localBlockIndex hb hbn i' k) j' :=
    hB _ _ _ _ (by simpa using hij) (by simpa using hij') (by simpa using hτ) (by simp) hj
  rw [hl, hr]

theorem isClosed_tiedEntries (b : ℕ) (τ : ℕ → ℕ) :
    IsClosed {A : KMat 𝕂 n | KTiedEntries b τ A} := by
  simp only [KTiedEntries, Set.setOf_forall]
  exact isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
    isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
        isClosed_eq (by fun_prop) (by fun_prop)

def ksharedMatrixSpace (b : ℕ) (τ : ℕ → ℕ) : Submodule ℝ (KMat 𝕂 n) where
  carrier := {A | KSupported (fun i => i.val / b) A ∧ KTiedEntries b τ A}
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ => rfl⟩
  add_mem' := fun hA hB => ⟨hA.1.add hB.1,
    fun i j i' j' h1 h2 h3 h4 h5 => by simp [hA.2 i j i' j' h1 h2 h3 h4 h5, hB.2 i j i' j' h1 h2 h3 h4 h5]⟩
  smul_mem' := fun a _ hA => ⟨fun i j h => by simp [hA.1 i j h],
    fun i j i' j' h1 h2 h3 h4 h5 => by simp [hA.2 i j i' j' h1 h2 h3 h4 h5]⟩

theorem one_mem_ksharedMatrixSpace (b : ℕ) (τ : ℕ → ℕ) :
    (1 : KMat 𝕂 n) ∈ ksharedMatrixSpace b τ := ⟨KSupported.one, TiedEntries_one b τ⟩

theorem mul_mem_ksharedMatrixSpace (hb : 0 < b) (hbn : b ∣ n)
    (hA : A ∈ ksharedMatrixSpace b τ) (hB : B ∈ ksharedMatrixSpace b τ) :
    A * B ∈ ksharedMatrixSpace b τ :=
  ⟨hA.1.mul hB.1, TiedEntries_mul hb hbn hA.1 hB.1 hA.2 hB.2⟩

theorem cancel_left (A X Y : KMat 𝕂 n) (hA : A.det ≠ 0) (h : A * X = A * Y) : X = Y := by
  simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA), Matrix.one_mul]
    using congrArg (fun Z => A⁻¹ * Z) h

theorem cancel_right (A X Y : KMat 𝕂 n) (hA : A.det ≠ 0) (h : X * A = Y * A) : X = Y := by
  simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA), Matrix.mul_one]
    using congrArg (fun Z => Z * A⁻¹) h

theorem cancel_congruence (A X Y : KMat 𝕂 n) (hA : A.det ≠ 0) (h : Aᴴ * X * A = Aᴴ * Y * A) : X = Y :=
  cancel_left Aᴴ X Y (by simpa only [Matrix.det_conjTranspose, star_ne_zero] using hA)
    (cancel_right A (Aᴴ * X) (Aᴴ * Y) hA h)

instance kMatFiniteDimensional (n : ℕ) : FiniteDimensional ℝ (KMat 𝕂 n) :=
  Module.Finite.trans 𝕂 (KMat 𝕂 n)

theorem ksharedMatrixSpace_inverse (hb : 0 < b) (hbn : b ∣ n)
    (hA : A ∈ ksharedMatrixSpace b τ) (hdet : A.det ≠ 0) :
    A⁻¹ ∈ ksharedMatrixSpace b τ := by
  let S := ksharedMatrixSpace (𝕂 := 𝕂) (n := n) b τ
  let m : S →ₗ[ℝ] S :=
    { toFun := fun X => ⟨A * X.val, mul_mem_ksharedMatrixSpace hb hbn hA X.property⟩
      map_add' := fun X Y => Subtype.ext (Matrix.mul_add A X.val Y.val)
      map_smul' := fun a X => Subtype.ext (Matrix.mul_smul A a X.val) }
  have hm : Function.Injective m := fun X Y h =>
    Subtype.ext (cancel_left A X.val Y.val hdet (congrArg Subtype.val h))
  obtain ⟨X, hX⟩ := (LinearMap.injective_iff_surjective.mp hm)
    (⟨1, one_mem_ksharedMatrixSpace b τ⟩ : S)
  have hAX : A * X.val = 1 := congrArg Subtype.val hX
  have he : X.val = A⁻¹ := by
    apply cancel_left A X.val A⁻¹ hdet
    rw [hAX, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hdet)]
  rw [← he]; exact X.property

theorem kcayley_mul (A : KMat 𝕂 n) (hA : kadmissible A) : kcayley A * (1 + A) = 1 - A := by
  simp only [kcayley, Matrix.mul_assoc, Matrix.nonsing_inv_mul (1 + A) (isUnit_iff_ne_zero.mpr hA), Matrix.mul_one]

theorem one_add_kcayley_mul (A : KMat 𝕂 n) (hA : kadmissible A) :
    (1 + kcayley A) * (1 + A) = (2 : ℝ) • (1 : KMat 𝕂 n) := by
  rw [Matrix.add_mul, Matrix.one_mul, kcayley_mul A hA, two_smul ℝ]; abel

theorem admissible_cayley (A : KMat 𝕂 n) (hA : kadmissible A) : kadmissible (kcayley A) := by
  have he : (1 + kcayley A) * ((1 / 2 : ℝ) • (1 + A)) = 1 := by
    rw [Matrix.mul_smul, one_add_kcayley_mul A hA, smul_smul]; norm_num
  exact Matrix.det_ne_zero_of_right_inverse he

theorem cayley_involutive (A : KMat 𝕂 n) (hA : kadmissible A) : kcayley (kcayley A) = A := by
  apply cancel_right (1 + kcayley A) _ _ (admissible_cayley A hA)
  rw [kcayley_mul (kcayley A) (admissible_cayley A hA)]
  apply cancel_right (1 + A) _ _ hA
  calc (1 - kcayley A) * (1 + A) = (1 + A) - (1 - A) := by rw [Matrix.sub_mul, Matrix.one_mul, kcayley_mul A hA]
    _ = A * ((2 : ℝ) • (1 : KMat 𝕂 n)) := by rw [two_smul ℝ]; noncomm_ring
    _ = A * (1 + kcayley A) * (1 + A) := by rw [Matrix.mul_assoc, one_add_kcayley_mul A hA]

theorem cayley_unitary (A : KMat 𝕂 n) (hs : KIsSkew A) (hA : kadmissible A) : KUnitary (kcayley A) := by
  suffices hh : (kcayley A)ᴴ * kcayley A = 1 from ⟨hh, mul_eq_one_comm.mp hh⟩
  apply cancel_congruence (1 + A) _ 1 hA
  have he := kcayley_mul A hA
  have ht : (1 + A)ᴴ * (kcayley A)ᴴ = (1 - A)ᴴ := by
    simpa only [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose he
  calc (1 + A)ᴴ * ((kcayley A)ᴴ * kcayley A) * (1 + A) =
      ((1 + A)ᴴ * (kcayley A)ᴴ) * (kcayley A * (1 + A)) := by noncomm_ring
    _ = (1 - A)ᴴ * (1 - A) := by rw [ht, he]
    _ = (1 + A)ᴴ * (1 : KMat 𝕂 n) * (1 + A) := by
      change Aᴴ = -A at hs
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one, hs]
      noncomm_ring

theorem cayley_isSkew (Q : KMat 𝕂 n) (hQ : KUnitary Q) (hd : kadmissible Q) : KIsSkew (kcayley Q) := by
  have he := kcayley_mul Q hd
  have ht : (1 + Q)ᴴ * (kcayley Q)ᴴ = (1 - Q)ᴴ := by
    simpa only [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose he
  apply eq_neg_of_add_eq_zero_left
  apply cancel_congruence (1 + Q) _ 0 hd
  calc (1 + Q)ᴴ * ((kcayley Q)ᴴ + kcayley Q) * (1 + Q) =
      ((1 + Q)ᴴ * (kcayley Q)ᴴ) * (1 + Q) + (1 + Q)ᴴ * (kcayley Q * (1 + Q)) := by noncomm_ring
    _ = (1 - Q)ᴴ * (1 + Q) + (1 + Q)ᴴ * (1 - Q) := by rw [ht, he]
    _ = (2 : ℝ) • (1 - Qᴴ * Q) := by
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one, two_smul ℝ]
      noncomm_ring
    _ = (1 + Q)ᴴ * (0 : KMat 𝕂 n) * (1 + Q) := by rw [hQ.1]; simp

theorem cayley_intertwine (A B P : KMat 𝕂 n) (hA : kadmissible A) (hB : kadmissible B)
    (h : A * P = P * B) : kcayley A * P = P * kcayley B := by
  apply cancel_right (1 + B) _ _ hB
  have hp : P * (1 + B) = (1 + A) * P := by simp [Matrix.mul_add, Matrix.add_mul, h]
  calc kcayley A * P * (1 + B) = kcayley A * ((1 + A) * P) := by rw [Matrix.mul_assoc, hp]
    _ = (1 - A) * P := by rw [← Matrix.mul_assoc, kcayley_mul A hA]
    _ = P * (1 - B) := by simp [Matrix.sub_mul, Matrix.mul_sub, h]
    _ = P * kcayley B * (1 + B) := by rw [Matrix.mul_assoc, kcayley_mul B hB]

@[simp] theorem admissible_zero : kadmissible (0 : KMat 𝕂 n) := by simp [kadmissible]
@[simp] theorem cayley_zero : kcayley (0 : KMat 𝕂 n) = 1 := by simp [kcayley]
@[simp] theorem admissible_one : kadmissible (1 : KMat 𝕂 n) := by
  simpa only [cayley_zero] using admissible_cayley (0 : KMat 𝕂 n) admissible_zero

theorem admissible_of_isSkew (A : KMat 𝕂 n) (hA : KIsSkew A) : kadmissible A := by
  have hpos : (1 + Aᴴ * A).PosDef :=
    Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self A)
  have he : (1 - A) * (1 + A) = 1 + Aᴴ * A := by change Aᴴ = -A at hA; rw [hA]; noncomm_ring
  have hdet : ((1 - A) * (1 + A)).det ≠ 0 := by
    rw [he]; exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hpos.isUnit)
  rw [Matrix.det_mul] at hdet
  exact (mul_ne_zero_iff.mp hdet).2

theorem kcayley_mem_ksharedMatrixSpace (hb : 0 < b) (hbn : b ∣ n)
    (hA : A ∈ ksharedMatrixSpace b τ) (ha : kadmissible A) :
    kcayley A ∈ ksharedMatrixSpace b τ :=
  mul_mem_ksharedMatrixSpace hb hbn
    (Submodule.sub_mem _ (one_mem_ksharedMatrixSpace b τ) hA)
    (ksharedMatrixSpace_inverse hb hbn (Submodule.add_mem _ (one_mem_ksharedMatrixSpace b τ) hA) ha)

theorem cayley_shared (hb : 0 < b) (hbn : b ∣ n)
    (hC : C ∈ ksharedSkewSpace b τ) : KSharedFactor b τ (kcayley C) := by
  have ha := admissible_of_isSkew C hC.2.1
  have hm := kcayley_mem_ksharedMatrixSpace hb hbn ⟨hC.1, hC.2.2⟩ ha
  exact ⟨hm.1, cayley_unitary C hC.2.1 ha, hm.2⟩

theorem cayley_sharedSkew (hb : 0 < b) (hbn : b ∣ n)
    (hA : KSharedFactor b τ A) (ha : kadmissible A) :
    kcayley A ∈ ksharedSkewSpace b τ := by
  have hm := kcayley_mem_ksharedMatrixSpace hb hbn ⟨hA.1, hA.2.2⟩ ha
  exact ⟨hm.1, cayley_isSkew A hA.2.1 ha, hm.2⟩

theorem shared_factor_conjTranspose (hA : KSharedFactor b τ A) :
    KSharedFactor b τ Aᴴ :=
  ⟨hA.1.conjTranspose, hA.2.1.conjTranspose, TiedEntries_conjTranspose hA.2.2⟩

theorem shared_factor_mul (hb : 0 < b) (hbn : b ∣ n)
    (hA : KSharedFactor b τ A) (hB : KSharedFactor b τ B) :
    KSharedFactor b τ (A * B) :=
  ⟨hA.1.mul hB.1, hA.2.1.mul hB.2.1, TiedEntries_mul hb hbn hA.1 hB.1 hA.2.2 hB.2.2⟩

theorem sharedSkew_conjugate (hb : 0 < b) (hbn : b ∣ n)
    (hA : KSharedFactor b τ A) (hC : C ∈ ksharedSkewSpace b τ) :
    A * C * Aᴴ ∈ ksharedSkewSpace b τ := by
  have hm : A * C * Aᴴ ∈ ksharedMatrixSpace b τ :=
    mul_mem_ksharedMatrixSpace hb hbn
      (mul_mem_ksharedMatrixSpace hb hbn ⟨hA.1, hA.2.2⟩ ⟨hC.1, hC.2.2⟩)
      ⟨hA.1.conjTranspose, TiedEntries_conjTranspose hA.2.2⟩
  refine ⟨hm.1, ?_, hm.2⟩
  change (A * C * Aᴴ)ᴴ = -(A * C * Aᴴ)
  have hskew : Cᴴ = -C := hC.2.1
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hskew,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

theorem sharedSkew_conjugate_conjTranspose (hb : 0 < b) (hbn : b ∣ n)
    (hA : KSharedFactor b τ A) (hC : C ∈ ksharedSkewSpace b τ) :
    Aᴴ * C * A ∈ ksharedSkewSpace b τ := by
  simpa only [Matrix.conjTranspose_conjTranspose] using
    sharedSkew_conjugate hb hbn (shared_factor_conjTranspose hA) hC

theorem kcontinuous_matrix_product {X : Type*} [TopologicalSpace X]
    {A B : X → KMat 𝕂 n} (hA : Continuous A) (hB : Continuous B) :
    Continuous (fun x => A x * B x) := by
  apply continuous_pi; intro i; apply continuous_pi; intro j
  simp only [Matrix.mul_apply]
  exact continuous_finset_sum _ fun k _ =>
    ((continuous_apply k).comp ((continuous_apply i).comp hA)).mul
      ((continuous_apply j).comp ((continuous_apply k).comp hB))

theorem kcontinuous_matrix_conjTranspose {X : Type*} [TopologicalSpace X]
    {A : X → KMat 𝕂 n} (hA : Continuous A) :
    Continuous (fun x => (A x)ᴴ) := by
  apply continuous_pi; intro i; apply continuous_pi; intro j
  exact ((continuous_apply i).comp ((continuous_apply j).comp hA)).star

theorem ksmooth_matrix_product {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {A B : E → KMat 𝕂 n}
    (hA : ContDiff ℝ ⊤ A) (hB : ContDiff ℝ ⊤ B) :
    ContDiff ℝ ⊤ (fun x => A x * B x) := by
  rw [contDiff_pi]; intro i; rw [contDiff_pi]; intro j
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun k _ =>
    (contDiff_pi.mp (contDiff_pi.mp hA i) k).mul (contDiff_pi.mp (contDiff_pi.mp hB k) j)

theorem ksmooth_mul_at {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {A B : E → KMat 𝕂 n} {x : E}
    (hA : ContDiffAt ℝ ⊤ A x) (hB : ContDiffAt ℝ ⊤ B x) :
    ContDiffAt ℝ ⊤ (fun y => A y * B y) x := by
  rw [contDiffAt_pi]; intro i; rw [contDiffAt_pi]; intro j
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum fun k _ =>
    ((contDiffAt_pi.mp (contDiffAt_pi.mp hA i) k).mul (contDiffAt_pi.mp (contDiffAt_pi.mp hB k) j))

theorem ksmooth_conjTranspose_at {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {A : E → KMat 𝕂 n} {x : E}
    (hA : ContDiffAt ℝ ⊤ A x) :
    ContDiffAt ℝ ⊤ (fun y => (A y)ᴴ) x := by
  rw [contDiffAt_pi]; intro i; rw [contDiffAt_pi]; intro j
  exact ContinuousLinearMap.contDiff (starL' ℝ : 𝕂 ≃L[ℝ] 𝕂).toContinuousLinearMap
    |>.contDiffAt.comp x (contDiffAt_pi.mp (contDiffAt_pi.mp hA j) i)

theorem ksmooth_det : ContDiff ℝ ⊤ (fun A : KMat 𝕂 n => A.det) := by
  simp only [Matrix.det_apply']
  refine ContDiff.sum fun σ _ => ContDiff.mul contDiff_const (contDiff_prod fun i _ => ?_)
  exact (contDiff_apply ℝ 𝕂 i).comp (contDiff_apply ℝ (Fin n → 𝕂) (σ i))

theorem ksmooth_adjugate : ContDiff ℝ ⊤ (fun A : KMat 𝕂 n => A.adjugate) := by
  rw [contDiff_pi]; intro i; rw [contDiff_pi]; intro j
  simp only [Matrix.adjugate_apply]
  apply ksmooth_det.comp
  rw [contDiff_pi]; intro a; rw [contDiff_pi]; intro b
  by_cases ha : a = j
  · subst a; simp [Matrix.updateRow]; exact contDiff_const
  · simpa [Matrix.updateRow, Function.update_of_ne ha] using
      (contDiff_pi.mp (contDiff_pi.mp (contDiff_id : ContDiff ℝ ⊤ (id : KMat 𝕂 n → KMat 𝕂 n)) a) b)

theorem ksmooth_inverse_at (A : KMat 𝕂 n) (hA : A.det ≠ 0) :
    ContDiffAt ℝ ⊤ (fun B : KMat 𝕂 n => B⁻¹) A := by
  have h : ContDiffAt ℝ ⊤ (fun B : KMat 𝕂 n => B.det⁻¹ • B.adjugate) A := by
    rw [contDiffAt_pi]; intro i; rw [contDiffAt_pi]; intro j
    exact (ksmooth_det.contDiffAt.inv hA).mul
      (contDiffAt_pi.mp (contDiffAt_pi.mp ksmooth_adjugate.contDiffAt i) j)
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv] using h

theorem smooth_cayley_comp_at {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : E → KMat 𝕂 n} {x : E} (hA : ContDiffAt ℝ ⊤ A x) (hd : kadmissible (A x)) :
    ContDiffAt ℝ ⊤ (fun y => kcayley (A y)) x :=
  (ksmooth_mul_at (contDiffAt_const.sub contDiffAt_id)
    ((ksmooth_inverse_at (1 + A x) hd).comp (A x) (contDiffAt_const.add contDiffAt_id))).comp x hA

theorem admissible_open : IsOpen {A : KMat 𝕂 n | kadmissible A} :=
  isOpen_ne.preimage (ksmooth_det.continuous.comp (continuous_const.add continuous_id))

instance instBlockKGroup (block : Fin n → ℕ) : Group (BlockK 𝕂 block) where
  one := ⟨1, KSupported.one, by simp [KUnitary]⟩
  mul A B := ⟨A.val * B.val, A.property.1.mul B.property.1, A.property.2.mul B.property.2⟩
  inv A := ⟨A.valᴴ, A.property.1.conjTranspose, A.property.2.conjTranspose⟩
  mul_assoc A B C := Subtype.ext (Matrix.mul_assoc A.val B.val C.val)
  one_mul A := Subtype.ext (Matrix.one_mul A.val)
  mul_one A := Subtype.ext (Matrix.mul_one A.val)
  inv_mul_cancel A := Subtype.ext A.property.2.1

instance instBlockKTopologicalGroup (block : Fin n → ℕ) : IsTopologicalGroup (BlockK 𝕂 block) where
  continuous_mul := Continuous.subtype_mk
    (kcontinuous_matrix_product (continuous_subtype_val.comp continuous_fst)
      (continuous_subtype_val.comp continuous_snd)) _
  continuous_inv := Continuous.subtype_mk
    (kcontinuous_matrix_conjTranspose continuous_subtype_val) _

theorem kunitary_entry_bound {A : KMat 𝕂 n} (hA : KUnitary A) (i j : Fin n) :
    ‖A i j‖ ≤ 1 := by
  have hg := congrArg RCLike.re (congrFun (congrFun hA.1 j) j)
  have he : (∑ k : Fin n, ‖A k j‖ ^ 2) = 1 := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      ↓reduceIte, RCLike.one_re, map_sum] at hg
    rw [← hg]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hs : star (A k j) * A k j = (‖A k j‖ ^ 2 : 𝕂) := by
      rw [show star (A k j) = (starRingEnd 𝕂) (A k j) from congrFun RCLike.star_def _,
        RCLike.conj_mul]
    rw [hs]; norm_cast
  have hs : ‖A i j‖ ^ 2 ≤ 1 := by
    rw [← he]
    exact Finset.single_le_sum (fun k _ => sq_nonneg ‖A k j‖) (Finset.mem_univ i)
  nlinarith [norm_nonneg (A i j)]

instance instBlockKCompactSpace (block : Fin n → ℕ) : CompactSpace (BlockK 𝕂 block) := by
  apply isCompact_iff_compactSpace.mp
  have hc1 : IsClosed {A : KMat 𝕂 n | KSupported block A} := by
    simp only [KSupported, Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq ((continuous_apply j).comp (continuous_apply i)) continuous_const
  have hc2 : IsClosed {A : KMat 𝕂 n | KUnitary A} :=
    (isClosed_eq (kcontinuous_matrix_product (kcontinuous_matrix_conjTranspose continuous_id) continuous_id)
      continuous_const).inter
    (isClosed_eq (kcontinuous_matrix_product continuous_id (kcontinuous_matrix_conjTranspose continuous_id))
      continuous_const)
  have hb : IsCompact {A : KMat 𝕂 n | ∀ i j, A i j ∈ Metric.closedBall (0 : 𝕂) 1} :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => isCompact_closedBall (0 : 𝕂) 1
  exact hb.of_isClosed_subset (hc1.inter hc2) fun A hA i j => by
    simpa [Metric.mem_closedBall, dist_zero_right] using kunitary_entry_bound hA.2 i j

theorem khasDerivAt_matrix_conjTranspose {f : ℝ → KMat 𝕂 n} {u : KMat 𝕂 n}
    (hf : HasDerivAt f u 0) : HasDerivAt (fun t => (f t)ᴴ) uᴴ 0 := by
  rw [hasDerivAt_pi]; intro i; rw [hasDerivAt_pi]; intro j
  exact ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hf j)) i).star

theorem khasDerivAt_matrix_mul {f g : ℝ → KMat 𝕂 n} {u v : KMat 𝕂 n}
    (hf : HasDerivAt f u 0) (hg : HasDerivAt g v 0) :
    HasDerivAt (fun t => f t * g t) (u * g 0 + f 0 * v) 0 := by
  rw [hasDerivAt_pi]; intro i; rw [hasDerivAt_pi]; intro j
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  have hs := HasDerivAt.sum (u := Finset.univ) fun k _ =>
    ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hf i)) k).mul
      ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hg k)) j)
  simpa only [Finset.sum_apply, Finset.sum_fn, Pi.mul_apply, Pi.mul_def] using hs

theorem khasDerivAt_product2 (P : KMat 𝕂 n)
    {f g : ℝ → KMat 𝕂 n} {u v : KMat 𝕂 n}
    (hf : HasDerivAt f u 0) (hg : HasDerivAt g v 0) :
    HasDerivAt (fun t => kproduct2 (f t) P (g t)) (u * P * g 0 + f 0 * P * v) 0 := by
  simpa only [kproduct2, Matrix.mul_zero, add_zero] using
    khasDerivAt_matrix_mul (khasDerivAt_matrix_mul hf (hasDerivAt_const 0 P)) hg

theorem kcayley_line_derivative (A : KMat 𝕂 n) (hk : KIsSkew A) :
    HasDerivAt (fun t : ℝ => kcayley (t • A)) ((-2 : ℝ) • A) 0 := by
  let f : ℝ → KMat 𝕂 n := fun t => kcayley (t • A)
  have hsm : ContDiffAt ℝ ⊤ f 0 :=
    smooth_cayley_comp_at (contDiffAt_id.smul contDiffAt_const) (by simpa using admissible_zero)
  let V := deriv f 0
  have hd : HasDerivAt f V 0 := (hsm.differentiableAt (by simp)).hasDerivAt
  have hp : HasDerivAt (fun t : ℝ => (1 : KMat 𝕂 n) + t • A) A 0 := by
    simpa only [Pi.add_def, zero_add, id_eq, one_smul] using
      (hasDerivAt_const (0 : ℝ) (1 : KMat 𝕂 n)).add ((hasDerivAt_id (0 : ℝ)).smul_const A)
  have hm : HasDerivAt (fun t : ℝ => (1 : KMat 𝕂 n) - t • A) (-A) 0 := by
    simpa only [Pi.sub_def, zero_sub, id_eq, one_smul] using
      (hasDerivAt_const (0 : ℝ) (1 : KMat 𝕂 n)).sub ((hasDerivAt_id (0 : ℝ)).smul_const A)
  have he : (fun t : ℝ => f t * (1 + t • A)) = (fun t : ℝ => (1 : KMat 𝕂 n) - t • A) :=
    funext fun t => kcayley_mul _ (admissible_of_isSkew _ (kisSkew_smul t hk))
  have hz := khasDerivAt_matrix_mul hd hp
  rw [he] at hz
  have hv : V + A = -A := by simpa [f] using hz.unique hm
  have hv' : V = (-2 : ℝ) • A := by rw [eq_sub_of_add_eq hv, neg_smul, two_smul]; abel
  simpa only [f, hv'] using hd

theorem chartInv_line_hasDerivAt_zero {b : Fin n → ℕ} (Q : BlockK 𝕂 b)
    (v : {A : KMat 𝕂 n // KSupported b A ∧ KIsSkew A}) :
    HasDerivAt (fun t : ℝ => Q.val * kcayley (t • v.val)) ((-2 : ℝ) • (Q.val * v.val)) 0 := by
  simpa only [Matrix.zero_mul, zero_add, Matrix.mul_smul] using
    khasDerivAt_matrix_mul (hasDerivAt_const (0 : ℝ) Q.val) (kcayley_line_derivative v.val v.property.2)

@[simp] theorem unitCayley_zero : kunitCayley (0 : KMat 𝕂 n) = 1 := by simp [kunitCayley]

theorem unitCayley_smooth_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E → KMat 𝕂 n) (hs : ContDiff ℝ ⊤ A) (hk : ∀ x, KIsSkew (A x)) :
    ContDiff ℝ ⊤ (fun x => kunitCayley (A x)) :=
  contDiff_iff_contDiffAt.mpr fun x =>
    smooth_cayley_comp_at (hs.contDiffAt.const_smul (-1 / 2 : ℝ))
      (admissible_of_isSkew _ (kisSkew_smul _ (hk x)))

theorem unitCayley_line_derivative (A : KMat 𝕂 n) (hk : KIsSkew A) :
    HasDerivAt (fun t : ℝ => kunitCayley (t • A)) A 0 := by
  have hd := kcayley_line_derivative ((-1 / 2 : ℝ) • A) (kisSkew_smul _ hk)
  have hf : (fun t : ℝ => kunitCayley (t • A)) = (fun t : ℝ => kcayley (t • ((-1 / 2 : ℝ) • A))) := by
    funext t; unfold kunitCayley; rw [smul_comm]
  rw [hf]
  simpa only [smul_smul, show (-2 : ℝ) * (-1 / 2) = 1 by norm_num, one_smul] using hd

abbrev KFrobCoordinates (n : ℕ) := EuclideanSpace ℝ (Fin n × Fin n × Fin 2)

def encodeKFrob : KMat 𝕂 n →ₗ[ℝ] KFrobCoordinates n where
  toFun A := (WithLp.equiv 2 _).symm fun k =>
    if k.2.2 = 0 then RCLike.re (A k.1 k.2.1) else RCLike.im (A k.1 k.2.1)
  map_add' A B := by ext k; by_cases hk : k.2.2 = 0 <;> simp [hk]
  map_smul' a A := by ext k; by_cases hk : k.2.2 = 0 <;> simp [hk, Algebra.smul_def]

def decodeKFrob : KFrobCoordinates n →ₗ[ℝ] KMat 𝕂 n where
  toFun x i j := (x (i, j, 0) : 𝕂) + (x (i, j, 1) : 𝕂) * RCLike.I
  map_add' x y := by ext i j; simp only [Matrix.add_apply, PiLp.add_apply, map_add]; ring
  map_smul' a x := by ext i j; simp only [Matrix.smul_apply, PiLp.smul_apply, smul_eq_mul, Algebra.smul_def, map_mul, RingHom.id_apply]; ring

@[simp] theorem decode_encodeKFrob (A : KMat 𝕂 n) : decodeKFrob (encodeKFrob A) = A := by
  ext i j; exact RCLike.re_add_im (A i j)

theorem im_mul_I_im (z : 𝕂) : RCLike.im z * RCLike.im (RCLike.I : 𝕂) = RCLike.im z := by
  simpa only [map_add, RCLike.ofReal_im, RCLike.im_ofReal_mul, zero_add] using
    congrArg RCLike.im (RCLike.re_add_im z)

theorem inner_encode_decode_left (x : KFrobCoordinates n) (A : KMat 𝕂 n) :
    ⟪encodeKFrob (decodeKFrob (𝕂 := 𝕂) x), encodeKFrob A⟫_ℝ = ⟪x, encodeKFrob A⟫_ℝ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, encodeKFrob, decodeKFrob, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.star_apply, star_trivial, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.isValue]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change RCLike.re (A i j) * RCLike.re ((x (i, j, 0) : 𝕂) + (x (i, j, 1) : 𝕂) * RCLike.I) +
    RCLike.im (A i j) * RCLike.im ((x (i, j, 0) : 𝕂) + (x (i, j, 1) : 𝕂) * RCLike.I) =
    RCLike.re (A i j) * x (i, j, 0) + RCLike.im (A i j) * x (i, j, 1)
  simp only [map_add, RCLike.ofReal_re, RCLike.ofReal_im, RCLike.re_ofReal_mul,
    RCLike.im_ofReal_mul, RCLike.I_re, mul_zero, add_zero, zero_add]
  rw [← mul_assoc, mul_comm (RCLike.im (A i j)), mul_assoc, im_mul_I_im]

def kfrobInner (A B : KMat 𝕂 n) : ℝ := ⟪encodeKFrob A, encodeKFrob B⟫_ℝ
abbrev kfrobSq (A : KMat 𝕂 n) : ℝ := kfrobInner A A

theorem encodeKFrob_inner (A B : KMat 𝕂 n) : ⟪encodeKFrob A, encodeKFrob B⟫_ℝ = kfrobInner A B := rfl

theorem kfrobInner_eq_sum (A B : KMat 𝕂 n) :
    kfrobInner A B =
      ∑ i : Fin n, ∑ j : Fin n, (RCLike.re (A i j) * RCLike.re (B i j) + RCLike.im (A i j) * RCLike.im (B i j)) := by
  rw [kfrobInner, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, encodeKFrob, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.star_apply, star_trivial, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.isValue]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change RCLike.re (B i j) * RCLike.re (A i j) + RCLike.im (B i j) * RCLike.im (A i j) = _
  ring

theorem kfrobInner_eq_re_trace (A B : KMat 𝕂 n) :
    kfrobInner A B = RCLike.re (Matrix.trace (Aᴴ * B)) := by
  rw [kfrobInner_eq_sum]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, RCLike.mul_re]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by simp

theorem kfrobInner_comm (A B : KMat 𝕂 n) : kfrobInner A B = kfrobInner B A := real_inner_comm _ _
@[simp] theorem kfrobInner_zero_left (A : KMat 𝕂 n) : kfrobInner 0 A = 0 := by simp [kfrobInner]
@[simp] theorem kfrobInner_zero_right (A : KMat 𝕂 n) : kfrobInner A 0 = 0 := by simp [kfrobInner]
theorem kfrobInner_add_left (A B C : KMat 𝕂 n) : kfrobInner (A + B) C = kfrobInner A C + kfrobInner B C := by
  simp [kfrobInner, inner_add_left]
theorem kfrobInner_sub_left (A B C : KMat 𝕂 n) : kfrobInner (A - B) C = kfrobInner A C - kfrobInner B C := by
  simp [kfrobInner, inner_sub_left]
theorem kfrobInner_smul_left (a : ℝ) (A B : KMat 𝕂 n) : kfrobInner (a • A) B = a * kfrobInner A B := by
  simp [kfrobInner, real_inner_smul_left]
theorem kfrobInner_left_unitary (U : KMat 𝕂 n) (hU : KUnitary U) (A B : KMat 𝕂 n) :
    kfrobInner (U * A) (U * B) = kfrobInner A B := by
  rw [kfrobInner_eq_re_trace, kfrobInner_eq_re_trace, Matrix.conjTranspose_mul,
    Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU.1, Matrix.one_mul]
theorem kfrobInner_right_unitary (U : KMat 𝕂 n) (hU : KUnitary U) (A B : KMat 𝕂 n) :
    kfrobInner (A * U) (B * U) = kfrobInner A B := by
  rw [kfrobInner_eq_re_trace, kfrobInner_eq_re_trace, Matrix.conjTranspose_mul,
    show Uᴴ * Aᴴ * (B * U) = Uᴴ * (Aᴴ * B * U) by simp [Matrix.mul_assoc],
    Matrix.trace_mul_comm, Matrix.mul_assoc, hU.2, Matrix.mul_one]
theorem kfrobSq_nonneg (A : KMat 𝕂 n) : 0 ≤ kfrobInner A A := real_inner_self_nonneg
theorem kfrobSq_eq_zero_iff (A : KMat 𝕂 n) : kfrobInner A A = 0 ↔ A = 0 :=
  ⟨fun h => by rw [← decode_encodeKFrob A, inner_self_eq_zero.mp h, map_zero],
   fun h => by simp [h]⟩

def encodedKSubspace (S : Submodule ℝ (KMat 𝕂 n)) : Submodule ℝ (KFrobCoordinates n) :=
  S.map encodeKFrob

def kfrobProjection (S : Submodule ℝ (KMat 𝕂 n)) : KMat 𝕂 n →L[ℝ] KMat 𝕂 n :=
  ((decodeKFrob (𝕂 := 𝕂)).toContinuousLinearMap.comp
    ((encodedKSubspace S).subtypeL.comp (encodedKSubspace S).orthogonalProjection)).comp
    (encodeKFrob (𝕂 := 𝕂)).toContinuousLinearMap

theorem kfrobProjection_mem (S : Submodule ℝ (KMat 𝕂 n)) (Z : KMat 𝕂 n) :
    kfrobProjection S Z ∈ S := by
  obtain ⟨A, hA, he⟩ := ((encodedKSubspace S).orthogonalProjection (encodeKFrob Z)).property
  change decodeKFrob ((encodedKSubspace S).orthogonalProjection (encodeKFrob Z) : KFrobCoordinates n) ∈ S
  rw [← he, decode_encodeKFrob]
  exact hA

theorem kfrobProjection_normal (S : Submodule ℝ (KMat 𝕂 n)) (Z Y : KMat 𝕂 n) (hY : Y ∈ S) :
    kfrobInner (Z - kfrobProjection S Z) Y = 0 := by
  have h := Submodule.orthogonalProjectionFn_inner_eq_zero
    (K := encodedKSubspace S) (encodeKFrob Z) (encodeKFrob Y) ⟨Y, hY, rfl⟩
  rw [Submodule.starProjection_apply, inner_sub_left] at h
  unfold kfrobInner
  rw [map_sub, inner_sub_left]
  change ⟪encodeKFrob Z, encodeKFrob Y⟫_ℝ -
    ⟪encodeKFrob (decodeKFrob ((encodedKSubspace S).orthogonalProjection (encodeKFrob Z) : KFrobCoordinates n)), encodeKFrob Y⟫_ℝ = 0
  rw [inner_encode_decode_left]
  exact h

theorem kfrobProjection_unique_normal (S : Submodule ℝ (KMat 𝕂 n)) (Z Y : KMat 𝕂 n)
    (hY : Y ∈ S) (hn : ∀ W ∈ S, kfrobInner (Z - Y) W = 0) : kfrobProjection S Z = Y := by
  have hd := S.sub_mem (kfrobProjection_mem S Z) hY
  have h₁ := kfrobProjection_normal S Z _ hd
  have h₂ := hn (kfrobProjection S Z - Y) hd
  apply sub_eq_zero.mp
  apply (kfrobSq_eq_zero_iff _).mp
  have he : kfrobProjection S Z - Y = (Z - Y) - (Z - kfrobProjection S Z) := by abel
  conv_lhs => arg 1; rw [he]
  rw [kfrobInner_sub_left, h₂, h₁, sub_self]

@[simp] theorem kfrobProjection_of_mem (S : Submodule ℝ (KMat 𝕂 n)) (Y : KMat 𝕂 n) (hY : Y ∈ S) :
    kfrobProjection S Y = Y :=
  kfrobProjection_unique_normal S Y Y hY fun _ _ => by simp

theorem kfrobProjection_self_adjoint (S : Submodule ℝ (KMat 𝕂 n)) (A B : KMat 𝕂 n) :
    kfrobInner (kfrobProjection S A) B = kfrobInner A (kfrobProjection S B) := by
  have ha := kfrobProjection_normal S A _ (kfrobProjection_mem S B)
  have hb := kfrobProjection_normal S B _ (kfrobProjection_mem S A)
  rw [kfrobInner_sub_left] at ha hb
  rw [kfrobInner_comm B, kfrobInner_comm (kfrobProjection S B)] at hb
  linarith

def kambientGradient (f : KMat 𝕂 n → ℝ) (X : KMat 𝕂 n) : KMat 𝕂 n :=
  decodeKFrob ((InnerProductSpace.toDual ℝ (KFrobCoordinates n)).symm
    ((fderiv ℝ f X).comp (decodeKFrob (𝕂 := 𝕂)).toContinuousLinearMap))

theorem kambientGradient_represents (f : KMat 𝕂 n → ℝ) (X Z : KMat 𝕂 n) :
    fderiv ℝ f X Z = kfrobInner (kambientGradient f X) Z := by
  unfold kambientGradient kfrobInner
  rw [inner_encode_decode_left, InnerProductSpace.toDual_symm_apply]
  change fderiv ℝ f X Z = fderiv ℝ f X (decodeKFrob (encodeKFrob Z))
  rw [decode_encodeKFrob]

theorem kambientGradient_contDiff_of_loss (f : KMat 𝕂 n → ℝ) {r s : WithTop ℕ∞}
    (hf : ContDiff ℝ s f) (hrs : r + 1 ≤ s) : ContDiff ℝ r (kambientGradient f) := by
  unfold kambientGradient
  exact (decodeKFrob (𝕂 := 𝕂)).toContinuousLinearMap.contDiff.comp
    ((InnerProductSpace.toDual ℝ (KFrobCoordinates n)).symm.contDiff.comp
      ((hf.fderiv_right hrs).clm_comp contDiff_const))

end GS.SharedGeometry

namespace GS.UnitarySharing

def TiedEntries {n : ℕ} (b : ℕ) (τ : ℕ → ℕ) (A : GS.CMat n) : Prop :=
  ∀ i j i' j' : Fin n,
    i.val / b = j.val / b → i'.val / b = j'.val / b →
    τ (i.val / b) = τ (i'.val / b) →
    i.val % b = i'.val % b → j.val % b = j'.val % b → A i j = A i' j'

def SharedUnitaryFactor {n : ℕ} (b : ℕ) (τ : ℕ → ℕ) (A : GS.CMat n) : Prop :=
  GS.UnitaryGeometry.CSupported (fun i => i.val / b) A ∧ GS.Unitary A ∧ TiedEntries b τ A

def InSharedA2Unitary {n : ℕ} (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P X : GS.CMat n) : Prop :=
  ∃ L R, SharedUnitaryFactor b₂ τ₂ L ∧ SharedUnitaryFactor b₁ τ₁ R ∧
    X = GS.UnitaryGeometry.product2 L P R

end GS.UnitarySharing

namespace GS.GlobalGeometry
open GS.SharedGeometry

def TiedEntries {n : ℕ} (b : ℕ) (τ : ℕ → ℕ) (A : GS.Mat n) : Prop :=
  ∀ i j i' j' : Fin n,
    i.val / b = j.val / b → i'.val / b = j'.val / b →
    τ (i.val / b) = τ (i'.val / b) →
    i.val % b = i'.val % b → j.val % b = j'.val % b → A i j = A i' j'

def SharedOrthogonalFactor {n : ℕ} (b : ℕ) (τ : ℕ → ℕ) (A : GS.Mat n) : Prop :=
  GS.BlockDiagonal b A ∧ GS.Orthogonal A ∧ TiedEntries b τ A

def InSharedA2Orth {n : ℕ} (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P X : GS.Mat n) : Prop :=
  ∃ L R, SharedOrthogonalFactor b₂ τ₂ L ∧ SharedOrthogonalFactor b₁ τ₁ R ∧
    X = GS.product2 L P R

variable {n b : ℕ} {τ : ℕ → ℕ} {A B C : Mat n}
abbrev sharedSkewSpace (b : ℕ) (τ : ℕ → ℕ) : Submodule ℝ (Mat n) := ksharedSkewSpace b τ

theorem TiedEntries.pow (hb : 0 < b) (hbn : b ∣ n)
    (hAs : BlockDiagonal b A) (hA : TiedEntries b τ A) (k : ℕ) :
    TiedEntries b τ (A ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact TiedEntries_one b τ
  | succ k ih => rw [pow_succ]; exact TiedEntries_mul hb hbn (supported_pow hAs k) hAs ih hA

theorem matrixExp_tied (hb : 0 < b) (hbn : b ∣ n)
    (hAs : BlockDiagonal b A) (hA : TiedEntries b τ A) :
    TiedEntries b τ (matrixExp A) := by
  let F : Finset ℕ → Mat n := fun s => ∑ k ∈ s, ((k.factorial : ℝ)⁻¹) • A ^ k
  apply (isClosed_tiedEntries b τ).mem_of_tendsto (matrixExp_hasSum A)
  refine Filter.Eventually.of_forall fun s i j i' j' h1 h2 h3 h4 h5 => ?_
  simp only [F, Matrix.sum_apply, Matrix.smul_apply]
  exact Finset.sum_congr rfl fun k _ =>
    congrArg _ (TiedEntries.pow hb hbn hAs hA k i j i' j' h1 h2 h3 h4 h5)

theorem expLine_tied (hb : 0 < b) (hbn : b ∣ n)
    (hCs : BlockDiagonal b C) (hC : TiedEntries b τ C) (t : ℝ) :
    TiedEntries b τ (expLine C t) :=
  matrixExp_tied hb hbn (Supported.smul t hCs)
    (fun i j i' j' h1 h2 h3 h4 h5 => by simp [hC i j i' j' h1 h2 h3 h4 h5])

theorem gsExpLeft_shared (b : ℕ) (τ : ℕ → ℕ) (hb : 0 < b) (hbn : b ∣ n)
    (B C : Mat n) (hB : SharedOrthogonalFactor b τ B)
    (hC : C ∈ sharedSkewSpace b τ) (t : ℝ) :
    SharedOrthogonalFactor b τ (gsExpLeft B C t) :=
  ⟨gsExpLeft_supported B C hB.1 hC.1 t, gsExpLeft_orthogonal B C hB.2.1 hC.2.1 t,
   TiedEntries_mul hb hbn hB.1 (expLine_supported hC.1 t) hB.2.2 (expLine_tied hb hbn hC.1 hC.2.2 t)⟩

theorem gsExpRight_shared (b : ℕ) (τ : ℕ → ℕ) (hb : 0 < b) (hbn : b ∣ n)
    (B Ω : Mat n) (hB : SharedOrthogonalFactor b τ B)
    (hΩ : Ω ∈ sharedSkewSpace b τ) (t : ℝ) :
    SharedOrthogonalFactor b τ (gsExpRight B Ω t) :=
  ⟨gsExpRight_supported B Ω hB.1 hΩ.1 t, gsExpRight_orthogonal B Ω hB.2.1 hΩ.2.1 t,
   TiedEntries_mul hb hbn (expLine_supported hΩ.1 t) hB.1 (expLine_tied hb hbn hΩ.1 hΩ.2.2 t) hB.2.2⟩

end GS.GlobalGeometry
