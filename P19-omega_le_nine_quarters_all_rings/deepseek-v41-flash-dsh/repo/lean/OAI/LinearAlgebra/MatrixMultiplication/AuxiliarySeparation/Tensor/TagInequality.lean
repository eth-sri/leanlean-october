module

/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources to support arbitrary fields.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Entropy.Tag
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Separation.Basic
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Dot
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.CharacterBounds
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.FiniteSeparation
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.SharedPadding

public section

@[expose] section

namespace OAI

/-!
# The shared-input tensor tag inequality

Exact type words in a power of a matched-sector tensor are obtained by explicit
coordinate pullbacks. Their character values depend only on the type counts.
The finite auxiliary separation inequality therefore supplies the integral
bounds required by the entropy limit.
-/


open MatrixMultiplication.Foundation
open scoped BigOperators Classical

namespace MatrixMultiplication.AuxiliarySeparation

variable {K : Type*} [CommSemiring K]

variable {s : ℕ} {X Y Z : Type}
  [Fintype X] [Fintype Y] [Fintype Z]

/-- A word prescribes one branch tensor at each tensor-product position. -/
def branchWordTensor (B : Fin s → Tensor K X Y Z) {n : ℕ} (w : Fin n → Fin s) :
    Tensor K (Fin n → X) (Fin n → Y) (Fin n → Z) :=
  fun x y z => ∏ i, B (w i) (x i) (y i) (z i)

/-- The canonical branch word tensor evaluates multiplicatively. -/
theorem Character.value_branchWordTensor (χ : (Character K))
    (B : Fin s → Tensor K X Y Z) {n : ℕ} (w : Fin n → Fin s) :
    χ.value (branchWordTensor B w) = ∏ i, χ.value (B (w i)) := by
  induction n with
  | zero =>
      have hzero : branchWordTensor B w = Tensor.pullback
          (Equiv.equivPUnit (Fin 0 → X))
          (Equiv.equivPUnit (Fin 0 → Y))
          (Equiv.equivPUnit (Fin 0 → Z)) (unitTensor (K := K)) := by
        funext x y z
        simp [branchWordTensor, Tensor.pullback, unitTensor]
      rw [hzero, χ.value_reindex, χ.map_one]
      simp
  | succ n ih =>
      have heq : branchWordTensor B w = Tensor.pullback
          (Fin.consEquiv (fun _ : Fin (n + 1) => X)).symm
          (Fin.consEquiv (fun _ : Fin (n + 1) => Y)).symm
          (Fin.consEquiv (fun _ : Fin (n + 1) => Z)).symm
          (Tensor.product (B (w 0)) (branchWordTensor B (Fin.tail w))) := by
        funext x y z
        simp [branchWordTensor, Tensor.pullback, Tensor.product, Fin.consEquiv,
          Fin.prod_univ_succ, Fin.tail]
      rw [heq, χ.value_reindex, χ.map_product, ih, Fin.prod_univ_succ]
      rfl

/-- All words of an exact type have the same character value. -/
theorem Character.value_exact_branchWordTensor (χ : (Character K))
    (B : Fin s → Tensor K X Y Z) (counts : Fin s → ℕ) (w : ExactWords counts) :
    χ.value (branchWordTensor B w.val) = ∏ a, χ.value (B a) ^ counts a := by
  rw [χ.value_branchWordTensor,
    ← Fintype.prod_fiberwise' w.val (fun a => χ.value (B a))]
  simp only [Finset.prod_const, Finset.card_univ]
  apply Finset.prod_congr rfl
  intro a _
  rw [show Fintype.card {i // w.val i = a} = counts a from w.property a]

/-- A coordinate on a retained split leg remembers its type word. -/
def typeWordCoordinate (counts : Fin s → ℕ)
    (e : Fin (Fintype.card (ExactWords counts)) ≃ ExactWords counts)
    {U : Type} (y : Fin (Fintype.card (ExactWords counts)) ×
      (Fin (∑ a, counts a) → U)) : Fin (∑ a, counts a) → (Fin s × U) :=
  fun i => ((e y.1).val i, y.2 i)

/-- Restricting both split legs to one exact type produces a shared-first
tensor whose branches are precisely the prescribed branch products. -/
theorem exactType_power_pullback (B : Fin s → Tensor K X Y Z)
    (counts : Fin s → ℕ)
    (e : Fin (Fintype.card (ExactWords counts)) ≃ ExactWords counts) :
    Tensor.pullback id (typeWordCoordinate counts e) (typeWordCoordinate counts e)
        (Tensor.power (sharedFirstTensor B) (∑ a, counts a)) =
      sharedFirstTensor (fun h => branchWordTensor B (e h).val) := by
  funext x y z
  by_cases h : y.1 = z.1
  · simp [Tensor.pullback, Tensor.power, typeWordCoordinate, sharedFirstTensor,
      branchWordTensor, h]
  · have hword : (e y.1).val ≠ (e z.1).val := by
      intro heq
      exact h (e.injective (Subtype.ext heq))
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hword
    simp only [Tensor.pullback, Tensor.power, sharedFirstTensor, h, ↓reduceIte,
      typeWordCoordinate, id_eq]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

/-- The exact-type restriction never exceeds the source power in character. -/
theorem Character.exactType_value_le_power (χ : (Character K))
    (B : Fin s → Tensor K X Y Z) (counts : Fin s → ℕ)
    (e : Fin (Fintype.card (ExactWords counts)) ≃ ExactWords counts) :
    χ.value (sharedFirstTensor (fun h => branchWordTensor B (e h).val)) ≤
      χ.value (sharedFirstTensor B) ^ (∑ a, counts a) := by
  rw [← exactType_power_pullback B counts e, ← χ.value_power]
  exact χ.value_pullback_le _ _ _ _

/-- An explicit finite separation comparison and exact-type restriction
give the integral type bound over any coefficient semiring. -/
theorem Character.integral_type_comparison_of_separation (χ : Character K)
    (hsep : ∀ {M : ℕ} {X' Y' Z' : Type} [Fintype X'] [Fintype Y'] [Fintype Z'],
      0 < M → ∀ B' : Fin M → Tensor K X' Y' Z',
        (∑ i, χ.value (B' i)) * (M : ℝ) ^ χ.pX ≤
          6 * (M : ℝ) * χ.value (sharedFirstTensor B'))
    (B : Fin s → Tensor K X Y Z) (counts : Fin s → ℕ) :
    (Fintype.card (ExactWords counts) : ℝ) ^ χ.pX *
        ∏ a, χ.value (B a) ^ counts a ≤
      6 * χ.value (sharedFirstTensor B) ^ (∑ a, counts a) := by
  let M := Fintype.card (ExactWords counts)
  let e : Fin M ≃ ExactWords counts := (Fintype.equivFin _).symm
  let W : Fin M → Tensor K (Fin (∑ a, counts a) → X)
      (Fin (∑ a, counts a) → Y) (Fin (∑ a, counts a) → Z) :=
    fun h => branchWordTensor B (e h).val
  have hM : 0 < M := by
    simpa only [M, Fintype.card_eq_nat_card] using exactWords_card_pos counts
  have hfinite : ((M : ℝ) * ∏ a, χ.value (B a) ^ counts a) * (M : ℝ) ^ χ.pX ≤
      6 * (M : ℝ) * χ.value (sharedFirstTensor W) := by
    simpa only [W, χ.value_exact_branchWordTensor, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      hsep hM W
  have hsource : χ.value (sharedFirstTensor W) ≤
      χ.value (sharedFirstTensor B) ^ (∑ a, counts a) :=
    χ.exactType_value_le_power B counts e
  have hcancel : (M : ℝ) *
      ((M : ℝ) ^ χ.pX * ∏ a, χ.value (B a) ^ counts a) ≤
        (M : ℝ) * (6 * χ.value (sharedFirstTensor B) ^ (∑ a, counts a)) := by
    calc
      _ = ((M : ℝ) * ∏ a, χ.value (B a) ^ counts a) * (M : ℝ) ^ χ.pX := by ring
      _ ≤ 6 * (M : ℝ) * χ.value (sharedFirstTensor W) := hfinite
      _ ≤ 6 * (M : ℝ) * χ.value (sharedFirstTensor B) ^ (∑ a, counts a) :=
        mul_le_mul_of_nonneg_left hsource (by positivity)
      _ = _ := by ring
  have hbound := (mul_le_mul_iff_right₀ (Nat.cast_pos.mpr hM : (0 : ℝ) < M)).mp hcancel
  simpa only [M, Fintype.card_eq_nat_card] using hbound

/-- Positive branch values imply the shared-input tag inequality from a
finite separation bound. No field structure is used. -/
theorem Character.sharedFirst_tag_of_separation (χ : Character K)
    (hsep : ∀ {M : ℕ} {X' Y' Z' : Type} [Fintype X'] [Fintype Y'] [Fintype Z'],
      0 < M → ∀ B' : Fin M → Tensor K X' Y' Z',
        (∑ i, χ.value (B' i)) * (M : ℝ) ^ χ.pX ≤
          6 * (M : ℝ) * χ.value (sharedFirstTensor B'))
    (q : FiniteLaw (Fin s)) (B : Fin s → Tensor K X Y Z)
    (hB : ∀ a, 0 < χ.value (B a)) :
    Real.exp (χ.pX * finiteEntropy q.mass) *
        ∏ a, χ.value (B a) ^ q.mass a ≤ χ.value (sharedFirstTensor B) := by
  have hs : 0 < s := by
    by_contra hn
    have hs0 : s = 0 := Nat.eq_zero_of_not_pos hn
    subst s
    have htotal := q.total
    simp at htotal
  let a : Fin s := ⟨0, hs⟩
  have hbranch : Tensor.pullback id (fun y => (a, y)) (fun z => (a, z))
      (sharedFirstTensor B) = B a := by
    funext x y z
    simp [Tensor.pullback, sharedFirstTensor]
  have hbnd := χ.value_pullback_le (sharedFirstTensor B) id
    (fun y => (a, y)) (fun z => (a, z))
  rw [hbranch] at hbnd
  have hT : 0 < χ.value (sharedFirstTensor B) := (hB a).trans_le hbnd
  apply χ.tag_of_integral_type_comparison_of_value_pos q (sharedFirstTensor B) B χ.pX hT hB
  intro counts _hcounts
  simpa only [Fintype.card_eq_nat_card] using
    χ.integral_type_comparison_of_separation hsep B counts

/-- A coefficient one in each branch supplies positivity for the tag bound. -/
theorem Character.sharedFirst_tag_of_separation_of_coefficient_one (χ : Character K)
    (hsep : ∀ {M : ℕ} {X' Y' Z' : Type} [Fintype X'] [Fintype Y'] [Fintype Z'],
      0 < M → ∀ B' : Fin M → Tensor K X' Y' Z',
        (∑ i, χ.value (B' i)) * (M : ℝ) ^ χ.pX ≤
          6 * (M : ℝ) * χ.value (sharedFirstTensor B'))
    (q : FiniteLaw (Fin s)) (B : Fin s → Tensor K X Y Z)
    (hB : ∀ a, ∃ x y z, B a x y z = 1) :
    Real.exp (χ.pX * finiteEntropy q.mass) *
        ∏ a, χ.value (B a) ^ q.mass a ≤ χ.value (sharedFirstTensor B) :=
  χ.sharedFirst_tag_of_separation hsep q B
    (fun a => zero_lt_one.trans_le (χ.one_le_value_of_coefficient_one (hB a)))

section Field

variable {K : Type*} [Field K] [IsAlgClosed K]

end Field

end MatrixMultiplication.AuxiliarySeparation


end OAI
