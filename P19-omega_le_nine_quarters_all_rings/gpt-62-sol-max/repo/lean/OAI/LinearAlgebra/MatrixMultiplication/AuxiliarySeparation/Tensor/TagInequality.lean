module

public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convolution.Basic
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Basic
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth

public section

open scoped NNReal
@[expose] section

namespace OAI.MatrixMultiplication.AuxiliarySeparation

open Foundation Character TensorSemiring
noncomputable section

variable {s : ℕ} {X : Type} {Y Z : Fin s → Type}
variable [Fintype X] [∀ i, Fintype (Y i)] [∀ i, Fintype (Z i)]

/-- The separated tensor is the independent sum of the branches, each
multiplied by a dot product on its two split legs. -/
private def separationTarget (B : ∀ b, IntTensor X (Y b) (Z b)) :=
  blockSum (fun b => Tensor.product (B b)
    (dot s))

private def leftDegree (g : Fin s) := g.val^2
private def middleDegree (h u : Fin s) := s^2 - h.val^2 + h.val*u.val
private def rightDegree (h v : Fin s) := s^2 - h.val*v.val

/-- On the convolution support the excess degree is the square of the tag
mismatch. At the first possible degree both tag pairs therefore coincide. -/
private theorem threshold (g h u v : Fin s) {j : ℕ} (hj : j ≤ 2*s^2) :
    (j = leftDegree g + middleDegree h u + rightDegree h v ∧ 2*g.val+u.val = 2*h.val+v.val) ↔
      j = 2*s^2 ∧ h = g ∧ u = v := by
  have hp : h.val^2 ≤ s^2 := Nat.pow_le_pow_left h.isLt.le _
  have hm : h.val*v.val ≤ s^2 := by simpa [pow_two] using Nat.mul_le_mul h.isLt.le v.isLt.le
  constructor
  · rintro ⟨rfl, he⟩
    dsimp [leftDegree, middleDegree, rightDegree] at hj
    zify [hp, hm] at hj he
    have hs : ((g.val : ℤ)-h.val)^2 ≤ 0 := by linear_combination hj - (h.val : ℤ)*he
    have e : h = g := by simpa [sq_nonpos_iff, sub_eq_zero, Fin.ext_iff, eq_comm] using hs
    subst h
    simp_all [leftDegree, middleDegree, rightDegree]; grind
  rintro ⟨rfl,rfl,rfl⟩
  simp [leftDegree, middleDegree, rightDegree]; omega

/-- The tag filter is a pullback of ordinary convolution, so the construction
uses no root of unity or denominators. -/
private def separationDegeneration (B : ∀ i, IntTensor X (Y i) (Z i)) :
    Tensor.PolynomialRestrictionDegeneration
      (Tensor.product (sharedFirstTensor B) (convolution (2*s) s)) (separationTarget B) (2*s^2) := by
  classical
  refine Tensor.weightedDegeneration _ _ _
    (fun x => (x.2.1, ⟨2*x.1.val, by grind⟩))
    (fun y => (⟨y.1, y.2.1⟩, y.2.2))
    (fun z => (⟨z.1, z.2.1⟩, ⟨2*z.1.val+z.2.2.val, by omega⟩))
    (fun x => leftDegree x.1) (fun y => middleDegree y.1 y.2.2) (fun z => rightDegree z.1 z.2.2) ?_
  rintro ⟨g,x,_⟩ ⟨h,y,u⟩ ⟨l,z,v⟩ j hj
  by_cases e : l = h
  · subst l
    simp only [Tensor.product, convolution, sharedFirstTensor, dite_true,
      mul_ite, mul_one, mul_zero, ← ite_and]
    simp only [threshold g h u v hj]
    by_cases f : h = g
    · subst g
      simp [separationTarget, blockSum, Tensor.product, dot,
        ite_and, mul_ite]
    · simp [separationTarget, blockSum, f]
  · by_cases f : h = g <;>
      simp_all [sharedFirstTensor, Tensor.product, separationTarget, blockSum]

/-- Separation of branches with equal value costs at most three times their
number, via the value of the tag convolution tensor. -/
private theorem finiteSeparation_bound (χ : Character) (hm : 0 < s)
    (B : ∀ i, IntTensor X (Y i) (Z i)) {T : TensorClass} (hv : ∀ i, classOf (B i) = T) :
    χ.value (dot s) * χ T ≤ 3 * χ.value (sharedFirstTensor B) := by
  apply (mul_le_mul_iff_left₀ (Nat.cast_pos.mpr hm)).mp
  calc
    _ = χ.value (separationTarget B) := by
      simp [Character.value, separationTarget, classOf_blockSum, classOf_product, map_mul, hv, mul_comm]
    _ ≤ χ.value (Tensor.product (sharedFirstTensor B) (convolution (2*s) s)) :=
      χ.value_polynomialRestrictionDegeneration_le_ring (separationDegeneration B)
    _ ≤ χ.value (sharedFirstTensor B) * (3 * (s : ℝ≥0)) := by
      rw [χ.map_product]
      gcongr
      exact (χ.value_convolution_le _ _).trans (by exact_mod_cast (show 2*s+s-1 ≤ 3*s by omega))
    _ = _ := by ring


variable (B : ∀ i, IntTensor X (Y i) (Z i))

private abbrev wordTensor {n : ℕ} (w : Fin n → Fin s) := Tensor.wordProduct (fun i => B (w i))

/-- Sorting words by multiplicities uses at most `(n+1)^s` classes. -/
private def wordType {n : ℕ} (w : Fin n → Fin s) (a : Fin s) : Fin (n + 1) :=
  ⟨Fintype.card {i // w i = a}, Nat.lt_succ_of_le (by simpa using Fintype.card_subtype_le (fun i => w i = a))⟩

/-- The whole word of branch choices can be read on each split leg. -/
private theorem word_restriction {m n : ℕ} (w : Fin m → Fin n → Fin s) (hw : Function.Injective w) :
    IsRestriction (sharedFirstTensor (fun j => wordTensor B (w j))) (Tensor.power (sharedFirstTensor B) n) := by
  classical
  convert IsRestriction.pullback (Tensor.power (sharedFirstTensor B) n) id
    (fun (y : Σ j, ∀ i, Y (w j i)) i => ⟨w y.1 i, y.2 i⟩)
    (fun (z : Σ j, ∀ i, Z (w j i)) i => ⟨w z.1 i, z.2 i⟩) using 1
  symm
  ext x ⟨a,y⟩ ⟨b,z⟩
  by_cases e : b = a
  · subst b; simp [Tensor.pullback, Tensor.power, Tensor.wordProduct, sharedFirstTensor]
  obtain ⟨i, hi⟩ : ∃ i, w b i ≠ w a i := not_forall.mp (mt funext (hw.ne e))
  simp only [Tensor.pullback, id_eq, Tensor.power, Tensor.wordProduct, sharedFirstTensor, e, dite_false]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

variable (χ : Character) (ht : 0 < χ.exponent)

private def loss : ℝ≥0 := χ.normalize (fun _ => 3)

include ht in
private theorem type_sum_bound (n : ℕ) (c : Fin s → Fin (n+1)) :
    (∑ w : {w : Fin n → Fin s // wordType w = c}, χ.symmetrizedProfile (wordTensor B w.val)) ≤
      loss χ * (χ.symmetrizedProfile (sharedFirstTensor B)) ^ n := by
  let W := {w : Fin n → Fin s // wordType w = c}
  let m := Fintype.card W
  by_cases hm : 0 < m
  · let e : Fin m ≃ W := (Fintype.equivFin _).symm
    let T := ∏ a, classOf (B a) ^ (c a).val
    have hv (w : W) : classOf (wordTensor B w.val) = T := by
      rw [wordTensor, classOf_wordProduct, ← Fintype.prod_fiberwise' w.val (fun a => classOf (B a))]
      simp [T, ← w.property, wordType]
    have hi : χ.values (dot m) * χ.classValues T ≤
        (fun _ => (3 : ℝ≥0)) * χ.values (sharedFirstTensor B) ^ n := by
      intro i
      let ψ := χ.permutedCharacter i
      have H := finiteSeparation_bound ψ hm (fun j => wordTensor B (e j).val)
        (fun j => hv (e j))
      have H' := ψ.value_le_of_restriction (word_restriction B (fun j => (e j).val)
        (Subtype.val_injective.comp e.injective))
      rw [ψ.value_power] at H'
      exact H.trans (mul_le_mul_of_nonneg_left H' zero_le)
    have h := χ.normalize_mono ht hi
    rw [map_mul, map_mul, map_pow, χ.normalize_dot ht hm] at h
    change (∑ w : W, _) ≤ _
    simp_rw [symmetrizedProfile, hv]
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, loss, m] using! h
  · have : IsEmpty W := Fintype.card_eq_zero_iff.mp (by omega : m = 0)
    simp

include ht in
/-- The polynomial number of types removes the constant loss from finite separation. -/
theorem sharedFirst_sum_value_le :
    (∑ a, χ.symmetrizedProfile (B a)) ≤ χ.symmetrizedProfile (sharedFirstTensor B) := by
  refine NNReal.coe_le_coe.mp (le_of_pow_le_polynomial_mul_pow (C := loss χ) (d := s) (k := 1) (by positivity) ?_)
  norm_cast
  intro n
  have h := Fintype.prod_sum (ι := Fin n) (fun _ a => χ.symmetrizedProfile (B a))
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  rw [h]
  simp_rw [symmetrizedProfile, ← map_prod, ← classOf_wordProduct]
  rw [← Fintype.sum_fiberwise wordType]
  refine (Finset.sum_le_sum (fun c _ => type_sum_bound B χ ht n c)).trans_eq ?_
  simp [mul_left_comm, mul_assoc]

end
end OAI.MatrixMultiplication.AuxiliarySeparation
