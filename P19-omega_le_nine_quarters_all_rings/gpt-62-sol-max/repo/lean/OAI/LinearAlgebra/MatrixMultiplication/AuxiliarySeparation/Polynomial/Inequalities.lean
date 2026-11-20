module

public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convolution.Basic
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.TagInequality
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth

public section

@[expose] section

open scoped NNReal

namespace OAI.MatrixMultiplication.AuxiliarySeparation

open Foundation TensorSemiring

noncomputable section

namespace DeterminantFiltration

abbrev width (e : ℕ) (b : Fin 2) := if b = 0 then e+2 else e
abbrev Index (e : ℕ) := Σ b : Fin 2, Fin (width e b)

/-- The two graded branches, without padding or changing the first leg. -/
def branch (d e : ℕ) (b : Fin 2) : IntTensor (Fin (d+1)) (Fin (width e b)) (Fin (width (d+e) b)) :=
  fun i j k => if i.val + j.val = k.val then 1 else 0

def select {I : Type*} [DecidableEq I] (i j : I) : ℤ := if j = i then 1 else 0

def inputChange (e : ℕ) (j : Index e) (y : Fin (e+1) × Fin 2) : ℤ :=
  if hb : j.1 = 0 then
    if hj : j.2.val < e+1 then select (⟨j.2.val, hj⟩, 0) y else select (⟨e, by omega⟩, 1) y
  else
    have hj : j.2.val < e := by lia
    select (⟨j.2.val, by omega⟩, 1) y - select (⟨j.2.val+1, by omega⟩, 0) y

def outputDualChange (d e : ℕ) (k : Index (d+e)) (z : Fin (d+1+(e+1)-1) × Fin 2) : ℤ :=
  if hb : k.1 = 0 then
    have hk : k.2.val < d+e+2 := by lia
    (if h : k.2.val < d+e+1 then select (⟨k.2.val, by omega⟩, 0) z else 0) +
      (if h : 0 < k.2.val then select (⟨k.2.val-1, by omega⟩, 1) z else 0)
  else
    have hk : k.2.val < d+e := by lia
    select (⟨k.2.val, by omega⟩, 1) z

def changeOfBasis (d e : ℕ) :=
  Tensor.restrict ⟨fun i => select (i, ()), inputChange e, outputDualChange d e⟩
    (Tensor.product (convolution (d+1) (e+1)) (dot 2))

/-- Only coefficients in the two diagonal sectors and the lower cross term
are at or below the extraction degree. -/
def degeneration (d e : ℕ) :
    Tensor.PolynomialRestrictionDegeneration (changeOfBasis d e) (sharedFirstTensor (branch d e)) 1 := by
  classical
  refine Tensor.weightedDegeneration _ _ 1 id id id (fun _ => 0)
    (fun j => if j.1 = 0 then 1 else 0) (fun k => if k.1 = 0 then 0 else 1) ?_
  rintro i ⟨b,j⟩ ⟨c,k⟩ l hl
  have hi := i.isLt
  fin_cases b <;> fin_cases c <;> interval_cases l <;>
    simp [sharedFirstTensor, branch] <;> try rfl
  all_goals
    have hj := j.isLt
    have hk := k.isLt
    simp only [width, Fin.ext_iff, Fin.val_zero, Nat.one_ne_zero, ↓reduceIte] at hj hk
    simp [changeOfBasis, Tensor.restrict, inputChange, outputDualChange]
    split_ifs <;> try omega
  all_goals
    simp only [select, add_mul, sub_mul, mul_sub, mul_add, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ite_mul, mul_ite, zero_mul, mul_zero, one_mul, mul_one,
      Fintype.sum_ite_eq', add_zero, zero_add]
    simp [Tensor.product, convolution, dot]
  all_goals (try split_ifs) <;> omega

end DeterminantFiltration

namespace Sector

abbrev sourceWidth (a h : ℕ) := 3 * h + a - 1
abbrev rightStart (a h : ℕ) := 2 * h + a - 1
abbrev yWidth (a h : ℕ) (b : Fin 3) := if b = 1 then a+h-1 else h
abbrev zWidth (a h : ℕ) (b : Fin 3) := if b = 1 then h else a+h-1

private def embed (out : Bool) (a h : ℕ) (b : Fin 3)
    (j : Fin (if out then zWidth a h b else yWidth a h b)) :
    Fin (if out then a + sourceWidth a h - 1 else sourceWidth a h) :=
  let j' := if b = 1 then j.rev else j
  ⟨(if b = 0 then 0 else if b = 1 then (if out then h+a-1 else h) else rightStart a h) + j'.val, by
    have hj := j'.isLt
    cases out <;> fin_cases b <;> simp [yWidth, zWidth, rightStart, sourceWidth] at * <;> omega⟩

/-- Reversing both middle intervals gives a transpose of convolution. -/
def branch (a h : ℕ) (b : Fin 3) : IntTensor (Fin a) (Fin (yWidth a h b)) (Fin (zWidth a h b)) :=
  fun i j k => if (if b = 1 then i.val + k.val = j.val else i.val + j.val = k.val) then 1 else 0

/-- The interval offsets give positive degree on the support; degree one
keeps just the three matching intervals. -/
private noncomputable def restriction (a h : ℕ) :
    Tensor.PolynomialRestrictionDegeneration (convolution a (sourceWidth a h))
      (sharedFirstTensor (branch a h)) 1 := by
  classical
  refine Tensor.weightedDegeneration _ _ 1 id (fun y => embed false a h y.1 y.2) (fun z => embed true a h z.1 z.2)
    (fun _ => 0) (fun y => if y.1 = 1 then 1 else 0) (fun z => if z.1 = 1 then 0 else 1) ?_
  rintro i ⟨b,j⟩ ⟨c,k⟩ l hl
  have hi := i.isLt
  have hj := j.isLt
  have hk := k.isLt
  fin_cases b <;> fin_cases c <;> interval_cases l <;>
    simp [sharedFirstTensor, branch, convolution, embed,
      rightStart, yWidth, zWidth, Fin.val_rev] at * <;> try omega


end Sector

namespace Character

variable (χ : Character)

open DeterminantFiltration

/-- Apply the type-counting inequality to all six permutations at once. -/
private theorem symmetrizedProfile_sum_le
    (ht : 0 < χ.exponent)
    {m : ℕ} {X U V W : Type} {Y Z : Fin m → Type}
    [Fintype X] [∀ i, Fintype (Y i)] [∀ i, Fintype (Z i)]
    [Fintype U] [Fintype V] [Fintype W]
    (B : ∀ i, IntTensor X (Y i) (Z i)) (T : IntTensor U V W)
    {c : ℕ} (hc : 0 < c)
    (hB : ∀ ψ : Character, ψ.value (sharedFirstTensor B) ≤ ψ.value (dot c) * ψ.value T) :
    (∑ i, χ.symmetrizedProfile (B i)) ≤ c * χ.symmetrizedProfile T := by
  have H : χ.values (sharedFirstTensor B) ≤
      χ.values (dot c) * χ.values T := fun i => hB _
  have h := χ.normalize_mono ht H
  rw [map_mul, χ.normalize_dot ht hc] at h
  exact (sharedFirst_sum_value_le B χ ht).trans h

/-- The three dot-product exponents of an actual character sum to at most `9/4`. -/
theorem exponent_le_nine_quarters : χ.exponent ≤ 9 / 4 := by
  by_cases ht : 0 < χ.exponent
  swap
  · linarith
  refine ScalarProfile.exponent_le_nine_quarters ?_ ht
  exact {
    value a b := χ.convolutionProfile a b
    nonneg a b := NNReal.coe_nonneg _
    symmetric a b := congrArg NNReal.toReal (χ.convolutionProfile_comm a b)
    unit := by simp
    concave a b ha := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
      have H := χ.symmetrizedProfile_sum_le ht (branch d b) (convolution (d+1) (b+1)) (by decide : 0 < 2)
        (fun ψ => by
          refine (ψ.value_polynomialRestrictionDegeneration_le_ring (degeneration d b)).trans ?_
          rw [mul_comm, ← ψ.map_product]
          exact ψ.value_le_of_restriction ⟨_,rfl⟩)
      have hb (i : Fin 2) : χ.symmetrizedProfile (branch d b i) = χ.convolutionProfile (d+1) (width b i) :=
        congrArg χ.classProfile (classOf_eq_of_reindex (Equiv.refl _) (Equiv.refl _)
          (finCongr (by unfold width; split_ifs <;> omega)) rfl)
      exact_mod_cast (by simpa [Fin.sum_univ_two, hb, width, convolutionProfile, add_comm] using H :
        χ.convolutionProfile (d+1) b + χ.convolutionProfile (d+1) (b+2) ≤
          2 * χ.convolutionProfile (d+1) (b+1))
    tripling a h := by
      have H := χ.symmetrizedProfile_sum_le ht (Sector.branch a h) (convolution a (Sector.sourceWidth a h)) Nat.zero_lt_one
        (fun ψ => by simpa [Character.value, show classOf (dot 1) = 1 from dotClass.map_one] using ψ.value_polynomialRestrictionDegeneration_le_ring (Sector.restriction a h))
      have hs (i : Fin 3) : χ.symmetrizedProfile (Sector.branch a h i) = χ.convolutionProfile a h := by
        fin_cases i
        · rfl
        · exact χ.symmetrizedProfile_swap23 (convolution a h)
        · rfl
      exact_mod_cast (by simpa [hs, convolutionProfile] using H :
        (3 : ℝ≥0) * χ.convolutionProfile a h ≤ χ.convolutionProfile a (3*h+a-1))
    rank_bound n := by
      have H : χ.values (convolution n n) ≤ fun _ => ((2*n : ℕ) : ℝ≥0) := fun i => by
        exact ((χ.permutedCharacter i).value_convolution_le n n).trans
          (Nat.cast_le.mpr (by omega : n+n-1 ≤ 2*n))
      exact_mod_cast (χ.normalize_mono ht H).trans_eq (χ.normalize_const _)
  }

end Character
end
end OAI.MatrixMultiplication.AuxiliarySeparation
