module

public import NearlyMinimax.PaperInverse
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

@[expose] public section

/-! Free-coordinate increment polynomials and their vector-moment structure in Lemma U5(3). -/

noncomputable section
namespace NearlyMinimax
open scoped BigOperators
open MvPolynomial

section
variable (r : ℕ)

/-- Current and parent matrix entries together with their regression and density vector moments. -/
abbrev incrementVariables := parentInverseVariables r ⊕ (Bool × Bool × Fin r)

def currentVariableMatrix : Matrix (Fin r) (Fin r) (MvPolynomial (parentInverseVariables r) ℝ) :=
  fun i j => X (Sum.inl (i, j))

def parentVariableMatrix : Matrix (Fin r) (Fin r) (MvPolynomial (parentInverseVariables r) ℝ) :=
  fun i j => X (Sum.inr ⟨0, (i, j)⟩)

end

section
variable {r : ℕ} (a b : ℝ) (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (m : ℕ) (parent response : Bool)
    (i : Fin r)

def vectorMoment :
    MvPolynomial (incrementVariables r) ℝ := X (Sum.inr (parent, response, i))

def rawNumeratorPolynomial : MvPolynomial (incrementVariables r) ℝ :=
  rename Sum.inl (parentVariableMatrix r).det * vectorMoment false response i -
    ∑ j, ∑ k, ∑ l,
      rename Sum.inl (currentVariableMatrix r i j) * C (T j k) *
      rename Sum.inl ((parentVariableMatrix r).adjugate k l) * vectorMoment true response l

/-- The exact determinant-cleared numerator, affine in the formal response `y`. -/
def numeratorPolynomial :
    MvPolynomial (incrementVariables r) ℝ :=
  rawNumeratorPolynomial T false i - C y * rawNumeratorPolynomial T true i

def incrementEntryPolynomial : MvPolynomial (incrementVariables r) ℝ :=
  ∑ j, rename Sum.inl (parentInverseEntryPolynomial a b m i j) * numeratorPolynomial T y j

end

private theorem determinant_degree_le {V n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n (MvPolynomial V ℝ)) (hM : ∀ i j, (M i j).totalDegree ≤ 1) :
    M.det.totalDegree ≤ Fintype.card n := by
  rw [Matrix.det_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro σ hσ
  simp only [Units.smul_def]
  apply (MvPolynomial.totalDegree_smul_le _ _).trans
  apply (MvPolynomial.totalDegree_finsetProd Finset.univ _).trans
  calc
    _ ≤ ∑ _i : n, 1 := by bound
    _ = _ := by simp

private theorem adjugate_degree_le {V : Type*} {r : ℕ}
    (M : Matrix (Fin r) (Fin r) (MvPolynomial V ℝ))
    (hM : ∀ i j, (M i j).totalDegree ≤ 1) (i j : Fin r) :
    (M.adjugate i j).totalDegree ≤ r - 1 := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ k =>
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    apply (MvPolynomial.totalDegree_mul _ _).trans
    have hz : ((-1 : MvPolynomial V ℝ) ^ (j.val + i.val)).totalDegree ≤ 0 := by
      simpa using MvPolynomial.totalDegree_pow (-1 : MvPolynomial V ℝ) (j.val + i.val)
    have hd := determinant_degree_le (M.submatrix j.succAbove i.succAbove) (fun i j => hM _ _)
    simpa using Nat.add_le_add hz hd

section
variable {r : ℕ} [NeZero r] (a b : ℝ) (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (m : ℕ) (response : Bool)
    (i : Fin r)

/-- The cleared numerator has total degree at most `r+1`. -/
theorem rawNumeratorPolynomial_degree :
    (rawNumeratorPolynomial T response i).totalDegree ≤ r + 1 := by
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · apply (MvPolynomial.totalDegree_mul _ _).trans
    apply Nat.add_le_add
    · apply (MvPolynomial.totalDegree_rename_le _ _).trans
      simpa using determinant_degree_le (parentVariableMatrix r) (by simp [parentVariableMatrix])
    · simp [vectorMoment]
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro j hj
    apply MvPolynomial.totalDegree_finsetSum_le
    intro k hk
    apply MvPolynomial.totalDegree_finsetSum_le
    intro l hl
    have hadj := adjugate_degree_le (parentVariableMatrix r) (by simp [parentVariableMatrix]) k l
    have hadj' := (MvPolynomial.totalDegree_rename_le
      (Sum.inl : parentInverseVariables r → incrementVariables r) _).trans hadj
    have hA : (rename Sum.inl (currentVariableMatrix r i j) :
        MvPolynomial (incrementVariables r) ℝ).totalDegree ≤ 1 := by simp [currentVariableMatrix]
    have h1 := MvPolynomial.totalDegree_mul
      (rename Sum.inl (currentVariableMatrix r i j) : MvPolynomial (incrementVariables r) ℝ) (C (T j k))
    have h2 := MvPolynomial.totalDegree_mul
      (rename Sum.inl (currentVariableMatrix r i j) * C (T j k) : MvPolynomial (incrementVariables r) ℝ)
      (rename Sum.inl ((parentVariableMatrix r).adjugate k l))
    have h3 := MvPolynomial.totalDegree_mul
      (rename Sum.inl (currentVariableMatrix r i j) * C (T j k) *
        rename Sum.inl ((parentVariableMatrix r).adjugate k l)) (vectorMoment true response l)
    simp at h1
    have hv : (vectorMoment true response l).totalDegree = 1 := by simp [vectorMoment]
    rw [hv] at h3
    have hr  := NeZero.ne r
    omega

theorem numeratorPolynomial_degree :
    (numeratorPolynomial T y i).totalDegree ≤ r + 1 := by
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le (rawNumeratorPolynomial_degree T false i)
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simpa using rawNumeratorPolynomial_degree T true i

/-- The complete free-moment increment has the paper's degree bound `m+r+1`. -/
theorem incrementEntryPolynomial_degree :
    (incrementEntryPolynomial a b T y m i).totalDegree ≤ m + r + 1 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  apply (MvPolynomial.totalDegree_mul _ _).trans
  exact (Nat.add_le_add ((MvPolynomial.totalDegree_rename_le _ _).trans
    (parentInverseEntryPolynomial_degree a b r m i j))
    (numeratorPolynomial_degree T y j)).trans_eq (by omega)

end

def rawIncrementEntryPolynomial {r : ℕ} (a b : ℝ) (T : Matrix (Fin r) (Fin r) ℝ)
    (response : Bool) (m : ℕ) (i : Fin r) : MvPolynomial (incrementVariables r) ℝ :=
  ∑ j, rename Sum.inl (parentInverseEntryPolynomial a b m i j) *
    rawNumeratorPolynomial T response j

/-- The response variable appears only affinely in the entire increment polynomial. -/
theorem incrementEntryPolynomial_affine (r : ℕ) (a b : ℝ)
    (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (m : ℕ) (i : Fin r) :
    incrementEntryPolynomial a b T y m i =
      rawIncrementEntryPolynomial a b T false m i - C y *
        rawIncrementEntryPolynomial a b T true m i := by
  unfold incrementEntryPolynomial numeratorPolynomial rawIncrementEntryPolynomial
  have he (j : Fin r) :
      rename Sum.inl (parentInverseEntryPolynomial a b m i j) *
        (C y * rawNumeratorPolynomial T true j) =
      C y * (rename Sum.inl (parentInverseEntryPolynomial a b m i j) *
        rawNumeratorPolynomial T true j) := mul_left_comm ..
  simp_rw [mul_sub, he]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]

open RoughRegime.CombinedPolynomial

section
variable {r : ℕ} (a b : ℝ) (A C T : Matrix (Fin r) (Fin r) ℝ) (U V : Bool → Fin r → ℝ) (y : ℝ)

/-- Evaluation substitutes the current and parent Gram entries and the two vector families. -/
def incrementValuation : incrementVariables r → ℝ
  | Sum.inl x => entryValuation A (fun _ => C) x
  | Sum.inr (parent, response, i) => if parent then V response i else U response i

private theorem rawNumeratorPolynomial_eval
    (response : Bool) (i : Fin r) :
    eval (incrementValuation A C U V) (rawNumeratorPolynomial T response i) =
      incrementNumerator A C T (U response) (V response) i := by
  let f := MvPolynomial.eval₂Hom (RingHom.id ℝ) (entryValuation A (fun _ : Fin 1 => C))
  have hm : f.mapMatrix (parentVariableMatrix r) = C := by
    ext j k
    simp [f, parentVariableMatrix, entryValuation, RingHom.mapMatrix_apply]
  have hd : eval (incrementValuation A C U V)
      (rename Sum.inl (parentVariableMatrix r).det) = C.det := by
    rw [MvPolynomial.eval_rename]
    change f _ = C.det
    rw [f.map_det, hm]
  have ha (k l : Fin r) : eval (incrementValuation A C U V)
      (rename Sum.inl ((parentVariableMatrix r).adjugate k l)) = C.adjugate k l := by
    rw [MvPolynomial.eval_rename]
    have h := congrArg (fun M => M k l) (f.map_adjugate (parentVariableMatrix r))
    rw [hm] at h
    exact h
  simp [rawNumeratorPolynomial, hd, ha]
  simp [vectorMoment, incrementValuation, currentVariableMatrix, entryValuation]
  simp only [incrementNumerator, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc]

/-- Evaluating the free polynomial gives exactly the paper's cleared numerator for `β-yμ`. -/
theorem numeratorPolynomial_eval (i : Fin r) :
    eval (incrementValuation A C U V) (numeratorPolynomial T y i) =
      incrementNumerator A C T (U false - y • U true) (V false - y • V true) i := by
  rw [numeratorPolynomial, eval_sub, eval_mul, eval_C,
    rawNumeratorPolynomial_eval, rawNumeratorPolynomial_eval]
  simp only [incrementNumerator, Matrix.mulVec_sub, Matrix.mulVec_smul, smul_sub, smul_smul,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

end

open scoped Matrix.Norms.L2Operator

/-- The exact polynomial propagates any explicitly supplied small-increment bound to U5(2). -/
theorem incrementEntryPolynomial_error {r : ℕ} [NeZero r]
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (A C T : Matrix (Fin r) (Fin r) ℝ) (hA : A.IsHermitian) (hC : C.IsHermitian)
    (hSpecA : spectrum ℝ A ⊆ Set.Icc a b) (hSpecC : spectrum ℝ C ⊆ Set.Icc a b)
    (Q R : (Matrix (Fin r) (Fin r) ℝ)ˣ) {χ : ℝ}
    (hχ : ‖(Q : Matrix (Fin r) (Fin r) ℝ)‖ * ‖(↑Q⁻¹ : Matrix (Fin r) (Fin r) ℝ)‖ ≤ χ)
    (U V : Bool → Fin r → ℝ) (y ε : ℝ)
    (hδ : ‖(EuclideanSpace.equiv (Fin r) ℝ).symm
      ((matrixSimilarity Q A)⁻¹.mulVec (U false - y • U true) -
        T.mulVec ((matrixSimilarity R C)⁻¹.mulVec (V false - y • V true)))‖ ≤ ε)
    (m : ℕ) :
    let G := matrixSimilarity Q A
    let Cminus := matrixSimilarity R C
    ‖(EuclideanSpace.equiv (Fin r) ℝ).symm
      ((fun i => eval (incrementValuation G Cminus U V)
          (incrementEntryPolynomial a b T y m i)) -
        (G⁻¹.mulVec (U false - y • U true) -
          T.mulVec (Cminus⁻¹.mulVec (V false - y • V true))))‖ ≤
      (χ ^ 2 * b ^ (r + 1) * parentInverseErrorConstant a b r) * ε *
        (m + 1 : ℕ) ^ r *
        Real.exp (-m * intervalExteriorTau a b) := by
  simp_rw [incrementEntryPolynomial, eval_sum, eval_mul, numeratorPolynomial_eval, MvPolynomial.eval_rename]
  let β := U false - y • U true
  let βminus := V false - y • V true
  have hχ0  := (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans hχ
  have hb  := ha.trans hab
  have hM := parentInverseErrorConstant_pos ha hab r
  have hn := increment_numerator_norm_le ha hab A C T hA hC hSpecA hSpecC Q R hχ β βminus
  dsimp at hn
  have hsmall  := hn.trans
        (mul_le_mul_of_nonneg_left hδ (by positivity))
  have he := increment_polynomial_error ha hab A C T hA hC hSpecA hSpecC Q R hχ β βminus m
  dsimp at he
  apply he.trans
  apply (mul_le_mul_of_nonneg_left hsmall (by positivity)).trans_eq
  ring

end NearlyMinimax
