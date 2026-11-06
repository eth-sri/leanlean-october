module

public import NearlyMinimax.PaperInverse
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗎

/-! Free-coordinate increment polynomials and their vector-moment structure in Lemma U5(3). -/

open MvPolynomial

/-- Current and parent matrix entries together with their regression and density vector moments. -/
abbrev incrementVariables (r : ℕ) := parentInverseVariables r ⊕ Bool × Bool × Fin r

𝗇 𝔚 𝗲
𝗇 𝔐 𝔚 $ MvPolynomial (parentInverseVariables r) ℝ
def currentVariableMatrix (r : ℕ) : 𝔐 :=
  fun i j => X $ Sum.inl 𝘈₁

def parentVariableMatrix (r : ℕ) : 𝔐 :=
  fun i j => X $ Sum.inr ⟨0, 𝘈₁⟩

𝗇 𝔅 MvPolynomial (incrementVariables r) ℝ
𝗇 𝔗 Sum.inr (parent, response, i)
def vectorMoment (r : ℕ) (parent response : Bool) (i : Fin r) :
    𝔅 := X 𝔗

𝗇 𝔄 𝔚 ℝ
𝗇 𝔇 rename Sum.inl $ (parentVariableMatrix r).adjugate k l
𝗇 𝔢 rename Sum.inl $ currentVariableMatrix r i j
𝗇 𝔣 C $ T j k
𝗇 𝔍 𝔢 * 𝔣
𝗇 𝔓 vectorMoment r true response l
𝗇 𝔛 rename Sum.inl (parentVariableMatrix r).det
def rawNumeratorPolynomial (r : ℕ) (T : 𝔄)
    (response : Bool) (i : Fin r) : 𝔅 :=
  𝔛 * vectorMoment r false response i -
    ∑ j, ∑ k, ∑ l,
      𝔍 *
      𝔇 * 𝔓

𝗇 𝔘 rawNumeratorPolynomial r T
/-- The exact determinant-cleared numerator, affine in the formal response `y`. -/
def numeratorPolynomial (r : ℕ) (T : 𝔄) (y : ℝ) (i : Fin r) :
    𝔅 :=
  𝔘 false i - C y * 𝔘 true i

𝗃 𝔦 ἀ a b r m i j
𝗇 𝔊 rename Sum.inl 𝔦 parentInverseEntryPolynomial
𝗇 𝔟 numeratorPolynomial r T y
def incrementEntryPolynomial (r : ℕ) (a b : ℝ) (T : 𝔄)
    (y : ℝ) (m : ℕ) (i : Fin r) : 𝔅 :=
  ∑ j, 𝔊 * 𝔟 j

𝗇 𝔒 ∀ i j, (M i j).totalDegree ≤ 1
𝗇 𝔔 MvPolynomial V ℝ
𝗃 𝔥 (ἀ ..).trans
𝗃 𝔧 fun i ἀ => hM ..
private theorem determinant_degree_le [Fintype n] [DecidableEq n]
    (M : 𝘉₁ 𝔔) (hM : 𝔒) :
    M.det.totalDegree ≤ Fintype.card n := by
  rw [Matrix.det_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro σ hσ
  apply 𝔥 MvPolynomial.totalDegree_smul_le
  apply (MvPolynomial.totalDegree_finsetProd Finset.univ _).trans
  calc
    ∑ i, (M (σ i) i).totalDegree ≤ ∑ _i : n, 1 := Finset.sum_le_sum 𝔧 hi
    𝘿 := 𝖢₄

𝗇 𝔏 incrementEntryPolynomial r a b T y m i
𝗇 𝔡 𝘜₂
𝗃 𝔨 ἀ $ parentVariableMatrix r
section

variable (r : ℕ)

𝗇 𝔑 𝔥 MvPolynomial.totalDegree_mul
𝗇 𝔠 j.val + i.val
private theorem adjugate_degree_le (M : 𝔚 𝔔)
    (hM : 𝔒) (i j : Fin r) :
    (M.adjugate i j).totalDegree ≤ r - 1 := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ k =>
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    apply 𝔑
    have hz : ((-1 : 𝔔) ^ 𝔠).totalDegree ≤ 0 := by
      simpa using MvPolynomial.totalDegree_pow (-1 : 𝔔) 𝔠
    simpa using Nat.add_le_add hz $ determinant_degree_le (M.submatrix j.succAbove i.succAbove) 𝔧 j

𝗇 𝔙 (𝔢 : 𝔅)
/-- The cleared numerator has total degree at most `r+1`. -/
theorem rawNumeratorPolynomial_degree [NeZero r]
    T response i :
    (𝔘 response i).totalDegree ≤ 𝔡 := by
  apply 𝔥 MvPolynomial.totalDegree_sub
  apply max_le
  · apply 𝔑
    apply Nat.add_le_add
    · apply 𝔥 MvPolynomial.totalDegree_rename_le
      simpa using 𝔨 determinant_degree_le $ by simp [parentVariableMatrix]
    · simp [vectorMoment]
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro j hj
    apply MvPolynomial.totalDegree_finsetSum_le
    intro k hk
    apply MvPolynomial.totalDegree_finsetSum_le
    intro l hl
    have hadj' := (MvPolynomial.totalDegree_rename_le
      (Sum.inl : parentInverseVariables r → incrementVariables r) _).trans $ adjugate_degree_le r (parentVariableMatrix r) (by simp [parentVariableMatrix]) k l
    have hA : (𝔙).totalDegree ≤ 1 := by simp [currentVariableMatrix]
    have h1 := MvPolynomial.totalDegree_mul
      𝔙 𝔣
    have h2 := MvPolynomial.totalDegree_mul
      (𝔍 : 𝔅)
      𝔇
    have h3 := MvPolynomial.totalDegree_mul
      (𝔍 *
        𝔇) 𝔓
    simp at h1
    have hv : (𝔓).totalDegree = 1 := by simp [vectorMoment]
    have hr := NeZero.ne r
    omega

theorem numeratorPolynomial_degree [NeZero r]
    T y i :
    (𝔟 i).totalDegree ≤ 𝔡 := by
  apply 𝔥 MvPolynomial.totalDegree_sub
  apply max_le $ rawNumeratorPolynomial_degree r T false i
  apply 𝔑
  simpa using rawNumeratorPolynomial_degree r T true i

/-- The complete free-moment increment has the paper's degree bound `m+r+1`. -/
theorem incrementEntryPolynomial_degree [NeZero r] a b
    T y m i :
    (𝔏).totalDegree ≤ m + r + 1 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  apply 𝔑
  exact (Nat.add_le_add (𝔥 MvPolynomial.totalDegree_rename_le
    𝔦 parentInverseEntryPolynomial_degree)
    $ numeratorPolynomial_degree r T y j ).trans_eq 𝖡₃

end

def rawIncrementEntryPolynomial (r : ℕ) (a b : ℝ) (T : 𝔄)
    (response : Bool) (m : ℕ) (i : Fin r) : 𝔅 :=
  ∑ j, 𝔊 *
    𝔘 response j

/-- The response variable appears only affinely in the entire increment polynomial. -/
theorem incrementEntryPolynomial_affine r a b
    T y m i :
    𝔏 =
      rawIncrementEntryPolynomial r a b T false m i - C y *
        rawIncrementEntryPolynomial r a b T true m i := by
  unfold incrementEntryPolynomial numeratorPolynomial rawIncrementEntryPolynomial
  have he j :
      𝔊 *
        (C y * 𝔘 true j) =
      C y * (𝔊 *
        𝔘 true j) := mul_left_comm ..
  simp_rw [mul_sub, he]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]

open RoughRegime.CombinedPolynomial

𝗇 𝔖 fun _ : Fin 1 => C
/-- Evaluation substitutes the current and parent Gram entries and the two vector families. -/
def incrementValuation (A C : 𝔄)
    (U V : Bool → 𝗢) : incrementVariables r → ℝ
  | Sum.inl x => entryValuation A 𝔖 x
  | 𝔗 => if parent then V response i else U response i

𝗇 𝔎 incrementValuation A C U V
private theorem rawNumeratorPolynomial_eval
    (A C T : 𝔄) (U V : Bool → 𝗢)
    (response : Bool) (i : Fin r) :
    eval 𝔎 (𝔘 response i) =
      incrementNumerator A C T (U response) (V response) i := by
  let f := 𝚘 $ entryValuation A 𝔖
  have hm : 𝔨 f.mapMatrix = C := by
    ext j k
    simp [f, parentVariableMatrix, entryValuation]
  have hd : eval 𝔎
      𝔛 = C.det := by
    rw [MvPolynomial.eval_rename]
    change f (parentVariableMatrix r).det = C.det
    rw [f.map_det, hm]
  have ha k l : eval 𝔎
      𝔇 = C.adjugate k l := by
    rw [MvPolynomial.eval_rename]
    have h := congrArg (fun M => M k l) 𝔨 f.map_adjugate
    aesop
  simp only [rawNumeratorPolynomial, eval_sub, eval_mul, eval_sum, eval_C, hd, ha]
  simp only [vectorMoment, eval_X, incrementValuation, Bool.false_eq_true, ↓reduceIte,
    currentVariableMatrix, rename_X, entryValuation]
  simp only [incrementNumerator, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

𝗇 𝔈 U false - y • U true
𝗇 𝔉 V false - y • V true
𝗇 𝔞 incrementNumerator A C T 𝔈 𝔉
/-- Evaluating the free polynomial gives exactly the paper's cleared numerator for `β-yμ`. -/
theorem numeratorPolynomial_eval
    A C T U V
    y i :
    eval 𝔎 (𝔟 i) =
      𝔞 i := by
  rw [numeratorPolynomial, eval_sub, eval_mul, eval_C,
    rawNumeratorPolynomial_eval, rawNumeratorPolynomial_eval]
  simp only [incrementNumerator, Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply]
  ring

/-- Evaluation recovers the actual fitted-increment polynomial for arbitrary free Gram matrices. -/
theorem incrementEntryPolynomial_eval a b
    A C T U V
    y m i :
    eval 𝔎 𝔏 =
      (parentInversePolynomial a b A C m).mulVec
        𝔞 i := by
  simp only [incrementEntryPolynomial, eval_sum, eval_mul, numeratorPolynomial_eval]
  simp_rw [MvPolynomial.eval_rename]
  rfl

𝚼

𝗇 𝔜 (EuclideanSpace.equiv (Fin r) ℝ).symm
𝗃 𝔤 ἀ a b ha hab A C T hA hC hSpecA hSpecC Q R χ hχ β βminus
/-- The exact polynomial propagates any explicitly supplied small-increment bound to U5(2). -/
theorem incrementEntryPolynomial_error [NeZero r]
    a b (ha : 𝙆) (hab : 𝙭)
    A C T (hA : A.IsHermitian) (hC : C.IsHermitian)
    (hSpecA : spectrum ℝ A ⊆ Set.Icc a b) (hSpecC : spectrum ℝ C ⊆ Set.Icc a b)
    (Q R : 𝔄 ˣ) χ
    (hχ : ‖(Q : 𝔄)‖ * ‖(↑Q⁻¹ : 𝔄)‖ ≤ χ)
    U V y ε
    (hδ : ‖𝔜
      ((matrixSimilarity Q A)⁻¹.mulVec 𝔈 -
        T.mulVec ((matrixSimilarity R C)⁻¹.mulVec 𝔉))‖ ≤ ε)
    m :
    let G := matrixSimilarity Q A
    let Cminus := matrixSimilarity R C
    ‖𝔜
      ((fun i => eval (incrementValuation G Cminus U V)
          𝔏) -
        (G⁻¹.mulVec 𝔈 -
          T.mulVec (Cminus⁻¹.mulVec 𝔉)))‖ ≤
       χ ^ 2 * b ^ 𝔡 * parentInverseErrorConstant a b r * ε *
         (𝘻 : ℕ) ^ r *
        Real.exp (-m * exteriorTau 𝖬) := by
  simp_rw [incrementEntryPolynomial_eval]
  let β := 𝔈
  let βminus := 𝔉
  have hχ0 := (mul_nonneg (norm_nonneg _) $ norm_nonneg _ ).trans hχ
  have hb := ha.trans hab
  have hM := parentInverseErrorConstant_pos a b ha hab r
  have hn := 𝔤 increment_numerator_norm_le
  have hsmall := hn.trans
        $ mul_le_mul_of_nonneg_left hδ 𝖠₃
  have he := 𝔤 increment_polynomial_error m
  apply he.trans
  apply (mul_le_mul_of_nonneg_left hsmall 𝖠₃ ).trans_eq
  ring
