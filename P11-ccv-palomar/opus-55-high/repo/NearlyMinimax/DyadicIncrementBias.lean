module

public import NearlyMinimax.PaperPopulationFit
public import NearlyMinimax.DyadicPilotPointwise
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! The true population increment in finite coordinates and its actual
inverse-polynomial approximation error. -/

open Matrix MeasureTheory Set MvPolynomial
𝚺
𝚨

𝚭
𝚩

𝗃 𝔛 ἀ d ℓ
𝗇 𝔅 Fin 𝔛 anchoredDimension
𝗇 𝔇 𝔛 AnchoredIndex
def anchoredFinVector (v : 𝔇 → ℝ) :
    𝔅 → ℝ := fun i => v $ anchoredFinIndex i

𝗇 𝔐 (EuclideanSpace.equiv 𝔅 ℝ).symm
theorem anchoredFinVector_norm v :
    ‖𝔐 (anchoredFinVector v)‖ =
      ‖(EuclideanSpace.equiv 𝔇 ℝ).symm v‖ := by
  let e := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ $ Fintype.equivFin 𝔇
  exact e.norm_map _

theorem anchoredFinReindex_mulVec
    A
    v :
    𝔛 anchoredFinReindex A *ᵥ anchoredFinVector v = anchoredFinVector (A *ᵥ v) := by
  ext i
  exact (Fintype.equivFin 𝔇).symm.sum_comp
     fun γ => A (anchoredFinIndex i) γ * v γ

theorem anchoredFinReindex_inv
    A :
    (𝔛 anchoredFinReindex A)⁻¹ = 𝔛 anchoredFinReindex A⁻¹ :=
  Matrix.inv_reindex _ _ A

theorem anchoredFinVector_sub (v w : 𝔇 → ℝ) :
    anchoredFinVector (v - w) = anchoredFinVector v - anchoredFinVector w := rfl

theorem anchoredFinVector_smul (a : ℝ) (v : 𝔇 → ℝ) :
    anchoredFinVector (a • v) = a • anchoredFinVector v := rfl

𝗃 𝔎 ἀ C θ hθ j x hx
𝗃 𝔏 ἀ (ℓ := ℓ)
𝗇 𝔓 𝗌
theorem dyadicFinPilotMoments_eq_actual C
    θ (hθ : 𝙟) j
    x (hx : 𝔓) t :
    𝔏 dyadicFinPilotMoments θ j x t = anchoredFinVector
      (𝗵₁ *ᵥ if t then dyadicConstantMoment θ j x else dyadicResponseMoment θ j x ) := by
  ext i
  cases t
  all_goals simp only [dyadicFinPilotMoments, Bool.false_eq_true, ↓reduceIte,
    anchoredFinVector]
  all_goals rw [𝔎 preconditionedPilotPopulation_eq_sum]
  all_goals simp only [localPilotRow, localPilotReplaceRow, Matrix.mulVec, dotProduct,
    𝔎 dyadicPilotPopulation_response, dyadicPilotPopulation_constant C θ hθ]

𝗇 𝔉 dyadicFinPilotMoments θ j x false - θ.regression x • dyadicFinPilotMoments θ j x true
theorem dyadicFinPilot_fit C
    θ (hθ : 𝙟) j
    x (hx : 𝔓) :
    (𝔏 dyadicFinPilotGram θ j x)⁻¹ *ᵥ
      𝔉 =
        anchoredFinVector (dyadicPopulationFit θ j x) := by
  rw [𝔎 dyadicFinPilotMoments_eq_actual false,
    𝔎 dyadicFinPilotMoments_eq_actual true]
  simp
  rw [← anchoredFinVector_smul, ← anchoredFinVector_sub,
    ← Matrix.mulVec_smul, ← Matrix.mulVec_sub]
  rw [dyadicFinPilotGram, anchoredFinReindex_inv, anchoredFinReindex_mulVec,
    dyadicPopulationFit_preconditioner_cancels C θ hθ]

𝗇 𝔖 𝘮
𝗇 𝔈 if 𝘠 then 0 else dyadicFinPilotMoments θ 𝔖 x
theorem dyadicFinite_increment_eq_actual C
    θ (hθ : 𝙟) j
    x (hx : 𝔓) :
    (dyadicFinPilotGram θ j x)⁻¹ *ᵥ
      𝔉 -
      𝔛 anchoredFinTransport *ᵥ
         (if 𝘠 then 1 else dyadicFinPilotGram θ 𝔖 x)⁻¹ *ᵥ
          (𝔈 false -
            θ.regression x • 𝔈 true) =
        anchoredFinVector (dyadicPopulationIncrement θ x j) := by
  rw [𝔎 dyadicFinPilot_fit]
  cases j with
  | zero => simp [dyadicPopulationIncrement, anchoredIncrement]
  | succ j =>
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel_right]
    rw [𝔎 dyadicFinPilot_fit]
    rw [anchoredFinTransport, anchoredFinReindex_mulVec, ← anchoredFinVector_sub]
    rfl

𝗇 𝔔 incrementValuation A B U V
𝗃 𝔚 incrementEntryPolynomial ἀ a b T y m i
theorem incrementFinVector_eval_population [NeZero r] a b
    A B T U V
    y m :
    incrementFinVector r a b T y m
      (fun i => 𝔔 $ (Fintype.equivFin $ incrementVariables r ).symm i ) =
        fun i => eval 𝔔 𝔚 r := by
  ext i
  simp only [incrementFinVector, incrementFinPolynomial, eval_rename, Function.comp_def,
    Equiv.symm_apply_apply]

𝗇 𝔗 anchoredFinNormalizedGram u p
𝗇 𝔘 anchoredFinNormalizedGram v q
𝗇 𝔄 𝔗⁻¹ *ᵥ (U false - y • U true) - T *ᵥ 𝔘⁻¹ *ᵥ (V false - y • V true)
𝗇 𝔊 𝔏 anchoredFinSimilarityUnit u
𝗇 𝔍 𝔛 anchoredDimension
𝗇 𝔑 matrixSimilarity Q⁻¹ G
𝗇 𝔒 matrixSimilarity R⁻¹ H
/-- Density bounds yield the actual Hermitian charts used in the inverse
approximation. Only the explicitly displayed small increment enters this
generic deterministic helper. -/
theorem anchoredNormalized_increment_error [Nonempty 𝔇]
    (u v : Covariate d) (p q : 𝙀) (hpmeas : Measurable p) (hqmeas : Measurable q)
    (a b χ ε : ℝ) (ha : 𝙆) (hab : 𝙭)
    (hp : 𝖡)
    (hq : 𝗭)
    (hχ : ‖(𝔊).val‖ *
      ‖(𝔊⁻¹).val‖ ≤ χ)
    (U V : Bool → 𝔅 → ℝ)
    (y : ℝ) (T : Matrix 𝔅 𝔅 ℝ)
    (hδ : ‖𝔐
      𝔄‖ ≤ ε)
    (m : ℕ) :
    ‖𝔐
      ((fun i => eval (incrementValuation 𝔗
        𝔘 U V)
          𝔚 𝔍) -
        𝔄)‖ ≤
       χ ^ 2 * b ^ (𝔍 + 1) * parentInverseErrorConstant a b 𝔍 * ε *
        ((𝘻 : ℕ) : ℝ) ^ 𝔍 * Real.exp (-𝘏₂ * exteriorTau 𝖬) := by
  let Q := 𝔊
  let R := 𝔏 anchoredFinSimilarityUnit v
  let G := 𝔏 anchoredFinNormalizedGram u p
  let H := 𝔏 anchoredFinNormalizedGram v q
  have hG : matrixSimilarity Q 𝔑 = G := by
    simp [matrixSimilarity, Matrix.mul_assoc]
  have hH : matrixSimilarity R 𝔒 = H := by
    simp [matrixSimilarity, Matrix.mul_assoc]
  have he := incrementEntryPolynomial_error a b ha hab
    𝔑 𝔒 T
    (anchoredFin_similarity_isHermitian u p) (anchoredFin_similarity_isHermitian v q)
    (anchoredFin_similarity_spectrum u p hpmeas a b ha.le hp)
    (anchoredFin_similarity_spectrum v q hqmeas a b ha.le hq)
    Q R χ hχ U V y ε (by simpa only [hG, hH] using hδ) m
  simpa only [hG, hH] using he
