module

public import NearlyMinimax.DyadicPilotPopulation
public import NearlyMinimax.PopulationInverseDerivatives
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Actual known-Gram preconditioning of the dyadic raw features and its
uniform original-law L² budget. -/

open MeasureTheory ProbabilityTheory Matrix
𝚼
𝚨

𝚭
𝚩

𝗇 𝔇 𝗎
𝗇 𝔉 𝗬₂
𝗇 𝔚 Sum.inr $ Sum.inl γ
𝗇 𝔛 Sum.inr $ Sum.inr γ
def localPilotRow (a : 𝔉) : 𝔇 :=
  match a with
  | Sum.inl (γ, _) => γ
  | 𝔚 => γ
  | 𝔛 => γ

def localPilotReplaceRow (a : 𝔉)
    (β : 𝔇) : 𝔉 :=
  match a with
  | Sum.inl (_, δ) => Sum.inl (β, δ)
  | Sum.inr $ Sum.inl _ => Sum.inr $ Sum.inl β
  | Sum.inr $ Sum.inr _ => Sum.inr $ Sum.inr β

𝗇 𝔍 localPilotReplaceRow a β
𝗇 𝔒 𝗵₁ (localPilotRow a) β
/-- Precisely `K 1_I (B⁻¹ψψᵀ, B⁻¹ψY, B⁻¹ψ)` from the manuscript. -/
def preconditionedPilotFeature (j : ℕ) (x : Covariate d)
    (a : 𝔉) (z : Observation d) : ℝ :=
  ∑ β : 𝔇, 𝔒 *
    dyadicPilotFeature j x 𝔍 z

𝗇 𝔖 preconditionedPilotFeature j x a
def preconditionedPilotPopulation (θ : RegressionParameter d)
    (j : ℕ) (x : Covariate d) (a : 𝔉) : ℝ :=
  ∫ z, 𝔖 z ∂observationLaw θ

theorem preconditionedPilotFeature_measurable j
    x (a : 𝔉) : Measurable 𝔖 :=
  Finset.measurable_sum Finset.univ fun β _ =>
    measurable_const.mul $ dyadicPilotFeature_measurable j x _

𝗇 𝔈 𝗌
𝗇 𝔎 𝙟
𝗃 𝔞 ἀ C θ hθ
𝗃 𝔘 𝔞 ἀ j x hx
𝗇 𝔓 𝔘 dyadicPilotFeature_memLp_two
theorem preconditionedPilotFeature_memLp_two C
    θ (hθ : 𝔎) j x
    (hx : 𝔈) (a : 𝔉) :
    MemLp 𝔖 2 $ observationLaw θ :=
  memLp_finsetSum Finset.univ fun β _ =>
    (𝔓 𝔍).const_mul _

𝗃 𝔜 ἀ θ j x
𝗇 𝔗 𝔜 preconditionedPilotPopulation
/-- The exact preconditioned means are the known linear transform of the
original-law raw means; no population equivalence is assumed. -/
theorem preconditionedPilotPopulation_eq_sum C
    θ (hθ : 𝔎) j x
    (hx : 𝔈) a :
    𝔗 a =
      ∑ β : 𝔇, 𝔒 *
        𝔜 dyadicPilotPopulation 𝔍 := by
  let := 𝔞 observationLaw_isProbability
  unfold preconditionedPilotPopulation preconditionedPilotFeature
  rw [integral_finsetSum _ fun β _ =>
    ((𝔓 _).integrable 𝖠₄ ).const_mul _ ]
  simp only [integral_const_mul, dyadicPilotPopulation]

𝗇 𝔏 𝔘 preconditionedPilotPopulation_eq_sum
theorem preconditionedPilotPopulation_gram C
    θ (hθ : 𝔎) j x
    (hx : 𝔈) (γ δ : 𝔇) :
    𝔗 𝙫₂ =
      𝔜 dyadicPreconditionedGram γ δ := by
  rw [𝔏]
  simp only [localPilotRow, localPilotReplaceRow, 𝔞 dyadicPilotPopulation_gram,
    dyadicPreconditionedGram, Matrix.mul_apply]

𝗇 𝔔 anchoredPreconditionedMoment 𝘎₂ 𝔜 dyadicNormalizedDensity
theorem preconditionedPilotPopulation_response C
    θ (hθ : 𝔎) j x
    (hx : 𝔈) (γ : 𝔇) :
    𝔗 𝔚 =
      𝔔
        (θ.regression ∘ dyadicCellAffine j x) γ := by
  rw [𝔏]
  simp only [localPilotRow, localPilotReplaceRow, 𝔘 dyadicPilotPopulation_response,
    dyadicKnownGram_eq_normalized, anchoredPreconditionedMoment, Matrix.mulVec, dotProduct,
    𝔞 dyadicResponseMoment_eq_normalized]

theorem preconditionedPilotPopulation_constant C
    θ (hθ : 𝔎) j x
    (hx : 𝔈) (γ : 𝔇) :
    𝔗 𝔛 =
      𝔔
        𝙃 γ := by
  rw [𝔏]
  simp only [localPilotRow, localPilotReplaceRow, 𝔞 dyadicPilotPopulation_constant,
    dyadicKnownGram_eq_normalized, anchoredPreconditionedMoment, Matrix.mulVec, dotProduct,
    𝔞 dyadicConstantMoment_eq_normalized]

𝗇 𝔄 (dyadicKnownGram (ℓ := ℓ) j x)⁻¹
theorem dyadicKnownGram_inverse_uniform_bound :
    ∃ L : ℝ, 0 < L ∧ ∀ j : ℕ, ∀ x ∈ unitCube d, ‖𝔄‖ ≤ L := by
  obtain ⟨L, hL, hbound⟩ := anchoredGram_inverse_uniform_bound
  refine ⟨L, hL, ?_⟩
  intro j x hx
  rw [dyadicKnownGram_eq_normalized]
  exact hbound _ $ gridNormalizedAnchor_mem_cube _ _ x hx

𝗇 𝔅 ∫ z, preconditionedPilotFeature j x a z ^ 2 ∂observationLaw θ
𝗇 𝔊 B (localPilotRow a) β
𝗇 𝔐 ∫ z, f β z ^ 2 ∂observationLaw θ
𝗇 𝔑 fun β _ => (hlp β).integrable_sq
/-- Known preconditioning increases the raw budget by a fixed feature-count
and inverse-Gram factor; responses still require only a second moment. -/
theorem preconditionedPilotFeature_second_le C
    θ (hθ : 𝔎) j x
    (hx : 𝔈) (a : 𝔉)
    L (hL : 𝘨) (hB : ‖𝔄‖ ≤ L) :
    𝔅 ≤
       Fintype.card 𝔇 ^ 2 * 𝖱₂ *
        dyadicPilotMomentConstant C * 𝘟 := by
  let := 𝔞 observationLaw_isProbability
  letI : Nonempty 𝔇 := ⟨localPilotRow a⟩
  let B := 𝔄
  let f β z := 𝔊 *
    dyadicPilotFeature j x 𝔍 z
  have hlp β : MemLp (f β) 2 $ observationLaw θ :=
    (𝔓 _).const_mul _
  have hfirst : 𝔅 ≤
       Fintype.card 𝔇 * ∑ β, 𝔐 := by
    have h := integral_mono (𝔘 preconditionedPilotFeature_memLp_two a).integrable_sq ((integrable_finsetSum Finset.univ 𝔑).const_mul _)
       fun z => by simpa [preconditionedPilotFeature, f, B] using
        sq_sum_le_card_mul_sum_sq
    rwa [integral_const_mul, integral_finsetSum _ 𝔑] at h
  have hb β : |𝔊| ≤ L := by
    calc
      _ = ‖𝔊‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖B‖ := matrix_real_entry_norm_le B (localPilotRow a) β
      _ ≤ L := hB
  have hcoord β : 𝔐 ≤
      𝖱₂ * dyadicPilotMomentConstant C * 𝘟 := by
    simp only [f, mul_pow, integral_const_mul]
    have hb2 : 𝔊 ^ 2 ≤ 𝖱₂ := by
      simpa only [sq_abs] using 𝗂 (hb β) 2
    exact (mul_le_mul_of_nonneg_left (𝔘 dyadicPilotFeature_second_le _)
      $ sq_nonneg _ ).trans
      (by have hc := dyadicPilotMomentConstant_pos C
          have hk := dyadicPilotScale_pos d j
          nlinarith [mul_le_mul_of_nonneg_right hb2 $ mul_nonneg hc.le hk.le ])
  apply hfirst.trans
  apply (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun β _ => hcoord β )
    $ Nat.cast_nonneg _ ).trans_eq
  simp [pow_two, mul_assoc]

/-- One fixed inverse-Gram bound is selected once for the feature geometry. -/
def pilotInverseBound (d ℓ : ℕ) : ℝ :=
  Classical.choose $ dyadicKnownGram_inverse_uniform_bound (d := d) (ℓ := ℓ)

𝗇 𝔙 pilotInverseBound d ℓ
theorem pilotInverseBound_pos d ℓ : 0 < 𝔙 :=
  (Classical.choose_spec dyadicKnownGram_inverse_uniform_bound ).1

theorem pilotInverseBound_le j x (hx : 𝔈) :
    ‖𝔄‖ ≤ 𝔙 :=
  (Classical.choose_spec dyadicKnownGram_inverse_uniform_bound ).2 j x hx

def preconditionedPilotMomentConstant (C : ModelConstants d) (ℓ : ℕ) : ℝ :=
  max 1 $ (Fintype.card 𝔇 : ℝ) ^ 2 * 𝔙 ^ 2 *
    dyadicPilotMomentConstant C

theorem preconditionedPilotMomentConstant_pos (C : ModelConstants d) ℓ :
    0 < preconditionedPilotMomentConstant C ℓ := 𝘏

/-- A single fixed-model constant bounds every actual preconditioned raw
coordinate, uniformly in dyadic level and anchor. -/
theorem preconditionedPilotFeature_uniform_second_le C
    θ (hθ : 𝔎) j x
    (hx : 𝔈) (a : 𝔉) :
    𝔅 ≤
      preconditionedPilotMomentConstant C ℓ * 𝘟 := by
  apply (𝔘 preconditionedPilotFeature_second_le a 𝔙
    (pilotInverseBound_pos d ℓ).le $ pilotInverseBound_le j x hx ).trans
  exact mul_le_mul_of_nonneg_right (le_max_right ..) (dyadicPilotScale_pos d j).le
