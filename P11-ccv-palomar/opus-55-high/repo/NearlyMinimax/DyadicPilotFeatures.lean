module

public import NearlyMinimax.PilotFeatures
public import NearlyMinimax.AnchoredExpansion
public import NearlyMinimax.PairWindowGeometry
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! The manuscript's actual raw current-cell pilot coordinates and their
original-law second-moment budget, allowing unbounded responses. -/

𝚴
𝚨

𝚭
𝚩

𝗇 𝔊 𝗎
abbrev LocalPilotIndex (d ℓ : ℕ) :=
  Sum (𝔊 × 𝔊) $ Sum 𝔊 𝔊

𝗇 𝔍 𝙉 ^ j
def dyadicPilotScale (d j : ℕ) : ℝ := 𝔍 ^ d

𝗇 𝔇 𝘟
theorem dyadicPilotScale_pos d j : 0 < 𝔇 := by
  unfold dyadicPilotScale
  positivity

𝗇 𝔐 𝗟 ^ j
def dyadicPilotCell (j : ℕ) (x : Covariate d) : 𝘶 :=
  {z | regularGridCell 𝔐  𝖠₃  z =
    regularGridCell 𝔐  𝖠₃  x}

𝗃 𝔙 ἀ j x
𝗇 𝔄 𝔙 dyadicPilotCell
theorem dyadicPilotCell_measurable j (x : Covariate d) :
    MeasurableSet 𝔄 :=
  measurableSet_eq_fun (regular_grid_cell_measurable ..) measurable_const

theorem dyadicAnchoredFeature_measurable j x
    (γ : 𝔊) : Measurable fun z => 𝔙 dyadicAnchoredFeature z γ := (𝙰₁ $ continuous_pi fun i =>
    continuous_const.mul $ (continuous_apply i).sub continuous_const ).measurable

𝗇 𝔎 𝗌
𝗇 𝔑 𝘷
/-- Current-cell normalization bounds the exact anchored monomials, including
the assigned right cube boundary. -/
theorem dyadicAnchoredFeature_abs_le_one j x z
    (hx : 𝔎) (hz : z ∈ unitCube d) (hc : z ∈ 𝔄)
    (γ : 𝔊) : |𝔙 dyadicAnchoredFeature z γ| ≤ 1 := by
  apply anchoredMonomial_abs_le_one
  intro i
  have hr := regular_grid_same_cell_radius 𝔑  𝖠₃  z x hz hx hc i
  have hk : 0 < 𝔍 := 𝖠₃
  have he : (𝗜 : ℕ) = 𝔍 := 𝖢₄
  rw [he] at hr
  rw [abs_mul, abs_of_pos hk]
  exact (mul_le_mul_of_nonneg_left hr hk.le).trans_eq 𝖧₃

𝗇 𝔈 𝗬₂
𝗇 𝔠 𝔙 dyadicAnchoredFeature z.1
𝗇 𝔏 𝔠 γ
def dyadicPilotScalar (j : ℕ) (x : Covariate d)
    (a : 𝔈) (z : Observation d) : ℝ :=
  match a with
  | 𝙫₂ => 𝔏 * 𝔠 δ
  | Sum.inr $ Sum.inl γ => z.2 * 𝔏
  | Sum.inr $ Sum.inr γ => 𝔏

𝗇 𝔡 Prod.fst ⁻¹' 𝔄
𝗇 𝔖 (𝔡).indicator
𝗇 𝔘 𝔙 dyadicPilotScalar a
/-- The actual raw coordinates: normalized Gram, response vector, and
constant-response vector. Their mean is taken under the original law. -/
def dyadicPilotFeature (j : ℕ) (x : Covariate d)
    (a : 𝔈) (z : Observation d) : ℝ :=
  𝔇 * 𝔖
    𝔘 z

𝗃 𝔢 (𝔙 dyadicAnchoredFeature_measurable ἀ).comp measurable_fst
𝗇 𝔓 𝔢 γ
theorem dyadicPilotScalar_measurable j x
    (a : 𝔈) : Measurable 𝔘 := by
  cases a with
  | inl a =>
    exact (𝔢 a.1).mul
      𝔢 a.2
  | inr a =>
    cases a with
    | inl γ =>
      exact measurable_snd.mul
        𝔓
    | inr γ => exact 𝔓

𝗇 𝔒 𝔙 dyadicPilotCell_measurable
𝗇 𝔗 𝔙 dyadicPilotFeature a
theorem dyadicPilotFeature_measurable j x
    (a : 𝔈) : Measurable 𝔗 :=
  measurable_const.mul $ (𝔙 dyadicPilotScalar_measurable a).indicator
    $ measurable_fst 𝔒

𝗇 𝔛 z.1 ∈ 𝔄
𝗇 𝔜 le_add_of_nonneg_right $ abs_nonneg z.2
theorem dyadicPilotScalar_abs_bound j x
    (a : 𝔈) z (hx : 𝔎)
    (hz : z.1 ∈ unitCube d) (hc : 𝔛) :
    |𝔘 z| ≤ 1 + |z.2| := by
  have hb := dyadicAnchoredFeature_abs_le_one (ℓ := ℓ) j x z.1 hx hz hc
  cases a with
  | inl a =>
    change |𝔠 a.1 * 𝔠 a.2| ≤ _
    rw [abs_mul]
    apply (mul_le_mul (hb a.1) (hb a.2) (abs_nonneg _) 𝖠₄ ).trans
    simp only [one_mul]
    exact 𝔜
  | inr a =>
    cases a with
    | inl γ =>
      change |z.2 * 𝔏| ≤ _
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hb γ) $ abs_nonneg z.2 ).trans 𝖡₄
    | inr γ => exact (hb γ).trans 𝔜

𝗇 𝔞 dyadicPilotScale_pos d j
𝗃 𝔣 𝔙 ἀ a z hx hz
/-- Exact geometric support and the paper's raw feature envelope. -/
theorem dyadicPilotFeature_abs_bound j x
    (a : 𝔈) z (hx : 𝔎)
    (hz : z.1 ∈ unitCube d) :
    |𝔗 z| ≤ 𝔇 *
      𝔖
        (fun z : Observation d => 1 + |z.2|) z := by
  by_cases hc : 𝔛
  · have hc' : z ∈ 𝔡 := hc
    simp only [dyadicPilotFeature, indicator_of_mem hc', abs_mul,
      abs_of_pos 𝔞]
    exact mul_le_mul_of_nonneg_left (𝔣 dyadicPilotScalar_abs_bound hc)
      (𝔞).le
  · simp [dyadicPilotFeature, hc]

𝗇 𝔔 (memLp_const 𝙠).add hy
𝗃 𝔚 ἀ C θ hθ
theorem dyadicPilotFeature_memLp_two C
    θ (hθ : 𝙟) j x
    (hx : 𝔎) (a : 𝔈) :
    MemLp 𝔗 2 $ observationLaw θ := by
  let := 𝔚 observationLaw_isProbability
  have hy : MemLp (fun z => |z.2|) 2 $ observationLaw θ := by
    simpa only [Real.norm_eq_abs] using (𝔚 observationLaw_response_memLp_two).norm
  have hd : MemLp (fun z => 𝔇 * (1 + |z.2|))
      2 $ observationLaw θ := (𝔔).const_mul _
  apply hd.mono' (𝔙 dyadicPilotFeature_measurable a).aestronglyMeasurable
  filter_upwards [𝔚 observationLaw_cube_ae] with z hz
  apply (𝔣 dyadicPilotFeature_abs_bound).trans
  by_cases hc : 𝔛 <;> simp [hc]
  exact mul_nonneg (𝔞).le 𝖠₃

𝗇 𝔅 2 * (1 + responseSecondBound C)
def dyadicPilotMomentConstant (C : ModelConstants d) : ℝ :=
  𝔅 * C.densityUpper

theorem dyadicPilotMomentConstant_pos (C : ModelConstants d) :
    0 < dyadicPilotMomentConstant C := by
  have hden := C.one_lt_densityUpper
  have hresp := responseSecondBound_pos C
  unfold dyadicPilotMomentConstant
  positivity

𝗇 𝔉 ∫ z, 𝔙 dyadicPilotFeature a z ^ 2 ∂observationLaw θ
𝗇 𝔟 𝔇 ^ 2
/-- The order-independent raw coordinate budget `C_g K_j` follows from
the actual cell volume, design density cap, and conditional error moment. -/
theorem dyadicPilotFeature_second_le C
    θ (hθ : 𝙟) j x
    (hx : 𝔎) (a : 𝔈) :
    𝔉 ≤
      dyadicPilotMomentConstant C * 𝔇 := by
  let := 𝔚 observationLaw_isProbability
  have hy : MemLp (fun z => |z.2|) 2 $ observationLaw θ := by
    simpa only [Real.norm_eq_abs] using (𝔚 observationLaw_response_memLp_two).norm
  have hd : Integrable (fun z => 𝔟 *
      𝔖 (fun z => (1 + |z.2|) ^ 2) z)
      $ observationLaw θ :=
    ((𝔔).integrable_sq.indicator
      $ measurable_fst 𝔒 ).const_mul _
  have hfirst : 𝔉 ≤
      𝔟 *
        (𝔅 * 𝘐₂ 𝔄) := by
    apply (integral_mono_ae (𝔚 dyadicPilotFeature_memLp_two j x hx a).integrable_sq hd ?_).trans
    · rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (𝔚 observationLaw_localized_response_energy_le _
        𝔒) $ sq_nonneg _
    · filter_upwards [𝔚 observationLaw_cube_ae] with z hz
      have hb := 𝔣 dyadicPilotFeature_abs_bound
      by_cases hc : 𝔛
      · have hc' : z ∈ 𝔡 := hc
        simp only [indicator_of_mem hc'] at hb ⊢
        simpa only [sq_abs, mul_pow] using 𝗂 hb 2
      simp_all
  have hmass : 𝘐₂ 𝔄 ≤ C.densityUpper / 𝔇 := by
    convert 𝔚 regularGridProbability_cap 𝔑  𝖠₃ 
      $ regularGridCell 𝔑  𝖠₃  x using 1 <;>
      simp only [dyadicPilotCell, regularGridProbability, Set.preimage, Set.mem_singleton_iff,
        dyadicPilotScale, Nat.cast_pow, Nat.cast_ofNat]
  have hfactor : 0 ≤ 𝔟 * 𝔅 := by
    have := responseSecondBound_pos C
    positivity
  have hm := mul_le_mul_of_nonneg_left hmass hfactor
  have heq : 𝔟 * 𝔅 *
      (C.densityUpper / 𝔇) =
      dyadicPilotMomentConstant C * 𝔇 := by
    unfold dyadicPilotMomentConstant
    field_simp
  linarith

def dyadicPilotPopulation (θ : RegressionParameter d) (j : ℕ) (x : Covariate d) :
    𝔈 → ℝ := fun a => ∫ z, 𝔗 z ∂observationLaw θ
