module

public import NearlyMinimax.AllocationBounds
public import NearlyMinimax.DegreeBounds
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-!
# Scalar factorial variance allocation for the actual quadratic profile

The coarse/fine bounds below derive their degree conditions from the profile
and degree floor. No factorial-series inequality is an input hypothesis.
-/

𝚷
𝚶

𝚨

𝗇 𝔤 C_D * S
def profileVarianceArgument (C_D S z : ℝ) : ℝ := Real.exp z / 𝔤

def profileVarianceDegree (β S z : ℝ) : ℕ := Nat.floor $ β * quadraticProfile S z

𝗇 𝔈 profileVarianceArgument C_D S z
𝗇 𝔏 profileVarianceDegree β S z
𝗇 𝔠 C₀ / 𝔈
def profileVarianceWeight (C₀ C_D β S z : ℝ) : ℝ :=
  factorialSeries 𝔏 𝔈 *
    max 1 𝔠

𝗇 𝔉 4 * β ≤ C_D
𝗇 𝔑 1 ≤ C_D
𝗃 𝔣 0 < ἀ
𝗇 𝔒 𝔣 C_D
𝗃 𝔱 0 ≤ ἀ
𝗇 𝔔 𝔱 β
𝗇 𝔧 Nat.floor_le $ mul_nonneg hβ hQ
𝗇 𝔩 2 ≤ S
theorem profileVariance_coarse_ratio
    (hβ : 𝔔) (hD1 : 𝔑) (hDβ : 𝔉) (hS : 𝔩) (hz : z ≤ 0) :
    𝔏 * 𝔈 ≤ 𝙖 := by
  have hS₀ : 𝔣 S := 𝖡₄
  have hD₀ : 𝔒 := 𝖡₄
  have hCS := mul_pos hD₀ hS₀
  have hQ : 0 ≤ quadraticProfile S z :=
    (by positivity : 0 ≤ S / 4).trans $ quadraticProfile_lower hS₀
  have hfe := mul_le_mul_of_nonneg_right 𝔧 (Real.exp_pos z).le
  have hc := mul_le_mul_of_nonneg_left (quadraticProfile_coarse_bound hS hz) hβ
  have hDm := mul_le_mul_of_nonneg_right hDβ hS₀.le
  unfold profileVarianceDegree profileVarianceArgument
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hCS).2
  linarith

𝗃 𝔰 β * ἀ ^ 2 / 4
𝗇 𝔇 𝔰 S
theorem profileVariance_fine_degree_bounds
    (hβ : 𝔔) (hDβ : 𝔉) (hS : 𝔣 S) (hz0 : 𝔱 z) (hzS : z ≤ S) :
    𝔏 ≤ 𝔤 ∧
      𝔏 * z ≤ 𝔇 := by
  have hQ : 0 ≤ quadraticProfile S z :=
    (by positivity : 0 ≤ S / 4).trans $ quadraticProfile_lower hS
  have hf := 𝔧
  have hu := mul_le_mul_of_nonneg_left (quadraticProfile_fine_upper hS hz0 hzS) hβ
  have hv := mul_le_mul_of_nonneg_left (quadraticProfile_fine_bound hS hzS) hβ
  unfold profileVarianceDegree
  constructor
  all_goals nlinarith

𝗇 𝔖 1 ≤ C₀
𝗇 𝔗 profileVarianceWeight C₀ C_D β S z
𝗇 𝔨 div_pos (Real.exp_pos z) hCS
𝗃 𝔲 2 * ἀ
theorem profileVarianceWeight_coarse_bound
    (hC : 𝔖) (hD1 : 𝔑) (hDβ : 𝔉)
    (hβ : 𝔔) (hS : 𝔩) (hz : z ≤ 0) :
    𝔗 ≤ 𝔲 C₀ := by
  have hC₀ : 𝔣 C₀ := 𝖡₄
  have hS₀ : 𝔣 S := 𝖡₄
  have hD₀ : 𝔒 := 𝖡₄
  have hCS := mul_pos hD₀ hS₀
  have hx : 𝔣 𝔈 := 𝔨
  have hxC : 𝔈 ≤ C₀ := by
    have he := Real.exp_le_one_iff.2 hz
    have hx1 := (div_le_one hCS).2 $ he.trans 𝖥₃
    exact hx1.trans hC
  have hs := factorialSeries_coarse_bound hx.le
    $ profileVariance_coarse_ratio hβ hD1 hDβ hS hz
  unfold profileVarianceWeight
  rw [max_eq_right $ (le_div_iff₀ hx).2 $ by simpa using hxC ]
  calc
    _ ≤ 𝔲 𝔈 * 𝔠 :=
      mul_le_mul_of_nonneg_right hs $ div_nonneg hC₀.le hx.le
    _ = 𝔲 C₀ := 𝖧₃

𝗇 𝔅 𝚓₂
𝗇 𝔪 𝚔₂
𝗇 𝔭 C_D ^ 2
theorem profileVarianceWeight_fine_bound
    (hC : 𝔖) (hD1 : 𝔑) (hDβ : 𝔉)
    (hβ : 𝔔) (hS : 𝔩) (hz0 : 𝔱 z) (hzS : z ≤ S) :
    𝔗 ≤
      C₀ * 𝔭 * 𝔪 * Real.exp 𝔇 := by
  have hC₀ : 𝔣 C₀ := 𝖡₄
  have hS₀ : 𝔣 S := 𝖡₄
  have hD₀ : 𝔒 := 𝖡₄
  have hCS := mul_pos hD₀ hS₀
  obtain ⟨hdeg, hprod⟩ := profileVariance_fine_degree_bounds hβ hDβ hS₀ hz0 hzS
  have he : 𝔤 * 𝔈 = Real.exp z := by
    unfold profileVarianceArgument
    field_simp
  have hweight : max 1 𝔠 ≤ 𝔅 * S := by
    apply max_le
    · nlinarith
    · apply (div_le_iff₀ 𝔨).2
      calc
        C₀ ≤ C₀ * Real.exp z := by simpa using mul_le_mul_of_nonneg_left (Real.one_le_exp_iff.2 hz0) hC₀.le
        _ = 𝔅 * S * 𝔈 := 𝖤₃
  exact factorialSeries_fine_weighted hz0 hC₀.le hCS hdeg hprod
     𝖠₃  hweight

𝗇 𝔊 𝔲 C₀ * 𝔭
/-- Both coarse and fine levels obey the same explicit envelope. -/
theorem profileVarianceWeight_uniform_bound
    (hC : 𝔖) (hD1 : 𝔑) (hDβ : 𝔉)
    (hβ : 𝔔) (hS : 𝔩) (hz : z ≤ S) :
    𝔗 ≤
      𝔊 * 𝔪 * Real.exp 𝔇 := by
  have hsq : 1 ≤ 𝔭 * 𝔪 := 𝖥₄
  have hexp : 1 ≤ Real.exp 𝔇 := Real.one_le_exp_iff.2 𝖠₃
  have hfactor : 1 ≤ 𝔭 * 𝔪 * Real.exp 𝔇 := 𝖥₃
  rcases le_or_gt z 0 with hz0 | hz0
  · apply (profileVarianceWeight_coarse_bound hC hD1 hDβ hβ hS hz0).trans
    nlinarith
  · apply (profileVarianceWeight_fine_bound hC hD1 hDβ hβ hS hz0.le hz).trans
    bound

𝗇 𝔄 𝚑₂
𝗇 𝔮 δ * j
𝗇 𝔓 C₀ * Real.exp 𝔮 / x
𝗃 𝔳 ἀ δ a C
𝗇 𝔙 𝔳 allocationLevelPosition 𝔅 x j
/-- In the explicit candidate allocation, the normalized variance argument is exactly `C₀ K_j/n`. -/
theorem actual_profileVarianceArgument_eq_cell_fraction j
    (hC : 𝔣 C₀) (hD : 𝔒) (hx : 𝔣 x) (hS : 𝔣 𝔄) :
    profileVarianceArgument C_D 𝔄
      𝔙 = 𝔓 := by
  unfold profileVarianceArgument allocationLevelPosition
  rw [Real.exp_add, Real.exp_sub, Real.exp_log hx,
    Real.exp_log $ mul_pos (mul_pos hC hD) hS ]
  field_simp

𝗇 𝔟 profileVarianceWeight C₀ C_D β 𝔄
/-- The sampling weight in the explicit allocation is exactly `max{1,n/K_j}`. -/
theorem actual_profileVarianceWeight_eq_cell_weight j
    (hC : 𝔣 C₀) (hD : 𝔒) (hx : 𝔣 x) (hS : 𝔣 𝔄) :
    𝔟
      𝔙 =
        factorialSeries (profileVarianceDegree β 𝔄
          𝔙)
          𝔓 * max 1 (x / Real.exp 𝔮) := by
  unfold profileVarianceWeight
  rw [actual_profileVarianceArgument_eq_cell_fraction j hC hD hx hS]
  field_simp

𝗇 𝔥 fun j => 𝔟 𝔙
𝗇 𝔫 Finset.mem_range.2 $ Nat.succ_pos _
/-- The paper's maximum weighted factorial variance, over all explicit candidate levels. -/
def actualVarianceMaximum (δ a C C₀ C_D γ β x : ℝ) : ℝ :=
  (Finset.range $ 𝔳 terminalAllocationLevel 𝔅 γ x + 1 ).sup'
    ⟨0, 𝔫⟩ 𝔥

𝗇 𝔍 𝔳 actualVarianceMaximum C₀ C_D γ β x
theorem actualVarianceMaximum_nonneg
    (hD : 𝔒) (hS : 𝔣 𝔄) :
    𝔱 𝔍 := by
  have hw : 0 ≤ 𝔟
      (𝔳 allocationLevelPosition 𝔅 x 0) := by
    apply mul_nonneg
    · apply factorialSeries_nonneg
      unfold profileVarianceArgument
      positivity
    simp
  apply hw.trans
  exact Finset.le_sup'
     𝔥 𝔫

𝗇 𝔜 Real.exp 𝔰 𝔄
𝗇 𝔞 𝔊 * 𝔄 ^ 2
𝗇 𝔬 allocationWidth_tendsto_atTop ha C
/-- The actual maximum variance has the proved fine-level envelope eventually. -/
theorem eventually_actualVarianceMaximum_bound
    (hδ : 𝔣 δ) (ha : 𝔣 a) (hC : 𝔖) (hD1 : 𝔑)
    (hDβ : 𝔉) (hβ : 𝔔) (hγ : 𝔱 γ) C :
    ∀ᶠ x : ℝ in atTop,
      𝔍 ≤
        𝔞 *
          𝔜 := by
  have hH : 𝔣 𝔅 := 𝖠₃
  filter_upwards [(𝔬).eventually $ eventually_ge_atTop 2 ,
    eventually_actual_allocation_level_range hδ ha hH hγ C] with x hx hz
  apply Finset.sup'_le
  intro j hj
  exact profileVarianceWeight_uniform_bound hC hD1 hDβ hβ hx (hz j hj).2

𝗇 𝔡 candidateTerminalDepth a C 𝔅 γ x
𝗇 𝔯 roundedTerminalDepth δ (Real.log x) 𝔡
𝗇 𝔛 -2 * varpi * Real.log x + η * 𝔯
/-- The scalar spatial reserve multiplied by the actual maximum factorial variance. -/
def actualAllocationVarianceRatio (δ a C C₀ C_D γ β η varpi x : ℝ) : ℝ :=
  Real.exp 𝔛 *
      𝔍

𝗇 𝔎 1 + 2 * (η + 2) / β
𝗇 𝔐 𝔰 a
𝗇 𝔢 𝔳 actualAllocationVarianceRatio C₀ C_D γ β η varpi
𝗇 𝔘 𝔢 x
𝗇 𝔚 Real.exp $ -β * 𝔄 ^ 2 / 4 - 𝔲 𝔄
𝗇 𝔦 a * 𝚋
set_option maxHeartbeats 600000 in
/-- The actual scalar variance ratio has an explicit exponentially vanishing reserve. -/
theorem eventually_actualAllocationVarianceRatio_bound
    (hδ : 𝔣 δ) (ha : 𝔣 a) (hC : 𝔖) (hD1 : 𝔑)
    (hDβ : 𝔉) (hβ : 𝔣 β) (hγ : 𝔱 γ) (hη : 𝔱 η)
    (C : ℝ) (hshift : C = 𝔎) (hcoef : 𝔐 = 𝔲 varpi) :
    ∀ᶠ x : ℝ in atTop, 𝔱 𝔘 ∧
      𝔘 ≤
        𝔞 * Real.exp (-2 * 𝔄) := by
  have hH : 𝔣 𝔅 := 𝖠₃
  have hD : 𝔒 := 𝖡₄
  have hw := 𝔬
  filter_upwards [hw.eventually $ eventually_ge_atTop 𝙉 ,
    (hw.const_mul_atTop hH).eventually $ eventually_ge_atTop 𝙠 ,
    Real.tendsto_log_atTop.eventually $ eventually_ge_atTop 𝙋 ,
    eventually_terminal_cell_log_nonneg ha hH C γ,
    eventually_actualVarianceMaximum_bound hδ ha hC hD1 hDβ hβ.le hγ C]
    with x hS hHS hL hLT hmax
  have hS₀ : 𝔣 𝔄 := 𝖡₄
  have hn : 𝔱 𝔍 :=
    actualVarianceMaximum_nonneg (δ := δ) (a := a) (C := C) (C₀ := C₀)
      (C_D := C_D) (γ := γ) (β := β) (x := x) hD hS₀
  have hdef : 𝔄 =
      𝔦 - 𝔎 := by unfold allocationWidth; rw [hshift]
  have hbudget := quadratic_allocation_budget hβ (by linarith : 0 ≤ η + 2) hS₀.le hdef
  have hbase : 𝔰 𝔦 = 𝔲 varpi * Real.log x := by
    rw [mul_pow, Real.sq_sqrt hL]
    calc
      β * (𝗅 * Real.log x) / 4 = 𝔐 * Real.log x := 𝖢₃
      𝘿 := by rw [hcoef]
  rw [hbase] at hbudget
  have ht := (roundedTerminalDepth_bounds hδ hLT).2
  have hcand : 𝔡 ≤ 𝔄 := by
    unfold candidateTerminalDepth
    have hell : 0 ≤ Real.log (𝔅 * 𝔄) := Real.log_nonneg hHS
    have hlogS : 0 ≤ Real.log 𝔄 := Real.log_nonneg 𝖡₄
    linarith [mul_nonneg hγ hlogS]
  have hr : Real.exp 𝔛 ≤
      𝔚 :=
    allocation_budget_reserve (β := β) (S := 𝔄)
      (η := η) (varpi := varpi) (L := Real.log x)
      (T := 𝔯)
      hbudget hη $ ht.trans hcand
  constructor
  · unfold actualAllocationVarianceRatio
    exact mul_nonneg 𝙫 hn
  · unfold actualAllocationVarianceRatio
    calc
      _ ≤ 𝔚 *
          (𝔞 *
            𝔜) :=
        mul_le_mul hr hmax hn 𝙫
      _ = 𝔞 *
          (𝔚 *
            𝔜) := 𝖢₃
      𝘿 := by
        rw [← Real.exp_add]
        congr 2
        ring

𝗃 𝔴 hb.mono fun x hx => ἀ
/-- Consequently `W≤1` eventually follows for this actual scalar allocation, rather than being assumed. -/
theorem actualAllocationVarianceRatio_tends_zero
    (hδ : 𝔣 δ) (ha : 𝔣 a) (hC : 𝔖) (hD1 : 𝔑)
    (hDβ : 𝔉) (hβ : 𝔣 β) (hγ : 𝔱 γ) (hη : 𝔱 η)
    C (hshift : C = 𝔎) (hcoef : 𝔐 = 𝔲 varpi) :
    Tendsto 𝔢 atTop $ 𝓝 0 := by
  have hb := eventually_actualAllocationVarianceRatio_bound hδ ha hC hD1 hDβ hβ hγ hη C hshift hcoef
  apply squeeze_zero' 𝔴 hx.1 𝔴 hx.2
  exact (tendsto_allocation_reserve_bound C₀ C_D).comp 𝔬
