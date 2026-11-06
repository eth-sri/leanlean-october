module

public import NearlyMinimax.HighFramePolynomial
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Actual periodization and smooth local charts for polynomial frame fields. -/
open Set Function Filter
open scoped Topology ContDiff
𝚨
𝚩
𝚭
𝚬

𝗇 𝔏 𝙀
𝗇 𝔙 𝚁₂
𝗇 𝔥 (Int.cast_le (R := ℝ)).mp
𝗃 𝔬 fun r => ἀ r - z r
theorem integerLatticeTranslate_locallyFinite d (G : 𝔏)
    (hG : ∀ u, G u ≠ 0 → ∀ r, |u r| < 1) :
    LocallyFinite fun z : 𝔙 => support fun x : Covariate d =>
      G 𝔬 x := by
  intro x
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x 𝖠₄ , ?_⟩
  let S := fun r => Finset.Icc (⌊x r⌋ - 3) $ ⌊x r⌋ + 3
  apply (Fintype.piFinset S).finite_toSet.subset
  intro z hz
  obtain ⟨y, hy, hnear⟩ := hz
  apply Fintype.mem_piFinset.mpr
  intro r
  have hclose := abs_lt.mp $ hG 𝔬 y hy r
  have hcoord : |𝗵₂| < 1 := (show |𝗵₂| ≤ ‖𝙪₁‖ from by
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm 𝙪₁ r).trans_lt $ by assumption
  have hcoord' := abs_lt.mp hcoord
  have hfloor := Int.floor_le $ x r
  have hceil := Int.lt_floor_add_one $ x r
  apply Finset.mem_Icc.mpr
  constructor
  · apply 𝔥
    push_cast
    linarith
  · apply 𝔥
    push_cast
    linarith

𝗇 𝔓 ∀ r, (z r : ZMod k) = j r
𝗃 𝔤 ἀ d k
def highPeriodizedChart (d k : ℕ) (j : 𝔤 HighWindowLabels)
    (G : 𝔏) (x : Covariate d) : ℝ :=
  ∑ᶠ z : 𝔙, if 𝔓 then
    G fun r => 𝙦 * x r - z r else 0

𝗇 𝔫 highWindowTensor d u = 0
𝗇 𝔄 ∀ u, 𝔫 → G u = 0
𝗃 𝔯 ∀ r, ἀ r = j r
𝗇 𝔊 𝔯 z
𝗇 𝔚 k * x r
𝗃 𝔭 fun r => ἀ - z r
theorem highPeriodizedChart_locallyFinite d k (j : 𝔤 HighWindowLabels)
    (G : 𝔏) (hG0 : 𝔄) :
    LocallyFinite fun z : 𝔙 => support fun x : Covariate d =>
      if 𝔊 then G 𝔭 𝔚 else 0 := by
  have hlf := integerLatticeTranslate_locallyFinite d G $ by
    intro u hu r
    exact (highWindowTensor_support_bound (fun h => hu $ hG0 u h ) r).trans 𝖠₄
  have hc : Continuous fun x : Covariate d => fun r => 𝔚 := 𝖦₃
  apply (hlf.preimage_continuous hc).subset
  simp

𝗇 𝔐 𝔤 highPeriodizedChart j G
𝗇 𝔦 ContDiff ℝ ∞
theorem highPeriodizedChart_contDiff d k j
    G (hG : 𝔦 G)
    (hG0 : 𝔄) :
    𝔦 𝔐 := by
  apply ContMDiff.contDiff
  apply contMDiff_finsum _ $ 𝔤 highPeriodizedChart_locallyFinite j G hG0
  intro z
  apply ContDiff.contMDiff
  by_cases hz : 𝔊
  · simp only [ite_eq_left hz]
    fun_prop
  · simp only [ite_eq_right hz]
    exact contDiff_const

theorem highPeriodicWindow_term_le k j x
    (z : ℤ) (hz : 𝗆₁) :
    highWindowProfile (𝘘₁ - z) ≤ highPeriodicWindow k j x := by
  have hh := single_le_finsum z (highPeriodicWindow_locallyFinite k j |>.point_finite x)
    (fun q => (by
      split_ifs
      · exact highWindowProfile_nonneg _
      · exact le_rfl))
  aesop

𝗇 𝔡 k * y r
𝗇 𝔒 fun y => G 𝔭 𝔡
𝗇 𝔜 k ^ q
𝗇 𝔠 iteratedFDeriv ℝ q
𝗇 𝔧 𝗑
𝗇 𝔨 𝔤 highPeriodizedChart_eventuallyEq_single hk j G hG0 x
𝗃 𝔮 ‖𝔠 ἀ x‖
section

variable (d k : ℕ)
    [NeZero k]
    (hk : 𝔧)
    (j)
    (G)

include hk

𝗇 𝔉 fun a : ℤ => if a = j r then highWindowProfile $ 𝔡 - a else 0
/-- Any chart supported by the compact profile has one smooth chart formula
in a neighborhood, including points where that formula is zero. -/
theorem highPeriodizedChart_eventuallyEq_single (hG0 : 𝔄) x :
    ∃ z : 𝔙, 𝔓 ∧
      𝔐 =ᶠ[𝓝 x]
        𝔒 := by
  choose z hz he using fun r => highPeriodicWindow_eventuallyEq_single k hk (j r) $ x r
  refine ⟨z, hz, ?_⟩
  have hcoord r :=
    (continuous_apply r).continuousAt.eventually $ he r
  filter_upwards [Filter.eventually_all.mpr hcoord] with y hy
  rw [highPeriodizedChart, finsum_eq_single _ z]
  · simp_all
  · intro q hq
    by_cases hqj : 𝔯 q
    · simp only [ite_eq_left hqj]
      by_contra hnonzero
      have hprof :=
        fun h => hnonzero $ hG0 _ h
      have hqeq : q = z := by
        funext r
        have hqr : highWindowProfile (𝔡 - q r) ≠ 0 := by
          intro hh
          exact hprof $ Finset.prod_eq_zero (Finset.mem_univ r) hh
        have hqpositive :=
          lt_of_le_of_ne (highWindowProfile_nonneg _) $ Ne.symm hqr
        have hzpositive : 0 < highWindowProfile (𝔡 - z r) := by
          have hh := highPeriodicWindow_term_le k (j r) (y r) (q r) $ hqj r
          grind
        have hqs : q r ∈ support 𝔉 := by
          simp_all
        have hzs : z r ∈ support 𝔉 := by
          aesop
        exact highPeriodicWindow_support_subsingleton k  𝖡₃  (j r) (y r) hqs hzs
      exact hq hqeq
    simp_all

theorem highPeriodizedChart_derivative_bound (hG : 𝔦 G)
    (hG0 : 𝔄)
    q B (hB : ∀ u, ‖𝔠 G u‖ ≤ B) x :
    𝔮 𝔐 ≤ B * 𝔜 := by
  obtain ⟨z, hz, he⟩ := 𝔨
  rw [(he.iteratedFDeriv ℝ q).eq_of_nhds]
  have hh := smooth_affine_iteratedFDeriv_bound G hG k
    (fun r => z r ) x q B hB
  aesop

end

theorem highPeriodizedChart_tsupport_profile d (G : 𝔏)
    (hG0 : 𝔄) :
    tsupport G ⊆ tsupport (highWindowTensor d) := by
  apply closure_mono
  aesop

𝗇 𝔞 𝗝
section

variable (d k : ℕ)
    [NeZero k]
    (hk : 𝔧)

include hk

theorem highPeriodizedChart_derivative_support_lift j G
    (hG0 : 𝔄) q x
    (hx : 𝔠 𝔐 x ≠ 0) :
    ∃ z : 𝔙, 𝔊 ∧
      ∀ r, |𝔚 - z r| ≤ 3 / 4 := by
  obtain ⟨z, hz, he⟩ := 𝔨
  let A : 𝔏 := 𝔒
  have hn : 𝔠 A x ≠ 0 := by
    rwa [← (he.iteratedFDeriv ℝ q).eq_of_nhds]
  have hs := (support_iteratedFDeriv_subset q) hn
  have hc : Continuous fun y : Covariate d => fun r => 𝔡 - z r := by
    fun_prop
  exact ⟨z, hz, highWindowTensor_tsupport_bound
    $ highPeriodizedChart_tsupport_profile d G hG0 $ (tsupport_comp_subset_preimage G hc) hs ⟩

𝗇 𝔍 fun j => iteratedFDeriv ℝ q (𝔤 highPeriodizedChart j $ G j ) x ≠ 0
𝗇 𝔖 ∀ j u, 𝔫 → G j u = 0
theorem highPeriodizedChart_derivative_active_subset (G : 𝔤 HighWindowLabels → 𝔏)
    (hG0 : 𝔖) q x :
    Finset.univ.filter 𝔍 ⊆
      𝔤 highActiveLabelBox x := by
  intro j hj
  obtain ⟨z, hz, hclose⟩ := 𝔤 highPeriodizedChart_derivative_support_lift hk j (G j)
    (hG0 j) q x (Finset.mem_filter.mp hj).2
  apply Fintype.mem_piFinset.mpr
  intro r
  have he := integer_close_three_quarters 𝔚 (z r) $ hclose r
  rcases he with he | he
  · grind
  · simp only [← hz r, he, Finset.mem_insert, Finset.mem_singleton, or_true]

theorem highPeriodizedChart_derivative_overlap (G : 𝔤 HighWindowLabels → 𝔏)
    (hG0 : 𝔖) q x :
    (Finset.univ.filter 𝔍).card ≤
      𝔞 :=
  (Finset.card_le_card $ 𝔤 highPeriodizedChart_derivative_active_subset hk G hG0 q x ).trans
    $ 𝔤 highActiveLabelBox_card_le x

end

𝗃 𝔣 ἀ $ P j
𝗇 𝔇 𝔣 highFrameProfile
𝗇 𝔟 𝔤 highPeriodizedChart j 𝔇
def highFrameField (d k : ℕ) [NeZero k] (η : ℝ)
    (P : 𝔤 HighWindowLabels → 𝙣) (x : Covariate d) : ℝ :=
  η * ∑ j, 𝔟 x

theorem highFrameProfile_zero_of_window_zero P
    u (hu : 𝔫) : highFrameProfile P u = 0 := by
  simp only [highFrameProfile, hu, zero_mul]

𝗇 𝔢 𝔣 highFrameProfile_zero_of_window_zero
𝗇 𝔑 𝔤 highPeriodizedChart_contDiff j _ 𝔣 highFrameProfile_contDiff 𝔢
𝗇 𝔗 𝔤 highFrameField η P
theorem highFrameField_contDiff (d k : ℕ) [NeZero k] η
    P :
    𝔦 𝔗 := by
  change 𝔦 fun x => η • ∑ j, 𝔟 x
  apply ContDiff.const_smul
  apply ContDiff.sum
  intro j hj
  exact 𝔑

𝗇 𝔔 ∀ j, 𝔣 frameCoefficientL1 ≤ 𝗾₁
/-- The coefficient ball is independent of the polynomial degree. Its
normalization makes every derivative through the fixed order at most one
before the spatial rescaling. -/
theorem highFrameField_derivative_bound d m :
    ∃ Cfr , 𝗹 ∧ ∀ k , ∀ (_ : NeZero k), 𝔧 → ∀ η ,
      ∀ P ,
      𝔔 → ∀ q ≤ m, ∀ x ,
      𝔮 𝔗 ≤
        |η| * 𝖥 * 𝔜 := by
  obtain ⟨B, hB0, hB⟩ := highFrameProfile_derivative_bound d m
  let Cfr := max B 1
  have hCfr1 : 𝗹 := le_max_right ..
  have hCfr0 : 0 < Cfr := lt_of_lt_of_le  𝖠₄  hCfr1
  refine ⟨Cfr, hCfr1, ?_⟩
  intro k hk0 hk η P hP q hq x
  letI := hk0
  have hprofile j u :
      ‖𝔠 𝔇 u‖ ≤ 1 := by
    calc
      _ ≤ B * 𝔣 frameCoefficientL1 := 𝔣 hB q hq u
      _ ≤ Cfr * 𝗾₁ := mul_le_mul (le_max_left ..) (hP j)
        (frameCoefficientL1_nonneg _) hCfr0.le
      𝚘₂ := mul_inv_cancel₀ hCfr0.ne'
  have hchart j :
      𝔮 𝔟 ≤
        𝔜 := by
    simpa only [one_mul] using 𝔤 highPeriodizedChart_derivative_bound hk j _
      𝔣 highFrameProfile_contDiff 𝔢
      q 1 (hprofile j) x
  have hsmooth j :
      ContDiffAt ℝ q 𝔟 x :=
    ((𝔑).of_le 𝖢₄ ).contDiffAt
  have he : 𝔠 𝔗 x =
      η • ∑ j, 𝔠 𝔟 x := by
    change 𝔠
      (fun y => η • ∑ j, 𝔟 y) x = _
    rw [iteratedFDeriv_const_smul_apply' $ by
      fun_prop ]
    rw [iteratedFDeriv_fun_sum_apply fun j _ => hsmooth j ]
  rw [he, norm_smul, Real.norm_eq_abs]
  have hh := finite_sum_norm_le_active_count
    (fun j => 𝔠 𝔟 x)
    𝔞 𝔜 (pow_nonneg (Nat.cast_nonneg k) _) hchart
    $ 𝔤 highPeriodizedChart_derivative_overlap hk (fun j => 𝔇)
      (fun j => 𝔢) q x
  have hh' := mul_le_mul_of_nonneg_left hh $ abs_nonneg η
  grind

𝗇 𝔅 𝖿
𝗇 𝔈 𝗝 * cf
𝗇 𝔎 fun r => 𝗅₁
𝗇 𝔘 𝗈₂
𝗇 𝔛 ∑ r, 𝗅₁
𝗇 𝔩 q - C.smoothness
𝗇 𝔪 hCfr k hk0 hk 𝔅 P hP
/-- Original mixed partials, Euclidean Hölder modulus, and the full original
norm of the actual frame field, uniformly in degree and resolution. -/
theorem highFrameField_model_bounds (C : ModelConstants d) :
    ∃ Cfr , 𝗹 ∧ ∀ k , ∀ (_ : NeZero k), 𝔧 →
      ∀ cf , 𝚐₁ → ∀ P ,
      𝔔 →
      let F := 𝔤 highFrameField 𝔅 P
      (∀ x, |F x| ≤ 𝔞 * 𝔅) ∧
      (∀ γ : Fin d → Fin 𝔘, 𝔛 ≤ C.order → ∀ x,
        |multiPartial F 𝔎 x| ≤ 𝔈) ∧
      (∀ γ : Fin d → Fin 𝔘, 𝔛 = C.order → ∀ x y,
        |multiPartial F 𝔎 x - multiPartial F 𝔎 y| ≤
           2 * 𝔈 * euclideanNorm 𝘌 ^ C.alpha) ∧
       ∀ U , 𝘍₂ C.order C.alpha ≤
        ENNReal.ofReal ( ( (𝔘 : ℕ) ^ d + 2) * 𝔞 * cf) := by
  obtain ⟨Cfr, hCfr1, hCfr⟩ := highFrameField_derivative_bound d 𝔘
  refine ⟨Cfr, hCfr1, ?_⟩
  intro k hk0 hk cf hcf P hP
  letI := hk0
  let F := 𝔤 highFrameField 𝔅 P
  have hkR : 𝙠 ≤ k := 𝖥₄
  have hkpos : 𝙋 < k := lt_of_lt_of_le  𝖠₄  hkR
  have hA : 0 ≤ 𝔈 := 𝖠₃
  have hbound : ∀ q ≤ 𝔘, ∀ x,
      𝔮 F ≤ 𝔈 *
        k ^ 𝔩 := by
    intro q hq x
    have hh := 𝔪 q hq x
    rw [abs_of_nonneg 𝖠₃ ] at hh
    have hp : k ^ (-C.smoothness) * 𝔜 =
        𝙦 ^ 𝔩 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hkpos]
      ring
    nlinarith
  obtain ⟨hs, hm⟩ := mixed_bounds_of_scaled_derivatives C F
    (highFrameField_contDiff ..) k 𝔈 hkR hA hbound
  have hvalue x :
      |F x| ≤ 𝔞 * 𝔅 := by
    have hh := 𝔪 0  𝖡₃  x
    have hη : 0 ≤ 𝔅 := 𝖠₃
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_nonneg hη, pow_zero,
      mul_one] at hh
    linarith
  refine ⟨hvalue, hs, hm, ?_⟩
  intro U
  have hh := holderNorm_of_scaled_derivatives C U F (highFrameField_contDiff ..)
    k 𝔈 hkR hA hbound
  grind
