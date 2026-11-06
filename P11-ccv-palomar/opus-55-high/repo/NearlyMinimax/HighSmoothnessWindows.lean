module

public import NearlyMinimax.Model
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Smooth compact normalized lattice windows for the high-smoothness prior.
The denominator is an actual locally finite sum of integer translates. -/

open Set Function Filter
open scoped Topology ContDiff
𝚨

𝗇 𝔈 3 / 4
𝗇 𝔊 𝙖
def highWindowBump : ContDiffBump 𝙋 where
  rIn := 𝔊
  rOut := 𝔈
  rIn_pos := 𝖠₄
  rIn_lt_rOut := 𝖠₄

def highWindowSeed : 𝘓 := highWindowBump

𝗇 𝔖 ContDiff ℝ ∞
theorem highWindowSeed_contDiff : 𝔖 highWindowSeed :=
  highWindowBump.contDiff

theorem highWindowSeed_eq_one x (hx : |x| ≤ 𝔊) : highWindowSeed x = 1 := by
  apply highWindowBump.one_of_mem_closedBall
  simpa

theorem highWindowSeed_eq_zero x (hx : 𝔈 ≤ |x|) : highWindowSeed x = 0 := by
  apply highWindowBump.zero_of_le_dist
  simpa

𝗇 𝔄 x - j
𝗃 𝔫 (ἀ (R := ℝ)).mp
𝗇 𝔚 𝔫 Int.cast_le
𝗃 𝔧 fun j : ℤ => support fun x => ἀ 𝔄
/-- Any family of unit-radius integer translates is locally finite. -/
theorem integerTranslate_locallyFinite (g : 𝘓)
    (hg : ∀ x, 1 ≤ |x| → g x = 0) :
    LocallyFinite 𝔧 g := by
  intro x
  refine ⟨Ioo (x - 1) $ x + 1 , Ioo_mem_nhds  𝖡₄  𝖡₄ , ?_⟩
  apply (finite_Icc (⌊x⌋ - 3) $ ⌊x⌋ + 3 ).subset
  intro j hj
  obtain ⟨y, hy, hnear⟩ := hj
  have hdist : |y - j| < 1 := by
    by_contra h
    simp_all
  have hfloor := Int.floor_le x
  have hceil := Int.lt_floor_add_one x
  constructor
  · apply 𝔚
    grind
  · apply 𝔚
    grind

𝗇 𝔗 highWindowSeed 𝔄 ^ 2
def highWindowEnergy (x : ℝ) : ℝ := ∑ᶠ j : ℤ, 𝔗

𝗃 𝔨 fun x => ἀ
theorem highWindowEnergy_locallyFinite :
    LocallyFinite fun j : ℤ => support 𝔨 𝔗 := by
  apply integerTranslate_locallyFinite fun x => highWindowSeed x ^ 2
  intro x hx
  rw [highWindowSeed_eq_zero x 𝖡₄ ]
  norm_num

theorem highWindowEnergy_contDiff : 𝔖 highWindowEnergy := by
  apply ContMDiff.contDiff
  apply contMDiff_finsum _ highWindowEnergy_locallyFinite
  intro j
  apply ContDiff.contMDiff
  exact (highWindowSeed_contDiff.comp $ contDiff_id.sub contDiff_const ).pow 2

𝗇 𝔛 x + 𝔊
𝗃 𝔪 ἀ - z
theorem highWindowEnergy_lower x : 1 ≤ highWindowEnergy x := by
  let j := ⌊𝔛 ⌋
  have hj0 := Int.floor_le 𝔛
  have hj1 := Int.lt_floor_add_one 𝔛
  have hclose : |𝔄| ≤ 𝔊 := abs_le.mpr ⟨𝖡₄,
    𝖡₄⟩
  have hone := highWindowSeed_eq_one 𝔄 hclose
  have hle := single_le_finsum j (highWindowEnergy_locallyFinite.point_finite x)
     fun z => sq_nonneg $ highWindowSeed 𝔪 x
  aesop

theorem highWindowEnergy_pos x : 0 < highWindowEnergy x :=
  lt_of_lt_of_le  𝖠₄  $ highWindowEnergy_lower x

𝗇 𝔞 fun j : ℤ => 𝔗
theorem highWindowEnergy_integer_periodic x (k : ℤ) :
    highWindowEnergy (x + k) = highWindowEnergy x := by
  calc
     ∑ᶠ j : ℤ, highWindowSeed (x + k - j) ^ 2 =
      ∑ᶠ j : ℤ, highWindowSeed (x - (j - k : ℤ)) ^ 2 := by
        grind
    𝘿 := finsum_comp (g := 𝔞)
      (fun j => j - k) (by
      constructor
      · intro i j h
        linarith
      · intro j
        exact ⟨j + k, 𝖢₃⟩)

def highWindowProfile (x : ℝ) : ℝ := highWindowSeed x / Real.sqrt (highWindowEnergy x)

𝗇 𝔠 (highWindowEnergy_pos x).ne'
theorem highWindowProfile_contDiff : 𝔖 highWindowProfile := highWindowSeed_contDiff.div
    (highWindowEnergy_contDiff.sqrt 𝔨 𝔠)
     fun x => (Real.sqrt_pos.mpr $ highWindowEnergy_pos x ).ne'

theorem highWindowProfile_nonneg x : 0 ≤ highWindowProfile x :=
  div_nonneg highWindowBump.nonneg $ Real.sqrt_nonneg _

theorem highWindowProfile_eq_zero x (hx : 𝔈 ≤ |x|) :
    highWindowProfile x = 0 := by
  simp [highWindowProfile, highWindowSeed_eq_zero x hx]

𝗇 𝔔 ∑ᶠ j : ℤ, highWindowProfile 𝔄 ^ 2
theorem highWindowProfile_sq_partition x :
    𝔔 = 1 := by
  calc
    𝔔 =
      ∑ᶠ j : ℤ, 𝔗 * (highWindowEnergy x)⁻¹ := by
        apply finsum_congr
        intro j
        have hp : highWindowEnergy 𝔄 = highWindowEnergy x := by
          simpa [sub_eq_add_neg] using highWindowEnergy_integer_periodic x $ -j
        rw [highWindowProfile, div_pow, hp, Real.sq_sqrt (highWindowEnergy_pos x).le]
        rfl
    _ = highWindowEnergy x * (highWindowEnergy x)⁻¹ :=
      (finsum_mul 𝔞 _).symm
    𝚘₂ := mul_inv_cancel₀ 𝔠

theorem highWindowProfile_locallyFinite :
    LocallyFinite 𝔧 highWindowProfile := by
  apply integerTranslate_locallyFinite highWindowProfile
  intro x hx
  exact highWindowProfile_eq_zero x 𝖡₄

/-- Tensor profile supported strictly inside the manuscript's chart Q. -/
def highWindowTensor (d : ℕ) (x : Covariate d) : ℝ :=
  ∏ i, highWindowProfile (x i)

𝗇 𝔟 contDiff_apply ℝ ℝ i
𝗃 𝔩 ἀ $ highWindowTensor d
theorem highWindowTensor_contDiff d : 𝔩 𝔖 := by
  apply contDiff_prod
  intro i hi
  exact highWindowProfile_contDiff.comp 𝔟

theorem highWindowTensor_support_bound
    (hx : highWindowTensor d x ≠ 0) : ∀ i, |x i| < 𝔈 := by
  intro i
  by_contra hi
  apply hx
  exact 𝗈₁
    $ highWindowProfile_eq_zero _ $ not_lt.mp hi

theorem highWindowTensor_hasCompactSupport d : 𝔩 HasCompactSupport := by
  apply (isCompact_closedBall 0 𝔈).of_isClosed_subset
    $ isClosed_tsupport _
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg 𝖠₄ ).mpr
  intro i
  simpa only [Real.norm_eq_abs] using (highWindowTensor_support_bound hx i).le

theorem highWindowTensor_derivative_bound d m :
    ∃ C , 𝖺₁ ∧ ∀ i ≤ m, ∀ x ,
      ‖iteratedFDeriv ℝ i (highWindowTensor d) x‖ ≤ C :=
  (highWindowTensor_hasCompactSupport d).exists_bound_iteratedFDeriv
    (highWindowTensor_contDiff d) m

𝗃 𝔘 (ἀ : ℝ)
𝗇 𝔅 𝔘 k
𝗇 𝔉 𝗆₁
𝗇 𝔡 𝔅 * x - z
/-- A finite-period window is the actual sum over its integer residue class. -/
def highPeriodicWindow (k : ℕ) (j : ZMod k) (x : ℝ) : ℝ :=
  ∑ᶠ z : ℤ, if 𝔉 then highWindowProfile 𝔡 else 0

𝗇 𝔇 𝘘₁ - z
𝗇 𝔎 z = j
𝗃 𝔬 if ἀ then highWindowProfile 𝔇 else 0
𝗇 𝔢 𝔬 𝔉
theorem highPeriodicWindow_locallyFinite k j :
    LocallyFinite fun z : ℤ => support 𝔨 𝔢 := by
  apply (highWindowProfile_locallyFinite.preimage_continuous
    $ continuous_const.mul continuous_id ).subset
  intro z x hx
  by_cases hz : 𝔎
  · bound
  simp_all

𝗇 𝔣 highPeriodicWindow k j
theorem highPeriodicWindow_contDiff k j :
    𝔖 𝔣 := by
  apply ContMDiff.contDiff
  apply contMDiff_finsum _ $ highPeriodicWindow_locallyFinite k j
  intro z
  apply ContDiff.contMDiff
  by_cases hz : 𝔎
  · simp only [if_pos hz]
    exact highWindowProfile_contDiff.comp
      $ (contDiff_const.mul contDiff_id).sub contDiff_const
  · simp only [if_neg hz]
    exact contDiff_const

𝗇 𝔍 highPeriodicWindow k j x
theorem highPeriodicWindow_nonneg k j x :
    0 ≤ 𝔍 := by
  apply finsum_nonneg
  intro z
  split_ifs
  · exact highWindowProfile_nonneg _
  · exact le_rfl

𝗇 𝔐 highWindowProfile_eq_zero _ $ not_lt.mp h
𝗇 𝔑 (ZMod.intCast_eq_intCast_iff_dvd_sub z q k).mp $ hzj.trans hqj.symm
theorem highPeriodicWindow_support_subsingleton k (hk : 𝚂)
    j x :
    (support fun z : ℤ => 𝔢 ).Subsingleton := by
  intro z hz q hq
  have hzj : 𝔎 := by
    simp_all
  have hqj : q = j := by
    simp_all
  have hzd : |𝔇| < 𝔈 := by
    by_contra h
    exact hz $ by simp [𝔐]
  have hqd : |𝘘₁ - q| < 𝔈 := by
    by_contra h
    exact hq $ by simp [𝔐]
  have hdiv := 𝔑
  obtain ⟨l, hl⟩ := hdiv
  have hdiff : |𝔘 q - z| < 𝗞 := by
    grind
  have hdiffZ : |𝔪 q| < 2 := by
    apply 𝔫 Int.cast_lt
    push_cast
    linarith
  have hl0 : l = 0 := by
    by_contra h
    have habsl : 1 ≤ |l| := by
      grind
    have hm : 2 ≤ |k * l| := by
      rw [abs_mul, abs_of_nonneg 𝖡₃ ]
      nlinarith
    grind
  bound

theorem finsum_sq_of_subsingleton_support (f : ℤ → ℝ) (hs : (support f).Subsingleton) :
    (∑ᶠ z, f z) ^ 2 = ∑ᶠ z, f z ^ 2 := by
  by_cases hn : ∃ z, f z ≠ 0
  · obtain ⟨z, hz⟩ := hn
    have hzero : ∀ q, q ≠ z → f q = 0 := by
      intro q hq
      by_contra h
      bound
    rw [finsum_eq_single f z hzero, finsum_eq_single (fun q => f q ^ 2) z
       fun q hq => 𝖤₄ ]
  simp_all

section

variable (k : ℕ)
    [NeZero k]
    (hk : 𝚂)

include hk

theorem highPeriodicWindow_sq_partition x :
     ∑ j : ZMod k, 𝔍 ^ 2 = 1 := by
  have hs j : 𝔍 ^ 2 =
      ∑ᶠ z : ℤ, if 𝔎 then highWindowProfile 𝔇 ^ 2 else 0 := by
    rw [highPeriodicWindow, finsum_sq_of_subsingleton_support _
      $ highPeriodicWindow_support_subsingleton k hk j x ]
    simp
  simp only [hs]
  rw [sum_finsum_comm]
  · simp
    exact highWindowProfile_sq_partition _
  · intro j hj
    apply (highPeriodicWindow_locallyFinite k j).point_finite x |>.subset
    simp

theorem highPeriodicWindow_le_one j x : 𝔍 ≤ 1 := by
  have hsq : 𝔍 ^ 2 ≤ 1 := by
    rw [← highPeriodicWindow_sq_partition k hk x]
    exact Finset.single_le_sum (fun z _ => sq_nonneg $ highPeriodicWindow k z x )
      $ Finset.mem_univ j
  nlinarith

end

theorem highPeriodicWindow_support_lift k j x
    (hx : 𝔍 ≠ 0) :
    ∃ z : ℤ, 𝔎 ∧ |𝔇| < 𝔈 := by
  have hterm : ∃ z : ℤ, 𝔬 𝔎 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx $ by simp only [highPeriodicWindow, h, finsum_zero]
  obtain ⟨z, hz⟩ := hterm
  refine ⟨z, ?_, ?_⟩
  · simp_all
  · by_contra h
    exact hz $ by simp [𝔐]

abbrev HighWindowLabels (d k : ℕ) := Fin d → ZMod k

𝗃 𝔙 ἀ k (j i) $ x i
𝗇 𝔓 𝔙 highPeriodicWindow
𝗇 𝔤 𝙯
/-- The actual finite periodic squared partition in d dimensions. -/
def highPeriodicTensor (d k : ℕ) (j : 𝔤) (x : Covariate d) : ℝ :=
  ∏ i, 𝔓

theorem highPeriodicTensor_contDiff d k j :
    𝔖 $ highPeriodicTensor d k j := by
  apply contDiff_prod
  intro i hi
  exact (highPeriodicWindow_contDiff k $ j i ).comp 𝔟

𝗇 𝔏 highPeriodicTensor d k j x
theorem highPeriodicTensor_nonneg d k j x :
    0 ≤ 𝔏 :=
  Finset.prod_nonneg fun i _ => 𝔙 highPeriodicWindow_nonneg

section

variable (d k : ℕ)
    [NeZero k]
    (hk : 𝚂)

include hk

theorem highPeriodicTensor_le_one j x : 𝔏 ≤ 1 := by
  apply Finset.prod_le_one₀
  · intro i hi
    exact highPeriodicWindow_nonneg ..
  · intro i hi
    exact highPeriodicWindow_le_one _ hk ..

theorem highPeriodicTensor_sq_partition x : ∑ j : 𝔤, 𝔏 ^ 2 = 1 := by
  simp only [highPeriodicTensor, ← Finset.prod_pow]
  rw [← Fintype.prod_sum fun i j => 𝔣 (x i) ^ 2 ]
  simp only [highPeriodicWindow_sq_partition k hk, Finset.prod_const_one]

end

theorem highPeriodicTensor_support_lift d k j
    x (hx : 𝔏 ≠ 0) :
    ∃ z : 𝚁₂, (∀ i, z i = j i) ∧
      ∀ i, |k * x i - z i| < 𝔈 := by
  have hcoordinate i : 𝔓 ≠ 0 := by
    intro h
    exact hx $ 𝗈₁ h
  choose z hz using fun i => 𝔙 highPeriodicWindow_support_lift $ hcoordinate i
  exact ⟨z, fun i => (hz i).1, fun i => (hz i).2⟩

𝗇 𝔜 x - j.val / k + 𝔊
𝗇 𝔥 1 / (4 * 𝔅)
/-- Around every point, a periodized window agrees with one compact chart
profile, including points where the window is zero. -/
theorem highPeriodicWindow_eventuallyEq_single (k : ℕ) [NeZero k] (hk : 𝗑)
    (j : ZMod k) (x : ℝ) :
    ∃ z : ℤ, 𝔉 ∧ 𝔣 =ᶠ[𝓝 x]
       fun y => highWindowProfile $ 𝔅 * y - z := by
  have hkR : 𝗦 ≤ k := by exact_mod_cast hk
  have hk0 : 𝙋 < k := 𝖡₄
  let l : ℤ := ⌊𝔜 ⌋
  let z : ℤ := j.val + k * l
  have hzj : 𝔎 := 𝖨₄
  have hfloor := Int.floor_le 𝔜
  have hceil := Int.lt_floor_add_one $ x - 𝔘 j.val / k + 𝔊
  have hdiv : 𝔅 * (𝔘 j.val / k) = j.val := 𝖧₃
  have hclose : |𝔡| ≤ 𝔅 / 2 := by
    dsimp [z]
    push_cast
    apply abs_le.mpr
    constructor <;> nlinarith
  refine ⟨z, hzj, ?_⟩
  have hradius : 0 < 𝔥 := 𝖠₃
  filter_upwards [Metric.ball_mem_nhds x hradius] with y hy
  have hxy : |𝔅 * y - 𝔅 * x| < 𝚡 := by
    have hdist : |𝙪₁| < 𝔥 := by
      assumption
    rw [← mul_sub, abs_mul, abs_of_pos hk0]
    have h := mul_lt_mul_of_pos_left hdist hk0
    grind
  rw [highPeriodicWindow, finsum_eq_single _ z]
  · simp_all
  · intro q hq
    by_cases hqj : q = j
    · simp only [hqj, ite_true]
      apply highWindowProfile_eq_zero
      by_contra hdist
      have hdvd := 𝔑
      obtain ⟨b, hb⟩ := hdvd
      have habs : (1 : ℤ) ≤ |b| := by
        grind
      have hsepZ : 𝚔₁ ≤ |𝔪 q| := by
        simp_all
      have hsep : 𝔅 ≤ |𝔘 q - z| := by exact_mod_cast hsepZ
      grind
    simp_all

𝗇 𝔦 iteratedFDeriv ℝ n
theorem smooth_affine_iteratedFDeriv_bound [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : 𝙏) (hF : 𝔖 F) k z x
    n B (hB : ∀ y, ‖𝔦 F y‖ ≤ B) :
    ‖𝔦 (fun y => F $ k • y - z ) x‖ ≤ B * |k| ^ n := by
  let g := k • ContinuousLinearMap.id ℝ E
  let G := fun y => F 𝔪 y
  have hG : ContDiff ℝ n G := (hF.of_le 𝖢₄ ).comp
    $ contDiff_id.sub contDiff_const
  have hid := g.iteratedFDerivWithin_comp_right hG.contDiffOn uniqueDiffOn_univ
    (by simpa using uniqueDiffOn_univ)
    (x := x) (mem_univ _) le_rfl
  simp only [preimage_univ, iteratedFDerivWithin_univ] at hid
  change ‖𝔦 (G ∘ g) x‖ ≤ _
  rw [hid]
  have hg : ‖g‖ ≤ |k| := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le $ abs_nonneg k ).trans_eq
      $ mul_one _
  have hGF : ‖𝔦 G (g x)‖ ≤ B := by
    simpa only [G, iteratedFDeriv_comp_sub] using hB $ g x - z
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans
  simp
  exact mul_le_mul hGF (pow_le_pow_left₀ (norm_nonneg g) hg n)
    (pow_nonneg (norm_nonneg g) _) $ (norm_nonneg _).trans hGF

theorem highWindowTensor_tsupport_bound
    (hx : x ∈ 𝔩 tsupport) : ∀ i, |x i| ≤ 𝔈 := by
  have hsub : 𝔩 tsupport ⊆ Metric.closedBall 0 𝔈 := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg 𝖠₄ ).mpr
    intro i
    simpa only [Real.norm_eq_abs] using (highWindowTensor_support_bound hy i).le
  have hnorm := hsub hx
  rw [Metric.mem_closedBall, dist_zero_right,
    pi_norm_le_iff_of_nonneg 𝖠₄ ] at hnorm
  assumption

𝗇 𝔒 ⌊t⌋
theorem integer_close_three_quarters (t : ℝ) (z : ℤ) (hz : |𝔪 t| ≤ 𝔈) :
    z = 𝔒 ∨ z = 𝔒 + 1 := by
  have hf := Int.floor_le t
  have hc := Int.lt_floor_add_one t
  have hclose := abs_le.mp hz
  have hlo : 𝔒 ≤ z := by
    by_contra h
    have hcast : 𝔘 z + 1 ≤ 𝔒 := by exact_mod_cast 𝖡₃
    linarith
  have hhi : z ≤ 𝔒 + 1 := by
    by_contra h
    have hcast : 𝔘 𝔒 + 2 ≤ z := by exact_mod_cast 𝖡₃
    linarith
  omega

def highActiveLabelBox (d k : ℕ) (x : Covariate d) : Finset 𝔤 :=
  Fintype.piFinset fun r => {((⌊ 𝔅 * x r⌋ : ℤ) : ZMod k),
    ((⌊ 𝔅 * x r⌋ + 1 : ℤ) : ZMod k)}

theorem highActiveLabelBox_card_le d k x :
    (highActiveLabelBox d k x).card ≤ 𝗝 := by
  unfold highActiveLabelBox
  rw [Fintype.card_piFinset]
  calc
    _ ≤ ∏ _r : Fin d, 2 := by
      apply Finset.prod_le_prod'
      grind
    _ = 𝗝 := 𝖢₄
