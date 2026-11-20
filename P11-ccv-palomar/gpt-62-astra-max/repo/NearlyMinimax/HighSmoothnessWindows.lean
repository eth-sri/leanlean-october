module

public import NearlyMinimax.Model

@[expose] public section

/-! Smooth compact normalized lattice windows for the high-smoothness prior.
The denominator is an actual locally finite sum of integer translates. -/

noncomputable section
open Set Function Filter
open scoped Topology BigOperators ContDiff
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

def highWindowBump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 2
  rOut := 3 / 4
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def highWindowSeed : ℝ → ℝ := highWindowBump

theorem highWindowSeed_contDiff : ContDiff ℝ ∞ highWindowSeed :=
  highWindowBump.contDiff

theorem highWindowSeed_nonneg (x : ℝ) : 0 ≤ highWindowSeed x :=
  highWindowBump.nonneg

theorem highWindowSeed_eq_one {x : ℝ} (hx : |x| ≤ 1 / 2) : highWindowSeed x = 1 := by
  apply highWindowBump.one_of_mem_closedBall
  simpa

theorem highWindowSeed_eq_zero (x : ℝ) (hx : 3 / 4 ≤ |x|) : highWindowSeed x = 0 := by
  apply highWindowBump.zero_of_le_dist
  simpa

/-- Any family of unit-radius integer translates is locally finite. -/
theorem integerTranslate_locallyFinite (g : ℝ → ℝ)
    (hg : ∀ x, 1 ≤ |x| → g x = 0) :
    LocallyFinite (fun j : ℤ => support (fun x => g (x - j))) := by
  intro x
  refine ⟨Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
  apply (finite_Icc (⌊x⌋ - 3) (⌊x⌋ + 3)).subset
  intro j hj
  obtain ⟨y, hy, hnear⟩ := hj
  have hdist : |y - j| < 1 := by
    by_contra h
    aesop
  have hfloor := Int.floor_le x
  have hceil := Int.lt_floor_add_one x
  constructor
  · apply (Int.cast_le (R := ℝ)).mp
    grind
  · apply (Int.cast_le (R := ℝ)).mp
    grind

def highWindowEnergy (x : ℝ) : ℝ := ∑ᶠ j : ℤ, highWindowSeed (x - j) ^ 2

theorem highWindowEnergy_locallyFinite :
    LocallyFinite (fun j : ℤ => support (fun x => highWindowSeed (x - j) ^ 2)) := by
  apply integerTranslate_locallyFinite (fun x => highWindowSeed x ^ 2)
  intro x hx
  rw [highWindowSeed_eq_zero x (by linarith)]
  norm_num

theorem highWindowEnergy_contDiff : ContDiff ℝ ∞ highWindowEnergy := by
  apply ContMDiff.contDiff
  apply contMDiff_finsum _ highWindowEnergy_locallyFinite
  intro j
  apply ContDiff.contMDiff
  exact (highWindowSeed_contDiff.comp (contDiff_id.sub contDiff_const)).pow 2

section
variable (x : ℝ)

theorem highWindowEnergy_lower : 1 ≤ highWindowEnergy x := by
  let j  := ⌊x + 1 / 2⌋
  have hj0 := Int.floor_le (x + 1 / 2)
  have hj1 := Int.lt_floor_add_one (x + 1 / 2)
  have hclose : |x - j| ≤ 1 / 2 := abs_le.mpr ⟨by linarith,
    by linarith⟩
  simpa [highWindowEnergy, (highWindowSeed_eq_one hclose)] using single_le_finsum j (highWindowEnergy_locallyFinite.point_finite x) (fun z => by positivity)

theorem highWindowEnergy_pos : 0 < highWindowEnergy x :=
  lt_of_lt_of_le (by norm_num) (highWindowEnergy_lower x)

theorem highWindowEnergy_integer_periodic (k : ℤ) :
    highWindowEnergy (x + k) = highWindowEnergy x := by
  calc
    _ =
      _ := by
        apply finsum_congr
        intro j
        congr 2
        push_cast
        ring
    _ = _ := finsum_comp (g := fun j : ℤ => highWindowSeed (x - j) ^ 2)
      (fun j => j - k) (by
      constructor
      · intro i j h
        simpa using h
      · intro j
        exact ⟨j + k, by ring⟩)

def highWindowProfile : ℝ := highWindowSeed x / Real.sqrt (highWindowEnergy x)

end

theorem highWindowProfile_contDiff : ContDiff ℝ ∞ highWindowProfile := highWindowSeed_contDiff.div
    (highWindowEnergy_contDiff.sqrt (fun x => (highWindowEnergy_pos x).ne'))
    (fun x => (Real.sqrt_pos.mpr (highWindowEnergy_pos x)).ne')

theorem highWindowProfile_nonneg (x : ℝ) : 0 ≤ highWindowProfile x :=
  div_nonneg (highWindowSeed_nonneg x) (Real.sqrt_nonneg _)

theorem highWindowProfile_eq_zero {x : ℝ} (hx : 3 / 4 ≤ |x|) :
    highWindowProfile x = 0 := by
  simp [highWindowProfile, highWindowSeed_eq_zero x hx]

theorem highWindowProfile_sq_partition (x : ℝ) :
    (∑ᶠ j : ℤ, highWindowProfile (x - j) ^ 2) = 1 := by
  calc
    _ =
      _ := by
        apply finsum_congr
        intro j
        have hp : highWindowEnergy (x - j) = highWindowEnergy x := by
          simpa [sub_eq_add_neg] using highWindowEnergy_integer_periodic x (-j)
        rw [highWindowProfile, div_pow, hp, Real.sq_sqrt (highWindowEnergy_pos x).le]
        rfl
    _ = _ :=
      (finsum_mul (fun j : ℤ => highWindowSeed (x - j) ^ 2) _).symm
    _ = 1 := mul_inv_cancel₀ ((highWindowEnergy_pos x).ne')

theorem highWindowProfile_locallyFinite :
    LocallyFinite (fun j : ℤ => support (fun x => highWindowProfile (x - j))) := by
  apply integerTranslate_locallyFinite highWindowProfile
  intro x hx
  exact highWindowProfile_eq_zero (by linarith)

section
variable (d : ℕ) {k : ℕ} (hk : 2 ≤ k) (j : ZMod k) {f : ℤ → ℝ}

/-- Tensor profile supported strictly inside the manuscript's chart Q. -/
def highWindowTensor (x : Covariate d) : ℝ :=
  ∏ i, highWindowProfile (x i)

theorem highWindowTensor_contDiff : ContDiff ℝ ∞ (highWindowTensor d) := by
  apply contDiff_prod
  intro i hi
  exact highWindowProfile_contDiff.comp (contDiff_apply ..)

theorem highWindowTensor_support_bound {d : ℕ} {x : Covariate d}
    (hx : highWindowTensor d x ≠ 0) : ∀ i, |x i| < 3 / 4 := by
  intro i
  by_contra hi
  apply hx
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (highWindowProfile_eq_zero (not_lt.mp hi))

theorem highWindowTensor_hasCompactSupport : HasCompactSupport (highWindowTensor d) := by
  apply (isCompact_closedBall 0 (3 / 4)).of_isClosed_subset
    (isClosed_tsupport _)
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
  intro i
  exact (highWindowTensor_support_bound hx i).le

/-- A finite-period window is the actual sum over its integer residue class. -/
def highPeriodicWindow (x : ℝ) : ℝ :=
  ∑ᶠ z : ℤ, if z = j then highWindowProfile (k * x - z) else 0

theorem highPeriodicWindow_locallyFinite :
    LocallyFinite (fun z : ℤ => support (fun x =>
      if z = j then highWindowProfile (k * x - z) else 0)) := by
  apply (highWindowProfile_locallyFinite.preimage_continuous
    (continuous_const.mul continuous_id)).subset
  intro z x hx
  by_cases hz : z = j
  · simpa [hz] using hx
  · simp [hz] at hx

theorem highPeriodicWindow_contDiff :
    ContDiff ℝ ∞ (highPeriodicWindow j) := by
  apply ContMDiff.contDiff
  apply contMDiff_finsum _ (highPeriodicWindow_locallyFinite j)
  intro z
  apply ContDiff.contMDiff
  by_cases hz : z = j
  · simp [if_pos hz]
    exact highWindowProfile_contDiff.comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const)
  · simp [if_neg hz]
    exact contDiff_const

theorem highPeriodicWindow_nonneg (k : ℕ) (j : ZMod k) (x : ℝ) :
    0 ≤ highPeriodicWindow j x := by
  apply finsum_nonneg
  intro z
  split_ifs
  · exact highWindowProfile_nonneg _
  · exact le_rfl

include hk in
theorem highPeriodicWindow_support_subsingleton (x : ℝ) :
    (support (fun z : ℤ => if z = j then
      highWindowProfile (k * x - z) else 0)).Subsingleton := by
  intro z hz q hq
  have hzj : z = j := by
    simp_all
  have hqj : q = j := by
    simp_all
  have hzd : |k * x - z| < 3 / 4 := by
    by_contra h
    exact hz (by simp [highWindowProfile_eq_zero (not_lt.mp h)])
  have hqd : |k * x - q| < 3 / 4 := by
    by_contra h
    exact hq (by simp [highWindowProfile_eq_zero (not_lt.mp h)])
  obtain ⟨l, hl⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub z q k).mp (hzj.trans hqj.symm)
  have hdiff : |(q : ℝ) - z| < 3 / 2 := by
    have h1 := abs_lt.mp hzd
    have h2 := abs_lt.mp hqd
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have hdiffZ : |q - z| < 2 := by
    apply (Int.cast_lt (R := ℝ)).mp
    push_cast
    linarith
  have hl0 : l = 0 := by
    by_contra h
    have habsl : 1 ≤ |l| := by
      have hpos := abs_pos.mpr h
      omega
    have hm : 2 ≤ |k * l| := by
      rw [abs_mul, abs_of_nonneg (by omega)]
      nlinarith
    rw [← hl] at hm
    omega
  simp [hl0] at hl
  omega

theorem finsum_sq_of_subsingleton_support (hs : (support f).Subsingleton) :
    (∑ᶠ z, f z) ^ 2 = ∑ᶠ z, f z ^ 2 := by
  by_cases hn : ∃ z, f z ≠ 0
  · obtain ⟨z, hz⟩ := hn
    have hzero : ∀ q, q ≠ z → f q = 0 := by
      intro q hq
      by_contra h
      tauto
    rw [finsum_eq_single f z hzero, finsum_eq_single (fun q => f q ^ 2) z
      (fun q hq => by simp_all)]
  · aesop

end

theorem highPeriodicWindow_sq_partition {k : ℕ} [NeZero k] (hk : 2 ≤ k) (x : ℝ) :
    (∑ j : ZMod k, highPeriodicWindow j x ^ 2) = 1 := by
  have hs (j : ZMod k) : highPeriodicWindow j x ^ 2 =
      ∑ᶠ z : ℤ, if z = j then highWindowProfile (k * x - z) ^ 2 else 0 := by
    rw [highPeriodicWindow, finsum_sq_of_subsingleton_support
      (highPeriodicWindow_support_subsingleton hk j x)]
    simp
  simp [hs]
  rw [sum_finsum_comm]
  · simp
    exact highWindowProfile_sq_partition _
  · intro j hj
    apply (highPeriodicWindow_locallyFinite j).point_finite x |>.subset
    simp

theorem highPeriodicWindow_le_one (k : ℕ) [NeZero k] (hk : 2 ≤ k)
    (j : ZMod k) (x : ℝ) : highPeriodicWindow j x ≤ 1 := by
  have hsq : highPeriodicWindow j x ^ 2 ≤ 1 := by
    rw [← highPeriodicWindow_sq_partition hk x]
    exact Finset.single_le_sum (fun z _ => sq_nonneg (highPeriodicWindow z x))
      (Finset.mem_univ j)
  nlinarith

theorem highPeriodicWindow_support_lift {k : ℕ} {j : ZMod k} {x : ℝ}
    (hx : highPeriodicWindow j x ≠ 0) :
    ∃ z : ℤ, z = j ∧ |k * x - z| < 3 / 4 := by
  have hterm : ∃ z : ℤ, (if z = j then
      highWindowProfile (k * x - z) else 0) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (by simp [highPeriodicWindow, h])
  obtain ⟨z, hz⟩ := hterm
  refine ⟨z, ?_, ?_⟩
  · aesop
  · by_contra h
    exact hz (by simp [highWindowProfile_eq_zero (not_lt.mp h)])

abbrev HighWindowLabels (d k : ℕ) := Fin d → ZMod k

/-- The actual finite periodic squared partition in d dimensions. -/
def highPeriodicTensor {d k : ℕ} (j : HighWindowLabels d k) (x : Covariate d) : ℝ :=
  ∏ i, highPeriodicWindow (j i) (x i)

section
variable {d k : ℕ} (j : HighWindowLabels d k)

theorem highPeriodicTensor_contDiff :
    ContDiff ℝ ∞ (highPeriodicTensor j) := by
  apply contDiff_prod
  intro i hi
  exact (highPeriodicWindow_contDiff (j i)).comp (contDiff_apply ..)

theorem highPeriodicTensor_nonneg (x : Covariate d) :
    0 ≤ highPeriodicTensor j x :=
  Finset.prod_nonneg (fun i _ => highPeriodicWindow_nonneg ..)

theorem highPeriodicTensor_le_one [NeZero k] (hk : 2 ≤ k)
    (j : HighWindowLabels d k) (x : Covariate d) : highPeriodicTensor j x ≤ 1 := by
  apply Finset.prod_le_one₀
  · intro i hi
    exact highPeriodicWindow_nonneg ..
  · solve_by_elim [highPeriodicWindow_le_one]

end

theorem highPeriodicTensor_sq_partition (d k : ℕ) [NeZero k] (hk : 2 ≤ k)
    (x : Covariate d) : (∑ j : HighWindowLabels d k, highPeriodicTensor j x ^ 2) = 1 := by
  simp only [highPeriodicTensor, ← Finset.prod_pow]
  rw [← Fintype.prod_sum (fun i j => highPeriodicWindow j (x i) ^ 2)]
  simp [highPeriodicWindow_sq_partition hk, Finset.prod_const_one]

section
variable {d k : ℕ} {E : Type*} {j : HighWindowLabels d k} {x : Covariate d}

theorem highPeriodicTensor_support_lift (hx : highPeriodicTensor j x ≠ 0) :
    ∃ z : Fin d → ℤ, (∀ i, (z i) = j i) ∧
      ∀ i, |k * x i - z i| < 3 / 4 := by
  have hcoordinate i : highPeriodicWindow (j i) (x i) ≠ 0 := fun h => hx (Finset.prod_eq_zero (Finset.mem_univ i) h)
  choose z hz using fun i => highPeriodicWindow_support_lift (hcoordinate i)
  exact ⟨z, fun i => (hz i).1, fun i => (hz i).2⟩

/-- Around every point, a periodized window agrees with one compact chart
profile, including points where the window is zero. -/
theorem highPeriodicWindow_eventuallyEq_single [NeZero k] (hk : 4 ≤ k)
    (j : ZMod k) (x : ℝ) :
    ∃ z : ℤ, z = j ∧ highPeriodicWindow j =ᶠ[𝓝 x]
      (fun y => highWindowProfile (k * y - z)) := by
  have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  let l  := ⌊x - j.val / k + 1 / 2⌋
  let z  := j.val + k * l
  have hzj : z = j := by simp [z, ZMod.natCast_zmod_val]
  have hfloor := Int.floor_le (x - j.val / k + 1 / 2)
  have hceil := Int.lt_floor_add_one (x - j.val / k + 1 / 2)
  have hdiv : (k : ℝ) * (j.val / k) = j.val := by field_simp
  have hclose : |k * x - z| ≤ k / 2 := by
    dsimp [z]
    push_cast
    apply abs_le.mpr
    dsimp [l]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hfloor hk0.le,
      mul_lt_mul_of_pos_left hceil hk0]
  refine ⟨z, hzj, ?_⟩
  have hradius : 0 < 1 / (4 * (k : ℝ)) := by positivity
  filter_upwards [Metric.ball_mem_nhds x hradius] with y hy
  have hxy : |k * y - k * x| < 1 / 4 := by
    have hdist : |y - x| < 1 / (4 * k) := by
      assumption
    rw [← mul_sub, abs_mul, abs_of_pos hk0]
    have h := mul_lt_mul_of_pos_left hdist hk0
    grind
  rw [highPeriodicWindow, finsum_eq_single _ z]
  · simp_all
  · intro q hq
    by_cases hqj : q = j
    · simp [hqj]
      apply highWindowProfile_eq_zero
      by_contra hdist
      obtain ⟨b, hb⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub z q k).mp (hzj.trans hqj.symm)
      have hb0 : b ≠ 0 := by
        intro hb0
        simp [hb0] at hb
        omega
      have habs : 1 ≤ |b| := by
        have hpos := abs_pos.mpr hb0
        omega
      have hsep : k ≤ |(q : ℝ) - z| := by exact_mod_cast (by
        rw [hb, abs_mul, abs_of_nonneg (by omega)]
        nlinarith)
      have htri : |(q : ℝ) - z| ≤ |k * y - q| +
          |k * y - k * x| + |k * x - z| := by
        calc
          _ = |(q - k * y) + (k * y - k * x) +
              (k * x - z)| := by simp
          _ ≤ _ := abs_add_le _ _
          _ ≤ |q - k * y| + |k * y - k * x| +
              |k * x - z| := by
                gcongr
                exact abs_add_le _ _
          _ = _ := by rw [abs_sub_comm (q : ℝ) (k * y)]
      linarith
    · simp_all

theorem smooth_affine_iteratedFDeriv_bound [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : E → ℝ} (hF : ContDiff ℝ ∞ F) (k : ℝ) (z x : E)
    {n : ℕ} {B : ℝ} (hB : ∀ y, ‖iteratedFDeriv ℝ n F y‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (fun y => F (k • y - z)) x‖ ≤ B * |k| ^ n := by
  let g  := k • ContinuousLinearMap.id ℝ E
  let G  := fun y => F (y - z)
  have hG : ContDiff ℝ n G := (hF.of_le (by simp)).comp
    (contDiff_id.sub contDiff_const)
  have hid := g.iteratedFDerivWithin_comp_right hG.contDiffOn uniqueDiffOn_univ
    (by simp)
    (x := x) (mem_univ _) le_rfl
  simp [preimage_univ, iteratedFDerivWithin_univ] at hid
  change ‖iteratedFDeriv ℝ n (G ∘ g) x‖ ≤ _
  rw [hid]
  have hg : ‖g‖ ≤ |k| := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (abs_nonneg k)).trans_eq
      (mul_one _)
  have hGF : ‖iteratedFDeriv ℝ n G (g x)‖ ≤ B := by
    simpa only [G, iteratedFDeriv_comp_sub] using hB (g x - z)
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp
  exact mul_le_mul hGF (by bound)
    (by positivity) ((norm_nonneg _).trans hGF)

theorem highWindowTensor_tsupport_bound
    (hx : x ∈ tsupport (highWindowTensor d)) : ∀ i, |x i| ≤ 3 / 4 := by
  have hsub : tsupport (highWindowTensor d) ⊆ Metric.closedBall 0 (3 / 4) := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro i
    exact (highWindowTensor_support_bound hy i).le
  have hnorm := hsub hx
  rw [Metric.mem_closedBall, dist_zero_right,
    pi_norm_le_iff_of_nonneg (by norm_num)] at hnorm
  assumption

end

variable (d k : ℕ) (x : Covariate d) {t : ℝ}

theorem integer_close_three_quarters {z : ℤ} (hz : |t - z| ≤ 3 / 4) :
    z = ⌊t⌋ ∨ z = ⌊t⌋ + 1 := by
  have hf := Int.floor_le t
  have hc := Int.lt_floor_add_one t
  have hclose := abs_le.mp hz
  have hlo : ⌊t⌋ ≤ z := by
    by_contra h
    have hcast : (z : ℝ) + 1 ≤ ⌊t⌋ := by exact_mod_cast (by omega)
    linarith
  have hhi : z ≤ ⌊t⌋ + 1 := by
    by_contra h
    have hcast : (⌊t⌋ : ℝ) + 2 ≤ z := by exact_mod_cast (by omega)
    linarith
  omega

def highActiveLabelBox : Finset (HighWindowLabels d k) :=
  Fintype.piFinset (fun r => {((⌊k * x r⌋ : ℤ) : ZMod k),
    ((⌊k * x r⌋ + 1 : ℤ) : ZMod k)})

theorem highActiveLabelBox_card_le :
    (highActiveLabelBox d k x).card ≤ 2 ^ d := by
  unfold highActiveLabelBox
  rw [Fintype.card_piFinset]
  calc
    _ ≤ _ := by
      apply Finset.prod_le_prod'
      solve_by_elim [Finset.card_insert_le]
    _ = _ := by simp

end NearlyMinimax
