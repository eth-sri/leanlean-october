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

theorem highWindowSeed_nonneg x : 0 ≤ highWindowSeed x :=
  highWindowBump.nonneg

theorem highWindowSeed_eq_one x (hx : |x| ≤ 1 / 2) : highWindowSeed x = 1 := by
  apply highWindowBump.one_of_mem_closedBall
  simpa [Metric.mem_closedBall, Real.dist_eq, highWindowBump] using hx

theorem highWindowSeed_eq_zero x (hx : 3 / 4 ≤ |x|) : highWindowSeed x = 0 := by
  apply highWindowBump.zero_of_le_dist
  simpa [Real.dist_eq, highWindowBump] using hx

/-- Any family of unit-radius integer translates is locally finite. -/
theorem integerTranslate_locallyFinite (g : ℝ → ℝ)
    (hg : ∀ x, 1 ≤ |x| → g x = 0) :
    LocallyFinite (fun j : ℤ => support (fun x  => g (x - j))) := by
  intro x
  refine ⟨Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
  apply (finite_Icc (⌊x⌋ - 3) (⌊x⌋ + 3)).subset
  intro j hj
  obtain ⟨y, hy, hnear⟩ := hj
  have hdist : |y - j| < 1 := by
    by_contra h
    exact hy (hg _ (not_lt.mp h))
  have hd := abs_lt.mp hdist
  have hfloor := Int.floor_le x
  have hceil := Int.lt_floor_add_one x
  constructor
  · apply (Int.cast_le (R := ℝ)).mp
    push_cast
    linarith [hnear.1, hnear.2]
  · apply (Int.cast_le (R := ℝ)).mp
    push_cast
    linarith [hnear.1, hnear.2]

def highWindowEnergy x  := ∑ᶠ j : ℤ, highWindowSeed (x - j) ^ 2

theorem highWindowEnergy_locallyFinite :
    LocallyFinite (fun j : ℤ => support (fun x  => highWindowSeed (x - j) ^ 2)) := by
  apply integerTranslate_locallyFinite (fun x => highWindowSeed x ^ 2)
  intro x hx
  rw [highWindowSeed_eq_zero x (by linarith)]
  norm_num

theorem highWindowEnergy_contDiff : ContDiff ℝ ∞ highWindowEnergy := by
  unfold highWindowEnergy
  apply ContMDiff.contDiff
  apply contMDiff_finsum _ highWindowEnergy_locallyFinite
  intro j
  apply ContDiff.contMDiff
  exact (highWindowSeed_contDiff.comp (contDiff_id.sub contDiff_const)).pow 2

theorem highWindowEnergy_lower x : 1 ≤ highWindowEnergy x := by
  let j  := ⌊x + 1 / 2⌋
  have hj0 := Int.floor_le (x + 1 / 2)
  have hj1 := Int.lt_floor_add_one (x + 1 / 2)
  have hclose : |x - j| ≤ 1 / 2 := abs_le.mpr ⟨by dsimp [j]; linarith,
    by dsimp [j]; linarith⟩
  have hone := highWindowSeed_eq_one (x - j) hclose
  have hle := single_le_finsum j (highWindowEnergy_locallyFinite.point_finite x)
    (fun z : ℤ => sq_nonneg (highWindowSeed (x - z)))
  simpa [highWindowEnergy, hone] using hle

theorem highWindowEnergy_pos x : 0 < highWindowEnergy x :=
  lt_of_lt_of_le (by norm_num) (highWindowEnergy_lower x)

theorem highWindowEnergy_integer_periodic x (k : ℤ) :
    highWindowEnergy (x + k) = highWindowEnergy x := by
  unfold highWindowEnergy
  calc
    (∑ᶠ j : ℤ, highWindowSeed (x + k - j) ^ 2) =
      ∑ᶠ j : ℤ, highWindowSeed (x - (j - k : ℤ)) ^ 2 := by
        apply finsum_congr
        intro j
        congr 2
        push_cast
        ring
    _ = _ := finsum_comp (g := fun j : ℤ => highWindowSeed (x - j) ^ 2)
      (fun j : ℤ => j - k) (by
      constructor
      · intro i j h
        simp_all
      · intro j
        exact ⟨j + k, by dsimp; ring⟩)

def highWindowProfile x  := highWindowSeed x / Real.sqrt (highWindowEnergy x)

theorem highWindowProfile_contDiff : ContDiff ℝ ∞ highWindowProfile := highWindowSeed_contDiff.div
    (highWindowEnergy_contDiff.sqrt (fun x => (highWindowEnergy_pos x).ne'))
    (fun x => (Real.sqrt_pos.mpr (highWindowEnergy_pos x)).ne')

theorem highWindowProfile_nonneg x : 0 ≤ highWindowProfile x :=
  div_nonneg (highWindowSeed_nonneg x) (Real.sqrt_nonneg _)

theorem highWindowProfile_eq_zero x (hx : 3 / 4 ≤ |x|) :
    highWindowProfile x = 0 := by
  simp [highWindowProfile, highWindowSeed_eq_zero x hx]

theorem highWindowProfile_sq_partition x :
    (∑ᶠ j : ℤ, highWindowProfile (x - j) ^ 2) = 1 := by
  have hE := (highWindowEnergy_pos x).ne'
  calc
    (∑ᶠ j : ℤ, highWindowProfile (x - j) ^ 2) =
      ∑ᶠ j : ℤ, highWindowSeed (x - j) ^ 2 * (highWindowEnergy x)⁻¹ := by
        apply finsum_congr
        intro j
        have hp : highWindowEnergy (x - j) = highWindowEnergy x := by
          simpa [sub_eq_add_neg] using highWindowEnergy_integer_periodic x (-j)
        rw [highWindowProfile, div_pow, hp, Real.sq_sqrt (highWindowEnergy_pos x).le]
        rfl
    _ = highWindowEnergy x * (highWindowEnergy x)⁻¹ :=
      (finsum_mul (fun j : ℤ => highWindowSeed (x - j) ^ 2) _).symm
    _ = 1 := mul_inv_cancel₀ hE

theorem highWindowProfile_locallyFinite :
    LocallyFinite (fun j : ℤ => support (fun x  => highWindowProfile (x - j))) := by
  apply integerTranslate_locallyFinite highWindowProfile
  intro x hx
  exact highWindowProfile_eq_zero x (by linarith)

/-- Tensor profile supported strictly inside the manuscript's chart Q. -/
def highWindowTensor d (x : Covariate d)  :=
  ∏ i, highWindowProfile (x i)

theorem highWindowTensor_contDiff d : ContDiff ℝ ∞ (highWindowTensor d) := by
  apply contDiff_prod
  intro i hi
  exact highWindowProfile_contDiff.comp (contDiff_apply ℝ ℝ i)

theorem highWindowTensor_support_bound {d } {x }
    (hx : highWindowTensor d x ≠ 0) : ∀ i, |x i| < 3 / 4 := by
  intro i
  by_contra hi
  apply hx
  solve_by_elim [Finset.prod_eq_zero, Finset.mem_univ, highWindowProfile_eq_zero, not_lt.mp]

theorem highWindowTensor_hasCompactSupport d : HasCompactSupport (highWindowTensor d) := by
  apply (isCompact_closedBall (0 : Covariate d) (3 / 4 : ℝ)).of_isClosed_subset
    (isClosed_tsupport _)
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)).mpr
  intro i
  simpa only [Real.norm_eq_abs] using (highWindowTensor_support_bound hx i).le

theorem highWindowTensor_derivative_bound d m :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ m, ∀ x ,
      ‖iteratedFDeriv ℝ i (highWindowTensor d) x‖ ≤ C :=
  (highWindowTensor_hasCompactSupport d).exists_bound_iteratedFDeriv
    (highWindowTensor_contDiff d) m

/-- A finite-period window is the actual sum over its integer residue class. -/
def highPeriodicWindow k j x  :=
  ∑ᶠ z : ℤ, if (z : ZMod k) = j then highWindowProfile ((k : ℝ) * x - z) else 0

theorem highPeriodicWindow_locallyFinite k (j : ZMod k) :
    LocallyFinite (fun z : ℤ => support (fun x  =>
      if z = j then highWindowProfile (k * x - z) else 0)) := by
  apply (highWindowProfile_locallyFinite.preimage_continuous
    (continuous_const.mul continuous_id)).subset
  intro z x hx
  by_cases hz : (z : ZMod k) = j
  · simpa [hz] using hx
  · simp [hz] at hx

theorem highPeriodicWindow_contDiff k j :
    ContDiff ℝ ∞ (highPeriodicWindow k j) := by
  unfold highPeriodicWindow
  apply ContMDiff.contDiff
  apply contMDiff_finsum _ (highPeriodicWindow_locallyFinite k j)
  intro z
  apply ContDiff.contMDiff
  by_cases hz : (z : ZMod k) = j
  · simp only [if_pos hz]
    exact highWindowProfile_contDiff.comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const)
  · simp only [if_neg hz]
    exact contDiff_const

theorem highPeriodicWindow_nonneg k j x :
    0 ≤ highPeriodicWindow k j x := by
  apply finsum_nonneg
  intro z
  split_ifs
  · exact highWindowProfile_nonneg _
  · exact le_rfl

theorem highPeriodicWindow_support_subsingleton k (hk : 2 ≤ k)
    (j : ZMod k) x :
    (support (fun z : ℤ => if z = j then
      highWindowProfile (k * x - z) else 0)).Subsingleton := by
  intro z hz q hq
  have hzj : (z : ZMod k) = j := by
    by_contra h
    exact hz (by simp [h])
  have hqj : (q : ZMod k) = j := by
    by_contra h
    exact hq (by simp [h])
  have hzd : |(k : ℝ) * x - z| < 3 / 4 := by
    by_contra h
    exact hz (by simp [highWindowProfile_eq_zero _ (not_lt.mp h)])
  have hqd : |(k : ℝ) * x - q| < 3 / 4 := by
    by_contra h
    exact hq (by simp [highWindowProfile_eq_zero _ (not_lt.mp h)])
  have hdiv  := (ZMod.intCast_eq_intCast_iff_dvd_sub z q k).mp
    (hzj.trans hqj.symm)
  obtain ⟨l, hl⟩ := hdiv
  have hdiff : |(q : ℝ) - z| < 3 / 2 := by
    have h1 := abs_lt.mp hzd
    have h2 := abs_lt.mp hqd
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have hdiffZ : |q - z| < (2 : ℤ) := by
    apply (Int.cast_lt (R := ℝ)).mp
    push_cast
    linarith
  have hkZ : (2 : ℤ) ≤ k := by exact_mod_cast hk
  have hl0 : l = 0 := by
    by_contra h
    have habsl : (1 : ℤ) ≤ |l| := by
      have hpos := abs_pos.mpr h
      omega
    have hm : (2 : ℤ) ≤ |(k : ℤ) * l| := by
      rw [abs_mul, abs_of_nonneg (by omega : (0 : ℤ) ≤ k)]
      nlinarith
    rw [← hl] at hm
    omega
  simp only [hl0, mul_zero] at hl
  omega

theorem finsum_sq_of_subsingleton_support (f : ℤ → ℝ) (hs : (support f).Subsingleton) :
    (∑ᶠ z, f z) ^ 2 = ∑ᶠ z, f z ^ 2 := by
  by_cases hn : ∃ z, f z ≠ 0
  · obtain ⟨z, hz⟩ := hn
    have hzero : ∀ q, q ≠ z → f q = 0 := by
      intro q hq
      by_contra h
      exact hq (hs h hz)
    rw [finsum_eq_single f z hzero, finsum_eq_single (fun q => f q ^ 2) z
      (fun q hq => by rw [hzero q hq]; norm_num)]
  simp_all

section
variable (k : ℕ) [NeZero k] (hk : 2 ≤ k)
include hk

theorem highPeriodicWindow_sq_partition  x :
    (∑ j : ZMod k, highPeriodicWindow k j x ^ 2) = 1 := by
  have hs (j : ZMod k) : highPeriodicWindow k j x ^ 2 =
      ∑ᶠ z : ℤ, if (z : ZMod k) = j then highWindowProfile ((k : ℝ) * x - z) ^ 2 else 0 := by
    rw [highPeriodicWindow, finsum_sq_of_subsingleton_support _
      (highPeriodicWindow_support_subsingleton k hk j x)]
    apply finsum_congr
    intro z
    split_ifs <;> simp
  simp only [hs]
  rw [sum_finsum_comm]
  · simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact highWindowProfile_sq_partition _
  · intro j hj
    apply (highPeriodicWindow_locallyFinite k j).point_finite x |>.subset
    simp_all

theorem highPeriodicWindow_le_one 
    j x : highPeriodicWindow k j x ≤ 1 := by
  nlinarith [highPeriodicWindow_sq_partition k hk x, Finset.single_le_sum (fun z _ => sq_nonneg (highPeriodicWindow k z x))       (Finset.mem_univ j)]
end


theorem highPeriodicWindow_support_lift k j x
    (hx : highPeriodicWindow k j x ≠ 0) :
    ∃ z : ℤ, z = j ∧ |k * x - z| < 3 / 4 := by
  have hterm : ∃ z : ℤ, (if (z : ZMod k) = j then
      highWindowProfile ((k : ℝ) * x - z) else 0) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (by simp only [highPeriodicWindow, h, finsum_zero])
  obtain ⟨z, hz⟩ := hterm
  grind only [highWindowProfile_eq_zero]

abbrev HighWindowLabels d k := Fin d → ZMod k

section
variable (d k : ℕ)

/-- The actual finite periodic squared partition in d dimensions. -/
def highPeriodicTensor  (j : HighWindowLabels d k) (x : Covariate d)  :=
  ∏ i, highPeriodicWindow k (j i) (x i)

theorem highPeriodicTensor_contDiff  j :
    ContDiff ℝ ∞ (highPeriodicTensor d k j) := by
  apply contDiff_prod
  intro i hi
  exact (highPeriodicWindow_contDiff k (j i)).comp (contDiff_apply ℝ ℝ i)

theorem highPeriodicTensor_nonneg  j x :
    0 ≤ highPeriodicTensor d k j x :=
  Finset.prod_nonneg (fun i _ => highPeriodicWindow_nonneg k (j i) (x i))

section
variable [NeZero k] (hk : 2 ≤ k)
include hk

theorem highPeriodicTensor_le_one  
    j x : highPeriodicTensor d k j x ≤ 1 := by
  apply Finset.prod_le_one₀
  · intro i hi
    exact highPeriodicWindow_nonneg _ _ _
  · intro i hi
    exact highPeriodicWindow_le_one _ hk _ _

theorem highPeriodicTensor_sq_partition  
    x : (∑ j : HighWindowLabels d k, highPeriodicTensor d k j x ^ 2) = 1 := by
  simp only [highPeriodicTensor, ← Finset.prod_pow]
  rw [← Fintype.prod_sum (fun i (j : ZMod k) => highPeriodicWindow k j (x i) ^ 2)]
  simp only [highPeriodicWindow_sq_partition k hk, Finset.prod_const_one]
end


theorem highPeriodicTensor_support_lift  j
    x (hx : highPeriodicTensor d k j x ≠ 0) :
    ∃ z : Fin d → ℤ, (∀ i, (z i) = j i) ∧
      ∀ i, |k * x i - z i| < 3 / 4 := by
  have hcoordinate (i : Fin d) : highPeriodicWindow k (j i) (x i) ≠ 0 := by
    intro h
    exact hx (Finset.prod_eq_zero (Finset.mem_univ i) h)
  choose z hz using fun i => highPeriodicWindow_support_lift k (j i) (x i) (hcoordinate i)
  exact ⟨z, fun i => (hz i).1, fun i => (hz i).2⟩
end


/-- Around every point, a periodized window agrees with one compact chart
profile, including points where the window is zero. -/
theorem highPeriodicWindow_eventuallyEq_single k [NeZero k] (hk : 4 ≤ k)
    (j : ZMod k) x :
    ∃ z : ℤ, z = j ∧ highPeriodicWindow k j =ᶠ[𝓝 x]
      (fun y => highWindowProfile (k * y - z)) := by
  have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  let l  := ⌊x - (j.val : ℝ) / k + 1 / 2⌋
  let z  := (j.val : ℤ) + (k : ℤ) * l
  have hzj : (z : ZMod k) = j := by simp [z, ZMod.natCast_zmod_val]
  have hfloor := Int.floor_le (x - (j.val : ℝ) / k + 1 / 2)
  have hceil := Int.lt_floor_add_one (x - (j.val : ℝ) / k + 1 / 2)
  have hdiv : (k : ℝ) * ((j.val : ℝ) / k) = j.val := by field_simp
  have hclose : |(k : ℝ) * x - z| ≤ (k : ℝ) / 2 := by
    dsimp [z]
    push_cast
    apply abs_le.mpr
    dsimp [l]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hfloor hk0.le,
      mul_lt_mul_of_pos_left hceil hk0]
  refine ⟨z, hzj, ?_⟩
  have hradius : 0 < 1 / (4 * (k : ℝ)) := by positivity
  filter_upwards [Metric.ball_mem_nhds x hradius] with y hy
  have hxy : |(k : ℝ) * y - (k : ℝ) * x| < 1 / 4 := by
    have hdist : |y - x| < 1 / (4 * (k : ℝ)) := by
      bound
    rw [← mul_sub, abs_mul, abs_of_pos hk0]
    have h := mul_lt_mul_of_pos_left hdist hk0
    have hid : (k : ℝ) * (1 / (4 * (k : ℝ))) = 1 / 4 := by field_simp
    simpa only [hid] using h
  rw [highPeriodicWindow, finsum_eq_single _ z]
  · simp only [hzj, ite_true]
  · intro q hq
    by_cases hqj : (q : ZMod k) = j
    · simp only [hqj, ite_true]
      apply highWindowProfile_eq_zero
      by_contra hdist
      have hqclose  := not_le.mp hdist
      have hdvd  := (ZMod.intCast_eq_intCast_iff_dvd_sub z q k).mp
        (hzj.trans hqj.symm)
      obtain ⟨b, hb⟩ := hdvd
      have hb0 : b ≠ 0 := by
        intro hb0
        simp only [hb0, mul_zero] at hb
        exact hq (by omega)
      have habs : (1 : ℤ) ≤ |b| := by
        have hpos := abs_pos.mpr hb0
        omega
      have hsepZ : (k : ℤ) ≤ |q - z| := by
        simp_all
      have hsep : (k : ℝ) ≤ |(q : ℝ) - z| := by exact_mod_cast hsepZ
      have htri : |(q : ℝ) - z| ≤ |(k : ℝ) * y - q| +
          |(k : ℝ) * y - (k : ℝ) * x| + |(k : ℝ) * x - z| := by
        calc
          _ = |(q - (k : ℝ) * y) + ((k : ℝ) * y - (k : ℝ) * x) +
              ((k : ℝ) * x - z)| := by congr 1; ring
          _ ≤ |(q - (k : ℝ) * y) + ((k : ℝ) * y - (k : ℝ) * x)| +
              |(k : ℝ) * x - z| := abs_add_le _ _
          _ ≤ |q - (k : ℝ) * y| + |(k : ℝ) * y - (k : ℝ) * x| +
              |(k : ℝ) * x - z| := by
                gcongr
                exact abs_add_le _ _
          _ = _ := by rw [abs_sub_comm (q : ℝ) ((k : ℝ) * y)]
      linarith
    · simp only [hqj, ite_false]

theorem smooth_affine_iteratedFDeriv_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : E → ℝ) (hF : ContDiff ℝ ∞ F) (k : ℝ) (z x : E)
    (n : ℕ) (B : ℝ) (hB : ∀ y, ‖iteratedFDeriv ℝ n F y‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (fun y => F (k • y - z)) x‖ ≤ B * |k| ^ n := by
  let g  := k • ContinuousLinearMap.id ℝ E
  let G  := fun y => F (y - z)
  have hG : ContDiff ℝ n G := (hF.of_le (by simp)).comp
    (contDiff_id.sub contDiff_const)
  have hid := g.iteratedFDerivWithin_comp_right hG.contDiffOn uniqueDiffOn_univ
    (by simp_all)
    (x := x) (mem_univ _) (i := n) le_rfl
  simp only [preimage_univ, iteratedFDerivWithin_univ] at hid
  change ‖iteratedFDeriv ℝ n (G ∘ g) x‖ ≤ _
  rw [hid]
  have hg : ‖g‖ ≤ |k| := by
    dsimp [g]
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (abs_nonneg k)).trans_eq
      (mul_one _)
  have hGF : ‖iteratedFDeriv ℝ n G (g x)‖ ≤ B := by
    simpa only [G, iteratedFDeriv_comp_sub] using hB (g x - z)
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul hGF (pow_le_pow_left₀ (norm_nonneg g) hg n)
    (pow_nonneg (norm_nonneg g) _) ((norm_nonneg _).trans hGF)

theorem highWindowTensor_tsupport_bound {d } {x }
    (hx : x ∈ tsupport (highWindowTensor d)) : ∀ i, |x i| ≤ 3 / 4 := by
  have hsub : tsupport (highWindowTensor d) ⊆ Metric.closedBall (0 : Covariate d) (3 / 4 : ℝ) := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)).mpr
    intro i
    simpa only [Real.norm_eq_abs] using (highWindowTensor_support_bound hy i).le
  have hnorm := hsub hx
  rw [Metric.mem_closedBall, dist_zero_right,
    pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)] at hnorm
  simpa only [Real.norm_eq_abs] using hnorm

theorem integer_close_three_quarters (t : ℝ) (z : ℤ) (hz : |t - z| ≤ 3 / 4) :
    z = ⌊t⌋ ∨ z = ⌊t⌋ + 1 := by
  have hf := Int.floor_le t
  have hc := Int.lt_floor_add_one t
  have hclose := abs_le.mp hz
  have hlo : ⌊t⌋ ≤ z := by
    by_contra h
    have hcast : (z : ℝ) + 1 ≤ ⌊t⌋ := by exact_mod_cast (by omega : z + 1 ≤ ⌊t⌋)
    linarith
  have hhi : z ≤ ⌊t⌋ + 1 := by
    by_contra h
    have hcast : (⌊t⌋ : ℝ) + 2 ≤ z := by exact_mod_cast (by omega : ⌊t⌋ + 2 ≤ z)
    linarith
  omega

section
variable (d k : ℕ) (x : Covariate d)
include x

def highActiveLabelBox  : Finset (HighWindowLabels d k) :=
  Fintype.piFinset (fun r => {((⌊(k : ℝ) * x r⌋ : ℤ) : ZMod k),
    ((⌊(k : ℝ) * x r⌋ + 1 : ℤ) : ZMod k)})

theorem highActiveLabelBox_card_le  :
    (highActiveLabelBox d k x).card ≤ 2 ^ d := by
  unfold highActiveLabelBox
  rw [Fintype.card_piFinset]
  calc
    _ ≤ ∏ _r : Fin d, 2 := by
      solve_by_elim [Finset.prod_le_prod', Finset.card_insert_le]
    _ = 2 ^ d := by simp
end


end NearlyMinimax
