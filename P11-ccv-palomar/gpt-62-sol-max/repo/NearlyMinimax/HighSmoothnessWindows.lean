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

section
variable (x : ℝ)

theorem highWindowSeed_nonneg : 0 ≤ highWindowSeed x :=
  highWindowBump.nonneg

theorem highWindowSeed_eq_one (hx : |x| ≤ 1 / 2) : highWindowSeed x = 1 := by
  apply highWindowBump.one_of_mem_closedBall
  simpa [Metric.mem_closedBall, Real.dist_eq, highWindowBump] using hx

theorem highWindowSeed_eq_zero (hx : 3 / 4 ≤ |x|) : highWindowSeed x = 0 := by
  apply highWindowBump.zero_of_le_dist
  simpa [Real.dist_eq, highWindowBump] using hx

end

/-- Any family of unit-radius integer translates is locally finite. -/
theorem integerTranslate_locallyFinite (g : ℝ → ℝ)
    (hg : ∀ x, 1 ≤ |x| → g x = 0) :
    LocallyFinite (fun j : ℤ => support (fun x : ℝ => g (x - j))) := by
  intro x
  refine ⟨Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
  apply (finite_Icc (⌊x⌋ - 3) (⌊x⌋ + 3)).subset
  intro j hj
  obtain ⟨y, hy, hnear⟩ := hj
  have hdist : |y - j| < 1 := by
    by_contra h
    apply hy <;> simp_all
  have hd := abs_lt.mp hdist
  have hfloor := Int.floor_le x
  have hceil := Int.lt_floor_add_one x
  constructor
  · apply (Int.cast_le (R := ℝ)).mp <;> grind
  · apply (Int.cast_le (R := ℝ)).mp <;> grind

def highWindowEnergy (x : ℝ) : ℝ := ∑ᶠ j : ℤ, highWindowSeed (x - j) ^ 2

theorem highWindowEnergy_locallyFinite :
    LocallyFinite (fun j : ℤ => support (fun x : ℝ => highWindowSeed (x - j) ^ 2)) := by
  apply integerTranslate_locallyFinite (fun x => highWindowSeed x ^ 2)
  intro x hx
  simp [highWindowSeed_eq_zero x (by linarith)]

theorem highWindowEnergy_contDiff : ContDiff ℝ ∞ highWindowEnergy := by
  unfold highWindowEnergy
  apply ContMDiff.contDiff
  apply contMDiff_finsum _ highWindowEnergy_locallyFinite
  intro j
  apply ContDiff.contMDiff
  exact (highWindowSeed_contDiff.comp (contDiff_id.sub contDiff_const)).pow 2

section
variable (x : ℝ)

theorem highWindowEnergy_lower : 1 ≤ highWindowEnergy x := by
  let j := ⌊x + 1 / 2⌋
  have hj0 := Int.floor_le (x + 1 / 2)
  have hj1 := Int.lt_floor_add_one (x + 1 / 2)
  have hclose : |x - j| ≤ 1 / 2 := abs_le.mpr ⟨by dsimp [j]; linarith,
    by dsimp [j]; linarith⟩
  have hone := highWindowSeed_eq_one (x - j) hclose
  have hle := single_le_finsum j (highWindowEnergy_locallyFinite.point_finite x)
    (fun z : ℤ => sq_nonneg (highWindowSeed (x - z)))
  simpa [highWindowEnergy, hone] using hle

theorem highWindowEnergy_pos : 0 < highWindowEnergy x :=
  lt_of_lt_of_le (by norm_num) (highWindowEnergy_lower x)

theorem highWindowEnergy_integer_periodic (k : ℤ) :
    highWindowEnergy (x + k) = highWindowEnergy x := by
  unfold highWindowEnergy
  calc
    (∑ᶠ j : ℤ, highWindowSeed (x + k - j) ^ 2) =
      ∑ᶠ j : ℤ, highWindowSeed (x - (j - k : ℤ)) ^ 2 := by
        grind
    _ = _ := finsum_comp (g := fun j : ℤ => highWindowSeed (x - j) ^ 2)
      (fun j : ℤ => j - k) (by
      constructor
      · intro i j h <;> simp_all
      · intro j
        exact ⟨j + k, by dsimp; ring⟩)

end

def highWindowProfile (x : ℝ) : ℝ := highWindowSeed x / Real.sqrt (highWindowEnergy x)

theorem highWindowProfile_contDiff : ContDiff ℝ ∞ highWindowProfile := by
  exact highWindowSeed_contDiff.div
    (highWindowEnergy_contDiff.sqrt (fun x => (highWindowEnergy_pos x).ne'))
    (fun x => (Real.sqrt_pos.mpr (highWindowEnergy_pos x)).ne')

section
variable (x : ℝ)

theorem highWindowProfile_nonneg : 0 ≤ highWindowProfile x :=
  div_nonneg (highWindowSeed_nonneg x) (Real.sqrt_nonneg _)

theorem highWindowProfile_eq_zero (hx : 3 / 4 ≤ |x|) :
    highWindowProfile x = 0 := by
  simp [highWindowProfile, highWindowSeed_eq_zero x hx]

theorem highWindowProfile_sq_partition :
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

end

theorem highWindowProfile_locallyFinite :
    LocallyFinite (fun j : ℤ => support (fun x : ℝ => highWindowProfile (x - j))) := by
  apply integerTranslate_locallyFinite highWindowProfile
  grind [highWindowProfile_eq_zero]

/-- Tensor profile supported strictly inside the manuscript's chart Q. -/
def highWindowTensor (d : ℕ) (x : Covariate d) : ℝ :=
  ∏ i, highWindowProfile (x i)

theorem highWindowTensor_contDiff (d : ℕ) : ContDiff ℝ ∞ (highWindowTensor d) := by
  apply contDiff_prod
  intro i hi
  apply highWindowProfile_contDiff.comp <;> fun_prop

theorem highWindowTensor_support_bound {d : ℕ} {x : Covariate d}
    (hx : highWindowTensor d x ≠ 0) : ∀ i, |x i| < 3 / 4 := by
  intro i
  by_contra hi
  apply hx
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (highWindowProfile_eq_zero _ (not_lt.mp hi))

theorem highWindowTensor_hasCompactSupport (d : ℕ) : HasCompactSupport (highWindowTensor d) := by
  apply (isCompact_closedBall (0 : Covariate d) (3 / 4 : ℝ)).of_isClosed_subset
    (isClosed_tsupport _)
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)).mpr
  intro i
  simpa only [Real.norm_eq_abs] using (highWindowTensor_support_bound hx i).le

theorem highWindowTensor_derivative_bound (d m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ m, ∀ x : Covariate d,
      ‖iteratedFDeriv ℝ i (highWindowTensor d) x‖ ≤ C :=
  (highWindowTensor_hasCompactSupport d).exists_bound_iteratedFDeriv
    (highWindowTensor_contDiff d) m

/-- A finite-period window is the actual sum over its integer residue class. -/
def highPeriodicWindow (k : ℕ) (j : ZMod k) (x : ℝ) : ℝ :=
  ∑ᶠ z : ℤ, if (z : ZMod k) = j then highWindowProfile ((k : ℝ) * x - z) else 0

section
variable (k : ℕ)

section
variable (j : ZMod k)

theorem highPeriodicWindow_locallyFinite :
    LocallyFinite (fun z : ℤ => support (fun x : ℝ =>
      if (z : ZMod k) = j then highWindowProfile ((k : ℝ) * x - z) else 0)) := by
  apply (highWindowProfile_locallyFinite.preimage_continuous
    (continuous_const.mul continuous_id)).subset
  intro z x hx
  by_cases hz : (z : ZMod k) = j
  · simpa [hz] using hx
  simp_all

theorem highPeriodicWindow_contDiff :
    ContDiff ℝ ∞ (highPeriodicWindow k j) := by
  unfold highPeriodicWindow
  apply ContMDiff.contDiff
  apply contMDiff_finsum _ (highPeriodicWindow_locallyFinite k j)
  intro z
  apply ContDiff.contMDiff
  by_cases hz : (z : ZMod k) = j
  · simp only [if_pos hz]
    apply highWindowProfile_contDiff.comp <;> fun_prop
  · simp only [if_neg hz]
    exact contDiff_const

theorem highPeriodicWindow_nonneg (x : ℝ) :
    0 ≤ highPeriodicWindow k j x := by
  apply finsum_nonneg
  intro z
  split_ifs
  · exact highWindowProfile_nonneg _
  · exact le_rfl

private theorem periodic_term_support (x : ℝ) (z : ℤ)
    (hz : (if (z : ZMod k) = j then highWindowProfile ((k : ℝ) * x - z) else 0) ≠ 0) :
    (z : ZMod k) = j ∧ |(k : ℝ) * x - z| < 3 / 4 := by
  grind [highWindowProfile_eq_zero]

end

private theorem periodic_lift_separation {z q : ℤ}
    (hj : (z : ZMod k) = (q : ZMod k)) (hq : q ≠ z) :
    (k : ℝ) ≤ |(q : ℝ) - z| := by
  exact_mod_cast Int.le_abs_of_dvd (sub_ne_zero.mpr hq)
    ((ZMod.intCast_eq_intCast_iff_dvd_sub z q k).mp hj)

theorem highPeriodicWindow_support_subsingleton (hk : 2 ≤ k)
    (j : ZMod k) (x : ℝ) :
    (support (fun z : ℤ => if (z : ZMod k) = j then
      highWindowProfile ((k : ℝ) * x - z) else 0)).Subsingleton := by
  intro z hz q hq
  obtain ⟨hzj, hzd⟩ := periodic_term_support k j x z hz
  obtain ⟨hqj, hqd⟩ := periodic_term_support k j x q hq
  by_contra hn
  have hs := periodic_lift_separation k (hzj.trans hqj.symm) (Ne.symm hn)
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  rw [abs_lt] at hzd hqd
  rcases le_abs.mp hs with h | h <;> linarith

end

theorem finsum_sq_of_subsingleton_support (f : ℤ → ℝ) (hs : (support f).Subsingleton) :
    (∑ᶠ z, f z) ^ 2 = ∑ᶠ z, f z ^ 2 := by
  by_cases hn : ∃ z, f z ≠ 0
  · obtain ⟨z, hz⟩ := hn
    have hzero : ∀ q, q ≠ z → f q = 0 := by
      intro q hq
      by_contra h
      tauto
    rw [finsum_eq_single f z hzero, finsum_eq_single (fun q => f q ^ 2) z
      (fun q hq => by simp_all)]
  simp_all

section
variable (k : ℕ)

section
variable [NeZero k] (hk : 2 ≤ k)
include hk

theorem highPeriodicWindow_sq_partition (x : ℝ) :
    (∑ j : ZMod k, highPeriodicWindow k j x ^ 2) = 1 := by
  have hs (j : ZMod k) : highPeriodicWindow k j x ^ 2 =
      ∑ᶠ z : ℤ, if (z : ZMod k) = j then highWindowProfile ((k : ℝ) * x - z) ^ 2 else 0 := by
    rw [highPeriodicWindow, finsum_sq_of_subsingleton_support _
      (highPeriodicWindow_support_subsingleton k hk j x)]
    simp
  simp only [hs]
  rw [sum_finsum_comm]
  · simpa using highWindowProfile_sq_partition _
  · intro j hj
    apply (highPeriodicWindow_locallyFinite k j).point_finite x |>.subset <;> simp

theorem highPeriodicWindow_le_one
    (j : ZMod k) (x : ℝ) : highPeriodicWindow k j x ≤ 1 := by
  have hsq : highPeriodicWindow k j x ^ 2 ≤ 1 := by
    rw [← highPeriodicWindow_sq_partition k hk x]
    exact Finset.single_le_sum (fun z _ => sq_nonneg (highPeriodicWindow k z x))
      (Finset.mem_univ j)
  nlinarith [highPeriodicWindow_nonneg k j x]

end

theorem highPeriodicWindow_support_lift (j : ZMod k) (x : ℝ)
    (hx : highPeriodicWindow k j x ≠ 0) :
    ∃ z : ℤ, (z : ZMod k) = j ∧ |(k : ℝ) * x - z| < 3 / 4 := by
  by_contra! h
  exact hx (finsum_eq_zero_of_forall_eq_zero fun z =>
    not_not.mp (mt (periodic_term_support k j x z) (fun hz => (h z hz.1).not_gt hz.2)))

end

abbrev HighWindowLabels (d k : ℕ) := Fin d → ZMod k

/-- The actual finite periodic squared partition in d dimensions. -/
def highPeriodicTensor (d k : ℕ) (j : HighWindowLabels d k) (x : Covariate d) : ℝ :=
  ∏ i, highPeriodicWindow k (j i) (x i)

section
variable (d k : ℕ)

section
variable (j : HighWindowLabels d k)

theorem highPeriodicTensor_contDiff :
    ContDiff ℝ ∞ (highPeriodicTensor d k j) := by
  apply contDiff_prod
  intro i hi
  exact (highPeriodicWindow_contDiff k (j i)).comp (contDiff_apply ℝ ℝ i)

theorem highPeriodicTensor_nonneg (x : Covariate d) :
    0 ≤ highPeriodicTensor d k j x :=
  Finset.prod_nonneg (fun i _ => highPeriodicWindow_nonneg k (j i) (x i))

end

section
variable [NeZero k] (hk : 2 ≤ k)
include hk

theorem highPeriodicTensor_le_one
    (j : HighWindowLabels d k) (x : Covariate d) : highPeriodicTensor d k j x ≤ 1 := by
  apply Finset.prod_le_one₀
  · solve_by_elim [highPeriodicWindow_nonneg]
  · solve_by_elim [highPeriodicWindow_le_one]

theorem highPeriodicTensor_sq_partition
    (x : Covariate d) : (∑ j : HighWindowLabels d k, highPeriodicTensor d k j x ^ 2) = 1 := by
  simp only [highPeriodicTensor, ← Finset.prod_pow]
  rw [← Fintype.prod_sum (fun i (j : ZMod k) => highPeriodicWindow k j (x i) ^ 2)]
  simp only [highPeriodicWindow_sq_partition k hk, Finset.prod_const_one]

end

theorem highPeriodicTensor_support_lift (j : HighWindowLabels d k)
    (x : Covariate d) (hx : highPeriodicTensor d k j x ≠ 0) :
    ∃ z : Fin d → ℤ, (∀ i, (z i : ZMod k) = j i) ∧
      ∀ i, |(k : ℝ) * x i - z i| < 3 / 4 := by
  have hcoordinate (i : Fin d) : highPeriodicWindow k (j i) (x i) ≠ 0 := by
    intro h
    exact hx (Finset.prod_eq_zero (Finset.mem_univ i) h)
  choose z hz using fun i => highPeriodicWindow_support_lift k (j i) (x i) (hcoordinate i)
  exact ⟨z, fun i => (hz i).1, fun i => (hz i).2⟩

end

/-- Around every point, a periodized window agrees with one compact chart
profile, including points where the window is zero. -/
theorem highPeriodicWindow_eventuallyEq_single (k : ℕ) [NeZero k] (hk : 4 ≤ k)
    (j : ZMod k) (x : ℝ) :
    ∃ z : ℤ, (z : ZMod k) = j ∧ highPeriodicWindow k j =ᶠ[𝓝 x]
      (fun y => highWindowProfile ((k : ℝ) * y - z)) := by
  have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  let t := x - (j.val : ℝ) / k
  let z : ℤ := (j.val : ℤ) + (k : ℤ) * round t
  have hzj : (z : ZMod k) = j := by simp [z]
  have hclose : |(k : ℝ) * x - z| ≤ (k : ℝ) / 2 := by
    have he : (k : ℝ) * x - z = k * (t - round t) := by
      dsimp [z, t]
      push_cast
      field_simp
      ring
    rw [he, abs_mul, abs_of_pos hk0, ← mul_one_div]
    exact mul_le_mul_of_nonneg_left (abs_sub_round t) hk0.le
  refine ⟨z, hzj, ?_⟩
  filter_upwards [Metric.ball_mem_nhds x (by positivity : 0 < 1 / (4 * (k : ℝ)))] with y hy
  have hdist : |y - x| < 1 / (4 * (k : ℝ)) := by simpa only [Metric.mem_ball, Real.dist_eq] using hy
  have hxy : |(k : ℝ) * y - (k : ℝ) * x| < 1 / 4 := by
    rw [← mul_sub, abs_mul, abs_of_pos hk0]
    linarith [(lt_div_iff₀ (by positivity : 0 < 4 * (k : ℝ))).mp hdist]
  rw [highPeriodicWindow, finsum_eq_single _ z]
  · simp [hzj]
  · intro q hq
    by_contra h
    obtain ⟨hqj, hqd⟩ := periodic_term_support k j y q h
    have hs := periodic_lift_separation k (hzj.trans hqj.symm) hq
    rw [abs_le] at hclose
    rw [abs_lt] at hqd hxy
    rcases le_abs.mp hs with h' | h' <;> linarith

theorem smooth_affine_iteratedFDeriv_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : E → ℝ) (hF : ContDiff ℝ ∞ F) (k : ℝ) (z x : E)
    (n : ℕ) (B : ℝ) (hB : ∀ y, ‖iteratedFDeriv ℝ n F y‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (fun y => F (k • y - z)) x‖ ≤ B * |k| ^ n := by
  let g := k • ContinuousLinearMap.id ℝ E
  let G := fun y => F (y - z)
  have hG : ContDiff ℝ n G := (hF.of_le (by simp)).comp
    (contDiff_id.sub contDiff_const)
  have hid := g.iteratedFDerivWithin_comp_right hG.contDiffOn uniqueDiffOn_univ
    (by simp)
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

theorem highWindowTensor_tsupport_bound {d : ℕ} {x : Covariate d}
    (hx : x ∈ tsupport (highWindowTensor d)) : ∀ i, |x i| ≤ 3 / 4 := by
  have hsub : tsupport (highWindowTensor d) ⊆ Metric.closedBall (0 : Covariate d) (3 / 4 : ℝ) := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)).mpr
    intro i
    simpa only [Real.norm_eq_abs] using (highWindowTensor_support_bound hy i).le
  have hnorm := hsub hx
  simp_all [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)]

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

def highActiveLabelBox (d k : ℕ) (x : Covariate d) : Finset (HighWindowLabels d k) :=
  Fintype.piFinset (fun r => {((⌊(k : ℝ) * x r⌋ : ℤ) : ZMod k),
    ((⌊(k : ℝ) * x r⌋ + 1 : ℤ) : ZMod k)})

theorem highActiveLabelBox_card_le (d k : ℕ) (x : Covariate d) :
    (highActiveLabelBox d k x).card ≤ 2 ^ d := by
  unfold highActiveLabelBox
  rw [Fintype.card_piFinset]
  calc
    _ ≤ ∏ _r : Fin d, 2 := by
      apply Finset.prod_le_prod'
      intro r hr
      exact (Finset.card_insert_le _ _).trans (by simp)
    _ = 2 ^ d := by simp

end NearlyMinimax
