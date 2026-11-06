module
public import NearlyMinimax.CoordinatePartialBridge
public import NearlyMinimax.HighPriorModel
public import NearlyMinimax.AnchoredGeometry
public import RoughRegime.ComplexDerivativeBridge
@[expose] public section
noncomputable section
open Set Function Filter MeasureTheory RoughRegime.ComplexDerivativeBridge
open scoped Topology BigOperators ContDiff ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable {d : ℕ}
def highWindowBump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 2
  rOut := 3 / 4
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num
def highWindowSeed : ℝ → ℝ := highWindowBump
theorem highWindowSeed_contDiff : ContDiff ℝ ∞ highWindowSeed :=
  highWindowBump.contDiff
theorem highWindowSeed_eq_zero (x : ℝ) (hx : 3 / 4 ≤ |x|) : highWindowSeed x = 0 := by
  apply highWindowBump.zero_of_le_dist
  simpa [Real.dist_eq, highWindowBump] using hx
theorem integerTranslate_locallyFinite (g : ℝ → ℝ)
    (hg : ∀ x, 1 ≤ |x| → g x = 0) :
    LocallyFinite (fun j : ℤ => support (fun x : ℝ => g (x - j))) := by
  intro x
  refine ⟨Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
  apply (finite_Icc (⌊x⌋ - 3) (⌊x⌋ + 3)).subset
  intro j hj
  obtain ⟨y, hy, hnear⟩ := hj
  have := abs_lt.mp (by by_contra h; exact hy (hg _ (not_lt.mp h)))
  have := Int.floor_le x
  have := Int.lt_floor_add_one x
  constructor
  · apply (Int.cast_le (R := ℝ)).mp
    push_cast
    linarith [hnear.1, hnear.2]
  · apply (Int.cast_le (R := ℝ)).mp
    push_cast
    linarith [hnear.1, hnear.2]
def highWindowEnergy (x : ℝ) : ℝ := ∑ᶠ j : ℤ, highWindowSeed (x - j) ^ 2
theorem highWindowEnergy_locallyFinite :
    LocallyFinite (fun j : ℤ => support (fun x : ℝ => highWindowSeed (x - j) ^ 2)) := by
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
theorem highWindowEnergy_pos (x : ℝ) : 0 < highWindowEnergy x :=
  have h_highWindowEnergy_lower : 1 ≤ highWindowEnergy x := by
    let j : ℤ := ⌊x + 1 / 2⌋
    have hj0 := Int.floor_le (x + 1 / 2)
    have hj1 := Int.lt_floor_add_one (x + 1 / 2)
    have hclose : |x - j| ≤ 1 / 2 := abs_le.mpr ⟨by dsimp [j]; linarith,
      by dsimp [j]; linarith⟩
    have h_highWindowSeed_eq_one : highWindowSeed (x - j) = 1 := by
      apply highWindowBump.one_of_mem_closedBall
      simpa [Metric.mem_closedBall, Real.dist_eq, highWindowBump] using hclose
    have hone := h_highWindowSeed_eq_one
    have hle := single_le_finsum j (highWindowEnergy_locallyFinite.point_finite x)
      (fun z : ℤ => sq_nonneg (highWindowSeed (x - z)))
    simpa [highWindowEnergy, hone] using hle
  lt_of_lt_of_le (by norm_num) h_highWindowEnergy_lower
def highWindowProfile (x : ℝ) : ℝ := highWindowSeed x / Real.sqrt (highWindowEnergy x)
theorem highWindowProfile_contDiff : ContDiff ℝ ∞ highWindowProfile := by
  exact highWindowSeed_contDiff.div
    (highWindowEnergy_contDiff.sqrt (fun x => (highWindowEnergy_pos x).ne'))
    (fun x => (Real.sqrt_pos.mpr (highWindowEnergy_pos x)).ne')
theorem highWindowProfile_nonneg (x : ℝ) : 0 ≤ highWindowProfile x :=
  div_nonneg (highWindowBump.nonneg) (Real.sqrt_nonneg _)
theorem highWindowProfile_eq_zero (x : ℝ) (hx : 3 / 4 ≤ |x|) :
    highWindowProfile x = 0 := by
  simp [highWindowProfile, highWindowSeed_eq_zero x hx]
theorem highWindowProfile_sq_partition (x : ℝ) :
    (∑ᶠ j : ℤ, highWindowProfile (x - j) ^ 2) = 1 := by
  calc
    (∑ᶠ j : ℤ, highWindowProfile (x - j) ^ 2) =
      ∑ᶠ j : ℤ, highWindowSeed (x - j) ^ 2 * (highWindowEnergy x)⁻¹ := by
        apply finsum_congr
        intro j
        have hp : highWindowEnergy (x - j) = highWindowEnergy x := by
          have h_highWindowEnergy_integer_periodic (k : ℤ) : highWindowEnergy (x + k) = highWindowEnergy x := by
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
                  simpa only [sub_left_inj] using h
                · intro j
                  exact ⟨j + k, by dsimp; ring⟩)
          simpa [sub_eq_add_neg] using (h_highWindowEnergy_integer_periodic (-j))
        rw [highWindowProfile, div_pow, hp, Real.sq_sqrt (highWindowEnergy_pos x).le]
        rfl
    _ = highWindowEnergy x * (highWindowEnergy x)⁻¹ :=
      (finsum_mul (fun j : ℤ => highWindowSeed (x - j) ^ 2) _).symm
    _ = 1 := mul_inv_cancel₀ ((highWindowEnergy_pos x).ne')
theorem highWindowProfile_locallyFinite :
    LocallyFinite (fun j : ℤ => support (fun x : ℝ => highWindowProfile (x - j))) := by
  apply integerTranslate_locallyFinite highWindowProfile
  intro x hx
  exact highWindowProfile_eq_zero x (by linarith)
def highWindowTensor (d : ℕ) (x : Covariate d) : ℝ :=
  ∏ i, highWindowProfile (x i)
theorem highWindowTensor_contDiff (d : ℕ) : ContDiff ℝ ∞ (highWindowTensor d) := by
  apply contDiff_prod
  intro i hi
  exact highWindowProfile_contDiff.comp (contDiff_apply ℝ ℝ i)
theorem highWindowTensor_support_bound  {x : Covariate d}
    (hx : highWindowTensor d x ≠ 0) : ∀ i, |x i| < 3 / 4 := by
  intro i
  by_contra hi
  apply hx
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (highWindowProfile_eq_zero _ (not_lt.mp hi))
def highPeriodicWindow (k : ℕ) (j : ZMod k) (x : ℝ) : ℝ :=
  ∑ᶠ z : ℤ, if (z : ZMod k) = j then highWindowProfile ((k : ℝ) * x - z) else 0
theorem highPeriodicWindow_locallyFinite (k : ℕ) (j : ZMod k) :
    LocallyFinite (fun z : ℤ => support (fun x : ℝ =>
      if (z : ZMod k) = j then highWindowProfile ((k : ℝ) * x - z) else 0)) := by
  apply (highWindowProfile_locallyFinite.preimage_continuous
    (continuous_const.mul continuous_id)).subset
  intro z x hx
  by_cases hz : (z : ZMod k) = j
  · simpa [hz] using hx
  · simp [hz] at hx
theorem highPeriodicWindow_nonneg (k : ℕ) (j : ZMod k) (x : ℝ) :
    0 ≤ highPeriodicWindow k j x := by
  apply finsum_nonneg
  intro z
  split_ifs
  · exact highWindowProfile_nonneg _
  · exact le_rfl
theorem highPeriodicWindow_support_subsingleton (k : ℕ) (hk : 2 ≤ k)
    (j : ZMod k) (x : ℝ) :
    (support (fun z : ℤ => if (z : ZMod k) = j then
      highWindowProfile ((k : ℝ) * x - z) else 0)).Subsingleton := by
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
  have : |(q : ℝ) - z| < 3 / 2 := by
    have := abs_lt.mp hzd
    have := abs_lt.mp hqd
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have : |q - z| < (2 : ℤ) := by
    apply (Int.cast_lt (R := ℝ)).mp
    push_cast
    linarith
  have : (2 : ℤ) ≤ k := by exact_mod_cast hk
  have hl0 : l = 0 := by
    by_contra h
    have : (1 : ℤ) ≤ |l| := by
      have := abs_pos.mpr h
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
  · have hzero : ∀ z, f z = 0 := by simpa using hn
    simp only [hzero, zero_pow (by decide : (2 : ℕ) ≠ 0), finsum_zero]
theorem highPeriodicWindow_sq_partition (k : ℕ) [NeZero k] (hk : 2 ≤ k) (x : ℝ) :
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
    intro z hz
    change (if (z : ZMod k) = j then highWindowProfile ((k : ℝ) * x - z) else 0) ≠ 0
    change (if (z : ZMod k) = j then highWindowProfile ((k : ℝ) * x - z) ^ 2 else 0) ≠ 0 at hz
    by_cases hzj : (z : ZMod k) = j
    · simp only [ite_eq_left hzj] at hz ⊢
      exact fun h => hz (by rw [h]; norm_num)
    · exact False.elim (hz (by simp [hzj]))
theorem highPeriodicWindow_le_one (k : ℕ) [NeZero k] (hk : 2 ≤ k)
    (j : ZMod k) (x : ℝ) : highPeriodicWindow k j x ≤ 1 := by
  have : highPeriodicWindow k j x ^ 2 ≤ 1 := by
    rw [← highPeriodicWindow_sq_partition k hk x]
    exact Finset.single_le_sum (fun z _ => sq_nonneg (highPeriodicWindow k z x))
      (Finset.mem_univ j)
  nlinarith [highPeriodicWindow_nonneg k j x]
theorem highPeriodicWindow_support_lift (k : ℕ) (j : ZMod k) (x : ℝ)
    (hx : highPeriodicWindow k j x ≠ 0) :
    ∃ z : ℤ, (z : ZMod k) = j ∧ |(k : ℝ) * x - z| < 3 / 4 := by
  have hterm : ∃ z : ℤ, (if (z : ZMod k) = j then
      highWindowProfile ((k : ℝ) * x - z) else 0) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (by simp only [highPeriodicWindow, h, finsum_zero])
  obtain ⟨z, hz⟩ := hterm
  refine ⟨z, ?_, ?_⟩
  · by_contra h
    exact hz (by simp [h])
  · by_contra h
    exact hz (by simp [highWindowProfile_eq_zero _ (not_lt.mp h)])
abbrev HighWindowLabels (d k : ℕ) := Fin d → ZMod k
def highPeriodicTensor (d k : ℕ) (j : HighWindowLabels d k) (x : Covariate d) : ℝ :=
  ∏ i, highPeriodicWindow k (j i) (x i)
theorem highPeriodicTensor_contDiff (d k : ℕ) (j : HighWindowLabels d k) :
    ContDiff ℝ ∞ (highPeriodicTensor d k j) := by
  apply contDiff_prod
  intro i hi
  have h_highPeriodicWindow_contDiff (j : ZMod k) : ContDiff ℝ ∞ (highPeriodicWindow k j) := by
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
  exact (h_highPeriodicWindow_contDiff (j i)).comp (contDiff_apply ℝ ℝ i)
theorem highPeriodicTensor_nonneg (d k : ℕ) (j : HighWindowLabels d k) (x : Covariate d) :
    0 ≤ highPeriodicTensor d k j x :=
  Finset.prod_nonneg (fun i _ => highPeriodicWindow_nonneg k (j i) (x i))
theorem highPeriodicTensor_le_one (d k : ℕ) [NeZero k] (hk : 2 ≤ k)
    (j : HighWindowLabels d k) (x : Covariate d) : highPeriodicTensor d k j x ≤ 1 := by
  apply Finset.prod_le_one₀
  · intro i hi
    exact highPeriodicWindow_nonneg _ _ _
  · intro i hi
    exact highPeriodicWindow_le_one _ hk _ _
theorem smooth_affine_iteratedFDeriv_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : E → ℝ) (hF : ContDiff ℝ ∞ F) (k : ℝ) (z x : E)
    (n : ℕ) (B : ℝ) (hB : ∀ y, ‖iteratedFDeriv ℝ n F y‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (fun y => F (k • y - z)) x‖ ≤ B * |k| ^ n := by
  let g : E →L[ℝ] E := k • ContinuousLinearMap.id ℝ E
  let G : E → ℝ := fun y => F (y - z)
  have hG : ContDiff ℝ n G := (hF.of_le (by simp)).comp
    (contDiff_id.sub contDiff_const)
  have hid := g.iteratedFDerivWithin_comp_right hG.contDiffOn uniqueDiffOn_univ
    (by simpa using (uniqueDiffOn_univ : UniqueDiffOn ℝ (univ : Set E)))
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
theorem highWindowTensor_tsupport_bound  {x : Covariate d}
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
  have := Int.floor_le t
  have := Int.lt_floor_add_one t
  have := abs_le.mp hz
  have : ⌊t⌋ ≤ z := by
    by_contra h
    have : (z : ℝ) + 1 ≤ ⌊t⌋ := by exact_mod_cast (by omega : z + 1 ≤ ⌊t⌋)
    linarith
  have : z ≤ ⌊t⌋ + 1 := by
    by_contra h
    have : (⌊t⌋ : ℝ) + 2 ≤ z := by exact_mod_cast (by omega : ⌊t⌋ + 2 ≤ z)
    linarith
  omega
def highActiveLabelBox (d k : ℕ) (x : Covariate d) : Finset (HighWindowLabels d k) :=
  Fintype.piFinset (fun r => {((⌊(k : ℝ) * x r⌋ : ℤ) : ZMod k),
    ((⌊(k : ℝ) * x r⌋ + 1 : ℤ) : ZMod k)})
theorem finite_sum_norm_le_active_count  [Fintype J]
    [NormedAddCommGroup E] (g : J → E) (N : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ j, ‖g j‖ ≤ B)
    (hcount : (Finset.univ.filter (fun j => g j ≠ 0)).card ≤ N) :
    ‖∑ j, g j‖ ≤ ↑N * B := by
  let A := Finset.univ.filter (fun j => g j ≠ 0)
  calc
    _ ≤ ∑ j, ‖g j‖ := norm_sum_le _ _
    _ = _ := (by symm; rw [Finset.sum_filter]; apply Finset.sum_congr rfl; intro j hj; by_cases hg : g j = 0 <;> simp [hg])
    _ ≤ ∑ _j ∈ A, B := Finset.sum_le_sum (fun j _ => hbound j)
    _ = ↑A.card * B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) hB
theorem holder_of_scaled_sup_and_lipschitz (k r A α q : ℝ)
    (hk : 0 < k) (hr : 0 ≤ r) (hA : 0 ≤ A) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hsup : q ≤ 2 * A * k ^ (-α))
    (hlip : q ≤ A * k ^ (1 - α) * r) :
    q ≤ 2 * A * r ^ α := by
  by_cases hr0 : r = 0
  · subst r
    simpa only [mul_zero, Real.zero_rpow hα0.ne'] using hlip
  have hrpos  := lt_of_le_of_ne hr (Ne.symm hr0)
  by_cases hkr : k * r ≤ 1
  · have hp  :=
      Real.rpow_le_one (mul_nonneg hk.le hr) hkr (sub_nonneg.mpr hα1)
    have hid : k ^ (1 - α) * r = (k * r) ^ (1 - α) * r ^ α := by
      rw [Real.mul_rpow hk.le hr, mul_assoc, ← Real.rpow_add hrpos]
      simp only [sub_add_cancel, Real.rpow_one]
    have hsmall : A * k ^ (1 - α) * r ≤ A * r ^ α := by
      calc
        _ = A * ((k * r) ^ (1 - α) * r ^ α) := by rw [← hid]; ring
        _ ≤ A * (1 * r ^ α) := by gcongr
        _ = _ := by ring
    have : 0 ≤ A * r ^ α := mul_nonneg hA (Real.rpow_nonneg hr _)
    exact (hlip.trans hsmall).trans (by nlinarith)
  · have hp  := Real.one_le_rpow (le_of_not_ge hkr) hα0.le
    exact hsup.trans (mul_le_mul_of_nonneg_left (by rw [Real.rpow_neg hk.le, ← one_div]; apply (div_le_iff₀ (Real.rpow_pos_of_pos hk α)).mpr; simpa only [Real.mul_rpow hk.le hr, one_mul, mul_comm] using hp) (by positivity))
theorem multiIndexBasis_norm  (γ : Fin d → ℕ) (j : Fin (∑ r, γ r)) :
    ‖multiIndexBasis γ j‖ = 1 := by
  simp [multiIndexBasis, wordBasis, Pi.norm_single]
theorem multiPartial_norm_le_iterated  (F : Covariate d → ℝ)
    (hF : ContDiff ℝ ∞ F) (γ : Fin d → ℕ) (x : Covariate d) :
    |multiPartial F γ x| ≤ ‖iteratedFDeriv ℝ (∑ r, γ r) F x‖ := by
  rw [multiPartial_eq_iteratedFDeriv univ isOpen_univ F (∑ r, γ r)
    (hF.of_le (by simp)).contDiffOn γ le_rfl x (mem_univ x)]
  simpa only [Real.norm_eq_abs, multiIndexBasis_norm, Finset.prod_const_one, mul_one] using ((iteratedFDeriv ℝ (∑ r, γ r) F x).le_opNorm (multiIndexBasis γ))
theorem covariate_norm_le_euclidean  (x : Covariate d) : ‖x‖ ≤ euclideanNorm x := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro r
  simpa only [Real.norm_eq_abs, euclideanNorm] using abs_coordinate_le_euclideanNorm x r
theorem mixed_bounds_of_scaled_derivatives  (C : ModelConstants d)
    (F ) (hF : ContDiff ℝ ∞ F) (k A )
    (hk : 1 ≤ k) (hA : 0 ≤ A)
    (hbound : ∀ q ≤ C.order + 1, ∀ x,
      ‖iteratedFDeriv ℝ q F x‖ ≤ A * k ^ ((q : ℝ) - C.smoothness)) :
    (∀ γ : Fin d → Fin (C.order + 1), (∑ r, (γ r).val) ≤ C.order → ∀ x,
      |multiPartial F (fun r => (γ r).val) x| ≤ A) ∧
    (∀ γ : Fin d → Fin (C.order + 1), (∑ r, (γ r).val) = C.order → ∀ x y,
      |multiPartial F (fun r => (γ r).val) x - multiPartial F (fun r => (γ r).val) y| ≤
        2 * A * euclideanNorm (x - y) ^ C.alpha) := by
  constructor
  · intro γ hγ x
    apply (multiPartial_norm_le_iterated F hF _ x).trans
    apply (hbound _ (by omega) x).trans
    have : ((∑ r, (γ r).val : ℕ) : ℝ) ≤ C.order := by exact_mod_cast hγ
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.rpow_le_one_of_one_le_of_nonpos hk (by linarith [C.order_lt])) hA
  · intro γ hγ x y
    have hsup (z : Covariate d) : ‖iteratedFDeriv ℝ C.order F z‖ ≤ A * k ^ (-C.alpha) := by
      have he : C.order - C.smoothness = -C.alpha := by unfold ModelConstants.alpha; ring
      simpa only [he] using hbound C.order (by omega) z
    have hnext (z : Covariate d) : ‖fderiv ℝ (iteratedFDeriv ℝ C.order F) z‖ ≤
        A * k ^ (1 - C.alpha) := by
      rw [norm_fderiv_iteratedFDeriv]
      have he : ((C.order + 1 : ℕ) : ℝ) - C.smoothness = 1 - C.alpha := by
        unfold ModelConstants.alpha
        push_cast
        ring
      simpa only [he] using hbound (C.order + 1) le_rfl z
    have hfFinite : ContDiff ℝ (C.order + 1) F := hF.of_le (by simp)
    have hsmall := Convex.norm_image_sub_le_of_norm_fderiv_le
        (fun z (_hz : z ∈ (univ : Set (Covariate d))) =>
          hfFinite.contDiffAt.differentiableAt_iteratedFDeriv
            (by exact_mod_cast Nat.lt_succ_self C.order))
        (fun z _ => hnext z) convex_univ (mem_univ y) (mem_univ x)
    have hh := holder_of_scaled_sup_and_lipschitz k ‖x - y‖ A C.alpha
      ‖iteratedFDeriv ℝ C.order F x - iteratedFDeriv ℝ C.order F y‖
      (lt_of_lt_of_le (by norm_num) hk) (norm_nonneg _) hA C.alpha_pos C.alpha_le_one ((norm_sub_le _ _).trans (by nlinarith [hsup x, hsup y])) hsmall
    have h_multiPartial_diff_norm_le_iterated (γ : Fin d → ℕ) : |multiPartial F γ x - multiPartial F γ y| ≤
        ‖iteratedFDeriv ℝ (∑ r, γ r) F x - iteratedFDeriv ℝ (∑ r, γ r) F y‖ := by
      rw [multiPartial_eq_iteratedFDeriv univ isOpen_univ F (∑ r, γ r)
        (hF.of_le (by simp)).contDiffOn γ le_rfl x (mem_univ x),
        multiPartial_eq_iteratedFDeriv univ isOpen_univ F (∑ r, γ r)
        (hF.of_le (by simp)).contDiffOn γ le_rfl y (mem_univ y)]
      have hh := (iteratedFDeriv ℝ (∑ r, γ r) F x -
        iteratedFDeriv ℝ (∑ r, γ r) F y).le_opNorm (multiIndexBasis γ)
      simpa only [ContinuousMultilinearMap.sub_apply, Real.norm_eq_abs, multiIndexBasis_norm,
        Finset.prod_const_one, mul_one] using hh
    have heval := h_multiPartial_diff_norm_le_iterated (fun r => (γ r).val)
    rw [hγ] at heval
    exact (heval.trans hh).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) (covariate_norm_le_euclidean (x - y)) C.alpha_pos.le)
      (by positivity))
theorem holderNorm_of_scaled_derivatives  (C : ModelConstants d)
    (U : Set (Covariate d)) (F : Covariate d → ℝ) (hF : ContDiff ℝ ∞ F)
    (k A : ℝ) (hk : 1 ≤ k) (hA : 0 ≤ A)
    (hbound : ∀ q ≤ C.order + 1, ∀ x,
      ‖iteratedFDeriv ℝ q F x‖ ≤ A * k ^ ((q : ℝ) - C.smoothness)) :
    holderNorm U F C.order C.alpha ≤
      ENNReal.ofReal ((((C.order + 1 : ℕ) : ℝ) ^ d + 2) * A) := by
  obtain ⟨hs, hm⟩ := mixed_bounds_of_scaled_derivatives C F hF k A hk hA hbound
  have h_holderNorm_of_global_mixed_bounds : holderNorm U F C.order C.alpha ≤ ENNReal.ofReal (((C.order + 1 : ℕ) : ℝ) ^ d * A + 2 * A) := by
    have hL : 0 ≤ (2 * A) := by positivity
    have hs (γ : Fin d → Fin (C.order + 1)) (hγ : (∑ i, (γ i).val) ≤ C.order) :
        derivativeSup U (multiPartial F (fun i => (γ i).val)) ≤ ENNReal.ofReal A := by
      apply iSup_le
      intro x
      exact ENNReal.ofReal_le_ofReal (hs γ hγ x)
    have hh (γ : Fin d → Fin (C.order + 1)) (hγ : (∑ i, (γ i).val) = C.order) :
        holderSeminorm U (multiPartial F (fun i => (γ i).val)) C.alpha ≤ ENNReal.ofReal (2 * A) := by
      apply iSup_le
      intro x
      apply iSup_le
      intro y
      by_cases hxy : (x : Covariate d) = y
      · simp [hxy]
      · simp only [ite_eq_right_iff.mpr (fun h => False.elim (hxy h))]
        apply ENNReal.ofReal_le_ofReal
        apply (div_le_iff₀ (Real.rpow_pos_of_pos
          (euclideanNorm_pos_of_ne_zero (x.val - y.val) (sub_ne_zero.mpr hxy)) C.alpha)).mpr
        exact hm γ hγ x y
    have hsum : (∑ γ : Fin d → Fin (C.order + 1),
        if (∑ i, (γ i).val) ≤ C.order then
          derivativeSup U (multiPartial F (fun i => (γ i).val)) else 0) ≤
        ENNReal.ofReal (((C.order + 1 : ℕ) : ℝ) ^ d * A) := by
      calc
        _ ≤ ∑ _γ : Fin d → Fin (C.order + 1), ENNReal.ofReal A := by
          apply Finset.sum_le_sum
          intro γ hγ
          split_ifs with h
          · exact hs γ h
          · exact bot_le
        _ = _ := by
          rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hA)]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
            Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
    have hsem : (⨆ γ : Fin d → Fin (C.order + 1), if (∑ i, (γ i).val) = C.order then
        holderSeminorm U (multiPartial F (fun i => (γ i).val)) C.alpha else 0) ≤ ENNReal.ofReal (2 * A) := by
      apply iSup_le
      intro γ
      split_ifs with h
      · exact hh γ h
      · exact bot_le
    rw [ENNReal.ofReal_add (mul_nonneg (by positivity) hA) hL]
    exact add_le_add hsum hsem
  convert (h_holderNorm_of_global_mixed_bounds) using 1
  congr 1
  ring
def frameCoefficientL1  (P : MvPolynomial (Fin d) ℝ) : ℝ :=
  ∑ β ∈ P.support, |P.coeff β|
theorem frameCoefficientL1_nonneg  (P : MvPolynomial (Fin d) ℝ) :
    0 ≤ frameCoefficientL1 P := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
def frameScaledPolynomial  (P : MvPolynomial (Fin d) ℝ) : MvPolynomial (Fin d) ℝ :=
  MvPolynomial.bind₁ (fun r => MvPolynomial.C (1 / 8 ) * MvPolynomial.X r) P
theorem frameScaledPolynomial_eval  (P : MvPolynomial (Fin d) ℝ) (x : Covariate d) :
    MvPolynomial.eval x (frameScaledPolynomial P) = MvPolynomial.eval (fun r => x r / 8) P := by
  change MvPolynomial.eval₂Hom (RingHom.id ℝ) x _ = MvPolynomial.eval₂Hom (RingHom.id ℝ) _ P
  rw [frameScaledPolynomial, MvPolynomial.eval₂Hom_bind₁]
  simp only [map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', RingHom.id_apply]
  have he : (fun r => (1 / 8 : ℝ) * x r) = (fun r => x r / 8) := by funext r; ring
  rw [he]
theorem frame_complex_eval_norm_le_l1  (P : MvPolynomial (Fin d) ℝ)
    (z ) (hz : ∀ r, ‖z r‖ ≤ 1) :
    ‖MvPolynomial.eval₂ Complex.ofRealHom z P‖ ≤ frameCoefficientL1 P := by
  rw [MvPolynomial.eval₂_eq']
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro β hβ
  rw [norm_mul]
  change ‖(P.coeff β : ℂ)‖ * ‖∏ r, z r ^ β r‖ ≤ |P.coeff β|
  rw [Complex.norm_real]
  have hp : ‖∏ r, z r ^ β r‖ ≤ 1 := by
    rw [norm_prod]
    apply Finset.prod_le_one₀
    · intro r hr
      exact norm_nonneg _
    · intro r hr
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (hz r)
  exact (mul_le_mul_of_nonneg_left hp (abs_nonneg _)).trans_eq (mul_one _)
theorem frameScaledPolynomial_complex_bound  (P )
    (u : Covariate d) (hu : ‖u‖ ≤ 1) (z : Fin d → ℂ)
    (hz : ‖z - (fun r => (u r : ℂ))‖ < 1) :
    ‖MvPolynomial.eval z (complexify (frameScaledPolynomial P))‖ ≤ frameCoefficientL1 P := by
  have h_frameScaledPolynomial_complex_eval : MvPolynomial.eval z (complexify (frameScaledPolynomial P)) =
      MvPolynomial.eval₂ Complex.ofRealHom (fun r => z r / 8) P := by
    rw [complexify, MvPolynomial.eval_map]
    change MvPolynomial.eval₂Hom Complex.ofRealHom z _ =
      MvPolynomial.eval₂Hom Complex.ofRealHom _ P
    rw [frameScaledPolynomial, MvPolynomial.eval₂Hom_bind₁]
    simp only [map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
    change MvPolynomial.eval₂Hom Complex.ofRealHom (fun r => ((1 / 8 : ℝ) : ℂ) * z r) P = _
    have he : (fun r => ((1 / 8 : ℝ) : ℂ) * z r) = (fun r => z r / 8) := by
      funext r
      push_cast
      ring
    rw [he]
  rw [h_frameScaledPolynomial_complex_eval]
  apply frame_complex_eval_norm_le_l1
  intro r
  have : ‖z r - (u r : ℂ)‖ < 1 := (norm_le_pi_norm
    (z - fun r => (u r : ℂ)) r).trans_lt hz
  have : ‖(u r : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real] using (norm_le_pi_norm u r).trans hu
  have : ‖z r‖ ≤ 2 := by
    have := norm_sub_norm_le (z r) (u r : ℂ)
    linarith
  rw [norm_div]
  norm_num
  exact (div_le_one (by norm_num : (0 : ℝ) < 8)).mpr (by linarith)
theorem frameScaledPolynomial_contDiff  (P : MvPolynomial (Fin d) ℝ) :
    ContDiff ℝ ∞ (fun x => MvPolynomial.eval x (frameScaledPolynomial P)) :=
  (RoughRegime.PolynomialDerivatives.polynomial_contDiff _).of_le le_top
def highFrameProfile  (P : MvPolynomial (Fin d) ℝ) (u : Covariate d) : ℝ :=
  highWindowTensor d u * MvPolynomial.eval u (frameScaledPolynomial P)
theorem highFrameProfile_contDiff  (P : MvPolynomial (Fin d) ℝ) :
    ContDiff ℝ ∞ (highFrameProfile P) :=
  (highWindowTensor_contDiff d).mul (frameScaledPolynomial_contDiff P)
theorem highFrameProfile_tsupport_subset  (P ) :
    tsupport (highFrameProfile P) ⊆ tsupport (highWindowTensor d) :=
  tsupport_mul_subset_left (f := highWindowTensor d)
    (g := fun u => MvPolynomial.eval u (frameScaledPolynomial P))
theorem highFrameProfile_derivative_bound (d m : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ P : MvPolynomial (Fin d) ℝ, ∀ q ≤ m, ∀ u : Covariate d,
      ‖iteratedFDeriv ℝ q (highFrameProfile P) u‖ ≤ K * frameCoefficientL1 P := by
  have h_highWindowTensor_hasCompactSupport : HasCompactSupport (highWindowTensor d) := by
    apply (isCompact_closedBall (0 : Covariate d) (3 / 4 : ℝ)).of_isClosed_subset
      (isClosed_tsupport _)
    apply closure_minimal _ Metric.isClosed_closedBall
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)).mpr
    intro i
    simpa only [Real.norm_eq_abs] using (highWindowTensor_support_bound hx i).le
  have h_highWindowTensor_derivative_bound  := h_highWindowTensor_hasCompactSupport.exists_bound_iteratedFDeriv
    (highWindowTensor_contDiff d) m
  obtain ⟨B, hB0, hB⟩ := h_highWindowTensor_derivative_bound
  let B' := max B 1
  let Cp := ↑m.factorial * (Real.exp 1) ^ m
  let K := ↑2 ^ m * B' * Cp
  have : 0 < B' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have : 0 < Cp := by dsimp [Cp]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro P q hq u
  have hL1 := frameCoefficientL1_nonneg P
  by_cases hu : u ∈ tsupport (highWindowTensor d)
  · have hunorm : ‖u‖ ≤ 1 := by
      apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
      intro r
      rw [Real.norm_eq_abs]
      exact (highWindowTensor_tsupport_bound hu r).trans (by norm_num)
    have hder := norm_iteratedFDeriv_mul_le (highWindowTensor_contDiff d)
      (frameScaledPolynomial_contDiff P) u (n := q) (by simp)
    change ‖iteratedFDeriv ℝ q (highFrameProfile P) u‖ ≤ _ at hder
    calc
      _ ≤ _ := hder
      _ ≤ ∑ j ∈ Finset.range (q + 1), (q.choose j : ℝ) * B' *
          (frameCoefficientL1 P * Cp) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjq : j ≤ q := by simpa using (Finset.mem_range.mp hj)
        have hjm : j ≤ m := hjq.trans hq
        have hpm : q - j ≤ m := (Nat.sub_le _ _).trans hq
        gcongr
        · exact (hB j hjm u).trans (le_max_left _ _)
        have h_frameScaledPolynomial_derivatives_bound (q : ℕ) (hq : q ≤ m) : ‖iteratedFDeriv ℝ q (fun x => MvPolynomial.eval x (frameScaledPolynomial P)) u‖ ≤
            frameCoefficientL1 P * ↑m.factorial * (Real.exp 1) ^ m := by
          have : ↑q.factorial ≤ m.factorial := by exact_mod_cast Nat.factorial_le hq
          have := frameCoefficientL1_nonneg P
          have he : ↑1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
          have : (Real.exp 1) ^ q ≤ (Real.exp 1) ^ m := pow_le_pow_right₀ he hq
          by_cases hq0 : q = 0
          · subst q
            rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
            have h_frameScaledPolynomial_value_bound : |MvPolynomial.eval u (frameScaledPolynomial P)| ≤ frameCoefficientL1 P := by
              have hc := frameScaledPolynomial_complex_bound P u hunorm (fun r => (u r : ℂ)) (by simp)
              rw [complexify, MvPolynomial.eval_map] at hc
              change ‖MvPolynomial.eval₂ Complex.ofRealHom (Complex.ofRealHom ∘ u)
                (frameScaledPolynomial P)‖ ≤ frameCoefficientL1 P at hc
              rw [← MvPolynomial.eval₂_comp] at hc
              change ‖(MvPolynomial.eval u (frameScaledPolynomial P) : ℂ)‖ ≤ frameCoefficientL1 P at hc
              simpa only [Complex.norm_real, Real.norm_eq_abs] using hc
            apply h_frameScaledPolynomial_value_bound.trans
            have hmfac : (1 : ℝ) ≤ m.factorial := by exact_mod_cast Nat.factorial_pos m
            have hmexp : (1 : ℝ) ≤ (Real.exp 1) ^ m := one_le_pow₀ he
            have hh : (1 : ℝ) ≤ (m.factorial : ℝ) * (Real.exp 1) ^ m := by nlinarith
            have hx := mul_le_mul_of_nonneg_left hh (frameCoefficientL1_nonneg P)
            nlinarith
          have h_frameScaledPolynomial_derivative_bound : ‖iteratedFDeriv ℝ q (fun x => MvPolynomial.eval x (frameScaledPolynomial P)) u‖ ≤
              frameCoefficientL1 P * ↑q.factorial * (Real.exp 1) ^ q := by
            have hq : 0 < q := Nat.pos_of_ne_zero hq0
            simpa only [div_one] using real_polynomial_derivative_norm_bound
              (frameScaledPolynomial P) u 1 (frameCoefficientL1 P) (by norm_num)
              (frameCoefficientL1_nonneg P) (frameScaledPolynomial_complex_bound P u hunorm) hq
          · apply h_frameScaledPolynomial_derivative_bound.trans
            gcongr
        · simpa only [Cp, mul_assoc] using
            (h_frameScaledPolynomial_derivatives_bound (q - j) hpm)
      _ = ↑2 ^ q * B' * (frameCoefficientL1 P * Cp) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        congr 2
        rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
      _ ≤ ↑2 ^ m * B' * (frameCoefficientL1 P * Cp) := by
        gcongr
        norm_num
      _ = K * frameCoefficientL1 P := by dsimp [K]; ring
  · have hzero : iteratedFDeriv ℝ q (highFrameProfile P) u = 0 := by
      by_contra hn
      exact hu (highFrameProfile_tsupport_subset P
        ((support_iteratedFDeriv_subset (𝕜 := ℝ) q) (show u ∈ Function.support (iteratedFDeriv ℝ q (highFrameProfile P)) from hn)))
    rw [hzero, norm_zero]
    exact mul_nonneg hK.le hL1
def highPeriodizedChart (d k : ℕ) (j : HighWindowLabels d k)
    (G : Covariate d → ℝ) (x : Covariate d) : ℝ :=
  ∑ᶠ z : Fin d → ℤ, if (∀ r, (z r : ZMod k) = j r) then
    G (fun r => (k : ℝ) * x r - z r) else 0
theorem highPeriodizedChart_locallyFinite (d k : ℕ) (j : HighWindowLabels d k)
    (G : Covariate d → ℝ) (hG0 : ∀ u, highWindowTensor d u = 0 → G u = 0) :
    LocallyFinite (fun z : Fin d → ℤ => support (fun x : Covariate d =>
      if (∀ r, (z r : ZMod k) = j r) then G (fun r => (k : ℝ) * x r - z r) else 0)) := by
  have h_integerLatticeTranslate_locallyFinite : LocallyFinite (fun z : Fin d → ℤ => support (fun x : Covariate d =>
      G (fun r => x r - z r))) := by
    have hG : ∀ u, G u ≠ 0 → ∀ r, |u r| < 1 := (by
    intro u hu r
    have hw : highWindowTensor d u ≠ 0 := fun h => hu (hG0 u h)
    exact (highWindowTensor_support_bound hw r).trans (by norm_num))
    intro x
    refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x (by norm_num), ?_⟩
    let S : Fin d → Finset ℤ := fun r => Finset.Icc (⌊x r⌋ - 3) (⌊x r⌋ + 3)
    apply (Fintype.piFinset S).finite_toSet.subset
    intro z hz
    obtain ⟨y, hy, hnear⟩ := hz
    apply Fintype.mem_piFinset.mpr
    intro r
    have := abs_lt.mp (hG (fun r => y r - z r) hy r)
    have hnorm : ‖y - x‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hnear
    have hcoord  := (show |y r - x r| ≤ ‖y - x‖ from by
        simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (y - x) r).trans_lt hnorm
    have := abs_lt.mp hcoord
    have := Int.floor_le (x r)
    have := Int.lt_floor_add_one (x r)
    apply Finset.mem_Icc.mpr
    constructor
    · apply (Int.cast_le (R := ℝ)).mp
      push_cast
      linarith
    · apply (Int.cast_le (R := ℝ)).mp
      push_cast
      linarith
  have hlf := h_integerLatticeTranslate_locallyFinite
  have hc : Continuous (fun x : Covariate d => fun r => (k : ℝ) * x r) := by fun_prop
  apply (hlf.preimage_continuous hc).subset
  intro z x hx
  by_cases hz : ∀ r, (z r : ZMod k) = j r
  · change (if (∀ r, (z r : ZMod k) = j r) then
      G (fun r => (k : ℝ) * x r - z r) else 0) ≠ 0 at hx
    rw [ite_eq_left hz] at hx
    change G (fun r => (k : ℝ) * x r - z r) ≠ 0
    exact hx
  · simp [hz] at hx
theorem highPeriodizedChart_contDiff (d k : ℕ) (j : HighWindowLabels d k)
    (G : Covariate d → ℝ) (hG : ContDiff ℝ ∞ G)
    (hG0 : ∀ u, highWindowTensor d u = 0 → G u = 0) :
    ContDiff ℝ ∞ (highPeriodizedChart d k j G) := by
  apply ContMDiff.contDiff
  apply contMDiff_finsum _ (highPeriodizedChart_locallyFinite d k j G hG0)
  intro z
  apply ContDiff.contMDiff
  by_cases hz : ∀ r, (z r : ZMod k) = j r
  · simp only [ite_eq_left hz]
    apply hG.comp
    fun_prop
  · simp only [ite_eq_right hz]
    exact contDiff_const
theorem highPeriodizedChart_eventuallyEq_single (d k : ℕ) [NeZero k] (hk : 4 ≤ k)
    (j : HighWindowLabels d k) (G : Covariate d → ℝ)
    (hG0 : ∀ u, highWindowTensor d u = 0 → G u = 0) (x : Covariate d) :
    ∃ z : Fin d → ℤ, (∀ r, (z r : ZMod k) = j r) ∧
      highPeriodizedChart d k j G =ᶠ[𝓝 x]
        (fun y => G (fun r => (k : ℝ) * y r - z r)) := by
  have h_highPeriodicWindow_eventuallyEq_single (j : ZMod k) (x : ℝ) : ∃ z : ℤ, (z : ZMod k) = j ∧ highPeriodicWindow k j =ᶠ[𝓝 x]
      (fun y => highWindowProfile ((k : ℝ) * y - z)) := by
    have : (4 : ℝ) ≤ k := by exact_mod_cast hk
    have hk0 : (0 : ℝ) < k := by linarith
    let l : ℤ := ⌊x - (j.val : ℝ) / k + 1 / 2⌋
    let z : ℤ := (j.val : ℤ) + (k : ℤ) * l
    have hzj : (z : ZMod k) = j := by simp [z]
    have : (k : ℝ) * ((j.val : ℝ) / k) = j.val := by field_simp
    have : |(k : ℝ) * x - z| ≤ (k : ℝ) / 2 := by
      dsimp [z]
      push_cast
      apply abs_le.mpr
      dsimp [l]
      constructor <;> nlinarith [mul_le_mul_of_nonneg_left (Int.floor_le (x - (j.val : ℝ) / k + 1 / 2)) hk0.le,
        mul_lt_mul_of_pos_left (Int.lt_floor_add_one (x - (j.val : ℝ) / k + 1 / 2)) hk0]
    refine ⟨z, hzj, ?_⟩
    have hradius : 0 < 1 / (4 * (k : ℝ)) := by positivity
    filter_upwards [Metric.ball_mem_nhds x hradius] with y hy
    have : |(k : ℝ) * y - (k : ℝ) * x| < 1 / 4 := by
      have hdist : |y - x| < 1 / (4 * (k : ℝ)) := by
        simpa only [Metric.mem_ball, Real.dist_eq] using hy
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
        have  := not_le.mp hdist
        have hdvd  := (ZMod.intCast_eq_intCast_iff_dvd_sub z q k).mp
          (hzj.trans hqj.symm)
        obtain ⟨b, hb⟩ := hdvd
        have hb0 : b ≠ 0 := by
          intro hb0
          simp only [hb0, mul_zero] at hb
          exact hq (by omega)
        have : (1 : ℤ) ≤ |b| := by
          have := abs_pos.mpr hb0
          omega
        have hsepZ : (k : ℤ) ≤ |q - z| := by
          rw [hb, abs_mul, abs_of_nonneg (by omega : (0 : ℤ) ≤ k)]
          nlinarith
        have : (k : ℝ) ≤ |(q : ℝ) - z| := by exact_mod_cast hsepZ
        have : |(q : ℝ) - z| ≤ |(k : ℝ) * y - q| +
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
  choose z hz he using fun r => (h_highPeriodicWindow_eventuallyEq_single (j r) (x r))
  refine ⟨z, hz, ?_⟩
  have hcoord (r : Fin d) : ∀ᶠ y : Covariate d in 𝓝 x,
      highPeriodicWindow k (j r) (y r) = highWindowProfile ((k : ℝ) * y r - z r) :=
    (continuous_apply r).continuousAt.eventually (he r)
  filter_upwards [Filter.eventually_all.mpr hcoord] with y hy
  rw [highPeriodizedChart, finsum_eq_single _ z]
  · simp only [ite_eq_left hz]
  · intro q hq
    by_cases hqj : ∀ r, (q r : ZMod k) = j r
    · simp only [ite_eq_left hqj]
      by_contra hnonzero
      have hprof  :=
        fun h => hnonzero (hG0 _ h)
      have hqeq : q = z := by
        funext r
        have hqr : highWindowProfile ((k : ℝ) * y r - q r) ≠ 0 := by
          intro hh
          exact hprof (Finset.prod_eq_zero (Finset.mem_univ r) hh)
        have hqpositive  :=
          lt_of_le_of_ne (highWindowProfile_nonneg _) (Ne.symm hqr)
        have hzpositive : 0 < highWindowProfile ((k : ℝ) * y r - z r) := by
          have h_highPeriodicWindow_term_le : highWindowProfile ((k : ℝ) * y r - q r) ≤ highPeriodicWindow k (j r) (y r) := by
            have hz  := hqj r
            have hh := single_le_finsum (q r) (highPeriodicWindow_locallyFinite k (j r) |>.point_finite (y r))
              (fun q : ℤ => show 0 ≤ (if (q : ZMod k) = (j r) then
                highWindowProfile ((k : ℝ) * y r - q) else 0) from by
                split_ifs
                · exact highWindowProfile_nonneg _
                · exact le_rfl)
            simpa only [ite_eq_left hz, highPeriodicWindow] using hh
          have hh := h_highPeriodicWindow_term_le
          rw [hy r] at hh
          exact hqpositive.trans_le hh
        have hzs : z r ∈ support (fun a : ℤ => if (a : ZMod k) = j r then
            highWindowProfile ((k : ℝ) * y r - a) else 0) := by
          simpa only [mem_support, ite_eq_left (hz r)] using hzpositive.ne'
        exact highPeriodicWindow_support_subsingleton k (by omega) (j r) (y r) (by simpa only [mem_support, ite_eq_left (hqj r)] using hqr) hzs
      exact hq hqeq
    · simp only [ite_eq_right hqj]
theorem highPeriodizedChart_derivative_support_lift (d k : ℕ) [NeZero k] (hk : 4 ≤ k)
    (j : HighWindowLabels d k) (G : Covariate d → ℝ)
    (hG0 : ∀ u, highWindowTensor d u = 0 → G u = 0) (q : ℕ) (x : Covariate d)
    (hx : iteratedFDeriv ℝ q (highPeriodizedChart d k j G) x ≠ 0) :
    ∃ z : Fin d → ℤ, (∀ r, (z r : ZMod k) = j r) ∧
      ∀ r, |(k : ℝ) * x r - z r| ≤ 3 / 4 := by
  obtain ⟨z, hz, he⟩ := highPeriodizedChart_eventuallyEq_single d k hk j G hG0 x
  let A : Covariate d → ℝ := fun y => G (fun r => (k : ℝ) * y r - z r)
  have hn : iteratedFDeriv ℝ q A x ≠ 0 := by
    rwa [← (he.iteratedFDeriv ℝ q).eq_of_nhds]
  have hsub : support (iteratedFDeriv ℝ q A) ⊆ tsupport A :=
    support_iteratedFDeriv_subset (𝕜 := ℝ) q
  have hs : x ∈ tsupport A := hsub (show x ∈ support (iteratedFDeriv ℝ q A) from hn)
  have ht  :=
    (tsupport_comp_subset_preimage G (by fun_prop)) hs
  have h_highPeriodizedChart_tsupport_profile : tsupport G ⊆ tsupport (highWindowTensor d) := by
    apply closure_mono
    intro u hu
    exact fun h => hu (hG0 u h)
  exact ⟨z, hz, highWindowTensor_tsupport_bound
    (h_highPeriodizedChart_tsupport_profile ht)⟩
theorem highPeriodizedChart_derivative_overlap (d k : ℕ) [NeZero k] (hk : 4 ≤ k)
    (G : HighWindowLabels d k → Covariate d → ℝ)
    (hG0 : ∀ j u, highWindowTensor d u = 0 → G j u = 0) (q : ℕ) (x : Covariate d) :
    (Finset.univ.filter (fun j => iteratedFDeriv ℝ q (highPeriodizedChart d k j (G j)) x ≠ 0)).card ≤
      2 ^ d :=
  have h_highActiveLabelBox_card_le : (highActiveLabelBox d k x).card ≤ 2 ^ d := by
    unfold highActiveLabelBox
    rw [Fintype.card_piFinset]
    calc
      _ ≤ ∏ _r : Fin d, 2 := by
        apply Finset.prod_le_prod'
        intro r hr
        exact (Finset.card_insert_le _ _).trans (by simp)
      _ = 2 ^ d := by simp
  have h_highPeriodizedChart_derivative_active_subset : Finset.univ.filter (fun j => iteratedFDeriv ℝ q (highPeriodizedChart d k j (G j)) x ≠ 0) ⊆
      highActiveLabelBox d k x := by
    intro j hj
    obtain ⟨z, hz, hclose⟩ := highPeriodizedChart_derivative_support_lift d k hk j (G j)
      (hG0 j) q x (Finset.mem_filter.mp hj).2
    apply Fintype.mem_piFinset.mpr
    intro r
    have he := integer_close_three_quarters ((k : ℝ) * x r) (z r) (hclose r)
    rcases he with he | he
    · simp only [← hz r, he, Finset.mem_insert, Finset.mem_singleton, true_or]
    · simp only [← hz r, he, Finset.mem_insert, Finset.mem_singleton, or_true]
  (Finset.card_le_card h_highPeriodizedChart_derivative_active_subset).trans
    h_highActiveLabelBox_card_le
def highFrameField (d k : ℕ) [NeZero k] (η : ℝ)
    (P : HighWindowLabels d k → MvPolynomial (Fin d) ℝ) (x : Covariate d) : ℝ :=
  η * ∑ j, highPeriodizedChart d k j (highFrameProfile (P j)) x
theorem highFrameProfile_zero_of_window_zero  (P : MvPolynomial (Fin d) ℝ)
    (u : Covariate d) (hu : highWindowTensor d u = 0) : highFrameProfile P u = 0 := by
  simp only [highFrameProfile, hu, zero_mul]
theorem highFrameField_contDiff (d k : ℕ) [NeZero k] (η : ℝ)
    (P : HighWindowLabels d k → MvPolynomial (Fin d) ℝ) :
    ContDiff ℝ ∞ (highFrameField d k η P) := by
  change ContDiff ℝ ∞ (fun x => η • ∑ j, highPeriodizedChart d k j (highFrameProfile (P j)) x)
  apply ContDiff.const_smul
  apply ContDiff.sum
  intro j hj
  exact highPeriodizedChart_contDiff d k j _ (highFrameProfile_contDiff (P j))
    (highFrameProfile_zero_of_window_zero (P j))
end NearlyMinimax
