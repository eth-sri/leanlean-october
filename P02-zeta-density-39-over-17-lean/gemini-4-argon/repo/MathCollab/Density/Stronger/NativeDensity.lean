module
public import PairActualDensity
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import TaoTrudgianYang2025.ExponentPairBProcess
public import MathCollab.Density.Stronger.ShortZeroCount
public import MathCollab.Density.DensityConclusion

@[expose] public section

open Filter MeasureTheory Set Real Montgomery.RationalMoment Montgomery.RationalMoment.RightDetector TaoTrudgianYang2025
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

private theorem smoothShortZeroCount_eq_rightDetector (η σ δ T : ℝ) :
    RightDetector.smoothShortZeroCount η σ (lowerExponent σ) δ T =
      smoothShortZeroCount η σ δ T := by
  have hs : RightDetector.smoothingExponent (lowerExponent σ) = smoothingExponent σ :=
    smoothingExponent_eq.symm
  have hy : RightDetector.detectorY (lowerExponent σ) T = detectorY σ T := by
    unfold RightDetector.detectorY detectorY; rw [hs]
  have ht : RightDetector.smoothTaylorIndices (lowerExponent σ) T = smoothTaylorIndices σ T := by
    unfold RightDetector.smoothTaylorIndices smoothTaylorIndices; rw [hy]
  have hp : RightDetector.smoothPoweredIndices (lowerExponent σ) δ T =
      smoothPoweredIndices σ δ T := by
    unfold RightDetector.smoothPoweredIndices smoothPoweredIndices
      RightDetector.smoothPowerBound smoothPowerBound; rw [ht, hs]
  have hc : RightDetector.smoothPoweredFamilyCoefficient η (lowerExponent σ) δ T =
      smoothPoweredFamilyCoefficient η σ δ T := by
    ext q n; unfold RightDetector.smoothPoweredFamilyCoefficient smoothPoweredFamilyCoefficient; rw [hy]
  unfold RightDetector.smoothShortZeroCount smoothShortZeroCount
    RightDetector.smoothShortZeroFinset smoothShortZeroFinset
    RightDetector.smoothPoweredFamilyScale smoothPoweredFamilyScale
  rw [hp, hc]

theorem stronger_density_bound_native {σ ε : ℝ} (hσ : 3/4 < σ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T : ℝ) ≤ C*T^(3*(1-σ)/(2*σ)+ε) := by
  by_cases hσ' : σ < 1
  · let a : ℝ := lowerExponent σ
    have hσ0 : 0 < σ := by linarith
    have ha_eq : 3*a*(1-σ) = 3*(1-σ)/(2*σ) := by unfold a lowerExponent; ring
    have hth : 1/8 < (3*a/4)*(σ-1/2) := by
      unfold a lowerExponent
      rw [show (3*(1/(2*σ))/4)*(σ-1/2) = (6*σ-3)/(16*σ) by field_simp; ring]
      exact (div_lt_div_iff₀ (by norm_num) (by positivity)).mpr (by linarith)
    have hwp : PhysicalDetectorWindow σ a := ⟨hσ, hσ',
      by unfold a lowerExponent; exact (div_le_div_iff₀ (by norm_num) (by positivity)).mpr (by linarith),
      by unfold a lowerExponent; exact (div_lt_div_iff₀ (by positivity) (by norm_num)).mpr (by linarith),
      hth⟩
    let r : ℕ := max 3 ⌈1/(σ-3/4)⌉₊
    have hr : 3 ≤ r := le_max_left _ _
    have hrR : (3:ℝ) ≤ r := by exact_mod_cast hr
    have hR : 1/(σ-3/4) ≤ (r:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 3 _)
    have hpair := (exponentPair_heathBrown hr).bProcess
    let k : ℝ := 1-(3*(r:ℝ)-2)/((r:ℝ)*((r:ℝ)-1)*((r:ℝ)+2))-1/2
    let l : ℝ := 2/(((r:ℝ)-1)^2*((r:ℝ)+2))+1/2
    have hpair' : ExponentPair k l := hpair
    have hk : 0 < k := by
      have hs := heathBrownPair_slope hrR
      have hp := heathBrownPairK_pos hrR
      unfold heathBrownPairL heathBrownPairK at hs hp
      dsimp [k]; linarith
    have hk_half : k ≤ 1/2 := hpair'.inTriangle.2.1
    have hl_half : 1/2 ≤ l := hpair'.inTriangle.2.2.1
    have hl_sub : l - 1/2 ≤ σ - 3/4 := by
      have hd : 2*(r:ℝ) ≤ ((r:ℝ)-1)^2*((r:ℝ)+2) := by nlinarith [sq_nonneg ((r:ℝ)-3)]
      have h1 : l - 1/2 ≤ 1/(r:ℝ) := by
        dsimp [l]; rw [add_sub_cancel_right]
        calc 2/(((r:ℝ)-1)^2*((r:ℝ)+2)) ≤ 2/(2*(r:ℝ)) :=
              div_le_div_of_nonneg_left (by norm_num) (by positivity) hd
          _ = 1/(r:ℝ) := by ring
      exact h1.trans ((div_le_iff₀ (by positivity)).mpr
        ((div_le_iff₀ (by linarith)).mp hR |>.trans_eq (mul_comm _ _)))
    let θ : ℝ := (3*a/4)*(σ-1/2)
    have hfirst : 1-6*θ ≤ 3*a*(1-σ) := by
      rw [← sub_nonpos, show 1-6*θ - 3*a*(1-σ) = (2*σ-3)/(8*σ) by
        dsimp [θ, a, lowerExponent]; field_simp; ring]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    have hsecond : 1+l/k-(4+(2+4*l)/k)*θ ≤ 3*a*(1-σ) := by
      rw [← sub_nonpos, show 1+l/k-(4+(2+4*l)/k)*θ - 3*a*(1-σ) =
          (-8*(σ-3/4) - 16*(σ-3/4)*(1/2-k) + (12-8*σ)*(l-1/2))/(16*k*σ) by
        dsimp [θ, a, lowerExponent]; field_simp; ring]
      refine div_nonpos_of_nonpos_of_nonneg ?_ (by positivity)
      nlinarith [mul_nonneg (show 0 ≤ 16*(σ-3/4) by linarith) (show 0 ≤ 1/2-k by linarith),
        mul_nonneg (show 0 ≤ 6-(12-8*σ) by linarith) (show 0 ≤ l-1/2 by linarith)]
    let b : ℝ := 4+(2+4*l)/k
    have hb : 0 < b := by dsimp [b]; positivity
    let s : ℝ := min ((θ-1/8)/4) (ε/(8*(b+6)))
    have hs : 0 < s := lt_min (by dsimp [θ]; linarith) (by positivity)
    have hsθ : s ≤ (θ-1/8)/4 := min_le_left _ _
    have hsb : s*(8*(b+6)) ≤ ε := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    have hs6 : 6*s ≤ ε/4 := by nlinarith [mul_pos hs hb]
    have hsb' : b*s ≤ ε/4 := by nlinarith
    let q : ℝ := θ-s
    let δ : ℝ := min s (1/16)
    have hδ : 0 < δ := lt_min hs (by norm_num)
    have hδs : δ ≤ s := min_le_left _ _
    have hδcap : δ ≤ 1/16 := min_le_right _ _
    have hq : 1/8 < q := by dsimp [q]; linarith
    have hmargin : q+δ/2 < θ := by dsimp [q]; linarith
    let η : ℝ := min (ε/24) ((σ-3/4)/16)
    have hη : 0 < η := lt_min (by positivity) (by linarith)
    have hηeps : 12*η ≤ ε/2 := by have := min_le_left (ε/24) ((σ-3/4)/16); dsimp [η]; linarith
    have hmargin_short : 8*η < σ-3/4 := by have := min_le_right (ε/24) ((σ-3/4)/16); dsimp [η]; linarith
    obtain ⟨Cs,hCs,hshort⟩ := smoothShortZeroCount_bound hσ hσ' hη hmargin_short δ
    obtain ⟨Cl,hCl,hlong⟩ := Physical.smoothLongZeroCount_pair_tail_general hpair' hk hwp
      hδ (by linarith) hη (show 0 < ε/2 by positivity) hq hmargin
      (show 1-6*q ≤ 3*a*(1-σ)+(ε/2)/2 by dsimp [q,θ] at *; linarith)
      (show 1+l/k-(4+(2+4*l)/k)*q ≤ 3*a*(1-σ)+(ε/2)/2 by
        change 1+l/k-b*(θ-s) ≤ _; change 1+l/k-b*θ ≤ _ at hsecond; nlinarith)
    have hslab : ∀ᶠ T : ℝ in atTop,
        (zetaSlabCount σ T (2*T):ℝ) ≤ (Cs+Cl)*T^(3*a*(1-σ)+ε) := by
      filter_upwards [hshort,hlong,eventually_ge_atTop (1:ℝ)] with T hsT hlT hT
      unfold densityExponent at hsT
      rw [← smoothShortZeroCount_eq_rightDetector, ← ha_eq] at hsT
      have hs' := hsT.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hT (show 3*a*(1-σ)+12*η ≤ 3*a*(1-σ)+ε by linarith)) hCs.le)
      have hl' := hlT.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hT (show 3*a*(1-σ)+ε/2 ≤ 3*a*(1-σ)+ε by linarith)) hCl.le)
      rw [Physical.smooth_zeroCount_partition η σ a δ T,Nat.cast_add]
      nlinarith only [hs',hl']
    have hp : 0 < 3*a*(1-σ)+ε := by rw [ha_eq]; positivity
    rw [← ha_eq]
    exact zetaDensity_bound_of_eventual_slabs hp (by positivity : 0 < Cs+Cl) hslab
  · refine ⟨1, by norm_num, fun T hT => ?_⟩
    rw [zetaDensityCount_eq_zero_of_one_le (not_lt.mp hσ')]
    simp only [Nat.cast_zero, one_mul]; positivity

