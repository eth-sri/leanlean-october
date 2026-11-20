module
public import DensityStrip.Pair
public import DensityStrip.Exponents
public import TaoTrudgianYang2025.ExponentPairBProcess
public import TaoTrudgianYang2025.BetaHalfDuality
public import MathCollab.Density.LargeValues
public import MathCollab.Density.DensityConclusion

@[expose] public section
noncomputable section
open Real Finset Filter MathCollab.Density MathCollab.Density.Stronger GuthMaynard.Improvement
open Montgomery.RationalMoment.RightDetector TaoTrudgianYang2025 Expdb
namespace DensityStrip

/-- The B transform of the triangle inequality suffices for the critical
tail in the classical three-quarter window. -/
private theorem half_pair : ExponentPair (1/2) (1/2) := by
  have h : ExponentPair 0 1 := by
    apply exponentPair_of_beta_bound_half (by norm_num [InExponentPairTriangle]) (by norm_num)
    intro α _
    simpa [exponentPairLine] using exponentSumGrowthExponent_le_iff.mpr (isExponentSumBound_self α)
  convert h.bProcess using 1 <;> norm_num

private theorem strong_window {s a e : ℝ} (hs : 3/4<s) (hs' : s≤1) (ha : 1/2≤a)
    (hid : a*(2*s)=1) (he : 0<e) (hη : e≤(s-3/4)/8) (ha' : 3*a/2+e≤1) :
    WindowCount s a (3*a*(1-s)) 10 e := by
  let κ := (s-3/4)/2
  obtain ⟨C,hC,hlv⟩ := large_values (κ:=κ) (by dsimp [κ]; linarith) he
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (2:ℝ)] with T ht
  intro N Q b W hn hlo hhi hb hloc hsep hlarge
  let V := Q^s*T^(-2*e); let p := 3*a*(1-s); let x := logb T Q
  have hT : 1<T := by linarith
  have ht' : 0<T := by linarith
  have hn' : 0<Q := by linarith
  have hV : 0<V := by dsimp [V]; positivity
  have hx : a≤x := by simpa only [logb_rpow ht' hT.ne'] using logb_le_logb_of_le hT (rpow_pos_of_pos ht' _) hlo
  have hx' : x≤3*a/2+e := by simpa only [logb_rpow ht' hT.ne'] using logb_le_logb_of_le hT hn' hhi
  have hheight : Q^(3/4+κ) ≤ V := by
    dsimp only [V]; exponents hT
    change (3/4+κ)*x ≤ s*x+-2*e
    dsimp [κ]; nlinarith only [mul_nonneg (show 0≤x-1/2 by linarith) (sub_nonneg.mpr hs.le),hη]
  have H := hlv T V N b W ht (by change 0 < (N:ℝ) at hn'; exact_mod_cast hn') hV
    ((rpow_le_rpow_of_exponent_le hT.le (by linarith : 1/3≤a)).trans hlo)
    (hhi.trans ((rpow_le_rpow_of_exponent_le hT.le ha').trans_eq (rpow_one _))) hheight (by
      intro n hn; apply hb n
      exact (sourceRatioIndices_mem hn'.le n).mpr (by change (N:ℝ) < n ∧ (n:ℝ) ≤ 2*N; exact_mod_cast mem_Ioc.mp hn)) ⟨T,hloc⟩ hsep (by
      intro t ht; simpa only [detectingPolynomial_eq_boundedPolynomial] using hlarge t ht)
  have hdiag : Q^2/V^2 ≤ T^(p+9*e) := by
    dsimp only [V,p]; exponents hT; norm_num only [Nat.cast_ofNat]
    change 2*x-2*(s*x+-2*e) ≤ 3*a*(1-s)+9*e
    nlinarith only [mul_le_mul_of_nonneg_right hx' (show 0≤2-2*s by linarith),he,mul_nonneg he.le (show 0 ≤ s by linarith)]
  have hsecond : Q^3*sqrt T/V^4 ≤ T^(p+9*e) := by
    rw [sqrt_eq_rpow]; dsimp only [V,p]; exponents hT; norm_num only [Nat.cast_ofNat]
    change 3*x+1/2-4*(s*x+-2*e) ≤ 3*a*(1-s)+9*e
    nlinarith only [hid,he,mul_nonneg (sub_nonneg.mpr hx) (show 0≤4*s-3 by linarith)]
  exact (H.trans (mul_le_mul_of_nonneg_left (add_le_add hdiag hsecond) (by positivity))).trans_eq <| by
    rw [show p+10*e=e+(p+9*e) by ring,rpow_add ht' e (p+9*e)]; ring

theorem strong_density {s ε : ℝ} (hs : 3/4<s) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ T : ℝ, 2≤T → (zetaDensityCount s T:ℝ) ≤ C*T^(3*(1-s)/(2*s)+ε) := by
  by_cases hr : s<1
  swap
  · refine ⟨1,by norm_num,fun T ht => ?_⟩
    rw [zetaDensityCount_eq_zero_of_one_le (le_of_not_gt hr)]; push_cast; positivity
  let a := 1/(2*s)
  have hpos : 0<2*s := by linarith
  have heq : a*(2*s)=1 := div_mul_cancel₀ _ hpos.ne'
  have ha : 1/2≤a := (le_div_iff₀ hpos).mpr (by linarith)
  have ha' : a<2/3 := (div_lt_iff₀ hpos).mpr (by linarith)
  have hθ : 1/8 < (3*a/4)*(s-1/2) := by nlinarith only [heq,ha']
  convert pair_density half_pair (by norm_num) ⟨hs,hr,ha,ha',hθ⟩ _ _ (by norm_num : (0:ℝ)≤10)
    (c:=min ((s-3/4)/8) (1-3*a/2)) (lt_min (by linarith) (by linarith)) _ hε using 1
  · dsimp [a]; ring_nf
  · nlinarith only [heq,ha]
  · norm_num; nlinarith only [heq,ha']
  · intro e he he'; exact strong_window hs hr.le ha heq he (le_min_iff.mp he').1 (by linarith only [(le_min_iff.mp he').2])
end DensityStrip
