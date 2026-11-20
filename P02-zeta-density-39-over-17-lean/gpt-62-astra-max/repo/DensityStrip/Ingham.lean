module
public import DensityStrip.Low
public import DensityStrip.Exponents
public import GuthMaynard.Improvement.NativeDensitySourceBridge
public import GuthMaynard.Improvement.SeparatedSecondMoment

@[expose] public section
open Real Finset Filter MathCollab.Density MathCollab.Density.Stronger GuthMaynard.Improvement
noncomputable section
namespace DensityStrip

/-- The diagonal and height terms of the separated second moment are
controlled at opposite ends of the powered window. -/
private theorem mean_window {s a e : ℝ} (hs : 1/2 < s) (hs' : s ≤ 1) (ha : a ≤ 1)
    (hid : a*(2-s)=1) (he : 0<e) (he' : e≤1/100) : WindowCount s a (3*a*(1-s)) 10 e := by
  let p := 3*a*(1-s)
  refine ⟨408,by norm_num,?_⟩
  filter_upwards [eventually_ge_atTop (2:ℝ),log_pow_eventually_le_rpow 1 he] with T hT hlog
  intro Q; try dsimp only
  let N : ℝ := Q
  intro b W hN hlo hhi hb hloc hsep hlarge
  change 2 ≤ N at hN
  have ht : 1<T := by linarith
  have ht' : 0<T := by linarith
  have hn : 0<N := by linarith
  let V := N^s*T^(-2*e)
  have hV : 0<V := by dsimp [V]; positivity
  have hl : a ≤ logb T N := by simpa only [logb_rpow ht' ht.ne'] using logb_le_logb_of_le ht (rpow_pos_of_pos ht' _) hlo
  have hu : logb T N ≤ 3*a/2+e := by simpa only [logb_rpow ht' ht.ne'] using logb_le_logb_of_le ht hn hhi
  have hheight : N*T/V^2 ≤ T^(p+4*e) := by
    dsimp [V,p]; exponents ht; norm_num only [Nat.cast_ofNat]
    nlinarith only [hid,mul_nonneg (sub_nonneg.mpr hl) (show 0≤2*s-1 by linarith)]
  have hdiag : N^2/V^2 ≤ T^(p+6*e) := by
    dsimp [V,p]; exponents ht; norm_num only [Nat.cast_ofNat]
    nlinarith only [mul_le_mul_of_nonneg_right hu (show 0 ≤ 2-2*s by linarith),mul_nonneg he.le (by linarith : 0 ≤ s)]
  have hN2 : N ≤ T^2 := hhi.trans ((rpow_le_rpow_of_exponent_le ht.le (by linarith : 3*a/2+e≤2)).trans_eq (rpow_two _))
  have hh : log (2*N) ≤ 3*T^e := calc
    _ ≤ log (T*T^2) := log_le_log (by positivity) (mul_le_mul hT hN2 hn.le ht'.le)
    _ ≤ _ := by rw [log_mul ht'.ne' (pow_pos ht' _).ne',log_pow]; norm_num at hlog ⊢; linarith
  have hlogN : 0 ≤ log (2*N) := log_nonneg (by linarith)
  have H := separated_second_moment hN ht'.le b hb W hloc hsep
  have hw := sum_le_sum fun t ht => pow_le_pow_left₀ hV.le (hlarge t ht) 2
  rw [sum_const,nsmul_eq_mul] at hw
  apply ((le_div_iff₀ (sq_pos_of_pos hV)).mpr (hw.trans H)).trans
  calc
    _ = 102*(N*T/V^2+(N^2/V^2)*log (2*N)) := by ring
    _ ≤ 102*(T^(p+4*e)+T^(p+6*e)*(3*T^e)) := by gcongr
    _ = 102*(T^(p+4*e)+3*T^(p+7*e)) := by rw [show p+7*e=(p+6*e)+e by ring,rpow_add ht' (p+6*e)]; ring
    _ ≤ 102*(T^(p+10*e)+3*T^(p+10*e)) := by gcongr <;> linarith
    _ = _ := by dsimp [p]; ring

theorem ingham {s ε : ℝ} (hl : 1/2 ≤ s) (hr : s ≤ 9/13) (hε : 0 < ε) :
    ∃ C : ℝ, 0<C ∧ ∀ T : ℝ, 2≤T → (zetaDensityCount s T:ℝ) ≤ C*T^(3*(1-s)/(2-s)+ε) := by
  rcases hl.eq_or_lt with heq | hs
  · subst s
    exact native_density_epsilon_bound (by norm_num) (by norm_num) GuthMaynard.NativeMoment.ingham_zero_density_at_half_native hε
  let a := 1/(2-s)
  have hd : 0 < 2-s := by linarith
  have ha : 2/3 < a := (lt_div_iff₀ hd).mpr (by linarith)
  have ha' : a ≤ 1 := (div_le_iff₀ hd).mpr (by linarith)
  have hid : a*(2-s)=1 := div_mul_cancel₀ _ hd.ne'
  convert low_density hs (by linarith) ha (by linarith) (p:=3*a*(1-s))
    (by nlinarith only [mul_nonneg (show 0≤a-2/3 by linarith) (show 0≤1-s by linarith)]) (by norm_num : (5:ℝ)≤10)
    (fun _ he he' => mean_window hs (by linarith) ha' hid he he') hε using 1 <;> dsimp [a] <;> ring_nf

end DensityStrip
