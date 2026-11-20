module
public import DensityStrip.Kernel
public import GuthMaynard.NativeSource.GuthMaynard.TerminalTypeI
public import WeylPort.AFE.ZetaTruncation
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp

@[expose] public section
noncomputable section
open Real Complex Finset Filter Asymptotics TaoTrudgianYang2025 GuthMaynard.NativeMoment
open scoped ComplexConjugate
namespace DensityStrip

/-- The long, un-mollified alternative has monotone weights, so an exponent
pair for the logarithmic phase controls the entire block. -/
theorem long_bound {k l e : ℝ} (pair : ExponentPair k l) (he : 0<e) : ∃ C : ℝ, 0 < C ∧ ∀ {A N : ℕ} {s t : ℝ},
    0 < N → N < A → 0 ≤ s → 0 < t →
    ‖dirichletPoly N (classicalZetaLongLineCoeff A s) t‖ ≤
      C*((N:ℝ)^(-s)*(t^(k+e)*(N:ℝ)^(l-k)+(N:ℝ)/t)) := by
  obtain ⟨C,hC,h⟩ := log_prefix_bound pair he
  refine ⟨C,hC,?_⟩
  intro A N s t hN hNA hs ht
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hp (j : ℕ) (hj : j ≤ N) := h hN (a:=N+1) (b:=N+j) (by omega) (by omega) ht
  have hb := long_block_of_prefix_bound A N s t hs hN hNA (B:=C*(t^(k+e)*(N:ℝ)^(l-k)+(N:ℝ)/t)) (fun j hj => by
    have he : Icc (N+1) (N+j) = Ico (N+1) (N+1+j) := by ext i; simp; omega
    have hh := hp j hj
    rw [he, sum_Ico_eq_sum_range, Nat.add_sub_cancel_left] at hh
    convert hh using 2
    apply sum_congr rfl
    intro n _
    simpa only [Nat.cast_add, Nat.cast_one] using unitaryPhase_logarithmicPhase_eq_cpow t (N+1+n) (by omega))
  refine hb.trans ?_
  rw [mul_left_comm]
  have hx : (N+1:ℝ)^(-s) ≤ (N:ℝ)^(-s) := Real.rpow_le_rpow_of_nonpos hn (by linarith) (by linarith)
  gcongr

/-- A fixed logarithmic loss costs an arbitrarily small power. -/
theorem logloss {η C : ℝ} (hη : 0 < η) (hC : 0 < C) :
    ∀ᶠ T : ℝ in atTop, C*(1+Real.log T) ≤ T^η := by
  filter_upwards [eventually_ge_atTop (1:ℝ), (tendsto_rpow_atTop hη).eventually_ge_atTop (2*C),
    (isLittleO_log_rpow_atTop hη).bound (show 0 < (2*C)⁻¹ by positivity)] with T hT hc hb
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hT),
    abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hT) η)] at hb
  have hh : Real.log T ≤ T^η/(2*C) := by simpa only [div_eq_inv_mul] using hb
  have := (le_div_iff₀ (by positivity)).mp hh
  linarith

/-- On any vertical line between the half-line and one, the elementary
Euler--Maclaurin truncation at the square of the height has bounded error. -/
private theorem truncation {t b : ℝ} (ht : 1≤t) (hb : 1/2≤b) (hb' : b≤1) :
    let N := ⌈t⌉₊^2; let s := (b:ℂ)+(t:ℂ)*I
    ‖riemannZeta s‖ ≤ 9+‖classicalZetaPartialSum N s‖ := by
  intro N s
  have hceil := Nat.le_ceil t
  have hc : 0<(⌈t⌉₊:ℝ) := by linarith
  have hc' := Nat.ceil_lt_add_one (by linarith : 0≤t)
  have hn : 0<N := pow_pos (by exact_mod_cast hc) 2
  have hN : 1≤(N:ℝ) := by exact_mod_cast hn
  have hNr : 0<(N:ℝ) := by positivity
  have hs : s.re=b := by simp [s]
  have him : s.im=t := by simp [s]
  have hs1 : s≠1 := by intro h; rw [h] at him; norm_num at him; linarith
  have hs0 : s≠0 := by intro h; rw [h] at hs; norm_num at hs; linarith
  have h := DhimanKadiriQuesadaHerrera2026.norm_zeta_sub_regularized_sum_le hn (s:=s) (by linarith) hs1
  let Z := ∑ n ∈ range (N+1), 1/(n:ℂ)^s
  let P := (N:ℂ)^(1-s)/(s-1)
  change ‖riemannZeta s-(Z+P)‖ ≤ _ at h
  have hid : Z = classicalZetaPartialSum N s := by
    dsimp [Z,classicalZetaPartialSum]
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (Nat.succ_pos _), Nat.succ_eq_add_one, Ico_add_one_right_eq_Icc]
    simp [Complex.zero_cpow hs0,Complex.cpow_neg,one_div]
  have hpow : (N:ℝ)^(1/2:ℝ) = ⌈t⌉₊ := by
    dsimp [N]; push_cast; rw [← sqrt_eq_rpow,sqrt_sq (by positivity)]
  have hden : t≤‖s-1‖ := by simpa [him,abs_of_nonneg (by linarith : 0≤t)] using abs_im_le_norm (s-1)
  have hp : ‖P‖ ≤ 2 := by
    dsimp [P]; rw [norm_div,Complex.norm_natCast_cpow_of_pos hn,div_le_iff₀ (by linarith : 0<‖s-1‖)]
    simp only [Complex.sub_re, Complex.one_re,hs]
    exact (rpow_le_rpow_of_exponent_le hN (by linarith : 1-b≤1/2)).trans <| hpow.le.trans (by linarith)
  have hz : ‖s‖ ≤ 1+t := (norm_le_abs_re_add_abs_im s).trans (by rw [hs,him,abs_of_nonneg (by linarith : 0≤b),abs_of_nonneg (by linarith : 0≤t)]; linarith)
  have hquot : ‖s‖/b ≤ 2*(1+t) := (div_le_iff₀ (by linarith)).mpr (by nlinarith only [hz,mul_nonneg (show 0≤1+t by linarith) (show 0≤2*b-1 by linarith)])
  rw [hs,Real.rpow_neg hNr.le] at h
  have herr := (le_mul_inv_iff₀ (rpow_pos_of_pos hNr b)).mp <| show ‖riemannZeta s-(Z+P)‖ ≤ (1/2+‖s‖/b)*((N:ℝ)^b)⁻¹ by rwa [mul_comm] at h
  have hpow' := rpow_le_rpow_of_exponent_le hN hb
  rw [hpow] at hpow'
  have herr' : ‖riemannZeta s-(Z+P)‖ ≤ 7 := by
    by_contra! hn'
    nlinarith only [herr,hquot,hceil,hpow',ht,mul_lt_mul_of_pos_right hn' (rpow_pos_of_pos hNr b)]
  have H := norm_add_le (riemannZeta s-(Z+P)) (Z+P)
  rw [sub_add_cancel] at H
  have H' := norm_add_le Z P
  rw [← hid]
  linarith only [H,H',hp,herr']

/-- On the line `b = l-k`, the main term for *every* dyadic block is the
same power of the ordinate. The second term is bounded all the way up to
the quadratic Euler--Maclaurin cutoff. -/
theorem pair_growth {k l b e : ℝ} (pair : ExponentPair k l) (he : 0<e)
    (hb : 1/2≤b) (hb' : b<1) (hid : l-k=b) :
    ∃ C : ℝ, 0<C ∧ ∀ t : ℝ, ‖riemannZeta ((b:ℂ)+(t:ℂ)*I)‖ ≤ C*(1+|t|)^(k+2*e) := by
  obtain ⟨D,hD,hblock⟩ := long_bound pair he
  have hk : 0≤k := pair.inTriangle.1
  have hlog := Real.log_pos (by norm_num : (1:ℝ)<2)
  have hevent : ∀ᶠ t : ℝ in atTop, ‖riemannZeta ((b:ℂ)+(t:ℂ)*I)‖ ≤ (10+3*D)*t^(k+2*e) := by
    filter_upwards [eventually_ge_atTop (2:ℝ), logloss he (show 0<3+2/Real.log 2 by positivity)] with t ht hsmall
    let M := ⌈t⌉₊; let A := M^2
    have ht' : 0<t := by linarith
    have h1 : 1≤t := by linarith
    have hM := Nat.le_ceil t
    have hm : 1≤M := Nat.ceil_pos.mpr ht'
    have hA : 1≤A := Nat.one_le_pow _ _ hm
    have hM' : (M:ℝ) ≤ 2*t := (Nat.ceil_lt_add_one ht'.le).le.trans (by linarith)
    have hsum := classicalZetaPartialSum_eq_short_add_long 1 A ((b:ℂ)+(t:ℂ)*I) hA
    have hcut := truncation h1 hb hb'.le
    change _ ≤ 9+‖classicalZetaPartialSum A _‖ at hcut
    rw [hsum, mul_comm (t:ℂ) I, classicalZetaLongTail_eq_wideDirichletPoly _ _ _ _ le_rfl,
      wideDirichletPoly_eq_sum_blocks] at hcut
    simp only [classicalZetaPartialSum,Icc_self,sum_singleton,Nat.cast_one,one_cpow,mul_one] at hcut
    let J := Nat.clog 2 A
    have hterm (r : ℕ) (hr : r∈range J) : ‖dirichletPoly (2^r) (classicalZetaLongLineCoeff A b) t‖ ≤ 3*D*t^(k+e) := by
      let N := 2^r
      have hn : 0<N := pow_pos (by decide) _
      have hn' : N<A := by
        by_contra! h
        exact (Nat.not_le_of_gt (mem_range.mp hr)) ((Nat.clog_le_iff_le_pow Nat.one_lt_two).mpr h)
      have H := hblock (s:=b) hn hn' (by linarith) ht'
      have hn0 : 0<(N:ℝ) := by exact_mod_cast hn
      have hn1 : 1≤(N:ℝ) := by exact_mod_cast hn
      have hpow : (N:ℝ)^(1-b) ≤ 2*t := calc
        _ ≤ (N:ℝ)^(1/2:ℝ) := rpow_le_rpow_of_exponent_le hn1 (by linarith)
        _ ≤ (A:ℝ)^(1/2:ℝ) := by gcongr
        _ = M := by dsimp [A]; push_cast; rw [← sqrt_eq_rpow,sqrt_sq (by positivity)]
        _ ≤ _ := hM'
      rw [hid,mul_add,show (N:ℝ)^(-b)*(t^(k+e)*(N:ℝ)^b)=t^(k+e) by rw [rpow_neg hn0.le]; field_simp,
        show (N:ℝ)^(-b)*((N:ℝ)/t) = (N:ℝ)^(1-b)/t by rw [rpow_sub hn0,rpow_neg hn0.le,rpow_one]; ring] at H
      exact H.trans (by nlinarith only [mul_le_mul_of_nonneg_left ((div_le_iff₀ ht').mpr hpow) hD.le,
        mul_le_mul_of_nonneg_left (one_le_rpow h1 (show 0≤k+e by linarith)) hD.le])
    have hj : (J:ℝ)≤t^e := by
      unfold J
      rw [← natCeil_logb_natCast]
      refine (Nat.ceil_lt_add_one (logb_nonneg (by norm_num) (by exact_mod_cast hA))).le.trans (le_trans ?_ hsmall)
      have hl := log_le_log (show 0<(M:ℝ) by exact_mod_cast hm) hM'
      rw [Real.log_mul (by norm_num) ht'.ne'] at hl
      simp only [logb,A,Nat.cast_pow,log_pow,Nat.cast_ofNat]
      field_simp
      nlinarith only [hl,Real.log_nonneg h1,mul_nonneg (Real.log_nonneg h1) hlog.le]
    let f := fun r : ℕ => dirichletPoly (2^r) (classicalZetaLongLineCoeff A b) t
    have H : ‖∑ r ∈ range J, f r‖ ≤ t^e*(3*D*t^(k+e)) := calc
      _ ≤ ∑ r ∈ range J, ‖f r‖ := norm_sum_le _ _
      _ ≤ ∑ _ ∈ range J, 3*D*t^(k+e) := sum_le_sum hterm
      _ ≤ _ := by simp only [sum_const,card_range,nsmul_eq_mul]; gcongr
    have K := norm_add_le (1:ℂ) (∑ r ∈ range J,f r)
    rw [norm_one] at K
    rw [show t^e*(3*D*t^(k+e))=3*D*t^(k+2*e) by rw [show k+2*e=e+(k+e) by ring,rpow_add ht' e (k+e)]; ring] at H
    change _ ≤ 9+‖1+∑ r ∈ range J,f r‖ at hcut
    rw [mul_comm I (t:ℂ)] at hcut
    nlinarith only [K,H,hcut,one_le_rpow h1 (show 0≤k+2*e by linarith)]
  obtain ⟨B,hB⟩ := eventually_atTop.mp hevent
  let f := fun t : ℝ => ‖riemannZeta ((b:ℂ)+(t:ℂ)*I)‖
  have hc : Continuous f := by
    apply continuous_iff_continuousAt.mpr; intro t
    apply ContinuousAt.norm
    apply ContinuousAt.comp' (differentiableAt_riemannZeta ?_).continuousAt (by fun_prop)
    intro h; have := congrArg Complex.re h; simp at this; linarith
  obtain ⟨E,hE⟩ := (isCompact_Icc : IsCompact (Set.Icc 0 B)).bddAbove_image hc.continuousOn
  let C := max E (10+3*D)
  have hC : 0<C := lt_of_lt_of_le (by positivity) (le_max_right ..)
  refine ⟨C,hC,fun t => ?_⟩
  have heq : f t = f |t| := by
    rcases le_or_gt 0 t with h|h
    · rw [abs_of_nonneg h]
    rw [abs_of_neg h]; dsimp [f]
    rw [← Complex.norm_conj,← _root_.riemannZeta_conj]
    simp
  change f t ≤ _
  rw [heq]
  by_cases ht : |t|≤B
  · exact (hE ⟨|t|,⟨abs_nonneg _,ht⟩,rfl⟩).trans <| (le_max_left ..).trans <| le_mul_of_one_le_right hC.le (one_le_rpow (by linarith [abs_nonneg t]) (by linarith))
  exact (hB _ (le_of_not_ge ht)).trans (mul_le_mul (le_max_right ..) (rpow_le_rpow (abs_nonneg _) (by linarith) (by linarith)) (by positivity) hC.le)

end DensityStrip
