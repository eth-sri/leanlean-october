module
public import DensityStrip.Exponents
public import DensityStrip.Prefix
public import GuthMaynard.NativeSource.GuthMaynard.TerminalTypeI
public import LaterPairs.Native.ParabolaBilinearLocalization.Part03
public import LaterPairs.Native.ExponentPairAProcess

@[expose] public section
noncomputable section
open Real Complex Finset Filter Asymptotics TaoTrudgianYang2025 GuthMaynard.NativeMoment
namespace DensityStrip

theorem pair₀ : ExponentPair (13/84) (55/84) := exponentPair_bourgain
theorem pair₁ : ExponentPair (13/194) (152/194) := by
  convert pair₀.aProcess using 1 <;> norm_num

private theorem kernel_bound : ∃ C : ℝ, 0 < C ∧ ∀ {Q : ℕ} {u L : ℝ},
    0 < Q → (Q:ℝ) ≤ |u| → |u| ≤ L →
      ‖logarithmicKernel Q u‖ ≤ C * (L^(13/84+tiny)*(Q:ℝ)^(1/2:ℝ)) := by
  obtain ⟨C,hC,h⟩ := log_prefix_bound pair₀ (e:=tiny) (by norm_num [tiny])
  refine ⟨2*C,by positivity,?_⟩
  intro Q u L hQ hlo hhi
  have hQ1 : (1:ℝ) ≤ Q := by exact_mod_cast hQ
  have hp := h hQ (a:=Q+1) (b:=2*Q) (by omega) le_rfl (zero_lt_one.trans_le (hQ1.trans hlo))
  rw [← norm_logarithmicKernel_abs, logarithmicKernel, dyadicInterval, show Ioc Q (2*Q) = Icc (Q+1) (2*Q) by ext; simp]
  rw [show (55:ℝ)/84-13/84=1/2 by norm_num] at hp
  refine hp.trans ?_
  have h0 : 0 ≤ 13/84+tiny := by norm_num [tiny]
  have h1 : 1 ≤ L^(13/84+tiny)*(Q:ℝ)^(1/2:ℝ) :=
    one_le_mul_of_one_le_of_one_le (one_le_rpow (hQ1.trans (hlo.trans hhi)) h0) (one_le_rpow hQ1 (by norm_num))
  have hq := (div_le_one (zero_lt_one.trans_le (hQ1.trans hlo))).2 hlo
  have H := Real.rpow_le_rpow (abs_nonneg u) hhi h0
  rw [show 2*C*(L^(13/84+tiny)*(Q:ℝ)^(1/2:ℝ))=C*((L^(13/84+tiny)*(Q:ℝ)^(1/2:ℝ))+(L^(13/84+tiny)*(Q:ℝ)^(1/2:ℝ))) by ring]
  gcongr
  exact hq.trans h1

/-- Short powered blocks: subdivide at length `L = T^(1-p) Q^(2-2s)`.
The choice balances the diagonal term against the number of subintervals. -/
theorem short_count {s η : ℝ} (hl : 17/19 ≤ s) (hr : s ≤ 1) (he : 0 < η) (he' : η ≤ tiny) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : ℕ), T^length s ≤ Q → (Q:ℝ) ≤ T^(3*length s/2+η) →
      ∀ (b : ℕ → ℂ), (∀ n ∈ dyadicInterval Q, ‖b n‖ ≤ 1) → ∀ W : Finset ℝ,
      IsSeparated 1 W → InBaseInterval (3*T) W →
      (∀ t ∈ W, (Q:ℝ)^s*T^(-η) ≤ ‖dirichletPoly Q b t‖) →
      (W.card:ℝ) ≤ T^(exponent s+6*η) := by
  obtain ⟨C,hC,hk⟩ := kernel_bound
  obtain ⟨ha,ha',_⟩ := length_spec hl hr
  filter_upwards [eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop (by norm_num [tiny] : 0 < tiny)).eventually_ge_atTop (2*C),
    (tendsto_rpow_atTop he).eventually_ge_atTop 8,
    logloss he (show 0 < 1+12*π by positivity)] with T ht hCsmall h8 hlog
  intro Q hlo hhi b hb W hSep hBase hlarge
  have hT : 0 < T := zero_lt_one.trans ht
  have hQ : 0 < (Q:ℝ) := (Real.rpow_pos_of_pos hT _).trans_le hlo
  have hQn : 0 < Q := by exact_mod_cast hQ
  let x := logb T Q
  let z := localLength s x
  have hx : T^x = Q := rpow_logb hT ht.ne' hQ
  have hxlo := (rpow_le_rpow_left_iff ht).mp (hlo.trans_eq hx.symm)
  have hxhi := (rpow_le_rpow_left_iff ht).mp (hx.le.trans hhi)
  have hx1 : x ≤ 1 := by nlinarith only [ha', hxhi, he'.trans (show tiny ≤ 1/100 by norm_num [tiny])]
  obtain ⟨hz,hbudget⟩ := kernel_margin hl hr hxlo hx1
  have hL : 0 < T^z := rpow_pos_of_pos hT _
  let V := (Q:ℝ)^s*T^(-η)
  have hV : 0 < V := by dsimp [V]; positivity
  have hE := dyadic_energy_le_length Q b hb
  let D := C*((T^z)^(13/84+tiny)*(Q:ℝ)^(1/2:ℝ))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hAbs : 2*(Q:ℝ)*D ≤ V^2 := calc
    _ = (2*C)*((Q:ℝ)*((T^z)^(13/84+tiny)*(Q:ℝ)^(1/2:ℝ))) := by dsimp [D]; ring
    _ ≤ T^tiny*((Q:ℝ)*((T^z)^(13/84+tiny)*(Q:ℝ)^(1/2:ℝ))) := by gcongr
    _ ≤ _ := by
      dsimp only [V]
      exponents ht
      change tiny+(x+((13/84+tiny)*z+1/2*x)) ≤ 2*(s*x+-η)
      dsimp only [z]; norm_num [tiny] at hbudget he' ⊢; nlinarith only [hbudget, he']
  have H := count_of_kernel Q (3*T) V (T^z) W b hQn hV hL hD
    (fun u hu hu' => hk hQn hu hu') hSep hBase hlarge (le_trans (by gcongr) hAbs)
  have hQT : (Q:ℝ) ≤ T := hx.symm.le.trans <| (rpow_le_rpow_of_exponent_le ht.le hx1).trans_eq (rpow_one _)
  have hh : 1+12*π*(harmonic Q:ℝ) ≤ T^η := calc
    _ ≤ 1+12*π*(1+Real.log T) := by gcongr; exact (harmonic_le_one_add_log Q).trans (by gcongr)
    _ ≤ (1+12*π)*(1+Real.log T) := by linarith only [Real.log_nonneg ht.le]
    _ ≤ _ := hlog
  have hdiag : 2*(∑ n ∈ dyadicInterval Q, ‖b n‖^2)*((Q:ℝ)+12*π*Q*(harmonic Q:ℝ))/V^2 ≤
      2*T^η*((Q:ℝ)^2/V^2) := by
    have hnn : 0 ≤ (harmonic Q:ℝ) := by rw [harmonic_eq_sum_Icc]; push_cast; positivity
    calc
      _ ≤ 2*(Q:ℝ)*((Q:ℝ)+12*π*Q*(harmonic Q:ℝ))/V^2 := by gcongr
      _ = 2*(1+12*π*(harmonic Q:ℝ))*((Q:ℝ)^2/V^2) := by ring
      _ ≤ _ := by gcongr
  let M := (Q:ℝ)^2/V^2
  have hsmall : M ≤ T^(exponent s+3*η) := by
    dsimp only [M,V]; exponents ht
    change 2*x-2*(s*x+-η) ≤ exponent s+3*η
    unfold exponent
    have := mul_le_mul_of_nonneg_right hxhi (by linarith : 0 ≤ 2-2*s)
    nlinarith [mul_nonneg he.le (show 0 ≤ 2*s-1 by linarith)]
  have hbal : T/T^z*M ≤ T^(exponent s+3*η) := by
    dsimp only [M,V]; exponents ht
    change 1-z+(2*x-2*(s*x+-η)) ≤ exponent s+3*η
    dsimp only [z,localLength]; linarith
  have hf := Nat.floor_le (show 0 ≤ 3*T/T^z by positivity)
  have hcf : (((⌊3*T/T^z⌋₊+1:ℕ):ℝ)) ≤ 3*T/T^z+1 := by push_cast; linarith
  calc
    _ ≤ (((⌊3*T/T^z⌋₊+1:ℕ):ℝ))*(2*T^η*M) := H.trans (by gcongr)
    _ ≤ (3*T/T^z+1)*(2*T^η*M) := by gcongr
    _ = 2*T^η*(3*(T/T^z*M)+M) := by ring
    _ ≤ 2*T^η*(3*T^(exponent s+3*η)+T^(exponent s+3*η)) := by gcongr
    _ = 8*T^η*T^(exponent s+3*η) := by ring
    _ ≤ T^η*T^η*T^(exponent s+3*η) := by gcongr
    _ ≤ _ := by exponents ht; linarith

end DensityStrip
