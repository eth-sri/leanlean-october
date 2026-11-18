module

public import Mathlib
public import PottsDiscontinuity.Bethe.FourierSawtooth
public import PottsDiscontinuity.Bethe.Prop21Rho

/-!
# Proposition 2.1 for `τ`: the explicit solution of (cOE_Δ) and its uniqueness
-/

@[expose] public section

open Complex Real MeasureTheory Filter Topology Set intervalIntegral

namespace PottsDiscontinuity.Bethe

noncomputable def tauPartial (lam α : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, (-1) ^ (n + 1) / (π * ((n : ℝ) + 1)) * Real.tanh (lam * ((n + 1 : ℕ) : ℝ)) *
    Real.sin (((n + 1 : ℕ) : ℝ) * α)

noncomputable def tauSeries (lam α : ℝ) : ℝ := limUnder atTop (tauPartial lam α)

noncomputable def tau (Δ x : ℝ) : ℝ := tauSeries (lamOf Δ) (kInv (lamOf Δ) x)

noncomputable def tauCoeff (lam : ℝ) (n : ℕ) : ℝ :=
  2 * (-1) ^ n * (1 - Real.tanh (lam * ((n + 1 : ℕ) : ℝ))) / ((n : ℝ) + 1)

noncomputable def tauU (lam α : ℝ) : ℝ := trigSeries 0 (fun _ => 0) (tauCoeff lam) α

noncomputable def TcontFn (lam α : ℝ) : ℝ := -α + tauU lam α

noncomputable def tauCont (Δ x : ℝ) : ℝ := TcontFn (lamOf Δ) (kInv (lamOf Δ) x) / (2 * π)

private theorem one_sub_tanh_eq_mul_secCoeff (lam : ℝ) (n : ℕ) :
    1 - Real.tanh (lam * ((n + 1 : ℕ) : ℝ)) = Real.exp (-lam) ^ (n + 1) * secCoeff lam n := by
  rw [Real.tanh_eq_sinh_div_cosh]
  have hc : Real.cosh (lam * ((n + 1 : ℕ) : ℝ)) ≠ 0 := (Real.cosh_pos _).ne'
  have h1 : 1 - Real.sinh (lam * ((n + 1 : ℕ) : ℝ)) / Real.cosh (lam * ((n + 1 : ℕ) : ℝ)) =
      Real.exp (-(lam * ((n + 1 : ℕ) : ℝ))) / Real.cosh (lam * ((n + 1 : ℕ) : ℝ)) := by
    field_simp; rw [Real.cosh_sub_sinh]
  rw [h1]; unfold secCoeff
  rw [← Real.exp_nat_mul, show (n + 1 : ℕ) * -lam = -(lam * ((n + 1 : ℕ) : ℝ)) by push_cast; ring]; ring

theorem abs_tauCoeff_le (lam : ℝ) (n : ℕ) : |tauCoeff lam n| ≤ 2 * Real.exp (-lam) ^ (n + 1) := by
  have h1 := one_sub_tanh_eq_mul_secCoeff lam n
  have hsec1 : secCoeff lam n ≤ 1 := (div_le_one (Real.cosh_pos _)).2 (Real.one_le_cosh _)
  have h4 : 0 ≤ 1 - Real.tanh (lam * ((n + 1 : ℕ) : ℝ)) := by rw [h1]; exact mul_nonneg (by positivity) (secCoeff_pos lam n).le
  have h5 : 1 - Real.tanh (lam * ((n + 1 : ℕ) : ℝ)) ≤ Real.exp (-lam) ^ (n + 1) := by
    rw [h1]; exact mul_le_of_le_one_right (by positivity) hsec1
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  unfold tauCoeff
  rw [abs_div, abs_of_pos hn, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_pos two_pos, abs_of_nonneg h4, div_le_iff₀ hn]
  nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem summable_tauCoeff {lam : ℝ} (hlam : 0 < lam) : Summable (tauCoeff lam) := by
  have hr : 0 < Real.exp (-lam) := Real.exp_pos _
  have hr1 : Real.exp (-lam) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hs : Summable (fun n : ℕ => 2 * Real.exp (-lam) ^ (n + 1)) :=
    ((summable_geometric_of_lt_one hr.le hr1).mul_left (2 * Real.exp (-lam))).congr fun _ => by ring
  exact Summable.of_norm_bounded hs fun n => by rw [Real.norm_eq_abs]; exact abs_tauCoeff_le lam n

theorem continuous_TcontFn {lam : ℝ} (hlam : 0 < lam) : Continuous (TcontFn lam) :=
  continuous_neg.add (continuous_trigSeries summable_zero (summable_tauCoeff hlam) 0)

theorem continuous_tauCont {Δ : ℝ} (hΔ : Δ < -1) : Continuous (tauCont Δ) :=
  ((continuous_TcontFn (lamOf_pos hΔ)).comp (continuous_kInv (lamOf_pos hΔ))).div_const _

private theorem TcontFn_add_xiConv {Δ : ℝ} (hΔ : Δ < -1) (α : ℝ) :
    TcontFn (lamOf Δ) α + xiConv (2 * lamOf Δ) (TcontFn (lamOf Δ)) α = PsiFn Δ α := by
  have hlam := lamOf_pos hΔ; have hlam2 : 0 < 2 * lamOf Δ := by linarith
  have hu := summable_tauCoeff hlam
  have hr : 0 < Real.exp (-(2 * lamOf Δ)) := Real.exp_pos _
  have hr1 : Real.exp (-(2 * lamOf Δ)) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hX := xiConv_trigSeries hlam2 summable_zero hu 0 α
  have hz2 : Summable (fun n : ℕ => Real.exp (-(2 * lamOf Δ)) ^ (n + 1) * 0) := by simp
  have hsum : HasSum (fun n : ℕ => -2 * (2 * (-1) ^ (n + 1) * Real.exp (-(2 * lamOf Δ)) ^ (n + 1) /
      ((n : ℝ) + 1) * Real.sin (((n + 1 : ℕ) : ℝ) * α))) _ :=
    ((hasSum_trigTerm summable_zero hu α).add
      (hasSum_trigTerm hz2 (summable_pow_succ_mul hu hr.le hr1.le) α)).congr_fun fun n => by
        symm; unfold trigTerm tauCoeff; dsimp only
        rw [one_sub_tanh_eq_mul_secCoeff]
        have h2 := one_add_exp_two_mul_div_cosh (lam := lamOf Δ) n
        have h3 : Real.exp (-(2 * lamOf Δ)) ^ (n + 1) = Real.exp (-lamOf Δ) ^ (n + 1) * Real.exp (-lamOf Δ) ^ (n + 1) := by
          rw [← mul_pow, ← Real.exp_add, show -(2 * lamOf Δ) = -lamOf Δ + -lamOf Δ by ring]
        have hn : (n : ℝ) + 1 ≠ 0 := by positivity
        calc _ = 2 * (-1) ^ n * Real.exp (-lamOf Δ) ^ (n + 1) * ((1 + Real.exp (-(2 * lamOf Δ)) ^ (n + 1)) * secCoeff (lamOf Δ) n) /
                ((n : ℝ) + 1) * Real.sin (((n + 1 : ℕ) : ℝ) * α) := by ring
          _ = -2 * (2 * (-1) ^ (n + 1) * Real.exp (-(2 * lamOf Δ)) ^ (n + 1) / ((n : ℝ) + 1) * Real.sin (((n + 1 : ℕ) : ℝ) * α)) := by
                rw [h2, h3, pow_succ (-1 : ℝ) n]; field_simp
  have hU_eq : tauU (lamOf Δ) α + xiConv (2 * lamOf Δ) (tauU (lamOf Δ)) α = -2 * sawS (2 * lamOf Δ) α := by
    have hu_uniq := hsum.unique ((hasSum_xiConv_neg_id hlam2 α).mul_left (-2))
    rw [xiConv_neg_id hlam2] at hu_uniq
    unfold tauU; rw [hX]; unfold trigSeries; unfold trigTerm at hu_uniq; dsimp only at hu_uniq ⊢; linarith
  have hcontU : IntervalIntegrable (tauU (lamOf Δ)) volume (-π) π :=
    (continuous_trigSeries summable_zero hu 0).intervalIntegrable _ _
  change (-α + tauU (lamOf Δ) α) + xiConv (2 * lamOf Δ) (fun β => -β + tauU (lamOf Δ) β) α = _
  rw [xiConv_add hlam2 (continuous_neg.intervalIntegrable _ _) hcontU, xiConv_neg_id hlam2, PsiFn_eq_neg_sub_sawS hΔ]
  linarith

theorem tauCont_isCOESolution {Δ : ℝ} (hΔ : Δ < -1) : IsCOESolution Δ (tauCont Δ) := by
  have hTr : Ttrans Δ (tauCont Δ) = TcontFn (lamOf Δ) := by
    funext α; unfold Ttrans tauCont; rw [kInv_kMap (lamOf_pos hΔ)]; have := Real.pi_pos; field_simp
  rw [isCOESolution_iff hΔ, hTr]
  exact fun α _ => TcontFn_add_xiConv hΔ α

theorem eq_tauCont_of_isCOESolution_of_integrableOn {Δ : ℝ} (hΔ : Δ < -1) {τ' : ℝ → ℝ}
    (hτ' : IntegrableOn τ' (Icc (-π) π) volume) (h : IsCOESolution Δ τ') :
    ∀ x ∈ Icc (-π) π, τ' x = tauCont Δ x := by
  have hlam := lamOf_pos hΔ; have hlam2 : 0 < 2 * lamOf Δ := by linarith
  have hpi : 2 * π ≠ 0 := by positivity
  have hTr : Ttrans Δ (tauCont Δ) = TcontFn (lamOf Δ) := by
    funext α; unfold Ttrans tauCont; rw [kInv_kMap hlam]; field_simp [Real.pi_pos.ne']
  have hT'eq := (isCOESolution_iff hΔ τ').1 h
  have hTeq := hTr ▸ (isCOESolution_iff hΔ (tauCont Δ)).1 (tauCont_isCOESolution hΔ)
  have hT'ii : IntervalIntegrable (Ttrans Δ τ') volume (-π) π :=
    intervalIntegrable_of_integrableOn_Icc ((integrableOn_comp_kMap_of_Xi hlam hτ').const_mul (2 * π))
  have hTii : IntervalIntegrable (TcontFn (lamOf Δ)) volume (-π) π :=
    (continuous_TcontFn hlam).intervalIntegrable _ _
  have hD0 := eq_zero_of_eq_neg_xiConv (D := fun β => Ttrans Δ τ' β - TcontFn (lamOf Δ) β) hlam2 (hT'ii.sub hTii) fun α hα => by
    rw [xiConv_sub hlam2 hT'ii hTii]
    have := hT'eq α (Ioc_subset_Icc_self hα); have := hTeq α (Ioc_subset_Icc_self hα)
    linarith
  have hae : ∀ᵐ β ∂(volume.restrict (Icc (-π) π)), τ' (kMap (lamOf Δ) β) = tauCont Δ (kMap (lamOf Δ) β) := by
    rw [Measure.restrict_congr_set Ioc_ae_eq_Icc.symm]
    filter_upwards [hD0] with β hβ
    change Ttrans Δ τ' β - TcontFn (lamOf Δ) β = 0 at hβ
    exact mul_left_cancel₀ hpi (by change Ttrans Δ τ' β = Ttrans Δ (tauCont Δ) β; rw [hTr]; linarith)
  have hae2 := ae_eq_of_comp_kMap hlam hτ' (integrableOn_Icc_of_continuous (continuous_tauCont hΔ)) hae
  intro x hx
  have h5 : cOEop Δ τ' x = cOEop Δ (tauCont Δ) x := by
    unfold cOEop; congr 1
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    refine integral_congr_ae ?_
    rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
    exact hae2.mono fun y hy => by dsimp only; rw [hy]
  exact mul_left_cancel₀ hpi (by rw [h x hx, tauCont_isCOESolution hΔ x hx, h5])

theorem tendsto_tauPartial {lam : ℝ} (hlam : 0 < lam) {α : ℝ} (hα : |α| < π) :
    Tendsto (tauPartial lam α) atTop (𝓝 (TcontFn lam α / (2 * π))) := by
  have hU := (hasSum_trigTerm summable_zero (summable_tauCoeff hlam) α).tendsto_sum_nat
  have h2 := ((tendsto_sawtooth hα).add (hU.const_mul (1 / 2))).const_mul (1 / π)
  have hpi := Real.pi_pos
  have hval : 1 / π * (-α / 2 + 1 / 2 * ∑' n, trigTerm (fun _ => (0 : ℝ)) (tauCoeff lam) n α) =
      TcontFn lam α / (2 * π) := by unfold TcontFn tauU trigSeries trigTerm; simp only [zero_add]; field_simp
  rw [hval] at h2
  refine h2.congr fun N => ?_
  unfold tauPartial tauCoeff trigTerm
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hn : (i : ℝ) + 1 ≠ 0 := by positivity
  field_simp; rw [pow_succ (-1 : ℝ) i]; ring

theorem tauSeries_eq {lam : ℝ} (hlam : 0 < lam) {α : ℝ} (hα : |α| < π) :
    tauSeries lam α = TcontFn lam α / (2 * π) :=
  (tendsto_tauPartial hlam hα).limUnder_eq

theorem tauSeries_pi (lam : ℝ) : tauSeries lam π = 0 := by
  have h (N : ℕ) : tauPartial lam π N = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [Real.sin_nat_mul_pi]; simp [mul_comm]
  unfold tauSeries; rw [funext h]; exact tendsto_const_nhds.limUnder_eq

theorem tauSeries_neg_pi (lam : ℝ) : tauSeries lam (-π) = 0 := by
  have h (N : ℕ) : tauPartial lam (-π) N = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [mul_neg, Real.sin_neg, Real.sin_nat_mul_pi]; simp
  unfold tauSeries; rw [funext h]; exact tendsto_const_nhds.limUnder_eq

theorem tau_eq_tauCont {Δ : ℝ} (hΔ : Δ < -1) {x : ℝ} (hx : x ∈ Ioo (-π) π) :
    tau Δ x = tauCont Δ x := by
  have hlam := lamOf_pos hΔ
  have hm := kInv_mem_Icc hlam (Ioo_subset_Icc_self hx)
  have hk := kMap_kInv hlam x
  exact tauSeries_eq hlam (abs_lt.2
    ⟨lt_of_le_of_ne hm.1 fun h => hx.1.ne (by rw [← hk, ← h, kMap_neg_pi]),
     lt_of_le_of_ne hm.2 fun h => hx.2.ne (by rw [← hk, h, kMap_pi])⟩)

end PottsDiscontinuity.Bethe
