module

public import Erdos408.Analytic.PNT
public import Erdos408.Analytic.PrimeTwist
public import OAI.NumberTheory.PrimeGaps.Indices
public import Erdos821.Blueprint.Classical

@[expose] public section

open Filter MeasureTheory

namespace Erdos821.DivisorHarmonic

open OAI.LargePrimeGaps

/-- The character sum weighted by the Chebyshev theta coefficients. -/
noncomputable def thetaCharacterPrefix {q : ℕ}
    (y : ℝ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, χ n * (theta n)

open Erdos408.PrimeTwist

/-- At zero frequency the prime component of the twisted Perron kernel is
exactly the theta-character sum. -/
private lemma theta_at_zero {q : ℕ} (y : ℝ) (χ : DirichletCharacter ℂ q) :
    thetaCharacterPrefix y χ = ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, primeCoeff χ 0 n := by
  rw [thetaCharacterPrefix, ← Finset.Icc_add_one_left_eq_Ioc]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  by_cases hp : n.Prime <;> simp [primeCoeff, theta, hp]

/-- Absorb any fixed logarithmic loss against a power saving. -/
private lemma absorb_log (u v A : ℝ) (hv : 0 < v) : ∀ᶠ y : ℝ in atTop,
    Real.log y ^ u * y ^ (1 - v) ≤ y * Real.log y ^ (-A) := by
  filter_upwards [(isLittleO_log_rpow_rpow_atTop (u + A) hv).bound one_pos,
    eventually_gt_atTop 1] with y h hy
  have hy0 := zero_lt_one.trans hy
  have hL := Real.log_pos hy
  simp [abs_of_pos (Real.rpow_pos_of_pos hL _), abs_of_pos (Real.rpow_pos_of_pos hy0 _)] at h
  rw [Real.rpow_neg hL.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hL _),
    mul_right_comm, ← Real.rpow_add hL]
  calc _ ≤ y ^ v * y ^ (1-v) := by gcongr
       _ = y := by rw [← Real.rpow_add hy0]; ring_nf; simp

/-- Uniform power saving for the theta-character prefix of nonprincipal
characters. The power-saving PNT already proved for all levels absorbs both
the polylogarithmic conductor and the higher prime powers. -/
theorem thetaCharacterPrefix_log_bound (A B : ℝ) :
    ∃ K > 0, ∀ᶠ y : ℝ in atTop,
      ∀ q, ∀ χ : DirichletCharacter ℂ q,
        0 < q → (q : ℝ) ≤ (Real.log y) ^ B → χ ≠ 1 →
        ‖thetaCharacterPrefix y χ‖ ≤ K * y * (Real.log y) ^ (-A) := by
  obtain ⟨c, hc, C, h⟩ := Erdos408.sum_vonMangoldt_mul_char_sub_le
  refine ⟨|C| + 2, by positivity, ?_⟩
  filter_upwards [absorb_log (B * |C|) c A hc, absorb_log 1 (1/2) A (by norm_num),
    eventually_ge_atTop 2] with y hm hp hy
  intro q χ hq hk hχ
  let : NeZero q := ⟨hq.ne'⟩
  have hs := h q χ y hy
  simp [ite_eq_right hχ] at hs
  have hy1 : 1 ≤ y := by linarith
  have hf : 1 ≤ ⌊y⌋₊ := by simp_all
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (Nat.succ_le_of_lt hq)
  have hpow : (q : ℝ)^C ≤ Real.log y ^ (B * |C|) := calc
    _ ≤ (q : ℝ)^|C| := Real.rpow_le_rpow_of_exponent_le hq1 (le_abs_self _)
    _ ≤ (Real.log y ^ B)^|C| := by gcongr
    _ = _ := (Real.rpow_mul (Real.log_nonneg hy1) ..).symm
  let S := ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, twistCoeff χ 0 n
  have hS : ‖S‖ ≤ |C| * (y * Real.log y ^ (-A)) := calc
    _ ≤ C * (q : ℝ)^C * y^(1-c) := by simpa [S, twistCoeff, mul_comm] using hs
    _ ≤ |C| * Real.log y ^ (B * |C|) * y^(1-c) := by gcongr; exact le_abs_self _
    _ ≤ _ := by rw [mul_assoc]; gcongr
  have hx := norm_sum_twistCoeff_sub_primeCoeff_le χ 0 hf
  have hsl := Real.sqrt_le_sqrt (Nat.floor_le (by linarith : 0 ≤ y))
  have hll := Real.log_le_log (Nat.cast_pos.mpr hf) (Nat.floor_le (by linarith : 0 ≤ y))
  rw [show 1 - (1/2 : ℝ) = 1/2 by norm_num, ← Real.sqrt_eq_rpow, Real.rpow_one] at hp
  rw [theta_at_zero]
  calc _ ≤ ‖S‖ + ‖S - ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, primeCoeff χ 0 n‖ := by
            exact le_trans (le_of_eq (congrArg norm (sub_sub_cancel S _).symm)) (norm_sub_le _ _)
       _ ≤ |C| * (y * Real.log y ^ (-A)) + 2 * √⌊y⌋₊ * Real.log ⌊y⌋₊ := by gcongr
       _ ≤ |C| * (y * Real.log y ^ (-A)) + 2 * √y * Real.log y := by gcongr
       _ ≤ _ := by linarith

/-- The Mellin weight dual to the theta coefficients. -/
noncomputable def thetaMellinWeight (t y : ℝ) : ℂ :=
  Erdos821.Blueprint.Analytic.mellin y t * (y : ℂ)⁻¹ * (Real.log y : ℂ)⁻¹

/-- The derivative of the Mellin-over-prime weight has the usual `(|t|+2)/(y² log y)` bound. -/
theorem thetaMellinWeight_deriv_norm_le (t y : ℝ) (hy : 0 < y)
    (hlog : 1 ≤ Real.log y) :
    ‖deriv (thetaMellinWeight t) y‖ ≤ (|t| + 2) / (y ^ 2 * Real.log y) := by
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hlogpos : 0 < Real.log y := by positivity
  have hlogC : (Real.log y : ℂ) ≠ 0 := by exact_mod_cast hlogpos.ne'
  have hm : HasDerivAt (fun z : ℝ => Erdos821.Blueprint.Analytic.mellin z t)
      ((Complex.I * (t : ℂ) * (y : ℂ)⁻¹) *
        Erdos821.Blueprint.Analytic.mellin y t) y := by
    have hlog' := HasDerivAt.ofReal_comp (Real.hasDerivAt_log hy.ne')
    convert (hlog'.const_mul (Complex.I * (t : ℂ))).cexp using 1 <;>
      simp [Erdos821.Blueprint.Analytic.mellin]; ring
  have hid : HasDerivAt (fun z : ℝ => (z : ℂ)) 1 y :=
    HasDerivAt.ofReal_comp (hasDerivAt_id y)
  have hyInv := hid.inv hyC
  have hlogInv :=
    (HasDerivAt.ofReal_comp (Real.hasDerivAt_log hy.ne')).inv hlogC
  have hweight := (hm.mul hyInv).mul hlogInv
  change ‖deriv ((fun z : ℝ => Erdos821.Blueprint.Analytic.mellin z t) *
    (fun z : ℝ => (z : ℂ))⁻¹ *
    (fun z : ℝ => (Real.log z : ℂ))⁻¹) y‖ ≤ _
  rw [hweight.deriv]
  change ‖((Complex.I * (t : ℂ) * (y : ℂ)⁻¹ *
      Erdos821.Blueprint.Analytic.mellin y t * (y : ℂ)⁻¹ +
      Erdos821.Blueprint.Analytic.mellin y t * (-1 / (y : ℂ) ^ 2)) *
      (Real.log y : ℂ)⁻¹ +
      Erdos821.Blueprint.Analytic.mellin y t * (y : ℂ)⁻¹ *
        (-((y⁻¹ : ℝ) : ℂ) / (Real.log y : ℂ) ^ 2))‖ ≤ _
  have hmnorm : ‖Erdos821.Blueprint.Analytic.mellin y t‖ = 1 := by
    simp [Erdos821.Blueprint.Analytic.mellin, Complex.norm_exp]
  have hInorm : ‖Complex.I‖ = 1 := by simp
  have hynorm : ‖(y : ℂ)‖ = y := by simp [abs_of_pos hy]
  have hlognorm : ‖(Real.log y : ℂ)‖ = Real.log y := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlogpos]
  have hterm₁ :
      ‖Complex.I * (t : ℂ) * (y : ℂ)⁻¹ *
        Erdos821.Blueprint.Analytic.mellin y t * (y : ℂ)⁻¹‖ = |t| / y ^ 2 := by
    simp [hmnorm, hynorm, Complex.norm_real]
    ring
  have hterm₂ :
      ‖Erdos821.Blueprint.Analytic.mellin y t * (-1 / (y : ℂ) ^ 2)‖ = 1 / y ^ 2 := by
    simp [hmnorm]
  have hterm₃ :
      ‖Erdos821.Blueprint.Analytic.mellin y t * (y : ℂ)⁻¹ *
        (-((y⁻¹ : ℝ) : ℂ) / (Real.log y : ℂ) ^ 2)‖ =
        1 / (y ^ 2 * (Real.log y) ^ 2) := by
    simp [hmnorm, abs_of_pos hy, abs_of_pos hlogpos]
    ring
  calc
    _ ≤ ‖Complex.I * (t : ℂ) * (y : ℂ)⁻¹ *
          Erdos821.Blueprint.Analytic.mellin y t * (y : ℂ)⁻¹ +
          Erdos821.Blueprint.Analytic.mellin y t * (-1 / (y : ℂ) ^ 2)‖ *
        ‖((Real.log y : ℂ)⁻¹)‖ +
        ‖Erdos821.Blueprint.Analytic.mellin y t * (y : ℂ)⁻¹ *
          (-((y⁻¹ : ℝ) : ℂ) / (Real.log y : ℂ) ^ 2)‖ := by
      calc
        _ ≤ ‖(Complex.I * (t : ℂ) * (y : ℂ)⁻¹ *
              Erdos821.Blueprint.Analytic.mellin y t * (y : ℂ)⁻¹ +
              Erdos821.Blueprint.Analytic.mellin y t * (-1 / (y : ℂ) ^ 2)) *
              (Real.log y : ℂ)⁻¹‖ +
            ‖Erdos821.Blueprint.Analytic.mellin y t * (y : ℂ)⁻¹ *
              (-((y⁻¹ : ℝ) : ℂ) / (Real.log y : ℂ) ^ 2)‖ := norm_add_le _ _
        _ = _ := by simp
    _ ≤ (|t| / y ^ 2 + 1 / y ^ 2) * (1 / Real.log y) +
          1 / (y ^ 2 * (Real.log y) ^ 2) := by
      have hab := norm_add_le
        (Complex.I * (t : ℂ) * (y : ℂ)⁻¹ *
          Erdos821.Blueprint.Analytic.mellin y t * (y : ℂ)⁻¹)
        (Erdos821.Blueprint.Analytic.mellin y t * (-1 / (y : ℂ) ^ 2))
      calc
        _ ≤ (‖Complex.I * (t : ℂ) * (y : ℂ)⁻¹ *
              Erdos821.Blueprint.Analytic.mellin y t * (y : ℂ)⁻¹‖ +
              ‖Erdos821.Blueprint.Analytic.mellin y t * (-1 / (y : ℂ) ^ 2)‖) *
              ‖(Real.log y : ℂ)⁻¹‖ +
            ‖Erdos821.Blueprint.Analytic.mellin y t * (y : ℂ)⁻¹ *
              (-((y⁻¹ : ℝ) : ℂ) / (Real.log y : ℂ) ^ 2)‖ := by gcongr
        _ = _ := by
          rw [hterm₁, hterm₂, hterm₃, norm_inv, hlognorm]
          simp
    _ ≤ _ := by
      have hinv : 1 / Real.log y ≤ 1 := by
        apply (div_le_iff₀ hlogpos).2
        linarith
      have hden : 0 < y ^ 2 * Real.log y := by positivity
      have hEq : (|t| / y ^ 2 + 1 / y ^ 2) * (1 / Real.log y) +
          1 / (y ^ 2 * (Real.log y) ^ 2) =
          (|t| + 1 + 1 / Real.log y) / (y ^ 2 * Real.log y) := by
        field_simp
      rw [hEq]
      apply (div_le_div_iff₀ hden hden).2
      nlinarith [abs_nonneg t]

/-- Abel summation over an interval of primes. A linear bound `K*y` on the
cumulative theta sum pays one endpoint term at each end and an integral of
`K (|t|+2) / y` along the interval. -/
private theorem abel_bound {q : ℕ} (χ : DirichletCharacter ℂ q) (t K : ℝ) {n m : ℕ}
    (hn : Real.exp 1 ≤ n) (hnm : n ≤ m) (hK : 0 ≤ K)
    (hθ : ∀ y, (n : ℝ) ≤ y → ‖thetaCharacterPrefix y χ‖ ≤ K * y) :
    ‖∑ p ∈ (Finset.Ioc n m).filter Nat.Prime,
      χ p * Blueprint.Analytic.mellin p t / (p : ℂ)‖ ≤
        K * (2 + (|t| + 2) * Real.log ((m : ℝ) / n)) := by
  let w := thetaMellinWeight t
  let c := fun k : ℕ ↦ χ k * (theta k : ℂ)
  have hn₁ : 1 < (n : ℝ) := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr one_pos) hn
  have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have hlog {y : ℝ} (hy : n ≤ y) : 1 ≤ Real.log y :=
    (Real.le_log_iff_exp_le (zero_lt_one.trans (hn₁.trans_le hy))).mpr (hn.trans hy)
  have hsmooth : ContDiffOn ℝ 2 w (Set.Ioi 1) := by
    let s := Set.Ioi (1:ℝ)
    have hl : ContDiffOn ℝ 2 Real.log s := Real.contDiffOn_log.mono fun x hx ↦ (zero_lt_one.trans hx).ne'
    have hg : ContDiffOn ℝ 2 (fun y : ℝ ↦ (Real.log y : ℂ)) s := hl.continuousLinearMap_comp Complex.ofRealCLM
    have hy : ContDiffOn ℝ 2 (fun y : ℝ ↦ (y : ℂ)) s := Complex.ofRealCLM.contDiff.contDiffOn
    exact ((Complex.contDiff_exp.comp_contDiffOn (contDiffOn_const.mul hg : ContDiffOn ℝ 2 (fun y : ℝ ↦ Complex.I * (t : ℂ) * (Real.log y : ℂ)) s)).mul
      (hy.inv (fun y h ↦ Complex.ofReal_ne_zero.mpr (zero_lt_one.trans h).ne'))).mul
      (hg.inv (fun y h ↦ Complex.ofReal_ne_zero.mpr (Real.log_pos h).ne'))
  have hsub : Set.Icc (n : ℝ) m ⊆ Set.Ioi 1 := fun y hy ↦ hn₁.trans_le hy.1
  have hdiff y (hy : y ∈ Set.Icc (n : ℝ) m) :=
    (hsmooth.differentiableOn (by norm_num) y (hsub hy)).differentiableAt (isOpen_Ioi.mem_nhds (hsub hy))
  have hint := ((hsmooth.deriv_of_isOpen (m := 0) isOpen_Ioi (by norm_num)).continuousOn.mono hsub).integrableOn_Icc (μ := volume)
  have hprefix (y : ℝ) : ∑ k ∈ Finset.Icc 0 ⌊y⌋₊, c k = thetaCharacterPrefix y χ := by
    rw [← Finset.sum_Ioc_add_eq_sum_Icc (Nat.zero_le _)]
    simp [c, thetaCharacterPrefix, theta]
  have hweight {y : ℝ} (hy : n ≤ y) : ‖w y * thetaCharacterPrefix y χ‖ ≤ K := by
    have hly := hlog hy
    have hy0 : 0 < y := zero_lt_one.trans (hn₁.trans_le hy)
    have hnw : ‖w y‖ ≤ y⁻¹ := by
      simp [w, thetaMellinWeight, Blueprint.Analytic.mellin, Complex.norm_exp,
        abs_of_pos hy0, abs_of_pos (Real.log_pos (hn₁.trans_le hy))]
      exact mul_le_of_le_one_right (by positivity) (inv_le_one_of_one_le₀ hly)
    calc _ ≤ y⁻¹ * (K * y) := (norm_mul ..).le.trans
              (mul_le_mul hnw (hθ y hy) (norm_nonneg _) (by positivity))
         _ = K := by field_simp
  have hcomp : ContinuousOn (fun y : ℝ ↦ K * (|t|+2) * y⁻¹) (Set.Icc n m) :=
    continuousOn_const.mul (continuousOn_id.inv₀ fun y hy ↦ ne_of_gt (zero_lt_one.trans (hsub hy)))
  have hInt : ‖∫ y in Set.Ioc (n : ℝ) m, deriv w y * thetaCharacterPrefix y χ‖ ≤
      K * (|t|+2) * Real.log ((m : ℝ) / n) := calc
    _ ≤ ∫ y in Set.Ioc (n : ℝ) m, K * (|t|+2) * y⁻¹ := by
      apply norm_integral_le_of_norm_le (hcomp.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
      refine ae_restrict_of_forall_mem measurableSet_Ioc fun y hy ↦ ?_
      have hy0 : 0 < y := zero_lt_one.trans (hn₁.trans hy.1)
      have hly := hlog hy.1.le
      rw [norm_mul]
      calc _ ≤ ((|t|+2)/(y^2 * Real.log y)) * (K*y) :=
                  mul_le_mul (thetaMellinWeight_deriv_norm_le t y hy0 hly) (hθ y hy.1.le) (norm_nonneg _) (by positivity)
           _ ≤ ((|t|+2)/y^2) * (K*y) := by gcongr; nlinarith
           _ = _ := by field_simp
    _ = _ := by rw [← intervalIntegral.integral_of_le hnm', intervalIntegral.integral_const_mul,
                       integral_inv_of_pos (zero_lt_one.trans hn₁) (zero_lt_one.trans (hn₁.trans_le hnm'))]
  have hsum := sum_mul_eq_sub_sub_integral_mul c n.cast_nonneg hnm' hdiff hint
  simp_rw [hprefix] at hsum
  simp at hsum
  have hterms : (∑ p ∈ (Finset.Ioc n m).filter Nat.Prime, χ p * Blueprint.Analytic.mellin p t / (p : ℂ)) =
      ∑ k ∈ Finset.Ioc n m, w k * c k := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    by_cases hp : k.Prime
    · have hlogne : (Real.log k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
      have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
      simp only [w, c, theta, hp, thetaMellinWeight, ite_true]
      push_cast
      rw [Complex.ofReal_log (by positivity)] at hlogne
      push_cast at hlogne
      field_simp [hlogne, hk0]
    · simp [c, theta, hp]
  rw [hterms, hsum]
  have := norm_sub_le (w m * thetaCharacterPrefix m χ) (w n * thetaCharacterPrefix n χ)
  have := norm_sub_le (w m * thetaCharacterPrefix m χ - w n * thetaCharacterPrefix n χ)
    (∫ y in Set.Ioc (n : ℝ) m, deriv w y * thetaCharacterPrefix y χ)
  linarith [hweight le_rfl, hweight hnm']

end Erdos821.DivisorHarmonic

namespace Erdos821.Blueprint

open Analytic
open OAI.LargePrimeGaps

set_option maxHeartbeats 1000000 in
/-- The harmonic character estimate follows from the theta-character prefix bound by Abel
summation with the Mellin-over-prime weight. -/
theorem HarmonicCharacters_proof : HarmonicCharacters := by
  intro c C B A hc hC hB hA
  let E : ℝ := A + B + 2
  let D := 2 * E / c
  let β := 2 * B / c
  have hE : 0 < E := by positivity
  have hD : 0 < D := by positivity
  obtain ⟨M, hM, hThetaEventually⟩ :=
    Erdos821.DivisorHarmonic.thetaCharacterPrefix_log_bound D β
  obtain ⟨Yθ, hThetaFrom⟩ := Filter.eventually_atTop.1 hThetaEventually
  let Ybig := max 1 Yθ
  have hLogLim := Real.tendsto_log_atTop
  have hULim :=
    (tendsto_rpow_atTop (by linarith : 0 < c / 2)).comp hLogLim
  have hXEvents : ∀ᶠ x : ℝ in atTop,
      2 ≤ x ∧ 1 ≤ Real.log x ∧ 3 ≤ (Real.log x) ^ (c / 2) ∧
        Real.log Ybig ≤ (Real.log x) ^ (c / 2) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ),
      hLogLim.eventually_ge_atTop 1, hULim.eventually_ge_atTop 3,
      hULim.eventually_ge_atTop (Real.log Ybig)] with x hx hL hU hY
    exact ⟨hx, hL, hU, hY⟩
  refine ⟨(2 + 3 * C) * M, by positivity, ?_⟩
  filter_upwards [hXEvents] with x hx
  rcases hx with ⟨hx2, hLone, hu3, hYbigLog⟩
  let L : ℝ := Real.log x
  let u : ℝ := L ^ (c / 2)
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < L := by positivity
  have hLone' : 1 ≤ L := by assumption
  have hu3' : 3 ≤ u := by simpa [L, u] using hu3
  have hYbigLog' : Real.log Ybig ≤ u := by simpa [L, u] using hYbigLog
  have hU_sq : u ^ 2 = L ^ c := by
    dsimp [u]
    rw [pow_two, ← Real.rpow_add hLpos]
    congr 1
    ring
  have hExp2u : 2 ≤ Real.exp (2 * u) := by
    have h := Real.add_one_le_exp (2 * u)
    linarith [hu3']
  have hExpU : 2 * Real.exp u ≤ Real.exp (L ^ c) := by
    calc
      2 * Real.exp u ≤ Real.exp u * Real.exp (2 * u) := by
        nlinarith [Real.exp_pos u, hExp2u]
      _ = Real.exp (u + 2 * u) := by rw [← Real.exp_add]
      _ ≤ Real.exp (u ^ 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hu3']
      _ = Real.exp (L ^ c) := by rw [hU_sq]
  have hExpLtwo : 2 ≤ Real.exp (L ^ c) := by
    have h := Real.add_one_le_exp (L ^ c)
    linarith [(by
      calc
        1 = (1 : ℝ) ^ c := by simp
        _ ≤ L ^ c := Real.rpow_le_rpow (by norm_num) hLone' (by linarith))]
  intro lo hi t r χ hlo hlohi hhi hr hrLog hχ ht
  let a := ⌈lo⌉₊
  let n := a - 1
  let m := ⌊hi⌋₊
  have hloPos : 0 < lo := by
    have hlo' : Real.exp (L ^ c) ≤ lo := by simpa [L, Analytic.L] using hlo
    exact (Real.exp_pos _).trans_le hlo'
  have haPos : 1 ≤ a := by
    apply Nat.one_le_iff_ne_zero.mpr
    positivity
  have hna : n + 1 = a := Nat.sub_add_cancel haPos
  have haLeLo : lo ≤ a := by
    exact_mod_cast Nat.le_ceil lo
  have hnCast : n = (a : ℝ) - 1 := by
    dsimp [n]
    rw [Nat.cast_sub (by omega : 1 ≤ a)]
    simp
  have hloLarge : 2 ≤ lo := Trans.trans hExpLtwo hlo
  have hloExp : Real.exp (L ^ c) ≤ lo := by assumption
  have hnExp : Real.exp u ≤ (n : ℝ) := by
    linarith
  have hYθLe : Yθ ≤ Real.exp u := by
    have hYexp : Ybig ≤ Real.exp u := by
      calc
        Ybig = Real.exp (Real.log Ybig) := by
          rw [Real.exp_log]
          positivity
        _ ≤ Real.exp u := Real.exp_le_exp.mpr hYbigLog'
    exact le_trans (le_max_right 1 Yθ) hYexp
  have hnYθ : Yθ ≤ (n : ℝ) := hYθLe.trans hnExp
  have hnOne : 1 ≤ (n : ℝ) := by
    linarith
  have hnNatOne : 1 ≤ n := by exact_mod_cast hnOne
  have hnm : n ≤ m := by
    have haUpper : a ≤ m + 1 := by
      dsimp [a]
      apply Nat.ceil_le.mpr
      exact hlohi.trans (by
        exact_mod_cast (Nat.lt_floor_add_one hi).le)
    omega
  have hnmReal : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hmPos : 0 < (m : ℝ) := by linarith
  have hmLeHi : (m : ℝ) ≤ hi := by
    exact Nat.floor_le (by linarith [hloPos, hlohi])
  have hLogN : u ≤ Real.log n := by
    calc
      u = Real.log (Real.exp u) := by simp
      _ ≤ Real.log n := by gcongr
  have hBetaPow : u ^ β = L ^ B := by
    dsimp [β]
    rw [← Real.rpow_mul hLpos.le (c / 2) (2 * B / c)]
    congr 1
    field_simp
  have hDPow : u ^ (-D) = L ^ (-E) := by
    dsimp [D]
    rw [← Real.rpow_mul hLpos.le (c / 2) (- (2 * E / c))]
    congr 1
    field_simp
  have hLocalTheta (y : ℝ) (hny : (n : ℝ) ≤ y) :
      ‖Erdos821.DivisorHarmonic.thetaCharacterPrefix y χ‖ ≤
        M * y * L ^ (-E) := by
    have hyPos : 0 < y := by linarith
    have hLogLower : u ≤ Real.log y := by
      calc
        u ≤ Real.log n := hLogN
        _ ≤ Real.log y := by gcongr
    have hqβ : (r : ℝ) ≤ (Real.log y) ^ β := by
      calc
        (r : ℝ) ≤ L ^ B := hrLog
        _ = u ^ β := hBetaPow.symm
        _ ≤ (Real.log y) ^ β :=
          by gcongr
    have hTheta := hThetaFrom y (hnYθ.trans hny) r χ (by omega) hqβ hχ
    have hPower : (Real.log y) ^ (-D) ≤ L ^ (-E) := by
      calc
        (Real.log y) ^ (-D) ≤ u ^ (-D) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hLogLower (by linarith)
        _ = L ^ (-E) := hDPow
    exact hTheta.trans <| mul_le_mul_of_nonneg_left hPower
      (mul_nonneg hM.le hyPos.le)
  have hlogm : Real.log ((m : ℝ) / n) ≤ C * L := by
    rw [Real.log_div hmPos.ne' (by positivity : (n : ℝ) ≠ 0)]
    have hle := Real.log_le_log hmPos (hmLeHi.trans hhi)
    rw [Real.log_rpow hxpos] at hle
    linarith [Real.log_nonneg hnOne]
  have hab := Erdos821.DivisorHarmonic.abel_bound χ t (M * L ^ (-E))
    ((Real.exp_le_exp.mpr (by linarith : 1 ≤ u)).trans hnExp) hnm (by positivity)
    (fun y h ↦ by simpa [mul_right_comm] using hLocalTheta y h)
  change ‖∑ p ∈ (Finset.Icc a m).filter Nat.Prime, _‖ ≤ _
  rw [← hna, Finset.Icc_add_one_left_eq_Ioc]
  refine hab.trans ?_
  have hB1 : 1 ≤ L ^ B := Real.one_le_rpow hLone' hB.le
  have hL1 : L ^ (-E) ≤ L ^ (-A) := Real.rpow_le_rpow_of_exponent_le hLone' (by linarith)
  have hpow : L ^ (-E) * L ^ B * L ≤ L ^ (-A) := by
    rw [← Real.rpow_add hLpos, ← Real.rpow_add_one hLpos.ne']
    apply Real.rpow_le_rpow_of_exponent_le hLone'
    linarith
  have ht' : |t| + 2 ≤ 3 * L ^ B := by have h : |t| ≤ L ^ B := ht; linarith
  have hratio := Real.log_nonneg ((one_le_div (zero_lt_one.trans_le hnOne)).mpr hnmReal)
  calc _ ≤ M * L ^ (-E) * (2 + (3 * L ^ B) * (C * L)) := by gcongr
       _ = 2 * M * L ^ (-E) + 3 * C * M * (L ^ (-E) * L ^ B * L) := by ring
       _ ≤ 2 * M * L ^ (-A) + 3 * C * M * L ^ (-A) := by gcongr
       _ = (2 + 3 * C) * M * L ^ (-A) := by ring

end Erdos821.Blueprint
