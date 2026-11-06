module

public import AnalyticESC.Basic

public section

set_option hygiene false
local notation "𝕭" => 2 * q + p
local notation "𝕬" => isPreconnected_nbhd ε
local notation "𝖟" => f y - g y
local notation "𝖞" => j + 2
local notation "𝖘" => ε / c

local notation "𝖗" => nbhd ε

local notation "𝖖" => a + b

local notation "𝔶" => f x - g x

local notation "𝔵" => v - 1

local notation "𝔲" => 𝔇 f ξ₁ - 𝔇 g ξ₂

local notation "𝔨" => y - x

local notation "𝔧" => 2 * Real.exp 1 / p

local notation "𝔤" => 2 + Q

local notation "𝔣" => -x ^ 2 / σ

/-!
# Real-variable and identity-theorem lemmas

Lemma 3.1 (closeness of two functions gives closeness of their derivatives), its iterate, the
identity theorem on `B_ε` in the forms used in the paper, and the elementary bound (4.3).
-/

namespace AnalyticESC
variable {Q η : ℝ}

variable {U : Set ℝ} {a b p x ε σ : ℝ} {f : ℝ → ℝ} {g h : ℂ → ℂ}

open Set Metric Filter Topology

/-! ## Lemma 3.1 and its iterate -/

/-- Taylor's theorem of order two with the Lagrange remainder, for a `𝒞²` map on an open set
containing the segment between `x` and `y`. -/
theorem exists_taylor_two (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) (hxy : x ≠ y) (hsub : uIcc x y ⊆ U) :
    ∃ ξ ∈ uIoo x y, f y - f x - deriv f x * 𝔨 = 𝔇 f ξ * 𝔨 ^ 2 / 2 := by
  obtain ⟨ξ, hξ, h⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hxy
    ((hf.mono hsub).of_le (by norm_num))
  refine ⟨ξ, hξ, ?_⟩
  have hd : derivWithin f (uIcc x y) x = deriv f x := by
    have : DifferentiableAt ℝ f x :=
      (hf.contDiffAt (hU.mem_nhds (hsub left_mem_uIcc))).differentiableAt (by norm_num)
    exact this.derivWithin (uniqueDiffOn_uIcc hxy x left_mem_uIcc)
  simp at h
  rw [iteratedDeriv_succ, iteratedDeriv_one] at h
  grind

local notation "𝔉" P => ∀ x ∈ Icc a b, P

/-- Lemma 3.1 for `𝒞²` maps on a neighbourhood of `J = [a, b]`, with any common bound `Q` for the
second derivatives. -/
theorem abs_deriv_sub_le_of_abs_sub_le {f g : ℝ → ℝ} (hU : IsOpen U)
    (hab : Icc a b ⊆ U) (hf : ContDiffOn ℝ 2 f U) (hg : ContDiffOn ℝ 2 g U) (hη : 0 < η)
    (hJ : 2 * Real.sqrt η < b - a) (hfQ : 𝔉 |𝔇 f x| ≤ Q)
    (hgQ : 𝔉 |𝔇 g x| ≤ Q) (hfg : 𝔉 |f x - g x| ≤ η) :
    𝔉 |deriv f x - deriv g x| ≤ 𝔤 * Real.sqrt η := by
  intro x hx
  have hs := Real.sqrt_pos.2 hη
  -- One of `x ± √η` lies in `[a, b]`.
  obtain ⟨y, hy, hyx⟩ : ∃ y ∈ Icc a b, |y - x| = Real.sqrt η := by
    by_cases h : x + Real.sqrt η ≤ b
    · exact ⟨x + Real.sqrt η, ⟨by grind, h⟩, by simp⟩
    · refine ⟨x - Real.sqrt η, ⟨by linarith, by grind⟩, ?_⟩
      simp_all
  have hsub := uIcc_subset_Icc hx hy
  obtain ⟨ξ₁, hξ₁, h₁⟩ := exists_taylor_two hU hf (by grind) (hsub.trans hab)
  obtain ⟨ξ₂, hξ₂, h₂⟩ := exists_taylor_two hU hg (by grind) (hsub.trans hab)
  have hξ₁' := hsub (Ioo_subset_Icc_self hξ₁)
  have hξ₂' := hsub (Ioo_subset_Icc_self hξ₂)
  have hd2 : 𝔨 ^ 2 = η := by grind
  have key : (deriv f x - deriv g x) * 𝔨 = 𝖟 - 𝔶 -
      𝔲 * 𝔨 ^ 2 / 2 := by
    linear_combination h₂ - h₁
  have hb : |𝔇 f ξ₁ - 𝔇 g ξ₂| ≤ 2 * Q := by grind
  have hmain : |deriv f x - deriv g x| * Real.sqrt η ≤ 𝔤 * Real.sqrt η * Real.sqrt η := by
    rw [← hyx, ← abs_mul, key, hd2, hyx, mul_assoc, ← sq, Real.sq_sqrt hη.le]
    have e1 := abs_sub (f y - g y - 𝔶)
      (𝔲 * η / 2)
    have e2 := abs_sub 𝖟 𝔶
    have e3 : |𝔲 * η / 2| ≤ Q * η := by
      rw [abs_div, abs_mul, abs_of_pos hη, abs_two]
      nlinarith
    grind
  simp_all

/-- The `j`-th derivative of a `𝒞ⁿ` map on an open set is `𝒞^m` there whenever `j + m ≤ n`. -/
theorem contDiffOn_iteratedDeriv_of_isOpen (hU : IsOpen U)
    {n : ℕ} (hf : ContDiffOn ℝ n f U) (hjm : j + m ≤ n) :
    ContDiffOn ℝ m (iteratedDeriv j f) U := by
  induction j generalizing m with
  | zero =>
    exact hf.of_le (by simp_all)
  | succ j ih =>
    rw [iteratedDeriv_succ]
    exact (ih (m := m + 1) (by omega)).deriv_of_isOpen hU (by simp_all)

/-- Lemma 3.1 iterated `k` times: closeness `η ≤ 1` of `f` and `g` gives closeness
`(2 + Q)² η^{2^{-k}}` of their `k`-th derivatives, given bounds `Q` on the derivatives of order
at most `k + 1`. -/
theorem abs_iteratedDeriv_sub_le {f g : ℝ → ℝ} (k : ℕ) (hU : IsOpen U)
    (hab : Icc a b ⊆ U) (hf' : ContDiffOn ℝ ↑(k + 1) f U) (hg' : ContDiffOn ℝ ↑(k + 1) g U)
    (hη : 0 < η) (hη1 : η ≤ 1) (hQ : 0 ≤ Q)
    (hfQ : ∀ j ≤ k + 1, 𝔉 |iteratedDeriv j f x| ≤ Q)
    (hgQ : ∀ j ≤ k + 1, 𝔉 |iteratedDeriv j g x| ≤ Q)
    (hJ : 2 * 𝔤 * η ^ (2⁻¹ ^ k : ℝ) < b - a) (hfg : 𝔉 |f x - g x| ≤ η) :
    𝔉 |iteratedDeriv k f x - iteratedDeriv k g x| ≤ 𝔤 ^ 2 * η ^ (2⁻¹ ^ k : ℝ) :=
  by
  have h2Q : 1 ≤ 𝔤 ^ 2 := by nlinarith
  -- The bound `(2 + Q)² η^{2^{-j}}` is preserved by one application of Lemma 3.1.
  suffices H : ∀ j ≤ k, ∀ x ∈ Icc a b,
      |iteratedDeriv j f x - iteratedDeriv j g x| ≤ 𝔤 ^ 2 * η ^ (2⁻¹ ^ j : ℝ) from
    H k le_rfl
  intro j
  induction j with
  | zero =>
    intro _ x hx
    simp
    nlinarith [hfg x hx]
  | succ j ih =>
    intro hjk x hx
    have hsqrt : Real.sqrt (𝔤 ^ 2 * η ^ (2⁻¹ ^ j : ℝ)) =
        𝔤 * η ^ (2⁻¹ ^ (j + 1) : ℝ) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by linarith), Real.sqrt_eq_rpow,
        ← Real.rpow_mul hη.le, pow_succ, one_div]
    have hexp : η ^ (2⁻¹ ^ (j + 1) : ℝ) ≤ η ^ (2⁻¹ ^ k : ℝ) := by bound
    have hdd : ∀ φ : ℝ → ℝ, 𝔇 (iteratedDeriv j φ) = iteratedDeriv 𝖞 φ := by
      intro φ
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
    have key := abs_deriv_sub_le_of_abs_sub_le hU hab
      (contDiffOn_iteratedDeriv_of_isOpen hU hf' (m := 2) (by omega))
      (contDiffOn_iteratedDeriv_of_isOpen hU hg' (m := 2) (by omega)) (by positivity) (by nlinarith)
      (fun y hy => by rw [hdd]; exact hfQ 𝖞 (by omega) y hy)
      (fun y hy => by rw [hdd]; exact hgQ 𝖞 (by omega) y hy)
      (ih (by omega)) x hx
    rw [hsqrt, ← iteratedDeriv_succ, ← iteratedDeriv_succ] at key
    exact key.trans_eq (by ring)

/-! ## The identity theorem on `B_ε` -/

/-- The inclusion `ℝ → ℂ` maps punctured neighbourhoods into punctured neighbourhoods. -/
theorem tendsto_ofReal_nhdsNE c :
    Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] c) (𝓝[≠] c) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp_all

/-- The real points of a nondegenerate interval accumulate in `ℂ` at its midpoint. -/
theorem frequently_ofReal_mem_Icc (hab : a < b) :
    ∃ᶠ z : ℂ in 𝓝[≠] ((𝖖 / 2 : ℝ) : ℂ), ∃ x ∈ Icc a b, z = x := by
  have h1 : ∃ᶠ x in 𝓝[≠] (𝖖 / 2), x ∈ Icc a b :=
    (eventually_nhdsWithin_of_eventually_nhds (Icc_mem_nhds (by linarith) (by linarith))).frequently
  exact (tendsto_ofReal_nhdsNE _).frequently (h1.mono fun x hx => ⟨x, hx, rfl⟩)

section
variable (hε : 0 < ε) (hg : DifferentiableOn ℂ g 𝖗)
include hε hg

/-- Identity theorem: maps holomorphic on `B_ε` that agree on a nondegenerate interval of `I`
agree on `B_ε`. -/
theorem eqOn_nbhd_of_eqOn_Icc (hh : DifferentiableOn ℂ h 𝖗)
    (hab : a < b) (hI : Icc a b ⊆ I) (heq : 𝔉 g x = h x) : EqOn g h 𝖗 := by
  have hc : ((𝖖 / 2 : ℝ) : ℂ) ∈ nbhd ε :=
    ofReal_mem_nbhd hε (hI ⟨by linarith, by linarith⟩)
  refine (hg.analyticOnNhd isOpen_nbhd).eqOn_of_preconnected_of_frequently_eq (hh.analyticOnNhd isOpen_nbhd)
    𝕬 hc ?_
  exact (frequently_ofReal_mem_Icc hab).mono fun z ⟨x, hx, hz⟩ => hz ▸ heq x hx

/-- Identity theorem: maps holomorphic on `B_ε` with all derivatives equal at a point of `I`
agree on `B_ε`. -/
theorem eqOn_nbhd_of_iteratedDeriv_eq (hh : DifferentiableOn ℂ h 𝖗) (hx : x ∈ I)
    (heq : ∀ k, iteratedDeriv k g x = iteratedDeriv k h x) : EqOn g h 𝖗 := by
  -- Both maps equal their Taylor series at `x` on the disc of radius `ε`.
  have hloc : g =ᶠ[𝓝 (x : ℂ)] h := by
    filter_upwards [ball_mem_nhds (x : ℂ) hε] with z hz
    rw [← Complex.taylorSeries_eq_on_ball' hz (hg.mono (ball_subset_nbhd hx)),
      ← Complex.taylorSeries_eq_on_ball' hz (hh.mono (ball_subset_nbhd hx))]
    simp_all
  exact (hg.analyticOnNhd isOpen_nbhd).eqOn_of_preconnected_of_eventuallyEq (hh.analyticOnNhd isOpen_nbhd)
    𝕬 (ofReal_mem_nbhd hε hx) hloc

/-- A map holomorphic on `B_ε`, not identically zero on `I`, has finitely many zeros in `I`. -/
theorem finite_zeros (hne : ∃ x ∈ I, g x ≠ 0) : {x : ℝ | x ∈ I ∧ g x = 0}.Finite := by
  by_contra hinf
  -- Infinitely many zeros in the compact `I` accumulate at some `c ∈ I`.
  obtain ⟨c, hcI, hacc⟩ :=
    Set.Infinite.exists_accPt_of_subset_isCompact hinf isCompact_Icc fun x hx => hx.1
  have hzero :=
    (hg.analyticOnNhd isOpen_nbhd).eqOn_zero_of_preconnected_of_frequently_eq_zero
      𝕬 (ofReal_mem_nbhd hε hcI) (by rw [accPt_iff_frequently_nhdsNE] at hacc; exact (tendsto_ofReal_nhdsNE c).frequently (hacc.mono fun x hx => hx.2))
  obtain ⟨x, hx, hgx⟩ := hne
  exact hgx (hzero (ofReal_mem_nbhd hε hx))

end

/-! ## The bound (4.3) -/

local notation "𝔓" => (p / 2)
local notation "𝔔" => (𝔓 * σ)

/-- The maximum of `|x|^p e^{-x²/σ}` over `x ∈ ℝ` is `(pσ/2)^{p/2} e^{-p/2}`. -/
theorem rpow_abs_mul_exp_le (hp : 0 < p) (hσ : 0 < σ) x :
    |x| ^ p * Real.exp 𝔣 ≤ 𝔔 ^ 𝔓 * Real.exp (-𝔓) := by
  have hA : 0 < 𝔓 := by positivity
  have hAσ : 0 < 𝔓 * σ := by positivity
  set v := x ^ 2 / 𝔔 with hv_def
  have h2 : |x| ^ p = 𝔔 ^ 𝔓 * v ^ 𝔓 := by
    rw [← Real.mul_rpow hAσ.le (by positivity), hv_def, mul_div_cancel₀ _ hAσ.ne',
      show p = 2 * 𝔓 by ring, Real.rpow_mul (abs_nonneg x)]
    norm_num
  have h3 : v ^ 𝔓 ≤ Real.exp (𝔵 * 𝔓) := by
    rw [Real.exp_mul]
    exact Real.rpow_le_rpow (by positivity) (by linarith [Real.add_one_le_exp 𝔵]) hA.le
  have h4 : 𝔵 * 𝔓 + -x ^ 2 / σ = -𝔓 := by grind
  calc |x| ^ p * Real.exp 𝔣
      = 𝔔 ^ 𝔓 * (v ^ 𝔓 * Real.exp 𝔣) := by grind
    _ ≤ 𝔔 ^ 𝔓 * (Real.exp (𝔵 * 𝔓) * Real.exp 𝔣) := by
      gcongr
    _ = 𝔔 ^ 𝔓 * Real.exp (-𝔓) := by rw [← Real.exp_add, h4]

/-- The elementary bound (4.3): for `c, p, ε > 0` and `q > -p/2`,
`sup_{x ∈ ℝ} c σ^q |x|^p e^{-x²/σ} ≤ ε` whenever
`0 < σ ≤ (2e/p)^{p/(2q+p)} (ε/c)^{1/(q+p/2)}`. -/
theorem gaussian_bound (hc : 0 < c) (hp : 0 < p) (hε : 0 < ε) (hq : -𝔓 < q)
    (hσ : 0 < σ)
    (hσle : σ ≤ 𝔧 ^ (p / 𝕭) * 𝖘 ^ (1 / (q + 𝔓)))
    x : c * σ ^ q * |x| ^ p * Real.exp 𝔣 ≤ ε := by
  have hA : 0 < 𝔓 := by positivity
  have hr : 0 < q + 𝔓 := by linarith
  have h2qp : 0 < 2 * q + p := by linarith
  -- Raise the hypothesis on `σ` to the power `q + p/2`.
  have hσr : σ ^ (q + 𝔓) ≤ 𝔧 ^ 𝔓 * 𝖘 := by
    have h := Real.rpow_le_rpow hσ.le hσle hr.le
    rwa [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity),
      ← Real.rpow_mul (by positivity),
      show p / 𝕭 * (q + 𝔓) = 𝔓 by field_simp,
      one_div_mul_cancel hr.ne', Real.rpow_one] at h
  have he : 𝔓 * 𝔧 = Real.exp 1 := by field_simp
  calc c * σ ^ q * |x| ^ p * Real.exp 𝔣
      = c * σ ^ q * (|x| ^ p * Real.exp 𝔣) := by ring
    _ ≤ c * σ ^ q * (𝔔 ^ 𝔓 * Real.exp (-𝔓)) :=
      mul_le_mul_of_nonneg_left (rpow_abs_mul_exp_le hp hσ x) (by positivity)
    _ = c * (𝔓 ^ 𝔓 * Real.exp (-𝔓)) * σ ^ (q + 𝔓) := by
      rw [Real.mul_rpow hA.le hσ.le, Real.rpow_add hσ]
      ring
    _ ≤ c * (𝔓 ^ 𝔓 * Real.exp (-𝔓)) *
        (𝔧 ^ 𝔓 * 𝖘) := by gcongr
    _ = c * 𝖘 * (Real.exp (-𝔓) * (𝔓 * 𝔧) ^ 𝔓) := by
      rw [Real.mul_rpow hA.le (by positivity)]
      ring
    _ = ε := by
      rw [he, Real.exp_one_rpow, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
      field_simp

end AnalyticESC
