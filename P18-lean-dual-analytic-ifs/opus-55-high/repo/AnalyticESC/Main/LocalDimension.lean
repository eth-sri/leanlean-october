module

public import AnalyticESC.Main.Example
public import AnalyticESC.Separation
set_option hygiene false
local notation "𝕭" => m r
local notation "𝕬" => measurable_prefix n
local notation "𝖟" => Real.rpow_nonneg (hpos _).le _
local notation "𝖞" => Φ.pressureSum t n
local notation "𝖝" => wordCylinder w
local notation "𝔲" => 1 + x

local notation "𝔨" => j + k

local notation "𝔧" => List.ofFn v

local notation "𝔤" => 2 ^ s

local notation "𝔣" => wordCylinder 𝔧


@[expose] public section

/-!
# The local dimension of the natural measure of the polynomial example

The natural measure `μ = ν ∘ π⁻¹` of the polynomial example in Section 1.2.2, where
`ν` is the Gibbs measure of the potential `s(Φ) log|f'_{ω₁}(π(σω))|`, has local dimension
`s(Φ) - 1/3 < s(Φ)` at `0`.

The Gibbs measure is not constructed here. The results assume a probability measure `ν` on `Σ`
with the Gibbs property `C⁻¹ ‖f_w'‖^s ≤ ν[w] ≤ C ‖f_w'‖^s` for every finite word `w`, which Bowen's
theorem provides for `s = s(Φ)`. The Gibbs property determines `s`: the pressure
`P(t) = lim_n (1/n) log ∑_{w ∈ Σ_n} ‖f_w'‖^t` vanishes at `t = s` and at no other `t`.
-/

namespace AnalyticESC
variable {w : 𝔚 3} {ω : ℕ → Fin 3}

variable {n : ℕ} {s x : ℝ}

open Set Metric Filter Topology MeasureTheory

/-- The cylinder `[w] = {ω ∈ Σ : ω₁ ⋯ ω_{|w|} = w}` of a finite word. -/
def wordCylinder (w : 𝔚 N) : Set 𝔖 N :=
  {ω | ∀ k : Fin w.length, ω k = w[k]}

namespace IFS

variable (Φ : IFS N ε) (w : 𝔚 N)

/-- `‖f_w'‖ = sup_{x ∈ [0,1]} |f_w'(x)|`. -/
noncomputable def supDeriv : ℝ := ⨆ x : I, ‖𝔡ᶜ Φ w x‖

/-- The sum `∑_{w ∈ Σ_n} ‖f_w'‖^t`, whose exponential growth rate is the pressure `P(t)`. -/
noncomputable def pressureSum (t : ℝ) (n : ℕ) : ℝ :=
  ∑ w : Fin n → Fin N, Φ.supDeriv (List.ofFn w) ^ t

/-- The pressure `P(t) = lim_n (1/n) log ∑_{w ∈ Σ_n} ‖f_w'‖^t` vanishes exactly for `t = s`. -/
def PressureZero (s : ℝ) : Prop :=
  ∀ t, Tendsto (fun n => Real.log 𝖞 / n) atTop (𝓝 0) ↔ t = s

/-- `ν` has the Gibbs property for the potential `s log|f'|`: `ν[w]` is comparable to `‖f_w'‖^s`,
uniformly over finite words `w`. -/
def IsGibbs (s : ℝ) (ν : Measure 𝔖 N) : Prop :=
  ∃ C > 0, ∀ w,
    C⁻¹ * Φ.supDeriv w ^ s ≤ ν.real 𝖝 ∧
      ν.real 𝖝 ≤ C * Φ.supDeriv w ^ s

/-- The prefix map `ω ↦ ω₁ ⋯ ωₙ` is measurable. -/
theorem measurable_prefix n : Measurable fun (ω : 𝔖 N) (k : Fin n) => ω k := by fun_prop

/-- The natural projection is measurable, so `ν ∘ π⁻¹` is the image measure of `ν`. -/
theorem measurable_natProj : Measurable Φ.natProj :=
  measurable_of_tendsto_metrizable
    (f := fun n ω => (Φ.comp (List.ofFn fun k => ω k) 0).re)
    (fun n => (measurable_of_finite fun v : Fin n → Fin N => (Φ.comp 𝔧 0).re).comp
      𝕬)
    (tendsto_pi_nhds.2 Φ.tendsto_natProj)

/-- The cylinders of the words of length `n` cover `Σ`: the measure of the set of infinite words
whose prefix of length `n` lies in `S` is the sum of the measures of the cylinders of `S`. -/
theorem sum_measureReal_wordCylinder (ν : Measure 𝔖 N) [IsFiniteMeasure ν] n
    (S : Finset (Fin n → Fin N)) :
    ∑ v ∈ S, ν.real 𝔣 =
      ν.real ((fun (ω : 𝔖 N) (k : Fin n) => ω k) ⁻¹' ↑S) := by
  rw [← map_measureReal_apply 𝕬 (MeasurableSet.of_discrete),
    ← sum_measureReal_singleton]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_measureReal_apply 𝕬 (MeasurableSet.of_discrete)]
  congr
  ext ω
  simp [wordCylinder, funext_iff, Fin.forall_iff]

theorem sum_measureReal_wordCylinder_univ (ν : Measure 𝔖 N)
    [IsProbabilityMeasure ν] n :
    ∑ v : Fin n → Fin N, ν.real 𝔣 = 1 := by
  rw [sum_measureReal_wordCylinder, Finset.coe_univ, preimage_univ, probReal_univ]

theorem bddAbove_norm_deriv_comp :
    BddAbove (range fun x : I => ‖𝔡ᶜ Φ w x‖) :=
  ⟨Φ.cmax ^ w.length, by
    rintro _ ⟨x, rfl⟩
    exact Φ.norm_deriv_comp_le w (Φ.ofReal_mem_cl x.2)⟩

/-- `|f_w'(x)| ≤ ‖f_w'‖` for `x ∈ [0,1]`. -/
theorem norm_deriv_le_supDeriv (hx : x ∈ I) :
    ‖𝔡ᶜ Φ w x‖ ≤ Φ.supDeriv w :=
  le_ciSup (Φ.bddAbove_norm_deriv_comp w)
    ⟨x, hx⟩

/-- `‖f_w'‖ ≤ c_max^{|w|}`. -/
theorem supDeriv_le : Φ.supDeriv w ≤ Φ.cmax ^ w.length :=
  ciSup_le fun x => Φ.norm_deriv_comp_le w (Φ.ofReal_mem_cl x.2)

/-- `c_min^{|w|} ≤ ‖f_w'‖`. -/
theorem cmin_pow_le_supDeriv : Φ.cmin ^ w.length ≤ Φ.supDeriv w :=
  (Φ.cmin_pow_le_norm_deriv_comp w
    (Φ.ofReal_mem_cl zero_mem_I)).trans
    (Φ.norm_deriv_le_supDeriv w zero_mem_I)

theorem supDeriv_pos (hN : 0 < N) w : 0 < Φ.supDeriv w :=
  (pow_pos (Φ.cmin_pos hN) _).trans_le (Φ.cmin_pow_le_supDeriv w)

theorem pressureSum_pos (hN : 0 < N) t n : 0 < Φ.pressureSum t n :=
  Finset.sum_pos (fun _ _ => Real.rpow_pos_of_pos (Φ.supDeriv_pos hN _) t)
    ⟨fun _ => ⟨0, hN⟩, Finset.mem_univ _⟩

local notation "𝔩" => (t - s) * Real.log Φ.cmax

/-- The Gibbs property determines the exponent: the pressure `P(t)` exists and vanishes exactly
for `t = s`, so `s = s(Φ)`. -/
theorem tendsto_pressure_iff_of_isGibbs (hN : 0 < N)
    [IsProbabilityMeasure ν] (hν : Φ.IsGibbs s ν) :
    Φ.PressureZero s := fun t => by
  obtain ⟨C, hC, hG⟩ := hν
  have hL := Real.log_neg (Φ.cmax_pos hN) Φ.cmax_lt_one
  have hpos := Φ.supDeriv_pos hN
  have hP := Φ.pressureSum_pos hN t
  -- the Gibbs property and `∑_w ν[w] = 1` give `C⁻¹ ≤ P_n(s) ≤ C`
  have hPs : ∀ n, Φ.pressureSum s n ≤ C ∧ C⁻¹ ≤ Φ.pressureSum s n := by
    intro n
    rw [← inv_mul_le_one₀ hC, inv_le_iff_one_le_mul₀' hC,
      ← sum_measureReal_wordCylinder_univ ν n, pressureSum, Finset.mul_sum, Finset.mul_sum]
    exact ⟨Finset.sum_le_sum fun v _ => (hG _).1, Finset.sum_le_sum fun v _ => (hG _).2⟩
  -- `‖f_w'‖^t = ‖f_w'‖^s ⋅ exp(log ‖f_w'‖ ⋅ (t - s))` and `log ‖f_w'‖ ≤ |w| log c_max`
  have hsum : ∀ n, (s ≤ t → Φ.pressureSum t n ≤
      Φ.pressureSum s n * Real.exp (𝔩 * n)) ∧
      (t ≤ s → Φ.pressureSum s n * Real.exp (𝔩 * n) ≤
        Φ.pressureSum t n) := fun n => by
    have hlog : ∀ v, Real.log (Φ.supDeriv 𝔧) ≤ n * Real.log Φ.cmax :=
      fun v => by simpa using Real.log_le_log (hpos _) (Φ.supDeriv_le 𝔧)
    have hterm : ∀ w, Φ.supDeriv w ^ t =
        Φ.supDeriv w ^ s * Real.exp (Real.log (Φ.supDeriv w) * (t - s)) := fun w => by
      rw [← Real.rpow_def_of_pos (hpos w), ← Real.rpow_add (hpos w), add_sub_cancel]
    simp [pressureSum, Finset.sum_mul, hterm]
    exact ⟨fun h => Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (by nlinarith [hlog v])) 𝖟,
      fun h => Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (by nlinarith [hlog v])) 𝖟⟩
  -- taking logarithms and dividing by `n`
  have key : ∀ n, 1 ≤ n →
      (s ≤ t → Real.log 𝖞 / n ≤ Real.log C / n + 𝔩) ∧
      (t ≤ s → -Real.log C / n + 𝔩 ≤ Real.log 𝖞 / n) := by
    intro n hn
    have hn : (0 : ℝ) < n := Nat.cast_pos.2 hn
    rw [div_add' _ _ _ hn.ne', div_add' _ _ _ hn.ne', div_le_div_iff_of_pos_right hn,
      div_le_div_iff_of_pos_right hn, Real.log_le_iff_le_exp (hP n), Real.le_log_iff_exp_le (hP n),
      Real.exp_add, Real.exp_add, Real.exp_neg, Real.exp_log hC]
    exact ⟨fun h => ((hsum n).1 h).trans (mul_le_mul_of_nonneg_right (hPs n).1 (Real.exp_pos _).le),
      fun h => (mul_le_mul_of_nonneg_right (hPs n).2 (Real.exp_pos _).le).trans ((hsum n).2 h)⟩
  have hlim : ∀ b, Tendsto (fun n : ℕ => b / n + 𝔩) atTop
      (𝓝 𝔩) :=
    fun b => by simpa using (tendsto_const_div_atTop_nhds_zero_nat b).add_const _
  refine ⟨fun h => by_contra fun hts => ?_, fun hts => ?_⟩
  · rcases lt_or_gt_of_ne hts with hts | hts
    · nlinarith [le_of_tendsto_of_tendsto (hlim _) h
        (eventually_atTop.2 ⟨1, fun n hn => (key n hn).2 hts.le⟩)]
    · nlinarith [le_of_tendsto_of_tendsto h (hlim _)
        (eventually_atTop.2 ⟨1, fun n hn => (key n hn).1 hts.le⟩)]
  · subst hts
    simpa using tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlim (-Real.log C)) (hlim (Real.log C))
      (eventually_atTop.2 ⟨1, fun n hn => (key n hn).2 le_rfl⟩)
      (eventually_atTop.2 ⟨1, fun n hn => (key n hn).1 le_rfl⟩)

/-- `π(ω) = f_{ω₁ ⋯ ω_k}(π(σ^k ω))`, where `σ` is the left shift. -/
theorem natProj_eq_comp_prefix ω k :
    Φ.natProj ω =
      (Φ.comp (List.ofFn fun j : Fin k => ω j) (Φ.natProj fun j => ω 𝔨)).re := by
  set v : 𝔖 N := fun j => ω 𝔨
  set a := List.ofFn fun j => ω j
  have hlist : ∀ n, (List.ofFn fun j : Fin (n + k) => ω j) =
      a ++ List.ofFn fun j : Fin n => v j := fun n =>
    List.ext_getElem (by grind) fun l h1 h2 => by grind
  have hc : ContinuousAt (fun t : ℝ => (Φ.comp a t).re) (Φ.natProj v) :=
    Complex.continuous_re.continuousAt.comp ((Φ.differentiableAt_comp a
      (Φ.ofReal_mem_cl (Φ.attractor_subset_I ⟨v, rfl⟩))).continuousAt.comp
      Complex.continuous_ofReal.continuousAt)
  refine tendsto_nhds_unique ((tendsto_add_atTop_iff_nat k).2 (Φ.tendsto_natProj ω)) ?_
  refine (hc.tendsto.comp (Φ.tendsto_natProj v)).congr fun n => ?_
  rw [Function.comp_apply, hlist n, Φ.comp_append, Function.comp_apply, ← Complex.ofReal_zero,
    ← Φ.comp_ofReal _ zero_mem_I]

end IFS

/-! ### The local dimension: an analytic lemma -/

/-- If `a ρ^n ≤ m(r) ≤ b ρ^n` whenever `λ^{n+2} < r ≤ λ^{n+1}`, then
`log m(r) / log r → log ρ / log λ` as `r → 0⁺`. -/
theorem tendsto_log_div_log_of_bounds {m : ℝ → ℝ} (hlam0 : 0 < lam)
    (hlam1 : lam < 1) (hρ : 0 < ρ) (ha : 0 < a) (hb : 0 < b)
    (h : ∀ n r, lam ^ (n + 2) < r → r ≤ lam ^ (n + 1) →
      a * ρ ^ n ≤ m r ∧ m r ≤ b * ρ ^ n) :
    Tendsto (fun r => Real.log 𝕭 / Real.log r) (𝓝[>] 0)
      (𝓝 (Real.log ρ / Real.log lam)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    ((tendsto_const_nhds (x := |Real.log a| + |Real.log b| + 2 * |Real.log ρ|)).div_atTop
      (tendsto_abs_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero))
  filter_upwards [Ioo_mem_nhdsGT hlam0] with r ⟨hr0, hr⟩
  have hlr := (Real.log_neg hr0 (hr.trans hlam1)).ne
  rw [Real.norm_eq_abs, show Real.log 𝕭 / Real.log r - Real.log ρ / Real.log lam =
    (Real.log 𝕭 - Real.log ρ * (Real.log r / Real.log lam)) / Real.log r by field_simp, abs_div]
  refine div_le_div_of_nonneg_right ?_ (abs_nonneg _)
  obtain ⟨_ | n, hk1, hk2⟩ :=
    exists_nat_pow_near_of_lt_one hr0 (hr.le.trans hlam1.le) hlam0 hlam1
  · grind
  obtain ⟨h1, h2⟩ := h n r hk1 hk2
  have hρn := pow_pos hρ n
  have hl1 := Real.log_le_log (mul_pos ha hρn) h1
  have hl2 := Real.log_le_log ((mul_pos ha hρn).trans_le h1) h2
  have hr1 := Real.log_lt_log (pow_pos hlam0 _) hk1
  have hr2 := Real.log_le_log hr0 hk2
  rw [Real.log_mul ha.ne' hρn.ne'] at hl1
  rw [Real.log_mul hb.ne' hρn.ne'] at hl2
  simp at hl1 hl2 hr1 hr2
  have ht1 : n + 1 ≤ Real.log r / Real.log lam := by rw [le_div_iff_of_neg (by bound)]; linarith
  have ht2 : Real.log r / Real.log lam ≤ n + 2 := by rw [div_le_iff_of_neg (by bound)]; linarith
  have hB : |(n - Real.log r / Real.log lam) * Real.log ρ| ≤ 2 * |Real.log ρ| := by
    rw [abs_mul]
    gcongr
    grind
  grind

/-! ### The local dimension: the maps `f₁` and `f₂` of the example

The Lean letters `0, 1, 2` index the maps `f₁, f₂, f₃` of the paper. Words over the letters `0, 1`
are the words `w` with `i ≠ 2` for every letter `i` of `w`. -/
local notation "𝔬" => (1 / 8 : ℝ)


/-- For the letters `i = 0, 1` and real `x ≥ 0`, `f_i(x)` is real with
`x/8 ≤ f_i(x) ≤ x/8 + x²/32`, and `1/8 ≤ |f_i'(x)| ≤ 1/8 + x/16`. -/
theorem ld_f (hi : i ≠ 2) (hx : 0 ≤ x) :
    ∃ y : ℝ, exampleIFS.f i x = y ∧ x / 8 ≤ y ∧ y ≤ x / 8 + x ^ 2 / 32 ∧
      𝔬 ≤ ‖𝔡 exampleIFS i x‖ ∧ ‖𝔡 exampleIFS i x‖ ≤ 𝔬 + x / 16 := by
  obtain rfl | rfl | rfl := example_fin_three i
  · refine ⟨_, exampleMaps_zero_ofReal x, le_rfl, by nlinarith, ?_⟩
    simp [exampleIFS, deriv_exampleMaps_zero]
    positivity
  · refine ⟨_, exampleMaps_one_ofReal x, by nlinarith, le_rfl, ?_⟩
    simp only [exampleIFS, deriv_exampleMaps_one]
    rw [show (1 / 8 : ℂ) + x / 16 = ((1 / 8 + x / 16 : ℝ) : ℂ) by simp_all,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    grind
  · grind

/-- For words `w` over the letters `0, 1` and `x ∈ [0,1]`: `8^{-|w|} x ≤ f_w(x) ≤ 8^{-|w|} x (1 + x)`
and `8^{-|w|} ≤ |f_w'(x)| ≤ 8^{-|w|} (1 + x)`. -/
theorem ld_comp (hw : ∀ i ∈ w, i ≠ 2) (hx : x ∈ I) :
    𝔬 ^ w.length * x ≤ (exampleIFS.comp w x).re ∧
      (exampleIFS.comp w x).re ≤ 𝔬 ^ w.length * (x * 𝔲) ∧
      𝔬 ^ w.length ≤ ‖𝔡ᶜ exampleIFS w x‖ ∧
      ‖𝔡ᶜ exampleIFS w x‖ ≤ 𝔬 ^ w.length * 𝔲 := by
  induction w using List.reverseRecOn generalizing x with
  | nil => simp; constructor <;> nlinarith [hx.1]
  | append_singleton u i ih =>
    obtain ⟨hx0, hx1⟩ := hx
    obtain ⟨y, hy, h1, h2, h3, h4⟩ := ld_f (hw i (by simp)) hx0
    obtain ⟨h5, h6, h7, h8⟩ := ih (x := y) (fun j hj => hw j (by simp_all)) ⟨by linarith, by nlinarith⟩
    rw [exampleIFS.deriv_comp_append u [i] (subset_closure (ofReal_mem_nbhd (by norm_num) ⟨hx0, hx1⟩)),
      exampleIFS.comp_append, Function.comp_apply]
    simp only [IFS.comp_cons, IFS.comp_nil, Function.comp_id, hy, norm_mul, List.length_append,
      List.length_singleton, pow_succ]
    have hp : 0 < 𝔬 ^ u.length := by positivity
    have hx2 := mul_nonneg (mul_nonneg hx0 hx0) (sub_nonneg.2 hx1)
    have : y * (1 + y) ≤ 𝔬 * (x * 𝔲) := by
      nlinarith
    refine ⟨by nlinarith, by nlinarith, ?_, ?_⟩
    · nlinarith
    · have : (1 + y) * (𝔬 + x / 16) ≤ 𝔬 * 𝔲 := by nlinarith
      nlinarith

/-- `8^{-|w|} ≤ ‖f_w'‖ ≤ 2 ⋅ 8^{-|w|}` for words `w` over the letters `0, 1`. -/
theorem ld_supDeriv_bounds (hw : ∀ i ∈ w, i ≠ 2) :
    𝔬 ^ w.length ≤ exampleIFS.supDeriv w ∧
      exampleIFS.supDeriv w ≤ 2 * 𝔬 ^ w.length := by
  refine ⟨(ld_comp hw zero_mem_I).2.2.1.trans
    (exampleIFS.norm_deriv_le_supDeriv w zero_mem_I), ciSup_le fun x => (ld_comp hw x.2).2.2.2.trans ?_⟩
  nlinarith [x.2.2, pow_pos (by norm_num : 0 < 𝔬) w.length]

/-- If `y ≤ x ≤ 2y`, then `x^s` is comparable to `y^s` for every real `s`. -/
theorem ld_rpow_bounds (s : ℝ) (hy : 0 < y) (h1 : y ≤ x) (h2 : x ≤ 2 * y) :
    min 1 𝔤 * y ^ s ≤ x ^ s ∧ x ^ s ≤ max 1 𝔤 * y ^ s := by
  have h2y : (2 * y) ^ s = 2 ^ s * y ^ s := Real.mul_rpow (by norm_num) hy.le
  have := Real.rpow_nonneg hy.le s
  rcases le_total 0 s with hs | hs
  · have := Real.rpow_le_rpow hy.le h1 hs
    have := h2y ▸ Real.rpow_le_rpow (hy.le.trans h1) h2 hs
    constructor <;> nlinarith [min_le_left 1 ((2 : ℝ) ^ s), le_max_right 1 ((2 : ℝ) ^ s)]
  · have := Real.rpow_le_rpow_of_nonpos hy h1 hs
    have := h2y ▸ Real.rpow_le_rpow_of_nonpos (hy.trans_le h1) h2 hs
    constructor <;> nlinarith [min_le_right 1 ((2 : ℝ) ^ s), le_max_left 1 ((2 : ℝ) ^ s)]

/-! ### The local dimension: cylinders of words over the letters `0, 1` -/

/-- The words of length `n` over the letters `0, 1`. -/
def ldWords n : Finset (Fin n → Fin 3) := Fintype.piFinset fun _ => {0, 1}

theorem ld_mem_words : v ∈ ldWords n ↔ ∀ k, v k ≠ 2 := by
  rw [ldWords, Fintype.mem_piFinset]
  grind

/-- The Gibbs bounds summed over the words of length `n` over the letters `0, 1`. -/
theorem ld_sum_bounds {ν : Measure (ℕ → Fin 3)} (hC : 0 < C)
    (hG : ∀ w, C⁻¹ * exampleIFS.supDeriv w ^ s ≤ ν.real 𝖝 ∧
      ν.real 𝖝 ≤ C * exampleIFS.supDeriv w ^ s) (n : ℕ) :
    C⁻¹ * min 1 𝔤 * (2 * 𝔬 ^ s) ^ n ≤
        ∑ v ∈ ldWords n, ν.real 𝔣 ∧
      ∑ v ∈ ldWords n, ν.real 𝔣 ≤
        C * max 1 𝔤 * (2 * 𝔬 ^ s) ^ n := by
  have hterm : ∀ v ∈ ldWords n,
      C⁻¹ * min 1 𝔤 * (𝔬 ^ s) ^ n ≤ ν.real 𝔣 ∧
        ν.real 𝔣 ≤ C * max 1 𝔤 * (𝔬 ^ s) ^ n := by
    intro v hv
    obtain ⟨h1, h2⟩ := ld_supDeriv_bounds (List.forall_mem_ofFn_iff.2 (ld_mem_words.1 hv))
    rw [List.length_ofFn] at h1 h2
    obtain ⟨h3, h4⟩ := ld_rpow_bounds s (pow_pos (by norm_num) n) h1 h2
    rw [← Real.rpow_pow_comm (by norm_num)] at h3 h4
    have := inv_pos.2 hC
    constructor <;> nlinarith [hG 𝔧]
  have hs1 := Finset.sum_le_sum fun v hv => (hterm v hv).1
  have hs2 := Finset.sum_le_sum fun v hv => (hterm v hv).2
  rw [Finset.sum_const, nsmul_eq_mul] at hs1 hs2
  rw [mul_pow, show ((ldWords n).card : ℝ) = 2 ^ n by simp [ldWords]] at *
  grind

/-! ### The local dimension: the natural projection near `0` -/

/-- If the first `n` letters of `ω` are `0` or `1`, then `π(ω) ≤ 2 ⋅ 8^{-n}`. -/
theorem ld_natProj_le (h : (fun k : Fin n => ω k) ∈ ldWords n) :
    exampleIFS.natProj ω ≤ 2 * 𝔬 ^ n := by
  have hy := exampleIFS.attractor_subset_I ⟨fun j => ω (j + n), rfl⟩
  have := (ld_comp (List.forall_mem_ofFn_iff.2 (ld_mem_words.1 h)) hy).2.1
  rw [List.length_ofFn, ← exampleIFS.natProj_eq_comp_prefix] at this
  linarith [mul_le_mul_of_nonneg_left (mul_le_mul hy.2 (add_le_add_left hy.2 1) (by grind)
    zero_le_one) (pow_pos (by norm_num : 0 < 𝔬) n).le]

/-- If the letter of `ω` in position `k` (from `0`) is the first letter `2`, then
`π(ω) ≥ (29/32) 8^{-k}`. -/
theorem ld_le_natProj (hk : ω k = 2) (h : ∀ j < k, ω j ≠ 2) :
    29 / 32 * 𝔬 ^ k ≤ exampleIFS.natProj ω := by
  have h29 := exampleIFS.natProj_eq_comp_prefix (fun j => ω 𝔨) 1
  have := (ld_comp (List.forall_mem_ofFn_iff.2 fun j => h j j.2) (exampleIFS.attractor_subset_I ⟨fun j => ω 𝔨, rfl⟩)).1
  rw [List.length_ofFn, ← exampleIFS.natProj_eq_comp_prefix] at this
  refine (mul_comm _ _).trans_le (le_trans ?_ this)
  gcongr
  simp only [List.ofFn_succ, List.ofFn_zero, Fin.val_zero, zero_add, hk] at h29
  rw [h29, IFS.comp_cons, IFS.comp_nil, Function.comp_id, show exampleIFS.f 2 = exampleMaps 2 from rfl,
    exampleMaps_two_ofReal, Complex.ofReal_re]
  nlinarith [(exampleIFS.attractor_subset_I ⟨fun j => ω (j + 1 + k), rfl⟩).1]

/-- The natural measure of the polynomial example in Section 1.2.2: a measure `ν` with the Gibbs
property for the potential `s log|f'|` fixes `s = s(Φ)` as the unique zero of the pressure,
and the natural measure `μ = ν ∘ π⁻¹` has local dimension `s(Φ) - 1/3` at `0`. -/
theorem example_localDim {ν : Measure (ℕ → Fin 3)} [IsProbabilityMeasure ν]
    (hν : exampleIFS.IsGibbs s ν) :
    exampleIFS.PressureZero s ∧
    Tendsto (fun r => Real.log ((ν.map exampleIFS.natProj).real (closedBall 0 r)) / Real.log r)
      (𝓝[>] 0) (𝓝 (s - 1 / 3)) := by
  refine ⟨exampleIFS.tendsto_pressure_iff_of_isGibbs (by norm_num) hν, ?_⟩
  obtain ⟨C, hC, hG⟩ := hν
  set ρ : ℝ := 2 * 𝔬 ^ s with hρ_def
  have hρ : 0 < ρ := mul_pos two_pos (Real.rpow_pos_of_pos (by norm_num) s)
  have h2 := Real.log_pos one_lt_two
  have hd : s - 1 / 3 = Real.log ρ / Real.log 𝔬 := by
    rw [hρ_def, Real.log_mul two_ne_zero (Real.rpow_pos_of_pos (by norm_num) s).ne',
      Real.log_rpow (by norm_num), show 𝔬 = 2⁻¹ ^ 3 by norm_num, Real.log_pow,
      Real.log_inv]
    field_simp
    ring
  rw [hd]
  refine tendsto_log_div_log_of_bounds
    (m := fun r => (ν.map exampleIFS.natProj).real (closedBall 0 r)) (by norm_num) (by norm_num)
    hρ (mul_pos (mul_pos (inv_pos.2 hC) (lt_min one_pos (Real.rpow_pos_of_pos two_pos s)))
      (pow_pos hρ 3)) (mul_pos (mul_pos hC (lt_max_of_lt_left (c := 2 ^ s) one_pos)) hρ) fun n r hr1 hr2 => ?_
  rw [pow_add] at hr1
  rw [pow_succ] at hr2
  simp [map_measureReal_apply exampleIFS.measurable_natProj measurableSet_closedBall]
  constructor
  · -- the cylinders of the words of length `n + 3` over `0, 1` lie in `π⁻¹ B(0,r)`
    calc C⁻¹ * min 1 𝔤 * ρ ^ 3 * ρ ^ n = C⁻¹ * min 1 𝔤 * ρ ^ (n + 3) := by ring
      _ ≤ _ := (ld_sum_bounds hC hG (n + 3)).1
      _ ≤ _ := by
        rw [IFS.sum_measureReal_wordCylinder]
        refine measureReal_mono fun ω hω => ?_
        have := ld_natProj_le hω
        rw [pow_add] at this
        simp [abs_of_nonneg (exampleIFS.attractor_subset_I ⟨ω, rfl⟩).1]
        nlinarith
  · -- `π⁻¹ B(0,r)` lies in the cylinders of the words of length `n + 1` over `0, 1`
    refine le_trans ?_ ((ld_sum_bounds hC hG (n + 1)).2.trans_eq (by ring))
    rw [IFS.sum_measureReal_wordCylinder]
    refine measureReal_mono fun ω hω => ?_
    rw [mem_preimage, mem_closedBall, Real.dist_eq, sub_zero] at hω
    have key : ∀ k, k ≤ n → ω k ≠ 2 := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro hk h2
        have h1 := ld_le_natProj h2 fun j hj => ih j hj (hj.trans_le hk).le
        have h3 : 𝔬 ^ n ≤ 𝔬 ^ k :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
        nlinarith [le_abs_self (exampleIFS.natProj ω)]
    rw [mem_preimage, Finset.mem_coe, ld_mem_words]
    grind

end AnalyticESC
