module

public import AnalyticESC.Main.Example
public import AnalyticESC.Separation

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

open Set Metric Filter Topology MeasureTheory

/-- The cylinder `[w] = {ω ∈ Σ : ω₁ ⋯ ω_{|w|} = w}` of a finite word. -/
def wordCylinder {N : ℕ} (w : List (Fin N)) : Set (ℕ → Fin N) :=
  {ω | ∀ k : Fin w.length, ω k = w[k]}

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-- `‖f_w'‖ = sup_{x ∈ [0,1]} |f_w'(x)|`. -/
noncomputable def supDeriv (w : List (Fin N)) : ℝ := ⨆ x : I, ‖deriv (Φ.comp w) x‖

/-- The sum `∑_{w ∈ Σ_n} ‖f_w'‖^t`, whose exponential growth rate is the pressure `P(t)`. -/
noncomputable def pressureSum (t : ℝ) (n : ℕ) : ℝ :=
  ∑ w : Fin n → Fin N, Φ.supDeriv (List.ofFn w) ^ t

/-- `ν` has the Gibbs property for the potential `s log|f'|`: `ν[w]` is comparable to `‖f_w'‖^s`,
uniformly over finite words `w`. -/
def IsGibbs (s : ℝ) (ν : Measure (ℕ → Fin N)) : Prop :=
  ∃ C > 0, ∀ w : List (Fin N),
    C⁻¹ * Φ.supDeriv w ^ s ≤ ν.real (wordCylinder w) ∧
      ν.real (wordCylinder w) ≤ C * Φ.supDeriv w ^ s

/-- The prefix map `ω ↦ ω₁ ⋯ ωₙ` is measurable. -/
private theorem measurable_prefix (n : ℕ) : Measurable fun (ω : ℕ → Fin N) (k : Fin n) => ω k :=
  Measurable.of_eval fun k => measurable_pi_apply (k : ℕ)

/-- The natural projection is measurable, so `ν ∘ π⁻¹` is the image measure of `ν`. -/
theorem measurable_natProj : Measurable Φ.natProj :=
  measurable_of_tendsto_metrizable
    (f := fun n ω => (Φ.comp (List.ofFn fun k : Fin n => ω k) 0).re)
    (fun n => (measurable_of_finite fun v : Fin n → Fin N => (Φ.comp (List.ofFn v) 0).re).comp
      (measurable_prefix n))
    (tendsto_pi_nhds.2 Φ.tendsto_natProj)

/-- The measure of the set of infinite words whose prefix of length `n` lies in `S` is the sum of
the measures of the cylinders of the words in `S`. -/
private theorem sum_measureReal_wordCylinder (ν : Measure (ℕ → Fin N)) [IsFiniteMeasure ν] (n : ℕ)
    (S : Finset (Fin n → Fin N)) :
    ∑ v ∈ S, ν.real (wordCylinder (List.ofFn v)) =
      ν.real ((fun (ω : ℕ → Fin N) (k : Fin n) => ω k) ⁻¹' ↑S) := by
  rw [← map_measureReal_apply (measurable_prefix n) .of_discrete, ← sum_measureReal_singleton]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_measureReal_apply (measurable_prefix n) .of_discrete]
  congr 1; ext ω; simp [wordCylinder, funext_iff, Fin.forall_iff]

/-- The cylinders of the words of length `n` have total measure `1`. -/
theorem sum_measureReal_wordCylinder_univ (ν : Measure (ℕ → Fin N))
    [IsProbabilityMeasure ν] (n : ℕ) :
    ∑ v : Fin n → Fin N, ν.real (wordCylinder (List.ofFn v)) = 1 := by
  rw [sum_measureReal_wordCylinder, Finset.coe_univ, preimage_univ, probReal_univ]

/-- `|f_w'(x)| ≤ ‖f_w'‖` for `x ∈ [0,1]`. -/
theorem norm_deriv_le_supDeriv (w : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    ‖deriv (Φ.comp w) x‖ ≤ Φ.supDeriv w :=
  le_ciSup (f := fun x : I => ‖deriv (Φ.comp w) ((x : ℝ) : ℂ)‖)
    ⟨Φ.cmax ^ w.length, by
      rintro _ ⟨y, rfl⟩
      exact Φ.norm_deriv_comp_le w (subset_closure (ofReal_mem_nbhd Φ.ε_pos y.2))⟩
    ⟨x, hx⟩

/-- `‖f_w'‖ ≤ c_max^{|w|}`. -/
theorem supDeriv_le (w : List (Fin N)) : Φ.supDeriv w ≤ Φ.cmax ^ w.length := by
  have : Nonempty I := ⟨⟨0, le_rfl, zero_le_one⟩⟩
  exact ciSup_le fun x => Φ.norm_deriv_comp_le w (subset_closure (ofReal_mem_nbhd Φ.ε_pos x.2))

/-- `c_min^{|w|} ≤ ‖f_w'‖`. -/
theorem cmin_pow_le_supDeriv (w : List (Fin N)) : Φ.cmin ^ w.length ≤ Φ.supDeriv w :=
  (Φ.cmin_pow_le_norm_deriv_comp w
    (subset_closure (ofReal_mem_nbhd Φ.ε_pos (left_mem_Icc.2 zero_le_one)))).trans
    (Φ.norm_deriv_le_supDeriv w (left_mem_Icc.2 zero_le_one))

end IFS

/-! ### The local dimension: an analytic lemma -/

/-- If `a ρ^n ≤ m(r) ≤ b ρ^n` whenever `λ^{n+2} < r ≤ λ^{n+1}`, then
`log m(r) / log r → log ρ / log λ` as `r → 0⁺`. -/
private theorem tendsto_log_div_log_of_bounds {m : ℝ → ℝ} {lam ρ a b : ℝ} (hlam0 : 0 < lam)
    (hlam1 : lam < 1) (hρ : 0 < ρ) (ha : 0 < a) (hb : 0 < b)
    (h : ∀ (n : ℕ) (r : ℝ), lam ^ (n + 2) < r → r ≤ lam ^ (n + 1) →
      a * ρ ^ n ≤ m r ∧ m r ≤ b * ρ ^ n) :
    Tendsto (fun r => Real.log (m r) / Real.log r) (𝓝[>] 0)
      (𝓝 (Real.log ρ / Real.log lam)) := by
  set d := Real.log ρ / Real.log lam
  set K := |Real.log a| + |Real.log b| + 2 * |Real.log ρ|
  have hL : Real.log lam < 0 := Real.log_neg hlam0 hlam1
  have hbound (r : ℝ) (hr0 : 0 < r) (hr : r < lam) : |Real.log (m r) - d * Real.log r| ≤ K := by
    obtain ⟨_ | n, hk1, hk2⟩ :=
      exists_nat_pow_near_of_lt_one hr0 (hr.le.trans hlam1.le) hlam0 hlam1
    · rw [zero_add, pow_one] at hk1; linarith
    obtain ⟨h1, h2⟩ := h n r hk1 hk2
    have hρn := pow_pos hρ n
    have hl1 := Real.log_le_log (mul_pos ha hρn) h1
    have hl2 := Real.log_le_log ((mul_pos ha hρn).trans_le h1) h2
    rw [Real.log_mul ha.ne' hρn.ne', Real.log_pow] at hl1
    rw [Real.log_mul hb.ne' hρn.ne', Real.log_pow] at hl2
    have hr1 := Real.log_lt_log (pow_pos hlam0 _) hk1
    have hr2 := Real.log_le_log hr0 hk2
    rw [Real.log_pow] at hr1 hr2; push_cast at hr1 hr2
    set t := Real.log r / Real.log lam
    have ht1 : n + 1 ≤ t := (le_div_iff_of_neg hL).2 (by linarith)
    have ht2 : t ≤ n + 2 := (div_le_iff_of_neg hL).2 (by linarith)
    have hB : |(n - t) * Real.log ρ| ≤ 2 * |Real.log ρ| := by
      rw [abs_mul]; gcongr; rw [abs_le]; constructor <;> linarith
    rw [show d * Real.log r = Real.log ρ * t by simp only [d, t]; ring,
      show Real.log (m r) - Real.log ρ * t =
        (Real.log (m r) - n * Real.log ρ) + (n - t) * Real.log ρ by ring, abs_le]
    constructor <;> linarith [neg_abs_le (Real.log a), le_abs_self (Real.log b),
      abs_nonneg (Real.log a), abs_nonneg (Real.log b),
      neg_abs_le ((n - t) * Real.log ρ), le_abs_self ((n - t) * Real.log ρ)]
  have hK : Tendsto (fun r => K / |Real.log r|) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_abs_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hK
  filter_upwards [Ioo_mem_nhdsGT hlam0] with r hr
  have hlr : Real.log r ≠ 0 := (Real.log_neg hr.1 (hr.2.trans hlam1)).ne
  rw [Real.norm_eq_abs, show Real.log (m r) / Real.log r - d =
    (Real.log (m r) - d * Real.log r) / Real.log r by field_simp, abs_div]
  exact div_le_div_of_nonneg_right (hbound r hr.1 hr.2) (abs_nonneg _)

/-! ### The local dimension: the maps `f₁` and `f₂` of the example -/

private theorem ld_fin_three (i : Fin 3) (hi : i ≠ 2) : i = 0 ∨ i = 1 := by
  revert i; decide

/-- For the letters `i = 0, 1` and real `x`, `f_i(x)` is real with
`x/8 ≤ f_i(x) ≤ x/8 + x²/32`. -/
private theorem ld_f_ofReal (i : Fin 3) (hi : i ≠ 2) (x : ℝ) :
    ∃ y : ℝ, exampleIFS.f i x = y ∧ x / 8 ≤ y ∧ y ≤ x / 8 + x ^ 2 / 32 := by
  rcases ld_fin_three i hi with rfl | rfl
  · exact ⟨x / 8, exampleMaps_zero_ofReal x, le_rfl, by linarith [sq_nonneg x]⟩
  · exact ⟨x / 8 + x ^ 2 / 32, exampleMaps_one_ofReal x, by linarith [sq_nonneg x], le_rfl⟩

private theorem ld_norm_deriv_f_le (i : Fin 3) (hi : i ≠ 2) {x : ℝ} (hx : 0 ≤ x) :
    ‖deriv (exampleIFS.f i) x‖ ≤ 1 / 8 + x / 16 := by
  change ‖deriv (exampleMaps i) x‖ ≤ 1 / 8 + x / 16
  rcases ld_fin_three i hi with rfl | rfl
  · rw [congrFun deriv_exampleMaps_zero _]; norm_num; positivity
  · rw [congrFun deriv_exampleMaps_one _, show (1 / 8 : ℂ) + (x : ℂ) / 16 = ((1 / 8 + x / 16 : ℝ) : ℂ)
      by push_cast; ring, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

/-! ### The local dimension: compositions of `f₁` and `f₂` -/

private theorem ld_comp_and_deriv_zero {w : List (Fin 3)} (hw : ∀ i ∈ w, i ≠ 2) :
    exampleIFS.comp w 0 = 0 ∧ deriv (exampleIFS.comp w) 0 = (1 / 8 : ℂ) ^ w.length := by
  induction w with
  | nil => simp [deriv_id]
  | cons i w ih =>
    obtain ⟨ih0, ihd⟩ := ih fun j hj => hw j (List.mem_cons_of_mem i hj)
    rw [exampleIFS.deriv_comp_cons i w (zero_mem_closure_nbhd (by norm_num)),
      IFS.comp_cons, Function.comp_apply, ih0, ihd, List.length_cons, pow_succ']
    rcases ld_fin_three i (hw i List.mem_cons_self) with rfl | rfl
    · exact ⟨by change (0 : ℂ) / 8 = 0; norm_num,
        by rw [show deriv (exampleIFS.f 0) = _ from deriv_exampleMaps_zero]⟩
    · exact ⟨by change (0 : ℂ) / 8 + 0 ^ 2 / 32 = 0; norm_num,
        by rw [show deriv (exampleIFS.f 1) = _ from deriv_exampleMaps_one]; norm_num⟩

/-- `8^{-|w|} x ≤ f_w(x)` for words `w` over the letters `0, 1` and `x ∈ [0,1]`. -/
private theorem ld_le_re_comp {w : List (Fin 3)} (hw : ∀ i ∈ w, i ≠ 2) {x : ℝ} (hx : x ∈ I) :
    (1 / 8 : ℝ) ^ w.length * x ≤ (exampleIFS.comp w x).re := by
  induction w with
  | nil => simp
  | cons i w ih =>
    have hw' : ∀ j ∈ w, j ≠ 2 := fun j hj => hw j (List.mem_cons_of_mem i hj)
    obtain ⟨y, hy', h1, -⟩ := ld_f_ofReal i (hw i List.mem_cons_self) _
    have := ih hw'
    rw [IFS.comp_cons, Function.comp_apply, exampleIFS.comp_ofReal w hx, hy', Complex.ofReal_re,
      List.length_cons, pow_succ]
    nlinarith

/-- `f_w(x) ≤ 8^{-|w|} x (1 + x)` and `|f_w'(x)| ≤ 8^{-|w|} (1 + x)` for words `w` over `0, 1`
and `x ∈ [0,1]`. -/
private theorem ld_comp_and_deriv_le {w : List (Fin 3)} (hw : ∀ i ∈ w, i ≠ 2) {x : ℝ}
    (hx : x ∈ I) :
    (exampleIFS.comp w x).re ≤ (1 / 8 : ℝ) ^ w.length * (x * (1 + x)) ∧
      ‖deriv (exampleIFS.comp w) x‖ ≤ (1 / 8 : ℝ) ^ w.length * (1 + x) := by
  induction w using List.reverseRecOn generalizing x with
  | nil =>
    simp only [IFS.comp_nil, id, Complex.ofReal_re, deriv_id, norm_one, List.length_nil, pow_zero,
      one_mul]
    exact ⟨by nlinarith [hx.1], by linarith [hx.1]⟩
  | append_singleton u i ih =>
    have hu : ∀ j ∈ u, j ≠ 2 := fun j hj => hw j (List.mem_append_left _ hj)
    have hi : i ≠ 2 := hw i (List.mem_append_right _ (List.mem_singleton_self i))
    have hz : (x : ℂ) ∈ closure (nbhd (1 / 100)) :=
      subset_closure (ofReal_mem_nbhd (by norm_num) hx)
    obtain ⟨hx0, hx1⟩ := hx
    obtain ⟨y, hy, h1, h2⟩ := ld_f_ofReal i hi x
    have hc : exampleIFS.comp [i] = exampleIFS.f i := rfl
    obtain ⟨ih1, ih2⟩ := ih hu ⟨by linarith, by nlinarith⟩
    refine ⟨?_, ?_⟩
    · rw [exampleIFS.comp_append, Function.comp_apply, hc, hy, List.length_append,
        List.length_singleton, pow_succ]
      have hyy : y * (1 + y) ≤ 1 / 8 * (x * (1 + x)) := by
        have : y * (1 + y) ≤ (x / 8 + x ^ 2 / 32) * (1 + x / 4) :=
          mul_le_mul h2 (by nlinarith) (by linarith) (by positivity)
        nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.2 hx1)]
      exact ih1.trans ((mul_le_mul_of_nonneg_left hyy (by positivity)).trans_eq (by ring))
    · rw [exampleIFS.deriv_comp_append u [i] hz, hc, hy, norm_mul, List.length_append,
        List.length_singleton, pow_succ]
      have h5 : (1 + y) * ‖deriv (exampleIFS.f i) x‖ ≤ 1 / 8 * (1 + x) := by
        have : (1 + y) * ‖deriv (exampleIFS.f i) x‖ ≤
            (1 + (x / 8 + x ^ 2 / 32)) * (1 / 8 + x / 16) :=
          mul_le_mul (by linarith) (ld_norm_deriv_f_le i hi hx0) (norm_nonneg _) (by positivity)
        nlinarith
      exact ((mul_le_mul_of_nonneg_right ih2 (norm_nonneg _)).trans_eq (mul_assoc _ _ _)).trans
        ((mul_le_mul_of_nonneg_left h5 (by positivity)).trans_eq (by ring))

/-- `8^{-|w|} ≤ ‖f_w'‖ ≤ 2 ⋅ 8^{-|w|}` for words `w` over the letters `0, 1`. -/
private theorem ld_supDeriv_bounds {w : List (Fin 3)} (hw : ∀ i ∈ w, i ≠ 2) :
    (1 / 8 : ℝ) ^ w.length ≤ exampleIFS.supDeriv w ∧
      exampleIFS.supDeriv w ≤ 2 * (1 / 8 : ℝ) ^ w.length := by
  constructor
  · have h := exampleIFS.norm_deriv_le_supDeriv w (x := 0) (left_mem_Icc.2 zero_le_one)
    rwa [Complex.ofReal_zero, (ld_comp_and_deriv_zero hw).2, norm_pow, norm_div, norm_one,
      Complex.norm_ofNat] at h
  · have : Nonempty I := ⟨⟨0, le_rfl, zero_le_one⟩⟩
    refine ciSup_le fun x => ((ld_comp_and_deriv_le hw x.2).2).trans ?_
    have hpow : (0 : ℝ) ≤ (1 / 8) ^ w.length := by positivity
    nlinarith [x.2.2]

/-- If `y ≤ x ≤ 2y`, then `x^s` is comparable to `y^s` for every real `s`. -/
private theorem ld_rpow_bounds {x y : ℝ} (s : ℝ) (hy : 0 < y) (h1 : y ≤ x) (h2 : x ≤ 2 * y) :
    min 1 (2 ^ s) * y ^ s ≤ x ^ s ∧ x ^ s ≤ max 1 (2 ^ s) * y ^ s := by
  have hx : 0 < x := hy.trans_le h1
  have h2y : (2 * y) ^ s = 2 ^ s * y ^ s := Real.mul_rpow (by norm_num) hy.le
  have hys := Real.rpow_nonneg hy.le s
  rcases le_total 0 s with hs | hs
  · exact ⟨(mul_le_of_le_one_left hys (min_le_left _ _)).trans (Real.rpow_le_rpow hy.le h1 hs),
      (Real.rpow_le_rpow hx.le h2 hs).trans
        (h2y ▸ mul_le_mul_of_nonneg_right (le_max_right _ _) hys)⟩
  · exact ⟨(mul_le_mul_of_nonneg_right (min_le_right _ _) hys).trans
        (h2y ▸ Real.rpow_le_rpow_of_nonpos hx h2 hs),
      (Real.rpow_le_rpow_of_nonpos hy h1 hs).trans (le_mul_of_one_le_left hys (le_max_left _ _))⟩

/-! ### The local dimension: cylinders of words over the letters `0, 1` -/

/-- The words of length `n` over the letters `0, 1`. -/
def ldWords (n : ℕ) : Finset (Fin n → Fin 3) := Fintype.piFinset fun _ => {0, 1}

theorem ld_mem_words {n : ℕ} {v : Fin n → Fin 3} : v ∈ ldWords n ↔ ∀ k, v k ≠ 2 := by
  rw [ldWords, Fintype.mem_piFinset]
  refine forall_congr' fun k => ?_
  generalize v k = i; revert i; decide

private theorem ld_ofFn_ne_two {n : ℕ} {v : Fin n → Fin 3} (hv : v ∈ ldWords n) :
    ∀ i ∈ List.ofFn v, i ≠ 2 := by
  intro i hi
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hi
  exact ld_mem_words.1 hv k

/-- The Gibbs bounds summed over the words of length `n` over the letters `0, 1`. -/
private theorem ld_sum_bounds {s C : ℝ} {ν : Measure (ℕ → Fin 3)} (hC : 0 < C)
    (hG : ∀ w : List (Fin 3), C⁻¹ * exampleIFS.supDeriv w ^ s ≤ ν.real (wordCylinder w) ∧
      ν.real (wordCylinder w) ≤ C * exampleIFS.supDeriv w ^ s) (n : ℕ) :
    C⁻¹ * min 1 (2 ^ s) * (2 * (1 / 8 : ℝ) ^ s) ^ n ≤
        ∑ v ∈ ldWords n, ν.real (wordCylinder (List.ofFn v)) ∧
      ∑ v ∈ ldWords n, ν.real (wordCylinder (List.ofFn v)) ≤
        C * max 1 (2 ^ s) * (2 * (1 / 8 : ℝ) ^ s) ^ n := by
  have hterm : ∀ v ∈ ldWords n,
      C⁻¹ * (min 1 (2 ^ s) * ((1 / 8 : ℝ) ^ s) ^ n) ≤ ν.real (wordCylinder (List.ofFn v)) ∧
        ν.real (wordCylinder (List.ofFn v)) ≤ C * (max 1 (2 ^ s) * ((1 / 8 : ℝ) ^ s) ^ n) := by
    intro v hv
    obtain ⟨h1, h2⟩ := ld_supDeriv_bounds (ld_ofFn_ne_two hv)
    rw [List.length_ofFn] at h1 h2
    obtain ⟨h3, h4⟩ := ld_rpow_bounds s (pow_pos (by norm_num) n) h1 h2
    rw [← Real.rpow_pow_comm (by norm_num)] at h3 h4
    exact ⟨(mul_le_mul_of_nonneg_left h3 (inv_pos.2 hC).le).trans (hG _).1,
      (hG _).2.trans (mul_le_mul_of_nonneg_left h4 hC.le)⟩
  have hs1 := Finset.sum_le_sum fun v hv => (hterm v hv).1
  have hs2 := Finset.sum_le_sum fun v hv => (hterm v hv).2
  have hcard : (ldWords n).card = 2 ^ n := by
    rw [ldWords, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]; rfl
  rw [Finset.sum_const, hcard, nsmul_eq_mul] at hs1 hs2
  push_cast at hs1 hs2
  exact ⟨(by rw [mul_pow]; ring : C⁻¹ * _ * _ = _).trans_le hs1,
    hs2.trans_eq (by rw [mul_pow]; ring)⟩

/-! ### The local dimension: the natural projection near `0` -/

/-- If the first `n` letters of `ω` are `0` or `1`, then `π(ω) ≤ 2 ⋅ 8^{-n}`. -/
theorem ld_natProj_le {n : ℕ} {ω : ℕ → Fin 3} (h : (fun k : Fin n => ω k) ∈ ldWords n) :
    exampleIFS.natProj ω ≤ 2 * (1 / 8 : ℝ) ^ n := by
  have hy := exampleIFS.attractor_subset_I ⟨fun j => ω (j + n), rfl⟩
  rw [exampleIFS.natProj_eq_comp_prefix ω n]
  refine ((ld_comp_and_deriv_le (ld_ofFn_ne_two h) hy).1).trans ?_
  rw [List.length_ofFn]
  have hpow : (0 : ℝ) ≤ (1 / 8) ^ n := by positivity
  have : exampleIFS.natProj (fun j => ω (j + n)) * (1 + exampleIFS.natProj (fun j => ω (j + n)))
      ≤ 2 := by nlinarith [hy.1, hy.2]
  nlinarith

/-- If the letter of `ω` in position `k` (from `0`) is the first letter `2`, then
`π(ω) ≥ (29/32) 8^{-k}`. -/
private theorem ld_le_natProj {k : ℕ} {ω : ℕ → Fin 3} (hk : ω k = 2) (h : ∀ j < k, ω j ≠ 2) :
    29 / 32 * (1 / 8 : ℝ) ^ k ≤ exampleIFS.natProj ω := by
  have hw : ∀ i ∈ List.ofFn (fun j : Fin k => ω j), i ≠ 2 := by
    intro i hi; obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hi; exact h j j.2
  set σ : ℕ → Fin 3 := fun j => ω (j + k)
  have h29 : 29 / 32 ≤ exampleIFS.natProj σ := by
    rw [exampleIFS.natProj_eq_realMap σ, show σ 0 = 2 by simpa [σ] using hk, IFS.realMap,
      show exampleIFS.f 2 = exampleMaps 2 from rfl, exampleMaps_two_ofReal, Complex.ofReal_re]
    nlinarith [(exampleIFS.attractor_subset_I ⟨fun j => σ (j + 1), rfl⟩).1]
  rw [exampleIFS.natProj_eq_comp_prefix ω k]
  refine le_trans ?_ (ld_le_re_comp hw (exampleIFS.attractor_subset_I ⟨σ, rfl⟩))
  rw [List.length_ofFn]
  have : (0 : ℝ) ≤ (1 / 8) ^ k := by positivity
  nlinarith

/-- The natural measure of the polynomial example in Section 1.2.2: for a measure `ν` with the Gibbs
property for the potential `s log|f'|`, the natural measure `μ = ν ∘ π⁻¹` has local dimension
`s - 1/3` at `0`. -/
theorem example_localDim {s : ℝ} {ν : Measure (ℕ → Fin 3)} [IsProbabilityMeasure ν]
    (hν : exampleIFS.IsGibbs s ν) :
    Tendsto (fun r => Real.log ((ν.map exampleIFS.natProj).real (closedBall 0 r)) / Real.log r)
      (𝓝[>] 0) (𝓝 (s - 1 / 3)) := by
  obtain ⟨C, hC, hG⟩ := hν
  set ρ : ℝ := 2 * (1 / 8 : ℝ) ^ s with hρ_def
  have hρ : 0 < ρ := mul_pos two_pos (Real.rpow_pos_of_pos (by norm_num) s)
  have hmin : 0 < min 1 ((2 : ℝ) ^ s) := lt_min one_pos (Real.rpow_pos_of_pos two_pos s)
  have hmax : 0 < max 1 ((2 : ℝ) ^ s) := lt_max_of_lt_left one_pos
  have hμ (r : ℝ) : (ν.map exampleIFS.natProj).real (closedBall 0 r) =
      ν.real (exampleIFS.natProj ⁻¹' closedBall 0 r) :=
    map_measureReal_apply exampleIFS.measurable_natProj measurableSet_closedBall
  have hlow (n : ℕ) : C⁻¹ * min 1 (2 ^ s) * ρ ^ n ≤
      ν.real (exampleIFS.natProj ⁻¹' closedBall 0 (2 * (1 / 8 : ℝ) ^ n)) := by
    refine (ld_sum_bounds hC hG n).1.trans ?_
    rw [IFS.sum_measureReal_wordCylinder]
    refine measureReal_mono fun ω hω => ?_
    rw [mem_preimage, mem_closedBall, Real.dist_eq, sub_zero,
      abs_of_nonneg (exampleIFS.attractor_subset_I ⟨ω, rfl⟩).1]
    exact ld_natProj_le hω
  have hup (n : ℕ) (r : ℝ) (hr : r < 29 / 32 * (1 / 8 : ℝ) ^ n) :
      ν.real (exampleIFS.natProj ⁻¹' closedBall 0 r) ≤ C * max 1 (2 ^ s) * ρ ^ (n + 1) := by
    refine le_trans ?_ (ld_sum_bounds hC hG (n + 1)).2
    rw [IFS.sum_measureReal_wordCylinder]
    refine measureReal_mono fun ω hω => ?_
    rw [mem_preimage, mem_closedBall, Real.dist_eq, sub_zero] at hω
    have hle : exampleIFS.natProj ω ≤ r := (le_abs_self _).trans hω
    have key : ∀ k, k ≤ n → ω k ≠ 2 := fun k => by
      induction k using Nat.strong_induction_on with | _ k ih =>
      intro hk h2
      have h1 := ld_le_natProj h2 fun j hj => ih j hj (hj.trans_le hk).le
      have h3 : (1 / 8 : ℝ) ^ n ≤ (1 / 8) ^ k :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
      linarith
    rw [mem_preimage, Finset.mem_coe, ld_mem_words]
    exact fun k => key k (Nat.lt_succ_iff.1 k.2)
  have hd : s - 1 / 3 = Real.log ρ / Real.log (1 / 8) := by
    have h2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    rw [hρ_def, Real.log_mul two_ne_zero (Real.rpow_pos_of_pos (by norm_num) s).ne',
      Real.log_rpow (by norm_num), show Real.log (1 / 8) = -(3 * Real.log 2) by
        rw [one_div, Real.log_inv, show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring]
    field_simp; ring
  rw [hd]
  refine tendsto_log_div_log_of_bounds
    (m := fun r => (ν.map exampleIFS.natProj).real (closedBall 0 r)) (by norm_num) (by norm_num)
    hρ (mul_pos (mul_pos (inv_pos.2 hC) hmin) (pow_pos hρ 3)) (mul_pos (mul_pos hC hmax) hρ) ?_
  intro n r hr1 hr2
  have hpow : (0 : ℝ) < (1 / 8) ^ n := by positivity
  rw [hμ]
  refine ⟨?_, (hup n r (by rw [pow_succ] at hr2; nlinarith)).trans_eq (by ring)⟩
  have hr : 2 * (1 / 8 : ℝ) ^ (n + 3) ≤ r := by
    rw [pow_add]; rw [pow_add] at hr1; nlinarith
  exact (by ring : C⁻¹ * min 1 (2 ^ s) * ρ ^ 3 * ρ ^ n =
    C⁻¹ * min 1 (2 ^ s) * ρ ^ (n + 3)).trans_le
    ((hlow (n + 3)).trans (measureReal_mono (preimage_mono (closedBall_subset_closedBall hr))))

end AnalyticESC
