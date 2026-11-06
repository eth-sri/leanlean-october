module

public import AnalyticESC.Dual.Derivatives
public import AnalyticESC.Analysis

public section

set_option hygiene false
local notation "𝕳" => Φ.cmin⁻¹ ^ k
local notation "𝕲" => Φ.dualProj w
local notation "𝕱" => Φ.dualProj v
local notation "𝕰" => norm_nonneg _
local notation "𝕯" => M + 1
local notation "𝕮" => hsub x hx
local notation "𝕭" => nbhd ε
local notation "𝕬" => Icc_subset_Icc hp hq hx
local notation "𝔨" => Φ.comp u x

local notation "𝔧" => 2 + Q

/-!
# Closeness estimates for the proof of Theorem 1.5

Section 3: if `f_{a u}` and `f_{b u}` are `η`-close on `I`, then `H_{a^←}` and `H_{b^←}` are close
on `f_u(I)` (the estimate (3.2)); and closeness of dual projections on an
interval of `I` passes to all their derivatives, as in (3.3).
-/

namespace AnalyticESC

variable {V : Set ℂ} {g : ℂ → ℂ} {x η : ℝ}

open Set

/-- A complex number with zero imaginary part has norm the absolute value of its real part. -/
theorem norm_eq_abs_re_of_im_eq_zero {z : ℂ} (h : z.im = 0) : ‖z‖ = |z.re| := by
  conv_lhs => rw [← Complex.re_add_im z, h]
  simp

/-- Iterated derivatives of a map holomorphic on an open set are holomorphic there. -/
theorem differentiableOn_iteratedDeriv_of_isOpen (hV : IsOpen V)
    (hg : DifferentiableOn ℂ g V) k : DifferentiableOn ℂ (iteratedDeriv k g) V := by
  induction k with
  | zero => simpa using hg
  | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv hV

/-- A holomorphic map that is real at the real points of an open set has real iterated
derivatives there. -/
theorem im_iteratedDeriv_eq_zero (hV : IsOpen V)
    (hg : DifferentiableOn ℂ g V) (hreal : ∀ t : ℝ, (t : ℂ) ∈ V → (g t).im = 0) k
    (hx : (x : ℂ) ∈ V) : (iteratedDeriv k g x).im = 0 := by
  induction k generalizing x with
  | zero => simpa using hreal x hx
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact im_deriv_eq_zero hV (differentiableOn_iteratedDeriv_of_isOpen hV hg k)
      (fun t ht => ih ht) hx

local notation "𝔉" P => ∀ x ∈ Icc p q, P

/-- (3.3) for two maps holomorphic on `B_ε` and real at its real points: Lemma 3.1 iterated
`k` times, applied to their real restrictions. -/
theorem norm_iteratedDeriv_sub_le_of_real (hε : 0 < ε) {h : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g 𝕭) (hh : DifferentiableOn ℂ h 𝕭)
    (hgr : ∀ t : ℝ, (t : ℂ) ∈ nbhd ε → (g t).im = 0)
    (hhr : ∀ t : ℝ, (t : ℂ) ∈ nbhd ε → (h t).im = 0) k {p q Q : ℝ} (hp : 0 ≤ p)
    (hq : q ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1) (hQ : 0 ≤ Q)
    (hgQ : ∀ j ≤ k + 1, 𝔉 ‖iteratedDeriv j g x‖ ≤ Q)
    (hhQ : ∀ j ≤ k + 1, 𝔉 ‖iteratedDeriv j h x‖ ≤ Q)
    (hJ : 2 * 𝔧 * η ^ (2⁻¹ ^ k : ℝ) < q - p)
    (hgh : 𝔉 ‖g x - h x‖ ≤ η) :
    𝔉 ‖iteratedDeriv k g x - iteratedDeriv k h x‖ ≤
      𝔧 ^ 2 * η ^ (2⁻¹ ^ k : ℝ) := by
  have hsub : 𝔉 (x : ℂ) ∈ nbhd ε := fun x hx =>
    ofReal_mem_nbhd hε 𝕬
  have hd : ∀ {φ : ℂ → ℂ}, DifferentiableOn ℂ φ 𝕭 → ∀ j, ∀ x ∈ Icc p q,
      iteratedDeriv j (fun t : ℝ => (φ t).re) x = (iteratedDeriv j φ x).re :=
    fun hφ j x hx => iteratedDeriv_re_ofReal isOpen_nbhd hφ j 𝕮
  have hb : ∀ {φ : ℂ → ℂ}, DifferentiableOn ℂ φ 𝕭 →
      (∀ j ≤ k + 1, 𝔉 ‖iteratedDeriv j φ x‖ ≤ Q) →
        ∀ j ≤ k + 1, 𝔉 |iteratedDeriv j (fun t : ℝ => (φ t).re) x| ≤ Q :=
    fun hφ hQ j hj x hx => by rw [hd hφ j x hx]; exact (Complex.abs_re_le_norm _).trans (hQ j hj x hx)
  intro x hx
  rw [norm_eq_abs_re_of_im_eq_zero (by rw [Complex.sub_im, im_iteratedDeriv_eq_zero isOpen_nbhd hg
    hgr k 𝕮, im_iteratedDeriv_eq_zero isOpen_nbhd hh hhr k 𝕮, sub_zero]),
    Complex.sub_re, ← hd hg k x hx, ← hd hh k x hx]
  exact abs_iteratedDeriv_sub_le k (isOpen_nbhd.preimage Complex.continuous_ofReal) hsub
    (contDiffOn_re_ofReal isOpen_nbhd hg _) (contDiffOn_re_ofReal isOpen_nbhd hh _) hη hη1 hQ
    (hb hg hgQ) (hb hh hhQ) hJ (fun x hx => by
      rw [← Complex.sub_re]; exact (Complex.abs_re_le_norm _).trans (hgh x hx)) x hx

namespace IFS

variable (Φ : IFS N ε) (k : ℕ)

/-- Equation (2.9) and the polynomial bounds from Lemma 2.9 give
`|f_w^{(k+1)}| ≤ E_k c_max^{|w|}`. For `k = 1, 2` these are the second- and
third-derivative bounds used at the start of Section 3. -/
theorem exists_iteratedDeriv_comp_decay :
    ∃ E ≥ 0, ∀ w, Ɐ
      ‖iteratedDeriv (k + 1) (Φ.comp w) x‖ ≤ E * Φ.cmax ^ w.length := by
  obtain ⟨C, hC0, hC, -⟩ := Φ.exists_iteratedDeriv_bounds
  obtain ⟨E, hE0, hE⟩ := exists_norm_aeval_le_of_supported (gPoly_mem_supported k)
    C (fun ℓ _ => (hC0 ℓ).le)
  refine ⟨E, hE0, fun w x hx => ?_⟩
  have hz := ofReal_mem_nbhd Φ.ε_pos hx
  have heq := Φ.iteratedDeriv_succ_comp_reverse w.reverse k hz
  simp at heq
  rw [heq, norm_mul]
  calc _ ≤ Φ.cmax ^ w.length * E :=
      mul_le_mul (Φ.norm_deriv_comp_le w (subset_closure hz))
        (hE _ fun ℓ _ => hC ℓ x hx _) 𝕰 (pow_nonneg Φ.cmax_nonneg _)
    _ = _ := by linarith

/-- A common bound on `I` for the derivatives of order at most `k` of all compositions,
obtained from the polynomial identity and Lemma 2.9. -/
theorem exists_iteratedDeriv_comp_bound :
    ∃ Q, 0 ≤ Q ∧ ∀ j ≤ k, ∀ w : 𝔚 N, Ɐ ‖iteratedDeriv j (Φ.comp w) x‖ ≤ Q := by
  choose E hE0 hE using Φ.exists_iteratedDeriv_comp_decay
  have hS := Finset.sum_nonneg fun j (_ : j ∈ Finset.range k) => hE0 j
  refine ⟨1 + ∑ j ∈ Finset.range k, E j, by linarith, fun j hj w x hx => ?_⟩
  cases j with
  | zero => simpa using (Φ.norm_comp_ofReal_le_one w hx).trans (le_add_of_nonneg_right hS)
  | succ j =>
    linarith [hE j w x hx, Finset.single_le_sum (fun j _ => hE0 j) (Finset.mem_range.2 hj),
      mul_le_of_le_one_right (hE0 j) (pow_le_one₀ (n := w.length) Φ.cmax_nonneg Φ.cmax_lt_one.le)]

/-- The estimate (3.2): with `|a| = |b| ≥ 1` and different last letters, `η`-closeness of `f_{a u}`
and `f_{b u}` on `I` gives closeness `K c_min^{-2n} η^{1/4}` of `H_{a^←}` and `H_{b^←}` along
`f_u`, where `n = |a| + |u|`. -/
theorem exists_dualProj_closeness :
    ∃ K η₀ : ℝ, 0 < η₀ ∧ ∀ a b u : 𝔚 N, a.length = b.length → 0 < a.length →
      a.getLast? ≠ b.getLast? → ∀ η, 0 < η → η ≤ η₀ →
        (Ɐ ‖Φ.comp (a ++ u) x - Φ.comp (b ++ u) x‖ ≤ η) →
          Ɐ ‖Φ.dualProj (.fin a.reverse) 𝔨 - Φ.dualProj (.fin b.reverse) 𝔨‖
            ≤ K * Φ.cmin⁻¹ ^ (2 * (a.length + u.length)) * η ^ ((1 : ℝ) / 4) := by
  obtain ⟨Q, hQ0, hQ⟩ := Φ.exists_iteratedDeriv_comp_bound 3
  obtain ⟨M, hM0, hM⟩ := Φ.exists_norm_dualProj_le
  set c : ℝ := 1 / (4 * 𝔧) with hc_def
  have hc0 : 0 < c := by positivity
  refine ⟨𝕯 * 𝔧 ^ 2, c ^ 4, by positivity,
    fun a b u hab ha _ η hη hη0 hclose x hx => ?_⟩
  have hcmin := Φ.cmin_pos (a[0]'ha).pos
  have hη1 := hη0.trans (pow_le_one₀ hc0.le (by rw [hc_def, div_le_one (by positivity)]; linarith))
  have h14 : η ^ ((1 : ℝ) / 4) ≤ c := by
    calc η ^ (1 / 4) ≤ (c ^ 4) ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow hη.le hη0 (by norm_num)
      _ = c := by rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have hJ : ∀ r ≥ (1 : ℝ) / 4, 2 * 𝔧 * η ^ r < 1 - 0 := by
    intro r hr
    calc _ ≤ 2 * 𝔧 * c := by
          gcongr; exact (Real.rpow_le_rpow_of_exponent_ge hη hη1 hr).trans h14
      _ < 1 - 0 := by grind
  -- Closeness of first and second derivatives of `f_{a u}` and `f_{b u}`.
  set i := a ++ u with hi
  set j := b ++ u with hj
  have hlen : j.length = i.length := by grind
  have hd1 := norm_iteratedDeriv_sub_le_of_real Φ.ε_pos (Φ.differentiableOn_comp i)
    (Φ.differentiableOn_comp j) (fun _ => Φ.im_comp_ofReal i) (fun _ => Φ.im_comp_ofReal j) 1
    le_rfl le_rfl hη hη1 hQ0 (fun l hl => hQ l (by omega) i) (fun l hl => hQ l (by omega) j)
    (hJ _ (by norm_num)) hclose x hx
  have hd2 := norm_iteratedDeriv_sub_le_of_real Φ.ε_pos (Φ.differentiableOn_comp i)
    (Φ.differentiableOn_comp j) (fun _ => Φ.im_comp_ofReal i) (fun _ => Φ.im_comp_ofReal j) 2
    le_rfl le_rfl hη hη1 hQ0 (fun l hl => hQ l hl i) (fun l hl => hQ l hl j)
    (hJ _ (by norm_num)) hclose x hx
  rw [iteratedDeriv_one, iteratedDeriv_one] at hd1
  rw [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_succ, iteratedDeriv_one] at hd2
  -- The distortions `f_{a u}''/f_{a u}'` and `f_{b u}''/f_{b u}'` at `x`.
  have hz := Φ.ofReal_mem_cl hx
  have hinv : ∀ v, v.length ≤ i.length → ‖𝔡ᶜ Φ v x‖⁻¹ ≤ Φ.cmin⁻¹ ^ i.length :=
    fun v hv => by
      rw [inv_pow]
      exact inv_anti₀ (pow_pos hcmin _) ((pow_le_pow_of_le_one hcmin.le ((Φ.cmin_le_cmax (a[0]'ha).pos).trans Φ.cmax_lt_one.le) hv).trans
        (Φ.cmin_pow_le_norm_deriv_comp v hz))
  set A := 𝔡ᶜ Φ i x
  set B := 𝔡ᶜ Φ j x
  set A2 := 𝔇 (Φ.comp i) x
  set B2 := 𝔇 (Φ.comp j) x
  have hA := Φ.deriv_comp_ne_zero i hz
  have hB := Φ.deriv_comp_ne_zero j hz
  set E := 𝔧 ^ 2 * η ^ (2⁻¹ ^ 2 : ℝ) with hE
  have hAB : ‖B - A‖ ≤ E := by
    rw [norm_sub_rev]
    exact hd1.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hη hη1 (by norm_num)) (by positivity))
  have hdist : ‖A2 / A - B2 / B‖ ≤ 𝕯 * E * Φ.cmin⁻¹ ^ i.length := by
    rw [show A2 / A - B2 / B = (A2 / A * (B - A) + (A2 - B2)) / B by grind, norm_div,
      div_eq_mul_inv]
    exact (mul_le_mul ((norm_add_le _ _).trans (add_le_add ((norm_mul _ _).trans_le
      (mul_le_mul ((Φ.dualProj_fin_reverse i hz) ▸ hM _ _ hz) hAB 𝕰 hM0)) hd2)) (hinv j hlen.le)
      (by positivity) (by positivity)).trans_eq (by ring)
  -- The cocycle identity.
  have hcoc : ∀ v, Φ.dualProj (.fin (v ++ u).reverse) x =
      Φ.dualProj (.fin u.reverse) x +
        𝔡ᶜ Φ u x * Φ.dualProj (.fin v.reverse) 𝔨 := by
    intro v
    have := Φ.dualProj_prepend u.reverse (.fin v.reverse) hz
    simpa [Word.prepend] using this
  have hdiff : A2 / A - B2 / B = 𝔡ᶜ Φ u x *
      (Φ.dualProj (.fin a.reverse) 𝔨 - Φ.dualProj (.fin b.reverse) 𝔨) := by
    rw [← (Φ.dualProj_fin_reverse i hz), ← (Φ.dualProj_fin_reverse j hz), hi, hj, hcoc a, hcoc b]; ring
  rw [← mul_div_cancel_left₀ (_ - _) (Φ.deriv_comp_ne_zero u hz), ← hdiff, norm_div,
    div_eq_mul_inv]
  calc _ ≤ 𝕯 * E * Φ.cmin⁻¹ ^ i.length * Φ.cmin⁻¹ ^ i.length :=
        mul_le_mul hdist (hinv u (by simp_all)) (by positivity) (by positivity)
    _ = _ := by rw [hE, show i.length = a.length + u.length by simp_all, two_mul, pow_add]; norm_num; ring

/-- (3.3) for dual projections: closeness `η` of `H_v` and `H_w` on `[p, q] ⊆ I` gives closeness
`K η^{2^{-k}}` of their `k`-th derivatives, provided the interval is long compared with
`η^{2^{-k}}`. -/
theorem exists_iteratedDeriv_dualProj_closeness :
    ∃ K Q, 0 ≤ Q ∧ ∀ (v w : Word N) (p q η : ℝ), 0 ≤ p → p < q → q ≤ 1 → 0 < η → η ≤ 1 →
      2 * 𝔧 * η ^ (2⁻¹ ^ k : ℝ) < q - p →
      (𝔉 ‖Φ.dualProj v x - Φ.dualProj w x‖ ≤ η) →
        𝔉 ‖iteratedDeriv k 𝕱 x - iteratedDeriv k 𝕲 x‖ ≤
          K * η ^ (2⁻¹ ^ k : ℝ) := by
  obtain ⟨C, hCpos, hC, -⟩ := Φ.exists_iteratedDeriv_bounds
  set Q := ∑ j ∈ Finset.range (k + 2), C j
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun j _ => (hCpos j).le
  have hCQ : ∀ j ≤ k + 1, C j ≤ Q := fun j hj =>
    Finset.single_le_sum (fun i _ => (hCpos i).le) (Finset.mem_range.2 (by omega))
  refine ⟨𝔧 ^ 2, Q, hQ0, fun v w p q η hp _ hq hη hη1 hJ hvw => ?_⟩
  exact norm_iteratedDeriv_sub_le_of_real Φ.ε_pos (Φ.differentiableOn_dualProj v)
    (Φ.differentiableOn_dualProj w) (fun t ht => Φ.im_dualProj_ofReal v ht)
    (fun t ht => Φ.im_dualProj_ofReal w ht) k hp hq hη hη1 hQ0
    (fun j hj x hx => (hC j x 𝕬 v).trans (hCQ j hj))
    (fun j hj x hx => (hC j x 𝕬 w).trans (hCQ j hj)) hJ hvw

/-- The denominator in (3.3) is a norm, including for orientation-reversing words.
The interval estimate implies the displayed bound and its `c_min` bound. -/
theorem norm_iteratedDeriv_sub_le_on_image (hN : 0 < N) k u
    (hK : 0 ≤ K) (hη : 0 ≤ η)
    (hclose : ∀ y ∈ (fun t : ℝ => (Φ.comp u t).re) '' I,
      ‖iteratedDeriv k 𝕱 y - iteratedDeriv k 𝕲 y‖ ≤ K * η)
    (hx : x ∈ I) :
    ‖iteratedDeriv k 𝕱 𝔨 -
      iteratedDeriv k 𝕲 𝔨‖ ≤
        K / ‖𝔡ᶜ Φ u x‖ ^ k * η ∧
      K / ‖𝔡ᶜ Φ u x‖ ^ k * η ≤ K * 𝕳 ^ u.length * η := by
  have hx' := Φ.ofReal_mem_cl hx
  have hd1 : ‖𝔡ᶜ Φ u x‖ ^ k ≤ 1 :=
    pow_le_one₀ 𝕰 ((Φ.norm_deriv_comp_le u hx').trans
      (pow_le_one₀ Φ.cmax_nonneg Φ.cmax_lt_one.le))
  constructor
  · rw [Φ.comp_ofReal u hx]
    exact (hclose _ ⟨x, hx, rfl⟩).trans (mul_le_mul_of_nonneg_right
      ((le_div_iff₀ (pow_pos (norm_pos_iff.2 (Φ.deriv_comp_ne_zero u hx')) k)).2 (mul_le_of_le_one_right hK hd1)) hη)
  · have hc := Φ.cmin_pos hN
    have hlow := pow_le_pow_left₀ (pow_nonneg hc.le u.length) (Φ.cmin_pow_le_norm_deriv_comp u hx') k
    apply mul_le_mul_of_nonneg_right _ hη
    calc K / ‖𝔡ᶜ Φ u x‖ ^ k ≤ K / (Φ.cmin ^ u.length) ^ k := by bound
      _ = K * 𝕳 ^ u.length := by ring


end IFS

end AnalyticESC
