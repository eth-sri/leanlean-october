module

public import AnalyticESC.Dual.Derivatives
public import AnalyticESC.Analysis

@[expose] public section

/-!
# Closeness estimates for the proof of Theorem 1.5

Section 3: if `f_{a u}` and `f_{b u}` are `η`-close on `I`, then `H_{a^←}` and `H_{b^←}` are close
on `f_u(I)` (the estimate (3.2)); and closeness of dual projections on an
interval of `I` passes to all their derivatives, as in (3.3).
-/

namespace AnalyticESC

open Set Metric Filter Topology

/-- A holomorphic map that is real at the real points of an open set has real iterated
derivatives there. -/
theorem im_iteratedDeriv_eq_zero {g : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V)
    (hg : DifferentiableOn ℂ g V) (hreal : ∀ t : ℝ, (t : ℂ) ∈ V → (g t).im = 0) (k : ℕ)
    {x : ℝ} (hx : (x : ℂ) ∈ V) : (iteratedDeriv k g x).im = 0 := by
  induction k generalizing x with
  | zero => simpa using hreal x hx
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact im_deriv_eq_zero hV (differentiableOn_iteratedDeriv_of_isOpen hV hg k)
      (fun _ ht => ih ht) hx

/-- (3.3) for two maps holomorphic on `B_ε` and real at its real points: Lemma 3.1 iterated
`k` times, applied to their real restrictions. -/
theorem norm_iteratedDeriv_sub_le_of_real {ε : ℝ} (hε : 0 < ε) {g h : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (nbhd ε)) (hh : DifferentiableOn ℂ h (nbhd ε))
    (hgr : ∀ t : ℝ, (t : ℂ) ∈ nbhd ε → (g t).im = 0)
    (hhr : ∀ t : ℝ, (t : ℂ) ∈ nbhd ε → (h t).im = 0) (k : ℕ) {p q η Q : ℝ} (hp : 0 ≤ p)
    (hq : q ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1) (hQ : 0 ≤ Q)
    (hgQ : ∀ j ≤ k + 1, ∀ x ∈ Icc p q, ‖iteratedDeriv j g x‖ ≤ Q)
    (hhQ : ∀ j ≤ k + 1, ∀ x ∈ Icc p q, ‖iteratedDeriv j h x‖ ≤ Q)
    (hJ : 2 * (2 + Q) * η ^ ((2 : ℝ)⁻¹ ^ k) < q - p)
    (hgh : ∀ x ∈ Icc p q, ‖g x - h x‖ ≤ η) :
    ∀ x ∈ Icc p q, ‖iteratedDeriv k g x - iteratedDeriv k h x‖ ≤
      (2 + Q) ^ 2 * η ^ ((2 : ℝ)⁻¹ ^ k) := by
  have hV := isOpen_nbhd ε
  have hU : IsOpen {t : ℝ | (t : ℂ) ∈ nbhd ε} := hV.preimage Complex.continuous_ofReal
  have hsub : ∀ x ∈ Icc p q, (x : ℂ) ∈ nbhd ε := fun x hx =>
    ofReal_mem_nbhd hε (Icc_subset_Icc hp hq hx)
  have hdg (j : ℕ) {x : ℝ} (hx : x ∈ Icc p q) :
      iteratedDeriv j (fun t : ℝ => (g t).re) x = (iteratedDeriv j g x).re :=
    iteratedDeriv_re_ofReal hV hg j (hsub x hx)
  have hdh (j : ℕ) {x : ℝ} (hx : x ∈ Icc p q) :
      iteratedDeriv j (fun t : ℝ => (h t).re) x = (iteratedDeriv j h x).re :=
    iteratedDeriv_re_ofReal hV hh j (hsub x hx)
  have key := abs_iteratedDeriv_sub_le k hU hsub (contDiffOn_re_ofReal hV hg)
    (contDiffOn_re_ofReal hV hh) hη hη1 hQ
    (fun j hj x hx => by
      rw [hdg j hx]; exact (Complex.abs_re_le_norm _).trans (hgQ j hj x hx))
    (fun j hj x hx => by
      rw [hdh j hx]; exact (Complex.abs_re_le_norm _).trans (hhQ j hj x hx))
    hJ (fun x hx => by
      rw [← Complex.sub_re]; exact (Complex.abs_re_le_norm _).trans (hgh x hx))
  intro x hx
  have him : (iteratedDeriv k g x - iteratedDeriv k h x).im = 0 := by
    rw [Complex.sub_im, im_iteratedDeriv_eq_zero hV hg hgr k (hsub x hx),
      im_iteratedDeriv_eq_zero hV hh hhr k (hsub x hx), sub_zero]
  rw [← Complex.abs_re_eq_norm.2 him, Complex.sub_re, ← hdg k hx, ← hdh k hx]
  exact key x hx

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-- A common bound on `I` for the derivatives of order at most `k` of all compositions,
obtained from Cauchy's estimate on `B_ε`. -/
theorem exists_iteratedDeriv_comp_bound (k : ℕ) :
    ∃ Q, 0 ≤ Q ∧ ∀ j ≤ k, ∀ w : List (Fin N), ∀ x ∈ I, ‖iteratedDeriv j (Φ.comp w) x‖ ≤ Q := by
  obtain ⟨R, hR0, hR⟩ := Φ.exists_comp_bound
  have hε := Φ.ε_pos
  let B (j : ℕ) : ℝ := j.factorial * R / (ε / 2) ^ j
  have hB0 (j : ℕ) : 0 ≤ B j := by dsimp [B]; positivity
  refine ⟨∑ j ∈ Finset.range (k + 1), B j, Finset.sum_nonneg fun j _ => hB0 j,
    fun j hj w x hx => ?_⟩
  exact (norm_iteratedDeriv_le_of_nbhd hε (Φ.differentiableOn_comp w)
    (fun z hz => hR w z (subset_closure hz)) j hx).trans
    (Finset.single_le_sum (fun i _ => hB0 i) (Finset.mem_range.2 (Nat.lt_succ_of_le hj)))

/-- The estimate (3.2): with `|a| = |b| ≥ 1` and different last letters, `η`-closeness of `f_{a u}`
and `f_{b u}` on `I` gives closeness `K c_min^{-2n} η^{1/4}` of `H_{a^←}` and `H_{b^←}` along
`f_u`, where `n = |a| + |u|`. -/
theorem exists_dualProj_closeness :
    ∃ K η₀ : ℝ, 0 < η₀ ∧ ∀ a b u : List (Fin N), a.length = b.length → 0 < a.length →
      a.getLast? ≠ b.getLast? → ∀ η : ℝ, 0 < η → η ≤ η₀ →
        (∀ x ∈ I, ‖Φ.comp (a ++ u) x - Φ.comp (b ++ u) x‖ ≤ η) →
          ∀ x ∈ I, ‖Φ.dualProj (.fin a.reverse) (Φ.comp u x) - Φ.dualProj (.fin b.reverse) (Φ.comp u x)‖
            ≤ K * Φ.cmin⁻¹ ^ (2 * (a.length + u.length)) * η ^ ((1 : ℝ) / 4) := by
  obtain ⟨Q, hQ0, hQ⟩ := Φ.exists_iteratedDeriv_comp_bound 3
  obtain ⟨M, hM0, hM, -⟩ := Φ.exists_dualProj_bounds
  set c : ℝ := 1 / (4 * (2 + Q)) with hc_def
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 := by rw [hc_def, div_le_one (by positivity)]; linarith
  refine ⟨(M + 1) * (2 + Q) ^ 2, c ^ 4, by positivity,
    fun a b u hab ha _ η hη hη0 hclose x hx => ?_⟩
  obtain ⟨i₀, -⟩ := List.exists_mem_of_length_pos ha
  have hN : 0 < N := i₀.pos
  have hcmin := Φ.cmin_pos hN
  have hcinv1 : 1 ≤ Φ.cmin⁻¹ := one_le_inv₀ hcmin |>.2 ((Φ.cmin_le_cmax hN).trans Φ.cmax_lt_one.le)
  have hη1 : η ≤ 1 := hη0.trans (pow_le_one₀ hc0.le hc1)
  have h14 : η ^ ((1 : ℝ) / 4) ≤ c :=
    (Real.rpow_le_rpow hη.le hη0 (by norm_num)).trans_eq
      (by rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num)
  have hcQ : 2 * (2 + Q) * c < 1 - 0 := by rw [hc_def]; field_simp; norm_num
  set i := a ++ u with hi
  set j := b ++ u with hj
  have hlen : j.length = i.length := by simp [i, j, hab]
  set E := (2 + Q) ^ 2 * η ^ ((1 : ℝ) / 4) with hE
  have hd (m : ℕ) (hm : m ≤ 2) :
      ‖iteratedDeriv m (Φ.comp i) x - iteratedDeriv m (Φ.comp j) x‖ ≤ E := by
    have hexp : η ^ ((2 : ℝ)⁻¹ ^ m) ≤ η ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow_of_exponent_ge hη hη1 (by
        rw [show (1 : ℝ) / 4 = (2 : ℝ)⁻¹ ^ 2 by norm_num]
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hm)
    exact (norm_iteratedDeriv_sub_le_of_real Φ.ε_pos (Φ.differentiableOn_comp i)
      (Φ.differentiableOn_comp j) (fun _ => Φ.im_comp_ofReal i) (fun _ => Φ.im_comp_ofReal j)
      m le_rfl le_rfl hη hη1 hQ0 (fun l hl => hQ l (by omega) i) (fun l hl => hQ l (by omega) j)
      ((mul_le_mul_of_nonneg_left (hexp.trans h14) (by positivity)).trans_lt hcQ)
      hclose x hx).trans (mul_le_mul_of_nonneg_left hexp (by positivity))
  have hxn : (x : ℂ) ∈ nbhd ε := ofReal_mem_nbhd Φ.ε_pos hx
  have hz : (x : ℂ) ∈ closure (nbhd ε) := subset_closure hxn
  set A := deriv (Φ.comp i) x
  set B := deriv (Φ.comp j) x
  set A2 := deriv (deriv (Φ.comp i)) x
  set B2 := deriv (deriv (Φ.comp j)) x
  have hA : A ≠ 0 := Φ.deriv_comp_ne_zero i hz
  have hB : B ≠ 0 := Φ.deriv_comp_ne_zero j hz
  have hBinv : ‖B‖⁻¹ ≤ Φ.cmin⁻¹ ^ i.length := by
    rw [inv_pow]; exact inv_anti₀ (pow_pos hcmin _) (hlen ▸ Φ.cmin_pow_le_norm_deriv_comp j hz)
  have hHi : Φ.dualProj (.fin i.reverse) x = A2 / A := Φ.dualProj_fin_reverse i hxn
  have hHj : Φ.dualProj (.fin j.reverse) x = B2 / B := Φ.dualProj_fin_reverse j hxn
  have hAM : ‖A2 / A‖ ≤ M := hHi ▸ hM _ _ hz
  have hAB : ‖B - A‖ ≤ E := by simpa [A, B, norm_sub_rev] using hd 1 (by omega)
  have hd2 : ‖A2 - B2‖ ≤ E := by
    simpa [A2, B2, iteratedDeriv_succ, iteratedDeriv_one] using hd 2 le_rfl
  have hdist : ‖A2 / A - B2 / B‖ ≤ (M + 1) * E * Φ.cmin⁻¹ ^ i.length := by
    rw [show A2 / A - B2 / B = (A2 / A * (B - A) + (A2 - B2)) / B by field_simp; ring,
      norm_div, div_eq_mul_inv]
    exact (mul_le_mul ((norm_add_le _ _).trans (add_le_add
      (norm_mul (A2 / A) _ ▸ mul_le_mul hAM hAB (norm_nonneg _) hM0) hd2)) hBinv
      (by positivity) (by positivity)).trans_eq (by ring)
  have hcoc (v : List (Fin N)) : Φ.dualProj (.fin (v ++ u).reverse) x =
      Φ.dualProj (.fin u.reverse) x +
        deriv (Φ.comp u) x * Φ.dualProj (.fin v.reverse) (Φ.comp u x) := by
    have := Φ.dualProj_prepend u.reverse (.fin v.reverse) hz
    rw [List.reverse_reverse] at this
    simpa [Word.prepend, List.reverse_append] using this
  have hdiff : A2 / A - B2 / B = deriv (Φ.comp u) x *
      (Φ.dualProj (.fin a.reverse) (Φ.comp u x) - Φ.dualProj (.fin b.reverse) (Φ.comp u x)) := by
    rw [← hHi, ← hHj, hi, hj, hcoc a, hcoc b]; ring
  have hu : Φ.cmin ^ u.length ≤ ‖deriv (Φ.comp u) x‖ := Φ.cmin_pow_le_norm_deriv_comp u hz
  have hu0 : 0 < ‖deriv (Φ.comp u) x‖ := (pow_pos hcmin _).trans_le hu
  have huinv : ‖deriv (Φ.comp u) x‖⁻¹ ≤ Φ.cmin⁻¹ ^ i.length :=
    (inv_pow Φ.cmin u.length ▸ inv_anti₀ (pow_pos hcmin _) hu).trans
      (pow_le_pow_right₀ hcinv1 (by simp [i]))
  rw [show ‖Φ.dualProj (.fin a.reverse) (Φ.comp u x) - Φ.dualProj (.fin b.reverse) (Φ.comp u x)‖ =
    ‖A2 / A - B2 / B‖ * ‖deriv (Φ.comp u) x‖⁻¹ by rw [hdiff, norm_mul]; field_simp]
  exact (mul_le_mul hdist huinv (by positivity) (by positivity)).trans_eq
    (by simp only [hE, i, List.length_append, two_mul, pow_add]; ring)

/-- (3.3) for dual projections: closeness `η` of `H_v` and `H_w` on `[p, q] ⊆ I` gives closeness
`K η^{2^{-k}}` of their `k`-th derivatives, provided the interval is long compared with
`η^{2^{-k}}`. -/
theorem exists_iteratedDeriv_dualProj_closeness (k : ℕ) :
    ∃ K Q : ℝ, 0 ≤ Q ∧ ∀ (v w : Word N) (p q η : ℝ), 0 ≤ p → q ≤ 1 → 0 < η → η ≤ 1 →
      2 * (2 + Q) * η ^ ((2 : ℝ)⁻¹ ^ k) < q - p →
      (∀ x ∈ Icc p q, ‖Φ.dualProj v x - Φ.dualProj w x‖ ≤ η) →
        ∀ x ∈ Icc p q, ‖iteratedDeriv k (Φ.dualProj v) x - iteratedDeriv k (Φ.dualProj w) x‖ ≤
          K * η ^ ((2 : ℝ)⁻¹ ^ k) := by
  obtain ⟨C, hC0, hC, -⟩ := Φ.exists_iteratedDeriv_bounds
  set Q := ∑ j ∈ Finset.range (k + 2), C j
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun j _ => hC0 j
  have hCQ : ∀ j ≤ k + 1, C j ≤ Q := fun j hj =>
    Finset.single_le_sum (fun i _ => hC0 i) (Finset.mem_range.2 (by omega))
  refine ⟨(2 + Q) ^ 2, Q, hQ0, fun v w p q η hp hq hη hη1 hJ hvw => ?_⟩
  exact norm_iteratedDeriv_sub_le_of_real Φ.ε_pos (Φ.differentiableOn_dualProj v)
    (Φ.differentiableOn_dualProj w) (fun t ht => Φ.im_dualProj_ofReal v ht)
    (fun t ht => Φ.im_dualProj_ofReal w ht) k hp hq hη hη1 hQ0
    (fun j hj x hx => (hC j x (Icc_subset_Icc hp hq hx) v).trans (hCQ j hj))
    (fun j hj x hx => (hC j x (Icc_subset_Icc hp hq hx) w).trans (hCQ j hj)) hJ hvw

end IFS

end AnalyticESC
