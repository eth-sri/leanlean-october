module

public import AnalyticESC.Dual.Projection

@[expose] public section

namespace AnalyticESC

open Set Metric

theorem sum_mul_bounds {α : Type*} (S : Finset α) {f g : α → ℝ} {a b : ℝ}
    (h : ∀ i ∈ S, a * f i ≤ g i ∧ g i ≤ b * f i) :
    a * ∑ i ∈ S, f i ≤ ∑ i ∈ S, g i ∧ (∑ i ∈ S, g i) ≤ b * ∑ i ∈ S, f i := by
  simp_all [Finset.mul_sum, Finset.sum_le_sum]

theorem log_sub_mem_Icc_of_mul_bounds {x y a b : ℝ} (hy : 0 < y) (ha : 0 < a) (hb : 0 < b)
    (h : a * y ≤ x ∧ x ≤ b * y) : Real.log x - Real.log y ∈ Icc (Real.log a) (Real.log b) := by
  have hl := Real.log_le_log (mul_pos ha hy) h.1
  have hu := Real.log_le_log ((mul_pos ha hy).trans_le h.1) h.2
  grind [Real.log_mul]

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-- `‖f_w'‖ = sup_{x ∈ [0,1]} |f_w'(x)|`. -/
noncomputable def supDeriv (w : List (Fin N)) : ℝ := ⨆ x : I, ‖deriv (Φ.comp w) x‖

/-- The sum `∑_{w ∈ Σ_n} ‖f_w'‖^t`, whose exponential growth rate is the pressure `P(t)`. -/
noncomputable abbrev pressureSum := Challenge.pressureSum Φ.f

/-- The normalized log pressure sum at positive length `n + 1`. -/
noncomputable abbrev pressureRate := Challenge.pressureRatio Φ.f

/-- `|f_w'(x)| ≤ ‖f_w'‖` for `x ∈ [0,1]`. -/
theorem norm_deriv_le_supDeriv (w : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    ‖deriv (Φ.comp w) x‖ ≤ Φ.supDeriv w :=
  le_ciSup (f := fun t : I => ‖deriv (Φ.comp w) (t : ℝ)‖)
    ⟨Φ.cmax ^ w.length, forall_mem_range.2 fun t =>
      (Φ.norm_deriv_comp_bounds w (Φ.real_mem_closed t.2)).2⟩ ⟨x, hx⟩

theorem supDeriv_bounds (w : List (Fin N)) : Φ.supDeriv w ∈ Icc (Φ.cmin ^ w.length) (Φ.cmax ^ w.length) :=
  ⟨((Φ.norm_deriv_comp_bounds w (zero_mem_closure_nbhd Φ.ε_pos)).1).trans
    (Φ.norm_deriv_le_supDeriv w (left_mem_Icc.2 zero_le_one)),
    Real.iSup_le (fun x => (Φ.norm_deriv_comp_bounds w (Φ.real_mem_closed x.2)).2) (by positivity [Φ.cmax_nonneg])⟩

theorem supDeriv_pos (w : List (Fin N)) : 0 < Φ.supDeriv w :=
  (norm_pos_iff.2 (Φ.deriv_comp_ne_zero w (zero_mem_closure_nbhd Φ.ε_pos))).trans_le
    (Φ.norm_deriv_le_supDeriv w (left_mem_Icc.2 zero_le_one))

theorem pressureSum_pos (hN : 0 < N) (t : ℝ) (n : ℕ) : 0 < Φ.pressureSum t n :=
  Finset.sum_pos (fun _ _ => Real.rpow_pos_of_pos (Φ.supDeriv_pos _) t)
    ⟨fun _ => ⟨0, hN⟩, Finset.mem_univ _⟩

noncomputable def logNormDeriv (w : List (Fin N)) (x : ℝ) : ℝ :=
  Real.log ‖deriv (Φ.comp w) x‖

/-- A bound on the finite dual projections is a uniform Lipschitz bound for
`log |f_w'|` on the interval, of any word length. -/
theorem exists_logNormDeriv_lip : ∃ D, 0 ≤ D ∧ ∀ w, ∀ x ∈ I, ∀ y ∈ I,
    |Φ.logNormDeriv w x - Φ.logNormDeriv w y| ≤ D * |x - y| := by
  obtain ⟨D, hD, h⟩ := Φ.exists_norm_dualProj_le
  refine ⟨D, hD, fun w x hx y hy => ?_⟩
  have hd (t : ℝ) (ht : t ∈ I) : HasDerivWithinAt (Φ.logNormDeriv w)
      (Φ.dualProj (.fin w.reverse) t).re I t := by
    have hz := Φ.real_mem_closed ht
    have hn := Φ.deriv_comp_ne_zero w hz
    rw [Φ.deriv_comp_real w ht, Complex.ofReal_ne_zero] at hn
    have he (u : ℝ) (hu : u ∈ I) : Φ.logNormDeriv w u = Real.log (deriv (Φ.comp w) u).re := by
      rw [logNormDeriv, ← Φ.abs_re_deriv_comp w hu, Real.log_abs]
    rw [Φ.dualProj_fin_reverse w hz, Φ.deriv_comp_real w ht, Complex.div_ofReal_re]
    exact ((hasDerivAt_re_ofReal (Φ.analyticAt_comp w hz).deriv.differentiableAt).log hn).hasDerivWithinAt.congr he (he t ht)
  exact (convex_Icc 0 1).norm_image_sub_le_of_norm_hasDerivWithin_le hd
    (fun t ht => (Complex.abs_re_le_norm _).trans (h _ _ (Φ.real_mem_closed ht))) hy hx

/-- Uniform distortion controls nonnegative powers of the derivative. -/
theorem exists_distortion : ∃ R > 0, ∀ w, ∀ x ∈ I, ∀ s ≥ (0 : ℝ),
    ‖deriv (Φ.comp w) x‖ ^ s ≤ Φ.supDeriv w ^ s ∧
      Φ.supDeriv w ^ s ≤ R ^ s * ‖deriv (Φ.comp w) x‖ ^ s := by
  obtain ⟨D, hD, h⟩ := Φ.exists_logNormDeriv_lip
  refine ⟨Real.exp D, Real.exp_pos _, fun w x hx s hs => ⟨?_, ?_⟩⟩
  · exact Real.rpow_le_rpow (norm_nonneg _) (Φ.norm_deriv_le_supDeriv w hx) hs
  · rw [← Real.mul_rpow (Real.exp_pos D).le (norm_nonneg _)]
    refine Real.rpow_le_rpow (Φ.supDeriv_pos w).le (Real.iSup_le (fun y => ?_) (by positivity)) hs
    have hp (t : I) : 0 < ‖deriv (Φ.comp w) (t : ℝ)‖ :=
      norm_pos_iff.2 (Φ.deriv_comp_ne_zero w (Φ.real_mem_closed t.2))
    rw [← Real.exp_log (hp y), ← Real.exp_log (hp ⟨x, hx⟩), ← Real.exp_add, Real.exp_le_exp]
    have hxy : |(y : ℝ) - x| ≤ 1 := by grind
    have H := (le_abs_self _).trans ((h w y y.2 x hx).trans (mul_le_of_le_one_right hD hxy))
    aesop

end AnalyticESC.IFS
