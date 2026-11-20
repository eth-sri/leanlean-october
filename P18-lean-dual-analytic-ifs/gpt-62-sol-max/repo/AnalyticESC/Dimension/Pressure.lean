module

public import AnalyticESC.Dimension.Defs

@[expose] public section

/-!
# The pressure and the conformality dimension

The pressure `P(t) = lim_n (1/n) log ∑_{w ∈ Σ_n} ‖f_w'‖^t` of Section 1.2.1 exists for every `t`,
by sub-additivity, and vanishes at exactly one `t = s(Φ) ≥ 0`, the conformality dimension.
-/

namespace AnalyticESC

open Set Metric Filter Topology MeasureTheory

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-- The pressure approximants have slopes uniformly bounded by the two log derivatives. -/
private theorem rate_slope (hN : 0 < N) {x y : ℝ} (hxy : x ≤ y) (n : ℕ) :
    Φ.pressureRate y n - Φ.pressureRate x n ∈
      Icc ((y - x) * Real.log Φ.cmin) ((y - x) * Real.log Φ.cmax) := by
  let m := n+1
  let d := y - x
  let p := Φ.pressureSum x m
  let q := Φ.pressureSum y m
  have hn' : (0 : ℝ) < m := by positivity
  obtain ⟨hlo, hup⟩ : (Φ.cmin ^ m) ^ d * p ≤ q ∧ q ≤ (Φ.cmax ^ m) ^ d * p := by
    apply sum_mul_bounds
    intro v _
    let a := Φ.supDeriv (List.ofFn v)
    have ha : 0 < a := Φ.supDeriv_pos _
    have ⟨hl, hu⟩ : a ∈ Icc (Φ.cmin ^ m) (Φ.cmax ^ m) := by simpa only [List.length_ofFn] using Φ.supDeriv_bounds (List.ofFn v)
    have he : a ^ y = a ^ d * a ^ x := by grind [Real.rpow_add, sub_add_cancel]
    change (Φ.cmin ^ m) ^ d * a ^ x ≤ a ^ y ∧ a ^ y ≤ (Φ.cmax ^ m) ^ d * a ^ x
    rw [he]
    constructor <;> gcongr; positivity [Φ.cmin_nonneg]
  have hm := Φ.cmin_pos hN
  have hc := Φ.cmax_pos hN
  have h := log_sub_mem_Icc_of_mul_bounds (Φ.pressureSum_pos hN x m) (Real.rpow_pos_of_pos (pow_pos hm m) d)
    (Real.rpow_pos_of_pos (pow_pos hc m) d) ⟨hlo, hup⟩
  rw [Real.log_rpow (pow_pos hm m), Real.log_rpow (pow_pos hc m), Real.log_pow, Real.log_pow] at h
  change Real.log q / m - Real.log p / m ∈ Icc _ _
  rw [mem_Icc, ← sub_div, le_div_iff₀ hn', div_le_iff₀ hn']
  grind

private theorem rate_zero (n : ℕ) : Φ.pressureRate 0 n = Real.log N := by
  simp [Challenge.pressureRatio, divide, Challenge.pressureSum, Real.log_pow, Nat.cast_succ,
    show (n : ℝ) + 1 ≠ 0 by positivity]

private theorem tendsto_rate_zero : Tendsto (Φ.pressureRate 0) atTop (𝓝 (Real.log N)) :=
  tendsto_const_nhds.congr fun n => (Φ.rate_zero n).symm

/-- For `t ≥ 0`, `(1/n) log ∑_{w ∈ Σ_n} ‖f_w'‖^t` converges, by Fekete's lemma. -/
private theorem pr_exists_tendsto (hN : 0 < N) {t : ℝ} (ht : 0 ≤ t) :
    ∃ p, Tendsto (Φ.pressureRate t) atTop (𝓝 p) := by
  have hsub : Subadditive fun n => Real.log (Φ.pressureSum t n) := by
    intro m n
    have hP := Φ.pressureSum_pos hN t
    rw [← Real.log_mul (hP m).ne' (hP n).ne']
    apply Real.log_le_log (hP _)
    simp only [Challenge.pressureSum, ← supDeriv.eq_def, Finset.sum_mul_sum, ← Fintype.sum_prod_type']
    rw [← (Fin.appendEquiv m n).sum_comp]
    refine Finset.sum_le_sum fun (u, v) _ => ?_
    rw [show Fin.appendEquiv m n (u, v) = Fin.append u v from funext (Fin.appendEquiv_apply m n _),
      List.ofFn_fin_append, ← Real.mul_rpow (Φ.supDeriv_pos _).le (Φ.supDeriv_pos _).le]
    refine Real.rpow_le_rpow (Φ.supDeriv_pos _).le ?_ ht
    have : Nonempty I := ⟨⟨0, by simp⟩⟩
    refine ciSup_le fun x => ?_
    have hu := Φ.norm_deriv_le_supDeriv (List.ofFn u) (Φ.re_comp_mem_I (List.ofFn v) x.2)
    rw [Φ.deriv_comp_append _ _ (Φ.real_mem_closed x.2), norm_mul, Φ.comp_ofReal _ x.2]
    exact mul_le_mul hu (Φ.norm_deriv_le_supDeriv _ x.2) (norm_nonneg _) ((norm_nonneg _).trans hu)
  refine ⟨hsub.lim, (tendsto_add_atTop_iff_nat (f := fun n => Real.log (Φ.pressureSum t n) / n) 1).2
    (hsub.tendsto_lim ⟨t * Real.log Φ.cmin, ?_⟩)⟩
  rintro _ ⟨_ | n, rfl⟩
  · simpa using mul_nonpos_of_nonneg_of_nonpos ht (Real.log_nonpos Φ.cmin_nonneg (Φ.cmin_lt_one hN).le)
  · have h := (Φ.rate_slope hN ht n).1
    rw [Φ.rate_zero, sub_zero] at h
    have : 0 ≤ Real.log N := Real.log_nonneg (by simpa)
    change _ ≤ Φ.pressureRate t n; linarith

/-- The pressure has a unique zero `s(Φ) ≥ 0`. -/
theorem exists_pressure_zero (hN : 0 < N) :
    ∃ s : ℝ, 0 ≤ s ∧ Challenge.IsUniquePressureZero Φ.f s := by
  let P (t : ℝ) := limUnder atTop (Φ.pressureRate t)
  have hP {t : ℝ} (ht : 0 ≤ t)  :=
    tendsto_nhds_limUnder (Φ.pr_exists_tendsto hN ht)
  let U := Real.log Φ.cmax
  have hU  := Real.log_neg (Φ.cmax_pos hN) Φ.cmax_lt_one
  have hzero := Φ.tendsto_rate_zero
  have hP0  := tendsto_nhds_unique (hP le_rfl) hzero ▸ Real.log_nonneg (by simpa)
  have hslope {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)  :=
    isClosed_Icc.mem_of_tendsto ((hP (hx.trans hxy)).sub (hP hx))
      (.of_forall (Φ.rate_slope hN hxy))
  have hanti : StrictAntiOn P (Ici 0) := fun _ hx _ _ hxy => by
    exact sub_neg.1 (((hslope hx hxy.le).2).trans_lt (mul_neg_of_pos_of_neg (sub_pos.2 hxy) hU))
  have hcont : ContinuousOn P (Ici 0) := by
    refine (LipschitzOnWith.of_dist_le' (K := -(Real.log Φ.cmin)) fun x hx y hy => ?_).continuousOn
    wlog hxy : x ≤ y generalizing x y
    · simpa only [dist_comm] using this y hy x hx (le_of_not_ge hxy)
    obtain ⟨hl, hu⟩ := hslope hx hxy
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 (hanti.antitoneOn hx hy hxy)),
      abs_of_nonpos (sub_nonpos.2 hxy)]
    linarith
  let T := P 0 / -U
  have hT  := div_nonneg hP0 (neg_pos.2 hU).le
  have hPT : P T ≤ 0 := by
    have hTU : T * -U = P 0 := div_mul_cancel₀ _ (neg_ne_zero.2 hU.ne)
    grind
  obtain ⟨s, hs, hPs⟩ : (0 : ℝ) ∈ P '' Icc 0 T :=
    intermediate_value_Icc' hT (hcont.mono fun _ h => h.1) ⟨hPT, hP0⟩
  refine ⟨s, hs.1, fun t => ⟨fun h => ?_, fun e => e ▸ hPs ▸ hP hs.1⟩⟩
  rcases le_or_gt 0 t with ht | ht
  · exact hanti.injOn ht hs.1 ((tendsto_nhds_unique (hP ht) h).trans hPs.symm)
  · exfalso
    have hb := le_of_tendsto_of_tendsto (hzero.sub h) tendsto_const_nhds
      (.of_forall fun n => (Φ.rate_slope hN ht.le n).2)
    have hlog : 0 ≤ Real.log N := Real.log_nonneg (by simpa)
    have := mul_neg_of_pos_of_neg (sub_pos.2 ht) hU
    linarith

/-- An upper bound on the pressure at `1` excludes all zeros at or above `1`. -/
theorem pressure_zero_lt_one (hN : 0 < N) (h : Real.log N + Real.log Φ.cmax < 0) {s : ℝ}
    (hs : Tendsto (Φ.pressureRate s) atTop (𝓝 0)) : s < 1 := by
  by_contra! h₁
  have hb := le_of_tendsto_of_tendsto (hs.sub Φ.tendsto_rate_zero) tendsto_const_nhds
    (.of_forall fun n => (Φ.rate_slope hN (zero_le_one.trans h₁) n).2)
  rw [sub_zero, zero_sub] at hb
  have hu := Real.log_neg (Φ.cmax_pos hN) Φ.cmax_lt_one
  nlinarith

end IFS

end AnalyticESC
