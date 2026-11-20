module
public import AnalyticESC.Dimension.Geometry

@[expose] public section
namespace AnalyticESC.IFS
open Set Filter Topology
variable {N : ℕ} [NeZero N] (Φ : IFS N)

lemma supDeriv_pos (w) : 0 < Φ.supDeriv w := (Φ.weight_pos w zero_I).trans_le
  (Φ.norm_deriv_le_supDeriv w zero_I)

private lemma submul (u v) : Φ.supDeriv (u ++ v) ≤ Φ.supDeriv u * Φ.supDeriv v := by
  refine ciSup_le fun x => ?_
  change Φ.weight (u++v) x ≤ _
  rw [Φ.weight_append _ _ x.2]
  exact mul_le_mul (Φ.norm_deriv_le_supDeriv _ (Φ.re_comp_mem_I _ x.2)) (Φ.norm_deriv_le_supDeriv _ x.2) (norm_nonneg _) (Φ.supDeriv_pos _).le

lemma pressureSum_pos (t : ℝ) (n : ℕ) : 0 < Φ.pressureSum t n :=
  Finset.sum_pos (fun _ _ => Real.rpow_pos_of_pos (Φ.supDeriv_pos _) t) Finset.univ_nonempty

private lemma subadd {t : ℝ} (ht : 0 ≤ t) : Subadditive fun n => Real.log (Φ.pressureSum t n) := by
  intro m n
  rw [← Real.log_mul (Φ.pressureSum_pos t m).ne' (Φ.pressureSum_pos t n).ne']
  apply Real.log_le_log (Φ.pressureSum_pos t _)
  simp only [pressureSum,Finset.sum_mul_sum,← Fintype.sum_prod_type',← (Fin.appendEquiv m n).sum_comp]
  apply Finset.sum_le_sum; rintro ⟨u,v⟩ _
  change Φ.supDeriv (.ofFn (Fin.append u v)) ^ t ≤ _
  rw [List.ofFn_fin_append,← Real.mul_rpow (Φ.supDeriv_pos _).le (Φ.supDeriv_pos _).le]
  exact Real.rpow_le_rpow (Φ.supDeriv_pos _).le (Φ.submul _ _) ht

lemma rate_zero {n : ℕ} (hn : 0 < n) : Φ.rate 0 n = Real.log N := by
  simp [rate,pressureSum,Real.log_pow,hn.ne',mul_div_cancel_left₀]

/-- Increasing the exponent multiplies each weight by a factor between the
corresponding powers of the minimum and maximum contractions. -/
private lemma rate_gap {t u : ℝ} (h : t ≤ u) {n : ℕ} (hn : 0 < n) :
    Φ.rate u n - Φ.rate t n ∈ Icc ((u-t)*Real.log Φ.cmin) ((u-t)*Real.log Φ.cmax) := by
  let w (v : Block N n) := Φ.supDeriv (.ofFn v)
  have ht := Φ.pressureSum_pos t n
  have hm := Φ.cmin_pos
  have hM := Φ.cmax_pos
  have bound (v : Block N n) : w v ^ u ∈ Icc ((Φ.cmin^n)^(u-t) * w v ^ t) ((Φ.cmax^n)^(u-t) * w v ^ t) := by
    have hl : Φ.cmin^n ≤ w v := by simpa  using Φ.cmin_pow_le_supDeriv (.ofFn v)
    have hu : w v ≤ Φ.cmax^n := by simpa  using Φ.supDeriv_le (.ofFn v)
    have hv : 0 < w v := Φ.supDeriv_pos _
    have e : w v ^ u = w v ^ (u-t) * w v ^ t := by rw [← Real.rpow_add hv,sub_add_cancel]
    rw [e]; constructor <;> gcongr
  have H := sum_bounds (S := Finset.univ) fun v _ => bound v
  rw [←Finset.mul_sum,←Finset.mul_sum] at H
  have G := log_bounds (by positivity) (by positivity) ht H
  simp only [Real.log_rpow (pow_pos hm n), Real.log_rpow (pow_pos hM n),Real.log_pow,mem_Icc] at G
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  change _ ≤ Φ.rate u n - Φ.rate t n ∧ _
  simp only [rate,← sub_div,le_div_iff₀ hn',div_le_iff₀ hn']; grind

/-- The slope bound persists whenever the two pressure limits exist. -/
lemma slopes {x y p q : ℝ} (h : x ≤ y) (hp : Tendsto (Φ.rate x) atTop (𝓝 p)) (hq : Tendsto (Φ.rate y) atTop (𝓝 q)) :
    q-p ∈ Icc ((y-x)*Real.log Φ.cmin) ((y-x)*Real.log Φ.cmax) :=
  isClosed_Icc.mem_of_tendsto (hq.sub hp) ((eventually_gt_atTop 0).mono fun _ hn => Φ.rate_gap h hn)

lemma lim_zero : Tendsto (Φ.rate 0) atTop (𝓝 (Real.log N)) :=
  tendsto_const_nhds.congr' ((eventually_gt_atTop 0).mono fun _ hn => (Φ.rate_zero hn).symm)

/-- The pressure has a unique zero. Existence uses subadditivity at nonnegative
exponents; the slope bound gives uniqueness even among negative exponents. -/
theorem exists_pressure_zero : ∃ s ≥ 0, Φ.UniqueRoot s := by
  let P t := limUnder atTop (Φ.rate t)
  have hM := Real.log_neg (Φ.cmax_pos) Φ.cmax_lt_one
  have hN' : 0 ≤ Real.log N := by positivity
  have lim t (ht : 0 ≤ t) : Tendsto (Φ.rate t) atTop (𝓝 (P t)) := by
    apply tendsto_nhds_limUnder
    have sub := Φ.subadd ht
    refine ⟨_,sub.tendsto_lim ⟨min 0 (t*Real.log Φ.cmin),?_⟩⟩
    rintro _ ⟨n,rfl⟩
    cases n with
    | zero => simp
    | succ n =>
      have H := (Φ.rate_gap ht (n := n+1) (by omega)).1
      rw [Φ.rate_zero (by omega)] at H
      grind
  have gap x y (hx : 0 ≤ x) (hxy : x ≤ y) := Φ.slopes hxy (lim x hx) (lim y (hx.trans hxy))
  have hcont : ContinuousOn P (Ici 0) := by
    refine (LipschitzOnWith.of_dist_le' (K := -Real.log Φ.cmin) ?_).continuousOn
    intro x hx y hy
    wlog h : x ≤ y generalizing x y
    · simpa only [dist_comm] using this y hy x hx (le_of_not_ge h)
    have ⟨l,u⟩ := gap x y hx h
    rw [Real.dist_eq,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr h),abs_le]; constructor <;> nlinarith
  have hP0 := tendsto_nhds_unique (lim 0 le_rfl) Φ.lim_zero
  let T := Real.log N / -Real.log Φ.cmax
  have hT : 0 ≤ T := div_nonneg hN' (by linarith)
  have he : T * -Real.log Φ.cmax = Real.log N := div_mul_cancel₀ _ (by linarith)
  obtain ⟨s,hs,e⟩ := intermediate_value_Icc' hT (hcont.mono fun x hx => hx.1) (show 0 ∈ Icc (P T) (P 0) by grind)
  have lims := e ▸ lim s hs.1
  have distinct {x y} (hxy : x < y) (hx : Tendsto (Φ.rate x) atTop (𝓝 0)) (hy : Tendsto (Φ.rate y) atTop (𝓝 0)) : False := by
    have := (Φ.slopes hxy.le hx hy).2; nlinarith
  refine ⟨s,hs.1,fun t => (Φ.ratio_limit t).trans ⟨fun h => le_antisymm (not_lt.mp fun e => distinct e lims h) (not_lt.mp fun e => distinct e h lims),?_⟩⟩
  simp_all

end AnalyticESC.IFS
