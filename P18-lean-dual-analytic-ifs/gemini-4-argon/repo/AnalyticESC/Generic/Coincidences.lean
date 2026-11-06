module

public import AnalyticESC.Generic.Class
public import AnalyticESC.Analysis

@[expose] public section

/-!
# The interpolation in the proof of Theorem 1.4

A `d₂`-small perturbation of an IFS whose maps send `[0,1]` into `(0,1)` and whose compositions
along distinct finite words differ on `[0,1]`.

The perturbation is `f_i^t = (1 - t) f_i + t h_i` for a small `t > 0`, where the affine maps
`h_i(z) = a z + b_i` have pairwise disjoint images `h_i(I) ⊆ (0,1)`, so that distinct compositions
of the `h_i` differ on `I`. For fixed words and a
fixed point of `I`, compositions of the `f_i^t` are holomorphic in the complex parameter `t` on an
open set containing `[0,1]`, so two of them agree for finitely many `t ∈ [0,1]` only. A countable
union of finite sets misses some small `t > 0`. Auxiliary results are in the namespace
`IFS.Coincidences`.
-/

namespace AnalyticESC

open Set Metric Filter Topology

namespace IFS.Coincidences

variable {N : ℕ} {ε : ℝ}

/-! ## The affine maps `h_i` -/

/-- The common slope `a = 1/(2(N+2))` of the affine maps `h_i`. -/
noncomputable def slope (N : ℕ) : ℝ := 2⁻¹ / (N + 2)

/-- The offset `b_i = (i+1)/(N+2)` of the affine map `h_i`. -/
noncomputable def offset (i : Fin N) : ℝ := (((i : ℕ) : ℝ) + 1) / (N + 2)

/-- `a > 0`. -/
theorem slope_pos : 0 < slope N := by unfold slope; positivity

/-- `a < 1`. -/
theorem slope_lt_one : slope N < 1 := by
  unfold slope
  rw [div_lt_one (by positivity)]
  linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

/-- `b_i > 0`. -/
theorem offset_pos (i : Fin N) : 0 < offset i := by unfold offset; positivity

/-- `h_i(I) = [b_i, b_i + a] ⊆ (0,1)`. -/
theorem offset_add_slope_lt_one (i : Fin N) : offset i + slope N < 1 := by
  have hi : ((i : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast i.isLt
  rw [offset, slope, ← add_div, div_lt_one (by positivity)]; linarith

/-- The intervals `h_i(I) = [b_i, b_i + a]` are pairwise disjoint. -/
theorem offset_add_slope_lt_offset {i j : Fin N} (hij : i < j) : offset i + slope N < offset j := by
  have : ((i : ℕ) : ℝ) + 1 ≤ (j : ℕ) := by exact_mod_cast (hij : (i : ℕ) + 1 ≤ j)
  rw [offset, slope, offset, ← add_div]
  exact div_lt_div_of_pos_right (by linarith) (by positivity)

/-- The affine map `h_i(z) = a z + b_i`. -/
noncomputable def target (i : Fin N) (z : ℂ) : ℂ := slope N * z + offset i

/-- `h_i` is real at real points. -/
theorem target_ofReal (i : Fin N) (x : ℝ) : target i x = ((slope N * x + offset i : ℝ) : ℂ) := by
  simp [target]

/-! ## The perturbations `f_i^t` -/

variable (Φ : IFS N ε)

/-- The map `f_i^t = (1 - t) f_i + t h_i`, for a complex parameter `t`. -/
noncomputable def homotopy (t : ℂ) (i : Fin N) (z : ℂ) : ℂ := (1 - t) * Φ.f i z + t * target i z

/-- The composition `f^t_w = f^t_{w₁} ∘ ⋯ ∘ f^t_{w_k}` of the maps `f_i^t`. -/
noncomputable def compT (t : ℂ) (w : List (Fin N)) : ℂ → ℂ :=
  w.foldr (fun i g => homotopy Φ t i ∘ g) id

/-- `f^t_{iw} = f_i^t ∘ f^t_w`. -/
theorem compT_cons (t : ℂ) (i : Fin N) (w : List (Fin N)) :
    compT Φ t (i :: w) = homotopy Φ t i ∘ compT Φ t w := rfl

/-- `f_i^1 = h_i`. -/
theorem homotopy_one (i : Fin N) (z : ℂ) : homotopy Φ 1 i z = target i z := by simp [homotopy]

/-- For real `t`, the map `f_i^t` is real at the real points of `B_{2ε}`. -/
theorem im_homotopy_ofReal (t : ℝ) (i : Fin N) {x : ℝ} (hx : (x : ℂ) ∈ nbhd (2 * ε)) :
    (homotopy Φ t i x).im = 0 := by
  simp [homotopy, target, Complex.mul_im, Φ.im_f_ofReal i hx]

/-- For real `t` and `x`, `Re f_i^t(x) = (1 - t) Re f_i(x) + t h_i(x)`. -/
theorem re_homotopy_ofReal (t : ℝ) (i : Fin N) (x : ℝ) :
    (homotopy Φ t i x).re = (1 - t) * (Φ.f i x).re + t * (slope N * x + offset i) := by
  simp [homotopy, target, Complex.mul_re]

private theorem target_mem_Ioo (i : Fin N) {x : ℝ} (hx : x ∈ I) :
    slope N * x + offset i ∈ Ioo 0 1 :=
  ⟨by linarith [offset_pos i, mul_nonneg (slope_pos (N := N)).le hx.1],
   by linarith [offset_add_slope_lt_one i, mul_le_of_le_one_right (slope_pos (N := N)).le hx.2]⟩

/-- For `t ∈ [0,1]`, the map `f_i^t` sends `I` into `I`. -/
theorem re_homotopy_mem_I {t : ℝ} (ht : t ∈ I) (i : Fin N) {x : ℝ} (hx : x ∈ I) :
    (homotopy Φ t i x).re ∈ I := by
  rw [re_homotopy_ofReal]
  obtain ⟨hf0, hf1⟩ := (Φ.inClass i).re_mem_I x hx
  obtain ⟨h1, h2⟩ := target_mem_Ioo i hx
  exact ⟨by nlinarith [ht.1, ht.2], by nlinarith [ht.1, ht.2]⟩

/-- For `t ∈ (0,1)`, the map `f_i^t` sends `I` into `(0,1)`. -/
theorem re_homotopy_mem_Ioo {t : ℝ} (ht : t ∈ Ioo 0 1) (i : Fin N) {x : ℝ} (hx : x ∈ I) :
    (homotopy Φ t i x).re ∈ Ioo 0 1 := by
  rw [re_homotopy_ofReal]
  obtain ⟨hf0, hf1⟩ := (Φ.inClass i).re_mem_I x hx
  obtain ⟨h1, h2⟩ := target_mem_Ioo i hx
  exact ⟨by nlinarith [ht.1, ht.2], by nlinarith [ht.1, ht.2]⟩

/-- For `t ∈ [0,1]`, the compositions `f^t_w` send real points of `I` to real points of `I`. -/
theorem exists_compT_ofReal {t : ℝ} (ht : t ∈ I) (w : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    ∃ y ∈ I, compT Φ t w x = y := by
  induction w with
  | nil => exact ⟨x, hx, rfl⟩
  | cons i w ih =>
    obtain ⟨y, hy, hyx⟩ := ih
    refine ⟨(homotopy Φ t i y).re, re_homotopy_mem_I Φ ht i hy, ?_⟩
    rw [compT_cons, Function.comp_apply, hyx]
    exact Complex.ext (by simp)
      ((im_homotopy_ofReal Φ t i (ofReal_mem_nbhd (by linarith [Φ.ε_pos]) hy)).trans
        (Complex.ofReal_im _).symm)

/-! ## Distinct compositions of the affine maps -/

/-- For `x ∈ I`, the point `h_{iw}(x)` lies in `h_i(I) = [b_i, b_i + a]`. -/
theorem re_compT_one_cons_mem (i : Fin N) (w : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    (compT Φ 1 (i :: w) x).re ∈ Icc (offset i) (offset i + slope N) := by
  obtain ⟨y, hy, hyx⟩ := exists_compT_ofReal Φ (t := 1) ⟨zero_le_one, le_rfl⟩ w hx
  rw [Complex.ofReal_one] at hyx
  rw [compT_cons, Function.comp_apply, hyx, homotopy_one, target_ofReal, Complex.ofReal_re]
  exact ⟨by linarith [mul_nonneg (slope_pos (N := N)).le hy.1],
    by linarith [mul_le_of_le_one_right (slope_pos (N := N)).le hy.2]⟩

/-- Compositions of the affine maps `h_i` along distinct finite words differ on `I`. -/
theorem exists_compT_one_ne (u v : List (Fin N)) (huv : u ≠ v) :
    ∃ x ∈ I, compT Φ 1 u x ≠ compT Φ 1 v x := by
  have h0 : (0 : ℝ) ∈ I := ⟨le_rfl, zero_le_one⟩
  have hpos (i : Fin N) (w : List (Fin N)) : 0 < (compT Φ 1 (i :: w) ((0 : ℝ) : ℂ)).re :=
    (offset_pos i).trans_le (re_compT_one_cons_mem Φ i w h0).1
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => exact absurd rfl huv
    | cons j v => exact ⟨0, h0, fun h => (hpos j v).ne' (by rw [← h]; simp [compT])⟩
  | cons i u ih =>
    cases v with
    | nil => exact ⟨0, h0, fun h => (hpos i u).ne' (by rw [h]; simp [compT])⟩
    | cons j v =>
      by_cases hij : i = j
      · subst hij
        obtain ⟨x, hx, hne⟩ := ih v fun h => huv (by rw [h])
        refine ⟨x, hx, fun h => hne ?_⟩
        rw [compT_cons, compT_cons, Function.comp_apply, Function.comp_apply, homotopy_one,
          homotopy_one] at h
        exact mul_left_cancel₀ (Complex.ofReal_ne_zero.2 slope_pos.ne') (add_right_cancel h)
      · refine ⟨0, h0, fun h => ?_⟩
        have hi := re_compT_one_cons_mem Φ i u h0
        have hj := re_compT_one_cons_mem Φ j v h0
        rw [h] at hi
        rcases lt_or_gt_of_ne hij with hlt | hlt <;>
          linarith [offset_add_slope_lt_offset hlt, hi.1, hi.2, hj.1, hj.2]

/-! ## The perturbations lie in the class -/

/-- `(f_i^t)' = (1 - t) f_i' + t a` where `f_i` is differentiable. -/
theorem hasDerivAt_homotopy (t : ℂ) (i : Fin N) {z : ℂ} (hz : DifferentiableAt ℂ (Φ.f i) z) :
    HasDerivAt (homotopy Φ t i) ((1 - t) * deriv (Φ.f i) z + t * slope N) z :=
  ((hz.hasDerivAt.const_mul (1 - t)).add
    ((((hasDerivAt_id z).const_mul (slope N : ℂ)).add_const (offset i : ℂ)).const_mul t)).congr_deriv
    (by simp)

/-- `(f_i^t)' = (1 - t) f_i' + t a` on `B_{2ε}`. -/
theorem deriv_homotopy (t : ℂ) (i : Fin N) {z : ℂ} (hz : z ∈ nbhd (2 * ε)) :
    deriv (homotopy Φ t i) z = (1 - t) * deriv (Φ.f i) z + t * slope N :=
  (hasDerivAt_homotopy Φ t i
    ((Φ.differentiableOn_f i).differentiableAt ((isOpen_nbhd _).mem_nhds hz))).deriv

/-- For `0 < t < c_min/(c_min + 1)`, the map `f_i^t` lies in `S^ω_ε(I)`. -/
theorem inClass_homotopy {t : ℝ} (ht0 : 0 < t) (ht : t * (Φ.cmin + 1) < Φ.cmin) (i : Fin N) :
    InClass ε (homotopy Φ t i) := by
  have hc := Φ.cmin_nonneg
  have ht1 : t < 1 := by nlinarith
  have ha := slope_pos (N := N)
  have ha1 := slope_lt_one (N := N)
  have hn1 (z : ℂ) : ‖(1 - (t : ℂ)) * deriv (Φ.f i) z‖ = (1 - t) * ‖deriv (Φ.f i) z‖ := by
    rw [norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  have hn2 : ‖(t : ℂ) * slope N‖ = t * slope N := by
    rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  refine InClass.of_deriv Φ.ε_pos (fun z hz => (hasDerivAt_homotopy Φ t i
      ((Φ.differentiableOn_f i).differentiableAt ((isOpen_nbhd _).mem_nhds hz))).differentiableAt.differentiableWithinAt)
    (fun x hx => im_homotopy_ofReal Φ t i hx) (fun x hx => re_homotopy_mem_I Φ ⟨ht0.le, ht1.le⟩ i hx)
    (fun z hz h0 => ?_) (fun z hz => ?_)
  · have h := congrArg norm (eq_neg_of_add_eq_zero_left
      (deriv_homotopy Φ t i (IFS.closure_nbhd_subset_two hz) ▸ h0))
    rw [norm_neg, hn1, hn2] at h
    nlinarith [mul_le_mul_of_nonneg_left (Φ.cmin_le_norm_deriv i hz) (by linarith : (0 : ℝ) ≤ 1 - t),
      mul_lt_mul_of_pos_left ha1 ht0]
  · rw [deriv_homotopy Φ t i (IFS.closure_nbhd_subset_two hz)]
    refine (norm_add_le _ _).trans_lt ?_
    rw [hn1, hn2]
    nlinarith [mul_lt_mul_of_pos_left ((Φ.inClass i).norm_deriv_lt_one z hz)
      (by linarith : (0 : ℝ) < 1 - t), mul_lt_mul_of_pos_left ha1 ht0]

/-! ## The distance to the perturbation -/

/-- `d₂(f_i, f_i^t) ≤ t (4 + K)` for `t ∈ [0,1]`, where `K` bounds `|f_i''/f_i'|` on `cl B_ε`. -/
private theorem d2Map_homotopy_le (i : Fin N) {K : ℝ} (hK : 0 ≤ K)
    (hK' : ∀ z ∈ closure (nbhd ε), ‖Φ.nonlin i z‖ ≤ K) {t : ℝ} (ht : t ∈ I) :
    d2Map (Φ.f i) (homotopy Φ t i) ≤ t * (4 + K) := by
  have hmem {x : ℝ} (hx : x ∈ I) : (x : ℂ) ∈ nbhd (2 * ε) :=
    ofReal_mem_nbhd (by linarith [Φ.ε_pos]) hx
  have hcl {x : ℝ} (hx : x ∈ I) : (x : ℂ) ∈ closure (nbhd ε) :=
    subset_closure (ofReal_mem_nbhd Φ.ε_pos hx)
  have ht0 := ht.1
  have hnt : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_of_nonneg ht0]
  have e0 {x : ℝ} (hx : x ∈ I) : ‖Φ.f i x - homotopy Φ t i x‖ ≤ t * 2 := by
    obtain ⟨hf0, hf1⟩ := (Φ.inClass i).re_mem_I x hx
    obtain ⟨h1, h2⟩ := target_mem_Ioo i hx
    have hf : ‖Φ.f i x‖ ≤ 1 := by
      rw [← Complex.abs_re_eq_norm.2 (Φ.im_f_ofReal i (hmem hx)), abs_of_nonneg hf0]; exact hf1
    have hh : ‖target i x‖ ≤ 1 := by
      rw [target_ofReal, Complex.norm_real, Real.norm_of_nonneg h1.le]; exact h2.le
    rw [show Φ.f i x - homotopy Φ t i x = t * (Φ.f i x - target i x) by unfold homotopy; ring,
      norm_mul, hnt]
    exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (by linarith)) ht0
  have e1 {x : ℝ} (hx : x ∈ I) : ‖deriv (Φ.f i) x - deriv (homotopy Φ t i) x‖ ≤ t * 2 := by
    have h1 := (Φ.inClass i).norm_deriv_lt_one _ (hcl hx)
    have h2 : ‖(slope N : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg slope_pos.le]; exact slope_lt_one.le
    rw [show deriv (Φ.f i) x - deriv (homotopy Φ t i) x = t * (deriv (Φ.f i) x - slope N) by
      rw [deriv_homotopy Φ t i (hmem hx)]; ring, norm_mul, hnt]
    exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (by linarith)) ht0
  have e2 {x : ℝ} (hx : x ∈ I) :
      ‖deriv (deriv (Φ.f i)) x - deriv (deriv (homotopy Φ t i)) x‖ ≤ t * K := by
    have hzx := (isOpen_nbhd _).mem_nhds (hmem hx)
    have heq : deriv (homotopy Φ t i) =ᶠ[𝓝 (x : ℂ)]
        fun z => (1 - t) * deriv (Φ.f i) z + t * slope N :=
      Filter.eventually_of_mem hzx fun z hz => deriv_homotopy Φ t i hz
    have hd := ((Φ.differentiableOn_f i).deriv (isOpen_nbhd _)).differentiableAt hzx
    rw [heq.deriv_eq, deriv_add_const, deriv_const_mul _ hd,
      show deriv (deriv (Φ.f i)) x - (1 - t) * deriv (deriv (Φ.f i)) x =
        t * deriv (deriv (Φ.f i)) x by ring, norm_mul, hnt]
    exact mul_le_mul_of_nonneg_left
      ((Φ.norm_deriv_deriv_le i (hcl hx)).trans (hK' _ (hcl hx))) ht0
  have s0 := Real.iSup_le (fun x : I => e0 x.2) (by positivity)
  have s1 := Real.iSup_le (fun x : I => e1 x.2) (by positivity)
  have s2 := Real.iSup_le (fun x : I => e2 x.2) (by positivity)
  unfold d2Map; linarith

/-! ## Coincidences for finitely many parameters -/

/-- For a fixed word `w` and `x ∈ I`, the map `t ↦ f^t_w(x)` is complex analytic at every point of
`[0,1]`. -/
theorem analyticAt_compT (w : List (Fin N)) {x : ℝ} (hx : x ∈ I) {s : ℝ} (hs : s ∈ I) :
    AnalyticAt ℂ (fun t => compT Φ t w x) s := by
  induction w with
  | nil => exact analyticAt_const
  | cons i w ih =>
    obtain ⟨y, hy, hyx⟩ := exists_compT_ofReal Φ hs w hx
    have hf : AnalyticAt ℂ (Φ.f i) (compT Φ s w x) :=
      (Φ.differentiableOn_f i).analyticAt
        ((isOpen_nbhd _).mem_nhds (hyx ▸ ofReal_mem_nbhd (by linarith [Φ.ε_pos]) hy))
    have hfi : AnalyticAt ℂ (fun t => Φ.f i (compT Φ t w x)) s := AnalyticAt.comp hf ih
    show AnalyticAt ℂ
      (fun t => (1 - t) * Φ.f i (compT Φ t w x) + t * (slope N * compT Φ t w x + offset i)) s
    fun_prop

end IFS.Coincidences

namespace IFS

open Coincidences

variable {N : ℕ} {ε : ℝ}

/-- The interpolation at the start of the density proof of Theorem 1.4. -/
theorem exists_noCoincidence_near (Φ : IFS N ε) (hN : 0 < N) {r : ℝ} (hr : 0 < r) :
    ∃ t : ℝ, 0 < t ∧ ∃ Ψ : IFS N ε, Ψ.f = homotopy Φ t ∧ d2 Φ Ψ < r ∧
      (∀ i, ∀ x ∈ I, (Ψ.f i x).re ∈ Ioo 0 1) ∧ Ψ.NoCoincidence := by
  set c := Φ.cmin
  have hc : 0 < c := Φ.cmin_pos hN
  obtain ⟨K, hK, hK'⟩ := Φ.exists_nonlin_bound
  set B : Set ℝ := ⋃ p : List (Fin N) × List (Fin N),
    {t | t ∈ I ∧ p.1 ≠ p.2 ∧ ∀ x ∈ I, compT Φ t p.1 x = compT Φ t p.2 x}
  have hB : B.Countable := countable_iUnion fun p => Finite.countable <| by
    by_cases hp : p.1 = p.2
    · simp [hp]
    · obtain ⟨x, hx, hne⟩ := exists_compT_one_ne Φ p.1 p.2 hp
      exact (finite_zeros_of_analyticAt
        (fun s hs => (analyticAt_compT Φ p.1 hx hs).sub (analyticAt_compT Φ p.2 hx hs))
        ⟨1, ⟨zero_le_one, le_rfl⟩, by simpa [sub_eq_zero] using hne⟩).subset
        fun t ht => ⟨ht.1, sub_eq_zero.2 (ht.2.2 x hx)⟩
  set t₀ := min (c / (c + 1)) (r / (4 + K))
  have ht₀ : 0 < t₀ := lt_min (by positivity) (by positivity)
  obtain ⟨t, htB, ht⟩ := (hB.dense_compl ℝ).exists_mem_open isOpen_Ioo (nonempty_Ioo.2 ht₀)
  have ht1 : t * (c + 1) < c :=
    (lt_div_iff₀ (by positivity)).1 (ht.2.trans_le (min_le_left _ _))
  have ht2 : t * (4 + K) < r :=
    (lt_div_iff₀ (by positivity)).1 (ht.2.trans_le (min_le_right _ _))
  have ht_lt : t < 1 := by nlinarith [ht.1]
  have htI : t ∈ I := ⟨ht.1.le, ht_lt.le⟩
  refine ⟨t, ht.1, ⟨homotopy Φ t, Φ.ε_pos, inClass_homotopy Φ ht.1 ht1⟩, rfl,
    (Real.iSup_le (fun i => d2Map_homotopy_le Φ i hK (hK' i) htI)
      (mul_nonneg ht.1.le (by linarith))).trans_lt ht2,
    fun i x hx => re_homotopy_mem_Ioo Φ ⟨ht.1, ht_lt⟩ i hx, fun u v huv => ?_⟩
  by_contra! h
  exact htB (mem_iUnion.2 ⟨(u, v), htI, huv, h⟩)

end IFS

end AnalyticESC
