module

public import AnalyticESC.Conjugation

@[expose] public section

namespace AnalyticESC

open Set Metric Filter Topology MeasureTheory
open scoped Interval

namespace IFS.Coincidences

variable {N : ℕ} {ε : ℝ}

noncomputable def slope (N : ℕ) : ℝ := 1 / (2 * (N + 2))

noncomputable def offset (i : Fin N) : ℝ := (((i : ℕ) : ℝ) + 1) / (N + 2)

theorem slope_pos : 0 < slope N := by unfold slope; positivity

theorem slope_lt_one : slope N < 1 := by
  unfold slope; rw [div_lt_one (by positivity)]; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

theorem offset_pos (i : Fin N) : 0 < offset i := by unfold offset; positivity

private theorem offset_add_slope_eq (i : Fin N) :
    offset i + slope N = (2 * ((i : ℕ) : ℝ) + 3) / (2 * (N + 2)) := by
  unfold offset slope; field_simp; ring

theorem offset_add_slope_lt_one (i : Fin N) : offset i + slope N < 1 := by
  have hi : ((i : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast i.isLt
  rw [offset_add_slope_eq, div_lt_one (by positivity)]; linarith

theorem offset_add_slope_lt_offset {i j : Fin N} (hij : i < j) : offset i + slope N < offset j := by
  have hij'' : ((i : ℕ) : ℝ) + 1 ≤ (j : ℕ) := by exact_mod_cast (hij : (i : ℕ) + 1 ≤ j)
  rw [offset_add_slope_eq, show offset j = (2 * ((j : ℕ) : ℝ) + 2) / (2 * (N + 2)) by unfold offset; field_simp]
  exact div_lt_div_of_pos_right (by linarith) (by positivity)

noncomputable def target (i : Fin N) (z : ℂ) : ℂ := slope N * z + offset i

variable (Φ : IFS N ε)

noncomputable def homotopy (t : ℂ) (i : Fin N) (z : ℂ) : ℂ := (1 - t) * Φ.f i z + t * target i z

noncomputable def compT (t : ℂ) (w : List (Fin N)) : ℂ → ℂ :=
  w.foldr (fun i g => homotopy Φ t i ∘ g) id

theorem im_homotopy_ofReal (t : ℝ) (i : Fin N) {x : ℝ} (hx : (x : ℂ) ∈ nbhd (2 * ε)) :
    (homotopy Φ t i x).im = 0 := by
  simp [homotopy, target, Complex.mul_im, Φ.im_f_ofReal i hx]

theorem re_homotopy_ofReal (t : ℝ) (i : Fin N) (x : ℝ) :
    (homotopy Φ t i x).re = (1 - t) * (Φ.f i x).re + t * (slope N * x + offset i) := by
  simp [homotopy, target, Complex.mul_re]

theorem re_homotopy_mem_I {t : ℝ} (ht : t ∈ I) (i : Fin N) {x : ℝ} (hx : x ∈ I) :
    (homotopy Φ t i x).re ∈ I := by
  rw [re_homotopy_ofReal]
  have hf := (Φ.inClass i).re_mem_I x hx
  have h3 := mul_nonneg (slope_pos (N := N)).le hx.1
  have h4 := mul_le_of_le_one_right (slope_pos (N := N)).le hx.2
  exact ⟨by nlinarith [ht.1, ht.2, offset_pos i, mul_nonneg (sub_nonneg.2 ht.2) hf.1],
    by nlinarith [ht.1, ht.2, offset_add_slope_lt_one i, mul_nonneg (sub_nonneg.2 ht.2) (sub_nonneg.2 hf.2)]⟩

theorem re_homotopy_mem_Ioo {t : ℝ} (ht : t ∈ Ioo 0 1) (i : Fin N) {x : ℝ} (hx : x ∈ I) :
    (homotopy Φ t i x).re ∈ Ioo 0 1 := by
  rw [re_homotopy_ofReal]
  have hf := (Φ.inClass i).re_mem_I x hx
  have h3 := mul_nonneg (slope_pos (N := N)).le hx.1
  have h4 := mul_le_of_le_one_right (slope_pos (N := N)).le hx.2
  exact ⟨by nlinarith [ht.1, ht.2, offset_pos i, mul_nonneg (sub_nonneg.2 ht.2.le) hf.1],
    by nlinarith [ht.1, ht.2, offset_add_slope_lt_one i, mul_nonneg (sub_nonneg.2 ht.2.le) (sub_nonneg.2 hf.2)]⟩

theorem exists_compT_ofReal {t : ℝ} (ht : t ∈ I) (w : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    ∃ y ∈ I, compT Φ t w x = y := by
  induction w with
  | nil => exact ⟨x, hx, rfl⟩
  | cons i w ih =>
    obtain ⟨y, hy, hyx⟩ := ih
    refine ⟨(homotopy Φ t i y).re, re_homotopy_mem_I Φ ht i hy, ?_⟩
    change homotopy Φ t i (compT Φ t w x) = _
    rw [hyx]
    exact Complex.ext rfl (by simpa using im_homotopy_ofReal Φ t i (ofReal_mem_nbhd (by linarith [Φ.ε_pos]) hy))

theorem re_compT_one_cons_mem (i : Fin N) (w : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    (compT Φ 1 (i :: w) x).re ∈ Icc (offset i) (offset i + slope N) := by
  obtain ⟨y, hy, hyx⟩ := exists_compT_ofReal Φ (t := 1) ⟨zero_le_one, le_rfl⟩ w hx
  rw [Complex.ofReal_one] at hyx
  change (homotopy Φ 1 i (compT Φ 1 w x)).re ∈ _
  rw [hyx]
  simp only [homotopy, sub_self, zero_mul, one_mul, zero_add, target]
  have h3 := mul_nonneg (slope_pos (N := N)).le hy.1
  have h4 := mul_le_of_le_one_right (slope_pos (N := N)).le hy.2
  norm_cast; exact ⟨by linarith, by linarith⟩

theorem exists_compT_one_ne (u v : List (Fin N)) (huv : u ≠ v) :
    ∃ x ∈ I, compT Φ 1 u x ≠ compT Φ 1 v x := by
  have h0 : (0 : ℝ) ∈ I := ⟨le_rfl, zero_le_one⟩
  have hpos : ∀ i w, 0 < (compT Φ 1 (i :: w) ((0 : ℝ) : ℂ)).re := fun i w =>
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
        obtain ⟨x, hx, hne⟩ := ih v fun h => huv (h ▸ rfl)
        refine ⟨x, hx, fun h => hne ?_⟩
        change homotopy Φ 1 i (compT Φ 1 u x) = homotopy Φ 1 i (compT Φ 1 v x) at h
        simp only [homotopy, sub_self, zero_mul, one_mul, zero_add, target] at h
        exact mul_left_cancel₀ (Complex.ofReal_ne_zero.2 slope_pos.ne') (add_right_cancel h)
      · refine ⟨0, h0, fun h => ?_⟩
        have hi := re_compT_one_cons_mem Φ i u h0
        have hj := re_compT_one_cons_mem Φ j v h0
        rw [h] at hi
        rcases lt_or_gt_of_ne hij with hlt | hlt <;>
          linarith [offset_add_slope_lt_offset hlt, hi.1, hi.2, hj.1, hj.2]

theorem hasDerivAt_homotopy (t : ℂ) (i : Fin N) {z : ℂ} (hz : DifferentiableAt ℂ (Φ.f i) z) :
    HasDerivAt (homotopy Φ t i) ((1 - t) * deriv (Φ.f i) z + t * slope N) z :=
  ((hz.hasDerivAt.const_mul (1 - t)).add
    ((((hasDerivAt_id z).const_mul (slope N : ℂ)).add_const (offset i : ℂ)).const_mul t)).congr_deriv (by simp)

theorem deriv_homotopy (t : ℂ) (i : Fin N) {z : ℂ} (hz : z ∈ nbhd (2 * ε)) :
    deriv (homotopy Φ t i) z = (1 - t) * deriv (Φ.f i) z + t * slope N :=
  (hasDerivAt_homotopy Φ t i ((Φ.differentiableOn_f i).differentiableAt ((isOpen_nbhd _).mem_nhds hz))).deriv

theorem inClass_homotopy {t : ℝ} (ht0 : 0 < t) (ht : t * (Φ.cmin + 1) < Φ.cmin) (i : Fin N) :
    InClass ε (homotopy Φ t i) := by
  have ht1 : t < 1 := by nlinarith [Φ.cmin_nonneg]
  have ha := slope_pos (N := N); have ha1 := slope_lt_one (N := N)
  have hder : ∀ z ∈ closure (nbhd ε), deriv (homotopy Φ t i) z =
      ((1 - t : ℝ) : ℂ) * deriv (Φ.f i) z + ((t * slope N : ℝ) : ℂ) := fun z hz => by
    rw [deriv_homotopy Φ t i (IFS.closure_nbhd_subset_two hz)]; push_cast; ring
  have hn1 : ∀ z, ‖((1 - t : ℝ) : ℂ) * deriv (Φ.f i) z‖ = (1 - t) * ‖deriv (Φ.f i) z‖ := fun z => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hn2 : ‖((t * slope N : ℝ) : ℂ)‖ = t * slope N := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  refine inClass_of_deriv Φ.ε_pos
    (fun z hz => (hasDerivAt_homotopy Φ t i ((Φ.differentiableOn_f i).differentiableAt
      ((isOpen_nbhd _).mem_nhds hz))).differentiableAt.differentiableWithinAt)
    (fun x hx => im_homotopy_ofReal Φ t i hx)
    (fun x hx => re_homotopy_mem_I Φ ⟨ht0.le, ht1.le⟩ i hx) ?_ ?_
  · intro z hz h0
    have h := norm_sub_le
      (((1 - t : ℝ) : ℂ) * deriv (Φ.f i) z + ((t * slope N : ℝ) : ℂ)) ((t * slope N : ℝ) : ℂ)
    rw [add_sub_cancel_right, ← hder z hz, h0, norm_zero, hn1, hn2] at h
    nlinarith [mul_le_mul_of_nonneg_left (Φ.cmin_le_norm_deriv i hz) (by linarith : (0 : ℝ) ≤ 1 - t),
      mul_lt_mul_of_pos_left ha1 ht0]
  · intro z hz
    rw [hder z hz]
    refine (norm_add_le _ _).trans_lt ?_
    rw [hn1, hn2]
    nlinarith [mul_lt_mul_of_pos_left ((Φ.inClass i).norm_deriv_lt_one z hz) (by linarith : (0 : ℝ) < 1 - t),
      mul_lt_mul_of_pos_left ha1 ht0]

theorem exists_deriv_deriv_bound :
    ∃ K, 0 ≤ K ∧ ∀ i, ∀ x ∈ I, ‖deriv (deriv (Φ.f i)) x‖ ≤ K := by
  have hO := isOpen_nbhd (2 * ε)
  have h : ∀ i, ∃ C, ∀ z ∈ ((↑) : ℝ → ℂ) '' I, ‖deriv (deriv (Φ.f i)) z‖ ≤ C := fun i =>
    isCompact_image_I.exists_bound_of_continuousOn
      ((((Φ.differentiableOn_f i).deriv hO).deriv hO).continuousOn.mono
        fun _ ⟨x, hx, he⟩ => he ▸ ofReal_mem_nbhd (by linarith [Φ.ε_pos]) hx)
  choose C hC using h
  exact ⟨∑ i, |C i|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun i x hx =>
    (hC i x (mem_image_of_mem _ hx)).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun j => |C j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)))⟩

theorem d2Map_homotopy_le (i : Fin N) {K : ℝ} (hK : 0 ≤ K)
    (hK' : ∀ x ∈ I, ‖deriv (deriv (Φ.f i)) x‖ ≤ K) {t : ℝ} (ht : t ∈ I) :
    d2Map (Φ.f i) (homotopy Φ t i) ≤ t * (4 + K) := by
  have hmem : ∀ x : I, ((x : ℝ) : ℂ) ∈ nbhd (2 * ε) := fun x => ofReal_mem_nbhd (by linarith [Φ.ε_pos]) x.2
  have hnt : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_of_nonneg ht.1]
  have e0 : ∀ x : I, ‖Φ.f i ((x : ℝ) : ℂ) - homotopy Φ t i ((x : ℝ) : ℂ)‖ ≤ t * 2 := fun x => by
    have hre := (Φ.inClass i).re_mem_I x x.2
    have hf : ‖Φ.f i ((x : ℝ) : ℂ)‖ ≤ 1 := by
      rw [← Complex.re_add_im (Φ.f i _), Φ.im_f_ofReal i (hmem x), Complex.ofReal_zero, zero_mul,
        add_zero, Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.2 ⟨by linarith [hre.1], hre.2⟩
    have hh : ‖target i ((x : ℝ) : ℂ)‖ ≤ 1 := by
      rw [show target i ((x : ℝ) : ℂ) = ((slope N * x + offset i : ℝ) : ℂ) by simp [target],
        Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.2 ⟨by linarith [mul_nonneg (slope_pos (N := N)).le x.2.1, offset_pos i],
        by linarith [mul_le_of_le_one_right (slope_pos (N := N)).le x.2.2, offset_add_slope_lt_one i]⟩
    rw [show Φ.f i ((x : ℝ) : ℂ) - homotopy Φ t i ((x : ℝ) : ℂ) =
      t * (Φ.f i ((x : ℝ) : ℂ) - target i ((x : ℝ) : ℂ)) by unfold homotopy; ring, norm_mul, hnt]
    exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (by linarith)) ht.1
  have e1 : ∀ x : I, ‖deriv (Φ.f i) ((x : ℝ) : ℂ) - deriv (homotopy Φ t i) ((x : ℝ) : ℂ)‖ ≤ t * 2 := fun x => by
    have h1 := (Φ.inClass i).norm_deriv_lt_one _ (subset_closure (ofReal_mem_nbhd Φ.ε_pos x.2))
    have h2 : ‖(slope N : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg slope_pos.le]; exact slope_lt_one.le
    rw [show deriv (Φ.f i) ((x : ℝ) : ℂ) - deriv (homotopy Φ t i) ((x : ℝ) : ℂ) =
      t * (deriv (Φ.f i) ((x : ℝ) : ℂ) - slope N) by rw [deriv_homotopy Φ t i (hmem x)]; ring, norm_mul, hnt]
    exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (by linarith)) ht.1
  have e2 : ∀ x : I, ‖deriv (deriv (Φ.f i)) ((x : ℝ) : ℂ) -
      deriv (deriv (homotopy Φ t i)) ((x : ℝ) : ℂ)‖ ≤ t * K := fun x => by
    have heq : deriv (homotopy Φ t i) =ᶠ[𝓝 ((x : ℝ) : ℂ)]
        fun z => (1 - t) * deriv (Φ.f i) z + t * slope N :=
      Filter.eventuallyEq_of_mem ((isOpen_nbhd _).mem_nhds (hmem x)) fun _ hz => deriv_homotopy Φ t i hz
    rw [heq.deriv_eq, deriv_add_const,
      deriv_const_mul _ (((Φ.differentiableOn_f i).deriv (isOpen_nbhd _)).differentiableAt
        ((isOpen_nbhd _).mem_nhds (hmem x))),
      show deriv (deriv (Φ.f i)) ((x : ℝ) : ℂ) - (1 - t) * deriv (deriv (Φ.f i)) ((x : ℝ) : ℂ) =
        t * deriv (deriv (Φ.f i)) ((x : ℝ) : ℂ) by ring, norm_mul, hnt]
    exact mul_le_mul_of_nonneg_left (hK' x x.2) ht.1
  have := ht.1
  unfold d2Map
  linarith [Real.iSup_le e0 (by positivity), Real.iSup_le e1 (by positivity), Real.iSup_le e2 (by positivity)]

theorem finite_compT_eq {u v : List (Fin N)} {x : ℝ} (hx : x ∈ I)
    (hne : compT Φ 1 u x ≠ compT Φ 1 v x) :
    {t : ℝ | t ∈ I ∧ compT Φ t u x = compT Φ t v x}.Finite := by
  have hd_word : ∀ w : List (Fin N), ∃ O : Set ℂ, IsOpen O ∧ ((↑) : ℝ → ℂ) '' I ⊆ O ∧
      DifferentiableOn ℂ (fun t => compT Φ t w x) O := by
    intro w; induction w with
    | nil => exact ⟨univ, isOpen_univ, subset_univ _, differentiableOn_const _⟩
    | cons i w ih =>
      obtain ⟨O, hO, hIO, hd⟩ := ih
      refine ⟨O ∩ (fun t => compT Φ t w x) ⁻¹' nbhd (2 * ε),
        hd.continuousOn.isOpen_inter_preimage hO (isOpen_nbhd _), ?_, ?_⟩
      · rintro _ ⟨s, hs, rfl⟩
        obtain ⟨y, hy, hyx⟩ := exists_compT_ofReal Φ hs w hx
        refine ⟨hIO (mem_image_of_mem _ hs), ?_⟩
        show compT Φ s w x ∈ nbhd (2 * ε)
        rw [hyx]; exact ofReal_mem_nbhd (by linarith [Φ.ε_pos]) hy
      · have hg := hd.mono (inter_subset_left (t := (fun t => compT Φ t w x) ⁻¹' nbhd (2 * ε)))
        have hf : DifferentiableOn ℂ (fun t => Φ.f i (compT Φ t w x))
            (O ∩ (fun t => compT Φ t w x) ⁻¹' nbhd (2 * ε)) :=
          (Φ.differentiableOn_f i).comp hg fun _ ht => ht.2
        show DifferentiableOn ℂ
          (fun t => (1 - t) * Φ.f i (compT Φ t w x) + t * (slope N * compT Φ t w x + offset i)) _
        fun_prop
  obtain ⟨Ou, hOu, hIu, hdu⟩ := hd_word u
  obtain ⟨Ov, hOv, hIv, hdv⟩ := hd_word v
  obtain ⟨ρ, hρ, hsub⟩ :=
    isCompact_image_I.exists_thickening_subset_open (hOu.inter hOv) (subset_inter hIu hIv)
  rw [← nbhd_eq_thickening] at hsub
  exact (finite_zeros hρ ((hdu.mono (hsub.trans inter_subset_left)).sub
    (hdv.mono (hsub.trans inter_subset_right))) ⟨1, ⟨zero_le_one, le_rfl⟩, by simpa [sub_eq_zero] using hne⟩).subset
    fun _ ⟨ht, heq⟩ => ⟨ht, sub_eq_zero.2 heq⟩

end IFS.Coincidences

namespace IFS

open Coincidences

variable {N : ℕ} {ε : ℝ}

theorem exists_noCoincidence_near (Φ : IFS N ε) {r : ℝ} (hr : 0 < r) :
    ∃ Ψ : IFS N ε, d2 Φ Ψ < r ∧ (∀ i, ∀ x ∈ I, (Ψ.f i x).re ∈ Ioo 0 1) ∧ Ψ.NoCoincidence := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hw : ∀ w : List (Fin 0), w = [] := fun | [] => rfl | i :: _ => i.elim0
    exact ⟨Φ, by rwa [d2, Challenge.d2, Real.iSup_of_isEmpty], fun i => i.elim0, fun u v huv => absurd (by rw [hw u, hw v]) huv⟩
  have hc : 0 < Φ.cmin := Φ.cmin_pos hN
  obtain ⟨K, hK, hK'⟩ := exists_deriv_deriv_bound Φ
  set B : Set ℝ := ⋃ p : List (Fin N) × List (Fin N),
    {t | t ∈ I ∧ p.1 ≠ p.2 ∧ ∀ x ∈ I, compT Φ t p.1 x = compT Φ t p.2 x}
  have hB : B.Countable := countable_iUnion fun p => Finite.countable <| by
    by_cases hp : p.1 = p.2
    · simp [hp]
    · obtain ⟨x, hx, hne⟩ := exists_compT_one_ne Φ p.1 p.2 hp
      exact (finite_compT_eq Φ hx hne).subset fun _ ht => ⟨ht.1, ht.2.2 x hx⟩
  obtain ⟨t, htB, ht⟩ := (hB.dense_compl ℝ).exists_mem_open isOpen_Ioo
    (nonempty_Ioo.2 (lt_min (by positivity : 0 < Φ.cmin / (Φ.cmin + 1)) (by positivity : 0 < r / (4 + K))))
  have ht1 : t * (Φ.cmin + 1) < Φ.cmin := (lt_div_iff₀ (by positivity)).1 (ht.2.trans_le (min_le_left _ _))
  have ht2 : t * (4 + K) < r := (lt_div_iff₀ (by positivity)).1 (ht.2.trans_le (min_le_right _ _))
  have ht_lt : t < 1 := by nlinarith [ht.1]
  let Ψ : IFS N ε := ⟨homotopy Φ t, Φ.ε_pos, inClass_homotopy Φ ht.1 ht1⟩
  refine ⟨Ψ, (Real.iSup_le (fun i => d2Map_homotopy_le Φ i hK (hK' i) ⟨ht.1.le, ht_lt.le⟩)
    (mul_nonneg ht.1.le (by linarith))).trans_lt ht2,
    fun i x hx => re_homotopy_mem_Ioo Φ ⟨ht.1, ht_lt⟩ i hx, fun u v huv => ?_⟩
  by_contra! h
  exact htB (mem_iUnion.2 ⟨(u, v), ⟨ht.1.le, ht_lt.le⟩, huv, h⟩)

end IFS

namespace IFS.Continuity

theorem ofReal_mem_closure {δ : ℝ} (hδ : 0 < δ) {x : ℝ} (hx : x ∈ I) :
    (x : ℂ) ∈ closure (nbhd δ) := subset_closure (ofReal_mem_nbhd hδ hx)

def ContJet (F : ℂ → ℂ) : Prop :=
  Continuous (fun x : I => F x) ∧ Continuous (fun x : I => deriv F x) ∧
    Continuous (fun x : I => deriv (deriv F) x)

theorem InClass.contJet {ε : ℝ} (hε : 0 < ε) {f : ℂ → ℂ} (hf : InClass ε f) : ContJet f := by
  have hO := isOpen_nbhd (2 * ε)
  have hc : Continuous fun x : I => ((x : ℝ) : ℂ) := Complex.continuous_ofReal.comp continuous_subtype_val
  have hm : ∀ x : I, ((x : ℝ) : ℂ) ∈ nbhd (2 * ε) := fun x => ofReal_mem_nbhd (by positivity) x.2
  exact ⟨hf.differentiableOn.continuousOn.comp_continuous hc hm,
    (hf.differentiableOn.deriv hO).continuousOn.comp_continuous hc hm,
    ((hf.differentiableOn.deriv hO).deriv hO).continuousOn.comp_continuous hc hm⟩

theorem bddAbove_norm_sub {F G : ℂ → ℂ} (hF : Continuous fun x : I => F x)
    (hG : Continuous fun x : I => G x) :
    BddAbove (range fun x : I => ‖F ((x : ℝ) : ℂ) - G ((x : ℝ) : ℂ)‖) :=
  (isCompact_range (hF.sub hG).norm).bddAbove

variable {N : ℕ} {ε ε' : ℝ}

theorem d2_nonneg (Φ : IFS N ε) (Ψ : IFS N ε') : 0 ≤ d2 Φ Ψ :=
  Real.iSup_nonneg fun _ => add_nonneg (add_nonneg (Real.iSup_nonneg fun _ => norm_nonneg _)
    (Real.iSup_nonneg fun _ => norm_nonneg _)) (Real.iSup_nonneg fun _ => norm_nonneg _)

theorem norm_sub_le_d2 (Φ : IFS N ε) (Ψ : IFS N ε') (i : Fin N) {x : ℝ} (hx : x ∈ I) :
    ‖Φ.f i x - Ψ.f i x‖ ≤ d2 Φ Ψ ∧ ‖deriv (Φ.f i) x - deriv (Ψ.f i) x‖ ≤ d2 Φ Ψ ∧
      ‖deriv (deriv (Φ.f i)) x - deriv (deriv (Ψ.f i)) x‖ ≤ d2 Φ Ψ := by
  obtain ⟨f0, f1, f2⟩ := InClass.contJet Φ.ε_pos (Φ.inClass i)
  obtain ⟨g0, g1, g2⟩ := InClass.contJet Ψ.ε_pos (Ψ.inClass i)
  have e0 := le_ciSup (bddAbove_norm_sub f0 g0) ⟨x, hx⟩
  have e1 := le_ciSup (bddAbove_norm_sub f1 g1) ⟨x, hx⟩
  have e2 := le_ciSup (bddAbove_norm_sub f2 g2) ⟨x, hx⟩
  have hd : d2Map (Φ.f i) (Ψ.f i) ≤ d2 Φ Ψ :=
    le_ciSup (f := fun j => d2Map (Φ.f j) (Ψ.f j)) (Set.finite_range _).bddAbove i
  unfold d2Map at hd
  exact ⟨by linarith [(norm_nonneg _).trans e1, (norm_nonneg _).trans e2],
    by linarith [(norm_nonneg _).trans e0, (norm_nonneg _).trans e2],
    by linarith [(norm_nonneg _).trans e0, (norm_nonneg _).trans e1]⟩

end IFS.Continuity

namespace IFS

open Continuity

variable {N : ℕ} {ε : ℝ}

private theorem exists_uniform_dualTerm_bound (hN : 0 < N) (Φ : IFS N ε) :
    ∃ M' c' δ₀ : ℝ, 0 ≤ M' ∧ 0 ≤ c' ∧ c' < 1 ∧ 0 < δ₀ ∧
      ∀ {ε' : ℝ} (Ψ : IFS N ε'), d2 Φ Ψ < δ₀ → ∀ (u : ℕ → Fin N) (n : ℕ), ∀ x ∈ I,
        ‖Ψ.dualTerm (.inf u) n x‖ ≤ M' * c' ^ n := by
  obtain ⟨K₂, hK₂0, hK₂⟩ := Coincidences.exists_deriv_deriv_bound Φ
  have hm := Φ.cmin_pos hN; have hc1 := Φ.cmax_lt_one
  set δ₀ := min ((1 - Φ.cmax) / 2) (min (Φ.cmin / 2) 1)
  set c' := (1 + Φ.cmax) / 2
  set M' := (K₂ + 1) / (Φ.cmin / 2)
  have hc'0 : 0 ≤ c' := by dsimp [c']; linarith [Φ.cmax_nonneg]
  refine ⟨M', c', δ₀, by positivity, hc'0, by dsimp [c']; linarith,
    lt_min (by linarith) (lt_min (by linarith) one_pos), fun Ψ hΨ u n x hx => ?_⟩
  have hder : ∀ i, ∀ y ∈ I, ‖deriv (Ψ.f i) (y : ℂ)‖ ≤ c' := fun i y hy => by
    have ht := norm_sub_norm_le (deriv (Ψ.f i) y) (deriv (Φ.f i) y)
    rw [norm_sub_rev] at ht; dsimp [c']
    linarith [(norm_sub_le_d2 Φ Ψ i hy).2.1,
      Φ.norm_deriv_le_cmax i (ofReal_mem_closure Φ.ε_pos hy), hΨ.trans_le (min_le_left _ _)]
  have hnl : ∀ i, ∀ y ∈ I, ‖Ψ.nonlin i y‖ ≤ M' := fun i y hy => by
    obtain ⟨-, e1, e2⟩ := norm_sub_le_d2 Φ Ψ i hy
    have hlo : Φ.cmin / 2 ≤ ‖deriv (Ψ.f i) y‖ := by
      linarith [Φ.cmin_le_norm_deriv i (ofReal_mem_closure Φ.ε_pos hy),
        norm_sub_norm_le (deriv (Φ.f i) y) (deriv (Ψ.f i) y),
        hΨ.trans_le ((min_le_right _ _).trans (min_le_left _ _))]
    have hhi : ‖deriv (deriv (Ψ.f i)) y‖ ≤ K₂ + 1 := by
      have ht := norm_sub_norm_le (deriv (deriv (Ψ.f i)) y) (deriv (deriv (Φ.f i)) y)
      rw [norm_sub_rev] at ht
      linarith [hK₂ i y hy, hΨ.trans_le ((min_le_right _ _).trans (min_le_right _ _))]
    rw [nonlin, norm_div]
    exact div_le_div₀ (by positivity) hhi (half_pos hm) hlo
  have hpow : ∀ v : List (Fin N), ‖deriv (Ψ.comp v) x‖ ≤ c' ^ v.length := fun v => by
    induction v with
    | nil => simp [comp_nil]
    | cons i w ih =>
      rw [Ψ.deriv_comp_cons i w (ofReal_mem_closure Ψ.ε_pos hx), Ψ.comp_ofReal w hx, norm_mul,
        List.length_cons, pow_succ']
      exact mul_le_mul (hder i _ (Ψ.re_comp_mem_I w hx)) ih (norm_nonneg _) hc'0
  set v := (List.ofFn fun k : Fin n => u k).reverse
  change ‖Ψ.nonlin (u n) (Ψ.comp v x) * deriv (Ψ.comp v) x‖ ≤ M' * c' ^ n
  rw [norm_mul, Ψ.comp_ofReal v hx]
  exact mul_le_mul (hnl (u n) _ (Ψ.re_comp_mem_I v hx))
    ((by simp [v] : v.length = n) ▸ hpow v) (norm_nonneg _) (by positivity)

theorem lemma_2_7_union (Φ : IFS N ε) (h : Φ.DualSSC) :
    ∃ δ > 0, ∀ {ε' : ℝ} (Ψ : IFS N ε'), d2 Φ Ψ < δ → Ψ.DualSSC := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨1, one_pos, fun _ _ i => (i 0).elim0⟩
  by_contra! hcon
  have hseq : ∀ k : ℕ, ∃ ε' : ℝ, ∃ Ψ : IFS N ε', d2 Φ Ψ < 1 / (k + 1 : ℝ) ∧
      ∃ i j : ℕ → Fin N, i 0 ≠ j 0 ∧ ∀ x ∈ I, Ψ.dualProj (.inf i) x = Ψ.dualProj (.inf j) x :=
    fun k => by simpa [DualSSC] using hcon (1 / (k + 1 : ℝ)) (by positivity)
  choose εk hrest using hseq
  choose Ψk hd2 ik jk h0_ne heq using hrest
  obtain ⟨⟨i₀, j₀⟩, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq fun k => (ik k, jk k)
  let Ψ' (k : ℕ) : IFS N (εk (φ k)) := Ψk (φ k)
  have hd0 : Tendsto (fun k => d2 Φ (Ψ' k)) atTop (𝓝 0) :=
    squeeze_zero (fun k => d2_nonneg Φ (Ψ' k))
      (fun k => (hd2 (φ k)).le.trans (one_div_le_one_div_of_le (by positivity)
        (by exact_mod_cast Nat.add_le_add_right (hφ.id_le k) 1)))
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hcoord : ∀ m, ∀ᶠ k in atTop, ik (φ k) m = i₀ m ∧ jk (φ k) m = j₀ m := fun m => by
    have h1 := (((continuous_apply m).comp continuous_fst).tendsto (i₀, j₀)).comp hlim
    have h2 := (((continuous_apply m).comp continuous_snd).tendsto (i₀, j₀)).comp hlim
    rw [nhds_discrete, tendsto_pure] at h1 h2
    exact h1.and h2
  obtain ⟨k₀, hi0, hj0⟩ := (hcoord 0).exists
  obtain ⟨x, hx, hne⟩ := h i₀ j₀ (hi0 ▸ hj0 ▸ h0_ne (φ k₀))
  have htend : ∀ (F : ℂ → ℂ) (G : ℕ → ℂ → ℂ) {y : ℕ → ℝ} {y₀ : ℝ},
      ContinuousAt F y₀ → Tendsto y atTop (𝓝 y₀) →
      (∀ k, ‖F (y k) - G k (y k)‖ ≤ d2 Φ (Ψ' k)) →
      Tendsto (fun k => G k (y k)) atTop (𝓝 (F y₀)) :=
    fun F G {y y₀} hFc hy hFG => by
      have hsub : Tendsto (fun k => G k (y k) - F (y k)) atTop (𝓝 0) :=
        squeeze_zero_norm (fun k => by rw [norm_sub_rev]; exact hFG k) hd0
      simpa using hsub.add (hFc.tendsto.comp ((Complex.continuous_ofReal.tendsto y₀).comp hy))
  have hjet : ∀ (m : Fin N) {y : ℕ → ℝ} {y₀ : ℝ}, y₀ ∈ I → (∀ k, y k ∈ I) → Tendsto y atTop (𝓝 y₀) →
      Tendsto (fun k => (Ψ' k).f m (y k)) atTop (𝓝 (Φ.f m y₀)) ∧
        Tendsto (fun k => deriv ((Ψ' k).f m) (y k)) atTop (𝓝 (deriv (Φ.f m) y₀)) ∧
        Tendsto (fun k => deriv (deriv ((Ψ' k).f m)) (y k)) atTop (𝓝 (deriv (deriv (Φ.f m)) y₀)) :=
    fun m {y y₀} hy₀ hyI hy => by
      have hO := isOpen_nbhd (2 * ε)
      have hm := hO.mem_nhds (ofReal_mem_nbhd (by linarith [Φ.ε_pos]) hy₀)
      have hf := Φ.differentiableOn_f m
      exact ⟨htend _ _ (hf.continuousOn.continuousAt hm) hy fun k => (norm_sub_le_d2 Φ (Ψ' k) m (hyI k)).1,
        htend _ _ ((hf.deriv hO).continuousOn.continuousAt hm) hy fun k => (norm_sub_le_d2 Φ (Ψ' k) m (hyI k)).2.1,
        htend _ _ (((hf.deriv hO).deriv hO).continuousOn.continuousAt hm) hy fun k => (norm_sub_le_d2 Φ (Ψ' k) m (hyI k)).2.2⟩
  have hcomp : ∀ v : List (Fin N),
      Tendsto (fun k => ((Ψ' k).comp v x).re) atTop (𝓝 (Φ.comp v x).re) ∧
        Tendsto (fun k => deriv ((Ψ' k).comp v) x) atTop (𝓝 (deriv (Φ.comp v) x)) := fun v => by
    induction v with
    | nil => simp
    | cons m w ih =>
      obtain ⟨hc, hd⟩ := ih
      obtain ⟨t0, t1, -⟩ := hjet m (Φ.re_comp_mem_I w hx) (fun k => (Ψ' k).re_comp_mem_I w hx) hc
      have lim0 := (Complex.continuous_re.tendsto _).comp t0
      rw [← Φ.comp_ofReal w hx] at lim0
      have lim1 := t1.mul hd
      rw [← Φ.comp_ofReal w hx, ← Φ.deriv_comp_cons m w (ofReal_mem_closure Φ.ε_pos hx)] at lim1
      refine ⟨lim0.congr fun k => ?_, lim1.congr fun k => ?_⟩
      · show (((Ψ' k).f m (((Ψ' k).comp w x).re : ℂ)).re) = ((Ψ' k).f m ((Ψ' k).comp w x)).re
        rw [← (Ψ' k).comp_ofReal w hx]
      · rw [← (Ψ' k).comp_ofReal w hx, ← (Ψ' k).deriv_comp_cons m w (ofReal_mem_closure (Ψ' k).ε_pos hx)]
  obtain ⟨M', c', δ₀, -, hc'0, hc'1, hδ₀, hbd⟩ := exists_uniform_dualTerm_bound hN Φ
  have hproj : ∀ (u' : ℕ → ℕ → Fin N) (u₀ : ℕ → Fin N),
      (∀ m, ∀ᶠ k in atTop, u' k m = u₀ m) →
      Tendsto (fun k => (Ψ' k).dualProj (.inf (u' k)) x) atTop (𝓝 (Φ.dualProj (.inf u₀) x)) :=
    fun u' u₀ hu' => by
      refine tendsto_tsum_of_dominated_convergence
        ((summable_geometric_of_lt_one hc'0 hc'1).mul_left M') (fun n => ?_)
        ((hd0.eventually (gt_mem_nhds hδ₀)).mono fun k hk n => hbd (Ψ' k) hk (u' k) n x hx)
      set v := (List.ofFn fun m : Fin n => u₀ m).reverse
      obtain ⟨hc, hd⟩ := hcomp v
      obtain ⟨-, t1, t2⟩ := hjet (u₀ n) (Φ.re_comp_mem_I v hx) (fun k => (Ψ' k).re_comp_mem_I v hx) hc
      have hne0 := (Φ.inClass (u₀ n)).deriv_ne_zero _ (ofReal_mem_closure Φ.ε_pos (Φ.re_comp_mem_I v hx))
      have hterm : Tendsto (fun k => (Ψ' k).nonlin (u₀ n) ((Ψ' k).comp v x) * deriv ((Ψ' k).comp v) x)
          atTop (𝓝 (Φ.dualTerm (.inf u₀) n x)) := by
        have hlim_nl := (t2.div t1 hne0).mul hd
        rw [show deriv (deriv (Φ.f (u₀ n))) ((Φ.comp v x).re : ℂ) / deriv (Φ.f (u₀ n)) ((Φ.comp v x).re : ℂ) *
            deriv (Φ.comp v) x = Φ.dualTerm (.inf u₀) n x by
          simp only [dualTerm, Word.get?_inf, Word.take_inf, nonlin, ← Φ.comp_ofReal v hx]; rfl] at hlim_nl
        exact hlim_nl.congr fun k => by dsimp only [Pi.div_apply, nonlin]; rw [← (Ψ' k).comp_ofReal v hx]
      refine hterm.congr' ?_
      filter_upwards [eventually_all.2 fun m : Fin n => hu' m, hu' n] with k hpre hlast
      have hv : (List.ofFn fun m : Fin n => u' k m).reverse = v :=
        congrArg List.reverse (congrArg List.ofFn (funext hpre))
      simp only [dualTerm, Word.get?_inf, Word.take_inf, hlast, hv]
  exact hne (tendsto_nhds_unique
    ((hproj (fun k => ik (φ k)) i₀ fun m => (hcoord m).mono fun _ hc => hc.1).congr
      fun k => heq (φ k) x hx)
    (hproj (fun k => jk (φ k)) j₀ fun m => (hcoord m).mono fun _ hc => hc.2))

end IFS

def AgreeAt (f g : ℂ → ℂ) (y : ℂ) : Prop :=
  g y = f y ∧ deriv g y = deriv f y ∧ deriv (deriv g) y = deriv (deriv f) y

namespace MultiplicativeBump

private noncomputable def φ0 (s : ℝ) : ℝ := s ^ 2 * Real.exp (-s ^ 2)
private noncomputable def φ1 (s : ℝ) : ℝ := (2 * s - 2 * s ^ 3) * Real.exp (-s ^ 2)
private noncomputable def φ2 (s : ℝ) : ℝ := (2 - 10 * s ^ 2 + 4 * s ^ 4) * Real.exp (-s ^ 2)

private lemma hasDerivAt_φ (s : ℝ) :
    HasDerivAt φ0 (φ1 s) s ∧ HasDerivAt φ1 (φ2 s) s :=
  ⟨(((hasDerivAt_id' s).fun_pow 2).fun_mul
      (((hasDerivAt_id' s).fun_pow 2).fun_neg.exp)).congr_deriv (by simp only [φ1]; push_cast; ring),
   (((((hasDerivAt_id' s).const_mul 2).fun_sub
      (((hasDerivAt_id' s).fun_pow 3).const_mul 2)).fun_mul
      (((hasDerivAt_id' s).fun_pow 2).fun_neg.exp))).congr_deriv (by simp only [φ2]; push_cast; ring)⟩

private lemma mul_exp_neg_le {a C u : ℝ} (h : a ≤ C * Real.exp u) : a * Real.exp (-u) ≤ C :=
  (mul_le_mul_of_nonneg_right h (Real.exp_pos _).le).trans_eq
    (by rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one])

private lemma φ_bounds (s : ℝ) :
    |φ0 s| ≤ 1 ∧ |φ1 s| ≤ 10 ∧ |φ2 s| ≤ 20 ∧ s ^ 2 * |φ2 s| ≤ 64 := by
  set u := s ^ 2 with hu_def
  have hu0 : 0 ≤ u := sq_nonneg s
  have he : (1 + u / 2 + (u / 2) ^ 2 / 2) ^ 2 ≤ Real.exp u :=
    (pow_le_pow_left₀ (by positivity) (Real.quadratic_le_exp_of_nonneg (by positivity)) 2).trans_eq
      (by rw [← Real.exp_nat_mul]; congr 1; ring)
  have ha1 : |2 * s - 2 * s ^ 3| ≤ 2 + 4 * u + 2 * u ^ 2 := abs_le.2
    ⟨by nlinarith [sq_nonneg (1 + s), sq_nonneg (s * (1 - s))],
     by nlinarith [sq_nonneg (1 - s), sq_nonneg (s * (1 + s))]⟩
  have ha2 : |2 - 10 * u + 4 * u ^ 2| ≤ 2 + 10 * u + 4 * u ^ 2 := abs_le.2
    ⟨by nlinarith [sq_nonneg u], by nlinarith [sq_nonneg u]⟩
  have hn0 : |φ0 s| = u * Real.exp (-u) := abs_of_nonneg (by unfold φ0; positivity)
  have hn1 : |φ1 s| = |2 * s - 2 * s ^ 3| * Real.exp (-u) := by
    unfold φ1; rw [abs_mul, abs_of_pos (Real.exp_pos _), hu_def]
  have hn2 : |φ2 s| = |2 - 10 * u + 4 * u ^ 2| * Real.exp (-u) := by
    unfold φ2; rw [abs_mul, abs_of_pos (Real.exp_pos _), show s ^ 4 = u ^ 2 by rw [hu_def]; ring, hu_def]
  exact ⟨hn0 ▸ mul_exp_neg_le (by nlinarith [sq_nonneg u, sq_nonneg (u ^ 2)]),
    hn1 ▸ mul_exp_neg_le (by nlinarith [sq_nonneg u, sq_nonneg (u ^ 2)]),
    hn2 ▸ mul_exp_neg_le (by nlinarith [sq_nonneg u, sq_nonneg (u ^ 2)]),
    by rw [hn2, ← mul_assoc]; exact mul_exp_neg_le
         (by nlinarith [mul_le_mul_of_nonneg_left ha2 hu0, sq_nonneg u, sq_nonneg (u ^ 2)])⟩

private noncomputable def lagrange (S : Finset ℝ) (y : ℝ) (z : ℂ) : ℂ :=
  ∏ w ∈ S.erase y, ((z - w) / ((y : ℂ) - w)) ^ 3

private lemma differentiable_lagrange (S : Finset ℝ) (y : ℝ) : Differentiable ℂ (lagrange S y) := by
  unfold lagrange; fun_prop

private lemma lagrange_self (S : Finset ℝ) (y : ℝ) : lagrange S y y = 1 :=
  Finset.prod_eq_one fun w hw => by
    simp [div_self (sub_ne_zero.2 fun h => (Finset.ne_of_mem_erase hw).symm (Complex.ofReal_injective h))]

private lemma lagrange_other {S : Finset ℝ} {y w : ℝ} (hw : w ∈ S.erase y) :
    lagrange S y w = 0 ∧ deriv (lagrange S y) w = 0 ∧ deriv (deriv (lagrange S y)) w = 0 := by
  let R : ℂ → ℂ := fun z =>
    (1 / ((y : ℂ) - w) ^ 3) * ∏ v ∈ (S.erase y).erase w, ((z - v) / ((y : ℂ) - v)) ^ 3
  have hR : Differentiable ℂ R := by dsimp [R]; fun_prop
  have hR' : Differentiable ℂ (deriv R) := differentiableOn_univ.1 (hR.differentiableOn.deriv isOpen_univ)
  have hfun : lagrange S y = fun z => (z - w) ^ 3 * R z := by
    ext z; dsimp [R]; rw [lagrange, ← Finset.mul_prod_erase _ _ hw, div_pow]; ring
  have hd1 : ∀ z, HasDerivAt (fun z => (z - w) ^ 3 * R z)
      (3 * (z - w) ^ 2 * R z + (z - w) ^ 3 * deriv R z) z := fun z =>
    ((((hasDerivAt_id' z).sub_const _).fun_pow 3).fun_mul (hR z).hasDerivAt).congr_deriv (by push_cast; ring)
  rw [hfun]
  refine ⟨by simp, by rw [(hd1 w).deriv]; simp, ?_⟩
  rw [show deriv (fun z => (z - w) ^ 3 * R z) = _ from funext fun z => (hd1 z).deriv]
  exact ((((((hasDerivAt_id' (w : ℂ)).sub_const _).fun_pow 2).const_mul 3).fun_mul (hR w).hasDerivAt).fun_add
    ((((hasDerivAt_id' (w : ℂ)).sub_const _).fun_pow 3).fun_mul (hR' w).hasDerivAt)).congr_deriv
    (by simp [sub_self]) |>.deriv

private lemma entire_real_jet {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {H0 H1 H2 : ℝ → ℝ} (h0 : ∀ x : ℝ, h x = H0 x)
    (hd0 : ∀ x, HasDerivAt H0 (H1 x) x) (hd1 : ∀ x, HasDerivAt H1 (H2 x) x) (x : ℝ) :
    deriv h x = H1 x ∧ deriv (deriv h) x = H2 x := by
  have h1 : ∀ t : ℝ, deriv h t = H1 t := fun t =>
    ((hh t).hasDerivAt.comp_ofReal).unique (((hd0 t).ofReal_comp).congr_of_eventuallyEq
      (Eventually.of_forall h0))
  have hh' : Differentiable ℂ (deriv h) := differentiableOn_univ.1 (hh.differentiableOn.deriv isOpen_univ)
  exact ⟨h1 x, ((hh' x).hasDerivAt.comp_ofReal).unique (((hd1 x).ofReal_comp).congr_of_eventuallyEq
    (Eventually.of_forall h1))⟩

end MultiplicativeBump

open MultiplicativeBump in
theorem proposition_4_2 {ε : ℝ} (hε : 0 < ε) {f : ℂ → ℂ} (hf : InClass ε f)
    (hI : ∀ x ∈ I, (f x).re ∈ Ioo 0 1) (Y Z : Finset ℝ) (hY : ∀ y ∈ Y, y ∈ I)
    (hZ : ∀ z ∈ Z, z ∈ I) (hYZ : Disjoint Y Z) {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : ℂ → ℂ, (∃ ε' > 0, InClass ε' g) ∧
      (∀ y ∈ Y, g y = f y ∧ deriv g y = deriv f y ∧
        δ ≤ ‖deriv (deriv g) y / deriv g y - deriv (deriv f) y / deriv f y‖) ∧
      (∀ z ∈ Z, AgreeAt f g z) ∧ d2Map f g ≤ 23 * δ := by
  classical
  have hU := isOpen_nbhd (2 * ε)
  have hmem2 : MapsTo ((↑) : ℝ → ℂ) I (nbhd (2 * ε)) := fun _ hx => ofReal_mem_nbhd (by positivity) hx
  have hf0c : ContinuousOn (fun x : ℝ => (f x).re) I :=
    Complex.continuous_re.comp_continuousOn
      (hf.differentiableOn.continuousOn.comp Complex.continuous_ofReal.continuousOn hmem2)
  have hf1c : ContinuousOn (fun x : ℝ => ‖deriv f x‖) I :=
    ((hf.differentiableOn.deriv hU).continuousOn.comp Complex.continuous_ofReal.continuousOn hmem2).norm
  set mar : ℝ → ℝ := fun x =>
    min (min (f x).re (1 - (f x).re)) (min ‖deriv f x‖ (1 - ‖deriv f x‖)) with hmar_def
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0, by norm_num⟩
    ((hf0c.inf (continuousOn_const.sub hf0c)).inf (hf1c.inf (continuousOn_const.sub hf1c)))
  set m := mar x₀ with hm_def
  have hm : 0 < m := by
    have hcl := subset_closure (ofReal_mem_nbhd hε hx₀)
    simp only [hm_def, hmar_def, lt_min_iff]
    exact ⟨⟨(hI x₀ hx₀).1, by linarith [(hI x₀ hx₀).2]⟩,
      norm_pos_iff.2 (hf.deriv_ne_zero x₀ hcl), by linarith [hf.norm_deriv_lt_one x₀ hcl]⟩
  have hmar : ∀ x ∈ I, m ≤ (f x).re ∧ (f x).re ≤ 1 - m ∧ m ≤ ‖deriv f x‖ ∧ ‖deriv f x‖ ≤ 1 - m :=
    fun x hx => by
      have h : m ≤ mar x := isMinOn_iff.1 hmin x hx
      simp only [hmar_def, le_min_iff] at h
      exact ⟨h.1.1, by linarith [h.1.2], h.2.1, by linarith [h.2.2]⟩
  set S := Y ∪ Z
  let q0 (y x : ℝ) : ℝ := (lagrange S y x).re
  let q1 (y x : ℝ) : ℝ := (deriv (lagrange S y) x).re
  let q2 (y x : ℝ) : ℝ := (deriv (deriv (lagrange S y)) x).re
  have hq_diff : ∀ y, Differentiable ℂ (lagrange S y) ∧ Differentiable ℂ (deriv (lagrange S y)) ∧
      Differentiable ℂ (deriv (deriv (lagrange S y))) := fun y => by
    have d0 := differentiable_lagrange S y
    have d1 := differentiableOn_univ.1 (d0.differentiableOn.deriv isOpen_univ)
    exact ⟨d0, d1, differentiableOn_univ.1 (d1.differentiableOn.deriv isOpen_univ)⟩
  have hq_deriv : ∀ y x, HasDerivAt (q0 y) (q1 y x) x ∧ HasDerivAt (q1 y) (q2 y x) x :=
    fun y x => ⟨hasDerivAt_re_ofReal ((hq_diff y).1 x), hasDerivAt_re_ofReal ((hq_diff y).2.1 x)⟩
  let Q (x : ℝ) : ℝ := ∑ y ∈ Y, (|q0 y x| + |q1 y x| + |q2 y x|)
  have hQc : Continuous Q := continuous_finsetSum _ fun y _ => by
    obtain ⟨d0, d1, d2⟩ := hq_diff y
    exact (((Complex.continuous_re.comp (d0.continuous.comp Complex.continuous_ofReal)).abs.add
      (Complex.continuous_re.comp (d1.continuous.comp Complex.continuous_ofReal)).abs).add
      (Complex.continuous_re.comp (d2.continuous.comp Complex.continuous_ofReal)).abs)
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hQc.continuousOn
  set M := max 0 M₀
  have hM0 : 0 ≤ M := le_max_left _ _
  have hQM : ∀ x ∈ I, Q x ≤ M := fun x hx =>
    (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hM₀ x hx).trans (le_max_right 0 M₀))
  have hsep_ev : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → 2 * r < |y - y'| := by
    refine (eventually_all_finset Y).2 fun y _ => (eventually_all_finset Y).2 fun y' _ => ?_
    by_cases hyy : y = y'
    · exact Eventually.of_forall fun _ h => absurd hyy h
    · filter_upwards [Ioo_mem_nhdsGT (half_pos (abs_pos.2 (sub_ne_zero.2 hyy)))] with r hr _
      linarith [hr.2]
  have hnear_ev : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ y ∈ Y, ∀ x : ℝ, |x - y| < r → |q0 y x| ≤ 2 := by
    refine (eventually_all_finset Y).2 fun y _ => ?_
    obtain ⟨r', hr', h'⟩ := Metric.continuousAt_iff.1
      (Complex.continuous_re.comp ((hq_diff y).1.continuous.comp Complex.continuous_ofReal)).continuousAt 1 one_pos
    filter_upwards [Ioo_mem_nhdsGT hr'] with ρ hρ x hx
    have hd := h' (show dist x y < r' by rw [Real.dist_eq]; exact hx.trans hρ.2)
    have hq0y : q0 y y = 1 := by simp [q0, lagrange_self]
    change dist (q0 y x) (q0 y y) < 1 at hd
    rw [hq0y, Real.dist_eq] at hd
    linarith [abs_sub_abs_le_abs_sub (q0 y x) 1, abs_one (α := ℝ)]
  obtain ⟨r, ⟨hr_sep, hr_near⟩, hr0⟩ := ((hsep_ev.and hnear_ev).and self_mem_nhdsWithin).exists
  set τ := min δ (m / 2)
  have hτ : 0 < τ := lt_min hδ (half_pos hm)
  set K := (δ / 2) * M
  set L := 21 + 64 / r ^ 2
  have hK0 : 0 ≤ K := by positivity
  have hL0 : 10 ≤ L := by dsimp [L]; linarith [show 0 ≤ 64 / r ^ 2 by positivity]
  set ρ := min 1 (τ / (K * L + 1))
  have hρ_pos : 0 < ρ := by positivity
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρ2 : ρ ^ 2 ≤ ρ := by nlinarith
  have hρ_lt : K * L * ρ < τ :=
    calc K * L * ρ ≤ K * L * (τ / (K * L + 1)) := mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ < (K * L + 1) * (τ / (K * L + 1)) := mul_lt_mul_of_pos_right (lt_add_one _) (by positivity)
      _ = τ := mul_div_cancel₀ _ (by positivity)
  let bt0 (y x : ℝ) : ℝ := q0 y x * (ρ ^ 2 * φ0 ((x - y) / ρ))
  let bt1 (y x : ℝ) : ℝ := q1 y x * (ρ ^ 2 * φ0 ((x - y) / ρ)) + q0 y x * (ρ * φ1 ((x - y) / ρ))
  let bt2 (y x : ℝ) : ℝ := q2 y x * (ρ ^ 2 * φ0 ((x - y) / ρ)) +
    2 * q1 y x * (ρ * φ1 ((x - y) / ρ)) + q0 y x * φ2 ((x - y) / ρ)
  have hbt_deriv : ∀ y x, HasDerivAt (bt0 y) (bt1 y x) x ∧ HasDerivAt (bt1 y) (bt2 y x) x := fun y x => by
    have hρne := hρ_pos.ne'
    have hw : HasDerivAt (fun u : ℝ => (u - y) / ρ) (1 / ρ) x := by
      simpa using ((hasDerivAt_id' x).sub_const y).div_const ρ
    have he0 : HasDerivAt (fun u => ρ ^ 2 * φ0 ((u - y) / ρ)) (ρ * φ1 ((x - y) / ρ)) x := by
      convert (((hasDerivAt_φ ((x - y) / ρ)).1.comp x hw).const_mul (ρ ^ 2)) using 1 <;> [rfl; field_simp]
    have he1 : HasDerivAt (fun u => ρ * φ1 ((u - y) / ρ)) (φ2 ((x - y) / ρ)) x := by
      convert (((hasDerivAt_φ ((x - y) / ρ)).2.comp x hw).const_mul ρ) using 1 <;> [rfl; field_simp]
    exact ⟨((hq_deriv y x).1.fun_mul he0).congr_deriv rfl,
      (((hq_deriv y x).2.fun_mul he0).fun_add ((hq_deriv y x).1.fun_mul he1)).congr_deriv
        (by dsimp [bt2]; ring)⟩
  let H0 (x : ℝ) : ℝ := δ / 2 * ∑ y ∈ Y, bt0 y x
  let H1 (x : ℝ) : ℝ := δ / 2 * ∑ y ∈ Y, bt1 y x
  let H2 (x : ℝ) : ℝ := δ / 2 * ∑ y ∈ Y, bt2 y x
  let h : ℂ → ℂ := fun z => ((δ / 2 : ℝ) : ℂ) * ∑ y ∈ Y, lagrange S y z *
    ((ρ : ℂ) ^ 2 * (((z - y) / ρ) ^ 2 * Complex.exp (-((z - y) / ρ) ^ 2)))
  have hh_diff : Differentiable ℂ h :=
    Differentiable.const_mul (Differentiable.fun_sum fun y _ =>
      (differentiable_lagrange S y).mul (by fun_prop)) _
  have hh_real : ∀ x : ℝ, h x = H0 x := fun x => by
    simp only [h, H0, bt0, q0, φ0, Complex.ofReal_mul, Complex.ofReal_sum]
    congr 1; refine Finset.sum_congr rfl fun y _ => ?_
    have hq_re : lagrange S y x = ((∏ w ∈ S.erase y, ((x - w) / (y - w)) ^ 3 : ℝ) : ℂ) := by simp [lagrange]
    rw [hq_re, Complex.ofReal_re, show ((x : ℂ) - y) / ρ = (((x - y) / ρ : ℝ) : ℂ) by push_cast; rfl]
    simp [Complex.ofReal_exp]
  have hh_jet : ∀ x : ℝ, deriv h x = H1 x ∧ deriv (deriv h) x = H2 x :=
    entire_real_jet hh_diff hh_real
      (fun x => (HasDerivAt.fun_sum fun y _ => (hbt_deriv y x).1).const_mul _)
      (fun x => (HasDerivAt.fun_sum fun y _ => (hbt_deriv y x).2).const_mul _)
  set g : ℂ → ℂ := fun z => f z + h z
  have hdg : ∀ x ∈ I, deriv g x = deriv f x + H1 x ∧
      deriv (deriv g) x = deriv (deriv f) x + H2 x := fun x hx => by
    have hd1 : ∀ w ∈ nbhd (2 * ε), deriv g w = deriv f w + deriv h w := fun w hw =>
      ((hf.differentiableOn.differentiableAt (hU.mem_nhds hw)).hasDerivAt.fun_add (hh_diff w).hasDerivAt).deriv
    have hx2 := hmem2 hx
    refine ⟨(hd1 x hx2).trans (by rw [(hh_jet x).1]), ?_⟩
    rw [(Filter.eventuallyEq_of_mem (hU.mem_nhds hx2) hd1).deriv_eq,
      (((hf.differentiableOn.deriv hU).differentiableAt (hU.mem_nhds hx2)).hasDerivAt.fun_add
        ((differentiableOn_univ.1 (hh_diff.differentiableOn.deriv isOpen_univ) x).hasDerivAt)).deriv,
      (hh_jet x).2]
  have hest : ∀ x ∈ I, |H0 x| < τ ∧ |H1 x| < τ ∧ |H2 x| < 21 * δ := fun x hx => by
    have hsumQ := hQM x hx
    have hb01 : |H0 x| + |H1 x| ≤ K * L * ρ := by
      have h11L : K * (11 * ρ) ≤ K * L * ρ := by
        have : 11 ≤ L := by dsimp [L]; linarith [show 0 ≤ 64 / r ^ 2 by positivity]
        nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this hρ_pos.le) hK0]
      rw [show H0 x = δ / 2 * ∑ y ∈ Y, bt0 y x from rfl,
        show H1 x = δ / 2 * ∑ y ∈ Y, bt1 y x from rfl,
        abs_mul, abs_mul, abs_of_pos (half_pos hδ), ← mul_add]
      have hs : |∑ y ∈ Y, bt0 y x| + |∑ y ∈ Y, bt1 y x| ≤ M * (11 * ρ) := by
        refine (add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)).trans ?_
        rw [← Finset.sum_add_distrib]
        refine (Finset.sum_le_sum (g := fun y => (|q0 y x| + |q1 y x| + |q2 y x|) * (11 * ρ)) fun y _ => ?_).trans
          (by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hsumQ (by positivity))
        dsimp [bt0, bt1]
        have a1 := abs_add_le (q1 y x * (ρ ^ 2 * φ0 ((x - y) / ρ))) (q0 y x * (ρ * φ1 ((x - y) / ρ)))
        rw [abs_mul, abs_mul, abs_of_pos (pow_pos hρ_pos 2), abs_mul, abs_mul, abs_of_pos hρ_pos] at a1
        rw [abs_mul, abs_mul, abs_of_pos (pow_pos hρ_pos 2)]
        have t1 := mul_le_of_le_one_right (by positivity : 0 ≤ ρ ^ 2) (φ_bounds ((x - y) / ρ)).1
        have t2 := mul_le_mul_of_nonneg_left (φ_bounds ((x - y) / ρ)).2.1 hρ_pos.le
        nlinarith [hρ_pos, abs_nonneg (q0 y x), abs_nonneg (q1 y x), abs_nonneg (q2 y x)]
      linarith [mul_le_mul_of_nonneg_left hs (half_pos hδ).le,
        show δ / 2 * (M * (11 * ρ)) = K * (11 * ρ) by dsimp [K]; ring]
    have hb2 : |H2 x| ≤ 20 * δ + K * L * ρ := by
      rw [show H2 x = δ / 2 * ∑ y ∈ Y, bt2 y x from rfl, abs_mul, abs_of_pos (half_pos hδ)]
      have hcard : (Y.filter fun y => |x - y| < r).card ≤ 1 := Finset.card_le_one.2 fun y hy y' hy' => by
        by_contra hne
        have h1 := hr_sep y (Finset.mem_filter.1 hy).1 y' (Finset.mem_filter.1 hy').1 hne
        have h2 := abs_sub_le y x y'; rw [abs_sub_comm y x] at h2
        linarith [(Finset.mem_filter.1 hy).2, (Finset.mem_filter.1 hy').2]
      have hsum : |∑ y ∈ Y, bt2 y x| ≤ 40 + M * L * ρ := by
        have h1 : |∑ y ∈ Y, bt2 y x| ≤ Q x * (21 * ρ) +
            ((∑ y ∈ Y with |x - y| < r, |q0 y x| * |φ2 ((x - y) / ρ)|) +
              ∑ y ∈ Y with ¬ |x - y| < r, |q0 y x| * |φ2 ((x - y) / ρ)|) :=
          (Finset.abs_sum_le_sum_abs _ _).trans <| (Finset.sum_le_sum
            (g := fun y => (|q0 y x| + |q1 y x| + |q2 y x|) * (21 * ρ) + |q0 y x| * |φ2 ((x - y) / ρ)|)
            fun y _ => by
              dsimp [bt2]
              have a1 := abs_add_le (q2 y x * (ρ ^ 2 * φ0 ((x - y) / ρ)) + 2 * q1 y x * (ρ * φ1 ((x - y) / ρ)))
                (q0 y x * φ2 ((x - y) / ρ))
              have a2 := abs_add_le (q2 y x * (ρ ^ 2 * φ0 ((x - y) / ρ))) (2 * q1 y x * (ρ * φ1 ((x - y) / ρ)))
              rw [abs_mul, abs_mul, abs_of_pos (pow_pos hρ_pos 2), abs_mul, abs_mul, abs_two, abs_mul, abs_of_pos hρ_pos] at a2
              rw [abs_mul] at a1
              have t1 := mul_le_of_le_one_right (by positivity : 0 ≤ ρ ^ 2) (φ_bounds ((x - y) / ρ)).1
              have t2 := mul_le_mul_of_nonneg_left (φ_bounds ((x - y) / ρ)).2.1 hρ_pos.le
              exact (a1.trans (add_le_add a2 le_rfl)).trans
                (by nlinarith [hρ_pos, abs_nonneg (q0 y x), abs_nonneg (q1 y x), abs_nonneg (q2 y x)])).trans_eq
            (by rw [Finset.sum_add_distrib, ← Finset.sum_mul,
                  ← Finset.sum_filter_add_sum_filter_not Y (fun y => |x - y| < r)
                    (fun y => |q0 y x| * |φ2 ((x - y) / ρ)|)])
        have hn : ∑ y ∈ Y with |x - y| < r, |q0 y x| * |φ2 ((x - y) / ρ)| ≤ 40 :=
          (Finset.sum_le_card_nsmul _ _ 40 fun y hy => by
            have := mul_le_mul (hr_near y (Finset.mem_filter.1 hy).1 x (Finset.mem_filter.1 hy).2)
              (φ_bounds ((x - y) / ρ)).2.2.1 (abs_nonneg _) (by norm_num)
            linarith).trans ((nsmul_le_nsmul_left (by norm_num) hcard).trans_eq (one_nsmul _))
        have hfar : ∑ y ∈ Y with ¬ |x - y| < r, |q0 y x| * |φ2 ((x - y) / ρ)| ≤ M * (64 / r ^ 2 * ρ) := by
          refine ((Finset.sum_le_sum (g := fun y => (|q0 y x| + |q1 y x| + |q2 y x|) * (64 / r ^ 2 * ρ))
            fun y hy => ?_).trans
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by positivity)).trans
            (by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hsumQ (by positivity))
          have hf := not_lt.1 (Finset.mem_filter.1 hy).2
          have hsq : r ^ 2 ≤ (x - y) ^ 2 := sq_abs (x - y) ▸ pow_le_pow_left₀ hr0.le hf 2
          have hb := (φ_bounds ((x - y) / ρ)).2.2.2
          rw [div_pow, div_mul_eq_mul_div] at hb
          have hb' : r ^ 2 * |φ2 ((x - y) / ρ)| ≤ 64 * ρ ^ 2 := by
            have := (div_le_iff₀ (pow_pos hρ_pos 2)).1 hb
            nlinarith [abs_nonneg (φ2 ((x - y) / ρ))]
          have hb'' : |φ2 ((x - y) / ρ)| ≤ 64 / r ^ 2 * ρ := by
            rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hr0 2), mul_comm]; nlinarith
          nlinarith [mul_le_mul_of_nonneg_left hb'' (abs_nonneg (q0 y x)),
            abs_nonneg (q1 y x), abs_nonneg (q2 y x), (show 0 ≤ 64 / r ^ 2 * ρ by positivity)]
        have h21 : Q x * (21 * ρ) ≤ M * (21 * ρ) := mul_le_mul_of_nonneg_right hsumQ (by positivity)
        have hML : M * (21 * ρ) + M * (64 / r ^ 2 * ρ) = M * L * ρ := by dsimp [L]; ring
        linarith
      linarith [mul_le_mul_of_nonneg_left hsum (half_pos hδ).le,
        show δ / 2 * (40 + M * L * ρ) = 20 * δ + K * L * ρ by dsimp [K]; ring]
    exact ⟨by linarith [abs_nonneg (H1 x)], by linarith [abs_nonneg (H0 x)],
      hb2.trans_lt (by linarith [hρ_lt.trans_le (min_le_left δ (m / 2))])⟩
  have hbt_self : ∀ y : ℝ, bt0 y y = 0 ∧ bt1 y y = 0 ∧ bt2 y y = 2 := fun y => by
    simp [bt0, bt1, bt2, q0, φ0, φ1, φ2, lagrange_self]
  have hbt_other : ∀ {y w : ℝ}, w ∈ S.erase y → bt0 y w = 0 ∧ bt1 y w = 0 ∧ bt2 y w = 0 := by
    intro y w hw; obtain ⟨z0, z1, z2⟩ := lagrange_other hw
    simp [bt0, bt1, bt2, q0, q1, q2, z0, z1, z2]
  have hjet_S : ∀ w ∈ S, g w = f w ∧ deriv g w = deriv f w ∧ deriv (deriv g) w = deriv (deriv f) w + H2 w :=
    fun w hw => by
      have hwI : w ∈ I := (Finset.mem_union.1 hw).elim (hY w) (hZ w)
      have h0 : H0 w = 0 := mul_eq_zero_of_right _ (Finset.sum_eq_zero fun y _ =>
        if hwy : w = y then hwy ▸ (hbt_self w).1 else (hbt_other (Finset.mem_erase.2 ⟨hwy, hw⟩)).1)
      have h1 : H1 w = 0 := mul_eq_zero_of_right _ (Finset.sum_eq_zero fun y _ =>
        if hwy : w = y then hwy ▸ (hbt_self w).2.1 else (hbt_other (Finset.mem_erase.2 ⟨hwy, hw⟩)).2.1)
      exact ⟨by simp [g, hh_real w, h0], by rw [(hdg w hwI).1, h1]; simp, (hdg w hwI).2⟩
  refine ⟨g, ?_, fun y hy => ?_, fun z hz => ?_, ?_⟩
  · refine exists_inClass hε (hf.differentiableOn.add hh_diff.differentiableOn)
      (fun x hx => by simp [g, hh_real x, hf.im_eq_zero x hx])
      (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
    · have := abs_le.1 (hest x hx).1.le
      simp only [g, Complex.add_re, hh_real x, Complex.ofReal_re]
      exact ⟨by linarith [(hmar x hx).1, min_le_right δ (m / 2)],
        by linarith [(hmar x hx).2.1, min_le_right δ (m / 2)]⟩
    · intro h0
      have hd := h0 ▸ (hdg x hx).1
      have : ‖deriv f x‖ = |H1 x| := by
        rw [eq_neg_of_add_eq_zero_left hd.symm, norm_neg, Complex.norm_real, Real.norm_eq_abs]
      linarith [(hmar x hx).2.2.1, (hest x hx).2.1, min_le_right δ (m / 2)]
    · rw [(hdg x hx).1]
      have := norm_add_le (deriv f x) (H1 x)
      rw [Complex.norm_real, Real.norm_eq_abs] at this
      linarith [(hmar x hx).2.2.2, (hest x hx).2.1, min_le_right δ (m / 2)]
  · have hyS : y ∈ S := Finset.mem_union_left _ hy
    obtain ⟨e0, e1, e2⟩ := hjet_S y hyS
    have hh2y : H2 y = δ := by
      dsimp [H2]
      rw [Finset.sum_eq_single y (fun y' _ hne => (hbt_other (Finset.mem_erase.2 ⟨hne.symm, hyS⟩)).2.2)
        (fun h => absurd hy h), (hbt_self y).2.2]; ring
    have hdf_ne : deriv f y ≠ 0 := norm_pos_iff.1 (hm.trans_le (hmar y (hY y hy)).2.2.1)
    refine ⟨e0, e1, ?_⟩
    rw [e1, e2, hh2y, add_div, add_sub_cancel_left, norm_div, Complex.norm_real,
      Real.norm_of_nonneg hδ.le, le_div_iff₀ (norm_pos_iff.2 hdf_ne)]
    nlinarith [(hmar y (hY y hy)).2.2.2]
  · have hzS : z ∈ S := Finset.mem_union_right _ hz
    obtain ⟨e0, e1, e2⟩ := hjet_S z hzS
    have hh2z : H2 z = 0 := mul_eq_zero_of_right _ (Finset.sum_eq_zero fun y hy =>
      (hbt_other (Finset.mem_erase.2 ⟨fun he => Finset.disjoint_left.1 hYZ (he ▸ hy) hz, hzS⟩)).2.2)
    exact ⟨e0, e1, by rw [e2, hh2z]; simp⟩
  · have : Nonempty I := ⟨⟨0, le_rfl, zero_le_one⟩⟩
    calc d2Map f g ≤ δ + δ + 21 * δ := add_le_add (add_le_add
          (ciSup_le fun x => by
            rw [norm_sub_rev]; simpa [g, hh_real x, Real.norm_eq_abs] using (hest x x.2).1.le.trans (min_le_left _ _))
          (ciSup_le fun x => by
            rw [norm_sub_rev, (hdg x x.2).1, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
            exact (hest x x.2).2.1.le.trans (min_le_left _ _)))
          (ciSup_le fun x => by
            rw [norm_sub_rev, (hdg x x.2).2, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
            exact (hest x x.2).2.2.le)
      _ = 23 * δ := by ring

private theorem disjoint_image_add_of_abs_sub_lt {A B : Set ℝ} {δ τ : ℝ}
    (hA : ∀ a ∈ A, ∀ a' ∈ A, |a - a'| < δ / 3) (hB : ∀ b ∈ B, ∀ b' ∈ B, |b - b'| < δ / 3)
    (hAB : (A ∩ B).Nonempty) (hτ : δ ≤ |τ|) : Disjoint ((· + τ) '' A) B := by
  obtain ⟨x, hxA, hxB⟩ := hAB
  have hδ : 0 < δ := by simpa using hA x hxA x hxA
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨a, ha, rfl⟩ hb
  linarith [hA a ha x hxA, hB (a + τ) hb x hxB,
    (by simpa using abs_sub (a + τ - x) (a - x) : |τ| ≤ |a + τ - x| + |a - x|)]

namespace IFS

variable {N : ℕ} {ε ε' : ℝ}

private theorem dualComp_eq_of_agreeAt (Φ : IFS N ε) (Ψ : IFS N ε') {w : List (Fin N)} {z : ℂ}
    (hag : ∀ m (hm : m < w.length),
      AgreeAt (Φ.f w[m]) (Ψ.f w[m]) (Φ.comp (w.take m).reverse z))
    (h : ℂ → ℂ) : Ψ.dualComp w h z = Φ.dualComp w h z := by
  induction w generalizing z with
  | nil => rfl
  | cons i w ih =>
    obtain ⟨h0, h1, h2⟩ := hag 0 (by simp)
    simp only [List.getElem_cons_zero, List.take_zero, List.reverse_nil, comp_nil, id] at h0 h1 h2
    have htail : ∀ m (hm : m < w.length),
        AgreeAt (Φ.f w[m]) (Ψ.f w[m]) (Φ.comp (w.take m).reverse (Φ.f i z)) := fun m hm => by
      have := hag (m + 1) (by simp [hm])
      rwa [List.take_succ_cons, List.reverse_cons, Φ.comp_append, List.getElem_cons_succ] at this
    change deriv (Ψ.f i) z * Ψ.dualComp w h (Ψ.f i z) + Ψ.nonlin i z =
      deriv (Φ.f i) z * Φ.dualComp w h (Φ.f i z) + Φ.nonlin i z
    rw [h0, ih htail, h1, nonlin, nonlin, h1, h2]

private theorem dualCylAt_eq_of_agreeAt (Φ : IFS N ε) (Ψ : IFS N ε') (k K : ℝ) {w : List (Fin N)}
    {x : ℝ} (hag : ∀ m (hm : m < w.length),
      AgreeAt (Φ.f w[m]) (Ψ.f w[m]) (Φ.comp (w.take m).reverse x)) :
    Ψ.dualCylAt k K w x = Φ.dualCylAt k K w x := by
  rw [dualCylAt, dualCylAt, dualComp_eq_of_agreeAt Φ Ψ hag, dualComp_eq_of_agreeAt Φ Ψ hag]

private theorem dualCylAt_cons_eq_of_agreeAt (Φ : IFS N ε) (Ψ : IFS N ε') (k K : ℝ) {i : Fin N}
    {w : List (Fin N)} {x : ℝ} (h0 : Ψ.f i x = Φ.f i x)
    (h1 : deriv (Ψ.f i) x = deriv (Φ.f i) x)
    (hag : ∀ m (hm : m < w.length),
      AgreeAt (Φ.f w[m]) (Ψ.f w[m]) (Φ.comp (w.take m).reverse (Φ.f i x))) :
    Ψ.dualCylAt k K (i :: w) x =
      (· + (Ψ.nonlin i x - Φ.nonlin i x).re) '' Φ.dualCylAt k K (i :: w) x := by
  have hc : ∀ h : ℂ → ℂ, Ψ.dualComp (i :: w) h x =
      Φ.dualComp (i :: w) h x + (Ψ.nonlin i x - Φ.nonlin i x) := fun h => by
    change deriv (Ψ.f i) x * Ψ.dualComp w h (Ψ.f i x) + Ψ.nonlin i x =
      (deriv (Φ.f i) x * Φ.dualComp w h (Φ.f i x) + Φ.nonlin i x) + _
    rw [h0, h1, dualComp_eq_of_agreeAt Φ Ψ hag]; ring
  rw [dualCylAt, dualCylAt, image_add_const_uIcc, hc, hc, Complex.add_re, Complex.add_re]

private theorem re_dualComp_const (Φ : IFS N ε) (w : List (Fin N)) (c : ℝ) {x : ℝ} (hx : x ∈ I) :
    (Φ.dualComp w (fun _ => (c : ℂ)) x).re =
      (deriv (Φ.comp w.reverse) x).re * c + (Φ.dualProj (.fin w) x).re := by
  rw [Φ.dualComp_apply w _ (ofReal_mem_nbhd Φ.ε_pos hx)]; simp [Complex.mul_re]

private theorem abs_sub_le_cmax_pow_of_mem_dualCylAt (Φ : IFS N ε) {k K : ℝ} (hkK : k ≤ K)
    (w : List (Fin N)) {x : ℝ} (hx : x ∈ I) {p q : ℝ} (hp : p ∈ Φ.dualCylAt k K w x)
    (hq : q ∈ Φ.dualCylAt k K w x) : |p - q| ≤ Φ.cmax ^ w.length * (K - k) := by
  refine (abs_sub_le_of_uIcc_subset_uIcc (uIcc_subset_uIcc hq hp)).trans ?_
  rw [Φ.re_dualComp_const _ _ hx, Φ.re_dualComp_const _ _ hx]
  have hd : |(deriv (Φ.comp w.reverse) x).re| ≤ Φ.cmax ^ w.length := by
    have h := Φ.norm_deriv_comp_le w.reverse (subset_closure (ofReal_mem_nbhd Φ.ε_pos hx))
    rw [List.length_reverse] at h
    exact (Complex.abs_re_le_norm _).trans h
  calc _ = |(deriv (Φ.comp w.reverse) x).re| * (K - k) := by
        rw [← abs_of_nonneg (sub_nonneg.2 hkK), ← abs_mul]; congr 1; ring
    _ ≤ Φ.cmax ^ w.length * (K - k) := mul_le_mul_of_nonneg_right hd (sub_nonneg.2 hkK)

private theorem dualSSC_of_cyl (Φ : IFS N ε) {k K : ℝ} (n : ℕ)
    (hH : ∀ u : ℕ → Fin N, ∀ y ∈ I, (Φ.dualProj (.inf u) y).re ∈ Icc k K)
    (hdisj : ∀ i j : Fin (n + 1) → Fin N, i 0 ≠ j 0 →
      Φ.DualCylDisjoint k K (List.ofFn i) (List.ofFn j)) : Φ.DualSSC := by
  intro i j hij
  obtain ⟨x, hx, hd⟩ := hdisj (fun m => i m) (fun m => j m) (by simpa using hij)
  have hmem : ∀ u : ℕ → Fin N, (Φ.dualProj (.inf u) x).re ∈
      Φ.dualCylAt k K (List.ofFn fun m : Fin (n + 1) => u m) x := fun u => by
    set w := List.ofFn fun m : Fin (n + 1) => u m
    have hprep : Word.inf u = (Word.inf fun m => u (m + (n + 1))).prepend w := by
      change Word.inf u = Word.inf fun m => if h : m < w.length then w[m] else u (m - w.length + (n + 1))
      congr 1; funext m; simp only [w, List.length_ofFn]
      split_ifs with hm <;> [simp only [List.getElem_ofFn]; (congr 1; omega)]
    have hxn := ofReal_mem_nbhd Φ.ε_pos hx
    rw [hprep, dualCylAt, Φ.re_dualComp_const _ _ hx, Φ.re_dualComp_const _ _ hx,
      Φ.dualProj_prepend w _ (subset_closure hxn), Φ.comp_ofReal w.reverse hx]
    simp only [Complex.add_re, Complex.mul_re, Φ.im_deriv_comp_ofReal _ hxn, zero_mul, sub_zero, mem_uIcc]
    obtain ⟨h1, h2⟩ := hH (fun m => u (m + (n + 1))) _ (Φ.re_comp_mem_I w.reverse hx)
    rcases le_total 0 (deriv (Φ.comp w.reverse) x).re with ha | ha
    · exact Or.inl ⟨by nlinarith, by nlinarith⟩
    · exact Or.inr ⟨by nlinarith, by nlinarith⟩
  exact ⟨x, hx, fun heq => Set.disjoint_left.1 hd (heq ▸ hmem i) (hmem j)⟩

private theorem finite_exceptional (Φ : IFS N ε) (h : Φ.NoCoincidence) (n : ℕ) {F : Set ℝ}
    (hF : F.Finite) :
    {t : ℝ | t ∈ I ∧ ((∃ v w : List (Fin N), v.length ≤ n ∧ w.length ≤ n ∧ v ≠ w ∧
      (Φ.comp v t).re = (Φ.comp w t).re) ∨
      ∃ v : List (Fin N), v.length ≤ n ∧ (Φ.comp v t).re ∈ F)}.Finite := by
  have hW := List.finite_length_le (Fin N) n
  have heq : ∀ {v w : List (Fin N)}, v ≠ w → {t : ℝ | t ∈ I ∧ (Φ.comp v t).re = (Φ.comp w t).re}.Finite :=
    fun {v w} hvw => by
      obtain ⟨x, hx, hne⟩ := h v w hvw
      exact (finite_zeros Φ.ε_pos ((Φ.differentiableOn_comp v).sub (Φ.differentiableOn_comp w))
        ⟨x, hx, sub_ne_zero.2 hne⟩).subset fun t ⟨ht, he⟩ =>
          ⟨ht, by show Φ.comp v t - Φ.comp w t = 0; rw [Φ.comp_ofReal v ht, Φ.comp_ofReal w ht, he, sub_self]⟩
  have hval : ∀ (w : List (Fin N)) (y : ℝ), {t : ℝ | t ∈ I ∧ (Φ.comp w t).re = y}.Finite :=
    fun w y => Set.Subsingleton.finite fun _ ha _ hb => Φ.injOn_re_comp w ha.1 hb.1 (ha.2.trans hb.2.symm)
  refine ((hW.biUnion fun v _ => hW.biUnion fun w _ =>
      Set.finite_iUnion fun hvw : v ≠ w => heq hvw).union
    (hW.biUnion fun v _ => hF.biUnion fun y _ => hval v y)).subset ?_
  rintro t ⟨ht, ⟨v, w, hv, hw, hvw, he⟩ | ⟨v, hv, hvF⟩⟩
  · exact Or.inl (mem_biUnion hv (mem_biUnion hw (mem_iUnion_of_mem hvw ⟨ht, he⟩)))
  · exact Or.inr (mem_biUnion hv (mem_biUnion hvF ⟨ht, rfl⟩))

private theorem disjoint_uIcc_iff {a b c d : ℝ} :
    Disjoint (uIcc a b) (uIcc c d) ↔ max a b < min c d ∨ max c d < min a b := by
  refine ⟨fun h => ?_, ?_⟩
  · by_contra! hcon
    exact Set.disjoint_left.1 h
      (show max (min a b) (min c d) ∈ uIcc a b from ⟨le_max_left _ _, max_le min_le_max hcon.1⟩)
      (show max (min a b) (min c d) ∈ uIcc c d from ⟨le_max_right _ _, max_le hcon.2 min_le_max⟩)
  · rintro (h | h) <;> refine Set.disjoint_left.2 fun x hx hx' => ?_ <;> linarith [hx.1, hx.2, hx'.1, hx'.2]

private theorem infinite_good (Φ : IFS N ε) (k K : ℝ) (a b : List (Fin N)) :
    {t : ℝ | t ∈ I ∧ (Φ.DualCylDisjoint k K a b →
      Disjoint (Φ.dualCylAt k K a t) (Φ.dualCylAt k K b t))}.Infinite := by
  by_cases hd : Φ.DualCylDisjoint k K a b
  · obtain ⟨x, hx, hdx⟩ := hd
    have hc : ∀ (w : List (Fin N)) (c : ℝ),
        Tendsto (fun t : ℝ => (Φ.dualComp w (fun _ => (c : ℂ)) t).re) (𝓝[I] x)
          (𝓝 (Φ.dualComp w (fun _ => (c : ℂ)) x).re) := fun w c => by
      have hg : ContinuousOn (fun z => deriv (Φ.comp w.reverse) z * c + Φ.dualProj (.fin w) z) (nbhd ε) :=
        ((((Φ.differentiableOn_comp w.reverse).deriv (isOpen_nbhd ε)).continuousOn).mul
          continuousOn_const).add (Φ.differentiableOn_dualProj (.fin w)).continuousOn
      exact ((Complex.continuous_re.comp_continuousOn
        (hg.comp Complex.continuous_ofReal.continuousOn fun _ ht => ofReal_mem_nbhd Φ.ε_pos ht)).congr
        fun t ht => by rw [Φ.dualComp_apply w _ (ofReal_mem_nbhd Φ.ε_pos ht)]; rfl) x hx
    have hev : ∀ᶠ t in 𝓝[I] x, Disjoint (Φ.dualCylAt k K a t) (Φ.dualCylAt k K b t) := by
      unfold dualCylAt at hdx ⊢
      simp_rw [disjoint_uIcc_iff] at hdx ⊢
      rcases hdx with h1 | h1
      · exact (((hc a k).max (hc a K)).eventually_lt ((hc b k).min (hc b K)) h1).mono fun _ => Or.inl
      · exact (((hc b k).max (hc b K)).eventually_lt ((hc a k).min (hc a K)) h1).mono fun _ => Or.inr
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhdsWithin_iff.1 hev
    have hlt : max (x - r / 2) 0 < min (x + r / 2) 1 := by
      rw [max_lt_iff, lt_min_iff, lt_min_iff]
      exact ⟨⟨by linarith, by linarith [hx.2]⟩, by linarith [hx.1], zero_lt_one⟩
    refine (Set.Icc_infinite hlt).mono fun t ht => ?_
    have h1 : t ∈ I := ⟨(le_max_right _ _).trans ht.1, ht.2.trans (min_le_right _ _)⟩
    refine ⟨h1, fun _ => hsub ⟨?_, h1⟩⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [(le_max_left _ _).trans ht.1], by linarith [ht.2.trans (min_le_left _ _)]⟩
  · exact (Set.Icc_infinite zero_lt_one).mono fun _ ht => ⟨ht, fun h' => absurd h' hd⟩

private structure IsPointChoice (Φ : IFS N ε) (k K : ℝ) (n : ℕ)
    (x : (Fin n → Fin N) × (Fin n → Fin N) → ℝ) : Prop where
  mem_I : ∀ p, x p ∈ I
  disjoint : ∀ p, Φ.DualCylDisjoint k K (List.ofFn p.1) (List.ofFn p.2) →
    Disjoint (Φ.dualCylAt k K (List.ofFn p.1) (x p)) (Φ.dualCylAt k K (List.ofFn p.2) (x p))
  nodup_fst : ∀ p, (Φ.orbit (List.ofFn p.1) (x p)).Nodup
  nodup_snd : ∀ p, (Φ.orbit (List.ofFn p.2) (x p)).Nodup
  sep : ∀ p q, p ≠ q →
    ∀ y ∈ Φ.orbit (List.ofFn p.1) (x p) ++ Φ.orbit (List.ofFn p.2) (x p),
      y ∉ Φ.orbit (List.ofFn q.1) (x q) ++ Φ.orbit (List.ofFn q.2) (x q)

private theorem lemma_4_1 (Φ : IFS N ε) (n : ℕ) (k K : ℝ) (h : Φ.NoCoincidence) :
    ∃ x : (Fin n → Fin N) × (Fin n → Fin N) → ℝ, Φ.IsPointChoice k K n x := by
  classical
  let Good (p : (Fin n → Fin N) × (Fin n → Fin N)) (t : ℝ) : Prop :=
    t ∈ I ∧ (Φ.DualCylDisjoint k K (List.ofFn p.1) (List.ofFn p.2) →
        Disjoint (Φ.dualCylAt k K (List.ofFn p.1) t) (Φ.dualCylAt k K (List.ofFn p.2) t)) ∧
      (Φ.orbit (List.ofFn p.1) t).Nodup ∧ (Φ.orbit (List.ofFn p.2) t).Nodup
  have hstep : ∀ (p : (Fin n → Fin N) × (Fin n → Fin N)) {F : Set ℝ}, F.Finite →
      ∃ t, Good p t ∧ ∀ y ∈ Φ.orbit (List.ofFn p.1) t ++ Φ.orbit (List.ofFn p.2) t, y ∉ F := by
    intro p F hF
    obtain ⟨t, ⟨ht, hdisj⟩, hex⟩ := ((Φ.infinite_good k K (List.ofFn p.1)
      (List.ofFn p.2)).sdiff (Φ.finite_exceptional h n hF)).nonempty
    have hnodup : ∀ i : Fin n → Fin N, (Φ.orbit (List.ofFn i) t).Nodup := fun i =>
      List.Nodup.map_on (fun l hl l' hl' he => by
        by_contra hne
        rw [List.mem_range, List.length_ofFn] at hl hl'
        have hl1 : l ≤ (List.ofFn i).length := by simp; omega
        have hl2 : l' ≤ (List.ofFn i).length := by simp; omega
        exact hex ⟨ht, Or.inl ⟨_, _, by simp, by simp, fun heq => hne (by
          have := congrArg List.length heq
          simp only [List.length_reverse, List.length_take, min_eq_left hl1, min_eq_left hl2] at this
          exact this), he⟩⟩) List.nodup_range
    refine ⟨t, ⟨ht, hdisj, hnodup p.1, hnodup p.2⟩, fun y hy => ?_⟩
    rcases List.mem_append.1 hy with hy | hy <;>
      { simp only [orbit, List.mem_map, List.mem_range] at hy
        obtain ⟨l, -, rfl⟩ := hy
        exact fun hyF => hex ⟨ht, Or.inr ⟨_, by simp, hyF⟩⟩ }
  suffices H : ∀ S : Finset ((Fin n → Fin N) × (Fin n → Fin N)),
      ∃ x : (Fin n → Fin N) × (Fin n → Fin N) → ℝ, (∀ p ∈ S, Good p (x p)) ∧
        ∀ p ∈ S, ∀ q ∈ S, p ≠ q →
          ∀ y ∈ Φ.orbit (List.ofFn p.1) (x p) ++ Φ.orbit (List.ofFn p.2) (x p),
            y ∉ Φ.orbit (List.ofFn q.1) (x q) ++ Φ.orbit (List.ofFn q.2) (x q) by
    obtain ⟨x, hg, hs⟩ := H Finset.univ
    exact ⟨x, fun p => (hg p (Finset.mem_univ _)).1, fun p => (hg p (Finset.mem_univ _)).2.1,
      fun p => (hg p (Finset.mem_univ _)).2.2.1, fun p => (hg p (Finset.mem_univ _)).2.2.2,
      fun p q => hs p (Finset.mem_univ _) q (Finset.mem_univ _)⟩
  intro S
  induction S using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp, by simp⟩
  | insert a S ha ih =>
    obtain ⟨x, hgood, hsep⟩ := ih
    obtain ⟨t, hgt, havoid⟩ := hstep a (S.finite_toSet.biUnion fun q _ =>
      (Φ.orbit (List.ofFn q.1) (x q) ++ Φ.orbit (List.ofFn q.2) (x q)).finite_toSet)
    have hxS : ∀ q ∈ S, Function.update x a t q = x q :=
      fun q hq => Function.update_of_ne (ne_of_mem_of_not_mem hq ha) _ _
    refine ⟨Function.update x a t, fun p hp => ?_, fun p hp q hq hpq y hy => ?_⟩
    · rcases Finset.mem_insert.1 hp with rfl | hp
      · rwa [Function.update_self]
      · rw [hxS p hp]; exact hgood p hp
    · rcases Finset.mem_insert.1 hp with rfl | hpS <;> rcases Finset.mem_insert.1 hq with rfl | hqS
      · exact absurd rfl hpq
      · rw [Function.update_self] at hy; rw [hxS q hqS]
        exact fun hyq => havoid y hy (mem_biUnion hqS hyq)
      · rw [hxS p hpS] at hy; rw [Function.update_self]
        exact fun hyq => havoid y hyq (mem_biUnion hpS hy)
      · rw [hxS p hpS] at hy; rw [hxS q hqS]
        exact hsep p hpS q hqS hpq y hy

private theorem self_mem_orbit (Φ : IFS N ε) (w : List (Fin N)) (t : ℝ) : t ∈ Φ.orbit w t := by
  simpa [orbit] using List.mem_map.2 ⟨0, List.mem_range.2 (Nat.succ_pos w.length), by simp⟩

private def Bad (Φ : IFS N ε) (k K : ℝ) {n : ℕ} (p : (Fin n → Fin N) × (Fin n → Fin N)) : Prop :=
  ¬ Φ.DualCylDisjoint k K (List.ofFn p.1) (List.ofFn p.2)

private noncomputable def pairsFinset (N n : ℕ) :
    Finset ((Fin (n + 1) → Fin N) × (Fin (n + 1) → Fin N)) := by
  classical exact Finset.univ.filter fun p => p.1 0 < p.2 0

private noncomputable def orbitPoints (Φ : IFS N ε) (n : ℕ)
    (x : (Fin (n + 1) → Fin N) × (Fin (n + 1) → Fin N) → ℝ) : Finset ℝ := by
  classical exact (pairsFinset N n).biUnion fun p =>
    (Φ.orbit (List.ofFn p.1) (x p) ++ Φ.orbit (List.ofFn p.2) (x p)).toFinset

private noncomputable def badPoints (Φ : IFS N ε) (k K : ℝ) (n : ℕ)
    (x : (Fin (n + 1) → Fin N) × (Fin (n + 1) → Fin N) → ℝ) (ℓ : Fin N) : Finset ℝ := by
  classical exact ((pairsFinset N n).filter fun p => Φ.Bad k K p ∧ p.1 0 = ℓ).image x

private noncomputable def goodPoints (Φ : IFS N ε) (k K : ℝ) (n : ℕ)
    (x : (Fin (n + 1) → Fin N) × (Fin (n + 1) → Fin N) → ℝ) (ℓ : Fin N) : Finset ℝ := by
  classical exact Φ.orbitPoints n x \ Φ.badPoints k K n x ℓ

private theorem mem_orbitPoints {Φ : IFS N ε} {n : ℕ}
    {x : (Fin (n + 1) → Fin N) × (Fin (n + 1) → Fin N) → ℝ} {y : ℝ} :
    y ∈ Φ.orbitPoints n x ↔ ∃ p, p.1 0 < p.2 0 ∧
      y ∈ Φ.orbit (List.ofFn p.1) (x p) ++ Φ.orbit (List.ofFn p.2) (x p) := by
  simp [orbitPoints, pairsFinset]

private theorem mem_badPoints {Φ : IFS N ε} {k K : ℝ} {n : ℕ}
    {x : (Fin (n + 1) → Fin N) × (Fin (n + 1) → Fin N) → ℝ} {ℓ : Fin N} {y : ℝ} :
    y ∈ Φ.badPoints k K n x ℓ ↔
      ∃ p, p.1 0 < p.2 0 ∧ (Φ.Bad k K p ∧ p.1 0 = ℓ) ∧ x p = y := by
  simp [badPoints, pairsFinset, and_assoc]

private theorem IsPointChoice.dualCylDisjoint {Φ : IFS N ε} (Ψ : IFS N ε') {k K δ : ℝ}
    (hkK : k ≤ K) {n : ℕ} {x : (Fin (n + 1) → Fin N) × (Fin (n + 1) → Fin N) → ℝ}
    (hx : Φ.IsPointChoice k K (n + 1) x) (hn : Φ.cmax ^ (n + 1) * (K - k) < δ / 3)
    (hY : ∀ ℓ, ∀ y ∈ Φ.badPoints k K n x ℓ, Ψ.f ℓ y = Φ.f ℓ y ∧
      deriv (Ψ.f ℓ) y = deriv (Φ.f ℓ) y ∧ δ ≤ ‖Ψ.nonlin ℓ y - Φ.nonlin ℓ y‖)
    (hZ : ∀ ℓ, ∀ z ∈ Φ.goodPoints k K n x ℓ, AgreeAt (Φ.f ℓ) (Ψ.f ℓ) z)
    {p : (Fin (n + 1) → Fin N) × (Fin (n + 1) → Fin N)} (hp : p.1 0 < p.2 0) :
    Ψ.DualCylDisjoint k K (List.ofFn p.1) (List.ofFn p.2) := by
  have ht := hx.mem_I p
  have heq_p : ∀ {q}, x q = x p → q = p := fun {q} h => by
    by_contra hqp
    exact hx.sep q p hqp (x q) (List.mem_append_left _ (Φ.self_mem_orbit _ _))
      (h ▸ List.mem_append_left _ (Φ.self_mem_orbit _ _))
  have hbad_iff : ∀ ℓ, x p ∈ Φ.badPoints k K n x ℓ ↔ Φ.Bad k K p ∧ p.1 0 = ℓ := fun ℓ =>
    ⟨fun hy => by obtain ⟨q, -, hqb, hqx⟩ := mem_badPoints.1 hy; rwa [← heq_p hqx],
      fun h => mem_badPoints.2 ⟨p, hp, h, rfl⟩⟩
  have hgood_of_ne : ∀ {y}, y ∈ Φ.orbit (List.ofFn p.1) (x p) ++ Φ.orbit (List.ofFn p.2) (x p) →
      y ≠ x p → ∀ ℓ, y ∈ Φ.goodPoints k K n x ℓ := fun {y} hy hne ℓ =>
    Finset.mem_sdiff.2 ⟨mem_orbitPoints.2 ⟨p, hp, hy⟩, fun hyB => by
      obtain ⟨q, -, -, rfl⟩ := mem_badPoints.1 hyB
      exact hx.sep p q (fun h => hne (h ▸ rfl)) (x q) hy
        (List.mem_append_left _ (Φ.self_mem_orbit _ _))⟩
  have hself_good : ∀ ℓ, ¬ (Φ.Bad k K p ∧ p.1 0 = ℓ) → x p ∈ Φ.goodPoints k K n x ℓ := fun ℓ h =>
    Finset.mem_sdiff.2 ⟨mem_orbitPoints.2 ⟨p, hp, List.mem_append_left _ (Φ.self_mem_orbit _ _)⟩,
      fun hy => h ((hbad_iff ℓ).1 hy)⟩
  have horb_later : ∀ (w : List (Fin N)), w = List.ofFn p.1 ∨ w = List.ofFn p.2 →
      (Φ.orbit w (x p)).Nodup → ∀ m, 0 < m → m ≤ w.length → ∀ ℓ,
        (Φ.comp (w.take m).reverse (x p)).re ∈ Φ.goodPoints k K n x ℓ :=
    fun w hw hnd m hm0 hm ℓ => by
      have hmem : (Φ.comp (w.take m).reverse (x p)).re ∈ Φ.orbit w (x p) :=
        List.mem_map.2 ⟨m, List.mem_range.2 (Nat.lt_succ_of_le hm), rfl⟩
      have hne : (Φ.comp (w.take m).reverse (x p)).re ≠ x p := fun he => by
        have := List.inj_on_of_nodup_map hnd (List.mem_range.2 (Nat.lt_succ_of_le hm))
          (List.mem_range.2 (Nat.succ_pos w.length)) (by simpa using he)
        omega
      exact hgood_of_ne (hw.elim (fun e => List.mem_append_left _ (e ▸ hmem))
        (fun e => List.mem_append_right _ (e ▸ hmem))) hne ℓ
  have hagree : ∀ {v : List (Fin N)} {ℓ : Fin N}, (Φ.comp v (x p)).re ∈ Φ.goodPoints k K n x ℓ →
      AgreeAt (Φ.f ℓ) (Ψ.f ℓ) (Φ.comp v (x p)) := fun h => Φ.comp_ofReal _ ht ▸ hZ _ _ h
  have hsnd : x p ∈ Φ.goodPoints k K n x (p.2 0) →
      Ψ.dualCylAt k K (List.ofFn p.2) (x p) = Φ.dualCylAt k K (List.ofFn p.2) (x p) := fun h0 =>
    dualCylAt_eq_of_agreeAt Φ Ψ k K fun m hm => hagree <| by
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · simpa using h0
      · exact horb_later _ (Or.inr rfl) (hx.nodup_snd p) m hm0 hm.le _
  refine ⟨x p, ht, ?_⟩
  by_cases hb : Φ.Bad k K p
  · obtain ⟨h0, h1, hτ⟩ := hY _ _ ((hbad_iff _).2 ⟨hb, rfl⟩)
    have hZ0 : x p ∈ Φ.goodPoints k K n x (p.2 0) := hself_good _ fun h => hp.ne h.2
    have hbad : ¬ Disjoint (Φ.dualCylAt k K (List.ofFn p.1) (x p))
        (Φ.dualCylAt k K (List.ofFn p.2) (x p)) := fun hd => hb ⟨x p, ht, hd⟩
    rw [hsnd hZ0]
    rw [List.ofFn_succ (f := p.1)] at hbad ⊢
    rw [dualCylAt_cons_eq_of_agreeAt Φ Ψ k K h0 h1 fun m hm => by
      rw [show Φ.comp ((List.ofFn fun i => p.1 i.succ).take m).reverse (Φ.f (p.1 0) (x p)) =
        Φ.comp (((p.1 0 :: List.ofFn fun i => p.1 i.succ).take (m + 1)).reverse) (x p) by
          rw [List.take_succ_cons, List.reverse_cons, Φ.comp_append]; rfl, ← List.ofFn_succ]
      exact hagree (horb_later _ (Or.inl rfl) (hx.nodup_fst p) (m + 1) (Nat.succ_pos m)
        (by rw [List.length_ofFn]; rw [List.length_ofFn] at hm; omega) _)]
    have hre_τ : δ ≤ |(Ψ.nonlin (p.1 0) (x p) - Φ.nonlin (p.1 0) (x p)).re| := by
      rwa [Complex.abs_re_eq_norm.2]
      rw [Complex.sub_im, Ψ.im_nonlin_ofReal _ (ofReal_mem_nbhd Ψ.ε_pos ht),
        Φ.im_nonlin_ofReal _ (ofReal_mem_nbhd Φ.ε_pos ht), sub_zero]
    exact disjoint_image_add_of_abs_sub_lt
      (fun a ha a' ha' => (Φ.abs_sub_le_cmax_pow_of_mem_dualCylAt hkK _ ht ha ha').trans_lt (by simpa using hn))
      (fun b hb b' hb' => (Φ.abs_sub_le_cmax_pow_of_mem_dualCylAt hkK _ ht hb hb').trans_lt (by simpa using hn))
      (not_disjoint_iff_nonempty_inter.1 hbad) hre_τ
  · have hZ0 : ∀ ℓ, x p ∈ Φ.goodPoints k K n x ℓ := fun ℓ => hself_good ℓ fun h => hb h.1
    rw [dualCylAt_eq_of_agreeAt Φ Ψ k K fun m hm => hagree <| by
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · simpa using hZ0 (List.ofFn p.1)[0]
      · exact horb_later _ (Or.inl rfl) (hx.nodup_fst p) m hm0 hm.le _,
      hsnd (hZ0 _)]
    exact hx.disjoint p (not_not.1 hb)

private theorem exists_invariant_cylinder_near (hN : 0 < N) (Φ : IFS N ε) :
    ∃ K > 0, ∃ η > 0, ∀ {ε' : ℝ} (Ψ : IFS N ε'), d2 Φ Ψ < η →
      ∀ u : ℕ → Fin N, ∀ y ∈ I, (Ψ.dualProj (.inf u) y).re ∈ Icc (-K) K := by
  obtain ⟨M', c', δ₀, hM', hc'0, hc'1, hδ₀, hbd⟩ := exists_uniform_dualTerm_bound hN Φ
  have hc : 0 < 1 - c' := sub_pos.2 hc'1
  refine ⟨M' / (1 - c') + 1, by positivity, δ₀, hδ₀, fun Ψ hΨ u y hy =>
    abs_le.1 ((Complex.abs_re_le_norm _).trans ?_)⟩
  exact (tsum_of_norm_bounded ((hasSum_geometric_of_lt_one hc'0 hc'1).mul_left M')
    fun n => hbd Ψ hΨ u n y hy).trans (by rw [div_eq_mul_inv]; linarith)

theorem exists_dualSSC_near (hN : 0 < N) (Φ : IFS N ε)
    (hI : ∀ i, ∀ x ∈ I, (Φ.f i x).re ∈ Ioo 0 1) (hnc : Φ.NoCoincidence) {r : ℝ} (hr : 0 < r) :
    ∃ ε' : ℝ, ∃ Ψ : IFS N ε', d2 Φ Ψ < r ∧ Ψ.DualSSC := by
  obtain ⟨K, hK0, η, hη, hstable⟩ := exists_invariant_cylinder_near hN Φ
  set δ := min r η / 50
  have hδ : 0 < δ := div_pos (lt_min hr hη) (by norm_num)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Φ.cmax ^ (n + 1) * (K - -K) < δ / 3 := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
      (show 0 < δ / 3 / (K - -K) from div_pos (by linarith) (by linarith)) Φ.cmax_lt_one
    exact ⟨n, (mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one Φ.cmax_nonneg Φ.cmax_lt_one.le (Nat.le_succ n))
      (by linarith)).trans_lt ((lt_div_iff₀ (by linarith)).1 hn)⟩
  obtain ⟨x, hx⟩ := Φ.lemma_4_1 (n + 1) (-K) K hnc
  have hbad_I : ∀ i, ∀ y ∈ Φ.badPoints (-K) K n x i, y ∈ I := fun i y hy => by
    obtain ⟨p, -, -, rfl⟩ := mem_badPoints.1 hy; exact hx.mem_I p
  have hgood_I : ∀ i, ∀ y ∈ Φ.goodPoints (-K) K n x i, y ∈ I := fun i y hy => by
    obtain ⟨p, -, hy⟩ := mem_orbitPoints.1 (Finset.mem_sdiff.1 hy).1
    rcases List.mem_append.1 hy with hy | hy <;>
      { obtain ⟨l, -, rfl⟩ := List.mem_map.1 hy; exact Φ.re_comp_mem_I _ (hx.mem_I p) }
  choose g hg using fun i => proposition_4_2 Φ.ε_pos (Φ.inClass i) (hI i)
    (Φ.badPoints (-K) K n x i) (Φ.goodPoints (-K) K n x i) (hbad_I i) (hgood_I i)
    (Finset.disjoint_left.2 fun _ hY hZ => (Finset.mem_sdiff.1 hZ).2 hY) hδ
  obtain ⟨ε', hε', hgε'⟩ := exists_inClass_forall fun i => (hg i).1
  let Ψ : IFS N ε' := ⟨g, hε', hgε'⟩
  have hd : d2 Φ Ψ < min r η := by
    have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    exact (ciSup_le fun i => (hg i).2.2.2).trans_lt (by dsimp [δ]; linarith [lt_min hr hη])
  refine ⟨ε', Ψ, hd.trans_le (min_le_left _ _), Ψ.dualSSC_of_cyl n
    (hstable Ψ (hd.trans_le (min_le_right _ _))) fun i j hij => ?_⟩
  rcases lt_or_gt_of_ne hij with h | h
  · exact hx.dualCylDisjoint Ψ (by linarith) hn (fun ℓ => (hg ℓ).2.1) (fun ℓ => (hg ℓ).2.2.1) (p := (i, j)) h
  · obtain ⟨t, ht, hdisj⟩ := hx.dualCylDisjoint Ψ (by linarith) hn
      (fun ℓ => (hg ℓ).2.1) (fun ℓ => (hg ℓ).2.2.1) (p := (j, i)) h
    exact ⟨t, ht, hdisj.symm⟩

end IFS

namespace OpenDense

private theorem iSup_norm_sub_le_add {F G H : ℂ → ℂ}
    (hF : Continuous fun x : I => F x) (hG : Continuous fun x : I => G x) (hH : Continuous fun x : I => H x) :
    (⨆ x : I, ‖F ((x : ℝ) : ℂ) - H ((x : ℝ) : ℂ)‖) ≤
      (⨆ x : I, ‖F ((x : ℝ) : ℂ) - G ((x : ℝ) : ℂ)‖) +
        ⨆ x : I, ‖G ((x : ℝ) : ℂ) - H ((x : ℝ) : ℂ)‖ :=
  Real.iSup_le (fun x => (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (add_le_add (le_ciSup (IFS.Continuity.bddAbove_norm_sub hF hG) x)
      (le_ciSup (IFS.Continuity.bddAbove_norm_sub hG hH) x)))
    (add_nonneg (Real.iSup_nonneg fun _ => norm_nonneg _) (Real.iSup_nonneg fun _ => norm_nonneg _))

theorem d2_le_add {N : ℕ} {ε ε' ε'' : ℝ} (Φ : IFS N ε) (Φ' : IFS N ε') (Ψ : IFS N ε'') :
    d2 Φ Ψ ≤ d2 Φ Φ' + d2 Φ' Ψ := by
  have nonneg : ∀ a b : ℂ → ℂ, 0 ≤ d2Map a b := fun _ _ =>
    add_nonneg (add_nonneg (Real.iSup_nonneg fun _ => norm_nonneg _)
      (Real.iSup_nonneg fun _ => norm_nonneg _)) (Real.iSup_nonneg fun _ => norm_nonneg _)
  refine Real.iSup_le (fun i => ?_)
    (add_nonneg (Real.iSup_nonneg fun _ => nonneg _ _) (Real.iSup_nonneg fun _ => nonneg _ _))
  obtain ⟨f0, f1, f2⟩ := IFS.Continuity.InClass.contJet Φ.ε_pos (Φ.inClass i)
  obtain ⟨g0, g1, g2⟩ := IFS.Continuity.InClass.contJet Φ'.ε_pos (Φ'.inClass i)
  obtain ⟨h0, h1, h2⟩ := IFS.Continuity.InClass.contJet Ψ.ε_pos (Ψ.inClass i)
  have hmap : d2Map (Φ.f i) (Ψ.f i) ≤ d2Map (Φ.f i) (Φ'.f i) + d2Map (Φ'.f i) (Ψ.f i) := by
    unfold d2Map
    linarith [iSup_norm_sub_le_add f0 g0 h0, iSup_norm_sub_le_add f1 g1 h1, iSup_norm_sub_le_add f2 g2 h2]
  exact hmap.trans (add_le_add
    (le_ciSup (f := fun j => d2Map (Φ.f j) (Φ'.f j)) (Set.finite_range _).bddAbove i)
    (le_ciSup (f := fun j => d2Map (Φ'.f j) (Ψ.f j)) (Set.finite_range _).bddAbove i))

end OpenDense

end AnalyticESC
