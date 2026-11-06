module

public import AnalyticESC.Generic.Class
public import AnalyticESC.Analysis
set_option hygiene false
local notation "𝖟" => hmem x
local notation "𝖞" => 4 + K
local notation "𝖝" => (Φ.differentiableOn_f i).differentiableAt (isOpen_nbhd.mem_nhds hz)
local notation "𝔣" => Φ.f i

local notation "𝔟" => 1 - t


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

variable {t x : ℝ}

open Set Topology

namespace IFS.Coincidences


/-! ## The affine maps `h_i` -/

/-- The common slope `a = 1/(2(N+2))` of the affine maps `h_i`. -/
noncomputable def slope (N : ℕ) : ℝ := 1 / (2 * (N + 2))

/-- The offset `b_i = (i+1)/(N+2)` of the affine map `h_i`. -/
noncomputable def offset (i : Fin N) : ℝ := (((i : ℕ) : ℝ) + 1) / (N + 2)

/-- `a > 0`. -/
theorem slope_pos : 0 < slope N := by unfold slope; positivity

/-- `a < 1`. -/
theorem slope_lt_one : slope N < 1 := by
  unfold slope
  bound

/-- `b_i > 0`. -/
theorem offset_pos (i : Fin N) : 0 < offset i := by unfold offset; positivity

/-- `h_i(I) = [b_i, b_i + a] ⊆ (0,1)`. -/
theorem offset_add_slope_lt_one (i : Fin N) : offset i + slope N < 1 := by
  have : (i : ℝ) + 1 ≤ N := by exact_mod_cast i.isLt
  unfold offset slope
  rw [div_add_div _ _ (by positivity) (by positivity), div_lt_one (by positivity)]
  nlinarith

/-- The intervals `h_i(I) = [b_i, b_i + a]` are pairwise disjoint. -/
theorem offset_add_slope_lt_offset {i j : Fin N} (hij : i < j) : offset i + slope N < offset j := by
  have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
  unfold offset slope
  rw [div_add_div _ _ (by positivity) (by positivity), div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_self_pos.2 (by positivity : (N + 2 : ℝ) ≠ 0)]

/-- The affine map `h_i(z) = a z + b_i`. -/
noncomputable def target (i : Fin N) (z : ℂ) : ℂ := slope N * z + offset i

/-- `h_i` is real at real points. -/
theorem target_ofReal (i : Fin N) (x : ℝ) : target i x = ((slope N * x + offset i : ℝ) : ℂ) := by aesop

/-! ## The perturbations `f_i^t` -/

variable (Φ : IFS N ε)

/-- The map `f_i^t = (1 - t) f_i + t h_i`, for a complex parameter `t`. -/
noncomputable def homotopy (t : ℂ) (i : Fin N) (z : ℂ) : ℂ := 𝔟 * Φ.f i z + t * target i z

local notation "𝔥" => homotopy Φ t i

/-- The composition `f^t_w = f^t_{w₁} ∘ ⋯ ∘ f^t_{w_k}` of the maps `f_i^t`. -/
noncomputable def compT (t : ℂ) (w : 𝔚 N) : ℂ → ℂ :=
  w.foldr (fun i g => 𝔥 ∘ g) id

/-- `f^t_{iw} = f_i^t ∘ f^t_w`. -/
theorem compT_cons t (i : Fin N) (w : 𝔚 N) :
    compT Φ t (i :: w) = 𝔥 ∘ compT Φ t w :=
  rfl

/-- `f_i^1 = h_i`. -/
theorem homotopy_one i z : homotopy Φ 1 i z = target i z := by simp [homotopy]

/-- For real `t`, the map `f_i^t` is real at the real points of `B_{2ε}`. -/
theorem im_homotopy_ofReal (t : ℝ) i (hx : (x : ℂ) ∈ 𝔑 ε) :
    (𝔥 x).im = 0 := by
  simp [homotopy, target, Φ.im_f_ofReal i hx]

/-- For real `t` and `x`, `Re f_i^t(x) = (1 - t) Re f_i(x) + t h_i(x)`. -/
theorem re_homotopy_ofReal (t : ℝ) i (x : ℝ) :
    (𝔥 x).re = 𝔟 * (Φ.f i x).re + t * (slope N * x + offset i) := by
  simp [homotopy, target]

/-- For `t ∈ [0,1]`, the map `f_i^t` sends `I` into `I`, and into `(0,1)` if `t > 0`. -/
theorem re_homotopy_mem_I (ht : t ∈ I) (i : Fin N) (hx : x ∈ I) :
    (𝔥 x).re ∈ I ∧ (0 < t → (𝔥 x).re ∈ Ioo 0 1) := by
  rw [re_homotopy_ofReal]
  have hf := (Φ.inClass i).re_mem_I x hx
  have := offset_pos i
  have := offset_add_slope_lt_one i
  have hs := slope_pos (N := N)
  have := mul_nonneg hs.le hx.1
  have := mul_le_of_le_one_right hs.le hx.2
  have := mul_nonneg (sub_nonneg.2 ht.2) hf.1
  have := mul_nonneg (sub_nonneg.2 ht.2) (sub_nonneg.2 hf.2)
  exact ⟨⟨by nlinarith [ht.1], by nlinarith [ht.1]⟩, fun h => ⟨by nlinarith, by nlinarith⟩⟩

/-- For `t ∈ [0,1]`, the compositions `f^t_w` send real points of `I` to real points of `I`. -/
theorem exists_compT_ofReal (ht : t ∈ I) w (hx : x ∈ I) :
    ∃ y ∈ I, compT Φ t w x = y := by
  induction w with
  | nil => exact ⟨x, hx, rfl⟩
  | cons i w ih =>
    obtain ⟨y, hy, hyx⟩ := ih
    refine ⟨(𝔥 y).re, (re_homotopy_mem_I Φ ht i hy).1, ?_⟩
    rw [compT_cons, Function.comp_apply, hyx]
    refine Complex.ext (by simp) ?_
    exact im_homotopy_ofReal Φ t i (Φ.ofReal_mem_nbhd2 hy)

/-! ## Distinct compositions of the affine maps -/

/-- For `x ∈ I`, the point `h_{iw}(x)` lies in `h_i(I) = [b_i, b_i + a]`. -/
theorem re_compT_one_cons_mem (i : Fin N) (w : 𝔚 N) (hx : x ∈ I) :
    (compT Φ 1 (i :: w) x).re ∈ Icc (offset i) (offset i + slope N) := by
  obtain ⟨y, hy, hyx⟩ := exists_compT_ofReal Φ one_mem_I w hx
  rw [Complex.ofReal_one] at hyx
  rw [compT_cons, Function.comp_apply, hyx, homotopy_one, target_ofReal, Complex.ofReal_re]
  have h3 : 0 ≤ slope N * y := mul_nonneg slope_pos.le hy.1
  have h4 : slope N * y ≤ slope N := mul_le_of_le_one_right slope_pos.le hy.2
  grind

/-- Compositions of the affine maps `h_i` along distinct finite words differ on `I`. -/
theorem exists_compT_one_ne u v (huv : u ≠ v) :
    ∃ x ∈ I, compT Φ 1 u x ≠ compT Φ 1 v x := by
  -- a nonempty word sends `0` to a point with positive real part
  induction u generalizing v with
  | nil =>
    obtain _ | ⟨j, v⟩ := v
    · grind
    exact ⟨0, zero_mem_I, fun h => ((fun i w => (offset_pos i).trans_le (re_compT_one_cons_mem Φ i w zero_mem_I).1) j v).ne' (by rw [← h]; simp [compT])⟩
  | cons i u ih =>
    obtain _ | ⟨j, v⟩ := v
    · exact ⟨0, zero_mem_I, fun h => ((fun i w => (offset_pos i).trans_le (re_compT_one_cons_mem Φ i w zero_mem_I).1) i u).ne' (by aesop)⟩
    by_cases hij : i = j
    · -- equal first letters: `h_i` is injective
      subst hij
      obtain ⟨x, hx, hne⟩ := ih v fun h => huv (by simp_all)
      refine ⟨x, hx, fun h => hne ?_⟩
      simp [compT_cons, homotopy_one] at h
      exact mul_left_cancel₀ (Complex.ofReal_ne_zero.2 slope_pos.ne') (add_right_cancel h)
    · -- distinct first letters: the images of `0` lie in disjoint intervals
      refine ⟨0, zero_mem_I, fun h => ?_⟩
      have hi := re_compT_one_cons_mem Φ i u zero_mem_I
      have hj := re_compT_one_cons_mem Φ j v zero_mem_I
      rw [h] at hi
      rcases lt_or_gt_of_ne hij with hlt | hlt <;> linarith [offset_add_slope_lt_offset hlt, hi.1, hi.2, hj.1, hj.2]

/-! ## The perturbations lie in the class -/

/-- `(f_i^t)' = (1 - t) f_i' + t a` where `f_i` is differentiable. -/
theorem hasDerivAt_homotopy t (i : Fin N) {z : ℂ} (hz : DifferentiableAt ℂ 𝔣 z) :
    HasDerivAt 𝔥 (𝔟 * 𝔡 Φ i z + t * slope N) z := by
  have h := (hz.hasDerivAt.const_mul 𝔟).add
    ((((hasDerivAt_id z).const_mul (slope N : ℂ)).add_const (offset i : ℂ)).const_mul t)
  aesop

/-- `(f_i^t)' = (1 - t) f_i' + t a` on `B_{2ε}`. -/
theorem deriv_homotopy t (i : Fin N) {z : ℂ} (hz : z ∈ 𝔑 ε) :
    deriv 𝔥 z = 𝔟 * 𝔡 Φ i z + t * slope N :=
  (hasDerivAt_homotopy Φ t i
    𝖝).deriv

/-- For `0 < t < c_min/(c_min + 1)`, the map `f_i^t` lies in `S^ω_ε(I)`. -/
theorem inClass_homotopy (ht0 : 0 < t) (ht : t * (Φ.cmin + 1) < Φ.cmin) i :
    InClass ε 𝔥 := by
  have hc := Φ.cmin_nonneg
  have ht1 : t < 1 := by nlinarith
  have ha1 := slope_lt_one (N := N)
  have key : ∀ z ∈ 𝔹 ε,
      |‖deriv 𝔥 z‖ - 𝔟 * ‖𝔡 Φ i z‖| ≤ t * slope N := fun z hz => by
    have := abs_norm_sub_norm_le (deriv 𝔥 z) ((1 - t : ℂ) * 𝔡 Φ i z)
    rw [deriv_homotopy Φ t i (IFS.closure_nbhd_subset_two hz)] at *
    rw [add_sub_cancel_left, norm_mul, norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_of_nonneg (by linarith),
      Complex.norm_of_nonneg ht0.le, Complex.norm_of_nonneg slope_pos.le] at this
    exact_mod_cast this
  refine InClass.of_deriv Φ.ε_pos (fun z hz => (hasDerivAt_homotopy Φ t i
    𝖝).differentiableAt.differentiableWithinAt)
    (fun x hx => im_homotopy_ofReal Φ t i hx) (fun x hx => (re_homotopy_mem_I Φ ⟨ht0.le, ht1.le⟩ i hx).1)
    (fun z hz h0 => ?_) fun z hz => ?_
  · have := key z hz
    rw [h0, norm_zero] at this
    nlinarith [abs_le.1 this, mul_le_mul_of_nonneg_left (Φ.cmin_le_norm_deriv i hz) (by linarith : 0 ≤ 1 - t)]
  · nlinarith [abs_le.1 (key z hz), mul_lt_mul_of_pos_left ((Φ.inClass i).norm_deriv_lt_one z hz) (by linarith : 0 < 1 - t)]

/-! ## The distance to the perturbation -/

/-- A common bound for the second derivatives `f_i''` on `I`. -/
theorem exists_deriv_deriv_bound :
    ∃ K, 0 ≤ K ∧ ∀ i, Ɐ ‖𝔇 𝔣 x‖ ≤ K := by
  choose C hC using fun i => isCompact_image_I.exists_bound_of_continuousOn
    ((((Φ.differentiableOn_f i).deriv isOpen_nbhd).deriv isOpen_nbhd).continuousOn.mono Φ.image_I_subset_nbhd2)
  exact ⟨max 0 (⨆ i, C i), le_max_left _ _, fun i x hx => (hC i x (mem_image_of_mem _ hx)).trans
    ((le_ciSup (Finite.bddAbove_range C) i).trans (le_max_right _ _))⟩

/-- `d₂(f_i, f_i^t) ≤ t (4 + K)` for `t ∈ [0,1]`, where `K` bounds `|f_i''|` on `I`. -/
theorem d2Map_homotopy_le (i : Fin N) (hK : 0 ≤ K)
    (hK' : Ɐ ‖𝔇 𝔣 x‖ ≤ K) (ht : t ∈ I) :
    d2Map 𝔣 𝔥 ≤ t * 𝖞 := by
  have hmem : ∀ x : I, (x : ℂ) ∈ 𝔑 ε := fun x => Φ.ofReal_mem_nbhd2 x.2
  have ht0 := ht.1
  have key : ∀ {D : ℂ} {c}, ‖D‖ ≤ c → ‖t * D‖ ≤ t * c := fun h => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
    nlinarith
  have hs := slope_pos (N := N)
  -- the values differ by `t (f_i - h_i)`, the first derivatives by `t (f_i' - a)` and the second
  -- derivatives by `t f_i''`
  have e0 : ∀ x : I, ‖Φ.f i x - 𝔥 x‖ ≤ t * 2 := by
    intro x
    have : ‖Φ.f i x‖ ≤ 1 := Φ.norm_comp_ofReal_le_one [i] x.2
    have : ‖target i x‖ ≤ 1 := by
      rw [target_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith [offset_pos i, offset_add_slope_lt_one i, x.2.1, x.2.2]
    exact show Φ.f i x - 𝔥 x = t * (Φ.f i x - target i x) by unfold homotopy; ring ▸ key ((norm_sub_le _ _).trans (by linarith))
  have e1 : ∀ x : I, ‖𝔡 Φ i x - deriv 𝔥 x‖ ≤ t * 2 := by
    intro x
    rw [deriv_homotopy Φ t i 𝖟, show ∀ a b : ℂ, a - (𝔟 * a + t * b) = t * (a - b)
      by grind]
    refine key ((norm_sub_le _ _).trans ?_)
    rw [Complex.norm_real, Real.norm_of_nonneg hs.le]
    linarith [(Φ.inClass i).norm_deriv_lt_one _ (Φ.ofReal_mem_cl x.2), slope_lt_one (N := N)]
  have e2 : ∀ x : I, ‖𝔇 𝔣 x - 𝔇 𝔥 x‖ ≤ t * K :=
    fun x => by
    have heq : deriv 𝔥 =ᶠ[𝓝 (x : ℂ)]
        fun z => 𝔟 * 𝔡 Φ i z + t * slope N := by
      filter_upwards [isOpen_nbhd.mem_nhds 𝖟] with z hz using deriv_homotopy Φ t i hz
    rw [heq.deriv_eq, deriv_add_const, deriv_const_mul _ (((Φ.differentiableOn_f i).deriv
      isOpen_nbhd).differentiableAt (isOpen_nbhd.mem_nhds 𝖟)),
      show ∀ a : ℂ, a - 𝔟 * a = t * a by grind]
    exact key (hK' x x.2)
  unfold d2Map
  linarith [Real.iSup_le e0 (by positivity), Real.iSup_le e1 (by positivity),
    Real.iSup_le e2 (by positivity)]

/-! ## Coincidences for finitely many parameters -/

/-- For a fixed word `w` and `x ∈ I`, the map `t ↦ f^t_w(x)` is holomorphic on an open set
containing `[0,1]`. -/
theorem exists_differentiableOn_compT w (hx : x ∈ I) :
    ∃ O, IsOpen O ∧ Iℂ ⊆ O ∧
      DifferentiableOn ℂ (fun t => compT Φ t w x) O := by
  induction w with
  | nil => exact ⟨univ, isOpen_univ, subset_univ _, differentiableOn_const _⟩
  | cons i w ih =>
    obtain ⟨O, hO, hIO, hd⟩ := ih
    refine ⟨O ∩ (fun t => compT Φ t w x) ⁻¹' 𝔑 ε,
      hd.continuousOn.isOpen_inter_preimage hO isOpen_nbhd, ?_, ?_⟩
    · -- for `t ∈ [0,1]`, `f^t_w(x)` is a point of `I`
      rintro _ ⟨s, hs, rfl⟩
      obtain ⟨y, hy, hyx⟩ := exists_compT_ofReal Φ hs w hx
      exact ⟨hIO (mem_image_of_mem _ hs), show compT Φ s w x ∈ _ from hyx ▸ Φ.ofReal_mem_nbhd2 hy⟩
    · have hg := hd.mono (inter_subset_left (t := (fun t => compT Φ t w x) ⁻¹' 𝔑 ε))
      have hf := (Φ.differentiableOn_f i).comp hg fun t ht => ht.2
      simp [compT_cons, homotopy, target]
      fun_prop

/-- If `h_u(x) ≠ h_v(x)`, then `f^t_u(x) = f^t_v(x)` for finitely many `t ∈ [0,1]` only. -/
theorem finite_compT_eq (hx : x ∈ I)
    (hne : compT Φ 1 u x ≠ compT Φ 1 v x) :
    {t : ℝ | t ∈ I ∧ compT Φ t u x = compT Φ t v x}.Finite := by
  obtain ⟨Ou, hOu, hIu, hdu⟩ := exists_differentiableOn_compT Φ u hx
  obtain ⟨Ov, hOv, hIv, hdv⟩ := exists_differentiableOn_compT Φ v hx
  obtain ⟨ρ, hρ, hsub⟩ :=
    isCompact_image_I.exists_thickening_subset_open (hOu.inter hOv) (subset_inter hIu hIv)
  refine (finite_zeros hρ (g := fun t => compT Φ t u x - compT Φ t v x) ((hdu.mono (hsub.trans inter_subset_left)).sub
    (hdv.mono (hsub.trans inter_subset_right))) ⟨1, one_mem_I, by positivity⟩).subset
    fun t ⟨ht, heq⟩ => ⟨ht, sub_eq_zero.2 heq⟩

end IFS.Coincidences

namespace IFS

open Coincidences


/-- The interpolation at the start of the density proof of Theorem 1.4. Every `Φ ∈ 𝔖_N(ε)` has, for
every `r > 0`, a perturbation `Ψ ∈ 𝔖_N(ε)` with `d₂(Φ, Ψ) < r` whose maps send `[0,1]` into `(0,1)`
and whose compositions along distinct finite words differ on `[0,1]`. -/
theorem exists_noCoincidence_near (Φ : IFS N ε) (hr : 0 < r) :
    ∃ Ψ : IFS N ε, d2 Φ Ψ < r ∧ (∀ i, Ɐ (Ψ.f i x).re ∈ Ioo 0 1) ∧ Ψ.NoCoincidence := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · -- without maps, `Ψ = Φ` works: every word is empty
    subst hN
    refine ⟨Φ, by simpa [d2] using hr, fun i => i.elim0, fun u v huv => ?_⟩
    rcases u with _ | ⟨⟨_, ⟨⟩⟩, _⟩
    rcases v with _ | ⟨⟨_, ⟨⟩⟩, _⟩
    simp_all
  set c := Φ.cmin
  have hc := Φ.cmin_pos hN
  obtain ⟨K, hK, hK'⟩ := exists_deriv_deriv_bound Φ
  -- the parameters `t ∈ [0,1]` at which two compositions along distinct words coincide on `I`
  set B : Set ℝ := ⋃ p : {p : 𝔚 N × 𝔚 N // p.1 ≠ p.2},
    {t | t ∈ I ∧ ¬∃ x ∈ I, compT Φ t p.1.1 x ≠ compT Φ t p.1.2 x}
  have hB : B.Countable := countable_iUnion fun p => by
    obtain ⟨x, hx, hne⟩ := exists_compT_one_ne Φ _ _ p.2
    exact ((finite_compT_eq Φ hx hne).subset fun t ht => ⟨ht.1, by_contra fun h => ht.2 ⟨x, hx, h⟩⟩).countable
  set t₀ := min (c / (c + 1)) (r / 𝖞)
  have ht₀ : 0 < t₀ := lt_min (by positivity) (by positivity)
  obtain ⟨t, htB, ht⟩ := (hB.dense_compl ℝ).exists_mem_open isOpen_Ioo (nonempty_Ioo.2 ht₀)
  have ht1 : t * (c + 1) < c :=
    (lt_div_iff₀ (by positivity)).1 (ht.2.trans_le (min_le_left _ _))
  have ht2 : t * 𝖞 < r :=
    (lt_div_iff₀ (by positivity)).1 (ht.2.trans_le (min_le_right _ _))
  have htI : t ∈ I := ⟨ht.1.le, by nlinarith⟩
  exact ⟨⟨homotopy Φ t, Φ.ε_pos, inClass_homotopy Φ ht.1 ht1⟩, (Real.iSup_le (fun i =>
    d2Map_homotopy_le Φ i hK (hK' i) htI) (mul_nonneg ht.1.le (by linarith))).trans_lt ht2,
    fun i x hx => (re_homotopy_mem_I Φ htI i hx).2 ht.1,
    fun u v huv => by_contra fun h => htB (mem_iUnion.2 ⟨⟨(u, v), huv⟩, htI, h⟩)⟩

end IFS

end AnalyticESC
