module

public import AnalyticESC.Defs

@[expose] public section

/-!
# Basic properties

The neighbourhoods `B_δ`, consequences of the conditions (A)–(C) defining the class, the
constants `c_min` and `c_max`, compositions along finite words, and the passage between complex
derivatives and derivatives of real restrictions.
-/

namespace AnalyticESC

open Set Metric Filter Topology

/-! ## The neighbourhoods `B_δ` -/

/-- The image of `I` in `ℂ` is compact. -/
theorem isCompact_image_I : IsCompact (((↑) : ℝ → ℂ) '' I) :=
  isCompact_Icc.image Complex.continuous_ofReal

theorem isOpen_nbhd (δ : ℝ) : IsOpen (nbhd δ) := isOpen_thickening

theorem convex_nbhd (δ : ℝ) : Convex ℝ (nbhd δ) :=
  ((convex_Icc (0 : ℝ) 1).linear_image Complex.ofRealCLM.toLinearMap).thickening δ

theorem isPreconnected_nbhd (δ : ℝ) : IsPreconnected (nbhd δ) := (convex_nbhd δ).isPreconnected

theorem isCompact_closure_nbhd (δ : ℝ) : IsCompact (closure (nbhd δ)) :=
  isCompact_image_I.isBounded.thickening.isCompact_closure

theorem ofReal_mem_nbhd {δ : ℝ} (hδ : 0 < δ) {x : ℝ} (hx : x ∈ I) : (x : ℂ) ∈ nbhd δ :=
  self_subset_thickening hδ _ (mem_image_of_mem _ hx)

theorem ball_subset_nbhd {δ x : ℝ} (hx : x ∈ I) : ball (x : ℂ) δ ⊆ nbhd δ :=
  ball_subset_thickening (mem_image_of_mem _ hx) δ

theorem nbhd_mono {δ δ' : ℝ} (h : δ ≤ δ') : nbhd δ ⊆ nbhd δ' := thickening_mono h _

theorem nbhd_of_nonpos {δ : ℝ} (h : δ ≤ 0) : nbhd δ = ∅ := thickening_of_nonpos h _

theorem zero_mem_closure_nbhd {δ : ℝ} (hδ : 0 < δ) : (0 : ℂ) ∈ closure (nbhd δ) :=
  subset_closure (by simpa using ofReal_mem_nbhd hδ (x := 0) ⟨le_rfl, zero_le_one⟩)

theorem closure_nbhd_subset {δ δ' : ℝ} (h : δ < δ') : closure (nbhd δ) ⊆ nbhd δ' := by
  rcases le_or_gt δ' 0 with h' | h'
  · simp [nbhd_of_nonpos (h.le.trans h')]
  · exact (closure_thickening_subset_cthickening δ _).trans (cthickening_subset_thickening' h' h _)

/-! ## Real restrictions -/

/-- The derivative of the real restriction of a complex differentiable map. -/
theorem hasDerivAt_re_ofReal {g : ℂ → ℂ} {x : ℝ} (hg : DifferentiableAt ℂ g x) :
    HasDerivAt (fun t : ℝ => (g t).re) (deriv g x).re x := hg.hasDerivAt.real_of_complex

/-- The real points of an open subset of `ℂ` form an open subset of `ℝ`. -/
theorem isOpen_setOf_ofReal_mem {U : Set ℂ} (hU : IsOpen U) : IsOpen {t : ℝ | (t : ℂ) ∈ U} :=
  hU.preimage Complex.continuous_ofReal

/-- Iterated derivatives of a map holomorphic on an open set are holomorphic there. -/
theorem differentiableOn_iteratedDeriv_of_isOpen {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) (k : ℕ) : DifferentiableOn ℂ (iteratedDeriv k g) U := by
  induction k with
  | zero => simpa using hg
  | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv hU

/-- Iterated derivatives of the real restriction of a holomorphic map. -/
theorem iteratedDeriv_re_ofReal {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) (k : ℕ) {x : ℝ} (hx : (x : ℂ) ∈ U) :
    iteratedDeriv k (fun t : ℝ => (g t).re) x = (iteratedDeriv k g x).re := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have heq : iteratedDeriv k (fun t : ℝ => (g t).re) =ᶠ[𝓝 x]
        fun t => (iteratedDeriv k g t).re := by
      filter_upwards [(isOpen_setOf_ofReal_mem hU).mem_nhds hx] with _ using ih
    rw [iteratedDeriv_succ, heq.deriv_eq, iteratedDeriv_succ]
    exact (hasDerivAt_re_ofReal ((differentiableOn_iteratedDeriv_of_isOpen hU hg k).differentiableAt
      (hU.mem_nhds hx))).deriv

/-- The real restriction of a holomorphic map is smooth on the real points of its domain. -/
theorem contDiffOn_re_ofReal {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) :
    ContDiffOn ℝ ⊤ (fun t : ℝ => (g t).re) {t : ℝ | (t : ℂ) ∈ U} := fun _ hx =>
  ((hg.contDiffOn hU).contDiffAt (hU.mem_nhds hx)).real_of_complex.contDiffWithinAt

/-- A holomorphic map that is real at the real points of an open set has real derivative
there. -/
theorem im_deriv_eq_zero {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (hreal : ∀ t : ℝ, (t : ℂ) ∈ U → (g t).im = 0) {x : ℝ} (hx : (x : ℂ) ∈ U) :
    (deriv g x).im = 0 := by
  refine (Complex.imCLM.hasFDerivAt.comp_hasDerivAt x
    (hg.differentiableAt (hU.mem_nhds hx)).hasDerivAt.comp_ofReal).unique
    ((hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq ?_)
  filter_upwards [(isOpen_setOf_ofReal_mem hU).mem_nhds hx] with t ht using hreal t ht

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-! ## Single maps -/

theorem nbhd_subset_two : nbhd ε ⊆ nbhd (2 * ε) := by
  rcases le_or_gt ε 0 with h | h
  · simp [nbhd_of_nonpos h]
  · exact nbhd_mono (by linarith)

theorem closure_nbhd_subset_two : closure (nbhd ε) ⊆ nbhd (2 * ε) := by
  rcases le_or_gt ε 0 with h | h
  · simp [nbhd_of_nonpos h]
  · exact closure_nbhd_subset (by linarith)

theorem differentiableOn_f (i : Fin N) : DifferentiableOn ℂ (Φ.f i) (nbhd (2 * ε)) :=
  (Φ.inClass i).differentiableOn

theorem differentiableAt_f (i : Fin N) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    DifferentiableAt ℂ (Φ.f i) z :=
  (Φ.differentiableOn_f i).differentiableAt ((isOpen_nbhd _).mem_nhds (closure_nbhd_subset_two hz))

theorem continuousOn_deriv_f (i : Fin N) : ContinuousOn (deriv (Φ.f i)) (nbhd (2 * ε)) :=
  ((Φ.differentiableOn_f i).deriv (isOpen_nbhd _)).continuousOn

theorem mapsTo_f (i : Fin N) : MapsTo (Φ.f i) (nbhd ε) (nbhd ε) :=
  fun _ hz => (Φ.inClass i).mapsTo (subset_closure hz)

theorem im_f_ofReal (i : Fin N) {t : ℝ} (ht : (t : ℂ) ∈ nbhd (2 * ε)) : (Φ.f i t).im = 0 :=
  (Φ.inClass i).im_eq_zero t ht

theorem continuousOn_norm_deriv_f (i : Fin N) :
    ContinuousOn (fun z => ‖deriv (Φ.f i) z‖) (closure (nbhd ε)) :=
  ((Φ.continuousOn_deriv_f i).mono closure_nbhd_subset_two).norm

theorem cmax_nonneg : 0 ≤ Φ.cmax :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _

theorem cmin_nonneg : 0 ≤ Φ.cmin :=
  Real.iInf_nonneg fun _ => Real.iInf_nonneg fun _ => norm_nonneg _

theorem cmax_lt_one : Φ.cmax < 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [cmax]
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨i, hi'⟩ := exists_eq_ciSup_of_finite
    (f := fun i : Fin N => ⨆ z : closure (nbhd ε), ‖deriv (Φ.f i) z‖)
  have : Nonempty (closure (nbhd ε)) := ⟨⟨0, zero_mem_closure_nbhd Φ.ε_pos⟩⟩
  obtain ⟨z, hz, hmax⟩ := (isCompact_closure_nbhd ε).exists_isMaxOn
    ⟨0, zero_mem_closure_nbhd Φ.ε_pos⟩ (Φ.continuousOn_norm_deriv_f i)
  rw [cmax, ← hi']
  exact (ciSup_le fun w => hmax w.2).trans_lt ((Φ.inClass i).norm_deriv_lt_one z hz)

theorem norm_deriv_le_cmax (i : Fin N) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    ‖deriv (Φ.f i) z‖ ≤ Φ.cmax :=
  (le_ciSup (image_eq_range (fun z => ‖deriv (Φ.f i) z‖) _ ▸
    (isCompact_closure_nbhd ε).bddAbove_image (Φ.continuousOn_norm_deriv_f i)) ⟨z, hz⟩).trans
    (le_ciSup (f := fun i => ⨆ z : closure (nbhd ε), ‖deriv (Φ.f i) z‖)
      (finite_range _).bddAbove i)

theorem cmin_pos (hN : 0 < N) : 0 < Φ.cmin := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨i, hi'⟩ := (range_nonempty
    (fun i : Fin N => ⨅ z : closure (nbhd ε), ‖deriv (Φ.f i) z‖)).csInf_mem (finite_range _)
  have : Nonempty (closure (nbhd ε)) := ⟨⟨0, zero_mem_closure_nbhd Φ.ε_pos⟩⟩
  obtain ⟨z, hz, hmin⟩ := (isCompact_closure_nbhd ε).exists_isMinOn
    ⟨0, zero_mem_closure_nbhd Φ.ε_pos⟩ (Φ.continuousOn_norm_deriv_f i)
  rw [cmin, iInf, ← hi']
  exact (norm_pos_iff.2 ((Φ.inClass i).deriv_ne_zero z hz)).trans_le (le_ciInf fun w => hmin w.2)

theorem cmin_le_norm_deriv (i : Fin N) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    Φ.cmin ≤ ‖deriv (Φ.f i) z‖ :=
  (ciInf_le (f := fun i => ⨅ z : closure (nbhd ε), ‖deriv (Φ.f i) z‖)
    (finite_range _).bddBelow i).trans
    (ciInf_le (f := fun z : closure (nbhd ε) => ‖deriv (Φ.f i) z‖)
      ⟨0, by rintro _ ⟨_, rfl⟩; exact norm_nonneg _⟩ ⟨z, hz⟩)

theorem cmin_le_cmax (hN : 0 < N) : Φ.cmin ≤ Φ.cmax :=
  (Φ.cmin_le_norm_deriv ⟨0, hN⟩ (zero_mem_closure_nbhd Φ.ε_pos)).trans
    (Φ.norm_deriv_le_cmax ⟨0, hN⟩ (zero_mem_closure_nbhd Φ.ε_pos))

theorem cmax_pos (hN : 0 < N) : 0 < Φ.cmax :=
  (Φ.cmin_pos hN).trans_le (Φ.cmin_le_cmax hN)

/-- `f_i''/f_i'` is complex differentiable at every point of `cl B_ε`. -/
theorem differentiableAt_nonlin (i : Fin N) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    DifferentiableAt ℂ (Φ.nonlin i) z := by
  have hz2 := (isOpen_nbhd _).mem_nhds (closure_nbhd_subset_two hz)
  have hd := (Φ.differentiableOn_f i).deriv (isOpen_nbhd _)
  exact ((hd.deriv (isOpen_nbhd _)).differentiableAt hz2).div (hd.differentiableAt hz2)
    ((Φ.inClass i).deriv_ne_zero z hz)

theorem exists_nonlin_bound :
    ∃ M, 0 ≤ M ∧ ∀ i, ∀ z ∈ closure (nbhd ε), ‖Φ.nonlin i z‖ ≤ M := by
  choose C hC using fun i => (isCompact_closure_nbhd ε).exists_bound_of_continuousOn
    fun z hz => (Φ.differentiableAt_nonlin i hz).continuousAt.continuousWithinAt
  exact ⟨∑ i, |C i|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun i z hz =>
    (hC i z hz).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)))⟩

theorem norm_deriv_deriv_le (i : Fin N) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    ‖deriv (deriv (Φ.f i)) z‖ ≤ ‖Φ.nonlin i z‖ := by
  rw [← div_mul_cancel₀ (deriv (deriv (Φ.f i)) z) ((Φ.inClass i).deriv_ne_zero z hz), norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) ((Φ.inClass i).norm_deriv_lt_one z hz).le

theorem norm_deriv_f_sub_le {i : Fin N} {M : ℝ} (hM : ∀ z ∈ closure (nbhd ε), ‖Φ.nonlin i z‖ ≤ M)
    {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) :
    ‖deriv (Φ.f i) a - deriv (Φ.f i) b‖ ≤ M * ‖(a : ℂ) - b‖ :=
  (convex_nbhd ε).norm_image_sub_le_of_norm_deriv_le
    (fun _ hz => ((Φ.differentiableOn_f i).deriv (isOpen_nbhd _)).differentiableAt
      ((isOpen_nbhd _).mem_nhds (nbhd_subset_two hz)))
    (fun z hz => (Φ.norm_deriv_deriv_le i (subset_closure hz)).trans (hM z (subset_closure hz)))
    (ofReal_mem_nbhd Φ.ε_pos hb) (ofReal_mem_nbhd Φ.ε_pos ha)

theorem im_deriv_f_ofReal (i : Fin N) {t : ℝ} (ht : (t : ℂ) ∈ nbhd (2 * ε)) :
    (deriv (Φ.f i) t).im = 0 :=
  im_deriv_eq_zero (isOpen_nbhd _) (Φ.differentiableOn_f i) (fun _ hs => Φ.im_f_ofReal i hs) ht

theorem im_nonlin_ofReal (i : Fin N) {t : ℝ} (ht : (t : ℂ) ∈ nbhd ε) :
    (Φ.nonlin i t).im = 0 := by
  have ht2 := nbhd_subset_two ht
  have hdd := im_deriv_eq_zero (isOpen_nbhd _) ((Φ.differentiableOn_f i).deriv (isOpen_nbhd _))
    (fun _ hs => Φ.im_deriv_f_ofReal i hs) ht2
  simp [nonlin, Complex.div_im, Φ.im_deriv_f_ofReal i ht2, hdd]

/-! ## Compositions along finite words -/

@[simp] theorem comp_nil : Φ.comp [] = id := rfl

@[simp] theorem comp_cons (i : Fin N) (w : List (Fin N)) : Φ.comp (i :: w) = Φ.f i ∘ Φ.comp w :=
  rfl

theorem comp_append (u v : List (Fin N)) : Φ.comp (u ++ v) = Φ.comp u ∘ Φ.comp v := by
  induction u with
  | nil => rfl
  | cons i u ih => rw [List.cons_append, comp_cons, ih, comp_cons]; rfl

theorem mapsTo_comp (w : List (Fin N)) : MapsTo (Φ.comp w) (nbhd ε) (nbhd ε) := by
  induction w with
  | nil => exact mapsTo_id _
  | cons i w ih => exact (Φ.mapsTo_f i).comp ih

theorem mapsTo_comp_closure (w : List (Fin N)) :
    MapsTo (Φ.comp w) (closure (nbhd ε)) (closure (nbhd ε)) := by
  induction w with
  | nil => exact mapsTo_id _
  | cons i w ih => exact ((Φ.inClass i).mapsTo.mono_right subset_closure).comp ih

theorem differentiableAt_comp (w : List (Fin N)) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    DifferentiableAt ℂ (Φ.comp w) z := by
  induction w with
  | nil => exact differentiableAt_id
  | cons i w ih => exact (Φ.differentiableAt_f i (Φ.mapsTo_comp_closure w hz)).comp z ih

theorem differentiableOn_comp (w : List (Fin N)) : DifferentiableOn ℂ (Φ.comp w) (nbhd ε) :=
  fun _ hz => (Φ.differentiableAt_comp w (subset_closure hz)).differentiableWithinAt

theorem deriv_comp_cons (i : Fin N) (w : List (Fin N)) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    deriv (Φ.comp (i :: w)) z = deriv (Φ.f i) (Φ.comp w z) * deriv (Φ.comp w) z :=
  deriv_comp z (Φ.differentiableAt_f i (Φ.mapsTo_comp_closure w hz)) (Φ.differentiableAt_comp w hz)

theorem deriv_comp_append (u v : List (Fin N)) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    deriv (Φ.comp (u ++ v)) z = deriv (Φ.comp u) (Φ.comp v z) * deriv (Φ.comp v) z := by
  rw [comp_append]
  exact deriv_comp z (Φ.differentiableAt_comp u (Φ.mapsTo_comp_closure v hz))
    (Φ.differentiableAt_comp v hz)

theorem norm_deriv_comp_le (w : List (Fin N)) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    ‖deriv (Φ.comp w) z‖ ≤ Φ.cmax ^ w.length := by
  induction w with
  | nil => simp [deriv_id]
  | cons i w ih =>
    rw [Φ.deriv_comp_cons i w hz, norm_mul, List.length_cons, pow_succ']
    exact mul_le_mul (Φ.norm_deriv_le_cmax i (Φ.mapsTo_comp_closure w hz)) ih (norm_nonneg _)
      Φ.cmax_nonneg

theorem cmin_pow_le_norm_deriv_comp (w : List (Fin N)) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    Φ.cmin ^ w.length ≤ ‖deriv (Φ.comp w) z‖ := by
  induction w with
  | nil => simp [deriv_id]
  | cons i w ih =>
    rw [Φ.deriv_comp_cons i w hz, norm_mul, List.length_cons, pow_succ']
    exact mul_le_mul (Φ.cmin_le_norm_deriv i (Φ.mapsTo_comp_closure w hz)) ih
      (pow_nonneg Φ.cmin_nonneg _) (norm_nonneg _)

theorem deriv_comp_ne_zero (w : List (Fin N)) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    deriv (Φ.comp w) z ≠ 0 := by
  induction w with
  | nil => simp [deriv_id]
  | cons i w ih =>
    rw [Φ.deriv_comp_cons i w hz]
    exact mul_ne_zero ((Φ.inClass i).deriv_ne_zero _ (Φ.mapsTo_comp_closure w hz)) ih

/-- A uniform bound for all compositions on `cl B_ε`. -/
theorem exists_comp_bound : ∃ R, 0 ≤ R ∧ ∀ w, ∀ z ∈ closure (nbhd ε), ‖Φ.comp w z‖ ≤ R := by
  obtain ⟨R, hR⟩ := (isCompact_closure_nbhd ε).isBounded.exists_norm_le
  exact ⟨max R 0, le_max_right _ _,
    fun w z hz => (hR _ (Φ.mapsTo_comp_closure w hz)).trans (le_max_left _ _)⟩

theorem norm_comp_sub_le (w : List (Fin N)) {z z' : ℂ} (hz : z ∈ nbhd ε) (hz' : z' ∈ nbhd ε) :
    ‖Φ.comp w z - Φ.comp w z'‖ ≤ Φ.cmax ^ w.length * ‖z - z'‖ :=
  (convex_nbhd ε).norm_image_sub_le_of_norm_deriv_le
    (fun _ hx => Φ.differentiableAt_comp w (subset_closure hx))
    (fun _ hx => Φ.norm_deriv_comp_le w (subset_closure hx)) hz' hz

/-- `|f_w(x) - f_w(y)| ≤ c_max^{|w|} |x - y|` on `I`. -/
theorem abs_re_comp_sub_le_mul (w : List (Fin N)) {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) :
    |(Φ.comp w x).re - (Φ.comp w y).re| ≤ Φ.cmax ^ w.length * |x - y| := by
  have h := Φ.norm_comp_sub_le w (ofReal_mem_nbhd Φ.ε_pos hx) (ofReal_mem_nbhd Φ.ε_pos hy)
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  exact (Complex.sub_re _ _ ▸ Complex.abs_re_le_norm _).trans h

/-- `|f_w(y) - f_w(z)| ≤ c_max^{|w|}` for `y, z ∈ I`. -/
theorem abs_re_comp_sub_le (w : List (Fin N)) {y z : ℝ} (hy : y ∈ I) (hz : z ∈ I) :
    |(Φ.comp w y).re - (Φ.comp w z).re| ≤ Φ.cmax ^ w.length :=
  (Φ.abs_re_comp_sub_le_mul w hy hz).trans (mul_le_of_le_one_right (pow_nonneg Φ.cmax_nonneg _)
    (abs_sub_le_iff.2 ⟨by linarith [hy.2, hz.1], by linarith [hz.2, hy.1]⟩))

theorem im_comp_ofReal (w : List (Fin N)) {t : ℝ} (ht : (t : ℂ) ∈ nbhd ε) :
    (Φ.comp w t).im = 0 := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [comp_cons, Function.comp_apply]
    have h1 : Φ.comp w t = ((Φ.comp w t).re : ℂ) := Complex.ext (by simp) (by simp [ih])
    rw [h1]
    exact Φ.im_f_ofReal i (h1 ▸ nbhd_subset_two (Φ.mapsTo_comp w ht))

theorem comp_ofReal (w : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    Φ.comp w x = ((Φ.comp w x).re : ℂ) :=
  Complex.ext (by simp) (by simp [Φ.im_comp_ofReal w (ofReal_mem_nbhd Φ.ε_pos hx)])

theorem re_comp_mem_I (w : List (Fin N)) {x : ℝ} (hx : x ∈ I) : (Φ.comp w x).re ∈ I := by
  induction w with
  | nil => simpa using hx
  | cons i w ih =>
    rw [comp_cons, Function.comp_apply, Φ.comp_ofReal w hx]
    exact (Φ.inClass i).re_mem_I _ ih

theorem im_deriv_comp_ofReal (w : List (Fin N)) {t : ℝ} (ht : (t : ℂ) ∈ nbhd ε) :
    (deriv (Φ.comp w) t).im = 0 :=
  im_deriv_eq_zero (isOpen_nbhd ε) (Φ.differentiableOn_comp w)
    (fun _ hs => Φ.im_comp_ofReal w hs) ht

theorem hasDerivAt_re_comp (w : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    HasDerivAt (fun t : ℝ => (Φ.comp w t).re) (deriv (Φ.comp w) x).re x :=
  hasDerivAt_re_ofReal (Φ.differentiableAt_comp w (subset_closure (ofReal_mem_nbhd Φ.ε_pos hx)))

/-- The real restriction of a composition is injective on `I`. -/
theorem injOn_re_comp (w : List (Fin N)) :
    InjOn (fun t : ℝ => (Φ.comp w t).re) I := by
  have key {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) (hab : a < b) :
      (Φ.comp w a).re ≠ (Φ.comp w b).re := fun heq => by
    have hsub : Icc a b ⊆ I := Icc_subset_Icc ha.1 hb.2
    obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero hab
      (fun t ht => (Φ.hasDerivAt_re_comp w (hsub ht)).continuousAt.continuousWithinAt) heq
      (fun t ht => Φ.hasDerivAt_re_comp w (hsub (Ioo_subset_Icc_self ht)))
    have hcI := hsub (Ioo_subset_Icc_self hc)
    exact Φ.deriv_comp_ne_zero w (subset_closure (ofReal_mem_nbhd Φ.ε_pos hcI))
      (Complex.ext hc0 (Φ.im_deriv_comp_ofReal w (ofReal_mem_nbhd Φ.ε_pos hcI)))
  intro a ha b hb hab
  rcases lt_trichotomy a b with h | h | h
  · exact absurd hab (key ha hb h)
  · exact h
  · exact absurd hab.symm (key hb ha h)

/-- The image `f_w(I)` is an interval of length between `c_min^{|w|}` and `c_max^{|w|}`. -/
theorem exists_image_comp_eq_Icc (w : List (Fin N)) :
    ∃ p q : ℝ, 0 ≤ p ∧ q ≤ 1 ∧ Φ.cmin ^ w.length ≤ q - p ∧ q - p ≤ Φ.cmax ^ w.length ∧
      ∀ y ∈ Icc p q, ∃ x ∈ I, (y : ℂ) = Φ.comp w x := by
  set h : ℝ → ℝ := fun x => (Φ.comp w x).re
  have hcont : ContinuousOn h I :=
    fun x hx => (Φ.hasDerivAt_re_comp w hx).continuousAt.continuousWithinAt
  have h0 := Φ.re_comp_mem_I w (left_mem_Icc.2 zero_le_one)
  have h1 := Φ.re_comp_mem_I w (right_mem_Icc.2 zero_le_one)
  refine ⟨min (h 0) (h 1), max (h 0) (h 1), le_min h0.1 h1.1, max_le h0.2 h1.2, ?_,
    (max_sub_min_eq_abs _ _).trans_le
      (Φ.abs_re_comp_sub_le w (y := 1) (z := 0) (right_mem_Icc.2 zero_le_one)
        (left_mem_Icc.2 zero_le_one)),
    fun y hy => ?_⟩
  · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope h (fun x => (deriv (Φ.comp w) x).re)
      zero_lt_one hcont fun x hx => Φ.hasDerivAt_re_comp w (Ioo_subset_Icc_self hx)
    have hcI : c ∈ I := Ioo_subset_Icc_self hc
    have hlow := Φ.cmin_pow_le_norm_deriv_comp w (subset_closure (ofReal_mem_nbhd Φ.ε_pos hcI))
    rw [← Complex.abs_re_eq_norm.2 (Φ.im_deriv_comp_ofReal w (ofReal_mem_nbhd Φ.ε_pos hcI)),
      hslope] at hlow
    simpa [max_sub_min_eq_abs, abs_sub_comm] using hlow
  · obtain ⟨x, hx, rfl⟩ := intermediate_value_uIcc (a := 0) (b := 1)
      (by rwa [uIcc_of_le zero_le_one]) hy
    rw [uIcc_of_le zero_le_one] at hx
    exact ⟨x, hx, (Φ.comp_ofReal w hx).symm⟩

end IFS

end AnalyticESC
