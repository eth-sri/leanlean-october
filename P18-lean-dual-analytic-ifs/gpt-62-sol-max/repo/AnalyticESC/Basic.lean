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

theorem sub_le_twice {a b : ℂ} {M : ℝ} (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) :
    ‖a - b‖ ≤ 2 * M := (norm_sub_le _ _).trans (by linarith)

/-! ## The neighbourhoods `B_δ` -/

/-- The image of `I` in `ℂ` is compact. -/
theorem isCompact_image_I : IsCompact (((↑) : ℝ → ℂ) '' I) :=
  isCompact_Icc.image Complex.continuous_ofReal

/-- The image of `I` in `ℂ` is convex. -/
theorem convex_image_I : Convex ℝ (((↑) : ℝ → ℂ) '' I) :=
  (convex_Icc (0 : ℝ) 1).linear_image Complex.ofRealCLM.toLinearMap

theorem nbhd_eq_thickening (δ : ℝ) : nbhd δ = thickening δ (((↑) : ℝ → ℂ) '' I) := by
  ext z
  simp [nbhd, mem_thickening_iff, dist_eq_norm]

theorem isOpen_nbhd (δ : ℝ) : IsOpen (nbhd δ) := by simp [nbhd_eq_thickening, isOpen_thickening]

theorem convex_nbhd (δ : ℝ) : Convex ℝ (nbhd δ) := by rw [nbhd_eq_thickening]; exact convex_image_I.thickening δ

theorem isPreconnected_nbhd (δ : ℝ) : IsPreconnected (nbhd δ) := (convex_nbhd δ).isPreconnected

theorem isCompact_closure_nbhd (δ : ℝ) : IsCompact (closedNbhd δ) := by
  rw [closedNbhd, nbhd_eq_thickening]
  exact isCompact_image_I.isBounded.thickening.isCompact_closure

theorem ofReal_mem_nbhd {δ : ℝ} (hδ : 0 < δ) {x : ℝ} (hx : x ∈ I) : (x : ℂ) ∈ nbhd δ :=
  ⟨x, hx, by simpa⟩

theorem ofReal_mem_closure {δ : ℝ} (hδ : 0 < δ) {x : ℝ} (hx : x ∈ I) :
    (x : ℂ) ∈ closedNbhd δ := subset_closure (ofReal_mem_nbhd hδ hx)

theorem ofReal_mem_nbhd_two {δ : ℝ} (hδ : 0 < δ) {x : ℝ} (hx : x ∈ I) :
    (x : ℂ) ∈ nbhd (2 * δ) := ofReal_mem_nbhd (by positivity) hx

theorem nbhd_mem_nhds {δ : ℝ} {z : ℂ} (hz : z ∈ nbhd δ) : nbhd δ ∈ 𝓝 z :=
  (isOpen_nbhd δ).mem_nhds hz

theorem _root_.DifferentiableOn.analyticAt_nbhd {δ : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableOn ℂ f (nbhd δ)) (hz : z ∈ nbhd δ) : AnalyticAt ℂ f z :=
  hf.analyticOnNhd (isOpen_nbhd δ) z hz

theorem ball_subset_nbhd {δ x : ℝ} (hx : x ∈ I) : ball (x : ℂ) δ ⊆ nbhd δ :=
  fun _ hz => ⟨x, hx, mem_ball_iff_norm.1 hz⟩

theorem nbhd_mono {δ δ' : ℝ} (h : δ ≤ δ') : nbhd δ ⊆ nbhd δ' :=
  fun _ ⟨x, hx, hz⟩ => ⟨x, hx, hz.trans_le h⟩

theorem zero_mem_closure_nbhd {δ : ℝ} (hδ : 0 < δ) : (0 : ℂ) ∈ closedNbhd δ := by
  simpa using ofReal_mem_closure hδ (x := 0) (left_mem_Icc.2 zero_le_one)

theorem closure_nbhd_subset_two {δ : ℝ} (hδ : 0 < δ) : closedNbhd δ ⊆ nbhd (2 * δ) := by
  simp only [closedNbhd, nbhd_eq_thickening]
  simp_all [cthickening_subset_thickening']

theorem nbhd_subset_two {δ : ℝ} (hδ : 0 < δ) : nbhd δ ⊆ nbhd (2 * δ) :=
  subset_closure.trans (closure_nbhd_subset_two hδ)

/-! ## Real restrictions -/

/-- The derivative of the real restriction of a complex differentiable map. -/
theorem hasDerivAt_re_ofReal {g : ℂ → ℂ} {x : ℝ} (hg : DifferentiableAt ℂ g x) :
    HasDerivAt (fun t : ℝ => (g t).re) (deriv g x).re x := hg.hasDerivAt.real_of_complex

theorem real_mem_nhds {U : Set ℂ} (hU : IsOpen U) {x : ℝ} (hx : (x : ℂ) ∈ U) :
    {t : ℝ | (t : ℂ) ∈ U} ∈ 𝓝 x := (hU.preimage Complex.continuous_ofReal).mem_nhds hx

/-- A holomorphic map that is real at the real points of an open set has real derivative
there. -/
theorem im_deriv_eq_zero {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (hreal : ∀ t : ℝ, (t : ℂ) ∈ U → (g t).im = 0) {x : ℝ} (hx : (x : ℂ) ∈ U) :
    (deriv g x).im = 0 := by
  exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (((hg.differentiableAt (hU.mem_nhds hx)).hasDerivAt).comp_ofReal)).unique
    ((hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
      (eventuallyEq_of_mem (real_mem_nhds hU hx) (by assumption)))

theorem _root_.DifferentiableOn.iteratedDeriv_complex {U : Set ℂ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (j : ℕ) : DifferentiableOn ℂ (iteratedDeriv j f) U := by
  induction j with
  | zero => assumption
  | succ j ih => simpa only [iteratedDeriv_succ] using ih.deriv hU

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

include Φ in
theorem real_mem_open {x : ℝ} (hx : x ∈ I) : (x : ℂ) ∈ nbhd ε :=
  ofReal_mem_nbhd Φ.ε_pos hx

include Φ in
theorem real_mem_closed {x : ℝ} (hx : x ∈ I) : (x : ℂ) ∈ closedNbhd ε :=
  subset_closure (Φ.real_mem_open hx)

/-! ## Single maps -/

theorem differentiableOn_f (i : Fin N) : DifferentiableOn ℂ (Φ.f i) (nbhd (2 * ε)) :=
  (Φ.inClass i).differentiableOn

theorem analyticAt_f (i : Fin N) {z : ℂ} (hz : z ∈ closedNbhd ε) : AnalyticAt ℂ (Φ.f i) z :=
  (Φ.differentiableOn_f i).analyticAt_nbhd (closure_nbhd_subset_two Φ.ε_pos hz)

theorem im_f_ofReal (i : Fin N) {t : ℝ} (ht : (t : ℂ) ∈ nbhd (2 * ε)) : (Φ.f i t).im = 0 :=
  (Φ.inClass i).im_eq_zero t ht

private theorem isCompact_norm_range {F : Fin N → ℂ → ℂ}
    (hF : ∀ i, ContinuousOn (F i) (closedNbhd ε)) :
    IsCompact (range fun p : Fin N × closedNbhd ε => ‖F p.1 p.2‖) := by
  have := isCompact_iff_compactSpace.1 (isCompact_closure_nbhd ε)
  exact isCompact_range (continuous_prod_of_discrete_left.2 fun i =>
    ((hF i).comp_continuous continuous_subtype_val Subtype.coe_prop).norm)

private noncomputable abbrev derivNorm (p : Fin N × closedNbhd ε) := ‖deriv (Φ.f p.1) p.2‖

private theorem isCompact_derivNorm : IsCompact (range Φ.derivNorm) :=
  isCompact_norm_range fun i _ hz => (Φ.analyticAt_f i hz).deriv.continuousAt.continuousWithinAt

private theorem cmax_eq : Φ.cmax = ⨆ p, Φ.derivNorm p := (ciSup_prod Φ.isCompact_derivNorm.bddAbove).symm

private theorem derivNorm_nonempty (hN : 0 < N) : (range Φ.derivNorm).Nonempty :=
  ⟨_, mem_range_self (⟨0, hN⟩, ⟨0, zero_mem_closure_nbhd Φ.ε_pos⟩)⟩

theorem cmax_nonneg : 0 ≤ Φ.cmax := Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _

theorem cmin_nonneg : 0 ≤ Φ.cmin := Real.iInf_nonneg fun _ => norm_nonneg _

theorem cmax_lt_one : Φ.cmax < 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [Challenge.cmax]
  rw [Φ.cmax_eq, iSup]
  obtain ⟨⟨i, z⟩, he⟩ := Φ.isCompact_derivNorm.sSup_mem (Φ.derivNorm_nonempty hN)
  rw [← he]
  exact (Φ.inClass i).norm_deriv_lt_one _ z.2

theorem norm_deriv_le_cmax (i : Fin N) {z : ℂ} (hz : z ∈ closedNbhd ε) :
    ‖deriv (Φ.f i) z‖ ≤ Φ.cmax :=
  Φ.cmax_eq ▸ le_ciSup Φ.isCompact_derivNorm.bddAbove (i, ⟨z, hz⟩)

theorem cmin_pos (hN : 0 < N) : 0 < Φ.cmin := by
  rw [cmin, iInf]
  obtain ⟨⟨i, z⟩, he⟩ := Φ.isCompact_derivNorm.sInf_mem (Φ.derivNorm_nonempty hN)
  rw [← he]
  exact norm_pos_iff.2 ((Φ.inClass i).deriv_ne_zero _ z.2)

theorem cmin_le_norm_deriv (i : Fin N) {z : ℂ} (hz : z ∈ closedNbhd ε) :
    Φ.cmin ≤ ‖deriv (Φ.f i) z‖ :=
  ciInf_le Φ.isCompact_derivNorm.bddBelow (i, ⟨z, hz⟩)

theorem cmin_le_cmax (hN : 0 < N) : Φ.cmin ≤ Φ.cmax :=
  (Φ.cmin_le_norm_deriv ⟨0, hN⟩ (zero_mem_closure_nbhd Φ.ε_pos)).trans
    (Φ.norm_deriv_le_cmax ⟨0, hN⟩ (zero_mem_closure_nbhd Φ.ε_pos))

theorem cmin_lt_one (hN : 0 < N) : Φ.cmin < 1 := (Φ.cmin_le_cmax hN).trans_lt Φ.cmax_lt_one

theorem cmax_pos (hN : 0 < N) : 0 < Φ.cmax := (Φ.cmin_pos hN).trans_le (Φ.cmin_le_cmax hN)

theorem analyticAt_nonlin (i : Fin N) {z : ℂ} (hz : z ∈ closedNbhd ε) :
    AnalyticAt ℂ (Φ.nonlin i) z :=
  let h := (Φ.analyticAt_f i hz).deriv
  h.deriv.div h ((Φ.inClass i).deriv_ne_zero _ hz)

theorem exists_nonlin_bound :
    ∃ M, 0 ≤ M ∧ ∀ i, ∀ z ∈ closedNbhd ε, ‖Φ.nonlin i z‖ ≤ M := by
  obtain ⟨M, h₀, hM⟩ := (isCompact_norm_range (F := Φ.nonlin) fun i _ hz =>
    (Φ.analyticAt_nonlin i hz).continuousAt.continuousWithinAt).isBounded.exists_pos_norm_le
  exact ⟨M, h₀.le, fun i z hz => (le_abs_self _).trans (hM _ ⟨(i, ⟨z, hz⟩), rfl⟩)⟩

/-! ## Compositions along finite words -/

@[simp] theorem comp_nil : Φ.comp [] = id := rfl

@[simp] theorem comp_cons (i : Fin N) (w : List (Fin N)) : Φ.comp (i :: w) = Φ.f i ∘ Φ.comp w :=
  rfl

theorem comp_append (u v : List (Fin N)) : Φ.comp (u ++ v) = Φ.comp u ∘ Φ.comp v := by
  induction u with
  | nil => rfl
  | cons i u ih => aesop

theorem mapsTo_comp_closure (w : List (Fin N)) :
    MapsTo (Φ.comp w) (closedNbhd ε) (closedNbhd ε) := by
  induction w with
  | nil => tauto
  | cons i w ih =>
    rw [comp_cons]
    exact fun _ hz => subset_closure ((Φ.inClass i).mapsTo _ (ih hz))

/-- Finite compositions are analytic on an open neighbourhood of the closed stadium. -/
theorem analyticAt_comp (w : List (Fin N)) {z : ℂ} (hz : z ∈ closedNbhd ε) :
    AnalyticAt ℂ (Φ.comp w) z := by
  induction w with
  | nil => exact analyticAt_id
  | cons i w ih => exact (Φ.analyticAt_f i (Φ.mapsTo_comp_closure w hz)).comp ih

theorem differentiableAt_comp (w : List (Fin N)) {z : ℂ} (hz : z ∈ closedNbhd ε) :
    DifferentiableAt ℂ (Φ.comp w) z := (Φ.analyticAt_comp w hz).differentiableAt

theorem differentiableOn_comp (w : List (Fin N)) : DifferentiableOn ℂ (Φ.comp w) (nbhd ε) :=
  fun _ hz => (Φ.differentiableAt_comp w (subset_closure hz)).differentiableWithinAt

theorem deriv_comp_append (u v : List (Fin N)) {z : ℂ} (hz : z ∈ closedNbhd ε) :
    deriv (Φ.comp (u ++ v)) z = deriv (Φ.comp u) (Φ.comp v z) * deriv (Φ.comp v) z := by
  rw [comp_append]
  exact deriv_comp z (Φ.differentiableAt_comp u (Φ.mapsTo_comp_closure v hz))
    (Φ.differentiableAt_comp v hz)

theorem deriv_comp_cons (i : Fin N) (w : List (Fin N)) {z : ℂ} (hz : z ∈ closedNbhd ε) :
    deriv (Φ.comp (i :: w)) z = deriv (Φ.f i) (Φ.comp w z) * deriv (Φ.comp w) z :=
  Φ.deriv_comp_append [i] w hz

theorem norm_deriv_comp_bounds (w : List (Fin N)) {z : ℂ} (hz : z ∈ closedNbhd ε) :
    Φ.cmin ^ w.length ≤ ‖deriv (Φ.comp w) z‖ ∧ ‖deriv (Φ.comp w) z‖ ≤ Φ.cmax ^ w.length := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [Φ.deriv_comp_cons i w hz, norm_mul, List.length_cons, pow_succ', pow_succ']
    have hy := Φ.mapsTo_comp_closure w hz
    have hl := Φ.cmin_le_norm_deriv i hy
    have hu := Φ.norm_deriv_le_cmax i hy
    have := Φ.cmin_nonneg
    have := Φ.cmax_nonneg
    exact ⟨by bound, by bound⟩

theorem deriv_comp_ne_zero (w : List (Fin N)) {z : ℂ} (hz : z ∈ closedNbhd ε) :
    deriv (Φ.comp w) z ≠ 0 := by
  cases w with
  | nil => simp
  | cons i w => exact norm_pos_iff.1 ((pow_pos (Φ.cmin_pos i.pos) _).trans_le
      (Φ.norm_deriv_comp_bounds _ hz).1)

/-- A uniform bound for all compositions on `cl B_ε`. -/
theorem exists_comp_bound : ∃ R, 0 ≤ R ∧ ∀ w, ∀ z ∈ closedNbhd ε, ‖Φ.comp w z‖ ≤ R := by
  obtain ⟨R, h₀, hR⟩ := (isCompact_closure_nbhd ε).isBounded.exists_pos_norm_le
  exact ⟨R, h₀.le, fun w z hz => hR _ (Φ.mapsTo_comp_closure w hz)⟩

theorem norm_comp_sub_le (w : List (Fin N)) {z z' : ℂ} (hz : z ∈ closedNbhd ε) (hz' : z' ∈ closedNbhd ε) :
    ‖Φ.comp w z - Φ.comp w z'‖ ≤ Φ.cmax ^ w.length * ‖z - z'‖ :=
  (convex_nbhd ε).closure.norm_image_sub_le_of_norm_deriv_le
    (fun _ => Φ.differentiableAt_comp w) (fun _ hx => (Φ.norm_deriv_comp_bounds w hx).2) hz' hz

@[simp] theorem reComp_nil (x : ℝ) : Φ.reComp [] x = x := Complex.ofReal_re x

@[simp] theorem reComp_singleton (i : Fin N) (x : ℝ) : Φ.reComp [i] x = Φ.realMaps i x := rfl

theorem comp_eq_realComp (w : List (Fin N)) {x : ℝ} (hx : (x : ℂ) ∈ closedNbhd ε) :
    Φ.comp w x = (Challenge.realComp Φ.realMaps w x : ℂ) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    have hz := closure_nbhd_subset_two Φ.ε_pos (Φ.mapsTo_comp_closure w hx)
    rw [ih] at hz
    rw [comp_cons, Function.comp_apply, ih]
    exact Complex.ext rfl (Φ.im_f_ofReal i hz)

theorem im_comp_ofReal (w : List (Fin N)) {x : ℝ} (hx : (x : ℂ) ∈ closedNbhd ε) : (Φ.comp w x).im = 0 :=
  congrArg Complex.im (Φ.comp_eq_realComp w hx)

theorem comp_ofReal (w : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    Φ.comp w x = (Φ.reComp w x : ℂ) := Complex.ext rfl (Φ.im_comp_ofReal w (Φ.real_mem_closed hx))

theorem reComp_append (u v : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    Φ.reComp (u ++ v) x = Φ.reComp u (Φ.reComp v x) := by
  simp only [reComp, comp_append, Function.comp_apply]
  rw [← Φ.comp_ofReal v hx]

theorem re_comp_mem_I (w : List (Fin N)) {x : ℝ} (hx : x ∈ I) : Φ.reComp w x ∈ I := by
  induction w with
  | nil => simpa
  | cons i w ih =>
    rw [show i :: w = [i] ++ w from rfl, Φ.reComp_append _ _ hx]
    exact (Φ.inClass i).re_mem_I _ ih

theorem deriv_comp_real (w : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    deriv (Φ.comp w) x = ((deriv (Φ.comp w) x).re : ℂ) :=
  Complex.ext rfl (im_deriv_eq_zero (isOpen_nbhd ε) (Φ.differentiableOn_comp w)
    (fun _ h => Φ.im_comp_ofReal w (subset_closure h)) (Φ.real_mem_open hx))

theorem abs_re_deriv_comp (w : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    |(deriv (Φ.comp w) x).re| = ‖deriv (Φ.comp w) x‖ :=
  Complex.abs_re_eq_norm.2 (congrArg Complex.im (Φ.deriv_comp_real w hx))

theorem hasDerivAt_re_comp (w : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    HasDerivAt (Φ.reComp w) (deriv (Φ.comp w) x).re x :=
  hasDerivAt_re_ofReal (Φ.differentiableAt_comp w (Φ.real_mem_closed hx))

/-- The image of `I` contains an interval of length at least `c_min^{|w|}`. -/
theorem exists_Icc_subset_image_comp (w : List (Fin N)) :
    ∃ p q : ℝ, 0 ≤ p ∧ p ≤ q ∧ q ≤ 1 ∧ Φ.cmin ^ w.length ≤ q - p ∧
      Icc p q ⊆ Φ.reComp w '' I := by
  let h := Φ.reComp w
  have hcont : ContinuousOn h I :=
    fun _ hx => (Φ.hasDerivAt_re_comp w hx).continuousAt.continuousWithinAt
  have h0 := Φ.re_comp_mem_I w (by simp : (0 : ℝ) ∈ I)
  have h1 := Φ.re_comp_mem_I w (by simp : (1 : ℝ) ∈ I)
  refine ⟨min (h 0) (h 1), max (h 0) (h 1), by grind, min_le_max, by grind, ?_, ?_⟩
  · obtain ⟨z, hz, hd⟩ := exists_hasDerivAt_eq_slope h _ zero_lt_one hcont
      (fun z hz => Φ.hasDerivAt_re_comp w (Ioo_subset_Icc_self hz))
    have hz' := Ioo_subset_Icc_self hz
    have hl := (Φ.norm_deriv_comp_bounds w (Φ.real_mem_closed hz')).1
    rw [← Φ.abs_re_deriv_comp w hz', hd] at hl
    rw [max_sub_min_eq_abs]
    simpa [abs_sub_comm] using hl
  · simpa [uIcc] using
      intermediate_value_uIcc (a := (0 : ℝ)) (b := 1) (by simpa only [uIcc_of_le zero_le_one] using hcont)

end IFS

end AnalyticESC
