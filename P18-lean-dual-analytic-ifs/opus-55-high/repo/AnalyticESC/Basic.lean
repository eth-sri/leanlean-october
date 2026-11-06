module

public import AnalyticESC.Defs

public section

set_option hygiene false
local notation "𝔟" => ofReal_mem_nbhd Φ.ε_pos
local notation "𝔞" => hcont.image_Icc zero_le_one
local notation "𝕬" => Φ.continuousOn_norm_deriv_f i
local notation "𝖟" => hU.mem_nhds hx
local notation "𝖞" => Ioo_subset_Icc_self hc
local notation "𝖝" => Φ.f i
local notation "𝖜" => nbhd δ
local notation "𝔲" => h '' I

local notation "𝔨" => Φ.comp w

local notation "𝔧" => 𝔹 ε

local notation "𝔤" => nbhd ε

local notation "𝔣" => Φ.mapsTo_comp_closure w hz

/-!
# Basic properties

The neighbourhoods `B_δ`, consequences of the conditions (A)–(C) defining the class, the
constants `c_min` and `c_max`, compositions along finite words, and the passage between complex
derivatives and derivatives of real restrictions.
-/

namespace AnalyticESC

variable {U : Set ℂ} {g : ℂ → ℂ} {t x y δ δ' : ℝ} {z : ℂ}

open Set Metric Topology

/-! ## The neighbourhoods `B_δ` -/

/-- The image of `I` in `ℂ` is compact. -/
theorem isCompact_image_I : IsCompact Iℂ :=
  isCompact_Icc.image Complex.continuous_ofReal

/-- The image of `I` in `ℂ` is convex. -/
theorem convex_image_I : Convex ℝ Iℂ :=
  (convex_Icc 0 1).linear_image Complex.ofRealCLM.toLinearMap

theorem isOpen_nbhd : IsOpen 𝖜 := isOpen_thickening

theorem convex_nbhd δ : Convex ℝ 𝖜 := convex_image_I.thickening δ

theorem isPreconnected_nbhd δ : IsPreconnected 𝖜 := (convex_nbhd δ).isPreconnected

theorem isBounded_nbhd δ : Bornology.IsBounded 𝖜 :=
  isCompact_image_I.isBounded.thickening

theorem isCompact_closure_nbhd δ : IsCompact (𝔹 δ) :=
  (isBounded_nbhd δ).isCompact_closure

theorem ofReal_mem_nbhd (hδ : 0 < δ) (hx : x ∈ I) : (x : ℂ) ∈ nbhd δ :=
  self_subset_thickening hδ _ (mem_image_of_mem _ hx)

theorem image_I_subset_nbhd (hδ : 0 < δ) : Iℂ ⊆ nbhd δ := self_subset_thickening hδ _

theorem ofReal_mem_closure (hδ : 0 < δ) (hx : x ∈ I) :
    (x : ℂ) ∈ 𝔹 δ :=
  subset_closure (ofReal_mem_nbhd hδ hx)

theorem ball_subset_nbhd (hx : x ∈ I) : ball (x : ℂ) δ ⊆ nbhd δ :=
  ball_subset_thickening (mem_image_of_mem _ hx) δ

theorem nbhd_mono (h : δ ≤ δ') : nbhd δ ⊆ nbhd δ' := thickening_mono h _

theorem nbhd_of_nonpos (h : δ ≤ 0) : nbhd δ = ∅ := thickening_of_nonpos h _

theorem zero_mem_closure_nbhd (hδ : 0 < δ) : 0 ∈ 𝔹 δ := by
  simpa using subset_closure (ofReal_mem_nbhd hδ zero_mem_I)

theorem closure_nbhd_subset (h : δ < δ') : 𝔹 δ ⊆ nbhd δ' := by
  rcases le_or_gt δ' 0 with h' | h'
  · simp [nbhd_of_nonpos (h.le.trans h')]
  · exact (closure_thickening_subset_cthickening δ _).trans (cthickening_subset_thickening' h' h _)

/-! ## Real restrictions -/

/-- The derivative of the real restriction of a complex differentiable map. -/
theorem hasDerivAt_re_ofReal (hg : DifferentiableAt ℂ g x) :
    HasDerivAt (fun t : ℝ => (g t).re) (deriv g x).re x := hg.hasDerivAt.real_of_complex

section
variable (hU : IsOpen U)
include hU

/-- The real points of an open subset of `ℂ` form an open subset of `ℝ`. -/
theorem isOpen_setOf_ofReal_mem : IsOpen {t : ℝ | (t : ℂ) ∈ U} :=
  hU.preimage Complex.continuous_ofReal

variable (hg : DifferentiableOn ℂ g U)
include hg

/-- Iterated derivatives of the real restriction of a holomorphic map. -/
theorem iteratedDeriv_re_ofReal k (hx : (x : ℂ) ∈ U) :
    iteratedDeriv k (fun t : ℝ => (g t).re) x = (iteratedDeriv k g x).re := by
  have hdiff : ∀ k, DifferentiableOn ℂ (iteratedDeriv k g) U := by
    intro k
    rw [iteratedDeriv_eq_iterate]
    exact ((hg.analyticOnNhd hU).iterated_deriv k).differentiableOn
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have heq : iteratedDeriv k (fun t : ℝ => (g t).re) =ᶠ[𝓝 x]
        fun t => (iteratedDeriv k g t).re := by
      filter_upwards [(isOpen_setOf_ofReal_mem hU).mem_nhds hx] with t ht using ih ht
    rw [iteratedDeriv_succ, heq.deriv_eq, iteratedDeriv_succ]
    exact (hasDerivAt_re_ofReal ((hdiff k).differentiableAt 𝖟)).deriv

/-- The real restriction of a holomorphic map is smooth on the real points of its domain. -/
theorem contDiffOn_re_ofReal n :
    ContDiffOn ℝ n (fun t : ℝ => (g t).re) {t : ℝ | (t : ℂ) ∈ U} := by
  intro x hx
  exact ((hg.contDiffOn hU).contDiffAt 𝖟).real_of_complex.contDiffWithinAt

/-- A holomorphic map that is real at the real points of an open set has real derivative
there. -/
theorem im_deriv_eq_zero (hreal : ∀ t : ℝ, (t : ℂ) ∈ U → (g t).im = 0) (hx : (x : ℂ) ∈ U) :
    (deriv g x).im = 0 :=
  (Complex.imCLM.hasFDerivAt.comp_hasDerivAt x
    (hg.differentiableAt 𝖟).hasDerivAt.comp_ofReal).unique
    ((hasDerivAt_const x 0).congr_of_eventuallyEq (by
      filter_upwards [(isOpen_setOf_ofReal_mem hU).mem_nhds hx] with t ht using hreal t ht))

end

/-- A map of `S^ω_ε(I)` has at most one fixed point in `I`. -/
theorem eq_of_re_eq_self (hε : 0 < ε) (hh : InClass ε h)
    (hx : x ∈ I) (hy : y ∈ I) (hhx : (h x).re = x) (hhy : (h y).re = y) : x = y := by
  have hd : Ɐ HasDerivAt (fun x : ℝ => (h x).re - x) ((deriv h x).re - 1) x := fun x hx =>
    (hasDerivAt_re_ofReal (hh.differentiableOn.differentiableAt
      (isOpen_nbhd.mem_nhds (ofReal_mem_nbhd (by linarith) hx)))).sub (hasDerivAt_id x)
  refine (strictAntiOn_of_deriv_neg (convex_Icc 0 1)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt) fun x hx => ?_).injOn hx hy
    (by linarith)
  rw [(hd x (interior_subset hx)).deriv, sub_neg]
  exact (Complex.re_le_norm _).trans_lt
    (hh.norm_deriv_lt_one x (ofReal_mem_closure hε (interior_subset hx)))

namespace IFS

variable (Φ : IFS N ε) (i : Fin N) (u v w : 𝔚 N)

include Φ in
theorem ofReal_mem_cl (hx : x ∈ I) : (x : ℂ) ∈ 𝔹 ε :=
  ofReal_mem_closure Φ.ε_pos hx

/-! ## Single maps -/

theorem nbhd_subset_two : nbhd ε ⊆ 𝔑 ε := by
  rcases le_or_gt ε 0 with h | h
  · simp [nbhd_of_nonpos h]
  · exact nbhd_mono (by linarith)

include Φ in
theorem ofReal_mem_nbhd2 (hx : x ∈ I) : (x : ℂ) ∈ 𝔑 ε := nbhd_subset_two (ofReal_mem_nbhd Φ.ε_pos hx)

include Φ in
theorem image_I_subset_nbhd2 : Iℂ ⊆ 𝔑 ε := image_subset_iff.2 fun _ => Φ.ofReal_mem_nbhd2

theorem closure_nbhd_subset_two : 𝔹 ε ⊆ 𝔑 ε := by
  rcases le_or_gt ε 0 with h | h
  · simp [nbhd_of_nonpos h]
  · exact closure_nbhd_subset (by linarith)

theorem differentiableOn_f : DifferentiableOn ℂ 𝖝 (𝔑 ε) :=
  (Φ.inClass i).differentiableOn

theorem differentiableAt_f (hz : z ∈ 𝔹 ε) :
    DifferentiableAt ℂ 𝖝 z :=
  (Φ.differentiableOn_f i).differentiableAt (isOpen_nbhd.mem_nhds (closure_nbhd_subset_two hz))

theorem continuousOn_deriv_f : ContinuousOn (𝔡 Φ i) (𝔑 ε) :=
  ((Φ.differentiableOn_f i).deriv isOpen_nbhd).continuousOn

theorem mapsTo_f : MapsTo 𝖝 𝔤 𝔤 :=
  fun _ hz => (Φ.inClass i).mapsTo (subset_closure hz)

theorem im_f_ofReal (ht : (t : ℂ) ∈ 𝔑 ε) : (Φ.f i t).im = 0 :=
  (Φ.inClass i).im_eq_zero t ht

local notation "𝔫" => ‖𝔡 Φ i z‖

theorem continuousOn_norm_deriv_f :
    ContinuousOn (fun z => 𝔫) 𝔧 :=
  ((Φ.continuousOn_deriv_f i).mono closure_nbhd_subset_two).norm

theorem bddAbove_norm_deriv :
    BddAbove (range fun z : 𝔹 ε => 𝔫) := by
  rw [← image_eq_range (fun z => 𝔫)]
  exact (isCompact_closure_nbhd ε).bddAbove_image 𝕬

theorem bddBelow_norm_deriv :
    BddBelow (range fun z : 𝔹 ε => 𝔫) :=
  ⟨0, by rintro _ ⟨z, rfl⟩; exact norm_nonneg _⟩

theorem cmax_nonneg : 0 ≤ Φ.cmax :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _

theorem cmin_nonneg : 0 ≤ Φ.cmin :=
  Real.iInf_nonneg fun _ => Real.iInf_nonneg fun _ => norm_nonneg _

theorem cmax_lt_one : Φ.cmax < 1 := by
  rcases isEmpty_or_nonempty (Fin N) with hN | hN
  · simp [cmax]
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite
    (f := fun i : Fin N => ⨆ z : 𝔹 ε, 𝔫)
  obtain ⟨z, hz, hmax⟩ := (isCompact_closure_nbhd ε).exists_isMaxOn
    ⟨0, zero_mem_closure_nbhd Φ.ε_pos⟩ 𝕬
  have : Nonempty 𝔧 := by aesop
  rw [cmax, ← hi]
  exact (ciSup_le fun w => hmax w.2).trans_lt ((Φ.inClass i).norm_deriv_lt_one z hz)

theorem norm_deriv_le_cmax (hz : z ∈ 𝔹 ε) :
    𝔫  ≤ Φ.cmax :=
  calc 𝔫  ≤ ⨆ z : 𝔹 ε, 𝔫  :=
        le_ciSup (Φ.bddAbove_norm_deriv i) ⟨z, hz⟩
    _ ≤ Φ.cmax := le_ciSup (f := fun i => ⨆ z : 𝔹 ε, 𝔫)
        (finite_range _).bddAbove i

theorem cmin_pos (hN : 0 < N) : 0 < Φ.cmin := by
  have : Nonempty (Fin N) := by tauto
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite
    (f := fun i : Fin N => ⨅ z : 𝔹 ε, 𝔫)
  obtain ⟨z, hz, hmin⟩ := (isCompact_closure_nbhd ε).exists_isMinOn
    ⟨0, zero_mem_closure_nbhd Φ.ε_pos⟩ 𝕬
  have : Nonempty 𝔧 := by aesop
  rw [cmin, ← hi]
  exact (norm_pos_iff.2 ((Φ.inClass i).deriv_ne_zero z hz)).trans_le (le_ciInf fun w => hmin w.2)

theorem cmin_le_norm_deriv (hz : z ∈ 𝔹 ε) :
    Φ.cmin ≤ 𝔫  :=
  calc Φ.cmin ≤ ⨅ z : 𝔹 ε, 𝔫  :=
        ciInf_le
          (finite_range _).bddBelow i
    _ ≤ 𝔫  := ciInf_le (Φ.bddBelow_norm_deriv i) ⟨z, hz⟩

theorem cmin_le_cmax (hN : 0 < N) : Φ.cmin ≤ Φ.cmax :=
  (Φ.cmin_le_norm_deriv ⟨0, hN⟩ (zero_mem_closure_nbhd Φ.ε_pos)).trans
    (Φ.norm_deriv_le_cmax ⟨0, hN⟩ (zero_mem_closure_nbhd Φ.ε_pos))

theorem cmax_pos (hN : 0 < N) : 0 < Φ.cmax := (Φ.cmin_pos hN).trans_le (Φ.cmin_le_cmax hN)

/-- `f_i''/f_i'` is holomorphic on an open set containing `cl B_ε`. -/
theorem exists_differentiableOn_nonlin :
    ∃ U : Set ℂ, IsOpen U ∧ 𝔹 ε ⊆ U ∧ DifferentiableOn ℂ (Φ.nonlin i) U := by
  refine ⟨𝔑 ε ∩ 𝔡 Φ i ⁻¹' {0}ᶜ,
    (Φ.continuousOn_deriv_f i).isOpen_inter_preimage isOpen_nbhd isOpen_compl_singleton,
    fun z hz => ⟨closure_nbhd_subset_two hz, (Φ.inClass i).deriv_ne_zero z hz⟩, ?_⟩
  have h1 := (Φ.differentiableOn_f i).deriv isOpen_nbhd
  exact ((h1.deriv isOpen_nbhd).mono inter_subset_left).div (h1.mono inter_subset_left) fun z hz => hz.2

theorem exists_nonlin_bound :
    ∃ M, 0 ≤ M ∧ ∀ i, ∀ z ∈ 𝔹 ε, ‖Φ.nonlin i z‖ ≤ M := by
  choose C hC using fun i => let ⟨_, _, hU, hd⟩ := Φ.exists_differentiableOn_nonlin i
    (isCompact_closure_nbhd ε).exists_bound_of_continuousOn (hd.continuousOn.mono hU)
  exact ⟨max 0 (⨆ i, C i), le_max_left _ _, fun i z hz =>
    (hC i z hz).trans ((le_ciSup (Finite.bddAbove_range C) i).trans (le_max_right _ _))⟩

theorem im_deriv_f_ofReal (ht : (t : ℂ) ∈ 𝔑 ε) :
    (𝔡 Φ i t).im = 0 :=
  im_deriv_eq_zero isOpen_nbhd (Φ.differentiableOn_f i) (fun _ hs => Φ.im_f_ofReal i hs) ht

theorem im_nonlin_ofReal (ht : (t : ℂ) ∈ nbhd ε) :
    (Φ.nonlin i t).im = 0 := by
  have ht2 := nbhd_subset_two ht
  have hdd : (𝔇 𝖝 t).im = 0 :=
    im_deriv_eq_zero isOpen_nbhd ((Φ.differentiableOn_f i).deriv isOpen_nbhd) (fun _ hs => Φ.im_deriv_f_ofReal i hs) ht2
  simp [nonlin, Complex.div_im, Φ.im_deriv_f_ofReal i ht2, hdd]

/-! ## Compositions along finite words -/

@[simp] theorem comp_nil : Φ.comp [] = id := rfl

@[simp] theorem comp_cons w : Φ.comp (i :: w) = Φ.f i ∘ Φ.comp w :=
  rfl

theorem comp_append : Φ.comp (u ++ v) = Φ.comp u ∘ Φ.comp v := by
  induction u with
  | nil => rfl
  | cons i u ih => rw [List.cons_append, comp_cons, ih, comp_cons]; rfl

theorem mapsTo_comp : MapsTo 𝔨 𝔤 𝔤 := by
  induction w with
  | nil => exact mapsTo_id _
  | cons i w ih => rw [comp_cons]; exact (Φ.mapsTo_f i).comp ih

theorem mapsTo_comp_closure :
    MapsTo 𝔨 𝔧 𝔧 := by
  induction w with
  | nil => exact mapsTo_id _
  | cons i w ih =>
    exact ((Φ.inClass i).mapsTo.mono_right subset_closure).comp ih

section
variable (hz : z ∈ 𝔹 ε)
include hz

theorem differentiableAt_comp :
    DifferentiableAt ℂ 𝔨 z := by
  induction w with
  | nil => exact differentiableAt_id
  | cons i w ih =>
    exact (Φ.differentiableAt_f i 𝔣).comp z ih

theorem deriv_comp_cons :
    𝔡ᶜ Φ (i :: w) z = 𝔡 Φ i (Φ.comp w z) * 𝔡ᶜ Φ w z := by
  exact deriv_comp z (Φ.differentiableAt_f i 𝔣)
    (Φ.differentiableAt_comp w hz)

theorem deriv_comp_append :
    𝔡ᶜ Φ (u ++ v) z = 𝔡ᶜ Φ u (Φ.comp v z) * 𝔡ᶜ Φ v z := by
  rw [comp_append]
  exact deriv_comp z (Φ.differentiableAt_comp u (Φ.mapsTo_comp_closure v hz))
    (Φ.differentiableAt_comp v hz)

theorem norm_deriv_comp_le :
    ‖𝔡ᶜ Φ w z‖ ≤ Φ.cmax ^ w.length := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [Φ.deriv_comp_cons i w hz, norm_mul, List.length_cons, pow_succ']
    exact mul_le_mul (Φ.norm_deriv_le_cmax i 𝔣) ih (norm_nonneg _)
      Φ.cmax_nonneg

theorem cmin_pow_le_norm_deriv_comp :
    Φ.cmin ^ w.length ≤ ‖𝔡ᶜ Φ w z‖ := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [Φ.deriv_comp_cons i w hz, norm_mul, List.length_cons, pow_succ']
    exact mul_le_mul (Φ.cmin_le_norm_deriv i 𝔣) ih
      (pow_nonneg Φ.cmin_nonneg _) (norm_nonneg _)

theorem deriv_comp_ne_zero :
    𝔡ᶜ Φ w z ≠ 0 := by
  induction w with
  | nil => simp
  | cons i w ih =>
    exact Φ.deriv_comp_cons i w hz ▸ mul_ne_zero ((Φ.inClass i).deriv_ne_zero _ 𝔣) ih

end

theorem differentiableOn_comp : DifferentiableOn ℂ 𝔨 𝔤 :=
  fun _ hz => (Φ.differentiableAt_comp w (subset_closure hz)).differentiableWithinAt

/-- `f_w` is holomorphic on an open set containing `cl B_ε`. -/
theorem exists_differentiableOn_comp :
    ∃ U, IsOpen U ∧ 𝔹 ε ⊆ U ∧ DifferentiableOn ℂ 𝔨 U := by
  induction w with
  | nil => exact ⟨univ, isOpen_univ, subset_univ _, differentiableOn_id⟩
  | cons i w ih =>
    obtain ⟨U, hU, hcl, hd⟩ := ih
    refine ⟨U ∩ Φ.comp w ⁻¹' 𝔑 ε,
      hd.continuousOn.isOpen_inter_preimage hU isOpen_nbhd,
      fun z hz => ⟨hcl hz, closure_nbhd_subset_two 𝔣⟩, ?_⟩
    exact (Φ.differentiableOn_f i).comp (hd.mono inter_subset_left) fun z hz => hz.2

/-- A uniform bound for all compositions on `cl B_ε`. -/
theorem exists_comp_bound : ∃ R, 0 ≤ R ∧ ∀ w, ∀ z ∈ 𝔹 ε, ‖Φ.comp w z‖ ≤ R := by
  obtain ⟨R, hR⟩ := (isCompact_closure_nbhd ε).isBounded.exists_norm_le
  exact ⟨max R 0, le_max_right _ _,
    fun w z hz => (hR _ 𝔣).trans (le_max_left _ _)⟩

theorem norm_comp_sub_le (hz : z ∈ nbhd ε) (hz' : z' ∈ nbhd ε) :
    ‖Φ.comp w z - Φ.comp w z'‖ ≤ Φ.cmax ^ w.length * ‖z - z'‖ :=
  (convex_nbhd ε).norm_image_sub_le_of_norm_deriv_le
    (fun _ hx => Φ.differentiableAt_comp w (subset_closure hx))
    (fun _ hx => Φ.norm_deriv_comp_le w (subset_closure hx)) hz' hz

theorem im_comp_ofReal (ht : (t : ℂ) ∈ nbhd ε) :
    (Φ.comp w t).im = 0 := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [comp_cons, Function.comp_apply]
    have h1 : Φ.comp w t = ((Φ.comp w t).re : ℂ) := Complex.ext (by simp) (by omega)
    exact h1 ▸ Φ.im_f_ofReal i (by rw [← h1]; exact nbhd_subset_two (Φ.mapsTo_comp w ht))

section
variable (hx : x ∈ I)
include hx

theorem comp_ofReal :
    Φ.comp w x = ((Φ.comp w x).re : ℂ) :=
  Complex.ext (by simp) (by simp [Φ.im_comp_ofReal w (ofReal_mem_nbhd Φ.ε_pos hx)])

theorem re_comp_mem_I : (Φ.comp w x).re ∈ I := by
  induction w with
  | nil => simpa using hx
  | cons i w ih =>
    rw [comp_cons, Function.comp_apply, Φ.comp_ofReal w hx]
    exact (Φ.inClass i).re_mem_I _ ih

theorem norm_comp_ofReal_le_one : ‖Φ.comp w x‖ ≤ 1 := by
  rw [Φ.comp_ofReal w hx, Complex.norm_real, Real.norm_of_nonneg (Φ.re_comp_mem_I w hx).1]
  exact (Φ.re_comp_mem_I w hx).2

end

theorem im_deriv_comp_ofReal (ht : (t : ℂ) ∈ nbhd ε) :
    (𝔡ᶜ Φ w t).im = 0 :=
  im_deriv_eq_zero isOpen_nbhd (Φ.differentiableOn_comp w)
    (fun _ hs => Φ.im_comp_ofReal w hs) ht

/-- The two points `f_v(y), f_v(y')` for `y, y' ∈ I` are at distance at most `c_max^{|v|}`. -/
theorem abs_re_comp_sub_le v (hy : y ∈ I) (hy' : y' ∈ I) :
    |(Φ.comp v y).re - (Φ.comp v y').re| ≤ Φ.cmax ^ v.length := by
  have h := Φ.norm_comp_sub_le v (ofReal_mem_nbhd Φ.ε_pos hy) (ofReal_mem_nbhd Φ.ε_pos hy')
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  exact (Complex.abs_re_le_norm _).trans (h.trans (mul_le_of_le_one_right
    (pow_nonneg Φ.cmax_nonneg _) (abs_le.2 ⟨by grind, by grind⟩)))

/-- The real restriction of a composition is injective on `I`. -/
theorem injOn_re_comp :
    InjOn (fun t : ℝ => (Φ.comp w t).re) I := by
  have hd : ∀ t ∈ I, HasDerivAt (fun t : ℝ => (Φ.comp w t).re) (𝔡ᶜ Φ w t).re t :=
    fun t ht => hasDerivAt_re_ofReal (Φ.differentiableAt_comp w ((fun t ht => Φ.ofReal_mem_cl ht) t ht))
  -- Rolle's theorem
  have key : ∀ a ∈ I, ∀ b ∈ I, a < b → (Φ.comp w a).re ≠ (Φ.comp w b).re := by
    intro a ha b hb hab heq
    have hsub : Icc a b ⊆ I := by grind
    obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero (f' := fun t => (𝔡ᶜ Φ w t).re)
      hab (fun t ht => (hd t (hsub ht)).continuousAt.continuousWithinAt) heq
      (fun t ht => hd t (hsub (Ioo_subset_Icc_self ht)))
    exact Φ.deriv_comp_ne_zero w ((fun t ht => Φ.ofReal_mem_cl ht) c (hsub 𝖞)) (Complex.ext hc0
      (Φ.im_deriv_comp_ofReal w (ofReal_mem_nbhd Φ.ε_pos (hsub 𝖞))))
  exact fun a ha b hb hab => le_antisymm (not_lt.1 fun h => key b hb a ha h hab.symm)
    (not_lt.1 fun h => key a ha b hb h hab)

/-- The image `f_w(I)` is an interval of length between `c_min^{|w|}` and `c_max^{|w|}`. -/
theorem exists_image_comp_eq_Icc :
    ∃ p q : ℝ, 0 ≤ p ∧ p ≤ q ∧ q ≤ 1 ∧ Φ.cmin ^ w.length ≤ q - p ∧
      q - p ≤ Φ.cmax ^ w.length ∧ (fun x : ℝ => (Φ.comp w x).re) '' I = Icc p q := by
  set h : ℝ → ℝ := fun x => (Φ.comp w x).re
  have hderiv : Ɐ HasDerivAt h (𝔡ᶜ Φ w x).re x := fun x hx =>
    hasDerivAt_re_ofReal (Φ.differentiableAt_comp w (subset_closure (𝔟 hx)))
  have hcont : ContinuousOn h I := fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  set p := sInf 𝔲
  set q := sSup 𝔲
  have h0 := 𝔞 ▸ mem_image_of_mem h zero_mem_I
  have h1 := 𝔞 ▸ mem_image_of_mem h one_mem_I
  obtain ⟨a, ha, hpa⟩ : p ∈ h '' I := 𝔞 ▸ left_mem_Icc.2 (h0.1.trans h0.2)
  obtain ⟨b, hb, hqb⟩ : q ∈ h '' I := 𝔞 ▸ right_mem_Icc.2 (h0.1.trans h0.2)
  refine ⟨p, q, hpa ▸ (Φ.re_comp_mem_I w ha).1, h0.1.trans h0.2, hqb ▸ (Φ.re_comp_mem_I w hb).2, ?_,
    hpa ▸ hqb ▸ (le_abs_self _).trans (Φ.abs_re_comp_sub_le w hb ha), hcont.image_Icc zero_le_one⟩
  -- lower bound via the mean value theorem on `[0,1]`
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope h (fun x => (𝔡ᶜ Φ w x).re)
    zero_lt_one hcont (fun x hx => hderiv x (Ioo_subset_Icc_self hx))
  have := Φ.cmin_pow_le_norm_deriv_comp w (subset_closure (𝔟 𝖞))
  rw [← Complex.abs_re_eq_norm.2 (Φ.im_deriv_comp_ofReal w (𝔟 𝖞)),
    hslope, sub_zero, div_one] at this
  exact this.trans (abs_sub_le_iff.2 ⟨by grind, by grind⟩)

end IFS

end AnalyticESC
