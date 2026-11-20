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

lemma nbhd_eq (δ : ℝ) : nbhd δ = thickening δ (((↑) : ℝ → ℂ) '' I) := by
  ext; simp [nbhd,mem_thickening_iff,dist_eq_norm]

theorem isOpen_nbhd (δ : ℝ) : IsOpen (nbhd δ) := nbhd_eq δ ▸ isOpen_thickening

theorem convex_nbhd (δ : ℝ) : Convex ℝ (nbhd δ) := nbhd_eq δ ▸ ((convex_Icc 0 1).linear_image Complex.ofRealCLM.toLinearMap).thickening δ

theorem ofReal_mem_nbhd {δ : ℝ} (hδ : 0 < δ) {x : ℝ} (hx : x ∈ I) : (x : ℂ) ∈ nbhd δ :=
  ⟨x,hx,by simpa using hδ⟩

lemma zero_I : (0:ℝ) ∈ I := (0:I).2

lemma cl_two {ε : ℝ} (he : 0 < ε) : closure (nbhd ε) ⊆ nbhd (2*ε) := by
  rw [nbhd_eq,nbhd_eq]; exact (closure_thickening_subset_cthickening ε _).trans (cthickening_subset_thickening' (by linarith) (by linarith) _)

lemma near_real {U : Set ℂ} (ho : IsOpen U) {x : ℝ} (hx : (x:ℂ) ∈ U) : ∀ᶠ t : ℝ in 𝓝 x, (t:ℂ) ∈ U :=
  (ho.preimage Complex.continuous_ofReal).mem_nhds hx

abbrev restr (g : ℂ → ℂ) (x : ℝ) := (g x).re

lemma real_jet {g : ℂ → ℂ} {U : Set ℂ} (ho : IsOpen U) (hg : AnalyticOnNhd ℂ g U)
    (hr : ∀ x : ℝ, (x:ℂ) ∈ U → (g x).im = 0) (k : ℕ) {x : ℝ} (hx : (x:ℂ) ∈ U) :
    ((deriv^[k] (restr g) x:ℝ):ℂ) = deriv^[k] g x := by
  have ha : AnalyticOnNhd ℝ (restr g) (Complex.ofReal ⁻¹' U) := fun t ht => (hg _ ht).re_ofReal
  induction k generalizing x with
  | zero => exact Complex.ext rfl (hr _ hx).symm
  | succ k ih =>
    simp only [Function.iterate_succ_apply']
    have h := (ha.iterated_deriv k x hx).differentiableAt.hasDerivAt.ofReal_comp
    apply (h.congr_of_eventuallyEq _).unique (hg.iterated_deriv k _ hx).differentiableAt.hasDerivAt.comp_ofReal
    exact eventually_of_mem (near_real ho hx) fun t ht => (ih ht).symm
lemma analyticOnNhd_re_ofReal {ε : ℝ} (hε : 0 < ε) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (nbhd ε)) :
    AnalyticOnNhd ℝ (restr g) I := fun _ hx => (hg.analyticOnNhd (isOpen_nbhd _) _ (ofReal_mem_nbhd hε hx)).re_ofReal

/-- Regular analytic functions on the interval. -/
def Regular (g : ℝ → ℝ) := AnalyticOnNhd ℝ g I ∧ ∀ x ∈ I, deriv g x ≠ 0

lemma mean_slope {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f I) {x y} (hx : x ∈ I) (hy : y ∈ I) (h : x < y) :
    ∃ t ∈ Icc x y, deriv f t * (y-x) = f y - f x := by
  have sub := Icc_subset_Icc hx.1 hy.2
  obtain ⟨t,ht,H⟩ := exists_deriv_eq_slope f h (hf.continuousOn.mono sub) (hf.mono (Ioo_subset_Icc_self.trans sub))
  exact ⟨t,Ioo_subset_Icc_self ht,(eq_div_iff (sub_ne_zero.mpr h.ne')).mp H⟩

lemma Regular.injOn {f} (hf : Regular f) : InjOn f I := by
  have step {x y} (hx : x ∈ I) (hy : y ∈ I) (e : f x = f y) : y ≤ x := by
    by_contra! h; obtain ⟨t,ht,H⟩ := mean_slope hf.1.differentiableOn hx hy h
    have := hf.2 _ (Icc_subset_Icc hx.1 hy.2 ht); grind
  exact fun _ hx _ hy e => le_antisymm (step hy hx e.symm) (step hx hy e)

/-- Differentiating a slope ratio extracts the difference of logarithmic derivatives. -/
lemma ratio_jet {u v} (hu : Regular u) (hv : Regular v) {x} (hx : x ∈ I) : HasDerivAt (fun y => deriv u y / deriv v y)
    (deriv u x / deriv v x * (logDer u x - logDer v x)) x := by
  apply ((hu.1 x hx).deriv.differentiableAt.hasDerivAt.div (hv.1 x hx).deriv.differentiableAt.hasDerivAt (hv.2 x hx)).congr_deriv
  dsimp [logDer]; field_simp [hu.2 x hx,hv.2 x hx]

lemma Regular.coord {g} (hg : Regular g) : IsAnalyticCoord g := ⟨hg.1,hg.injOn⟩

/-- A function with zero derivative within `[0,1]` at every point of `[0,1]` is constant there. -/
theorem eq_of_hasDerivWithinAt_zero_I {u : ℝ → ℝ}
    (hu : ∀ x ∈ I, HasDerivWithinAt u 0 I x) {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) :
    u x = u y := by
  simpa [sub_eq_zero] using (convex_Icc 0 1).norm_image_sub_le_of_norm_hasDerivWithin_le hu (C := 0) (by simp) hy hx

/-- Evaluation is bounded by the supremum on a compact set. -/
lemma le_sup {α : Type*} [TopologicalSpace α] {s : Set α} (hs : IsCompact s) {f : α → ℝ}
    (hf : ContinuousOn f s) {x} (hx : x ∈ s) : f x ≤ ⨆ y : s, f y :=
  le_ciSup (f := fun y : s => f y) (image_eq_range f s ▸ hs.bddAbove_image hf) ⟨x,hx⟩

lemma logDer_comp {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {g f : 𝕜 → 𝕜} {x : 𝕜}
    (hg : AnalyticAt 𝕜 g (f x)) (hf : AnalyticAt 𝕜 f x) (hne : deriv g (f x) ≠ 0) :
    logDer (g ∘ f) x = logDer f x + deriv f x * logDer g (f x) := by
  have H := iteratedDeriv_comp_two hg.contDiffAt hf.contDiffAt
  simp [iteratedDeriv_succ] at H
  rw [logDer,deriv_comp x hg.differentiableAt hf.differentiableAt,H]; grind

namespace IFS

variable {N : ℕ} (Φ : IFS N)

lemma real_mem {x : ℝ} (hx : x ∈ I) : (x:ℂ) ∈ Φ.tube := ofReal_mem_nbhd Φ.ε_pos hx

lemma closedReal {x : ℝ} (hx : x ∈ I) : (x:ℂ) ∈ Φ.box :=
  subset_closure (Φ.real_mem hx)

/-! ## Single maps -/

lemma analytic_f (i : Fin N) : AnalyticOnNhd ℂ (Φ.f i) (Φ.box) :=
  ((Φ.inClass i).differentiableOn.analyticOnNhd (isOpen_nbhd _)).mono (cl_two Φ.ε_pos)

instance (ε : ℝ) : CompactSpace (closure (nbhd ε)) := isCompact_iff_compactSpace.mp (nbhd_eq ε ▸ isCompact_image_I.isBounded.thickening.isCompact_closure)

/-- Restrict a continuous family to the compact box. Its product norm controls all evaluations. -/
noncomputable abbrev onBox {f : ℂ → ℂ} (h : ContinuousOn f Φ.box) : C(Φ.box,ℂ) := ⟨_,h.domRestrict⟩

lemma eval_le {X ι : Type*} [TopologicalSpace X] [CompactSpace X] [Fintype ι] (f : ι → C(X,ℂ)) (i x) : ‖f i x‖ ≤ ‖f‖ :=
  ((f i).norm_coe_le_norm x).trans (norm_le_pi_norm f i)

noncomputable abbrev slope (i : Fin N) := Φ.onBox (Φ.analytic_f i).deriv.continuousOn

lemma cmax_eq : Φ.cmax = ‖Φ.slope‖ := by
  simp only [Pi.norm_def,Finset.sup_univ_eq_ciSup,NNReal.coe_iSup,coe_nnnorm,ContinuousMap.norm_eq_iSup_norm]; rfl

lemma cmax_nonneg : 0 ≤ Φ.cmax := Φ.cmax_eq ▸ norm_nonneg _

lemma cmax_lt {r : ℝ} (hr : 0 < r) (h : ∀ i z, z ∈ Φ.box → ‖deriv (Φ.f i) z‖ < r) : Φ.cmax < r :=
  Φ.cmax_eq ▸ (pi_norm_lt_iff hr).mpr fun i => ((Φ.slope i).norm_lt_iff hr).mpr fun z => h i _ z.2

lemma cmax_lt_one : Φ.cmax < 1 := Φ.cmax_lt one_pos fun i => (Φ.inClass i).norm_deriv_lt_one

lemma shrinks : Tendsto (fun n : ℕ => Φ.cmax^n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one

lemma norm_deriv_le_cmax (i : Fin N) {z : ℂ} (hz : z ∈ Φ.box) : ‖deriv (Φ.f i) z‖ ≤ Φ.cmax :=
  Φ.cmax_eq ▸ eval_le Φ.slope i ⟨z,hz⟩

noncomputable abbrev invSlope (i : Fin N) := Φ.onBox ((Φ.analytic_f i).deriv.continuousOn.inv₀ (Φ.inClass i).deriv_ne_zero)

/-- A positive lower bound for the contraction ratios, including the empty alphabet. -/
noncomputable def cmin := (max 1 ‖Φ.invSlope‖)⁻¹

lemma cmin_pos : 0 < Φ.cmin := by unfold cmin; positivity

lemma cmin_le_norm_deriv (i : Fin N) {z : ℂ} (hz : z ∈ Φ.box) : Φ.cmin ≤ ‖deriv (Φ.f i) z‖ := by
  apply (inv_le_comm₀ (by positivity) (norm_pos_iff.mpr ((Φ.inClass i).deriv_ne_zero _ hz))).mpr
  rw [← norm_inv]; exact (eval_le Φ.invSlope i ⟨z,hz⟩).trans (le_max_right ..)

lemma cmax_pos [NeZero N] : 0 < Φ.cmax :=
  (norm_pos_iff.mpr ((Φ.inClass 0).deriv_ne_zero _ (Φ.closedReal zero_I))).trans_le (Φ.norm_deriv_le_cmax 0 (Φ.closedReal zero_I))

lemma analytic_nonlin (i : Fin N) : AnalyticOnNhd ℂ (Φ.nonlin i) (Φ.box) :=
  ((Φ.analytic_f i).deriv.deriv).div (Φ.analytic_f i).deriv (Φ.inClass i).deriv_ne_zero

noncomputable abbrev outerBeta := ‖fun i => Φ.onBox (Φ.analytic_nonlin i).continuousOn‖

/-! ## Compositions along finite words -/

@[simp] theorem comp_nil : Φ.comp [] = id := rfl

@[simp] theorem comp_cons (i : Fin N) (w : Letters N) : Φ.comp (i :: w) = Φ.f i ∘ Φ.comp w :=
  rfl

theorem comp_append (u v : Letters N) : Φ.comp (u ++ v) = Φ.comp u ∘ Φ.comp v := by
  induction u with
  | nil => rfl
  | cons i u ih => aesop

lemma mapsTo_word {s : Set ℂ} (h : ∀ i, MapsTo (Φ.f i) s s) (w : Letters N) : MapsTo (Φ.comp w) s s := by
  induction w with
  | nil => exact mapsTo_id _
  | cons i w ih => exact (h i).comp ih

lemma mapsTo_comp (w : Letters N) : MapsTo (Φ.comp w) Φ.tube Φ.tube := Φ.mapsTo_word (fun i _ hz => (Φ.inClass i).mapsTo _ (subset_closure hz)) w
lemma mapsTo_comp_closure (w : Letters N) : MapsTo (Φ.comp w) Φ.box Φ.box := Φ.mapsTo_word (fun i _ hz => subset_closure ((Φ.inClass i).mapsTo _ hz)) w

lemma analytic_comp (w : Letters N) : AnalyticOnNhd ℂ (Φ.comp w) (Φ.box) := by
  induction w with
  | nil => exact analyticOnNhd_id
  | cons i w ih => exact (Φ.analytic_f i).comp ih (Φ.mapsTo_comp_closure w)

theorem differentiableAt_comp (w : Letters N) {z : ℂ} (hz : z ∈ Φ.box) :
    DifferentiableAt ℂ (Φ.comp w) z := (Φ.analytic_comp w z hz).differentiableAt

theorem differentiableOn_comp (w : Letters N) : DifferentiableOn ℂ (Φ.comp w) Φ.tube :=
  (Φ.analytic_comp w).differentiableOn.mono subset_closure

theorem deriv_comp_append (u v : Letters N) {z : ℂ} (hz : z ∈ Φ.box) :
    deriv (Φ.comp (u ++ v)) z = deriv (Φ.comp u) (Φ.comp v z) * deriv (Φ.comp v) z := by
  rw [comp_append]
  exact deriv_comp z (Φ.differentiableAt_comp u (Φ.mapsTo_comp_closure v hz))
    (Φ.differentiableAt_comp v hz)

theorem deriv_comp_cons (i : Fin N) (w : Letters N) {z : ℂ} (hz : z ∈ Φ.box) :
    deriv (Φ.comp (i :: w)) z = deriv (Φ.f i) (Φ.comp w z) * deriv (Φ.comp w) z := Φ.deriv_comp_append [i] w hz

lemma bounds (w : Letters N) {z : ℂ} (hz : z ∈ Φ.box) :
    Φ.cmin^w.length ≤ ‖deriv (Φ.comp w) z‖ ∧ ‖deriv (Φ.comp w) z‖ ≤ Φ.cmax^w.length := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [Φ.deriv_comp_cons i w hz,norm_mul,List.length_cons,pow_succ',pow_succ']
    have h := Φ.mapsTo_comp_closure w hz
    exact ⟨mul_le_mul (Φ.cmin_le_norm_deriv i h) ih.1 (pow_nonneg Φ.cmin_pos.le _) (norm_nonneg _),
      mul_le_mul (Φ.norm_deriv_le_cmax i h) ih.2 (norm_nonneg _) Φ.cmax_nonneg⟩

theorem deriv_comp_ne_zero (w : Letters N) {z : ℂ} (hz : z ∈ Φ.box) :
    deriv (Φ.comp w) z ≠ 0 := norm_pos_iff.mp ((pow_pos Φ.cmin_pos _).trans_le (Φ.bounds w hz).1)

/-- On the real slice composition commutes with restriction. -/
lemma real_comp (w : Letters N) {x : ℝ} (hx : (x:ℂ) ∈ Φ.tube) :
    Φ.comp w x = (Challenge.realComp Φ.realMap w x : ℂ) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    have h := cl_two Φ.ε_pos (subset_closure (Φ.mapsTo_comp w hx))
    rw [comp_cons,Function.comp_apply,ih]; rw [ih] at h
    exact Complex.ext rfl ((Φ.inClass i).im_eq_zero _ h)

lemma im_comp_ofReal (w : Letters N) {x : ℝ} (hx : (x:ℂ) ∈ Φ.tube) : (Φ.comp w x).im = 0 := by rw [Φ.real_comp w hx]; rfl

lemma comp_ofReal (w : Letters N) {x : ℝ} (hx : x ∈ I) : Φ.comp w x = ((Φ.comp w x).re : ℂ) := by rw [Φ.real_comp w (Φ.real_mem hx)]; rfl

/-- The real restriction of a word map. -/
abbrev R (w : Letters N) (x : ℝ) := (Φ.comp w x).re

theorem re_comp_mem_I (w : Letters N) : MapsTo (Φ.R w) I I := by
  intro x hx
  change (Φ.comp w x).re ∈ I
  induction w with
  | nil => simpa using hx
  | cons i w ih =>
    rw [comp_cons, Function.comp_apply, Φ.comp_ofReal w hx]
    exact (Φ.inClass i).re_mem_I _ ih

lemma R_jet (w : Letters N) (k : ℕ) {x : ℝ} (hx : (x:ℂ) ∈ Φ.tube) :
    ((deriv^[k] (Φ.R w) x : ℝ):ℂ) = deriv^[k] (Φ.comp w) x := real_jet (isOpen_nbhd _) ((Φ.analytic_comp w).mono subset_closure)
      (fun _ => Φ.im_comp_ofReal w) k hx

lemma R_deriv (w : Letters N) {x} (hx : x ∈ I) : ((deriv (Φ.R w) x:ℝ):ℂ) = deriv (Φ.comp w) x := Φ.R_jet w 1 (Φ.real_mem hx)

lemma R_logDer (a : Letters N) {x : ℝ} (hx : (x:ℂ) ∈ Φ.tube) : ((logDer (Φ.R a) x:ℝ):ℂ) = logDer (Φ.comp a) x := by
  rw [logDer,Complex.ofReal_div]; exact congrArg₂ (· / ·) (Φ.R_jet a 2 hx) (Φ.R_jet a 1 hx)

lemma regular_R (w : Letters N) : Regular (Φ.R w) :=
  ⟨analyticOnNhd_re_ofReal Φ.ε_pos (Φ.differentiableOn_comp w),fun x hx h =>
    Φ.deriv_comp_ne_zero w (Φ.closedReal hx) (by rw [← Φ.R_deriv w hx,h]; simp)⟩

lemma R_bounds (a : Letters N) {x} (hx : x ∈ I) :
    Φ.cmin ^ a.length ≤ |deriv (Φ.R a) x| ∧ |deriv (Φ.R a) x| ≤ Φ.cmax ^ a.length := by
  simpa [← Φ.R_deriv a hx] using Φ.bounds a (Φ.closedReal hx)

lemma deriv_R_lt {a : Letters N} (ha : a ≠ []) {x} (hx : x ∈ I) : |deriv (Φ.R a) x| < 1 :=
  (Φ.R_bounds a hx).2.trans_lt (pow_lt_one₀ Φ.cmax_nonneg Φ.cmax_lt_one (List.length_pos_iff.mpr ha).ne')

lemma R_lip (w : Letters N) {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) :
    |Φ.R w x - Φ.R w y| ≤ Φ.cmax^w.length * |x-y| :=
  (convex_Icc 0 1).norm_image_sub_le_of_norm_deriv_le (fun x hx => ((Φ.regular_R w).1 x hx).differentiableAt)
    (fun _ h => (Φ.R_bounds w h).2) hy hx

lemma abs_re_comp_sub_le (w : Letters N) {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) : |Φ.R w x - Φ.R w y| ≤ Φ.cmax^w.length :=
  (Φ.R_lip w hx hy).trans (mul_le_of_le_one_right (pow_nonneg Φ.cmax_nonneg _) (by grind))

lemma R_append (u v : Letters N) {x : ℝ} (hx : x ∈ I) : Φ.R (u++v) x = Φ.R u (Φ.R v x) := by
  simp only [R,Φ.comp_append,Function.comp_apply]; conv_lhs => rw [Φ.comp_ofReal v hx]

end IFS
end AnalyticESC
