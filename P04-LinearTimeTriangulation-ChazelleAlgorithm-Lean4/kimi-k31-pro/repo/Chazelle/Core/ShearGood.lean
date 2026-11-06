module

public import Chazelle.Core.SpecBase
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.LeftRightNhds

/-!
# Existence of a good shear parameter (WP-A)

Every quantity the visibility-map stage tests on the sheared polygon `shear ε P` is a rational
function of `ε` (`IsRatFn`: eventually, as `ε → 0⁺`, a quotient of polynomials with eventually
nonvanishing denominator; Lean's `x / 0 = 0` is handled by the closure under division).  A
rational function has an eventually constant sign as `ε → 0⁺` (`IsRatFn.evSign`: a nonzero
polynomial has finitely many roots, and the intermediate value theorem).  There are finitely many
tests (symbolic points with indices below `n`), so all of them are eventually constant; distinct
heights and agreement with the `(y, x)`-lexicographic order also hold eventually.  Main result:
`goodShearExists : GoodShearExistsSpec`.
-/

namespace Chazelle.Core

public section

open Set Filter Topology Polynomial

/-! ## Eventual signs near `0⁺` -/

/-- The complement of a finite set of reals belongs to `𝓝[>] 0`. -/
theorem compl_mem_nhdsGT_of_finite {S : Set ℝ} (hS : S.Finite) : Sᶜ ∈ 𝓝[>] (0 : ℝ) := by
  have h1 : (S \ {0})ᶜ ∈ 𝓝 (0 : ℝ) :=
    (hS.subset sdiff_subset).isClosed.compl_mem_nhds (fun h => h.2 rfl)
  filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with x hx1 hx2 hx
  exact hx1 ⟨hx, ne_of_gt hx2⟩

/-- A real polynomial is eventually zero or eventually nonzero as `ε → 0⁺`. -/
theorem poly_eventually_zero_or_ne (p : ℝ[X]) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), p.eval ε = 0) ∨ ∀ᶠ ε in 𝓝[>] (0 : ℝ), p.eval ε ≠ 0 := by
  by_cases hp : p = 0
  · left
    subst hp
    simp
  · right
    filter_upwards [compl_mem_nhdsGT_of_finite (finite_setOfPred_isRoot hp)] with x hx
    exact hx

/-- `f` has an eventually constant sign as `ε → 0⁺`. -/
@[expose] def EvSign (f : ℝ → ℝ) : Prop :=
  (∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < f ε) ∨ (∀ᶠ ε in 𝓝[>] (0 : ℝ), f ε = 0) ∨
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), f ε < 0

/-- A continuous function that is eventually nonzero as `ε → 0⁺` is eventually positive or
eventually negative (intermediate value theorem). -/
theorem evSign_of_continuous_of_ne {f : ℝ → ℝ} (hf : Continuous f)
    (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), f ε ≠ 0) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < f ε) ∨ ∀ᶠ ε in 𝓝[>] (0 : ℝ), f ε < 0 := by
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h
  have hδ0 : (0 : ℝ) < δ := hδ
  have hc : δ / 2 ∈ Ioo 0 δ := ⟨by linarith, by linarith⟩
  have hconn : (f '' Ioo 0 δ).OrdConnected :=
    (isPreconnected_Ioo.image f hf.continuousOn).ordConnected
  have key : ∀ x ∈ Ioo 0 δ, ∀ y ∈ Ioo 0 δ, f x < 0 → 0 < f y → False := by
    intro x hx y hy hfx hfy
    obtain ⟨z, hz, hz0⟩ :=
      hconn.out (mem_image_of_mem f hx) (mem_image_of_mem f hy) ⟨hfx.le, hfy.le⟩
    exact hsub hz hz0
  rcases lt_or_gt_of_ne (hsub hc) with hneg | hpos
  · right
    filter_upwards [Ioo_mem_nhdsGT hδ0] with x hx
    rcases lt_or_gt_of_ne (hsub hx) with h1 | h1
    · exact h1
    · exact (key _ hc _ hx hneg h1).elim
  · left
    filter_upwards [Ioo_mem_nhdsGT hδ0] with x hx
    rcases lt_or_gt_of_ne (hsub hx) with h1 | h1
    · exact (key _ hx _ hc h1 hpos).elim
    · exact h1

/-- A polynomial has an eventually constant sign as `ε → 0⁺`. -/
theorem evSign_poly (p : ℝ[X]) : EvSign (fun ε => p.eval ε) := by
  rcases poly_eventually_zero_or_ne p with h | h
  · exact Or.inr (Or.inl h)
  · rcases evSign_of_continuous_of_ne p.continuous h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inr h')

/-! ## Rational functions of the shear parameter -/

/-- `f` is, near `0⁺`, a quotient of real polynomials whose denominator is eventually
nonzero. -/
@[expose] def IsRatFn (f : ℝ → ℝ) : Prop :=
  ∃ p q : ℝ[X], (∀ᶠ ε in 𝓝[>] (0 : ℝ), q.eval ε ≠ 0) ∧
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), f ε = p.eval ε / q.eval ε

/-- **A rational function has an eventually constant sign as `ε → 0⁺`.** -/
theorem IsRatFn.evSign {f : ℝ → ℝ} (hf : IsRatFn f) : EvSign f := by
  obtain ⟨p, q, hq, hfe⟩ := hf
  rcases evSign_of_continuous_of_ne q.continuous hq with hq' | hq' <;>
    rcases evSign_poly p with hp | hp | hp
  · left
    filter_upwards [hfe, hq', hp] with ε h1 h2 h3
    rw [h1]
    exact div_pos_iff.2 (Or.inl ⟨h3, h2⟩)
  · right; left
    filter_upwards [hfe, hp] with ε h1 h3
    rw [h1, h3, zero_div]
  · right; right
    filter_upwards [hfe, hq', hp] with ε h1 h2 h3
    rw [h1]
    exact div_neg_iff.2 (Or.inr ⟨h3, h2⟩)
  · right; right
    filter_upwards [hfe, hq', hp] with ε h1 h2 h3
    rw [h1]
    exact div_neg_iff.2 (Or.inl ⟨h3, h2⟩)
  · right; left
    filter_upwards [hfe, hp] with ε h1 h3
    rw [h1, h3, zero_div]
  · left
    filter_upwards [hfe, hq', hp] with ε h1 h2 h3
    rw [h1]
    exact div_pos_iff.2 (Or.inr ⟨h3, h2⟩)

/-- Rational functions are closed under pointwise equality. -/
theorem IsRatFn.congr {f g : ℝ → ℝ} (hf : IsRatFn f) (h : ∀ ε, f ε = g ε) : IsRatFn g := by
  rwa [← funext h]

/-- Constants are rational functions. -/
theorem isRatFn_const (c : ℝ) : IsRatFn (fun _ => c) :=
  ⟨C c, 1, by simp, by simp⟩

/-- The identity is a rational function. -/
theorem isRatFn_id : IsRatFn (fun ε => ε) :=
  ⟨X, 1, by simp, by simp⟩

/-- Sums of rational functions are rational functions. -/
theorem IsRatFn.add {f g : ℝ → ℝ} (hf : IsRatFn f) (hg : IsRatFn g) :
    IsRatFn (fun ε => f ε + g ε) := by
  obtain ⟨p1, q1, hq1, hf1⟩ := hf
  obtain ⟨p2, q2, hq2, hg2⟩ := hg
  refine ⟨p1 * q2 + q1 * p2, q1 * q2, ?_, ?_⟩
  · filter_upwards [hq1, hq2] with ε h1 h2
    rw [eval_mul]
    exact mul_ne_zero h1 h2
  · filter_upwards [hq1, hq2, hf1, hg2] with ε h1 h2 h3 h4
    rw [h3, h4, div_add_div _ _ h1 h2]
    simp [eval_add, eval_mul]

/-- Differences of rational functions are rational functions. -/
theorem IsRatFn.sub {f g : ℝ → ℝ} (hf : IsRatFn f) (hg : IsRatFn g) :
    IsRatFn (fun ε => f ε - g ε) := by
  obtain ⟨p1, q1, hq1, hf1⟩ := hf
  obtain ⟨p2, q2, hq2, hg2⟩ := hg
  refine ⟨p1 * q2 - q1 * p2, q1 * q2, ?_, ?_⟩
  · filter_upwards [hq1, hq2] with ε h1 h2
    rw [eval_mul]
    exact mul_ne_zero h1 h2
  · filter_upwards [hq1, hq2, hf1, hg2] with ε h1 h2 h3 h4
    rw [h3, h4, div_sub_div _ _ h1 h2]
    simp [eval_sub, eval_mul]

/-- Products of rational functions are rational functions. -/
theorem IsRatFn.mul {f g : ℝ → ℝ} (hf : IsRatFn f) (hg : IsRatFn g) :
    IsRatFn (fun ε => f ε * g ε) := by
  obtain ⟨p1, q1, hq1, hf1⟩ := hf
  obtain ⟨p2, q2, hq2, hg2⟩ := hg
  refine ⟨p1 * p2, q1 * q2, ?_, ?_⟩
  · filter_upwards [hq1, hq2] with ε h1 h2
    rw [eval_mul]
    exact mul_ne_zero h1 h2
  · filter_upwards [hf1, hg2] with ε h3 h4
    rw [h3, h4, div_mul_div_comm]
    simp [eval_mul]

/-- Quotients of rational functions are rational functions (with Lean's `x / 0 = 0`). -/
theorem IsRatFn.div {f g : ℝ → ℝ} (hf : IsRatFn f) (hg : IsRatFn g) :
    IsRatFn (fun ε => f ε / g ε) := by
  obtain ⟨p1, q1, hq1, hf1⟩ := hf
  obtain ⟨p2, q2, hq2, hg2⟩ := hg
  rcases poly_eventually_zero_or_ne p2 with hp | hp
  · refine ⟨0, 1, by simp, ?_⟩
    filter_upwards [hg2, hp] with ε h1 h2
    rw [h1, h2]
    simp
  · refine ⟨p1 * q2, q1 * p2, ?_, ?_⟩
    · filter_upwards [hq1, hp] with ε h1 h2
      rw [eval_mul]
      exact mul_ne_zero h1 h2
    · filter_upwards [hf1, hg2] with ε h1 h2
      rw [h1, h2, div_div_div_eq]
      simp [eval_mul]

/-- The abscissa of a sheared point is a rational function of the parameter. -/
theorem isRatFn_shear_fst (a : Point) : IsRatFn (fun ε => (shearPt ε a).1) :=
  isRatFn_const a.1

/-- The ordinate of a sheared point is a rational function of the parameter. -/
theorem isRatFn_shear_snd (a : Point) : IsRatFn (fun ε => (shearPt ε a).2) :=
  (isRatFn_const a.2).add (isRatFn_id.mul (isRatFn_const a.1))

/-- The abscissa of a symbolic point of the sheared polygon is a rational function of the
parameter. -/
theorem isRatFn_eval_fst (P : Polygon) (s : SymPt) :
    IsRatFn (fun ε => (s.eval (shear ε P)).1) := by
  cases s with
  | vtx i =>
    exact (isRatFn_shear_fst (P.vtx i)).congr (fun ε => by simp [SymPt.eval, shear_vtx])
  | onEdge e h =>
    refine ((isRatFn_shear_fst (P.vtx e)).add
      (((isRatFn_shear_snd (P.vtx h)).sub (isRatFn_shear_snd (P.vtx e))).mul
        (((isRatFn_shear_fst (P.vtx ((e + 1) % P.n))).sub (isRatFn_shear_fst (P.vtx e))).div
          ((isRatFn_shear_snd (P.vtx ((e + 1) % P.n))).sub
            (isRatFn_shear_snd (P.vtx e)))))).congr ?_
    intro ε
    simp [SymPt.eval, edgeXAt, Visibility.edgeX, Visibility.xAt, shear_vtx, shear_n]

/-- The ordinate of a symbolic point of the sheared polygon is a rational function of the
parameter. -/
theorem isRatFn_eval_snd (P : Polygon) (s : SymPt) :
    IsRatFn (fun ε => (s.eval (shear ε P)).2) := by
  cases s with
  | vtx i =>
    exact (isRatFn_shear_snd (P.vtx i)).congr (fun ε => by simp [SymPt.eval, shear_vtx])
  | onEdge e h =>
    exact (isRatFn_shear_snd (P.vtx h)).congr (fun ε => by simp [SymPt.eval, shear_vtx])

/-- The orientation determinant of three symbolic points of the sheared polygon is a rational
function of the parameter. -/
theorem isRatFn_det_eval (P : Polygon) (s₁ s₂ s₃ : SymPt) :
    IsRatFn (fun ε => det (s₁.eval (shear ε P)) (s₂.eval (shear ε P)) (s₃.eval (shear ε P))) :=
  ((((isRatFn_eval_fst P s₂).sub (isRatFn_eval_fst P s₁)).mul
    ((isRatFn_eval_snd P s₃).sub (isRatFn_eval_snd P s₁))).sub
    (((isRatFn_eval_fst P s₃).sub (isRatFn_eval_fst P s₁)).mul
      ((isRatFn_eval_snd P s₂).sub (isRatFn_eval_snd P s₁)))).congr (fun ε => by
        simp [det])

/-! ## Eventually constant truth values -/

/-- The proposition `φ ε` has an eventually constant truth value as `ε → 0⁺`. -/
@[expose] def EvConst (φ : ℝ → Prop) : Prop := ∃ b : Prop, ∀ᶠ ε in 𝓝[>] (0 : ℝ), φ ε = b

/-- Positivity of a function with eventually constant sign is eventually constant. -/
theorem EvSign.evConst_pos {f : ℝ → ℝ} (h : EvSign f) : EvConst (fun ε => 0 < f ε) := by
  rcases h with h | h | h
  · exact ⟨True, h.mono fun ε hε => eq_true hε⟩
  · exact ⟨False, h.mono fun ε hε => eq_false (show ¬ 0 < f ε by rw [hε]; exact lt_irrefl 0)⟩
  · exact ⟨False, h.mono fun ε hε => eq_false (not_lt.2 hε.le)⟩

/-- Vanishing of a function with eventually constant sign is eventually constant. -/
theorem EvSign.evConst_zero {f : ℝ → ℝ} (h : EvSign f) : EvConst (fun ε => f ε = 0) := by
  rcases h with h | h | h
  · exact ⟨False, h.mono fun ε hε => eq_false hε.ne'⟩
  · exact ⟨True, h.mono fun ε hε => eq_true hε⟩
  · exact ⟨False, h.mono fun ε hε => eq_false hε.ne⟩

/-- The order of two rational functions is eventually constant. -/
theorem evConst_lt {f g : ℝ → ℝ} (hf : IsRatFn f) (hg : IsRatFn g) :
    EvConst (fun ε => f ε < g ε) := by
  obtain ⟨B, hB⟩ := (hg.sub hf).evSign.evConst_pos
  exact ⟨B, hB.mono fun ε h => (propext (sub_pos (a := g ε) (b := f ε))).symm.trans h⟩

/-- **The sign facts of three symbolic points of the sheared polygon are eventually constant
as `ε → 0⁺`.** -/
theorem evConst_signFacts (P : Polygon) (s₁ s₂ s₃ : SymPt) :
    ∃ B, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      SignFacts (s₁.eval (shear ε P)) (s₂.eval (shear ε P)) (s₃.eval (shear ε P)) = B := by
  obtain ⟨b1, h1⟩ := evConst_lt (isRatFn_eval_fst P s₁) (isRatFn_eval_fst P s₂)
  obtain ⟨b2, h2⟩ := evConst_lt (isRatFn_eval_snd P s₁) (isRatFn_eval_snd P s₂)
  obtain ⟨b3, h3⟩ := (isRatFn_det_eval P s₁ s₂ s₃).evSign.evConst_pos
  obtain ⟨b4, h4⟩ := (isRatFn_det_eval P s₁ s₂ s₃).evSign.evConst_zero
  refine ⟨(b1, b2, b3, b4), ?_⟩
  filter_upwards [h1, h2, h3, h4] with ε e1 e2 e3 e4
  unfold SignFacts
  exact Prod.ext e1 (Prod.ext e2 (Prod.ext e3 e4))

/-! ## Heights and the lexicographic order -/

/-- Two distinct points get distinct sheared heights for all small `ε > 0`. -/
theorem shear_heights_ne_eventually {a b : Point} (hab : a ≠ b) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), (shearPt ε a).2 ≠ (shearPt ε b).2 := by
  have hr  := (isRatFn_shear_snd a).sub (isRatFn_shear_snd b)
  rcases hr.evSign with h | h | h
  · exact h.mono fun ε hε => (sub_pos.1 hε).ne'
  · exfalso
    obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h
    have hδ0 : (0 : ℝ) < δ := hδ
    have e1 : (shearPt (δ / 2) a).2 - (shearPt (δ / 2) b).2 = 0 :=
      hsub (show δ / 2 ∈ Ioo 0 δ from ⟨by linarith, by linarith⟩)
    have e2 : (shearPt (δ / 4) a).2 - (shearPt (δ / 4) b).2 = 0 :=
      hsub (show δ / 4 ∈ Ioo 0 δ from ⟨by linarith, by linarith⟩)
    simp [shearPt] at e1 e2
    have h3 : (δ / 4) * (a.1 - b.1) = 0 := by linarith
    rcases mul_eq_zero.1 h3 with h4 | h4
    · linarith
    · have hx : a.1 = b.1 := by linarith
      rw [hx] at e1
      exact hab (Prod.ext hx (by linarith))
  · exact h.mono fun ε hε => (sub_neg.1 hε).ne

/-- The height of a sheared point is continuous in the parameter. -/
theorem continuous_shear_snd (a : Point) : Continuous fun ε : ℝ => (shearPt ε a).2 := by
  unfold shearPt
  fun_prop

/-- For all small `ε > 0`, the height order of the sheared points is the `(y, x)`-lexicographic
order of the original points. -/
theorem ylex_shear_eventually (a b : Point) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (Mountain.ylexLT a b ↔ Mountain.ylexLT (shearPt ε a) (shearPt ε b)) := by
  rcases lt_trichotomy a.2 b.2 with h | h | h
  · have hc : ∀ᶠ ε in 𝓝 (0 : ℝ), (shearPt ε a).2 < (shearPt ε b).2 :=
      (continuous_shear_snd a).continuousAt.eventually_lt (continuous_shear_snd b).continuousAt
        (by simpa [shearPt] using h)
    filter_upwards [nhdsWithin_le_nhds hc] with ε hε
    exact iff_of_true (Or.inl h) (Or.inl hε)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    unfold Mountain.ylexLT
    dsimp [shearPt]
    constructor
    · rintro (h1 | ⟨-, h1⟩)
      · linarith
      · left
        nlinarith
    · rintro (h1 | ⟨-, h1⟩)
      · right
        exact ⟨by nlinarith, by nlinarith⟩
      · right
        exact ⟨by rw [h], h1⟩
  · have hc : ∀ᶠ ε in 𝓝 (0 : ℝ), (shearPt ε b).2 < (shearPt ε a).2 :=
      (continuous_shear_snd b).continuousAt.eventually_lt (continuous_shear_snd a).continuousAt
        (by simpa [shearPt] using h)
    filter_upwards [nhdsWithin_le_nhds hc] with ε hε
    unfold Mountain.ylexLT
    exact iff_of_false (by rintro (h1 | ⟨h1, -⟩) <;> linarith)
      (by rintro (h1 | ⟨h1, -⟩) <;> linarith)

/-! ## The main theorem -/

/-- Finitely many symbolic points have indices below `n`. -/
theorem symPt_lt_finite (n : ℕ) : {s : SymPt | s.Lt n}.Finite := by
  have h : {s : SymPt | s.Lt n} ⊆ range (fun i : Fin n => SymPt.vtx i) ∪
      range (fun p : Fin n × Fin n => SymPt.onEdge p.1 p.2) := by
    intro s hs
    cases s with
    | vtx i => exact Or.inl ⟨⟨i, hs⟩, rfl⟩
    | onEdge e h => exact Or.inr ⟨(⟨e, hs.1⟩, ⟨h, hs.2⟩), rfl⟩
  exact ((finite_range _).union (finite_range _)).subset h

/-- **WP-A: every simple polygon has a good shear parameter.** -/
theorem goodShearExists : GoodShearExistsSpec := by
  intro P hP
  have hS : {s : SymPt | s.Lt P.n}.Finite := symPt_lt_finite P.n
  choose B hB using fun s₁ s₂ s₃ : SymPt => evConst_signFacts P s₁ s₂ s₃
  have hStab : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ s₁ ∈ {s : SymPt | s.Lt P.n},
      ∀ s₂ ∈ {s : SymPt | s.Lt P.n}, ∀ s₃ ∈ {s : SymPt | s.Lt P.n},
        SignFacts (s₁.eval (shear ε P)) (s₂.eval (shear ε P)) (s₃.eval (shear ε P)) =
          B s₁ s₂ s₃ := by
    rw [eventually_all_finite hS]
    intro s₁ _
    rw [eventually_all_finite hS]
    intro s₂ _
    rw [eventually_all_finite hS]
    intro s₃ _
    exact hB s₁ s₂ s₃
  have hI : (Iio P.n).Finite := finite_Iio _
  have hDist : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i ∈ Iio P.n, ∀ j ∈ Iio P.n, i ≠ j →
      (shearPt ε (P.vtx i)).2 ≠ (shearPt ε (P.vtx j)).2 := by
    rw [eventually_all_finite hI]
    intro i hi
    rw [eventually_all_finite hI]
    intro j hj
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => (h hij).elim
    · have hne : P.vtx i ≠ P.vtx j := fun h => hij (hP.2.1 i j hi hj h)
      exact (shear_heights_ne_eventually hne).mono fun ε h _ => h
  have hYlex : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i ∈ Iio P.n, ∀ j ∈ Iio P.n,
      (Mountain.ylexLT (P.vtx i) (P.vtx j) ↔
        Mountain.ylexLT (shearPt ε (P.vtx i)) (shearPt ε (P.vtx j))) := by
    rw [eventually_all_finite hI]
    intro i _
    rw [eventually_all_finite hI]
    intro j _
    exact ylex_shear_eventually _ _
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hStab.and (hDist.and hYlex))
  have hδ0 : (0 : ℝ) < δ := hδ
  obtain ⟨hStε, hDε, hYε⟩ := hsub (show δ / 2 ∈ Ioo 0 δ from ⟨by linarith, by linarith⟩)
  refine ⟨δ / 2, by linarith, ?_, ?_, ?_⟩
  · intro i j hi hj hij
    rw [shear_n] at hi hj
    rw [shear_vtx, shear_vtx]
    exact hDε i hi j hj hij
  · intro i j hi hj
    rw [shear_vtx, shear_vtx]
    exact hYε i hi j hj
  · intro ε' hε' hle s₁ s₂ s₃ h₁ h₂ h₃
    obtain ⟨hSt', -, -⟩ := hsub (show ε' ∈ Ioo 0 δ from ⟨hε', by linarith⟩)
    rw [hStε s₁ h₁ s₂ h₂ s₃ h₃, hSt' s₁ h₁ s₂ h₂ s₃ h₃]

end

end Chazelle.Core
