module

public import RequestProject.LocalDirichletNormalBootstrap
public import RequestProject.LocalDirichletGenuineChart
public import RequestProject.LocalDirichletRectangularSobolev
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Actual derivatives of the Dirichlet boundary restrictions

Continuous representatives supplied by the genuine rectangular L² estimate
are linked by the true horizontal FTC. The positive-height identities pass
to the bottom by dominated convergence on a finite interval. Consequently
the bottom values have the actual successive derivatives; no boundary jet
identity is included as an original-map assumption.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Metric Filter Complex MeasureTheory
open scoped Topology ContDiff

variable {a b : ℝ}

theorem dirichlet_closed_halfBox_horizontal_mem {a b x y : ℝ}
    (hx : x ∈ Icc (-a) a) (hy : y ∈ Icc 0 b) :
    rectangularComplexCoord (x, y) ∈ smoothDirichletClosedHalfBox a b := by
  simpa only [rectangularComplexCoord, smoothDirichletClosedHalfBox, mem_setOf_eq,
    Complex.add_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, zero_add,
    Complex.add_im, Complex.mul_im, mul_one] using
    (⟨abs_le.mpr hx, hy⟩)

/-- The actual full-approach continuous limit along vertical points.
This uses continuity of the constructed representative on the closed
rectangle, rather than asserting a trace limit. -/
theorem dirichlet_closed_halfBox_vertical_limit (hb : 0 < b)
    {U : ℂ → ℂ} (hU : ContinuousOn U (smoothDirichletClosedHalfBox a b))
    {x : ℝ} (hx : |x| ≤ a) :
    Tendsto (fun y  => U (rectangularComplexCoord (x, y))) (𝓝[>] 0)
      (𝓝 (U x)) := (hU.continuousWithinAt (by
    simpa only [rectangularComplexCoord, Complex.ofReal_zero, zero_mul, add_zero] using
      dirichlet_closed_halfBox_horizontal_mem (abs_le.mp hx)
        (⟨le_rfl, hb.le⟩))).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨by
    have hc : Continuous (fun y  => rectangularComplexCoord (x, y)) :=
      continuous_rectangularComplexCoord.comp
        (continuous_const.prodMk continuous_id)
    simpa only [rectangularComplexCoord, Complex.ofReal_zero, zero_mul, add_zero] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds, by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with y hy hyb
    exact dirichlet_closed_halfBox_horizontal_mem (abs_le.mp hx) ⟨hy.le, hyb.le⟩⟩)

/-- Actual horizontal FTC at the bottom, first in the increasing
orientation. The integral limit is justified by a genuine compact bound
for the continuous derivative representative. -/
theorem dirichlet_boundary_horizontal_ftc_of_le (hb : 0 < b)
    {U Q : ℂ → ℂ}
    (hU : ContinuousOn U (smoothDirichletClosedHalfBox a b))
    (hQ : ContinuousOn Q (smoothDirichletClosedHalfBox a b))
    (hd : ∀ x ∈ Ioo (-a) a, ∀ y ∈ Ioo 0 b,
      HasDerivAt (fun s  => U (rectangularComplexCoord (s, y)))
        (Q (rectangularComplexCoord (x, y))) x)
    {s t : ℝ} (hs : s ∈ Ioo (-a) a) (ht : t ∈ Ioo (-a) a) (hst : s ≤ t) :
    (∫ x in s..t, Q x) = U t - U s := by
  have hI : Icc s t ⊆ Ioo (-a) a := fun x hx =>
    ⟨hs.1.trans_le hx.1, hx.2.trans_lt ht.2⟩
  have hrow (V : ℂ → ℂ) (hV : ContinuousOn V (smoothDirichletClosedHalfBox a b))
      (y : ℝ) (hy : y ∈ Icc 0 b) :
      ContinuousOn (fun x  => V (rectangularComplexCoord (x, y))) (Icc s t) := by
    apply hV.comp (continuous_rectangularComplexCoord.comp
        (continuous_id.prodMk continuous_const)).continuousOn
    intro x hx
    exact dirichlet_closed_halfBox_horizontal_mem
      ⟨(hI hx).1.le, (hI hx).2.le⟩ hy
  obtain ⟨B, hB⟩ := (isCompact_smoothDirichletClosedHalfBox a b).exists_bound_of_continuousOn
    hQ
  have hint : Tendsto (fun y  => ∫ x in s..t, Q (rectangularComplexCoord (x, y)))
      (𝓝[>] 0) (𝓝 (∫ x in s..t, Q x)) := by
    simpa only [intervalIntegral.integral_of_le hst] using
      (tendsto_integral_filter_of_dominated_convergence (fun _  => B)
        (by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with y hy hyb
    exact ((hrow Q hQ y ⟨hy.le, hyb.le⟩).aestronglyMeasurable measurableSet_Icc).mono_measure
      (Measure.restrict_mono_set volume Ioc_subset_Icc_self)) (by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with y hy hyb
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hB _ (dirichlet_closed_halfBox_horizontal_mem
      ⟨(hI ⟨hx.1.le, hx.2⟩).1.le, (hI ⟨hx.1.le, hx.2⟩).2.le⟩ ⟨hy.le, hyb.le⟩)) (integrable_const B) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact dirichlet_closed_halfBox_vertical_limit hb hQ
      (abs_le.mpr ⟨(hI ⟨hx.1.le, hx.2⟩).1.le, (hI ⟨hx.1.le, hx.2⟩).2.le⟩)))
  exact tendsto_nhds_unique_of_eventuallyEq hint ((dirichlet_closed_halfBox_vertical_limit hb hU (abs_lt.mpr ht).le).sub
      (dirichlet_closed_halfBox_vertical_limit hb hU (abs_lt.mpr hs).le)) (by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with y hy hyb
    have hyy : y ∈ Icc 0 b := ⟨hy.le, hyb.le⟩
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst (hrow U hU y hyy)
      (fun x hx => hd x (hI ⟨hx.1.le, hx.2.le⟩) y ⟨hy, hyb⟩)
      ((hrow Q hQ y hyy).intervalIntegrable_of_Icc hst))

/-- The bottom FTC retains the true oriented interval integral. -/
theorem dirichlet_boundary_horizontal_ftc (hb : 0 < b)
    {U Q : ℂ → ℂ}
    (hU : ContinuousOn U (smoothDirichletClosedHalfBox a b))
    (hQ : ContinuousOn Q (smoothDirichletClosedHalfBox a b))
    (hd : ∀ x ∈ Ioo (-a) a, ∀ y ∈ Ioo 0 b,
      HasDerivAt (fun s  => U (rectangularComplexCoord (s, y)))
        (Q (rectangularComplexCoord (x, y))) x)
    {s t : ℝ} (hs : s ∈ Ioo (-a) a) (ht : t ∈ Ioo (-a) a) :
    (∫ x in s..t, Q x) = U t - U s := by
  by_cases hst : s ≤ t
  · exact dirichlet_boundary_horizontal_ftc_of_le hb hU hQ hd hs ht hst
  · rw [intervalIntegral.integral_symm,
      dirichlet_boundary_horizontal_ftc_of_le hb hU hQ hd ht hs (le_of_not_ge hst), neg_sub]

/-- A genuine clamped coordinate makes the continuous bottom derivative
globally continuous, so ordinary FTC-1 can be used without any regularity
assumption outside the actual rectangle. -/
def dirichletBoundaryClamp (a x : ℝ) : ℝ := max (-a) (min a x)

theorem dirichletBoundaryClamp_mem {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    dirichletBoundaryClamp a x ∈ Icc (-a) a :=
  ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem dirichletBoundaryClamp_eq {a x : ℝ} (hx : x ∈ Icc (-a) a) :
    dirichletBoundaryClamp a x = x := by
  simp [dirichletBoundaryClamp, min_eq_right hx.2, max_eq_right hx.1]

theorem continuous_dirichletBoundaryClamp (a : ℝ) : Continuous (dirichletBoundaryClamp a) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem continuous_dirichlet_clamped_boundary (ha : 0 ≤ a) (hb : 0 ≤ b)
    {Q : ℂ → ℂ} (hQ : ContinuousOn Q (smoothDirichletClosedHalfBox a b)) :
    Continuous (fun x  => Q (dirichletBoundaryClamp a x)) := by
  apply continuousOn_univ.mp
  apply hQ.comp (Complex.continuous_ofReal.comp (continuous_dirichletBoundaryClamp a)).continuousOn
  intro x _
  simpa only [rectangularComplexCoord, Complex.ofReal_zero, zero_mul, add_zero,
    Function.comp_apply] using
    dirichlet_closed_halfBox_horizontal_mem (dirichletBoundaryClamp_mem ha x)
      (⟨le_rfl, hb⟩)

/-- Boundary differentiation is a conclusion of actual interior
derivatives plus the proved bottom FTC. -/
theorem dirichlet_boundary_horizontal_hasDerivAt (ha : 0 < a) (hb : 0 < b)
    {U Q : ℂ → ℂ}
    (hU : ContinuousOn U (smoothDirichletClosedHalfBox a b))
    (hQ : ContinuousOn Q (smoothDirichletClosedHalfBox a b))
    (hd : ∀ x ∈ Ioo (-a) a, ∀ y ∈ Ioo 0 b,
      HasDerivAt (fun s  => U (rectangularComplexCoord (s, y)))
        (Q (rectangularComplexCoord (x, y))) x)
    {x : ℝ} (hx : x ∈ Ioo (-a) a) :
    HasDerivAt (fun s : ℝ => U s) (Q x) x := by
  let q  := fun s => Q (dirichletBoundaryClamp a s)
  have hqc : Continuous q := continuous_dirichlet_clamped_boundary ha.le hb.le hQ
  have hP  :=
    (intervalIntegral.integral_hasDerivAt_right (hqc.intervalIntegrable 0 x)
      hqc.aestronglyMeasurable.stronglyMeasurableAtFilter hqc.continuousAt).const_add (U 0)
  have hxq : q x = Q x := by
    simp [q, dirichletBoundaryClamp_eq ⟨hx.1.le, hx.2.le⟩]
  rw [hxq] at hP
  exact hP.congr_of_eventuallyEq (by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with s hs
    have hi : (∫ t in 0..s, q t) = ∫ t in 0..s, Q t :=
      intervalIntegral.integral_congr (fun t ht => by
        simp [q, dirichletBoundaryClamp_eq (uIcc_subset_Icc (⟨by linarith, ha.le⟩)         ⟨hs.1.le, hs.2.le⟩ ht)])
    have hftc := dirichlet_boundary_horizontal_ftc hb hU hQ hd
      (⟨by linarith, ha⟩) hs
    simp_all)

/-- Continuous representatives of the actual interior function and its
horizontal derivative inherit the actual positive-height derivatives.
Their bottom derivative is then supplied by the proved limiting FTC. -/
theorem dirichlet_boundary_extension_hasDerivAt (ha : 0 < a) (hb : 0 < b)
    {u U Q : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox a b))
    (hU : ContinuousOn U (smoothDirichletClosedHalfBox a b))
    (hUu : EqOn U u (smoothDirichletHalfBox a b))
    (hQ : ContinuousOn Q (smoothDirichletClosedHalfBox a b))
    (hQu : EqOn Q (dirD u 1) (smoothDirichletHalfBox a b))
    {x : ℝ} (hx : x ∈ Ioo (-a) a) :
    HasDerivAt (fun s : ℝ => U s) (Q x) x := by
  apply dirichlet_boundary_horizontal_hasDerivAt ha hb hU hQ _ hx
  intro t ht y hy
  rw [hQu (rectangularComplexCoord_mem_halfBox
    (⟨ht, hy⟩))]
  exact (rectangular_halfBox_horizontal_hasDerivAt hs ht hy).congr_of_eventuallyEq (by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs'
    exact hUu (rectangularComplexCoord_mem_halfBox
      (⟨hs', hy⟩)))

theorem continuousOn_dirichlet_boundary_restriction (hb : 0 ≤ b)
    {U : ℂ → ℂ} (hU : ContinuousOn U (smoothDirichletClosedHalfBox a b)) :
    ContinuousOn (fun x : ℝ => U x) (Ioo (-a) a) := by
  apply hU.comp Complex.continuous_ofReal.continuousOn
  intro x hx
  simpa only [rectangularComplexCoord, Complex.ofReal_zero, zero_mul, add_zero] using
    dirichlet_closed_halfBox_horizontal_mem ⟨hx.1.le, hx.2.le⟩
      (⟨le_rfl, hb⟩)

/-- The bottom zero value really forces the bottom horizontal
derivative to vanish. It is derived from the actual limiting FTC,
rather than used as a boundary condition on the derivative. -/
theorem dirichlet_zero_boundary_horizontal_extension (ha : 0 < a) (hb : 0 < b) {u Q : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox a b))
    (hc : ContinuousOn u (smoothDirichletClosedHalfBox a b))
    (hz : ∀ x ∈ Ioo (-a) a, u x = 0)
    (hQ : ContinuousOn Q (smoothDirichletClosedHalfBox a b))
    (hQu : EqOn Q (dirD u 1) (smoothDirichletHalfBox a b))
    {x : ℝ} (hx : x ∈ Ioo (-a) a) : Q x = 0 := (dirichlet_boundary_extension_hasDerivAt ha hb hs hc
    (fun _ _ => rfl) hQ hQu hx).unique ((hasDerivAt_const x 0).congr_of_eventuallyEq (by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with s hs'
    simp_all))

/-- The finite chain uses actual `HasDerivAt` identities. In particular
successive continuous fields are not silently declared to be jets. -/
theorem dirichlet_boundary_derivative_chain_contDiffOn {s : Set ℝ} (hs : IsOpen s)
    (n : ℕ) (v : ℕ → ℝ → ℂ)
    (hc : ∀ j ≤ n, ContinuousOn (v j) s)
    (hd : ∀ j < n, ∀ x ∈ s, HasDerivAt (v j) (v (j + 1) x) x) :
    ContDiffOn ℝ n (v 0) s := by
  induction n generalizing v with
  | zero => simp_all
  | succ n ih =>
      have hsucc : ContDiffOn ℝ (n + 1) (v 0) s := by
        apply (contDiffOn_succ_iff_deriv_of_isOpen hs).mpr
        refine ⟨fun x hx => (hd 0 (by omega) x hx).differentiableAt.differentiableWithinAt,
          ?_, (ih (fun j => v (j + 1))
          (fun j hj => hc (j + 1) (by omega))
          (fun j hj x hx => hd (j + 1) (by omega) x hx)).congr fun x hx => (hd 0 (by omega) x hx).deriv⟩
        norm_num
      assumption

/-- Each actual mixed field has a continuous closed-rectangle
representative once the true finite mixed L² cone contains its two
first derivatives and its mixed derivative. -/
theorem dirichlet_mixed_exists_continuous_extension (ha : 0 < a) (hb : 0 < b) {u : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox a b)) (N p q : ℕ)
    (hm : ∀ j k : ℕ, j + k ≤ N → MemLp (dirichletMixedDerivative j k u) 2
      (volume.restrict (smoothDirichletHalfBox a b)))
    (horder : p + q + 2 ≤ N) :
    ∃ U : ℂ → ℂ, ContinuousOn U (smoothDirichletClosedHalfBox a b) ∧
      EqOn U (dirichletMixedDerivative p q u) (smoothDirichletHalfBox a b) := by
  have hW := isOpen_smoothDirichletHalfBox a b
  have hy (j k : ℕ) (hjk : j + k + 1 ≤ N) :
      MemLp (dirD (dirichletMixedDerivative j k u) Complex.I) 2
        (volume.restrict (smoothDirichletHalfBox a b)) := by
    apply (hm j (k + 1) (by omega)).ae_eq
    filter_upwards [ae_restrict_mem hW.measurableSet] with z hz
    exact (dirD_dirichletMixedDerivative_I_eqOn hW hs j k hz).symm
  obtain ⟨U, hUc, hUu, _⟩ := dirichlet_halfBox_exists_continuous_extension ha hb
    (dirichletMixedDerivative_contDiffOn hW hs p q)
    (hm p q (by omega)) (hm (p + 1) q (by omega)) (hy p q (by omega)) (hy (p + 1) q (by omega))
  grind

/-- Actual finite mixed energy yields a genuine finite boundary jet
chain, and hence finite boundary smoothness of the chosen representative.
There are no prescribed derivative values on the bottom. -/
theorem dirichlet_mixed_exists_boundary_contDiffOn (ha : 0 < a) (hb : 0 < b) {u : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox a b)) (N p q n : ℕ)
    (hm : ∀ j k : ℕ, j + k ≤ N → MemLp (dirichletMixedDerivative j k u) 2
      (volume.restrict (smoothDirichletHalfBox a b)))
    (horder : p + q + n + 2 ≤ N) :
    ∃ V : ℕ → ℂ → ℂ,
      (∀ j ≤ n, ContinuousOn (V j) (smoothDirichletClosedHalfBox a b) ∧
        EqOn (V j) (dirichletMixedDerivative (p + j) q u) (smoothDirichletHalfBox a b)) ∧
      (∀ j < n, ∀ x ∈ Ioo (-a) a,
        HasDerivAt (fun s : ℝ => V j s) (V (j + 1) x) x) ∧
      ContDiffOn ℝ n (fun x : ℝ => V 0 x) (Ioo (-a) a) := by
  have hex : ∀ j : ℕ, ∃ U : ℂ → ℂ, j ≤ n →
      ContinuousOn U (smoothDirichletClosedHalfBox a b) ∧
        EqOn U (dirichletMixedDerivative (p + j) q u) (smoothDirichletHalfBox a b) := by
    intro j
    by_cases hj : j ≤ n
    · obtain ⟨U, hUc, hUu⟩ := dirichlet_mixed_exists_continuous_extension
        ha hb hs N (p + j) q hm (by omega)
      grind
    simp_all
  choose V hV using hex
  have hd : ∀ j < n, ∀ x ∈ Ioo (-a) a,
      HasDerivAt (fun s : ℝ => V j s) (V (j + 1) x) x := by
    intro j hj x hx
    exact dirichlet_boundary_extension_hasDerivAt ha hb
      (dirichletMixedDerivative_contDiffOn (isOpen_smoothDirichletHalfBox a b) hs (p + j) q)
      (hV j (by omega)).1 (hV j (by omega)).2
      (hV (j + 1) (by omega)).1 (by
      rw [dirD_dirichletMixedDerivative_one]
      grind) hx
  refine ⟨V, hV, hd, ?_⟩
  exact dirichlet_boundary_derivative_chain_contDiffOn isOpen_Ioo n
    (fun j x => V j x)
    (fun j hj => continuousOn_dirichlet_boundary_restriction hb.le (hV j hj).1) hd

/-- The boundary values of two continuous representatives of the same
actual interior function agree wherever their bottom intervals overlap.
This is what permits the genuine energy rectangle to depend on the order. -/
theorem dirichlet_boundary_extensions_eq {a b A B : ℝ} (hb : 0 < b) (hB : 0 < B)
    {u U V : ℂ → ℂ}
    (hU : ContinuousOn U (smoothDirichletClosedHalfBox a b))
    (hUu : EqOn U u (smoothDirichletHalfBox a b))
    (hV : ContinuousOn V (smoothDirichletClosedHalfBox A B))
    (hVu : EqOn V u (smoothDirichletHalfBox A B))
    {x : ℝ} (hx : x ∈ Ioo (-a) a) (hxA : x ∈ Ioo (-A) A) :
    U x = V x := tendsto_nhds_unique_of_eventuallyEq (dirichlet_closed_halfBox_vertical_limit hb hU (abs_lt.mpr hx).le) (dirichlet_closed_halfBox_vertical_limit hB hV (abs_lt.mpr hxA).le) (by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds,
      (eventually_lt_nhds hB).filter_mono nhdsWithin_le_nhds] with y hy hyb hyB
    simp [hUu (rectangularComplexCoord_mem_halfBox       (show (x, y) ∈ Ioo (-a) a ×ˢ Ioo 0 b from ⟨hx, hy, hyb⟩)), hVu (rectangularComplexCoord_mem_halfBox         (show (x, y) ∈ Ioo (-A) A ×ˢ Ioo 0 B from ⟨hxA, hy, hyB⟩))])

/-- Finite mixed-energy cones on successively smaller actual rectangles
give smoothness at the center of one fixed continuous representative.
The proof explicitly compares every new representative with the first;
it never asserts that all derivative orders share one energy rectangle. -/
theorem dirichlet_mixed_boundary_contDiffAt_of_finite_energy {A b a β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) {u U : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A b))
    (p q : ℕ)
    (hhigh : ∀ N : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ρ < A / 2 ∧ ρ < b ∧
      ∀ j k : ℕ, j + k ≤ N → MemLp (dirichletMixedDerivative j k u) 2
        (volume.restrict (smoothDirichletHalfBox ρ ρ)))
    (hU : ContinuousOn U (smoothDirichletClosedHalfBox a β))
    (hUu : EqOn U (dirichletMixedDerivative p q u) (smoothDirichletHalfBox a β)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => U x) 0 := by
  apply contDiffAt_infty.mpr
  intro n
  obtain ⟨ρ, hρ, hρA, hρb, hm⟩ := hhigh (p + q + n + 2)
  obtain ⟨V, hV, _, hVc⟩ := dirichlet_mixed_exists_boundary_contDiffOn
    hρ hρ (hs.mono (by
    intro z hz
    exact ⟨hz.1.trans (by linarith), hz.2.1, hz.2.2.trans hρb⟩)) (p + q + n + 2) p q n hm (le_refl _)
  exact (hVc.contDiffAt (isOpen_Ioo.mem_nhds
    (⟨by linarith, hρ⟩))).congr_of_eventuallyEq (by
    filter_upwards [isOpen_Ioo.mem_nhds
      (show 0 ∈ Ioo (-a) a from ⟨by linarith, ha⟩),
      isOpen_Ioo.mem_nhds (show 0 ∈ Ioo (-ρ) ρ from ⟨by linarith, hρ⟩)]
      with x hx hxρ
    exact dirichlet_boundary_extensions_eq hβ hρ hU hUu
      (hV 0 (by omega)).1 (by
    grind) hx hxρ)

/-- Both first derivatives can be represented on the same real
rectangle. Their all-order bottom smoothness is still obtained from
order-dependent smaller energy rectangles, rather than from a fixed
rectangle carrying an assumed all-order estimate. -/
theorem exists_dirichlet_gradient_smooth_boundary_fields {A b : ℝ}
    {u : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A b))
    (hhigh : ∀ N : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ρ < A / 2 ∧ ρ < b ∧
      ∀ j k : ℕ, j + k ≤ N → MemLp (dirichletMixedDerivative j k u) 2
        (volume.restrict (smoothDirichletHalfBox ρ ρ))) :
    ∃ (ρ : ℝ) (X Y : ℂ → ℂ), 0 < ρ ∧ ρ < A / 2 ∧ ρ < b ∧
      ContinuousOn X (smoothDirichletClosedHalfBox ρ ρ) ∧
      ContinuousOn Y (smoothDirichletClosedHalfBox ρ ρ) ∧
      EqOn X (dirD u 1) (smoothDirichletHalfBox ρ ρ) ∧
      EqOn Y (dirD u Complex.I) (smoothDirichletHalfBox ρ ρ) ∧
      ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => X x) 0 ∧
      ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => Y x) 0 := by
  obtain ⟨ρ, hρ, hρA, hρb, hm⟩ := hhigh 3
  have hWU : smoothDirichletHalfBox ρ ρ ⊆ smoothDirichletHalfBox A b := by
    intro z hz
    exact ⟨hz.1.trans (by linarith), hz.2.1, hz.2.2.trans hρb⟩
  obtain ⟨X, hXc, hXu⟩ := dirichlet_mixed_exists_continuous_extension
    hρ hρ (hs.mono hWU) 3 1 0 hm (by omega)
  obtain ⟨Y, hYc, hYu⟩ := dirichlet_mixed_exists_continuous_extension
    hρ hρ (hs.mono hWU) 3 0 1 hm (by omega)
  exact ⟨ρ, X, Y, hρ, hρA, hρb, hXc, hYc, hXu, hYu, dirichlet_mixed_boundary_contDiffAt_of_finite_energy
    hρ hρ hs 1 0 hhigh hXc hXu, dirichlet_mixed_boundary_contDiffAt_of_finite_energy
    hρ hρ hs 0 1 hhigh hYc hYu⟩

/-- The actual domain correspondence of the chosen smooth graph is
retained along with the constructed smooth boundary-gradient pair.
Thus downstream boundary inverse-map arguments can prove frontier
membership from the same genuine chart, without changing witnesses. -/
theorem exists_riemannMapping_genuine_gradient_smooth_boundary_fields {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) (himage : F '' ball 0 1 = Ω)
    {p : ℂ} (hp : p ∈ frontier Ω) :
    ∃ (d : smoothTraceTests) (c : ℂ) (hc : c ≠ 0)
      (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (K : NNReal) (A b ρ : ℝ)
      (X Y : ℂ → ℂ),
      ‖c‖ = 1 ∧ LipschitzWith K f ∧ f 0 = 0 ∧ 0 < A ∧ 0 < b ∧
      0 < ρ ∧ ρ < A / 2 ∧ ρ < b ∧
      (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
       let u := riemannMappingDirichletRemainder F d ∘ Ψ
       let U := smoothDirichletHalfBox A b
       (∀ z : ℂ, |z.re| < A → |z.im| < b → (Ψ z ∈ Ω ↔ 0 < z.im)) ∧
       MapsTo Ψ (smoothDirichletClosedHalfBox A b) (closure Ω) ∧
       MapsTo Ψ U Ω ∧ ContinuousOn u (smoothDirichletClosedHalfBox A b) ∧
       ContDiffOn ℝ (⊤ : ℕ∞) u U ∧
       (∀ x : ℝ, |x| < A → u x = 0) ∧
       ContinuousOn X (smoothDirichletClosedHalfBox ρ ρ) ∧
       ContinuousOn Y (smoothDirichletClosedHalfBox ρ ρ) ∧
       EqOn X (dirD u 1) (smoothDirichletHalfBox ρ ρ) ∧
       EqOn Y (dirD u Complex.I) (smoothDirichletHalfBox ρ ρ) ∧
       ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => X x) 0 ∧
       ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => Y x) 0) := by
  obtain ⟨d, c, hc, f, hf, K, A, b, hc₁, hLip, hf₀, hA, hb₀,
    hchart, hclosed, hmap, hu, hs, hz, _, _, hhigh⟩ :=
    exists_riemannMapping_flattened_genuine_chart_all_mixed_orders
      hb hS hsc F hF hinj himage hp
  obtain ⟨ρ, X, Y, hρ, hρA, hρb, hXc, hYc, hXu, hYu, hXs, hYs⟩ :=
    exists_dirichlet_gradient_smooth_boundary_fields hs hhigh
  exact ⟨d, c, hc, f, hf, K, A, b, ρ, X, Y, hc₁, hLip, hf₀, hA, hb₀,
    hρ, hρA, hρb, hchart, hclosed, hmap, hu, hs, hz, hXc, hYc, hXu, hYu, hXs, hYs⟩

end PolyaNeumann

end
