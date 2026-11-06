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


noncomputable section

namespace PolyaNeumann

open Set Metric Filter Complex MeasureTheory
open scoped Topology ContDiff

variable {a b : ℝ} {x : ℝ} {U Q : ℂ → ℂ}

theorem dirichlet_closed_halfBox_horizontal_mem 
    (hx : x ∈ Icc (-a) a) (hy : y ∈ Icc 0 b) :
    rectangularComplexCoord (x, y) ∈ smoothDirichletClosedHalfBox a b := by
  simpa [rectangularComplexCoord, smoothDirichletClosedHalfBox, mem_setOf_eq] using
    ⟨abs_le.mpr hx, hy⟩

/-- The actual full-approach continuous limit along vertical points.
This uses continuity of the constructed representative on the closed
rectangle, rather than asserting a trace limit. -/
local notation "Φ0" => smoothDirichletClosedHalfBox a b

theorem dirichlet_closed_halfBox_vertical_limit  (hb : 0 < b)
    {U : ℂ → ℂ} (hU : ContinuousOn U (Φ0))
     (hx : |x| ≤ a) :
    Tendsto (fun y => U (rectangularComplexCoord (x, y))) (𝓝[>] 0)
      (𝓝 (U (x : ℂ))) := by
  exact (hU.continuousWithinAt (by
    simpa [rectangularComplexCoord] using
      dirichlet_closed_halfBox_horizontal_mem (abs_le.mp hx)
        (⟨le_rfl, hb.le⟩))).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨(by
      have hc : Continuous (fun y => rectangularComplexCoord (x, y)) :=
        continuous_rectangularComplexCoord.comp
          ((continuous_const : Continuous (fun _ => x)).prodMk continuous_id)
      simpa [rectangularComplexCoord] using
        (hc.tendsto 0).mono_left nhdsWithin_le_nhds), (by
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with y hy hyb
      exact dirichlet_closed_halfBox_horizontal_mem (abs_le.mp hx) ⟨hy.le, hyb.le⟩)⟩)

/-- Actual horizontal FTC at the bottom, first in the increasing
orientation. The integral limit is justified by a genuine compact bound
for the continuous derivative representative. -/
theorem dirichlet_boundary_horizontal_ftc_of_le  (hb : 0 < b)
    
    (hU : ContinuousOn U (Φ0))
    (hQ : ContinuousOn Q (Φ0))
    (hd : ∀ x ∈ Ioo (-a) a, ∀ y ∈ Ioo 0 b,
      HasDerivAt (fun s => U (rectangularComplexCoord (s, y)))
        (Q (rectangularComplexCoord (x, y))) x)
    {s t : ℝ} (hs : s ∈ Ioo (-a) a) (ht : t ∈ Ioo (-a) a) (hst : s ≤ t) :
    (∫ x in s..t, Q (x : ℂ)) = U (t : ℂ) - U (s : ℂ) := by
  have hI : Icc s t ⊆ Ioo (-a) a := fun x hx =>
    ⟨hs.1.trans_le hx.1, hx.2.trans_lt ht.2⟩
  have hrow (V : ℂ → ℂ) (hV : ContinuousOn V (Φ0))
      (y : ℝ) (hy : y ∈ Icc (0 : ℝ) b) :
      ContinuousOn (fun x => V (rectangularComplexCoord (x, y))) (Icc s t) := by
    apply hV.comp (continuous_rectangularComplexCoord.comp (continuous_id.prodMk (continuous_const : Continuous (fun _ => y)))).continuousOn
    intro x hx
    exact dirichlet_closed_halfBox_horizontal_mem
      ⟨(hI hx).1.le, (hI hx).2.le⟩ hy
  obtain ⟨B, hB⟩ := (isCompact_smoothDirichletClosedHalfBox a b).exists_bound_of_continuousOn
    hQ
  exact tendsto_nhds_unique_of_eventuallyEq (show Tendsto (fun y => ∫ x in s..t, Q (rectangularComplexCoord (x, y))) (𝓝[>] 0) (𝓝 (∫ x in s..t, Q x)) by
    simpa [intervalIntegral.integral_of_le hst] using
      (tendsto_integral_filter_of_dominated_convergence (fun _ => B)
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
            (abs_le.mpr ⟨(hI ⟨hx.1.le, hx.2⟩).1.le, (hI ⟨hx.1.le, hx.2⟩).2.le⟩)))) ((dirichlet_closed_halfBox_vertical_limit hb hU (abs_lt.mpr ht).le).sub (dirichlet_closed_halfBox_vertical_limit hb hU (abs_lt.mpr hs).le)) (by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with y hy hyb
    have hyy : y ∈ Icc 0 b := ⟨hy.le, hyb.le⟩
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst (hrow U hU y hyy)
      (fun x hx => hd x (hI ⟨hx.1.le, hx.2.le⟩) y ⟨hy, hyb⟩)
      ((hrow Q hQ y hyy).intervalIntegrable_of_Icc hst))

/-- The bottom FTC retains the true oriented interval integral. -/
theorem dirichlet_boundary_horizontal_ftc  (hb : 0 < b)
    
    (hU : ContinuousOn U (Φ0))
    (hQ : ContinuousOn Q (Φ0))
    (hd : ∀ x ∈ Ioo (-a) a, ∀ y ∈ Ioo 0 b,
      HasDerivAt (fun s => U (rectangularComplexCoord (s, y)))
        (Q (rectangularComplexCoord (x, y))) x)
    {s t : ℝ} (hs : s ∈ Ioo (-a) a) (ht : t ∈ Ioo (-a) a) :
    (∫ x in s..t, Q (x : ℂ)) = U (t : ℂ) - U (s : ℂ) := by
  by_cases hst : s ≤ t
  · exact dirichlet_boundary_horizontal_ftc_of_le hb hU hQ hd hs ht hst
  · rw [intervalIntegral.integral_symm,
      dirichlet_boundary_horizontal_ftc_of_le hb hU hQ hd ht hs (le_of_not_ge hst), neg_sub]

/-- A genuine clamped coordinate makes the continuous bottom derivative
globally continuous, so ordinary FTC-1 can be used without any regularity
assumption outside the actual rectangle. -/
def dirichletBoundaryClamp (a x : ℝ) : ℝ := max (-a) (min a x)

theorem dirichletBoundaryClamp_eq  (hx : x ∈ Icc (-a) a) :
    dirichletBoundaryClamp a x = x := by
  simp [dirichletBoundaryClamp, min_eq_right hx.2, max_eq_right hx.1]

theorem continuous_dirichletBoundaryClamp a : Continuous (dirichletBoundaryClamp a) :=
  continuous_const.max (continuous_const.min continuous_id)

/-- Boundary differentiation is a conclusion of actual interior
derivatives plus the proved bottom FTC. -/
theorem dirichlet_boundary_horizontal_hasDerivAt  (ha : 0 < a) (hb : 0 < b)
    
    (hU : ContinuousOn U (Φ0))
    (hQ : ContinuousOn Q (Φ0))
    (hd : ∀ x ∈ Ioo (-a) a, ∀ y ∈ Ioo 0 b,
      HasDerivAt (fun s => U (rectangularComplexCoord (s, y)))
        (Q (rectangularComplexCoord (x, y))) x)
     (hx : x ∈ Ioo (-a) a) :
    HasDerivAt (fun s : ℝ => U (s : ℂ)) (Q (x : ℂ)) x := by
  let q : ℝ → ℂ := fun s => Q (dirichletBoundaryClamp a s : ℝ)
  have hqc : Continuous (fun x => Q (dirichletBoundaryClamp a x : ℝ)) := by
    apply continuousOn_univ.mp
    apply hQ.comp (Complex.continuous_ofReal.comp (continuous_dirichletBoundaryClamp a)).continuousOn
    intro x _
    simpa [rectangularComplexCoord] using
      dirichlet_closed_halfBox_horizontal_mem (⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩ : dirichletBoundaryClamp a x ∈ Icc (-a) a)
        (⟨le_rfl, hb.le⟩)
  let P : ℝ → ℂ := fun s => U 0 + ∫ t in 0..s, q t
  have hP : HasDerivAt P (q x) x :=
    (intervalIntegral.integral_hasDerivAt_right (hqc.intervalIntegrable 0 x)
      hqc.aestronglyMeasurable.stronglyMeasurableAtFilter hqc.continuousAt).const_add (U 0)
  rw [show q x = Q x by
    dsimp only [q]
    rw [dirichletBoundaryClamp_eq ⟨hx.1.le, hx.2.le⟩]] at hP
  exact hP.congr_of_eventuallyEq (by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with s hs
    have hi : (∫ t in 0..s, q t) = ∫ t in 0..s, Q t :=
      intervalIntegral.integral_congr (fun t ht => by
        dsimp only [q]
        rw [dirichletBoundaryClamp_eq ((uIcc_subset_Icc (⟨by linarith, ha.le⟩) ⟨hs.1.le, hs.2.le⟩) ht)])
    dsimp only [P]
    rw [hi, dirichlet_boundary_horizontal_ftc hb hU hQ hd (⟨by linarith, ha⟩) hs]
    simp only [Complex.ofReal_zero]
    abel)

/-- Continuous representatives of the actual interior function and its
horizontal derivative inherit the actual positive-height derivatives.
Their bottom derivative is then supplied by the proved limiting FTC. -/
local notation "Φ1" => smoothDirichletHalfBox a b

theorem dirichlet_boundary_extension_hasDerivAt  (ha : 0 < a) (hb : 0 < b)
    
    (hs : ContDiffOn ℝ ∞ u (Φ1))
    (hU : ContinuousOn U (Φ0))
    (hUu : EqOn U u (Φ1))
    (hQ : ContinuousOn Q (Φ0))
    (hQu : EqOn Q (dirD u 1) (Φ1))
     (hx : x ∈ Ioo (-a) a) :
    HasDerivAt (fun s : ℝ => U (s : ℂ)) (Q (x : ℂ)) x := by
  apply dirichlet_boundary_horizontal_hasDerivAt ha hb hU hQ _ hx
  intro t ht y hy
  rw [hQu (rectangularComplexCoord_mem_halfBox
    (⟨ht, hy⟩))]
  exact (rectangular_halfBox_horizontal_hasDerivAt hs ht hy).congr_of_eventuallyEq (by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs'
    exact hUu (rectangularComplexCoord_mem_halfBox
      (⟨hs', hy⟩)))

theorem continuousOn_dirichlet_boundary_restriction  (hb : 0 ≤ b)
    {U : ℂ → ℂ} (hU : ContinuousOn U (Φ0)) :
    ContinuousOn (fun x : ℝ => U (x : ℂ)) (Ioo (-a) a) := by
  apply hU.comp Complex.continuous_ofReal.continuousOn
  intro x hx
  simpa [rectangularComplexCoord] using
    dirichlet_closed_halfBox_horizontal_mem ⟨hx.1.le, hx.2.le⟩
      (⟨le_rfl, hb⟩)

/-- The bottom zero value really forces the bottom horizontal
derivative to vanish. It is derived from the actual limiting FTC,
rather than used as a boundary condition on the derivative. -/
theorem dirichlet_zero_boundary_horizontal_extension 
    (ha : 0 < a) (hb : 0 < b) 
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (Φ1))
    (hc : ContinuousOn u (Φ0))
    (hz : ∀ x ∈ Ioo (-a) a, u x = 0)
    (hQ : ContinuousOn Q (Φ0))
    (hQu : EqOn Q (dirD u 1) (Φ1))
     (hx : x ∈ Ioo (-a) a) : Q (x : ℂ) = 0 := by
  exact (dirichlet_boundary_extension_hasDerivAt ha hb hs hc (fun _ _ => rfl) hQ hQu hx).unique ((hasDerivAt_const x 0).congr_of_eventuallyEq (by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with s hs'
    exact hz s hs'))

/-- The finite chain uses actual `HasDerivAt` identities. In particular
successive continuous fields are not silently declared to be jets. -/
theorem dirichlet_boundary_derivative_chain_contDiffOn  (hs : IsOpen s)
    (n : ℕ) (v : ℕ → ℝ → ℂ)
    (hc : ∀ j ≤ n, ContinuousOn (v j) s)
    (hd : ∀ j < n, ∀ x ∈ s, HasDerivAt (v j) (v (j + 1) x) x) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (v 0) s := by
  induction n generalizing v with
  | zero => exact contDiffOn_zero.mpr (hc 0 (by omega))
  | succ n ih =>
      simpa [Nat.cast_succ] using show ContDiffOn ℝ (n + 1) (v 0) s by
        apply (contDiffOn_succ_iff_deriv_of_isOpen hs).mpr
        refine ⟨fun x hx => (hd 0 (by omega) x hx).differentiableAt.differentiableWithinAt,
          ?_, (show ContDiffOn ℝ n (v 1) s by
            exact ih (fun j => v (j + 1))
              (fun j hj => hc (j + 1) (by omega))
              (fun j hj x hx => hd (j + 1) (by omega) x hx)).congr (fun x hx => (hd 0 (by omega) x hx).deriv)⟩
        intro hn
        simp at hn

/-- Each actual mixed field has a continuous closed-rectangle
representative once the true finite mixed L² cone contains its two
first derivatives and its mixed derivative. -/
theorem dirichlet_mixed_exists_continuous_extension 
    (ha : 0 < a) (hb : 0 < b) 
    (hs : ContDiffOn ℝ ∞ u (Φ1)) N p q
    (hm : ∀ j k : ℕ, j + k ≤ N → MemLp (dirichletMixedDerivative j k u) 2
      (volume.restrict (Φ1)))
    (horder : p + q + 2 ≤ N) :
    ∃ U : ℂ → ℂ, ContinuousOn U (Φ0) ∧
      EqOn U (dirichletMixedDerivative p q u) (Φ1) := by
  have hW := isOpen_smoothDirichletHalfBox a b
  have hy (j k : ℕ) (hjk : j + k + 1 ≤ N) :
      MemLp (dirD (dirichletMixedDerivative j k u) Complex.I) 2
        (volume.restrict (Φ1)) := by
    apply (hm j (k + 1) (by omega)).ae_eq
    filter_upwards [ae_restrict_mem hW.measurableSet] with z hz
    exact (dirD_dirichletMixedDerivative_I_eqOn hW hs j k hz).symm
  obtain ⟨U, hUc, hUu, _⟩ := dirichlet_halfBox_exists_continuous_extension ha hb
    (dirichletMixedDerivative_contDiffOn hW hs p q)
    (hm p q (by omega)) (by
      rw [dirD_dirichletMixedDerivative_one]
      exact hm (p + 1) q (by omega)) (hy p q (by omega)) (by
      rw [dirD_dirichletMixedDerivative_one]
      exact hy (p + 1) q (by omega))
  exact ⟨U, hUc, hUu⟩

/-- Actual finite mixed energy yields a genuine finite boundary jet
chain, and hence finite boundary smoothness of the chosen representative.
There are no prescribed derivative values on the bottom. -/
theorem dirichlet_mixed_exists_boundary_contDiffOn 
    (ha : 0 < a) (hb : 0 < b) 
    (hs : ContDiffOn ℝ ∞ u (Φ1)) (N p q n : ℕ)
    (hm : ∀ j k : ℕ, j + k ≤ N → MemLp (dirichletMixedDerivative j k u) 2
      (volume.restrict (Φ1)))
    (horder : p + q + n + 2 ≤ N) :
    ∃ V : ℕ → ℂ → ℂ,
      (∀ j ≤ n, ContinuousOn (V j) (Φ0) ∧
        EqOn (V j) (dirichletMixedDerivative (p + j) q u) (Φ1)) ∧
      (∀ j < n, ∀ x ∈ Ioo (-a) a,
        HasDerivAt (fun s : ℝ => V j (s : ℂ)) (V (j + 1) (x : ℂ)) x) ∧
      ContDiffOn ℝ (n : WithTop ℕ∞) (fun x : ℝ => V 0 (x : ℂ)) (Ioo (-a) a) := by
  have hex : ∀ j : ℕ, ∃ U : ℂ → ℂ, j ≤ n →
      ContinuousOn U (Φ0) ∧
        EqOn U (dirichletMixedDerivative (p + j) q u) (Φ1) := by
    intro j
    by_cases hj : j ≤ n
    · obtain ⟨U, hUc, hUu⟩ := dirichlet_mixed_exists_continuous_extension
        ha hb hs N (p + j) q hm (by omega)
      exact ⟨U, fun _ => ⟨hUc, hUu⟩⟩
    · exact ⟨0, fun hj' => False.elim (hj hj')⟩
  choose V hV using hex
  have hd : ∀ j < n, ∀ x ∈ Ioo (-a) a,
      HasDerivAt (fun s : ℝ => V j (s : ℂ)) (V (j + 1) (x : ℂ)) x := by
    intro j hj x hx
    exact dirichlet_boundary_extension_hasDerivAt ha hb
      (dirichletMixedDerivative_contDiffOn (isOpen_smoothDirichletHalfBox a b) hs (p + j) q)
      (hV j (by omega)).1 (hV j (by omega)).2
      (hV (j + 1) (by omega)).1 (by
        rw [dirD_dirichletMixedDerivative_one]
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (hV (j + 1) (by omega)).2) hx
  refine ⟨V, hV, hd, ?_⟩
  exact dirichlet_boundary_derivative_chain_contDiffOn isOpen_Ioo n
    (fun j x => V j (x : ℂ))
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
     (hx : x ∈ Ioo (-a) a) (hxA : x ∈ Ioo (-A) A) :
    U (x : ℂ) = V (x : ℂ) := by
  exact tendsto_nhds_unique_of_eventuallyEq (dirichlet_closed_halfBox_vertical_limit hb hU (abs_lt.mpr hx).le) (dirichlet_closed_halfBox_vertical_limit hB hV (abs_lt.mpr hxA).le) (by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds,
      (eventually_lt_nhds hB).filter_mono nhdsWithin_le_nhds] with y hy hyb hyB
    rw [hUu (rectangularComplexCoord_mem_halfBox
      (show (x, y) ∈ Ioo (-a) a ×ˢ Ioo 0 b from ⟨hx, hy, hyb⟩)),
      hVu (rectangularComplexCoord_mem_halfBox
        (show (x, y) ∈ Ioo (-A) A ×ˢ Ioo 0 B from ⟨hxA, hy, hyB⟩))])

/-- Finite mixed-energy cones on successively smaller actual rectangles
give smoothness at the center of one fixed continuous representative.
The proof explicitly compares every new representative with the first;
it never asserts that all derivative orders share one energy rectangle. -/
theorem dirichlet_mixed_boundary_contDiffAt_of_finite_energy {A b a β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) 
    (hs : ContDiffOn ℝ ∞ u (smoothDirichletHalfBox A b))
    (p q : ℕ)
    (hhigh : ∀ N : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ρ < A / 2 ∧ ρ < b ∧
      ∀ j k : ℕ, j + k ≤ N → MemLp (dirichletMixedDerivative j k u) 2
        (volume.restrict (smoothDirichletHalfBox ρ ρ)))
    (hU : ContinuousOn U (smoothDirichletClosedHalfBox a β))
    (hUu : EqOn U (dirichletMixedDerivative p q u) (smoothDirichletHalfBox a β)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => U (x : ℂ)) 0 := by
  apply contDiffAt_infty.mpr
  intro n
  obtain ⟨ρ, hρ, hρA, hρb, hm⟩ := hhigh (p + q + n + 2)
  obtain ⟨V, hV, _, hVc⟩ := dirichlet_mixed_exists_boundary_contDiffOn
    hρ hρ (hs.mono (by
      intro z hz
      exact ⟨hz.1.trans (by linarith), hz.2.1, hz.2.2.trans hρb⟩)) (p + q + n + 2) p q n hm (le_refl _)
  exact (hVc.contDiffAt (isOpen_Ioo.mem_nhds
    (show (0 : ℝ) ∈ Ioo (-ρ) ρ from ⟨by linarith, hρ⟩))).congr_of_eventuallyEq (show (fun x : ℝ => U (x : ℂ)) =ᶠ[𝓝 (0 : ℝ)] (fun x => V 0 (x : ℂ)) by
      filter_upwards [isOpen_Ioo.mem_nhds
        (show (0 : ℝ) ∈ Ioo (-a) a from ⟨by linarith, ha⟩),
        isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-ρ) ρ from ⟨by linarith, hρ⟩)]
        with x hx hxρ
      exact dirichlet_boundary_extensions_eq hβ hρ hU hUu
        (hV 0 (by omega)).1 (by
          simpa using (hV 0 (by omega)).2) hx hxρ)

/-- Both first derivatives can be represented on the same real
rectangle. Their all-order bottom smoothness is still obtained from
order-dependent smaller energy rectangles, rather than from a fixed
rectangle carrying an assumed all-order estimate. -/
theorem exists_dirichlet_gradient_smooth_boundary_fields 
    
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A b))
    (hhigh : ∀ N : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ρ < A / 2 ∧ ρ < b ∧
      ∀ j k : ℕ, j + k ≤ N → MemLp (dirichletMixedDerivative j k u) 2
        (volume.restrict (smoothDirichletHalfBox ρ ρ))) :
    ∃ (ρ : ℝ) (X Y : ℂ → ℂ), 0 < ρ ∧ ρ < A / 2 ∧ ρ < b ∧
      ContinuousOn X (smoothDirichletClosedHalfBox ρ ρ) ∧
      ContinuousOn Y (smoothDirichletClosedHalfBox ρ ρ) ∧
      EqOn X (dirD u 1) (smoothDirichletHalfBox ρ ρ) ∧
      EqOn Y (dirD u Complex.I) (smoothDirichletHalfBox ρ ρ) ∧
      ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => X (x : ℂ)) 0 ∧
      ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => Y (x : ℂ)) 0 := by
  obtain ⟨ρ, hρ, hρA, hρb, hm⟩ := hhigh 3
  have hWU : smoothDirichletHalfBox ρ ρ ⊆ smoothDirichletHalfBox A b := by
    intro z hz
    exact ⟨hz.1.trans (by linarith), hz.2.1, hz.2.2.trans hρb⟩
  obtain ⟨X, hXc, hXu⟩ := dirichlet_mixed_exists_continuous_extension
    hρ hρ (hs.mono hWU) 3 1 0 hm (by omega)
  obtain ⟨Y, hYc, hYu⟩ := dirichlet_mixed_exists_continuous_extension
    hρ hρ (hs.mono hWU) 3 0 1 hm (by omega)
  exact ⟨ρ, X, Y, hρ, hρA, hρb, hXc, hYc, hXu, hYu, dirichlet_mixed_boundary_contDiffAt_of_finite_energy hρ hρ hs 1 0 hhigh hXc hXu, dirichlet_mixed_boundary_contDiffAt_of_finite_energy hρ hρ hs 0 1 hhigh hYc hYu⟩

/-- The actual domain correspondence of the chosen smooth graph is
retained along with the constructed smooth boundary-gradient pair.
Thus downstream boundary inverse-map arguments can prove frontier
membership from the same genuine chart, without changing witnesses. -/
theorem exists_riemannMapping_genuine_gradient_smooth_boundary_fields 
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    F (hF : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) (himage : F '' ball 0 1 = Ω)
     (hp : p ∈ frontier Ω) :
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
       (∀ x : ℝ, |x| < A → u (x : ℂ) = 0) ∧
       ContinuousOn X (smoothDirichletClosedHalfBox ρ ρ) ∧
       ContinuousOn Y (smoothDirichletClosedHalfBox ρ ρ) ∧
       EqOn X (dirD u 1) (smoothDirichletHalfBox ρ ρ) ∧
       EqOn Y (dirD u Complex.I) (smoothDirichletHalfBox ρ ρ) ∧
       ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => X (x : ℂ)) 0 ∧
       ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => Y (x : ℂ)) 0) := by
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
