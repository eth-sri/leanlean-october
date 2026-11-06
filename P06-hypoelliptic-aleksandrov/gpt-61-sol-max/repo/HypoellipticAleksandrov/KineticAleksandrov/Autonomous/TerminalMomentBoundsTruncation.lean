module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TerminalMomentBoundsKernel
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic
public import PDEFoundation.Calculus.RegularityOrder


/-! # Compact polynomial truncation and kernel comparison

Actual smooth compact terminal tests converge pointwise to the polynomial.
Fatou passes their uniform comparison bound to the extended terminal integral.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open MeasureTheory Filter
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal

section
variable (g : EvolutionAmbientState 1 → ℝ) (hg : ContDiff ℝ PDE.smoothOrder g) (N : ℕ)

/-- A smooth polynomial times the conservation cutoff is an actual bounded datum. -/
def momentCutoff  : BoundedBorel (EvolutionAmbientState 1) := by
  have hs := hg.mul (conservationDatum_smoothCompact N 0).1
  have hc : HasCompactSupport (fun x => g x * conservationDatum N x) :=
    (conservationDatum_smoothCompact N 0).2.1.mul_left
  refine ⟨fun x => g x * conservationDatum N x, hs.continuous.measurable, ?_⟩
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hs.continuous
  exact ⟨max C 0, le_max_right _ _, fun x =>
    (show |g x * conservationDatum N x| ≤ C from
      by exact hC x).trans (le_max_left _ _)⟩

/-- The compact polynomial truncation is admitted by the realization. -/
theorem momentCutoff_smoothCompact  (tau : ℝ) :
    IsSmoothCompactTerminalDatum autonomousWholeDomain (fun _ => 0) tau
      (momentCutoff g hg N) := by
  refine ⟨hg.mul (conservationDatum_smoothCompact N tau).1,
    (conservationDatum_smoothCompact N tau).2.1.mul_left, ?_⟩
  exact tsupport_mul_subset_right.trans (conservationDatum_smoothCompact N tau).2.2
end


/-- Each fixed point eventually lies in the unit region of both coordinate cutoffs. -/
theorem conservationDatum_eventually_one (x : EvolutionAmbientState 1) :
    ∀ᶠ N : ℕ in atTop, conservationDatum N x = 1 := by
  have h1 : ∀ᶠ N : ℕ in atTop, ‖x.1‖ ≤ (N : ℝ) + 1 :=
    (tendsto_natCast_atTop_atTop.eventually_ge_atTop ‖x.1‖).mono fun N h => by linarith
  have h2 : ∀ᶠ N : ℕ in atTop, ‖x.2‖ ≤ (N : ℝ) + 1 :=
    (tendsto_natCast_atTop_atTop.eventually_ge_atTop ‖x.2‖).mono fun N h => by linarith
  filter_upwards [h1, h2] with N hN1 hN2
  change zCutoffN 1 N x.1 * zCutoffN 1 N x.2 = 1
  rw [zCutoffN_eq_one hN1, zCutoffN_eq_one hN2, one_mul]

variable {lam Lam : ℝ} (hlam : 0 < lam) (A : SmoothAutonomous lam Lam) (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E) (g : EvolutionAmbientState 1 → ℝ) (hg : ContDiff ℝ PDE.smoothOrder g)

include hlam hE in
/-- Comparison bounds the integral of every actual compact polynomial test. -/
theorem momentCutoff_integral_le
    (W : Point → ℝ) (hc : Continuous W) (hr : ∀ p, IsSliceRegularAt W p)
    (tau : ℝ) (hn : ∀ p, p.time ≤ tau → 0 ≤ W p)
    (hop : ∀ p, p.time ≤ tau →
      transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1) W p ≤ 0)
    (ht : ∀ p, p.time = tau → g (p.position, p.velocity) = W p)
    (q : EvolutionQuery autonomousWholeDomain (fun _ => 0)) (hq : q.1.2.1 = tau) (N : ℕ) :
    ∫ x, momentCutoff g hg N x ∂E.2.master q ≤
      W ⟨q.1.1, q.1.2.2.1, q.1.2.2.2⟩ := by
  obtain ⟨u, hu, hrep, -⟩ := hE.1 tau _
    (momentCutoff_smoothCompact g hg N tau)
  let state : EvolutionState autonomousWholeDomain (fun _ => 0) q.1.1 :=
    ⟨q.1.2.2, q.2.2⟩
  have horder  := hq ▸ q.2.1
  have he := integral_master_eq_fiber E.2 autonomousWholeDomain_measurable
    q.1.1 tau horder state _ (momentCutoff g hg N).measurable

  have huq : u ⟨q.1.1, q.1.2.2.1, q.1.2.2.2⟩ =
      ∫ x, momentCutoff g hg N x ∂E.2.master q := by
    have hquery : evolutionQueryOfState autonomousWholeDomain _
        q.1.1 tau horder state = q := by
      apply Subtype.ext
      change (q.1.1, tau, q.1.2.2) = q.1
      rw [← hq]
    rw [hquery] at he
    exact (hrep q.1.1 horder state).trans ((hE.2.1 q.1.1 tau horder state (terminalStateDatum (momentCutoff g hg N))).trans he.symm)
  rw [← huq]
  apply terminal_polynomial_comparison hlam A tau _ u W hu hc hr hn hop
    (fun p hp => ?_) _ horder
  change g (p.position, p.velocity) * conservationDatum N (p.position, p.velocity) ≤ W p
  rw [ht p hp]
  exact (mul_le_mul_of_nonneg_left (conservationDatum_bounds N _).2 (hn p hp.le)).trans
    (by rw [mul_one])

include hlam hE hg in
/-- Fatou transfers compact polynomial comparison to the unbounded terminal moment. -/
theorem terminal_polynomial_lintegral_le  (hg0 : ∀ x, 0 ≤ g x)
    (W : Point → ℝ) (hc : Continuous W) (hr : ∀ p, IsSliceRegularAt W p)
    (tau : ℝ) (hn : ∀ p, p.time ≤ tau → 0 ≤ W p)
    (hop : ∀ p, p.time ≤ tau →
      transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1) W p ≤ 0)
    (ht : ∀ p, p.time = tau → g (p.position, p.velocity) = W p)
    (q : EvolutionQuery autonomousWholeDomain (fun _ => 0)) (hq : q.1.2.1 = tau) :
    (∫⁻ x, ENNReal.ofReal (g x) ∂E.2.master q) ≤
      ENNReal.ofReal (W ⟨q.1.1, q.1.2.2.1, q.1.2.2.2⟩) := by

  have hlim (x) : liminf (fun N => (fun N x => ENNReal.ofReal (momentCutoff g hg N x)) N x) atTop = ENNReal.ofReal (g x) := by

    rw [Filter.liminf_congr (by
        filter_upwards [conservationDatum_eventually_one x] with N hN
        change ENNReal.ofReal (g x * conservationDatum N x) = _
        rw [hN, mul_one]), liminf_const]
  rw [← lintegral_congr hlim]
  apply (lintegral_liminf_le (fun N => (momentCutoff g hg N).measurable.ennreal_ofReal)).trans
  refine liminf_le_of_frequently_le ?_ (by isBoundedDefault)
  apply (Filter.Eventually.of_forall (fun N => ?_)).frequently
  let : IsFiniteMeasure (E.2.master q) :=
    ⟨(E.2.mass_le_one q).trans_lt ENNReal.one_lt_top⟩

  rw [← ofReal_integral_eq_lintegral_ofReal (boundedBorel_integrable _ _) (Filter.Eventually.of_forall
    (fun x => (id (mul_nonneg (hg0 x) (conservationDatum_bounds N x).left))))]
  exact ENNReal.ofReal_le_ofReal (momentCutoff_integral_le hlam A E hE g hg W hc hr
    tau hn hop ht q hq N)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
