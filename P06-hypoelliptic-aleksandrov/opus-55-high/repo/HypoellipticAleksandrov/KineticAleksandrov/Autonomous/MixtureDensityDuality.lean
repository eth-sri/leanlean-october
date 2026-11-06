module

public import HypoellipticAleksandrov.KineticAleksandrov.BoundedBorel
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.DensityFromTests
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Normed.Group.Bounded

/-! # Density norm bounds from bounded Borel conjugate tests

This reusable duality step has no kinetic analytic assumptions. Its test premise
is discharged by integration of the proved one-pole estimate in the consumer.
-/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory
open scoped ENNReal

/-- Pairing against every real test identifies an integrable nonnegative density exactly. -/
theorem mixture_density_eq_of_pairing {X : Type*} [MeasurableSpace X]
    (mu m : Measure X) [IsFiniteMeasure mu] (g : X → ℝ)
    (hgn : ∀ x, 0 ≤ g x) (hgi : Integrable g m)
    (hpair : ∀ f : X → ℝ, (∫ x, f x * g x ∂m) = ∫ x, f x ∂mu) :
    mu = m.withDensity (fun x => ENNReal.ofReal (g x)) := by
  ext B hB
  have he : (∫ x in B, g x ∂m) = (mu B).toReal := by
    have hh := hpair (B.indicator (fun _ => 1))
    have hi : (fun x => B.indicator (fun _ => 1) x * g x) = B.indicator g := by
      funext x
      by_cases hx : x ∈ B
      · simp_all
      simp_all
    rw [hi] at hh
    simpa only [integral_indicator hB,
      integral_const, smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply,
      Measure.restrict_apply MeasurableSet.univ, univ_inter] using hh
  calc
    mu B = ENNReal.ofReal _ :=
      (ENNReal.ofReal_toReal (measure_ne_top mu B)).symm
    _ = ENNReal.ofReal _ := congrArg ENNReal.ofReal he.symm
    _ = ∫⁻ x in B, ENNReal.ofReal _ ∂m :=
      ofReal_integral_eq_lintegral_ofReal hgi.restrict
        (Filter.Eventually.of_forall hgn)
    _ = _ := (withDensity_apply _ hB).symm

/-- Bounded conjugate tests give a sharp measurable nonnegative density with its Lq norm. -/
theorem mixture_density_bound_of_bounded_tests {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (m mu : Measure E)
    [m.IsAddHaarMeasure] [IsFiniteMeasure mu] (q C : ℝ) (hq : 1 < q) (hC : 0 ≤ C)
    (htest : ∀ f : BoundedBorel E,
      MemLp f (ENNReal.ofReal (q / (q - 1))) m → (∀ x, 0 ≤ f x) →
      (∫ x, f x ∂mu) ≤ C * (eLpNorm f (ENNReal.ofReal (q / (q - 1))) m).toReal) :
    ∃ g : E → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x) ∧
      mu = m.withDensity (fun x => ENNReal.ofReal (g x)) ∧
      MemLp g (ENNReal.ofReal q) m ∧ (eLpNorm g (ENNReal.ofReal q) m).toReal ≤ C := by
  have hs : ∀ f : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      tsupport f ⊆ univ → (∀ x, 0 ≤ f x) →
      (∫ x, f x ∂mu) ≤ C *
        (eLpNorm f (ENNReal.ofReal (q / (q - 1))) (m.restrict univ)).toReal := by
    intro f hf hfc _ hfn
    obtain ⟨M, hM⟩ := hfc.exists_bound_of_continuous hf.continuous
    let F : BoundedBorel E := ⟨f, hf.continuous.measurable, max M 0,
      le_max_right _ _, fun x => by
        simp_all⟩
    simpa only [Measure.restrict_univ] using
      htest F (hf.continuous.memLp_of_hasCompactSupport hfc) hfn
  obtain ⟨_, g, hgm, hgn, hgi, hgp, hgb, _, hpair⟩ :=
    Occupation.exists_density_of_smooth_tests m mu isOpen_univ (by simp) hq hC hs
  simp only [Measure.restrict_univ] at hgi hgp hgb hpair
  exact ⟨g, hgm, hgn, mixture_density_eq_of_pairing mu m g hgn hgi hpair, hgp, hgb⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
