module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDensitiesContinuity
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
import PDEFoundation.Sobolev.OneDimensional.PrimitiveWeakIdentity
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Tactic

/-! # Lebesgue primitives of locally integrable angular fluxes -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

section
variable (g : ℝ → ℝ) (hg : LocallyIntegrable g volume)
include hg

/-- The oriented Lebesgue primitive of a locally integrable function is locally absolutely
continuous. -/
theorem bellman_lebesguePrimitive_locallyAC
    (a b : ℝ) (hab : a ≤ b) :
    AbsolutelyContinuousOnInterval (fun x => ∫ z in 0..x, g z) a b := by
  let l := min 0 a
  let u := max 0 b
  have hlu : l ≤ u := (min_le_left 0 a).trans (le_max_left 0 b)
  have hi : IntervalIntegrable g volume l u :=
    (intervalIntegrable_iff').2 (hg.integrableOn_isCompact isCompact_uIcc)
  have hc := hi.absolutelyContinuousOnInterval_intervalIntegral
    (show (0 : ℝ) ∈ uIcc l u by
      rw [uIcc_of_le hlu]; exact ⟨min_le_left _ _, le_max_left _ _⟩)
  apply hc.mono
  rw [uIcc_of_le hab, uIcc_of_le hlu]
  exact Icc_subset_Icc (min_le_right _ _) (le_max_right _ _)

/-- The oriented Lebesgue primitive is globally continuous. -/
theorem bellman_lebesguePrimitive_continuous : Continuous (fun x => ∫ z in 0..x, g z) :=
  bellman_locallyAC_continuous (bellman_lebesguePrimitive_locallyAC g hg)

/-- A locally integrable Lebesgue primitive has its original function as weak derivative. -/
theorem bellman_lebesguePrimitive_weak
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcφ : HasCompactSupport φ) :
    (∫ x, (∫ z in 0..x, g z) * deriv φ x) = -∫ x, g x * φ x := 
  PDE.intervalIntegral_weak_identity volume hg
    (bellman_lebesguePrimitive_continuous g hg).locallyIntegrable (hφ.of_le (by simp)) hcφ

end

end HypoellipticAleksandrov.KineticAleksandrov
