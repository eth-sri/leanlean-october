module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.MajorantAbstract
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import PDEFoundation.Calculus.RegularityOrder


/-!
# Passing sharp positive smooth-test bounds to continuous tests

The reference measure is Haar measure restricted to the open test region. The tested
measure is finite. Compact supports stay strictly inside that region.
-/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

variable (ν μ : Measure E)

/-- Positive smooth-test bounds extend sharply to continuous compactly supported tests. -/
theorem integral_le_of_smooth_tests  [ν.IsAddHaarMeasure]
    [IsFiniteMeasure μ] {U : Set E} (hU : IsOpen U) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpt : p ≠ ∞) {C : ℝ} (hC : 0 ≤ C)
    (htest : ∀ f : E → ℝ, ContDiff ℝ PDE.smoothOrder f → HasCompactSupport f →
      tsupport f ⊆ U → (∀ x, 0 ≤ f x) →
      (∫ x, f x ∂μ) ≤ C * (eLpNorm f p (ν.restrict U)).toReal)
    {f : E → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ U) (hf0 : ∀ x, 0 ≤ f x) :
    (∫ x, f x ∂μ) ≤ C * (eLpNorm f p (ν.restrict U)).toReal := by
  have hfp : MemLp f p (ν.restrict U) := hf.memLp_of_hasCompactSupport hfc
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hδ : 0 < ε / (C + 1) := div_pos hε (by positivity)
  obtain ⟨g, hgs, hgc, hgU, hg0, hfg, hgn⟩ :=
    exists_smooth_majorant_toReal_le ν hU hfc hfs hf.continuousOn
      (fun x _ => hf0 x) (Filter.Eventually.of_forall fun _ => le_rfl)
      hp hpt hfp hδ
  have hfg' : ∀ x, f x ≤ g x := by
    intro x
    by_cases hx : x ∈ tsupport f
    · exact hfg x hx
    · rw [image_eq_zero_of_notMem_tsupport hx]
      exact hg0 x
  calc
    (∫ x, f x ∂μ) ≤ ∫ x, g x ∂μ :=
      integral_mono (hf.integrable_of_hasCompactSupport hfc)
        (hgs.continuous.integrable_of_hasCompactSupport hgc) hfg'
    _ ≤ C * (eLpNorm g p (ν.restrict U)).toReal := htest g hgs hgc hgU hg0
    _ ≤ C * ((eLpNorm f p (ν.restrict U)).toReal + ε / (C + 1)) :=
      mul_le_mul_of_nonneg_left hgn hC
    _ ≤ C * (eLpNorm f p (ν.restrict U)).toReal + ε := by
      have hmul : C * (ε / (C + 1)) ≤ ε := by
        rw [← mul_div_assoc]
        exact (div_le_iff₀ (by positivity)).2 (by nlinarith)
      nlinarith

/-- Positive smooth-test bounds control the absolute integral of signed continuous tests. -/
theorem abs_integral_le_of_smooth_tests  [ν.IsAddHaarMeasure]
    [IsFiniteMeasure μ] {U : Set E} (hU : IsOpen U) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpt : p ≠ ∞) {C : ℝ} (hC : 0 ≤ C)
    (htest : ∀ f : E → ℝ, ContDiff ℝ PDE.smoothOrder f → HasCompactSupport f →
      tsupport f ⊆ U → (∀ x, 0 ≤ f x) →
      (∫ x, f x ∂μ) ≤ C * (eLpNorm f p (ν.restrict U)).toReal)
    {f : E → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ U) :
    |∫ x, f x ∂μ| ≤ C * (eLpNorm f p (ν.restrict U)).toReal := (LE.le.trans (norm_integral_le_integral_norm f)
  (Eq.mp
    (congrArg (fun _a => ∫ (x : E), |f x| ∂μ ≤ C * _a.toReal)
      (id (eLpNorm_norm f (Continuous.aestronglyMeasurable hf))))
    (integral_le_of_smooth_tests ν μ hU hp hpt hC htest (Continuous.abs hf) (HasCompactSupport.norm hfc)
      (LE.le.trans
        (closure_mono fun x hx hz =>
          hx (of_eq_true (Eq.trans (congrFun' (congrArg Eq (Eq.trans (congrArg abs hz) abs_zero)) 0) (eq_self 0))))
        hfs)
      fun x => abs_nonneg (f x))))

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
