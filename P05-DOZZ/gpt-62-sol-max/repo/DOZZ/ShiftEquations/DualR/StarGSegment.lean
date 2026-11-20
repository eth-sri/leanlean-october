/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.DualR.SwitchPoint
public import DOZZ.ShiftEquations.DualR.SegFactors
import DOZZ.Correlations.Analytic.StructureConstantHolomorphic
import DOZZ.ShiftEquations.Rbar.Continuation
import DOZZ.Brownian.Reflection.RtheorAnalytic
public import DOZZ.ShiftEquations.Representatives

/-!
# Continuation of the shifted second dual seed along a segment

From a good start point where the shifted second dual seed holds nearby (`starG_eventually`),
the shifted identity
`R(ε) (-𝒜(2Q - ε - 2/γ - γ/2) C(2Q - ε - 2/γ - γ, α, α')/(πμ)) = L R(α) C(ε, 2Q - α - 2/γ, α')`
continues along the segment to any end point where both shifted triples are in the extended
Seiberg domain (a convex condition) and all factors are analytic.
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

/-- **Segment continuation of the shifted second dual seed.** -/
theorem starG_segment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) {γ μ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hSeed : HasDualCrossing P X M γ μ)
    (hShiftGluing : HasShiftGluing P X M γ μ)
    {hR : ℝ} (hhR : 0 < hR) {R : ℂ → ℂ} (hRm : MeromorphicOn R (horizontalStrip hR))
    {BR : ℝ → Ω → BrownianPath × BrownianPath} {ZR : Ω → Measure ℝ}
    (hBR : IsReflectionFamily P γ BR ZR)
    (hRv : RepresentsReflection P γ μ BR ZR R)
    {es as a's ef af a'f : ℝ}
    (hS1 : ExtendedSeiberg3 γ (2 * Q γ - es - 2 / γ) as a's)
    (hS2 : ExtendedSeiberg3 γ es (2 * Q γ - as - 2 / γ) a's)
    (hS3 : ExtendedSeiberg3 γ (2 * Q γ - es - 2 / γ - γ) as a's)
    (hRes : AnalyticAt ℂ R (es : ℂ)) (hRas : AnalyticAt ℂ R (as : ℂ))
    (hsS1 : AnalyticAt ℂ Complex.Gamma (sExp γ (2 * Q γ - es - 2 / γ) as a's : ℂ))
    (hsS2 : AnalyticAt ℂ Complex.Gamma (sExp γ es (2 * Q γ - as - 2 / γ) a's : ℂ))
    (hsS3 : AnalyticAt ℂ Complex.Gamma (sExp γ (2 * Q γ - es - 2 / γ - γ) as a's : ℂ))
    (hgS1 : AnalyticAt ℂ Complex.Gamma (dualArg₁ γ es))
    (hgS2 : AnalyticAt ℂ Complex.Gamma (dualArg₂ γ as))
    (hgS3 : AnalyticAt ℂ Complex.Gamma (1 - dualArg₃ γ es as a's))
    (hgS4 : AnalyticAt ℂ Complex.Gamma (1 - dualArg₄ γ es as a's))
    (hAS : ShiftCoeffGood γ (((2 * Q γ - es - 2 / γ : ℝ) : ℂ) - γ / 2) as a's)
    (hP1 : ExtendedSeiberg3 γ (2 * Q γ - ef - 2 / γ - γ) af a'f)
    (hP2 : ExtendedSeiberg3 γ ef (2 * Q γ - af - 2 / γ) a'f)
    (hRef : AnalyticAt ℂ R (ef : ℂ)) (hRaf : AnalyticAt ℂ R (af : ℂ))
    (hsP1 : AnalyticAt ℂ Complex.Gamma (sExp γ (2 * Q γ - ef - 2 / γ - γ) af a'f : ℂ))
    (hsP2 : AnalyticAt ℂ Complex.Gamma (sExp γ ef (2 * Q γ - af - 2 / γ) a'f : ℂ))
    (hgP1 : AnalyticAt ℂ Complex.Gamma (dualArg₁ γ ef))
    (hgP2 : AnalyticAt ℂ Complex.Gamma (dualArg₂ γ af))
    (hgP3 : AnalyticAt ℂ Complex.Gamma (1 - dualArg₃ γ ef af a'f))
    (hgP4 : AnalyticAt ℂ Complex.Gamma (1 - dualArg₄ γ ef af a'f))
    (hAP : ShiftCoeffGood γ (((2 * Q γ - ef - 2 / γ : ℝ) : ℂ) - γ / 2) af a'f) :
    R ef * (-(1 / (Real.pi * μ)) *
        shiftCoeffA γ (γ / 2) (((2 * Q γ - ef - 2 / γ : ℝ) : ℂ) - γ / 2) af a'f *
          (structureConstant P M γ μ (2 * Q γ - ef - 2 / γ - γ) af a'f : ℂ)) =
      dualLC γ ef af a'f * R af * (structureConstant P M γ μ ef (2 * Q γ - af - 2 / γ) a'f : ℂ) := by
  have hnear := starG_eventually P X M hγ hγ2 hμ hX hM hSeed hShiftGluing hhR hRm hBR hRv
    (f₁ := fun t => es + t * (ef - es)) (f₂ := fun t => as + t * (af - as))
    (f₃ := fun t => a's + t * (a'f - a's)) (by fun_prop) (by fun_prop) (by fun_prop) (t₀ := 0)
    (by simp only [zero_mul, add_zero]; exact hS1) (by simp only [zero_mul, add_zero]; exact hS2)
    (by simp only [zero_mul, add_zero]; exact hS3)
    (by simp only [zero_mul, add_zero]; exact hRes) (by simp only [zero_mul, add_zero]; exact hRas)
    (by simp only [zero_mul, add_zero]; exact hsS1) (by simp only [zero_mul, add_zero]; exact hsS2)
    (by simp only [zero_mul, add_zero]; exact hsS3) (by simp only [zero_mul, add_zero]; exact hgS1)
    (by simp only [zero_mul, add_zero]; exact hgS2) (by simp only [zero_mul, add_zero]; exact hgS3)
    (by simp only [zero_mul, add_zero]; exact hgS4) (by simp only [zero_mul, add_zero]; exact hAS)
  let eShift : ℂ → ℂ := fun z => (2 * Q γ - 2 / γ : ℝ) - z - γ / 2
  have heShift (x : ℝ) : eShift x = (((2 * Q γ - x - 2 / γ : ℝ) : ℂ) - γ / 2) := by
    simp only [eShift, Complex.ofReal_sub]
    ring
  let A : ℂ → ℂ → ℂ → ℂ := fun e a b => -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) (eShift e) a b
  have heAnalytic (t : ℂ) : AnalyticAt ℂ (fun z => eShift (segC es ef z)) t :=
    (analyticAt_const.sub (analyticAt_segC es ef t)).sub analyticAt_const
  have hAm (t : ℂ) : MeromorphicAt (fun z => A (segC es ef z) (segC as af z) (segC a's a'f z)) t :=
    (MeromorphicAt.const _ _).fun_mul (meromorphicAt_shiftCoeffA_comp
      (heAnalytic t) (analyticAt_segC as af t) (analyticAt_segC a's a'f t))
  have hA1 : AnalyticAt ℂ (fun z => A (segC es ef z) (segC as af z) (segC a's a'f z)) 1 :=
    analyticAt_const.mul (analyticAt_shiftCoeffA_comp
      (heAnalytic 1) (analyticAt_segC as af 1) (analyticAt_segC a's a'f 1)
      (by simpa only [segC_one, heShift] using hAP))
  simpa only [A, heShift] using
    (dual_seed_eq_at_segment_end P X M hγ hγ2 hμ hX hM hhR hRm hAm hA1
      hS3 hS2 hP1 hP2 hRef hRaf hsP1 hsP2 hgP1 hgP2 hgP3 hgP4
      (by
        filter_upwards [nhdsWithin_le_nhds hnear] with t ht
        simpa only [A, heShift] using ht))

end DOZZ.Proofs

end
