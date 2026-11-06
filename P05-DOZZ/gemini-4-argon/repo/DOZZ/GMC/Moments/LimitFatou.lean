module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Fatou passage for moments of finite-cutoff test integrals. -/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

namespace DOZZ.Proofs

/-- A uniform extended-power bound for a sequence of real random variables passes to a limit
in measure. The use of `max · 0` lets the lemma apply to test integrals whose nonnegativity is
known only almost everywhere. -/
theorem lintegral_ennreal_rpow_le_of_tendstoInMeasure
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → Ω → ℝ) g p (C : ℝ≥0∞)
    (hfg : TendstoInMeasure P f atTop g)
    (hfmeas : ∀ n, AEMeasurable
      (fun ω => ENNReal.rpow (ENNReal.ofReal (max (f n ω) 0)) p) P)
    (hgbound : ∀ᵐ ω ∂P, 0 ≤ g ω)
    (hbound : ∀ n, ∫⁻ ω,
      ENNReal.rpow (ENNReal.ofReal (max (f n ω) 0)) p ∂P ≤ C) :
    ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (g ω)) p ∂P ≤ C := by
  obtain ⟨ns, hns, hsub⟩ := hfg.exists_seq_tendsto_ae
  let ψ : ℝ → ℝ≥0∞ := fun x => ENNReal.rpow (ENNReal.ofReal (max x 0)) p
  calc
    ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (g ω)) p ∂P
        = ∫⁻ ω, Filter.liminf (fun i => ψ (f (ns i) ω)) atTop ∂P := by
            exact lintegral_congr_ae (by filter_upwards [(by filter_upwards [hsub] with ω hω; exact Filter.Tendsto.liminf_eq ((ENNReal.continuous_rpow_const.comp (ENNReal.continuous_ofReal.comp (continuous_max.comp (continuous_id.prodMk continuous_const))) : Continuous ψ).continuousAt.tendsto.comp hω)), (show ∀ᵐ ω ∂P, ψ (g ω) = ENNReal.rpow (ENNReal.ofReal (g ω)) p by filter_upwards [hgbound] with ω hω; simp [ψ])] with ω hlimω htargetω; exact (hlimω.trans htargetω).symm)
    _ ≤ Filter.liminf (fun i => ∫⁻ ω, ψ (f (ns i) ω) ∂P) atTop :=
      lintegral_liminf_le' (fun i => hfmeas (ns i))
    _ ≤ Filter.limsup (fun i => ∫⁻ ω, ψ (f (ns i) ω) ∂P) atTop :=
      Filter.liminf_le_limsup
    _ ≤ C := Filter.limsup_le_of_le (by isBoundedDefault)
      (Filter.Eventually.of_forall fun i => hbound (ns i))

end DOZZ.Proofs
