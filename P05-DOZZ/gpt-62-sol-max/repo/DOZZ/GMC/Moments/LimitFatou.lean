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
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ) (p : ℝ) (C : ℝ≥0∞)
    (hfg : TendstoInMeasure P f atTop g)
    (hfmeas : ∀ n, AEMeasurable
      (fun ω => ENNReal.rpow (ENNReal.ofReal (max (f n ω) 0)) p) P)
    (hgbound : ∀ᵐ ω ∂P, 0 ≤ g ω)
    (hbound : ∀ n, ∫⁻ ω,
      ENNReal.rpow (ENNReal.ofReal (max (f n ω) 0)) p ∂P ≤ C) :
    ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (g ω)) p ∂P ≤ C := by
  obtain ⟨ns, hns, hsub⟩ := hfg.exists_seq_tendsto_ae
  let ψ  := fun x => ENNReal.rpow (ENNReal.ofReal (max x 0)) p
  have hψ : Continuous ψ := ENNReal.continuous_rpow_const.comp
      (ENNReal.continuous_ofReal.comp
        (continuous_max.comp (continuous_id.prodMk continuous_const)))
  have hlim : ∀ᵐ ω ∂P,
      Filter.liminf (fun i => ψ (f (ns i) ω)) atTop = ψ (g ω) := by
    filter_upwards [hsub] with ω hω
    exact Filter.Tendsto.liminf_eq (hψ.continuousAt.tendsto.comp hω)
  have htarget : ∀ᵐ ω ∂P, ψ (g ω) = ENNReal.rpow (ENNReal.ofReal (g ω)) p := by
    filter_upwards [hgbound] with ω hω
    simp [ψ]
  exact Trans.trans
    (Trans.trans
      (Trans.trans
        (lintegral_congr_ae
          (mp_mem htarget (mp_mem hlim (univ_mem' (id fun ω hlimω htargetω => Eq.symm (Eq.trans hlimω htargetω))))))
        (lintegral_liminf_le' fun i => hfmeas (ns i)))
      (liminf_le_limsup isBounded_le_of_top isBounded_ge_of_bot))
    (limsup_le_of_le isCobounded_le_of_bot (Eventually.of_forall fun i => hbound (ns i)))

end DOZZ.Proofs
