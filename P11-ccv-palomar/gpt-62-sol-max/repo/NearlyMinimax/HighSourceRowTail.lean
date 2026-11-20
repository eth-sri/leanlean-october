module

public import NearlyMinimax.HighResponseTensorTail
public import NearlyMinimax.CompleteSourceMassAnnihilation


@[expose] public section

/-! All-count response bounds on every actual row of the complete source
family. The density factors may depend on the full spatial carrier and
density atom, and are independent only of the response atom. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
attribute [local instance] Classical.propDecidable

/-- All rows of the actual complete source satisfy the same Taylor cap,
with their own true variation masses. In particular this holds for sample
counts exceeding the exterior selector degree. -/
theorem sourceRow_reference_all_count_bound {n : ℕ}
    (d : ℕ) [NeZero d] (k D M q : ℕ) (hn : 1 ≤ n)
    (ad bd C lam ℓ N μ a V η ρ pPlus : ℝ) (hpPlus : 0 ≤ pPlus)
    (hpos : ∀ i, 0 < (sourceRowData d k D M q ad bd C lam ℓ N μ).rowMass i)
    (i : SourceRowIndex d D M q ad bd C lam ℓ N μ)
    (reset : SourceRowDensityMark d D M q ad bd C lam ℓ N μ i → Fin n → ℝ)
    (hmReset : ∀ u, Measurable (fun e => reset e u))
    (hReset : ∀ e u, |reset e u| ≤ pPlus)
    (g w : Fin n → ℝ) (φ : Fin n → HighFrameIndex d D → ℝ)
    (c : HighFrameIndex d D → ℝ) (H : ResponseGuards C a V η ρ g w φ) (hc : ∑ γ, |c γ| ≤ C⁻¹) (y : Fin n → Fin 3) :
    |highMarkedResponseAction ((sourceRowData d k D M q ad bd C lam ℓ N μ).rowLaw i)
      ((sourceRowData d k D M q ad bd C lam ℓ N μ).rowActivation i) a V η
      (fun e => reset (sourceRowDensityProj d D M q ad bd C lam ℓ N μ i e))
      (fun e => coefficientReset c
        ((sourceRowData d k D M q ad bd C lam ℓ N μ).rowVector i e)
        ((sourceRowData d k D M q ad bd C lam ℓ N μ).rowTime i e)) g w φ y| ≤
      (pPlus^n*highSeparatedDerivativeBudget a ρ*(n : ℝ)^2*η^2)*
        (sourceRowData d k D M q ad bd C lam ℓ N μ).rowMass i := by
  let P := sourceRowPacket d D M q ad bd C lam ℓ N μ i
  obtain ⟨hfin, hA⟩ := sourceRowPacket_valid d D M q ad bd C lam ℓ N μ i
  exact responseTensor_reference_all_count_bound P.carrier q hn C a V η ρ pPlus hpPlus P.weights P.amplitude
    (responsePacketWeight_measurable P.weights q C P.amplitude hA.meas)
    (responsePacketWeight_integrable P.weights q C P.amplitude P.carrier hA) (hpos i)
    (fun ζ e => reset (ζ,e)) (fun e u => (hmReset u).comp (measurable_id.prodMk measurable_const))
    (fun ζ e u => hReset (ζ,e) u) g w φ c H hc y

end NearlyMinimax
