module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaInverseStability

@[expose] public section

/-!
# Physical stationary points for the model-phase B transformation

The frequency r is linked to the original positive N,T scales by v=r*N/T.
The unique critical point, its dual-phase value and its second derivative
are derived for the actual phase T*F(x/N)-r*x. No stationary-phase integral
or Poisson summation formula is asserted here.
-/

noncomputable section

open Set Expdb Filter
open scoped Topology ContDiff FourierTransform

namespace TaoTrudgianYang2025


def modelPhaseFrequencyPhase (F : ℝ → ℝ) (T N r x : ℝ) : ℝ :=
  T * F (x/N) - r*x

def modelPhaseStationaryPoint (F : ℝ → ℝ) (T N r : ℝ) : ℝ :=
  N * modelPhaseInverseSlope F (r*N/T)

theorem modelPhaseStationaryPoint_div {F : ℝ → ℝ} {T N r : ℝ}
    (hN : N ≠ 0) :
    modelPhaseStationaryPoint F T N r / N = modelPhaseInverseSlope F (r*N/T) := by
  unfold modelPhaseStationaryPoint
  field_simp

theorem modelPhaseFrequencyPhase_hasDerivAt
    {σ δ T N r x : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hx : x/N ∈ Ioo (1 : ℝ) 2) :
    HasDerivAt (modelPhaseFrequencyPhase F T N r) (T/N*deriv F (x/N)-r) x := by
  have hd := (approximateModelPhase_contDiffAt hF hx).differentiableAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  convert ((hd.hasDerivAt.comp x ((hasDerivAt_id x).div_const N)).const_mul T).sub
    ((hasDerivAt_id x).const_mul r) using 1
  · rfl
  · ring

theorem modelPhaseStationaryPoint_phase
    {F : ℝ → ℝ} {T N r : ℝ} (hT : T ≠ 0) (hN : N ≠ 0) :
    modelPhaseFrequencyPhase F T N r (modelPhaseStationaryPoint F T N r) =
      -T * modelPhaseLegendreDual F (r*N/T) := by
  unfold modelPhaseFrequencyPhase
  rw [modelPhaseStationaryPoint_div hN]
  unfold modelPhaseStationaryPoint modelPhaseLegendreDual
  field_simp
  ring

theorem modelPhaseFrequencyPhase_secondDeriv
    {σ δ T N r x : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hx : x/N ∈ Ioo (1 : ℝ) 2) :
    deriv (deriv (modelPhaseFrequencyPhase F T N r)) x =
      T/N^2 * deriv (deriv F) (x/N) := by
  have hd := (approximateModelPhase_deriv_contDiffAt hF hx).differentiableAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hh := ((hd.hasDerivAt.comp x ((hasDerivAt_id x).div_const N)).const_mul
    (T/N)).sub_const r
  have heq : deriv (modelPhaseFrequencyPhase F T N r) =ᶠ[𝓝 x]
      (fun y => T/N * deriv F (y/N) - r) := by
    have hc : ContinuousAt (fun y : ℝ => y/N) x := continuousAt_id.div_const N
    filter_upwards [hc (isOpen_Ioo.mem_nhds hx)] with y hy
    exact (modelPhaseFrequencyPhase_hasDerivAt hF hy).deriv
  simp only [Function.comp_apply, id_eq] at hh
  rw [heq.deriv_eq, hh.deriv]
  ring


