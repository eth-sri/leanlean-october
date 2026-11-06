module
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Selected physical-budget proofs released under MIT-0; see
../../../../../third_party/twelfth/LICENSE-MIT-0.
Source pin: 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Manifest: ../../../../../third_party/twelfth/PHYSICAL_PACKET_ASSEMBLY_MANIFEST.json.
The new assembly uses the literal native prefix/Gram bound and keeps the
actual stationary-zeta source-to-prefix inequality as an explicit premise.
Mathlib dependencies retain their Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonPhysicalBudget
public import MathCollab.Density.Stronger.Peaks.Inputs
import WeylPort.Analytic.RealLaplace

@[expose] public section
open Complex Filter MeasureTheory Set Topology Finset
open scoped Interval
open MathCollab.Density.Stronger
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

/-- The sole source-side premise. The phase maxima and source cutoff are literal,
and the constant is uniform before t and G. No packet estimate is a premise. -/
def LocalMeanSourceToPrefix : Prop :=
  ∀ δ κ : ℝ, 0 < δ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ t G : ℝ,
      T₀ ≤ t → t^δ ≤ G → G ≤ t^(1/2-δ) → t^(1/4+κ) ≤ G →
      (∫ u in t-G..t+G, zetaMomentCriticalNorm u^2) ≤
        C*G*Real.log t + C*G*t^(-(1/4:ℝ))*
          atkinsonUndampedDyadicPhaseBound t (atkinsonSourceCutoff t G (Real.log t))

/-- Physical width scales follow from any actual point of a nonempty packet. -/
theorem packet_width_scales {δ H G : ℝ} {W : Finset ℝ}
    (hδ : 0 < δ) (hH : 1 ≤ H) (_hG : 0 < G) (hW : W.Nonempty)
    (hrange : ∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ)) :
    H^δ ≤ G ∧ G ≤ Real.sqrt (2*H) := by
  obtain ⟨t,ht⟩ := hW
  pm_205 hHt htH hlower hupper hrange t ht
  have hH0 : 0 < H := by linarith
  refine ⟨(Real.rpow_le_rpow hH0.le hHt hδ.le).trans hlower,?_⟩
  calc
    G ≤ t^(1/2-δ) := hupper
    _ ≤ t^(1/2:ℝ) := Real.rpow_le_rpow_of_exponent_le (hH.trans hHt) (by linarith)
    _ = Real.sqrt t := (Real.sqrt_eq_rpow t).symm
    _ ≤ Real.sqrt (2*H) := Real.sqrt_le_sqrt htH

/-- Actual physical packets follow from the pointwise source inequality.
There is no local-mean-packet or moment assumption in this theorem. -/
theorem localMeanPacketInput_of_sourceToPrefix (hSource : LocalMeanSourceToPrefix) :
    Peaks.LocalMeanPacketInput := by
  intro δ κ ν hδ hκ hν
  obtain ⟨C,hC,T₀,hT₀,hsource⟩ := hSource δ κ hδ hκ
  obtain ⟨D,hD,H₁,hH₁,hgram⟩ :=
    exists_sum_atkinsonUndampedDyadicPhaseBound_sq_le_power hδ (show 0 < ν/2 by linarith)
  pm_107 E hE H₂ hH₂ hbudget exists_atkinsonPhysicalGapBudget_le_twoTerm hδ hν
  refine ⟨C,hC,C^2*D*E,by positivity,max T₀ (max H₁ H₂),
    hT₀.trans (le_max_left _ _),?_⟩
  intro H G A L W hH hG hsep hrange hlocal
  by_cases hW : W.Nonempty
  · have hTH : T₀ ≤ H := (le_max_left _ _).trans hH
    pm_343 h1H H₁ h2H H₂
    pm_4387
    have hnativeSep : IsSeparated G W := hsep
    have hp := hgram H G A L W h1H hwidth.1 hnativeSep
      (fun t ht => ⟨(hrange t ht).1,(hrange t ht).2.1⟩) hlocal
    have hphys := hbudget H G L W.card h2H hwidth.1 hwidth.2
    pm_4388
    calc
      _ ≤ ((C*G*H^(-(1/4:ℝ)))*(∑ t ∈ W, B t))^2 :=
        pow_le_pow_left₀ hsumpos hsum 2
      _ = C^2*G^2*H^(-(1/2:ℝ))*(∑ t ∈ W, B t)^2 := by
        rw [mul_pow,mul_pow,mul_pow,he]
      _ ≤ C^2*G^2*H^(-(1/2:ℝ))*(D*atkinsonPowerGapBudget (ν/2) H G L N W.card) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = (C^2*D)*(G^2*H^(-(1/2:ℝ))*atkinsonPowerGapBudget (ν/2) H G L N W.card) := by ring
      _ ≤ (C^2*D)*(E*H^ν*((W.card:ℝ)*H/G+(W.card:ℝ)^2*Real.sqrt (G*L))) :=
        mul_le_mul_of_nonneg_left hphys (by positivity)
      _ = _ := by ring
  simp_all

end MathCollab.Density.Stronger.Atkinson
