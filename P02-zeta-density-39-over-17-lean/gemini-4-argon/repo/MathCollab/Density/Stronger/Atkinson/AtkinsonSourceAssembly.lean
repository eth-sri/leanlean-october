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

@[expose] public section
open Complex Filter MeasureTheory Set Topology Finset MathCollab.Density.Stronger
open scoped Interval
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
  obtain ⟨hHt,htH,hlower,hupper⟩ := hrange t ht
  have hH0 : 0 < H := by linarith
  refine ⟨(Real.rpow_le_rpow hH0.le hHt hδ.le).trans hlower,?_⟩
  calc
    G ≤ t^(1/2-δ) := hupper
    _ ≤ t^(1/2:ℝ) := Real.rpow_le_rpow_of_exponent_le (hH.trans hHt) (by linarith)
    _ = Real.sqrt t := (Real.sqrt_eq_rpow t).symm
    _ ≤ Real.sqrt (2*H) := Real.sqrt_le_sqrt htH


