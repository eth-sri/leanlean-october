module
public import RationalDilatedHeight
public import MathCollab.Density.Packing

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment

theorem separated_interval_card {T t₀ : ℝ} (hT : 0 ≤ T)
    (W : Finset ℝ) (hloc : ∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T))
    (hsep : ∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) :
    (W.card : ℝ) ≤ T+1 := by
  have hspan := MathCollab.Density.intervalSpan_le_of_forall hT (U := W) (by
    intro t ht u hu
    have ht' := hloc t ht
    have hu' := hloc u hu
    exact abs_le.mpr ⟨by linarith [ht'.1, hu'.2], by linarith [hu'.1, ht'.2]⟩)
  have hc := MathCollab.Density.separated_card_le_localDiameter hsep
  dsimp [MathCollab.Density.localDiameter] at hc
  linarith



