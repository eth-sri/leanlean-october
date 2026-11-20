module

public import DedekindZetaZeroFree.Eisenstein.Induction.Height.ChamberCosetBounds

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPLiteralExceptionalResidue
open KPLiteralRaw

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

alias chamberIndex := chamberCosetIndex

theorem chamberHeightBound (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K)
    (s : ℂ) (hs : (1 : ℝ) / 3 < s.re) (g : G F ζ hζ) :
    ∃ B : ℝ, ∀ c : KPChamberBruhatTwoCells.RationalQuotient F,
      ‖f.val s (rationalLift F ζ hζ (Quotient.out c) * g)‖ ≤
        B * KPHeightSeries.term (Projectivization.mulHeight (K := F))
          (2 / 3 + s.re) (chamberIndex F c) :=
  chamberCosetHeightBound F ζ hζ K hK f s hs g

theorem summable_of_chamberHeightBound {u : KPChamberBruhatTwoCells.RationalQuotient F → ℂ}
    {a : ℝ} (ha : 1 < a) {B : ℝ}
    (hB : ∀ c, ‖u c‖ ≤
      B * KPHeightSeries.term (Projectivization.mulHeight (K := F)) a (chamberIndex F c)) :
    Summable u := by
  exact Summable.of_norm (Summable.of_nonneg_of_le (fun c => norm_nonneg _) hB ((((KPHeightSeries.relativeHeight_summable_tail F a ha).1).comp_injective (chamberCosetIndex_injective F)).mul_left B))

theorem chamberConvergence (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K)
    (s : ℂ) (hs : (1 : ℝ) / 3 < s.re) (g : G F ζ hζ) :
    Summable (fun c : KPChamberBruhatTwoCells.RationalQuotient F =>
      f.val s (rationalLift F ζ hζ (Quotient.out c) * g)) := by
  obtain ⟨B, hB⟩ := chamberHeightBound F ζ hζ K hK f s hs g
  refine summable_of_chamberHeightBound F ?_ hB
  linarith

end DedekindZetaZeroFree.KPLiteralExceptionalResidue

end
