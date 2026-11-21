module

public import DedekindZetaZeroFree.Algebra.RationalEvaluation

public import DedekindZetaZeroFree.Metaplectic.Intertwining.CubicResidueRegularValues

@[expose] public section

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel

namespace DedekindZetaZeroFree.KPActualScalarBinding.ResidueSteps

open KPLocalStoneVonNeumann KPRankOneCubicResidueReduction
open KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneGenericComposition KPRankOneRootParameter

noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

open RationalEvaluation

theorem regular_point_residue
    (S : ActualKPBinding F ζ hζ q) (P : Polarization S.heisenberg)
    (dx : Measure (KPExceptionalRaw.LocalField F q)) [dx.IsAddHaarMeasure]
    (hμ : 0 < integerMass (KPExceptionalRaw.LocalField F q) dx)
    (ω : (valuation (KPExceptionalRaw.LocalField F q)).integer)
    (hω : IsPrimitiveRoot ω 3) :
    ∀ (s z : ℂ), z ≠ 0 → z ^ 3 = t (KPExceptionalRaw.LocalField F q) s →
      denominator (KPExceptionalRaw.LocalField F q) .plus s ≠ 0 →
      denominator (KPExceptionalRaw.LocalField F q) .minus s ≠ 0 →
      ∀ (J : CompactOpenLevel (KPExceptionalRaw.ActualCover F ζ hζ q)),
        (J.toOpenSubgroup : Subgroup (KPExceptionalRaw.ActualCover F ζ hζ q)) ≤
          S.iwasawa.compact.toOpenSubgroup →
        ∀ (p : LevelLaurentOperator (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .plus)
          (pRev : LevelLaurentOperator (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .minus),
        IsLevelNumerator (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J dx .plus p →
        IsLevelNumerator (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J dx .minus pRev →
        (continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .minus pRev s).comp
          (continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .plus p s) =
            residueScalar (KPExceptionalRaw.LocalField F q) dx z • LinearMap.id ∧
        (continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .plus p s).comp
          (continuedLevel (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .minus pRev s) =
            residueScalar (KPExceptionalRaw.LocalField F q) dx z • LinearMap.id := by
  intro s z hz hzt hdplus hdminus J hJ p pRev hp hpRev
  let K := KPExceptionalRaw.LocalField F q
  obtain ⟨α,hα⟩ := IsAlgClosed.exists_pow_nat_eq (residueCardinality K : ℂ) (by decide : 0 < 6)
  have hq0 : (residueCardinality K : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField (Valuation.integer (valuation K)))).ne'
  have hα0 : α ≠ 0 := by
    intro he
    rw [he,zero_pow (by decide)] at hα
    exact hq0 hα.symm
  let w := r K s / α
  have hr0 : r K s ≠ 0 := Complex.exp_ne_zero _
  have hw0 : w ≠ 0 := div_ne_zero hr0 hα0
  have hroot : α * w = r K s := by dsimp [w]; field_simp
  have htw : w^6 = t K s := by
    dsimp [w]
    rw [div_pow,hα]
    unfold t
    ring
  have ht1 : t K s ≠ 1 := by
    intro he
    apply hdplus
    change 1 - t K s = 0
    rw [he,sub_self]
  have hw6 : w^6 ≠ 1 := htw ▸ ht1
  have hsc := ActualShellPort.residue_scalar_regular_evaluation (KPExceptionalRaw.LocalField F q) dx w hw0 hw6
  have hsz : residueScalar K dx (w^2) = residueScalar K dx z := by
    unfold residueScalar
    exact KPRankoneCubicScalarSum.finiteScalar_cube_root_independent K ω.val
      (hω.map_of_injective (f := (valuation K).integer.subtype) Subtype.val_injective) (integerMass K dx) (KPCubicHaar.abs K (3 : K))
      (w^2) z (t K s) (pow_ne_zero _ hw0) hz (by rw [← pow_mul]; exact htw) hzt ht1
  have hforward := forward_two_cell_residue F ζ hζ q S P dx hμ ω hω α hα J hJ p pRev hp hpRev
  have hreverse := reverse_two_cell_residue F ζ hζ q S P dx hμ ω hω α hα J hJ p pRev hp hpRev
  have hplus := KPActualResidueSources.actual_level_composition_specialize_regular
    F ζ hζ q S P dx J hJ α hα p pRev (rationalResidueScalar K dx) .plus s w
      hw0 hroot hdplus hdminus hsc.1 (by simpa only [ite_true, KPRankOneGenericComposition.rationalStandard, KPRankOneGeneric.rationalStandard, KPRankOneGenericComposition.rationalDenominator, KPRankOneGeneric.rationalDenominator] using hforward)
  have hminus := KPActualResidueSources.actual_level_composition_specialize_regular
    F ζ hζ q S P dx J hJ α hα p pRev (rationalResidueScalar K dx) .minus s w
      hw0 hroot hdplus hdminus hsc.1 (by simpa only [show Sign.minus ≠ Sign.plus from by decide,ite_false, KPRankOneGenericComposition.rationalStandard, KPRankOneGeneric.rationalStandard, KPRankOneGenericComposition.rationalDenominator, KPRankOneGeneric.rationalDenominator] using hreverse)
  rw [hsc.2,hsz] at hplus hminus
  exact ⟨hplus,hminus⟩

end
end DedekindZetaZeroFree.KPActualScalarBinding.ResidueSteps
