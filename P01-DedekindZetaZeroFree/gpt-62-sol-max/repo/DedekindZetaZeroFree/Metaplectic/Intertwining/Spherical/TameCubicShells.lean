module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Spherical.CubicUnitShells
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RootIndependenceAndExactness
public import DedekindZetaZeroFree.Metaplectic.Intertwining.Spherical.MeromorphicContinuation

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace DedekindZetaZeroFree.KPLocalTameIntertwiningBlock
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneTameSphericalFactor

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)

include hμ in

theorem tame_spherical_zero_shells_of_actual_compact
    (ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (hcompact : (S.iwasawa.compact.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) =
      (actualGoodCompactSplit F ζ hζ q ht).range)
    (φ : compactPicture S.borel P S.iwasawa .plus)
    (hφ : IsSphericalVector (LocalField F q) S.borel P S.iwasawa .plus φ) :
    ∀ n : ℕ, (∫ x in
      KPExceptionalRaw.FiniteSource.GoodSphericalVector.negativeValuationShell
        (LocalField F q) n,
      ((compactTrivialization S.borel P S.iwasawa .plus 0 φ).val
        (S.borel.liftedW⁻¹ *
          (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q))).val 1 ∂μ) =
      if 3 ∣ n + 1 then
        (haarMass (LocalField F q) μ : ℂ) *
        (1 - (residueCardinality (LocalField F q) : ℂ)⁻¹) *
        ((residueCardinality (LocalField F q) : ℂ)⁻¹) ^ ((n + 1) / 3) else 0 := by
  intro n
  have hf : ∀ k : KPTameCompact.K0 F q,
      IPlus S.borel P (actualGoodCompactSplit F ζ hζ q ht k)
        (compactTrivialization S.borel P S.iwasawa .plus 0 φ) =
          compactTrivialization S.borel P S.iwasawa .plus 0 φ := by
    intro k
    have hk : actualGoodCompactSplit F ζ hζ q ht k ∈ S.iwasawa.compact.toOpenSubgroup := by
      change _ ∈ (S.iwasawa.compact.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q))
      rw [hcompact]
      exact ⟨k, rfl⟩
    exact hφ.2 0 ⟨_, hk⟩
  have hs := KPExceptionalRaw.FiniteSource.GoodSphericalVector.actual_compact_spherical_negative_shell_coordinate
    F ζ hζ q (rawInducingAlias F ζ hζ q S) μ hμ ht P
    (compactTrivialization S.borel P S.iwasawa .plus 0 φ) hf n 1
  have hmass : haarMass (LocalField F q) μ = 1 := by
    simp [haarMass, hμ]
  simp only [rawInducingAlias, hφ.1 0, mul_one] at hs
  simp only [hmass, Complex.ofReal_one, one_mul]
  convert hs using 1

end DedekindZetaZeroFree.KPLocalTameIntertwiningBlock

end

end
