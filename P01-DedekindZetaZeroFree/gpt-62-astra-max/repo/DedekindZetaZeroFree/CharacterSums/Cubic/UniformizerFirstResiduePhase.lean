module

public import DedekindZetaZeroFree.CharacterSums.Gauss.LocalResidueUnitHaarIntegral
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.ConductorShellSubstitution

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPTameTransposeLiteralShell
open scoped NumberField Classical Topology
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneRootParameter KPTameJacquetTestDuality
open KPTameTransposeKernelUnfolding KPTameValuationCoordinates KPTameTransposeLiteral
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))

local notation "LocalCompletion" => LocalField F q

theorem residueShellIntegrand_eq_tame_phase
    (π : LocalCompletionˣ)
    (ψ : Multiplicative LocalCompletion →* ℂˣ)
    (κ : MulChar (RawResidue F q) ℂ)
    (hκ : RawPiFirstOrientation F ζ hζ q π κ)
    (p : KPTameCompact.O F q) (hp : (p : LocalCompletion) = π)
    (j : ZMod 3) (u : (KPTameCompact.O F q)ˣ) :
    KPTameGauss.residueShellIntegrand κ
      (AddChar.toMonoidHomEquiv.symm ((Units.coeHom ℂ).comp ψ)) p j
      ((KPTameCompact.unitInclusion F q) u) =
    (ordinaryIota F ζ hζ
      (KPHilbert.B3 F ζ hζ (Sum.inr q) π
        ((KPTameCompact.unitInclusion F q) u)) : ℂ) ^ j.val *
      (ψ (Multiplicative.ofAdd
        (((KPTameCompact.unitInclusion F q) u : LocalCompletion) /
          (π : LocalCompletion))) : ℂ) := by
  have hu : ((KPTameCompact.unitInclusion F q) u : LocalCompletion) ∈
      ((valuation LocalCompletion).integer : Subring LocalCompletion) :=
    (u : KPTameCompact.O F q).property
  simp only [KPTameGauss.residueShellIntegrand, dif_pos hu]
  rw [hp]
  change κ (IsLocalRing.residue (KPTameCompact.O F q) u) ^ j.val * _ = _
  rw [hκ u]
  rfl

theorem isClosed_integerUnitShell :
    IsClosed (KPTameGauss.integerUnitShell LocalCompletion) := by
  have he : KPTameGauss.integerUnitShell LocalCompletion =
      {u | valuation LocalCompletion u = 1} := by
    ext u
    constructor
    · rintro ⟨u, rfl, hu⟩
      exact (Valuation.integer.integers (valuation LocalCompletion)).isUnit_iff_valuation_eq_one.mp hu
    · intro hu
      exact ⟨⟨u, hu.le⟩, rfl,
        (Valuation.integer.integers (valuation LocalCompletion)).isUnit_iff_valuation_eq_one.mpr hu⟩
  rw [he]
  letI : TopologicalSpace (ValueGroupWithZero LocalCompletion) := WithZeroTopology.topologicalSpace
  letI : T5Space (ValueGroupWithZero LocalCompletion) := WithZeroTopology.t5Space
  exact (isClosed_singleton).preimage
    (IsValuativeTopology.continuous_valuation)

theorem measurable_integerUnitShell :
    MeasurableSet (KPTameGauss.integerUnitShell LocalCompletion) :=
  (isClosed_integerUnitShell F q).measurableSet

end DedekindZetaZeroFree.KPTameTransposeLiteralShell

end
