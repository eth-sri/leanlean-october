module

public import DedekindZetaZeroFree.Moments.Reflected.ProbeExponentBound
public import DedekindZetaZeroFree.Moments.Probes.MixedPhaseQuadraticHeckeFamily
public import DedekindZetaZeroFree.Arithmetic.Units.SixthPowerRepresentatives
public import DedekindZetaZeroFree.CharacterSums.Gauss.CompatibleCharactersAndSquarefreeReciprocity

@[expose] public section

namespace DedekindZetaZeroFree.MomentSources
open PrincipalMellin
open Filter Asymptotics
variable {F : Type} [Field F] [NumberField F]

structure SelectedMomentSource
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : ActualRecipe S η) where
  Ur : Finset R.A.Rˣ
  units : ActualRowTransfer.UnitRepresentatives R.A Ur
  psi : ∀ p : ThetaBranch.ExteriorPrime R.A, AddChar (DHCubic.Residue F p.val) ℂ
  primitive : ∀ p, (psi p).IsPrimitive
  L : R.A.UnitQuotient → Fˣ →* ℂ
  norm_one : ∀ v x, ‖L v x‖ = 1
  characters_compatible : PrincipalMellinSource.SourceCharacterCompatibility R psi L
  H : R.A.UnitQuotient → R.A.V → ℝ → ℂ
  profiles : RMSeparatedExpansion.FiniteProfileFamily R.A H
  reflected_domination : ∀ u ∈ Ur, ∀ h d : R.A.Exterior,
    Powerful h.val → Squarefree d.val → h.val ⊔ d.val = ⊤ →
    ∀ Z : ℝ, 0 < Z → ∃ v : R.A.UnitQuotient,
      ‖ThetaReflectionData.forwardB R.A R.probe.coefficients
        (ActualRowTransfer.dyadicRow R.A R.probe.coefficients u h d) Z‖ ^ 2 ≤
      ‖RMSeparatedExpansion.expansion R.A R.probe.allowed R.probe.unitReps
        R.σ psi (L v) (H v) h d Z‖ ^ 2
