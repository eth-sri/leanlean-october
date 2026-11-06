module

public import DedekindZetaZeroFree.Eisenstein.Induction.LocalSphericalSections
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ComplexChartsAndSphericalSections
public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Cubic.ReciprocityAndGenuineCharacterConventions

@[expose] public section

noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.EisensteinReferenceSections.LocalCovariance
open KPGlobalTorusFiniteStages
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : CompatibleModelData F ζ hζ) (C : LocalFiberData F ζ hζ P)




















theorem finite_scalar (q : HeightOneSpectrum (𝓞 F))
    (z : (KPHilbert.Completion F (Sum.inr q))ˣ)
    (g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) :
    (LocalSeed.finite F ζ hζ P C q).val
      (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
        (KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inr q) z * g)) =
    (LocalSeed.finite F ζ hζ P C q).val
      (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) g) := by
  rw [map_mul]
  have hs : KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
      (KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inr q) z) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (MonoidHom.mem_range.mpr ⟨z, rfl⟩)
  rw [hs, one_mul]

theorem finite_central (q : HeightOneSpectrum (𝓞 F)) (e : rootsOfUnity 3 F)
    (g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) :
    (LocalSeed.finite F ζ hζ P C q).val
      (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
        (KPLocalCover.centralInjection F ζ hζ (Sum.inr q) e * g)) =
    (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ e : ℂ) •
      (LocalSeed.finite F ζ hζ P C q).val
        (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) g) := by
  let S := C.canonical q
  let B := S.openCell (C.polarization q)
  let f := LocalSeed.finite F ζ hζ P C q
  have hv := f.property.1 (S.borel.torus (B.centralTorus e))
    (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) g)
  have hs : KPLocalPrincipalSeries.inducingScalar S.borel 0
      (S.borel.torus (B.centralTorus e)) = 1 := by
    simp [KPLocalPrincipalSeries.inducingScalar, KPLocalPrincipalSeries.deltaHalf,
      KPLocalPrincipalSeries.normPower, S.borel.retract_torus, B.central_coordinate,
      KPLocalPrincipalSeries.localAbs_one]
  change f.val (_ * _) = _ at hv
  rw [B.central_eq] at hv
  change f.val _ = KPLocalPrincipalSeries.inducingScalar S.borel 0
    (S.borel.torus (B.centralTorus e)) •
      KPLocalPrincipalSeries.borelAction S.borel (C.polarization q) .plus
        (S.borel.torus (B.centralTorus e)) (f.val _) at hv
  rw [hs, one_smul, B.genuine] at hv
  rw [map_mul]
  rw [S.openCell_ordinary (C.polarization q)] at hv
  exact hv

def complexMatrix (w : InfinitePlace F)
    (g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w)) :
    KPCplxCharacterHaar.ComplexGL2 :=
  Matrix.GeneralLinearGroup.map
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom g.g

def arch (w : InfinitePlace F)
    (g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w)) : ℂ :=
  (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ g.epsilon : ℂ) *
    KPCplxPrincipalSeriesCharts.sphericalSection
      KPCplxPrincipalSeriesCharts.positiveParameter (complexMatrix F ζ hζ w g)





theorem arch_central (w : InfinitePlace F) (e : rootsOfUnity 3 F)
    (g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w)) :
    arch F ζ hζ w (KPLocalCover.centralInjection F ζ hζ (Sum.inl w) e * g) =
      (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ e : ℂ) * arch F ζ hζ w g := by
  have he : (KPLocalCover.centralInjection F ζ hζ (Sum.inl w) e * g).epsilon = e * g.epsilon := by
    change e * g.epsilon * KPLocalCover.sigmaTwo F ζ hζ (Sum.inl w) 1 g.g = _
    rw [KPLocalChartTopology.complex_sigmaTwo_eq_one, mul_one]
  have hm : complexMatrix F ζ hζ w (KPLocalCover.centralInjection F ζ hζ (Sum.inl w) e * g) =
      complexMatrix F ζ hζ w g := by
    unfold complexMatrix
    congr 1
    exact one_mul g.g
  simp only [arch, he, hm, map_mul, Units.val_mul]
  ring




























theorem arch_scalar (w : InfinitePlace F)
    (z : (KPHilbert.Completion F (Sum.inl w))ˣ)
    (g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w)) :
    arch F ζ hζ w (KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inl w) z * g) =
      arch F ζ hζ w g := by
  have he : (KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inl w) z * g).epsilon = g.epsilon := by
    change 1 * g.epsilon * KPLocalCover.sigmaTwo F ζ hζ (Sum.inl w) _ _ = _
    rw [KPLocalChartTopology.complex_sigmaTwo_eq_one]
    simp
  have hm : complexMatrix F ζ hζ w (KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inl w) z * g) =
      Matrix.GeneralLinearGroup.scalar (Fin 2)
        (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom z) * complexMatrix F ζ hζ w g := by
    unfold complexMatrix
    change Matrix.GeneralLinearGroup.map _ (_ * g.g) = _
    rw [map_mul]
    congr 1
    apply Units.ext
    ext i j
    simp [KPScalarSplitCentral.scalarHom, KPScalarSplitCentral.scalarLift,
      KPScalarSplitCentral.scalarMatrix, KPLocalCover.sectionMap,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar, Matrix.GeneralLinearGroup.map,
      Matrix.diagonal, Pi.algebraMap_def]
    split_ifs <;> simp
  unfold arch
  rw [he, hm, KPCplxPrincipalSeriesCharts.central_invariance]






































end DedekindZetaZeroFree.EisensteinReferenceSections.LocalCovariance

end
