module

public import DedekindZetaZeroFree.Adeles.Quotients.Cusps.CompactCrossRepresentatives
public import DedekindZetaZeroFree.Metaplectic.Kubota.RationalSplitting.ArchimedeanFiniteFactorization
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GreenIdentity.PairingsAndFluxDefinitions

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory

namespace DedekindZetaZeroFree.KPBoundedCuspFrames

open scoped Matrix
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts

variable {F : Type} [Field F] [NumberField F]
variable {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}

 def rationalHom : KPCuspArithmetic.PGL2 F →*
    KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ :=
  (QuotientGroup.lift (Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) F))
    ((KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
      (KPAdelicCoverRestrictedProduct.rationalHom F ζ hζ)) (by
        rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
        exact KPRationalAdelicSplitting.rationalScalars_le_ker F ζ hζ)).codRestrict _ (by
    intro g
    induction g using Matrix.ProjGenLinGroup.induction_on with
    | mk G => exact ⟨KPRationalAdelicSplitting.rationalPGLQuotient F G, rfl⟩)
 theorem rationalHom_out (g : KPCuspArithmetic.PGL2 F) :
    (rationalHom (ζ := ζ) (hζ := hζ) g).val =
      KPRationalAdelicSplitting.rationalPGLHom F ζ hζ
        (KPRationalAdelicSplitting.rationalPGLQuotient F g.out) := by
  conv_lhs => rw [← Quotient.out_eq g]
  rfl

def actualFiniteRepresentative (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (j : KPMsGreenFlux.Cusps A) : KPFiniteCuspAtlas.FiniteCover F ζ hζ :=
  (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ
    ((A.cuspAtlas j.1).representative j.2))⁻¹ * A.representative j.1

def actualCuspLift (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (j : KPMsGreenFlux.Cusps A) (p : KPCuspCharts.Cross F)
    (k : KPMsGreenFlux.K F) (r : ℝ) : KPMsGreenFlux.Cover F ζ hζ :=
  KPMsGreenFlux.cuspRepresentative A j *
    KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (KPMsGreenFlux.balancedArch (ζ := ζ) (hζ := hζ) p k r) *
        (actualFiniteRepresentative A j).val

 theorem rationalHom_product (g : KPCuspArithmetic.PGL2 F) :
    (rationalHom (ζ := ζ) (hζ := hζ) g).val =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map w.embedding g.out)) *
          (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ g).val := by
  rw [rationalHom_out]
  have hl : KPRationalAdelicSplitting.rationalPGLHom F ζ hζ
      (KPRationalAdelicSplitting.rationalPGLQuotient F g.out) =
      KPMsClearedTruncationL2.rationalLift F ζ hζ g := by
    have hs : g = Matrix.ProjGenLinGroup.mk g.out := (Quotient.out_eq g).symm
    conv_rhs => rw [hs, KPMsClearedTruncationL2.rationalLift_mk]
    rw [KPRationalAdelicSplitting.rationalPGLHom_mk]
    rfl
  rw [hl]
  exact KPContinuation.RationalArchFiniteSplitting.rationalLift_product F ζ hζ g

private theorem insertion_commutes_finite (a : KPSmoothActualFlowData.GInfinity F)
    (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    Commute (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a) c.val :=
  KPMsResidualTailRestoration.SharpConstantTerm.FiberStability.insertion_commutes_cover
    F ζ hζ a c

theorem actualCuspLift_arch_finite_formula
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (j : KPMsGreenFlux.Cusps A) (p : KPCuspCharts.Cross F)
    (k : KPMsGreenFlux.K F) (r : ℝ) :
    actualCuspLift A j p k r = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      ((fun w => Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map w.embedding
        ((A.cuspAtlas j.1).representative j.2).out)) *
          KPMsGreenFlux.balancedArch (ζ := ζ) (hζ := hζ) p k r) *
            (A.representative j.1).val := by
  let σ := (A.cuspAtlas j.1).representative j.2
  let a := KPMsGreenFlux.balancedArch (ζ := ζ) (hζ := hζ) p k r
  let s := KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ σ
  have hσ : KPMsGreenFlux.cuspRepresentative A j =
      (rationalHom (ζ := ζ) (hζ := hζ) σ).val := (rationalHom_out σ).symm
  unfold actualCuspLift actualFiniteRepresentative
  rw [hσ, rationalHom_product,
    (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1]
  have hs := (insertion_commutes_finite (ζ := ζ) (hζ := hζ) a s).symm
  change (_ * s.val) * _ * (s.val⁻¹ * _) = _
  rw [mul_assoc _ s.val _, hs.eq]
  dsimp only [σ, a]
  group

end DedekindZetaZeroFree.KPBoundedCuspFrames

end
