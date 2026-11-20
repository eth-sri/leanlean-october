module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.BoundaryFlux.AngularConormalDescent
public import DedekindZetaZeroFree.Adeles.Quotients.CuspFrames.CubicCoveredRayCoordinates

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField Topology ENNReal NNReal BigOperators
open MeasureTheory
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.NormalCoefficient (action_out su_origin)
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.ActualFrames (balancedArch_eq_section)
open _root_.DedekindZetaZeroFree.KPMsFixedHaar (projective_action_mul)

namespace DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes.GradientCollar
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

 theorem balancedArch_basepoint
    (p : KPCuspCharts.Cross F) (k : K F) (r : ℝ) : KPMsFixedHaarDisintegration.archBasepoint F
      (balancedArch (ζ := ζ) (hζ := hζ) p k r) =
      KPCuspCharts.toArch F (p,KPMsFixedHaarDisintegration.logHeight (F := F) r) := by
    funext i
    change KPArch.action ((balancedArch p k r)
      (KPCusp.complexPlace F i)).out (0,0) = _
    have hk : KPArch.action (k (KPCusp.complexPlace F i)).val.out (0,0) = (0,0) := by
      obtain ⟨a,ha⟩ := (k (KPCusp.complexPlace F i)).property
      change Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding a) = _ at ha
      rw [← ha, action_out, su_origin]
    have he : balancedArch (ζ := ζ) (hζ := hζ) p k r (KPCusp.complexPlace F i) =
        balancedArch (ζ := ζ) (hζ := hζ) p 1 r (KPCusp.complexPlace F i) *
          (k (KPCusp.complexPlace F i)).val := by
      simp only [balancedArch, Pi.one_apply, OneMemClass.coe_one, mul_one]
    rw [he, projective_action_mul, hk]
    rw [balancedArch_eq_section p _ r rfl]
    exact congrFun (KPContSectorArchSphericalFibers.archBasepoint_iwasawaSection F ζ hζ
      (KPCuspCharts.toArch F (p,KPMsFixedHaarDisintegration.logHeight r))) i |>.trans
      (rfl)

end DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes.GradientCollar

end
