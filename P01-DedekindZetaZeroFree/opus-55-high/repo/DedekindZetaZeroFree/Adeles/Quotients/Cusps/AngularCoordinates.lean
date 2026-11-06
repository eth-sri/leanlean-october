module

public import DedekindZetaZeroFree.Eisenstein.Induction.BorelModulusAndIwasawaContinuity
public import DedekindZetaZeroFree.Adeles.Quotients.Cusps.CuspFrames

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Classical NumberField Topology NNReal
namespace DedekindZetaZeroFree.KPMsActualAngularSource
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
abbrev G := KPGlobalTorusFunctionData.G F ζ hζ
abbrev Level := KPGlobalTorusFunctionData.FiniteLevel F ζ hζ
abbrev Iwasawa := KPGlobalTorusBorelTwistCompatibility.IwasawaData F ζ hζ
abbrev NormOne (D : Iwasawa F ζ hζ) :=
  {g : G F ζ hζ // KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D g = 1}

def angularRelation (D : Iwasawa F ζ hζ) (U : Level F ζ hζ)
    (g g' : NormOne F ζ hζ D) : Prop :=
  ∃ (y : Fˣ) (x : KPGlobalTorusFunctionData.Adeles F)
    (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U),
    g'.val = ((KPGlobalTorusFunctionData.s F ζ hζ y).val *
      KPGlobalTorusFunctionData.N F ζ hζ x) * g.val * u.val

def angularSetoid (D : Iwasawa F ζ hζ) (U : Level F ζ hζ) :
    Setoid (NormOne F ζ hζ D) where
  r := Relation.EqvGen (angularRelation F ζ hζ D U)
  iseqv := ⟨Relation.EqvGen.refl, fun h => Relation.EqvGen.symm _ _ h,
    fun h k => Relation.EqvGen.trans _ _ _ h k⟩

abbrev Omega (D : Iwasawa F ζ hζ) (U : Level F ζ hζ) :=
  Quotient (angularSetoid F ζ hζ D U)
instance (D : Iwasawa F ζ hζ) (U : Level F ζ hζ) :
    MeasurableSpace (Omega F ζ hζ D U) := borel _

def fullAngularSetoid (D : Iwasawa F ζ hζ) : Setoid (NormOne F ζ hζ D) where
  r := Relation.EqvGen (fun g g' => ∃ (y : Fˣ) (x : KPGlobalTorusFunctionData.Adeles F),
    g'.val = ((KPGlobalTorusFunctionData.s F ζ hζ y).val *
      KPGlobalTorusFunctionData.N F ζ hζ x) * g.val)
  iseqv := ⟨Relation.EqvGen.refl, fun h => Relation.EqvGen.symm _ _ h,
    fun h k => Relation.EqvGen.trans _ _ _ h k⟩
abbrev FullOmega (D : Iwasawa F ζ hζ) := Quotient (fullAngularSetoid F ζ hζ D)
instance (D : Iwasawa F ζ hζ) : MeasurableSpace (FullOmega F ζ hζ D) := borel _

def fullToLevel (D : Iwasawa F ζ hζ) (U : Level F ζ hζ) :
    FullOmega F ζ hζ D → Omega F ζ hζ D U := by
  refine Quotient.lift (fun g => Quotient.mk (angularSetoid F ζ hζ D U) g) ?_
  intro a b hab
  apply Quotient.sound
  have hrel : ∀ a b, (fullAngularSetoid F ζ hζ D).r a b →
      (angularSetoid F ζ hζ D U).r a b := by
    apply Relation.EqvGen.mono
    rintro g g' ⟨y, x, h⟩
    exact ⟨y, x, 1, by simpa using h⟩
  exact hrel a b hab

theorem fullToLevel_mk (D : Iwasawa F ζ hζ) (U : Level F ζ hζ)
    (g : NormOne F ζ hζ D) :
    fullToLevel F ζ hζ D U (Quotient.mk _ g) = Quotient.mk _ g := rfl

structure SourceRecipe
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P) where
  iwasawa : Iwasawa F ζ hζ
  atlasLevel : Level F ζ hζ → KPMsFixedHaarDisintegration.Level F ζ hζ
  level_matching : ∀ U, KPGlobalTorusFunctionData.globalLevel F ζ hζ U =
    (atlasLevel U).toOpenSubgroup.toSubgroup.map (KPFiniteCuspAtlas.FiniteCover F ζ hζ).subtype
  height_normalized : ∀ U
    (j : KPMsFixedHaarDisintegration.CuspIndex (H.atlas (atlasLevel U)))
    (a : KPSmoothActualFlowData.GInfinity F) (p : KPCuspCharts.Cross F)
    (t : ℝ) (ε : rootsOfUnity 3 F)
    (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U),
    KPMsFixedHaarDisintegration.archBasepoint F a =
      KPCuspSiegel.action F (((H.atlas (atlasLevel U)).cuspAtlas j.1).representative j.2)
        (KPCuspCharts.toArch F (p,t)) →
    ((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ iwasawa
      ((KPMsActualCuspSource.rationalLift F ζ hζ
        (((H.atlas (atlasLevel U)).cuspAtlas j.1).representative j.2))⁻¹ *
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
          ((H.atlas (atlasLevel U)).representative j.1).val *
          KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val)) : ℝ≥0) : ℝ) =
      Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t)

def framedRadius (D : Iwasawa F ζ hζ) (σ g : G F ζ hζ) :
    KPMsFixedHaarDisintegration.Radius :=
  ⟨((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D (σ⁻¹ * g) : ℝ≥0) : ℝ),
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))⟩

def framedNormalization (D : Iwasawa F ζ hζ)
    (B : KPMsFixedHaarDisintegration.RadialData F ζ hζ) (σ g : G F ζ hζ) : G F ζ hζ :=
  (KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot
    (framedRadius F ζ hζ D σ g))⁻¹ * (σ⁻¹ * g)

theorem framedNormalization_normOne_continuous (D : Iwasawa F ζ hζ)
    (B : KPMsFixedHaarDisintegration.RadialData F ζ hζ) (σ : G F ζ hζ) :
    (∀ g, KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D
      (framedNormalization F ζ hζ D B σ g) = 1) ∧
    Continuous (framedNormalization F ζ hζ D B σ) := by
  constructor
  · intro g
    let r := framedRadius F ζ hζ D σ g
    let t := KPGlobalTorusFunctionData.torusArchChart F ζ hζ
      (KPMsFixedHaarDisintegration.positiveSlots F B.slot r)
    have hd : KPGlobalTorusFunctionData.delta F ζ hζ t =
        KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D (σ⁻¹ * g) := by
      apply Units.ext
      apply NNReal.eq
      change (((KPGlobalTorusFunctionData.ideleAbs F
        (KPGlobalTorusFunctionData.p F ζ hζ t) : ℝ≥0) : ℝ)) = r.val
      rw [B.lift_ratio, B.ell_norm]
    change KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D
      (t⁻¹.val * (σ⁻¹ * g)) = 1
    have hn : KPGlobalTorusFunctionData.N F ζ hζ 0 = 1 :=
      (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
    have he := KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_borel_mul
      F ζ hζ D t⁻¹ 0 (σ⁻¹ * g)
    simpa only [hn, mul_one, map_inv, hd, inv_mul_cancel] using he
  · have hframe : Continuous (fun g : G F ζ hζ => σ⁻¹ * g) :=
      continuous_const.mul continuous_id
    have hr : Continuous (framedRadius F ζ hζ D σ) :=
      ((KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent.fullCusp_iwasawaNorm_continuous
        F ζ hζ D).comp hframe).subtype_mk _
    exact ((B.continuous_section.comp hr).inv).mul hframe
