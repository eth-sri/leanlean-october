module

public import DedekindZetaZeroFree.Theta.Digits.ReflectedPeriodAveraging
public import DedekindZetaZeroFree.Theta.Whittaker.ExteriorTensorPeriods

@[expose] public section

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources NumberField MeasureTheory
open scoped Classical NumberField
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : PrincipalMellin.ActualRecipe S η)

abbrev restrictedLift : KPAdelicCoverRestrictedProduct.RestrictedCover F R.A.zeta12 R.A.primitive_zeta12 →* Group R :=
  (KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12).comp
    (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12)

theorem restrictedLift_commute_single
    (a : KPAdelicCoverRestrictedProduct.RestrictedCover F R.A.zeta12 R.A.primitive_zeta12)
    (p : KPFinitePlace F) (ha : a (Sum.inr p) = 1)
    (b : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p)) :
    Commute (restrictedLift R a) (finitePeriodLift R p b) := by
  apply Commute.map
  apply RestrictedProduct.ext
  intro w
  change a w * Pi.mulSingle (Sum.inr p) b w = Pi.mulSingle (Sum.inr p) b w * a w
  by_cases hw : w = Sum.inr p
  · subst w; simp [ha]
  · simp [Pi.mulSingle_eq_of_ne hw]

def sWeylTuple : KPAdelicCoverRestrictedProduct.RestrictedCover F R.A.zeta12 R.A.primitive_zeta12 :=
  ⟨fun w => match w with
    | Sum.inl u => KPStandardLocalRootLifts.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl u)
    | Sum.inr p => if p ∈ R.A.Sf then KPStandardLocalRootLifts.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) else 1,
    by
      filter_upwards [(KPRationalAdelicSplitting.WCoordinates_restricted F R.A.zeta12 R.A.primitive_zeta12)] with w hw
      cases w with
      | inl w => exact hw
      | inr p =>
        dsimp only
        split_ifs <;> first | exact hw | exact (KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p)).one_mem⟩

def exteriorWeylTuple : KPAdelicCoverRestrictedProduct.RestrictedCover F R.A.zeta12 R.A.primitive_zeta12 :=
  (sWeylTuple R)⁻¹ * KPRationalAdelicSplitting.WTuple F R.A.zeta12 R.A.primitive_zeta12

theorem exteriorWeylTuple_mem (w : KPHilbert.Place F) :
    exteriorWeylTuple R w ∈ DigitMasks.exteriorFactor R w := by
  cases w with
  | inl w =>
    change (KPStandardLocalRootLifts.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w))⁻¹ * _ ∈ (⊥ : Subgroup _)
    simp
  | inr p =>
    by_cases hp : p ∈ R.A.Sf
    · simp [exteriorWeylTuple, sWeylTuple, DigitMasks.exteriorFactor, hp]
    · change (if p ∈ R.A.Sf then KPStandardLocalRootLifts.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) else 1)⁻¹ *
        KPStandardLocalRootLifts.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) ∈ _
      rw [if_neg hp, inv_one, one_mul]
      simp only [DigitMasks.exteriorFactor, dif_pos hp]
      refine ⟨KPStandardLocalRootLifts.integralW F p, ?_⟩
      exact (KPStandardLocalRootLifts.W_eq_compact F R.A.zeta12 R.A.primitive_zeta12 p
        (fun h3 => DigitMasks.exterior_not_bad R p hp (Or.inr h3))).symm

theorem sDiagonal_exterior (y : R.A.G) (p : KPFinitePlace F) (hp : p ∉ R.A.Sf) :
    KPRationalAdelicSplitting.ATuple F R.A.zeta12 R.A.primitive_zeta12 (localIdele R y) (Sum.inr p) = 1 := by
  have he' := (DigitMasks.localIdele_exterior R y p hp)
  change KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p)
    (Units.map (KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inr p)).toMonoidHom (localIdele R y)) = 1
  rw [he', KPStandardLocalRootLifts.A_one]

end DedekindZetaZeroFree.OrbitExpansion

end
