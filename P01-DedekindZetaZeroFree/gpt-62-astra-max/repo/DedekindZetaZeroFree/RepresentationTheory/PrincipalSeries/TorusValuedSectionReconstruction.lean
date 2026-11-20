module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.OppositeCompositionVanishing
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.UnramifiedSphericalImage
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.TameBruhatTestDuality

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeSectionReconstruction

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneOppositeZero KPRankOneForwardTestVector
open KPTameJacquetTestDuality
open KPTameValuationCoordinates

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (hP : IsTamePolarization F ζ hζ q S P)

private theorem scalar_retract_reduction
    (ε : Sign) (f : scalarSections F ζ hζ q S P hP ε)
    (b : S.borel.B) (g : ActualCover F ζ hζ q) :
    f.val ((b : ActualCover F ζ hζ q) * g) =
      f.val ((S.borel.torus (S.borel.retract b) : ActualCover F ζ hζ q) * g) := by apply @DedekindZetaZeroFree.KPTameJacquetTestDualityScalarization.ScalarSectionLiftsAndWhittakerDimension.borel_reduce <;> assumption

local notation "LocalCompletion" => LocalField F q

private theorem normPower_product (x y : LocalCompletionˣ) :
    normPower LocalCompletion (x * y) (1 / 2) =
      normPower LocalCompletion x (1 / 2) *
        normPower LocalCompletion y (1 / 2) := by
  simp [normPower, localAbs_mul, Real.log_mul (ne_of_gt (localAbs_pos _ x))
    (ne_of_gt (localAbs_pos _ y)), mul_add, Complex.exp_add]

theorem reconstruction_section_membership
    (ε : Sign) (f : scalarSections F ζ hζ q S P hP ε)
    (v : ActualCover F ζ hζ q → InducedModule P)
    (hv : ∀ g t, (v g).val t =
      let t' := match ε with
        | .plus => t
        | .minus => S.borel.weyl.symm t
      (normPower LocalCompletion (S.borel.coordinate t') (1 / 2))⁻¹ *
        f.val ((S.borel.torus t' : ActualCover F ζ hζ q) * g)) :
    v ∈ sectionSpace S.borel P ε 0 := by
  refine ⟨?_, ?_⟩
  · intro b g
    apply Subtype.ext
    funext t
    cases ε <;> simp only [inducingAction, inducingScalar,
      normPower, zero_mul, Complex.exp_zero, mul_one,
      LinearMap.smul_apply, deltaHalf]
    · change (v ((b : ActualCover F ζ hζ q) * g)).val t =
        normPower LocalCompletion (S.borel.coordinate (S.borel.retract b)) (1 / 2) *
          (v g).val (t * S.borel.retract b)
      rw [hv, hv]
      simp only [map_mul]
      have hf := scalar_retract_reduction F ζ hζ q S P hP Sign.plus f
        (S.borel.torus t * b) g
      simp only [map_mul, S.borel.retract_torus, Subgroup.coe_mul,
        mul_assoc] at hf
      rw [hf, normPower_product]
      have hn : normPower LocalCompletion
          (S.borel.coordinate (S.borel.retract b)) (1 / 2) ≠ 0 :=
        Complex.exp_ne_zero _
      have ht : normPower LocalCompletion (S.borel.coordinate t) (1 / 2) ≠ 0 :=
        Complex.exp_ne_zero _
      field_simp
      simp only [Subgroup.coe_mul, mul_assoc]
    · change (v ((b : ActualCover F ζ hζ q) * g)).val t =
        normPower LocalCompletion (S.borel.coordinate (S.borel.retract b)) (1 / 2) *
          (v g).val (t * S.borel.weyl (S.borel.retract b))
      rw [hv, hv]
      simp only [map_mul, S.borel.weyl.symm_apply_apply]
      have hf := scalar_retract_reduction F ζ hζ q S P hP Sign.minus f
        (S.borel.torus (S.borel.weyl.symm t) * b) g
      simp only [map_mul, S.borel.retract_torus, Subgroup.coe_mul,
        mul_assoc] at hf
      rw [hf, normPower_product]
      have hn : normPower LocalCompletion
          (S.borel.coordinate (S.borel.retract b)) (1 / 2) ≠ 0 :=
        Complex.exp_ne_zero _
      have ht : normPower LocalCompletion
          (S.borel.coordinate (S.borel.weyl.symm t)) (1 / 2) ≠ 0 :=
        Complex.exp_ne_zero _
      field_simp
      simp only [Subgroup.coe_mul, mul_assoc]
  · obtain ⟨J, hJ⟩ := f.property.2
    refine ⟨J, ?_⟩
    intro j hj
    funext g
    apply Subtype.ext
    funext t
    change (v (g * j)).val t = (v g).val t
    rw [hv, hv]
    have hf : ∀ x, f.val (x * j) = f.val x := congrFun (hJ j hj)
    cases ε <;> simp only [← mul_assoc, hf]

end DedekindZetaZeroFree.KPTameTransposeSectionReconstruction

end
