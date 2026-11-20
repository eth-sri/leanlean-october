module

public import DedekindZetaZeroFree.Eisenstein.Residues.Cofactors.LocalParameterDisplacement
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.SignedWeylCellSections

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct BigOperators
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource.CofactorChamber
open KPLocalPrincipalSeries KPGlobalTorusFiniteStages KPLocalExceptionalConstruction
open KPGlobalResidualConstruction
open KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : PrincipalMellin.ActualRecipe S η)
    (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
    (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem rationalStageEval_congr (Q Q' : Finset (KPFinitePlace F))
    (hQ : Q = Q') (h : C.exceptional ⊆ Q) (h' : C.exceptional ⊆ Q')
    (t : KPGlobalTorusFunctionData.E F ζ hζ)
    (u : ∀ q : Q, Fiber R.A P C (.inr q.val))
    (u' : ∀ q : Q', Fiber R.A P C (.inr q.val))
    (hu : ∀ q hq hq', u ⟨q,hq⟩ = u' ⟨q,hq'⟩) :
    ActualCofactor.rationalStageEval F ζ hζ P C Q h t u =
      ActualCofactor.rationalStageEval F ζ hζ P C Q' h' t u' := by
  subst Q'
  apply congrArg (ActualCofactor.rationalStageEval F ζ hζ P C Q h t)
  funext q
  exact hu q.val q.property q.property

private theorem chamber_finite_signed (q : KPFinitePlace F) (z : ℂ)
    (f : sectionSpace (C.canonical q).borel (C.polarization q) .plus z)
    (x : KPGlobalTorusFunctionData.Adeles F) :
    f.val (KPPGLLocalCover.coverQuotient F ζ hζ (.inr q) (chamberRaw F ζ hζ x (.inr q))) =
      f.val ((C.canonical q).borel.liftedW⁻¹ * (C.canonical q).borel.upperRoot
        (Multiplicative.ofAdd (x.2 q)) * 1) := by
  have hg : KPPGLLocalCover.coverQuotient F ζ hζ (.inr q) (chamberRaw F ζ hζ x (.inr q)) =
      KPPGLLocalCover.W F ζ hζ (.inr q) * (C.canonical q).borel.upperRoot
        (Multiplicative.ofAdd (x.2 q)) := by
    simp only [chamberRaw, RestrictedProduct.mul_apply,
      KPRationalAdelicSplitting.WTuple_eval, KPGlobalTorusFunctionData.rootTuple, map_mul]
    rw [KPForwardHomRepair.canonicalUpperRoot_eq F ζ hζ q
      (C.canonical q) (C.polarization q)]
    rfl
  rw [hg, mul_one]
  exact LocalSignedChamber.section_unsigned_eq_signed F ζ hζ q
    (C.canonical q) (C.polarization q) z f _

theorem box_fiber_cylinder (E Q : Finset (KPFinitePlace F)) (hE : C.exceptional ⊆ E)
    (hEQ : E ⊆ Q)
    (φ : ∀ q : E, compactPicture (C.canonical q.val).borel (C.polarization q.val)
      (C.canonical q.val).iwasawa .plus)
    (x : KPGlobalTorusFunctionData.Adeles F) (hx : x ∈ TraceBox.adelicBox F Q)
    (z : ℂ) (t : KPGlobalTorusFunctionData.E F ζ hζ) :
    (coreFlatFiber R P C (cofactorSourceCore R P C E hE φ) z
      (chamberRaw F ζ hζ x)).val.val t =
      TraceBox.archCylinder F z x.1 *
      ActualCofactor.rationalChamberIntegrand F ζ hζ P C Q (hE.trans hEQ)
        (ExteriorTensorHaar.enlargedProfiles F ζ hζ P C E Q hE φ z) t z
        (fun q => x.2 q.val) := by
  rw [box_fiber_parameter R P C E Q hE hEQ φ x hx z t,
    comparison_pure_rational R P C]
  let y := cofactorExtendedTuple R P C E hE φ (⟨Finset.univ.disjSum Q, (cofactorSourceLevel R P C Q (hE.trans hEQ)).property⟩)
  apply congrArg₂ (· * ·)
  · simp only [y, cofactorExtendedTuple, cofactorSourceLevel, Finset.inl_mem_disjSum,
      Finset.mem_univ, dite_true, cofactorSourceTuple]
    calc
      _ = ∏ a : (Finset.univ.disjSum Q).toLeft,
          (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ
            (chamberRaw F ζ hζ x (.inl a.val)).epsilon : ℂ) *
          KPComplexIntertwinerParameterMajorant.forwardSection z
            KPComplexStandardIntertwinerGerm.compactSpherical
            (complexMatrix R.A a.val (chamberRaw F ζ hζ x (.inl a.val))) := by
        apply Finset.prod_congr rfl
        intro a _
        exact complex_spherical_parameter R P C (chamberRaw F ζ hζ x) z a.val
      _ = _ := by
        exact (Fintype.prod_equiv (Equiv.subtypeUnivEquiv (fun a => by simp)) _ _ (fun a => rfl)).trans (chamberRaw_archCylinder R z x)
  · unfold ActualCofactor.rationalChamberIntegrand
    apply rationalStageEval_congr R P C _ Q (Finset.toRight_disjSum) _ _ t
    intro q hq hq'
    rw [finite_parameter_value R P C E Q hE hEQ φ (chamberRaw F ζ hζ x) z ⟨q,hq'⟩]
    exact chamber_finite_signed R P C q z _ x

end DedekindZetaZeroFree.FourierContinuation.LiteralSource.CofactorChamber

end
