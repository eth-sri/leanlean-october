import RequestProject.GenusSpineSubstitutedBoundary
import RequestProject.ReceivedTreeComparison
import RequestProject.ReceivedTreeFoxCoordinates
import RequestProject.Tac
noncomputable section


/-! A genuine spine cover with the actual substituted group as its sheet set. -/
bwd

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb BlockFamily
open scoped Classical
variable {A Jr S : Type} (ρ : Jr ⊕ S → FreeGroup A)
  (q : S → ℕ) [∀ s, NeZero (q s)] (u : ∀ s, Fin (q s) × Bool → FreeGroup A)

def receivedSpineWordReceiver s :=
  (familySpineHom ρ q u s).comp
    (NamedPresentation.inclusion _ _)

abbrev receivedSpineCover (s : S) :=
  ReceivedTree.cover _ (receivedSpineWordReceiver ρ q u s)

/-- Its word coefficients are exactly the coefficient map in the relative Fox
boundary already proved for the substituted family. -/
theorem receivedSpineWordReceiver_coeff s (x : FreeGroupRing (SpinePresentationGen (q s))) :
    MonoidAlgebra.mapDomainRingHom ℤ (receivedSpineWordReceiver ρ q u s)
      (quotRingHom ℤ (relSub (spinePresentation (q s))) x) =
    NamedPresentation.receivedWordCoefficientMap (spinePresentation (q s))
      (spinePresentationMarkedWord (q s)) (familySpineHom ρ q u s) x := by
  change MonoidAlgebra.mapDomainRingHom ℤ (receivedSpineWordReceiver ρ q u s)
      (MonoidAlgebra.mapDomainRingHom ℤ
        (QuotientGroup.mk' _) x) =
    MonoidAlgebra.mapDomainRingHom ℤ (familySpineHom ρ q u s)
      (MonoidAlgebra.mapDomainRingHom ℤ
        (QuotientGroup.mk' _)
        (MonoidAlgebra.mapDomainRingHom ℤ (FreeGroup.map Sum.inl) x))
  simp only [BlockMor.mapDomainRingHom_comp']
  congr 1

set_option maxHeartbeats 500000 in
theorem familySpineHom_marked (s : S) (i : Fin (q s) × Bool) :
    familySpineHom ρ q u s (QuotientGroup.mk (FreeGroup.of (Sum.inr i))) =
      QuotientGroup.mk (FreeGroup.map (Sum.inl (β := Σ s, SpinePresentationGen (q s))) (u s i)) := by
  change QuotientGroup.mk (FreeGroup.map (genEmb s)
      (blockSubst u s (FreeGroup.map Sum.swap (FreeGroup.of (Sum.inr i))))) = _
  rwd [FreeGroup.map.of, Sum.swap_inr, blockSubst_of_inl]
  have h : (FreeGroup.map (genEmb (α := A) (Zt := fun s => SpinePresentationGen (q s)) s)).comp
      (FreeGroup.map (Sum.inl (β := SpinePresentationGen (q s)))) =
      FreeGroup.map (Sum.inl (β := Σ s, SpinePresentationGen (q s))) := by
    aesop
  exact congrArg QuotientGroup.mk (DFunLike.congr_fun h _)

/-- The old-face part of a named coefficient vector as an actual finite chain
in the constructed cover, with every group coefficient retained. -/
def receivedSpineFaceChain s
    (β : NamedSpineRel (q s) → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (familyFiniteSpineWordBlock q u)))) :
    (receivedSpineCover ρ q u s).F →₀ ℤ :=
  (ReceivedTree.cellCoordinates _).symm (fun j => β (Sum.inl j))

theorem receivedSpineFaceChain_coefficient s
    β (j : SpinePresentationRel (q s)) :
    ReceivedTree.cellCoefficient j (receivedSpineFaceChain ρ q u s β) = β (Sum.inl j) :=
  ReceivedTree.cellCoefficient_coordinates_symm _ _ _

/-- The actual two-boundary of the old face chain has the prescribed marked-word
coordinates whenever the genuine B2 internal-coordinate condition holds. -/
theorem receivedSpineFaceChain_relative_boundary s
    β
    (hβ : ∀ z,
      (∑ m, β m * foxMatrixPres (substPresF ρ (familyFiniteSpineWordBlock q u))
        (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩)) = 0)
    z :
    ReceivedTree.cellCoefficient z.1
      (Comb.bdry2 (receivedSpineCover ρ q u s) (receivedSpineFaceChain ρ q u s β)) =
      ∑ i, β (Sum.inr i) * NamedPresentation.receivedWordCoefficientMap
        (spinePresentation (q s)) (spinePresentationMarkedWord (q s))
        (familySpineHom ρ q u s) (fox z (spinePresentationMarkedWord (q s) i)) := by
  rwd [ReceivedTree.cellCoefficient_bdry2]
  simp [receivedSpineFaceChain_coefficient, ReceivedTree.coefficientMap,
    RingHom.comp_apply]
  change (∑ j, β (Sum.inl j) * MonoidAlgebra.mapDomainRingHom ℤ
    (receivedSpineWordReceiver ρ q u s)
    (quotRingHom ℤ _
      (fox z (spinePresentation _ j)))) = _
  simp only [receivedSpineWordReceiver_coeff]
  exact (familySpine_internal_zero_iff ρ q u s β).mp hβ z
