module

public import RequestProject.GenusSpineSubstitutedBoundary
public import RequestProject.ReceivedTreeComparison
public import RequestProject.ReceivedTreeFoxCoordinates

@[expose] public section

/-! A genuine spine cover with the actual substituted group as its sheet set. -/

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb BlockFamily
open scoped Classical
variable {A Jr S : Type} (ρ : Jr ⊕ S → FreeGroup A)
  (q : S → ℕ) [∀ s, NeZero (q s)] (u : ∀ s, Fin (q s) × Bool → FreeGroup A)

noncomputable def receivedSpineWordReceiver (s : S) : PresGroup (spinePresentation (q s)) →*
    PresGroup (spineFamilyPres ρ q u) :=
  (familySpineHom ρ q u s).comp
    (NamedPresentation.inclusion (spinePresentation (q s)) (spinePresentationMarkedWord (q s)))

noncomputable abbrev receivedSpineCover (s : S) : Complex2 :=
  ReceivedTree.cover (markedSpineTree (q s)) (receivedSpineWordReceiver ρ q u s)

/-- Its word coefficients are exactly the coefficient map in the relative Fox
boundary already proved for the substituted family. -/
theorem receivedSpineWordReceiver_coeff (s : S) (x : FreeGroupRing (SpinePresentationGen (q s))) :
    MonoidAlgebra.mapDomainRingHom ℤ (receivedSpineWordReceiver ρ q u s)
      (quotRingHom ℤ (relSub (spinePresentation (q s))) x) =
    NamedPresentation.receivedWordCoefficientMap (spinePresentation (q s))
      (spinePresentationMarkedWord (q s)) (familySpineHom ρ q u s) x := by
  unfold NamedPresentation.receivedWordCoefficientMap NamedPresentation.wordCoefficientMap
  change MonoidAlgebra.mapDomainRingHom ℤ (receivedSpineWordReceiver ρ q u s)
      (MonoidAlgebra.mapDomainRingHom ℤ
        (QuotientGroup.mk' (relSub (spinePresentation (q s)))) x) =
    MonoidAlgebra.mapDomainRingHom ℤ (familySpineHom ρ q u s)
      (MonoidAlgebra.mapDomainRingHom ℤ
        (QuotientGroup.mk' (relSub (namedSpinePresentation (q s))))
        (MonoidAlgebra.mapDomainRingHom ℤ (FreeGroup.map Sum.inl) x))
  simp only [MonoidAlgebra.mapDomainRingHom_apply_comp]
  congr 1

set_option maxHeartbeats 500000 in
theorem familySpineHom_marked (s : S) (i : Fin (q s) × Bool) :
    familySpineHom ρ q u s (QuotientGroup.mk (FreeGroup.of (Sum.inr i))) =
      QuotientGroup.mk (FreeGroup.map (Sum.inl (β := Σ s, SpinePresentationGen (q s))) (u s i)) := by
  change QuotientGroup.mk (FreeGroup.map (genEmb s)
      (blockSubst u s (FreeGroup.map Sum.swap (FreeGroup.of (Sum.inr i))))) = _
  erw [FreeGroup.map.of, Sum.swap_inr, blockSubst_of_inl]
  exact congrArg QuotientGroup.mk (FreeGroup.map.comp Sum.inl (genEmb s) (u s i))

/-- The old-face part of a named coefficient vector as an actual finite chain
in the constructed cover, with every group coefficient retained. -/
noncomputable def receivedSpineFaceChain (s : S)
    (β : NamedSpineRel (q s) → MonoidAlgebra ℤ
      (PresGroup (spineFamilyPres ρ q u))) :
    (receivedSpineCover ρ q u s).F →₀ ℤ :=
  (ReceivedTree.cellCoordinates (SpinePresentationRel (q s))).symm (fun j => β (Sum.inl j))

theorem receivedSpineFaceChain_coefficient (s : S)
    (β : NamedSpineRel (q s) → MonoidAlgebra ℤ
      (PresGroup (spineFamilyPres ρ q u))) (j : SpinePresentationRel (q s)) :
    ReceivedTree.cellCoefficient j (receivedSpineFaceChain ρ q u s β) = β (Sum.inl j) :=
  ReceivedTree.cellCoefficient_coordinates_symm _ _ _

/-- The actual two-boundary of the old face chain has the prescribed marked-word
coordinates whenever the genuine B2 internal-coordinate condition holds. -/
theorem receivedSpineFaceChain_relative_boundary (s : S)
    (β : NamedSpineRel (q s) → MonoidAlgebra ℤ
      (PresGroup (spineFamilyPres ρ q u)))
    (hβ : ∀ z : SpinePresentationGen (q s),
      (∑ m, β m * foxMatrixPres (spineFamilyPres ρ q u)
        (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩)) = 0)
    (z : SpinePresentationGen (q s)) :
    ReceivedTree.cellCoefficient z.1
      (Comb.bdry2 (receivedSpineCover ρ q u s) (receivedSpineFaceChain ρ q u s β)) =
      ∑ i, β (Sum.inr i) * NamedPresentation.receivedWordCoefficientMap
        (spinePresentation (q s)) (spinePresentationMarkedWord (q s))
        (familySpineHom ρ q u s) (fox z (spinePresentationMarkedWord (q s) i)) := by
  erw [ReceivedTree.cellCoefficient_bdry2]
  simp only [receivedSpineFaceChain_coefficient, ReceivedTree.coefficientMap,
    RingHom.comp_apply]
  change (∑ j, β (Sum.inl j) * MonoidAlgebra.mapDomainRingHom ℤ
    (receivedSpineWordReceiver ρ q u s)
    (quotRingHom ℤ (relSub (spinePresentation (q s)))
      (fox z (spinePresentation (q s) j)))) = _
  simp only [receivedSpineWordReceiver_coeff]
  exact (familySpine_internal_zero_iff ρ q u s β).mp hβ z

noncomputable abbrev singleReceivedSpineFaceChain (g : ℕ) [NeZero g]
    (σ : Jr ⊕ PUnit.{1} → FreeGroup A) (v : Fin g × Bool → FreeGroup A)
    (β : SpineCoefficients σ g v) :=
  receivedSpineFaceChain σ (fun _ : PUnit.{1} => g) (fun _ => v) PUnit.unit β

noncomputable abbrev singleReceivedSpineMarkingChain (g : ℕ) [NeZero g]
    (σ : Jr ⊕ PUnit.{1} → FreeGroup A) (v : Fin g × Bool → FreeGroup A)
    (β : SpineCoefficients σ g v) : (SpineReplacementGroup σ g v × (Fin g × Bool)) →₀ ℤ :=
  (ReceivedTree.cellCoordinates (Fin g × Bool)).symm (fun i => β (Sum.inr i))

end FiniteChains.Davis.Genus
