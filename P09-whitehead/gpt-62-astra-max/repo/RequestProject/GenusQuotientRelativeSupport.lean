module

public import RequestProject.GenusQuotientRelativeCorrection
public import RequestProject.UniversalOrderChainBridge

@[expose] public section

/-! The actual quotient correction stays over the old subposet, before and after
deck translation and conversion to nerve chains. Pending final Lean verification.
-/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

variable (S : P → Prop)

/-- Actual cover faces whose projected triangle lies in the chosen subposet. -/
noncomputable def supportedUniversalFaces :
    Submodule ℤ (UF (orderCx P) a →₀ ℤ) :=
  Finsupp.supported ℤ ℤ {t | t.1.2 ∈ ordTriOn S}

theorem mem_supportedUniversalFaces_iff
    (c : UF (orderCx P) a →₀ ℤ) :
    c ∈ supportedUniversalFaces S ↔ ∀ t ∈ c.support, t.1.2 ∈ ordTriOn S := Iff.rfl

theorem chain2_mem_supportedUniversalFaces {K : Complex2.{u}}
    (S : P → Prop) (f : Hom K (uCover (orderCx P) a))
    (hf : ∀ t, (f.onF t).1.2 ∈ ordTriOn S) (c : K.F →₀ ℤ) :
    chain2 f c ∈ supportedUniversalFaces S := by
  apply Finsupp.supported_comap_lmapDomain ℤ ℤ f.onF {t | t.1.2 ∈ ordTriOn S} <;> simp_all

/-- Deck translation changes the sheet and leaves every projected face unchanged. -/
theorem deck_mem_supportedUniversalFaces (S : P → Prop)
    (g : Pi1 (orderCx P) a) (c : UF (orderCx P) a →₀ ℤ)
    (hc : c ∈ supportedUniversalFaces S) :
    (univDeck (orderCx P) a).faceChains g c ∈ supportedUniversalFaces S := by
  apply Finsupp.supported_comap_lmapDomain ℤ ℤ _ _ <;> assumption

end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
open scoped Classical
variable (q : ℕ) [NeZero q] {α Jr : Type}
  (ρ : Jr ⊕ PUnit.{1} → FreeGroup α) (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

theorem receivedSpineToQuotient_face_old (t : (singleReceivedSpineCover q ρ u).F) :
    ((receivedSpineToQuotient q ρ u hrho).onF t).1.2 ∈ ordTriOn InQOld := by
  solve_by_elim

theorem receivedSpineToQuotient_chain_old
    (c : (singleReceivedSpineCover q ρ u).F →₀ ℤ) :
    chain2 (receivedSpineToQuotient q ρ u hrho) c ∈ supportedUniversalFaces InQOld :=
  chain2_mem_supportedUniversalFaces InQOld _
    (receivedSpineToQuotient_face_old q ρ u hrho) c

theorem oldCoverToNamedQuotient_face_old
    (t : (uCover _ _).F) :
    ((oldCoverToNamedQuotient q ρ u).onF t).1.2 ∈ ordTriOn InQOld := by
  solve_by_elim

theorem oldCoverToNamedQuotient_chain_old
    (c : (uCover _ _).F →₀ ℤ) :
    chain2 (oldCoverToNamedQuotient q ρ u) c ∈ supportedUniversalFaces InQOld :=
  chain2_mem_supportedUniversalFaces InQOld _
    (oldCoverToNamedQuotient_face_old q ρ u) c

theorem quotientMarkingCorrection_old
    (g : PresGroup _) (i : Fin q × Bool) :
    quotientMarkingCorrection q ρ u hrho g i ∈ supportedUniversalFaces InQOld :=
  deck_mem_supportedUniversalFaces InQOld _
    _
    (oldCoverToNamedQuotient_chain_old q ρ u (spineOldMarkingCorrection q i))

theorem quotientMarkingCorrections_old
    (c : (PresGroup _ × (Fin q × Bool)) →₀ ℤ) :
    quotientMarkingCorrections q ρ u hrho c ∈ supportedUniversalFaces InQOld := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => aesop
  | single x n =>
      erw [quotientMarkingCorrections, Finsupp.linearCombination_single]
      exact Submodule.smul_mem _ n (quotientMarkingCorrection_old q ρ u hrho x.1 x.2)

variable (β : NamedSpineRel q → MonoidAlgebra ℤ (PresGroup (substPresF ρ (finiteSpineWordBlock q u))))

/-- Both the received faces and the explicit marking correction are supported on old faces. -/
theorem quotientCorrectedRelativeChain_old :
    quotientCorrectedRelativeChain q ρ u hrho β ∈ supportedUniversalFaces InQOld :=
  Submodule.sub_mem _
    (receivedSpineToQuotient_chain_old q ρ u hrho _)
    (quotientMarkingCorrections_old q ρ u hrho _)

theorem quotientCorrectedRelativeChain_face_support :
    ∀ t ∈ (quotientCorrectedRelativeChain q ρ u hrho β).support,
      t.1.2 ∈ ordTriOn InQOld :=
  (mem_supportedUniversalFaces_iff InQOld _).mp
    (quotientCorrectedRelativeChain_old q ρ u hrho β)

noncomputable def quotientCorrectedRelativeNerveChain :=
  universalNerveChain2 (quotientCorrectedRelativeChain q ρ u hrho β)

theorem quotientCorrectedRelativeNerveChain_boundary
    (hβ : ∀ z : SpinePresentationGen q,
      (∑ m, β m * foxMatrixPres (substPresF ρ _)
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0) :
    Nerve.bdry (quotientCorrectedRelativeNerveChain q ρ u hrho β) =
      universalNerveChain1 (quotientSurfaceMarkingChains q ρ u hrho
        ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => β (Sum.inr i)))) := by
  simp_all [quotientCorrectedRelativeNerveChain, universalNerveChain2_bdry, quotientCorrectedRelativeChain_boundary]

end FiniteChains.Davis.Genus
