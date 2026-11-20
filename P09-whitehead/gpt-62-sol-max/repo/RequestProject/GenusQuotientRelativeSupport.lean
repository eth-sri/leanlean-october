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

/-- Actual cover faces whose projected triangle lies in the chosen subposet. -/
noncomputable def supportedUniversalFaces (S : P → Prop) :
    Submodule ℤ (UF (orderCx P) a →₀ ℤ) :=
  Finsupp.supported ℤ ℤ {t | t.1.2 ∈ ordTriOn S}

theorem mem_supportedUniversalFaces_iff (S : P → Prop)
    (c : UF (orderCx P) a →₀ ℤ) :
    c ∈ supportedUniversalFaces S ↔ ∀ t ∈ c.support, t.1.2 ∈ ordTriOn S := Iff.rfl

theorem chain2_mem_supportedUniversalFaces {K : Complex2.{u}}
    (S : P → Prop) (f : Hom K (uCover (orderCx P) a))
    (hf : ∀ t, (f.onF t).1.2 ∈ ordTriOn S) (c : K.F →₀ ℤ) :
    chain2 f c ∈ supportedUniversalFaces S := by
  apply Finsupp.supported_comap_lmapDomain ℤ ℤ f.onF {t | t.1.2 ∈ ordTriOn S}
  intro t _
  exact hf t

/-- Deck translation changes the sheet and leaves every projected face unchanged. -/
theorem deck_mem_supportedUniversalFaces (S : P → Prop)
    (g : Pi1 (orderCx P) a) (c : UF (orderCx P) a →₀ ℤ)
    (hc : c ∈ supportedUniversalFaces S) :
    (univDeck (orderCx P) a).faceChains g c ∈ supportedUniversalFaces S := by
  apply Finsupp.supported_comap_lmapDomain ℤ ℤ (deckF g) {t | t.1.2 ∈ ordTriOn S}
  exact hc

end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
open scoped Classical
variable (q : ℕ) [NeZero q] {α Jr : Type}
  (ρ : Jr ⊕ PUnit.{1} → FreeGroup α) (u : Fin q × Bool → FreeGroup α)
  (hrho : IsSpineRelator ρ q u)

theorem receivedSpineToQuotient_face_old (t : (singleReceivedSpineCover q ρ u).F) :
    ((receivedSpineToQuotient q ρ u hrho).onF t).1.2 ∈ ordTriOn InQOld := by
  tauto

theorem receivedSpineToQuotient_chain_old
    (c : (singleReceivedSpineCover q ρ u).F →₀ ℤ) :
    chain2 (receivedSpineToQuotient q ρ u hrho) c ∈ supportedUniversalFaces InQOld :=
  chain2_mem_supportedUniversalFaces InQOld (receivedSpineToQuotient q ρ u hrho)
    (receivedSpineToQuotient_face_old q ρ u hrho) c

theorem oldCoverToNamedQuotient_face_old
    (t : (uCover (spineOldCx q) (spineOldBase q)).F) :
    ((oldCoverToNamedQuotient q ρ u).onF t).1.2 ∈ ordTriOn InQOld := by
  change (oldIntoNamedQuotient q ρ u).onF t.1.2 ∈ ordTriOn InQOld
  tauto

theorem oldCoverToNamedQuotient_chain_old
    (c : (uCover (spineOldCx q) (spineOldBase q)).F →₀ ℤ) :
    chain2 (oldCoverToNamedQuotient q ρ u) c ∈ supportedUniversalFaces InQOld :=
  chain2_mem_supportedUniversalFaces InQOld (oldCoverToNamedQuotient q ρ u)
    (oldCoverToNamedQuotient_face_old q ρ u) c

theorem quotientMarkingCorrection_old
    (g : SpineReplacementGroup ρ q u) (i : Fin q × Bool) :
    quotientMarkingCorrection q ρ u hrho g i ∈ supportedUniversalFaces InQOld :=
  deck_mem_supportedUniversalFaces InQOld (finiteSpineToQuotient ρ q u hrho g)
    (chain2 (oldCoverToNamedQuotient q ρ u) (spineOldMarkingCorrection q i))
    (oldCoverToNamedQuotient_chain_old q ρ u (spineOldMarkingCorrection q i))

theorem quotientMarkingCorrections_old
    (c : (SpineReplacementGroup ρ q u × (Fin q × Bool)) →₀ ℤ) :
    quotientMarkingCorrections q ρ u hrho c ∈ supportedUniversalFaces InQOld := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa only [map_add] using Submodule.add_mem _ hc hd
  | single x n =>
      erw [quotientMarkingCorrections, Finsupp.linearCombination_single]
      exact Submodule.smul_mem _ n (quotientMarkingCorrection_old q ρ u hrho x.1 x.2)

/-- Both the received faces and the explicit marking correction are supported on old faces. -/
theorem quotientCorrectedRelativeChain_old
    (β : SpineCoefficients ρ q u) :
    quotientCorrectedRelativeChain q ρ u hrho β ∈ supportedUniversalFaces InQOld :=
  Submodule.sub_mem _
    (receivedSpineToQuotient_chain_old q ρ u hrho _)
    (quotientMarkingCorrections_old q ρ u hrho _)

theorem quotientCorrectedRelativeChain_face_support
    (β : SpineCoefficients ρ q u) :
    ∀ t ∈ (quotientCorrectedRelativeChain q ρ u hrho β).support,
      t.1.2 ∈ ordTriOn InQOld :=
  (mem_supportedUniversalFaces_iff InQOld _).mp
    (quotientCorrectedRelativeChain_old q ρ u hrho β)

noncomputable def quotientCorrectedRelativeNerveChain
    (β : SpineCoefficients ρ q u) :
    Ch (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u)) :=
  universalNerveChain2 (quotientCorrectedRelativeChain q ρ u hrho β)

theorem quotientCorrectedRelativeNerveChain_boundary
    (β : SpineCoefficients ρ q u)
    (hβ : SpineInternalCycle ρ q u β) :
    Nerve.bdry (quotientCorrectedRelativeNerveChain q ρ u hrho β) =
      universalNerveChain1 (quotientSurfaceMarkingChains q ρ u hrho
        (singleReceivedSpineMarkingChain q ρ u β)) := by
  erw [quotientCorrectedRelativeNerveChain, universalNerveChain2_bdry,
    quotientCorrectedRelativeChain_boundary q ρ u hrho β hβ]

end FiniteChains.Davis.Genus
