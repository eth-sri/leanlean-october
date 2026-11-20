/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthFrame
public import VaughtConjecture.Knight.PaddedOwnerRepair
public import VaughtConjecture.Knight.GrowthPaddedStepDecode
public import VaughtConjecture.Knight.PaddedTowerChart

/-! # Constructed higher donor owner-capped repair

The actual chart supplies lawful source-cut factorization. The pre-activation donor fibre
and supported decoder construct the replacement and every external-cap receipt.
-/

/- Adapted from LowOnlyPaddedStepPrivateRepair using growth admission. -/
@[expose] public section

namespace VaughtConjecture.Knight.GrowthPaddedStepDonorRepair
open Transform Value ExtOrd CappedDonor Growth CanonicalPairedInverse
open GrowthPaddedContract PaddedTower.Step GrowthOrderedBase
open GrowthPaddedStepDecode PaddedTower.Step SharpWitnessComposition
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : I.GrowthData}
  {frame : I.GrowthFrame X} {k : ℕ}
  (P : Layer frame k) (hk : 1 ≤ k) (hnext : k + 1 ≤ A.card)

theorem donor_grade (d : I.left.scheme.below (Finset.univ, k + 1)) :
    (carrier P hnext).grade (donorAt P hnext d).1 =
      I.left.scheme.grade d.1 := by
  exact (congrArg Prod.snd (original_index P hnext
    (I.leftFace.map d.1))).trans (congrArg Prod.snd (I.leftFace.index d.1))

/-- A supplied original owner identifies the actual donor lower domain.
The final lifting theorem chooses a maximal such owner from the prescription. -/
theorem owner_capped (hN : k + 1 < X.req.N)
    (c : I.left.scheme.below (Finset.univ, k + 1))
    (hc : I.left.scheme.cell c.1 = (Finset.univ, k + 1)) (hg : I.left.scheme.grade c.1 = (k + 1))
    {p : I.left.scheme.below (Finset.univ, k + 1) → ExtOrd}
    {q : (carrier P hnext).below (A, (k + 1)) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, k + 1) p)
    (hq : RespectsSemanticsBelow (rows P hk hnext) (A, (k + 1)) q)
    {γ : ExtOrd} (hγ : SelfVis (k + 1) γ) (hpos : ⊥ < γ) (hactive : γ < p c)
    (hag : ∀ d, min (q (donorAt P hnext d)) γ = min (p d) γ) :
    (rows P hk hnext).FaceLift (donorAt P hnext) (fun d => min (p d) (p c)) q γ := by
  classical
  obtain ⟨a, σ, H, hσ, hmax, hread⟩ := PaddedTower.Step.exists_chart P hk hnext hq
  have hreach : γ ≤ H := by
    have he := hag c
    rw [min_eq_right hactive.le] at he
    exact (he.ge.trans (min_le_left _ _)).trans
      (hmax _ ((donor_grade P hnext c).trans hg))
  have hchart (d) : min (σ (source P hk hnext a d.1)) γ = min (q d) γ := by
    rw [hread, min_assoc, min_eq_right hreach]
  obtain ⟨S, hS, he⟩ := a.property.2
  change S.profile = a.val at he
  have hcanon : S.profile ∈
      CanonicalPairedProfiles.inventory (Field I.right.scheme I.left.scheme) (k + 1) :=
    he.symm ▸ a.property.1
  have ha : (⟨S.profile, hcanon, S, hS, rfl⟩ : Catalogue X (k + 1)) = a := Subtype.ext he
  have hdonor (d : I.left.scheme.below (Finset.univ, k + 1)) :
      source P hk hnext a (donorAt P hnext d).1 = S.donorValues d.1 := by
    change source P hk hnext a
      (original P hnext (I.leftFace.map d.1)) = _
    rw [source_original]
    change a.val (GrowthOrderedBase.field I (I.leftFace.map d.1)) = S.donorValues d.1
    rw [← he]
    exact GrowthOrderedBase.field_donor I S d.1
  refine PrivateRowFactorization.repairOwner c hc hg _ hS.donor_lawful hp hq hdonor
    (fun d => CanonicalPairedProfiles.inventory_coded _ _ hcanon (.inr d.1))
    (fun d => source_short P hk hnext a d.1) hσ hγ hpos hactive hchart hag ?_
  intro b hb v hv heq
  rw [← ha]
  exact donor_source_repair P hk hnext hN hS hcanon hb hv heq

end
end VaughtConjecture.Knight.GrowthPaddedStepDonorRepair
