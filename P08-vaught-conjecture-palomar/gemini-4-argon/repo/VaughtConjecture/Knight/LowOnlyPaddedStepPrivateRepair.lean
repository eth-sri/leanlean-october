/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedStepDecode
public import VaughtConjecture.Knight.LowOnlyPaddedStepCharts

/-! # Constructed higher private owner-capped repair

The actual chart supplies lawful source-cut factorization. The private fibre
and supported decoder construct the replacement and every external-cap receipt.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.LowOnlyPaddedStepPrivateRepair
open Transform Value ExtOrd CappedDonor LowOnly CanonicalPairedInverse LowOnlyPaddedContract LowOnlyPaddedStepRows LowOnlyOrderedLadder
open LowOnlyPaddedStepDecode LowOnlyPaddedStepCharts SharpWitnessComposition

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  {I : WholeDonorBoundary.Input A B C R m n n} {F : LowOnly.Family I.left I.right K}
  {hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I F hroot hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

theorem private_grade (d : I.right.scheme.below (effC n (k + 1))) :
    (carrier P hnext).grade (privateAt P hnext d).1 = I.right.scheme.grade d.1 :=
  (congrArg Prod.snd (original_index P hnext (I.rightFace.map d.1))).trans
    (congrArg Prod.snd (I.rightFace.index d.1))

theorem owner_capped
    (c : I.right.scheme.below (effC n (k + 1)))
    (hc : I.right.scheme.cell c.1 = effC n (k + 1)) (hg : I.right.scheme.grade c.1 = (k + 1))
    {p : I.right.scheme.below (effC n (k + 1)) → ExtOrd}
    {q : (carrier P hnext).below (A, (k + 1)) → ExtOrd}
    (hp : RespectsSemanticsBelow I.right.rows (effC n (k + 1)) p)
    (hq : RespectsSemanticsBelow (rows P hk hnext) (A, (k + 1)) q)
    {γ : ExtOrd} (hγ : SelfVis (k + 1) γ) (hpos : ⊥ < γ) (hactive : γ < p c)
    (hag : ∀ d, min (q (privateAt P hnext d)) γ = min (p d) γ) :
    ∃ u, RespectsSemanticsBelow (rows P hk hnext) (A, (k + 1)) u ∧
      (∀ d, u (privateAt P hnext d) = min (p d) (p c)) ∧
      (∀ d, min (u d) γ = min (q d) γ) ∧ (∀ d, u d ≤ p c) := by
  classical
  obtain ⟨a, σ, H, hσ, hmax, hread⟩ := LowOnlyPaddedStepCharts.exists_chart P hk hnext hq
  obtain ⟨S, hS, he⟩ := a.property.2
  have hcanon : S.profile ∈ CanonicalPairedProfiles.inventory (Field I.left I.right) (k + 1) :=
    he.symm ▸ a.property.1
  exact PrivateRowFactorization.owner_capped_of_chart (Fintype.card (Field I.left I.right))
    (private_grade P hnext) c hc hg hp hq hγ hpos hactive hag hσ hmax hread
    (source_short P hk hnext a) hS.lawfulC
    (fun d => by
      change source P hk hnext a (original P hnext (I.rightFace.map d.1)) = _
      rw [source_original]; change a.val _ = _; rw [← he]
      exact LowOnlyOrderedLadder.field_private I F hroot
        (LowOnlyRecursiveCoverage.admissible_down F (by omega) (by omega) hS) d.1)
    (fun d => CanonicalPairedProfiles.inventory_coded _ _ hcanon (.inr (.inl d.1)))
    (fun d => CanonicalPairedProfiles.inventory_short _ _ hcanon (.inr (.inl d.1)))
    fun hb' hv hpre => by
      simpa only [show (⟨S.profile, hcanon, S, hS, rfl⟩ : F.Anchor (k + 1)) = a from Subtype.ext he]
        using private_source_repair P hk hnext hS hcanon hb' hv hpre
