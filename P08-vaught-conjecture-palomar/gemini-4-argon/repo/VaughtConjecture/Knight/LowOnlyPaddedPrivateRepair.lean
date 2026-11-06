/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedCharts

/-! # Constructed owner-capped private repair on the installed LOW successor

The three cuts remain distinct: the original external cap, the constructed
native grid cut, and the prescribed owner value. No alignment or replacement
source is supplied by the caller.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.LowOnlyPaddedPrivateRepair
open Transform Value ExtOrd CappedDonor LowOnly CanonicalPairedInverse LowOnlyPaddedSuccessor LowOnlyPaddedDecode LowOnlyPaddedCharts
open SharpWitnessComposition

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

theorem private_grade (d : I.right.scheme.below (effC n 2)) :
    (carrier I F hroot hA hB hC).grade (privateAt I F hroot hA hB hC d).1 =
      I.right.scheme.grade d.1 := by
  exact (congrArg Prod.snd (original_index I F hroot hA hB hC
    (I.rightFace.map d.1))).trans (congrArg Prod.snd (I.rightFace.index d.1))

theorem owner_capped
    (c : I.right.scheme.below (effC n 2))
    (hc : I.right.scheme.cell c.1 = effC n 2) (hg : I.right.scheme.grade c.1 = 2)
    {p : I.right.scheme.below (effC n 2) → ExtOrd}
    {q : (carrier I F hroot hA hB hC).below (A, 2) → ExtOrd}
    (hp : RespectsSemanticsBelow I.right.rows (effC n 2) p)
    (hq : RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2) q)
    {γ : ExtOrd} (hγ : SelfVis 2 γ) (hpos : ⊥ < γ) (hactive : γ < p c)
    (hag : ∀ d, min (q (privateAt I F hroot hA hB hC d)) γ = min (p d) γ) :
    ∃ u, RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2) u ∧
      (∀ d, u (privateAt I F hroot hA hB hC d) = min (p d) (p c)) ∧
      (∀ d, min (u d) γ = min (q d) γ) ∧ (∀ d, u d ≤ p c) := by
  classical
  obtain ⟨a, σ, H, hσ, hmax, hread⟩ := LowOnlyPaddedCharts.exists_chart I F hroot hA hB hC hq
  obtain ⟨S, hS, he⟩ := a.property.2
  have hcanon : S.profile ∈ CanonicalPairedProfiles.inventory (Field I.left I.right) 2 :=
    he.symm ▸ a.property.1
  exact PrivateRowFactorization.owner_capped_of_chart (Fintype.card (Field I.left I.right))
    (private_grade I F hroot hA hB hC) c hc hg hp hq hγ hpos hactive hag hσ hmax hread
    (source_short I F hroot hA hB hC a) hS.lawfulC
    (fun d => by
      change source I F hroot hA hB hC a (original I F hroot hA hB hC (I.rightFace.map d.1)) = _
      rw [original_readback]; change a.val _ = _; rw [← he]
      exact LowOnlyOrderedLadder.field_private I F hroot
        (LowOnlyRecursiveCoverage.admissible_down F (by decide) (by decide) hS) d.1)
    (fun d => CanonicalPairedProfiles.inventory_coded _ _ hcanon (.inr (.inl d.1)))
    (fun d => CanonicalPairedProfiles.inventory_short _ _ hcanon (.inr (.inl d.1)))
    fun hb' hv hpre => by
      simpa only [show (⟨S.profile, hcanon, S, hS, rfl⟩ : F.Anchor 2) = a from Subtype.ext he]
        using private_source_repair I F hroot hA hB hC hS hcanon hb' hv hpre
