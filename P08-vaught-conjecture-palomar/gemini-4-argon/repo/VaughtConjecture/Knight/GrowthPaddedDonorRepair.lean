/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPaddedCharts

/-! # Constructed owner-capped donor repair on the installed growth successor

The three cuts remain distinct: the original external cap, the constructed
native grid cut, and the prescribed owner value. No alignment or replacement
source is supplied by the caller. The argument reuses
`LowOnlyPaddedDonorRepair` with the pre-activation growth donor repair producer.
No symmetry of the admission predicate is used.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.GrowthPaddedDonorRepair
open Transform Value ExtOrd CappedDonor Growth CanonicalPairedInverse GrowthPaddedSuccessor GrowthPaddedDecode GrowthPaddedCharts
open SharpWitnessComposition

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : Growth.RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

theorem donor_grade (d : I.left.scheme.below (Finset.univ, 2)) :
    (carrier I X T hA hB hC).grade (donorAt I X T hA hB hC d).1 =
      I.left.scheme.grade d.1 := by
  exact (congrArg Prod.snd (original_index I X T hA hB hC
    (I.leftFace.map d.1))).trans (congrArg Prod.snd (I.leftFace.index d.1))

theorem owner_capped (hN : 2 < X.req.N)
    (c : I.left.scheme.below (Finset.univ, 2))
    (hc : I.left.scheme.cell c.1 = (Finset.univ, 2)) (hg : I.left.scheme.grade c.1 = 2)
    {p : I.left.scheme.below (Finset.univ, 2) → ExtOrd}
    {q : (carrier I X T hA hB hC).below (A, 2) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, 2) p)
    (hq : RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2) q)
    {γ : ExtOrd} (hγ : SelfVis 2 γ) (hpos : ⊥ < γ) (hactive : γ < p c)
    (hag : ∀ d, min (q (donorAt I X T hA hB hC d)) γ = min (p d) γ) :
    ∃ u, RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2) u ∧
      (∀ d, u (donorAt I X T hA hB hC d) = min (p d) (p c)) ∧
      (∀ d, min (u d) γ = min (q d) γ) ∧ (∀ d, u d ≤ p c) := by
  classical
  obtain ⟨a, σ, H, hσ, hmax, hread⟩ := GrowthPaddedCharts.exists_chart I X T hA hB hC hq
  obtain ⟨S, hS, he⟩ := a.property.2
  have hcanon : S.profile ∈
      CanonicalPairedProfiles.inventory (Field I.right.scheme I.left.scheme) 2 :=
    he.symm ▸ a.property.1
  exact PrivateRowFactorization.owner_capped_of_chart
    (Fintype.card (Field I.right.scheme I.left.scheme))
    (donor_grade I X T hA hB hC) c hc hg hp hq hγ hpos hactive hag hσ hmax hread
    (source_short I X T hA hB hC a) hS.donor_lawful
    (fun d => by
      change source I X T hA hB hC a (original I X T hA hB hC (I.leftFace.map d.1)) = _
      rw [original_readback]; change a.val _ = _; rw [← he]
      exact GrowthOrderedBase.field_donor I S d.1)
    (fun d => CanonicalPairedProfiles.inventory_coded _ _ hcanon (.inr d.1))
    (fun d => CanonicalPairedProfiles.inventory_short _ _ hcanon (.inr d.1))
    fun hb' hv hpre => by
      simpa only [show (⟨S.profile, hcanon, S, hS, rfl⟩ : Catalogue X 2) = a from Subtype.ext he]
        using donor_source_repair I X T hA hB hC hN hS hcanon hb' hv hpre
