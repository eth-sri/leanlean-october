/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedRestriction
public import VaughtConjecture.Knight.LowOnlyPaddedRankReadback
public import VaughtConjecture.Knight.LowOnlyPaddedTwoReadback

/-! # Native LOW readback retained through later installed layers

Actual occurrence maps and literal inherited rows transfer the three native
readback cases to arbitrary whole lawful sections of later carriers. These
are not identities between renderings at different construction grades.
The physical separator and the two private top receipts remain explicit.
-/

@[expose] public section

namespace VaughtConjecture.Knight.LowOnlyPaddedReadbackTransport
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder
open LowOnlyPaddedContract LowOnlyPaddedIteration LowOnlyPaddedRestriction
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n)

section Rank
variable (F : LowOnly.Family I.left I.right 1)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)
  {k : ℕ} (P : Layer I F hroot hA hB hC k)

theorem rank_readback {S : State I.left I.right}
    (hlt : LowSeparator.donorMax (LowSeparator.donorField F) S.profile < S.b)
    {qs qt}
    (hqs : RelativeLadderLayer.ranks (F.fields 1) qs = LadderScalarRendering.fieldRank S.profile)
    (hqt : RelativeLadderLayer.ranks (F.fields 1) qt = LadderScalarRendering.fieldRank
      (LowSeparatorRank.rankPartner (LowSeparator.donorField F) LowSeparator.cutoffField S.profile))
    {q} (hq : RespectsSemantics P.rows q)
    (hsep : q (P.baseMap (RelativeLadderLayer.leafOccurrence I.boundary (by omega) qt).1) <
      q (P.baseMap (RelativeLadderLayer.leafOccurrence I.boundary (by omega) qs).1))
    (hc : q (P.baseMap (RelativeLadderLayer.old I.boundary (by omega)
      (I.rightFace.map F.gap.c))) = ⊤)
    (hr : q (P.baseMap (RelativeLadderLayer.old I.boundary (by omega)
      (I.rightFace.map F.gap.r.1))) = ⊤)
    (d : I.left.scheme.below (effC n 1)) (hd : F.p d.1 = ⊤) :
    q (P.baseMap (RelativeLadderLayer.old I.boundary (by omega) (I.leftFace.map d.1))) = ⊤ :=
  LowOnlyPaddedRankReadback.donor_top_of_separator I F hroot (by omega) hB hC
    hlt hqs hqt (base_pullback I F hroot hA hB hC P hq) hsep hc hr d hd

end Rank

end
end VaughtConjecture.Knight.LowOnlyPaddedReadbackTransport
