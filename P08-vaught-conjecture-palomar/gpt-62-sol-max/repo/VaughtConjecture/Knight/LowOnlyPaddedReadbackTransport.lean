/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedIteration
public import VaughtConjecture.Knight.LowOnlyPaddedRankReadback

@[expose] public section

namespace VaughtConjecture.Knight.LowOnlyPaddedReadbackTransport

open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder

open LowOnlyPaddedContract LowOnlyPaddedIteration

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n)

section Rank

variable (F : LowOnly.Family I.left I.right 1)
  (hroot : I.RootMatches F.root)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)
  {k : ℕ} (P : Layer I F hroot hA hB hC k)

theorem rank_readback {S : State I.left I.right}
    (hlt : LowSeparator.donorMax (LowSeparator.donorField F) S.profile < S.b)
    {qs qt : F.Anchor 1}
    (hqs : RelativeLadderLayer.ranks (F.fields 1) qs = LadderScalarRendering.fieldRank S.profile)
    (hqt : RelativeLadderLayer.ranks (F.fields 1) qt = LadderScalarRendering.fieldRank
      (LowSeparatorRank.rankPartner (LowSeparator.donorField F) LowSeparator.cutoffField S.profile))
    {q : Cell P.carrier → ExtOrd} (hq : RespectsSemantics P.rows q)
    (hsep : q (P.baseMap (RelativeLadderLayer.leafOccurrence I.boundary (by omega) qt).1) <
      q (P.baseMap (RelativeLadderLayer.leafOccurrence I.boundary (by omega) qs).1))
    (hc : q (P.baseMap (RelativeLadderLayer.old I.boundary (by omega)
      (I.rightFace.map F.gap.c))) = ⊤)
    (hr : q (P.baseMap (RelativeLadderLayer.old I.boundary (by omega)
      (I.rightFace.map F.gap.r.1))) = ⊤)
    (d : I.left.scheme.below (effC n 1)) (hd : F.p d.1 = ⊤) :
    q (P.baseMap (RelativeLadderLayer.old I.boundary (by omega) (I.leftFace.map d.1))) = ⊤ :=
  LowOnlyPaddedRankReadback.donor_top_of_separator I F hroot (by omega) hB hC
    hlt hqs hqt (P.base_pullback hq) hsep hc hr d hd

end Rank

end

end VaughtConjecture.Knight.LowOnlyPaddedReadbackTransport
