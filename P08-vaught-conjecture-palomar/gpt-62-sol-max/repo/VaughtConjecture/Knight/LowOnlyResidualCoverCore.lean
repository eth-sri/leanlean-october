/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyResidualReceivingCore
public import VaughtConjecture.Knight.ReceiveCover

@[expose] public section

namespace VaughtConjecture.Knight.LowOnlyResidualReceiving

open TypeTower StageType KnightRealization Value ExtOrd CappedDonor

noncomputable section

universe w

variable {M : Type w} {α : LimitStage} {W : KnightRealization α M}
  (hcons : W.IsExactParentConsistent) (hFC : FiniteCutReceiving W) {K : ℕ}
  (hcoin : KnightRealization.IsCoinitial {x : W.LabelledExt | x.type.topGrade = K}) (hKpos : 0 < K)
  (hres : ∀ {k : ℕ} (B : Fin k ↪ M), ¬ TopSupportRigidCore.RigidCore W B)

include hcons hFC hcoin hKpos hres

/-- Every finite legal donor with top grades bounded by the characteristic is
received exactly over any literal realized face. -/
theorem receive_cover_of_tail {n m : ℕ} (Q : S α.1 m)
    (hQK : ∀ d, Q.label d = ⊤ → Q.scheme.scheme.grade d ≤ K)
    (f : Fin n ↪ Fin m) (t : Fin n ↪ M) (p : S α.1 n)
    (hp : typeMap f Q = some p) (ht : W.eval t = some p) :
    ∃ u : Fin m ↪ M, f.trans u = t ∧ W.eval u = some Q := by
  obtain ⟨u, Q', hfu, hu, he⟩ := receiveCover hcons
    (Inv := fun _ P => ∀ d, P.label d = ⊤ → P.scheme.scheme.grade d ≤ K)
    (Rel := fun P Q => P = Q) (fun _ => rfl) Eq.trans
    (fun Q g hg t p ht hQ hcof => by
      have hK (d : Cell (Q.restrictFace g hg).scheme.scheme)
          (hd : (Q.restrictFace g hg).label d = ⊤) : (Q.restrictFace g hg).scheme.scheme.grade d ≤ K :=
        by tauto
      obtain ⟨y, hy, hr⟩ := receive_of_tail hcons hFC hcoin hKpos hres t p ht _ hcof hK
      exact ⟨snoc t y hy, Q, Q.restrictFace g hg, castSuccEmb_trans_snoc t y hy,
        hQ, rfl, typeMap_eq_some g Q hg, hr⟩)
    Q f t p hp ht hQK
  grind

end

end VaughtConjecture.Knight.LowOnlyResidualReceiving
