/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthCappedReadback
public import VaughtConjecture.Knight.GrowthAttachedCarrier
public import VaughtConjecture.Knight.ActualLabelling
public import VaughtConjecture.Knight.TopSupportReceiving

@[expose] public section

namespace VaughtConjecture.Knight.GrowthCarrierEvaluation

open TypeTower StageType KnightRealization Value ExtOrd AmalgamationPlan CappedDonor

open Growth CellScheme.restrictFace

noncomputable section

universe w

variable {M : Type w} {α : LimitStage} {W : KnightRealization α M}
  {n J : ℕ} (C : S α.1 J) (P : SemScheme (n + 1)) (Q : SemScheme n)
  (e : Fin n ↪ Fin J)
  (hvC : Finset.univ.image e ∈ C.scheme.scheme.plan)
  (hvP : Finset.univ.image Fin.castSuccEmb ∈ P.scheme.plan)
  (hC : C.scheme.restrictFace e hvC = Q)
  (hP : P.restrictFace Fin.castSuccEmb hvP = Q)
  (X : RelativeData C.scheme.scheme C.scheme.rows P.scheme P.rows)
  (T : RootAttachment Q Fin.castSuccEmb hvP hP e hvC hC X)
  (hsmall : n + 1 < X.req.N)

local notation "E" => GrowthAttachedCarrier.semScheme C.scheme P Q e hvC hvP hC hP X T hsmall

local notation "F" => GrowthAttachedCarrier.privateFace C.scheme P Q e hvC hvP hC hP X T hsmall

local notation "G" => GrowthAttachedCarrier.donorFace C.scheme P Q e hvC hvP hC hP X T hsmall

local notation "R₀" => GrowthAttachedCarrier.private_receipt C.scheme P Q e hvC hvP hC hP X T hsmall

variable (L : W.ActualLabelling) {u : Fin J ↪ M}

/-- Restriction compatibility retains the evaluated private face literally. -/
theorem private_label {y : M} {hy : y ∉ Set.range u} {r : S α.1 (J + 1)}
    (hr : r.scheme = E) (hco : IsCoface C r) (heval : W.eval (snoc u y hy) = some r)
    (d : Cell C.scheme.scheme) :
    L.label (snoc u y hy) r (SemScheme.castCell hr.symm ((F).map d)) = L.label u C d := by
  obtain ⟨Er, v, hb, hv⟩ := r
  dsimp only at hr
  subst Er
  rw [← (R₀).occurrence d]
  exact L.mapCell heval (castSuccEmb_trans_snoc u y hy) hco d

include Q hvC hvP hC hP T hsmall in
/-- The same fresh point realizes the donor; its evaluated labels satisfy the
request relation. This is not realization of a preselected labelling. -/
theorem exists_correct_donor (hM : W.IsModel) (hu : W.eval u = some C)
    (hclass : InClass X.ZA (L.label u C)) :
    ∃ (y : M) (_hy : y ∉ Set.range u) (hyRoot : y ∉ Set.range (e.trans u))
      (s : S α.1 (n + 1)), W.eval (snoc (e.trans u) y hyRoot) = some s ∧
      ∃ hs : s.scheme = P,
        X.req.Correct (X.req.sec (L.label u C))
          (fun d => L.label (snoc (e.trans u) y hyRoot) s (SemScheme.castCell hs.symm d)) := by
  obtain ⟨y, hy, r, hr, hco, hev⟩ := hM.genSat u C hu E (R₀).extendsDomain
  let Gctx := GrowthPaddedIteration.BuildContext.full
      (GrowthAttachedCarrier.boundary C.scheme P Q e hvC hvP hC hP) X T
      (GrowthAttachedCarrier.height C.scheme P X hsmall)
      (GrowthAttachedCarrier.donor_proper C.scheme P e X hsmall)
      GrowthAttachedCarrier.private_proper
  have hc := GrowthCappedReadback.full_correct Gctx hsmall (Nat.sub_add_cancel Gctx.height).ge
    (respects_castCell hr (L.lawful hev)) (L.label u C) hclass (X.cap_ne_bot hclass)
    (private_label C P Q e hvC hvP hC hP X T hsmall L hr hco hev)
  have R₁ := GrowthAttachedCarrier.donor_receipt C.scheme P Q e hvC hvP hC hP X T hsmall
  obtain ⟨s, hs, he, hmap⟩ := exists_restriction_with_map (onePointProj e)
    R₁.visible R₁.restrict_eq (G).map R₁.occurrence hr
  obtain ⟨hyRoot, htup, heval⟩ := restrict_actual_extension hM.consistent e rfl hy hev hs
  have hval (d : Cell P.scheme) :
      L.label (snoc (e.trans u) y hyRoot) s (SemScheme.castCell he.symm d) =
        L.label (snoc u y hy) r (SemScheme.castCell hr.symm ((G).map d)) := by
    rw [← hmap d]
    exact (L.mapCell hev htup hs _).symm
  refine ⟨y, hy, hyRoot, s, heval, he, ?_⟩
  exact (congrArg (X.req.Correct (X.req.sec (L.label u C))) (funext hval)).mpr hc

end

end VaughtConjecture.Knight.GrowthCarrierEvaluation
