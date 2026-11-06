/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.GrowthCappedReadback
import VaughtConjecture.Knight.GrowthAttachedCarrier
import VaughtConjecture.Knight.ActualLabelling
import VaughtConjecture.Knight.TopSupportReceiving

/-! # Realize the growth carrier once, then evaluate its actual occurrences

Generalized saturation is used only in the original model. Any lawful,
restriction-compatible evaluator of its actual occurrences reads the request
relation on the installed donor. All receipts belong to the same fresh point.
The evaluator need not be a model, and its values need not lie below the stage.
-/

namespace VaughtConjecture.Knight.GrowthCarrierEvaluation
open TypeTower StageType KnightRealization    
open Growth 

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

local notation "E" => GrowthAttachedCarrier.semScheme T hsmall
local notation "F" => GrowthAttachedCarrier.privateFace T hsmall
local notation "G" => GrowthAttachedCarrier.donorFace T hsmall

theorem extendsDomain : ExtendsDomain C E :=
  ⟨GrowthAttachedCarrier.private_visible T hsmall,
    GrowthAttachedCarrier.restrict_private C.scheme P Q e hvC hvP hC hP X T hsmall⟩

theorem private_cellOf d :
    (extendsDomain C P Q e hvC hvP hC hP X T hsmall).cellOf d = (F).map d :=
  GrowthAttachedCarrier.private_occurrence C.scheme P Q e hvC hvP hC hP X T hsmall d

variable (L : W.ActualLabelling) {u : Fin J ↪ M}

/-- Restriction compatibility retains the evaluated private face literally. -/
theorem private_label {y} {hy : y ∉ Set.range u} {r : S α.1 (J + 1)}
    (hr : r.scheme = E) (hco : IsCoface C r) (heval : W.eval (snoc u y hy) = some r)
    d :
    L.label (snoc u y hy) r (SemScheme.castCell hr.symm ((F).map d)) = L.label u C d := by
  obtain ⟨Er, v, hb, hv⟩ := r
  dsimp  at hr
  subst Er
  rw [← private_cellOf C P Q e hvC hvP hC hP X T hsmall d]
  exact L.mapCell heval (castSuccEmb_trans_snoc hy) hco d

local notation "InClass₀" => InClass X.ZA (L.label u C)

local notation "Correct₀" => X.req.Correct (X.req.sec (L.label u C))

/-- Physical readback applies to any lawful evaluator in the required bottom class. -/
theorem correct_of_coface (hclass : InClass₀)
    {y} {hy : y ∉ Set.range u} {r : S α.1 (J + 1)}
    (hr : r.scheme = E) (hco : IsCoface C r) (heval : W.eval (snoc u y hy) = some r) :
    Correct₀
      (fun d => L.label (snoc u y hy) r (SemScheme.castCell hr.symm ((G).map d))) := GrowthCappedReadback.full_correct
    (GrowthAttachedCarrier.boundary C.scheme P Q e hvC hvP hC hP) X T
    (GrowthAttachedCarrier.height C.scheme P X hsmall)
    (GrowthAttachedCarrier.donor_proper C.scheme P e X hsmall)
    GrowthAttachedCarrier.private_proper _ _ hsmall (by omega)
    (respects_castCell hr (L.lawful heval)) (L.label u C) hclass (X.cap_ne_bot hclass)
    (private_label C P Q e hvC hvP hC hP X T hsmall L hr hco heval)

/-- Realization is a clause of the original model, not a law of the evaluator. -/
theorem exists_correct_coface (hM : W.IsModel) (hu : W.eval u = some C)
    (hclass : InClass₀) :
    ∃ (y : M) (hy : y ∉ Set.range u) (r : S α.1 (J + 1)) (hr : r.scheme = E),
      IsCoface C r ∧ W.eval (snoc u y hy) = some r ∧
      Correct₀
        (fun d => L.label (snoc u y hy) r (SemScheme.castCell hr.symm ((G).map d))) := by
  obtain ⟨y, hy, r, hr, hco, hev⟩ := hM.genSat u C hu E
    (extendsDomain C P Q e hvC hvP hC hP X T hsmall)
  exact ⟨y, hy, r, hr, hco, hev,
    correct_of_coface C P Q e hvC hvP hC hP X T hsmall L hclass hr hco hev⟩

def donor_restriction {r : S α.1 (J + 1)} (hr : r.scheme = E) :=
  exists_restriction_with_map (onePointProj e)
    (GrowthAttachedCarrier.donor_visible T hsmall)
    (GrowthAttachedCarrier.restrict_donor C.scheme P Q e hvC hvP hC hP X T hsmall)
    (G).map (GrowthAttachedCarrier.donor_occurrence C.scheme P Q e hvC hvP hC hP X T hsmall) hr

include Q hvC hvP hC hP T hsmall in
/-- The same fresh point realizes the donor; its evaluated labels satisfy the
request relation. This is not realization of a preselected labelling. -/
theorem exists_correct_donor (hM : W.IsModel) (hu : W.eval u = some C)
    (hclass : InClass₀) :
    ∃ (y : M) (_hy : y ∉ Set.range u) (hyRoot : y ∉ Set.range (e.trans u))
      (s : S α.1 (n + 1)), W.eval (snoc (e.trans u) y hyRoot) = some s ∧
      ∃ hs : s.scheme = P,
        Correct₀
          (fun d => L.label (snoc (e.trans u) y hyRoot) s (SemScheme.castCell hs.symm d)) := by
  obtain ⟨y, hy, r, hr, _, hev, hc⟩ :=
    exists_correct_coface C P Q e hvC hvP hC hP X T hsmall L hM hu hclass
  obtain ⟨s, hs, he, hmap⟩ := donor_restriction C P Q e hvC hvP hC hP X T hsmall hr
  obtain ⟨hyRoot, htup, heval⟩ := restrict_actual_extension hM.consistent e rfl hy hev hs
  have hval (d : Cell P.scheme) :
      L.label (snoc (e.trans u) y hyRoot) s (SemScheme.castCell he.symm d) =
        L.label (snoc u y hy) r (SemScheme.castCell hr.symm ((G).map d)) := by
    rw [← hmap d]
    exact (L.mapCell hev htup hs _).symm
  refine ⟨y, hy, hyRoot, s, heval, he, ?_⟩
  simpa only [hval] using hc


