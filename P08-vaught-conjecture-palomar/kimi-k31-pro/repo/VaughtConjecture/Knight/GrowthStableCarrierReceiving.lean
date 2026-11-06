/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthCarrierEvaluation
public import VaughtConjecture.Knight.StableActualLabelling
public import VaughtConjecture.Knight.GrowthStableSelectedInput
public import VaughtConjecture.Knight.TopSupportReceiving
public import VaughtConjecture.Knight.ActualOccurrence

/-! # Actual growth receiving evaluated by lawful stable labels

Generalized saturation realizes the legal scheme over the actual private
context. The stable labels of that actual coface are independently lawful,
agree with the private context's stable labels, and retain its bottom class.
Positive-cap physical correctness therefore applies even when the stable cap
is proper. No stable modelhood or realization of a selected display is used.

The calibrated `RelativeData` and literal root attachment remain inputs.
In particular this does not construct the shorter encoding or donor template.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthStableCarrierReceiving
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

variable (hM : W.IsModel) {u : Fin J ↪ M} (hu : W.eval u = some C)

include Q hvC hvP hC hP T hsmall hM hu in
/-- A fresh actual donor occurrence whose stable labels satisfy the calibrated
request relation. The donor scheme is literal, with no displayed-stage premise. -/
theorem exists_correct_donor (hclass : InClass X.ZA C.label) :
    ∃ (y : M) (_hy : y ∉ Set.range u) (hyRoot : y ∉ Set.range (e.trans u))
      (s : S α.1 (n + 1)), W.eval (snoc (e.trans u) y hyRoot) = some s ∧
      ∃ hs : s.scheme = P,
        X.req.Correct (X.req.sec (W.stableValue u C))
          (fun d => W.stableValue (snoc (e.trans u) y hyRoot) s
            (SemScheme.castCell hs.symm d)) := GrowthCarrierEvaluation.exists_correct_donor C P Q e hvC hvP hC hP X T hsmall
    (stableActualLabelling hM.consistent hM.covering) hM hu
    (fun d => (GrowthStableSelectedInput.private_bottom hM hu d.1).trans (hclass d))

