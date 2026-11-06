/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReceivingCatalogueSources

/-! # Rank-row incidences with retained private owners

Rank compression preserves the source-block bottom condition at grade one.
Consequently the admitted private section supplies faithful locality for the
long lower ladder rows against original owners, not just upper-row locality.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.ReceivingCatalogueIncidences
open Transform Value ExtOrd CappedDonor CappedDonor.Ref ReceivingLadderCarrier
open ReceivingCatalogueSources LadderScalarRendering
noncomputable section

/-- Visible postprocessing needs bottom reflection only on the actual target
table. This is a constructed faithful witness, not transformation transitivity. -/
theorem postprocess {Y : Type*} [Finite Y] {E t : Y → ExtOrd}
    (h : TransformsTo (fun _ : Y => 1) E t) (hE : ∀ d, SelfVis 1 (E d))
    {f : ExtOrd → ExtOrd} (hm : Monotone f) (h0 : f ⊥ = ⊥)
    (hv : ∀ d, SelfVis 1 (f (t d))) (hb : ∀ d, f (t d) = ⊥ ↔ t d = ⊥) :
    TransformsTo (fun _ : Y => 1) E (fun d => f (t d)) := by
  apply LongGuardRows.transforms_of_visible_table hE hv
  · intro d e he
    obtain ⟨g, σ, _, _, _, hσ, _, hr⟩ := h
    apply hm
    rw [hr d, hr e]
    exact min_le_min (hσ he) le_rfl
  · intro d hd
    obtain ⟨g, σ, _, _, hσ, _, _, hr⟩ := h
    rw [hr d, hd, hσ, min_bot_left, h0]
  · intro d e he hd
    exact (hb e).mpr (LongGuardRows.bottom_of_same_block h he ((hb d).mp hd))

variable {I : Type*} [Fintype I] {nP K : ℕ} {P : SemScheme (nP + 1)}
  {C : SemScheme 2} {R : Ref I nP 2 2 P C} (L : R.LowRef K)

variable (hC : C.scheme.plan = privatePlan) (request : Cell P.scheme)

local notation "H" => ReceivingCatalogueSources.ceiling (P := P) (C := C)
local notation "G" => grid (P := P) (C := C)
local notation "D" => carrier L hC
local notation "T" => SupportLadderRows.Point (rungs (P := P) (C := C))

end
end VaughtConjecture.Knight.ReceivingCatalogueIncidences
