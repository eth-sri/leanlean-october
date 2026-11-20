/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PointImageSemantics
public import VaughtConjecture.Knight.FullScopeBountiful
public import VaughtConjecture.Knight.CappedLifting

@[expose] public section

namespace VaughtConjecture.Knight.PointImageSemantics

open AmalgamationPlan Transform Value ExtOrd AmalgamatedBoundary

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

variable {B : Finset ι} {C : Finset κ} (D : CellScheme B) (e : ι ↪ κ)

variable (he : B.image e = C) (sem : Semantics D)

local notation "K" => pointImage D e he

theorem respects_owner_iff (c : Cell D) (q : (K).below ((K).cell c) → ExtOrd) :
    RespectsSemanticsBelow (rows D e he sem) ((K).cell c) q ↔
      RespectsSemanticsBelow sem (D.cell c) (q ∘ belowEquiv D e he c) :=
  respects_iff_of_equiv (belowEquiv D e he c).symm (fun _ => rfl)
    (fun _ _ => Finset.image_subset_image_iff e.injective) (fun _ _ _ => rfl) q

theorem bountiful (hD : D.IsComplete) (hb : sem.IsBountiful) :
    (rows D e he sem).IsBountiful := by
  intro CI BJ hCI hBJ h _
  obtain ⟨c, rfl⟩ := pointImage_complete D e he hD CI hCI
  obtain ⟨d, rfl⟩ := pointImage_complete D e he hD BJ hBJ
  exact CoatomBoundaryExtension.CappedLift.of_pullback (belowEquiv D e he c).symm
    (belowEquiv D e he d).symm (fun _ => rfl) le_rfl
    (respects_owner_iff D e he sem c) (respects_owner_iff D e he sem d)
    (CoatomBoundaryExtension.lift_of_bountiful hb (D.cell_mem c) (D.cell_mem d)
      ((below_iff D e he c d).mp h))

end VaughtConjecture.Knight.PointImageSemantics
