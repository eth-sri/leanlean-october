
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CanonicalTwoGradeLift

/-! # Inactive upper prescriptions at the original positive cap

The ambient is clipped at the external cap, its lower layer is lifted at that
same cap, and the results are spliced. No prescribed grade-two owner is needed.
In particular a grade-one face may retain arbitrary distinct values and top.
-/

namespace VaughtConjecture.Knight.CanonicalInactiveLift
open    CanonicalMixedGradeLayers CanonicalMixedOwnerLift
open CoatomBoundaryExtension GradeTailRestoration


variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hA : 2 ≤ A.card)
variable (hproper : AvoidsValue D.scope A) (hg : BoundedBy D.grade 2)

local notation "rows₀" => rows sem 1 (by decide) (by omega) hproper 2 hg (by decide) hA (by decide)

/-- The inactive branch includes grade-one sources, empty lower domains,
and grade-two prescriptions with no active owner. Only old grade-one face
lifts are consumed; the ambient need not extend outside its actual target. -/
theorem exists_lift {C : Finset ι} {n : ℕ} (hn : 1 ≤ n)
    (hfull₁ : IsEmpty (D.below (C, 1)) ∨ ∃ c : D.below (C, 1), D.cell c.1 = (C, 1))
    {p : BelowLabels D (C, n)} (hp : RespectsSemanticsBelow sem (C, n) p)
    {q : CanonicalMixedAmbient.target sem 1 (by decide) (by omega) 2 (by decide) hA → ExtOrd}
    (hq : RespectsSemanticsBelow
      (rows₀) (A, 2) q)
    {γ : ExtOrd} (hγ : SelfVis 2 γ) (hγb : γ ≠ ⊥)
    (hag : ∀ e , min (p e) γ =
      min (q (oldTarget sem 1 (by decide) (by omega) hproper 2 hg
        (by decide) hA (by decide) e.1)) γ)
    (hinactive : ∀ e , D.grade e.1 = 2 → p e ≤ γ)
    {U V O : GradedIndex ι}
    (hcover : ∀ d , D.grade d ≤ 1 →
      GradedLe (D.cell d) U ∨ GradedLe (D.cell d) V)
    (hCU : GradedLe (C, 1) U) (hOU : GradedLe O U) (hOV : GradedLe O V)
    (hinter : ∀ d , GradedLe (D.cell d) U → GradedLe (D.cell d) V →
      GradedLe (D.cell d) O)
    (hleft : CappedLift sem hCU) (hright : CappedLift sem hOV)
    (hU : U.2 ≤ 1) (hV : V.2 ≤ 1) :
    ∃ r ,
      RespectsSemanticsBelow
        (rows₀) (A, 2) r ∧
      (∀ e , r (oldTarget sem 1 (by decide) (by omega) hproper 2 hg
        (by decide) hA (by decide) e.1) = p e) ∧
      CappedEq r q γ := by 
  let v := fun d => min (q d) γ
  let core1 := rows₀
  have hv : RespectsSemanticsBelow
      (core1) (A, 2) v :=
    hq.cap hγ
  let p₁ : BelowLabels D (C, 1) := fun e => p ⟨e.1, e.2.1, e.2.2.trans hn⟩
  have hp₁  :=
    hp.mono (show GradedLe (C, 1) (C, n) from ⟨Finset.Subset.refl _, hn⟩)
  let q₁ := fun d => v (lowerIncl (by decide : 1 ≤ 2) d)
  have hq₁ : RespectsSemanticsBelow
      (core1) (A, 1) q₁ :=
    hv.mono (show GradedLe (A, 1) (A, 2) from
      ⟨Finset.Subset.refl _, (by decide : 1 ≤ 2)⟩)
  have hag₁ (e : D.below (C, 1)) : min (p₁ e) γ =
      min (q₁ (CanonicalLowerLift.oldLow sem (by omega) 2 (by decide) hA e.1 e.2.2)) γ := by
    
    rw [min_assoc, min_self]
    exact hag ⟨e.1, e.2.1, e.2.2.trans hn⟩
  have hex : ∃ w ,
      RespectsSemanticsBelow
        core1 (A, 1) w ∧
      (∀ e ,
        w (CanonicalLowerLift.oldLow sem (by omega) 2 (by decide) hA e.1 e.2.2) = p₁ e) ∧
      CappedEq w q₁ γ := by
    rcases hfull₁ with he | hf
    · let := he
      exact ⟨q₁, hq₁, fun e => isEmptyElim e, fun _ => rfl⟩
    · exact CanonicalLowerLift.exists_positive_lift hf hp₁ hq₁ (hγ.mono (by decide)) hγb hag₁
        hcover hCU hOU hOV hinter hleft hright hU hV
  obtain ⟨w, hw, hwread, hwcap⟩ := hex
  refine ⟨splice v w, splice_respects (by decide : 1 ≤ 2) hv hw
    (fun _ _ => min_le_right _ _) hwcap, ?_, ?_⟩
  · intro e
    by_cases he : D.grade e.1 ≤ 1
    · rw [splice_low v w _ (by rw [oldTarget_grade]; exact he)]
      exact hwread ⟨e.1, e.2.1, he⟩
    · rw [splice_high v w (by rw [oldTarget_grade]; exact he)]
      have he₂ : D.grade e.1 = 2 := by have := hg e.1; omega
      exact (hag e).symm.trans (min_eq_left (hinactive e he₂))
  · intro d
    exact (splice_cap (by decide : 1 ≤ 2) hwcap d).trans
      (show min (min (q d) γ) γ = min (q d) γ by rw [min_assoc, min_self])


