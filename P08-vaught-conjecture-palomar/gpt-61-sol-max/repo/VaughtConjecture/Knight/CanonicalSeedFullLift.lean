
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CanonicalSeedActiveLift
import VaughtConjecture.Knight.CanonicalRecursiveTopSections

/-! # All-cap proper-face lifting at the recursive seed grade

Bottom-cap supply first completes the actual old boundary using its two
lifting clauses, then extends through the recursive layers with exact top
decoding. Positive caps split into active and inactive prescribed owners.
No future completion or output bountifulness is assumed.
-/

namespace VaughtConjecture.Knight.CanonicalSeedFullLift
open    CoatomBoundaryExtension
open CanonicalRecursiveSeedRows CanonicalSeedCutPrefix CanonicalSeedActiveLift

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hA : 3 ≤ A.card)
variable (hp : AvoidsValue D.scope A)
variable {C : Finset ι} (hC : C ∈ D.plan) (hCA : C ≠ A)
variable {U V O : GradedIndex ι}
variable (hcover : ∀ d ,
  GradedLe ((cut (D := D)).cell d) U ∨ GradedLe ((cut (D := D)).cell d) V)
variable (hCU : GradedLe (C, 3) U) (hOU : GradedLe O U) (hOV : GradedLe O V)
variable (hinter : ∀ d , GradedLe ((cut (D := D)).cell d) U →
  GradedLe ((cut (D := D)).cell d) V → GradedLe ((cut (D := D)).cell d) O)
variable (hleft : CappedLift (cutRows sem) hCU) (hright : CappedLift (cutRows sem) hOV)

local notation "GradedLe₀" => GradedLe (C, 3) (A, 3)

include hC hCA hcover hOU hinter hleft hright in
/-- Local bottom-cap supply, not just extension of an already whole boundary.
The prescription may contain literal top. No ambient is needed. -/
theorem exists_section
    {p}
    (hpr : RespectsSemanticsBelow (outputRows sem hA hp) (C, 3) p) :
    ∃ r ,
      RespectsSemanticsBelow (outputRows sem hA hp) (A, 3) r ∧
      ∀ e, r (CellScheme.below.mono
        (show GradedLe₀ from
          ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) e) = p e := by
  have hCnot  := fun h =>
    hCA (Finset.Subset.antisymm (D.isPlan.subset_of_mem hC) h)
  let E := faceEquiv sem hA (C, 3) hCnot le_rfl
  have hp₀ := pullback_respects sem hA hp (C, 3) hCnot le_rfl hpr
  obtain ⟨b, hbread⟩ := CoatomBoundaryExtension.section_left hOU hinter hleft hright hp₀
  let F := GradeCutBoundary.belowEquiv D (A, 3) le_rfl
  have hu := (GradeCutBoundary.respects_iff sem (A, 3) le_rfl _).mp
    ((b.whole_respects hcover).toBelow (A, 3))
  obtain ⟨r, hr, hread⟩ := CanonicalRecursiveTopSections.exists_section sem hp 0 hA hu
  refine ⟨r, hr, ?_⟩
  intro e
  obtain ⟨d, rfl⟩ := E.surjective e
  let dA : (cut ).below (A, 3) :=
    ⟨d.1, d.2.1.trans (D.isPlan.subset_of_mem hC), d.2.2⟩
  have hd : CellScheme.below.mono
      (show GradedLe₀ from
        ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) (E d) =
      CanonicalRecursiveTopSections.boundaryTarget sem 0 hA (F dA) :=
    Subtype.ext (faceEquiv_val sem hA _ hCnot le_rfl d)
  rw [hd, hread]
  change b.whole hcover (F.symm (F dA)).1 = p (E d)
  rw [Equiv.symm_apply_apply]
  exact (b.whole_left hcover (CellScheme.below.mono hCU d)).trans
    ((b.value_left _).symm.trans (hbread d))

include hC hCA hcover hOU hinter hleft hright in
/-- All original permitted caps at the new same-grade proper-to-full pair.
The predecessor supplies only lower restoration. Old-face clauses supply
only boundary completion. Every actual successor auxiliary cap survives. -/
theorem full_lift
    (hb : CanonicalSeedRestoration.LowerBountiful sem hA hp)
    (hCc : 3 ≤ C.card)
    (hfull : ∃ c : (cut (D := D)).below (C, 3),
      (cut (D := D)).cell c.1 = (C, 3))
    (hU : U.2 ≤ 3) (hV : V.2 ≤ 3) :
    CappedLift (outputRows sem hA hp)
      (show GradedLe₀ from
        ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) := by
  intro p q γ hpr hqr hγ hag
  by_cases hγb : γ = ⊥
  · obtain ⟨r, hr, hread⟩ := exists_section sem hA hp hC hCA
      hcover hCU hOU hOV hinter hleft hright hpr
    exact ⟨r, hr, fun _ => by simp  [hγb, ], hread⟩
  by_cases hactive : ∃ d ,
      (carrier sem hA).grade d.1 = 3 ∧ γ < p d
  · obtain ⟨r, hr, hread, hcap⟩ := CanonicalSeedActiveLift.exists_lift
      sem hA hp hb hC hCA hCc hfull hpr hqr hγ hγb (fun d => (hag d).symm)
      hactive hcover hCU hOU hOV hinter hleft hright hU hV
    exact ⟨r, hr, hcap, hread⟩
  · exact CanonicalSeedRestoration.inactive sem hA hp
       hb hC (Nat.le_of_succ_le hCc) hpr hqr hγ hag
      (fun d hd => not_lt.mp (fun h => hactive ⟨d, hd, h⟩))


