
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.CanonicalRecursiveOwnerLift
import VaughtConjecture.Knight.CanonicalRecursiveRestoration

/-! # Literal active-owner lifting on the recursive successor

The prescription and ambient are arbitrary lawful physical sections. A maximal
prescribed owner is constructed by availability. Old-face lifting constructs
the coded boundary repair; predecessor bountifulness restores the complete
lower prescription, including distinct values above the owner and literal top.
-/

namespace VaughtConjecture.Knight.CanonicalRecursiveActiveLift
open    CoatomBoundaryExtension
open CanonicalRecursiveSuccessorRows CanonicalRecursiveCutPrefix
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (n : ℕ) (hA : n + 4 ≤ A.card)
variable (hp : AvoidsValue D.scope A)

abbrev predecessorState := CanonicalRecursiveSemantics.state sem hp n (Nat.le_of_succ_le hA)
local notation "predecessorState₀" => predecessorState sem n hA hp

abbrev outputRows := rows sem n hA hp (predecessorState₀)

local notation "cut₀" => cut (D := D) n

def faceEquiv (J : GradedIndex ι) (hJ : ¬ A ⊆ J.1) (hj : J.2 ≤ n + 4) :
    (cut₀).below J ≃ (carrier sem n hA).below J :=
  (GradeCutBoundary.belowEquiv D J hj).trans
    (CanonicalRecursiveBoundaryTransport.properEquiv sem (n + 1) hA J hJ)

local notation "oldTarget₀" => oldTarget sem n hA

theorem faceEquiv_val (J : GradedIndex ι) (hJ : ¬ A ⊆ J.1) (hj : J.2 ≤ n + 4)
    (d : (cut₀).below J) :
    (faceEquiv sem n hA J hJ hj d).1 = (oldTarget₀ d.1).1 :=
  CanonicalRecursiveBoundaryTransport.properEquiv_val sem hA hJ _

theorem faceEquiv_cell (J : GradedIndex ι) (hJ : ¬ A ⊆ J.1) (hj : J.2 ≤ n + 4)
    (d : (cut₀).below J) :
    (carrier sem n hA).cell (faceEquiv sem n hA J hJ hj d).1 =
      (cut₀).cell d.1 := by
  rw [faceEquiv_val, oldTarget_cell]

local notation "RespectsSemanticsBelow₀" => RespectsSemanticsBelow (outputRows sem n hA hp)

theorem pullback_respects (J : GradedIndex ι) (hJ : ¬ A ⊆ J.1) (hj : J.2 ≤ n + 4)
    {p}
    (hpr : RespectsSemanticsBelow₀ J p) :
    RespectsSemanticsBelow (cutRows sem n) J (p ∘ faceEquiv sem n hA J hJ hj) :=
  GradeCutBoundary.pullback_respects hj
    (CanonicalRecursiveBoundaryTransport.pullback_respects sem hp (n + 1) hA J hJ hpr)

/-- Uniform active branch. Every auxiliary cap is retained. The only lifting
inputs concern the actual predecessor and the two old boundary faces. -/
theorem exists_lift
    (hb : CanonicalRecursiveRestoration.LowerBountiful sem n hA (predecessorState₀))
    {C} (hC : C ∈ D.plan) (hCA : C ≠ A) (hCc : n + 4 ≤ C.card)
    (hfull : ∃ c : (cut₀).below (C, n + 4),
      (cut₀).cell c.1 = (C, n + 4))
    {p}
    (hpr : RespectsSemanticsBelow₀ (C, n + 4) p)
    {q}
    (hqr : RespectsSemanticsBelow₀ (A, n + 4) q)
    {γ} (hγ : SelfVis (n + 4) γ) (hγb : γ ≠ ⊥)
    (hag : ∀ e, min (p e) γ = min (q (CellScheme.below.mono
      (show GradedLe (C, n + 4) (A, n + 4) from
        ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) e)) γ)
    (hactive : ∃ d ,
      (carrier sem n hA).grade d.1 = n + 4 ∧ γ < p d)
    {U V O}
    (hcover : ∀ d ,
      GradedLe ((cut₀).cell d) U ∨ GradedLe ((cut₀).cell d) V)
    (hCU : GradedLe (C, n + 4) U) (hOU : GradedLe O U) (hOV : GradedLe O V)
    (hinter : ∀ d , GradedLe ((cut₀).cell d) U →
      GradedLe ((cut₀).cell d) V → GradedLe ((cut₀).cell d) O)
    (hleft : CappedLift (cutRows sem n) hCU) (hright : CappedLift (cutRows sem n) hOV)
    (hU : U.2 ≤ n + 4) (hV : V.2 ≤ n + 4) :
    ∃ r ,
      RespectsSemanticsBelow₀ (A, n + 4) r ∧
      (∀ e, r (CellScheme.below.mono
        (show GradedLe (C, n + 4) (A, n + 4) from
          ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) e) = p e) ∧
      CappedEq r q γ := by
  have hCnot : ¬ A ⊆ C := fun h =>
    hCA (Finset.Subset.antisymm (D.isPlan.subset_of_mem hC) h)
  let E := faceEquiv sem n hA (C, n + 4) hCnot le_rfl
  let p₀ := p ∘ E
  have hp₀ := pullback_respects sem n hA hp (C, n + 4) hCnot le_rfl hpr
  obtain ⟨c, hci, hmax⟩ := AmbientGradeCharts.exists_maximizer hp₀ hfull
  let M := p₀ c
  have hpc : γ < M := by
    obtain ⟨d, hd, hpd⟩ := hactive
    obtain ⟨e, rfl⟩ := E.surjective d
    have he : (cut₀).grade e.1 = n + 4 := by
      change ((carrier sem n hA).cell (E e).1).2 = n + 4 at hd
      rw [faceEquiv_cell] at hd
      exact hd
    exact hpd.trans_le (hmax e he)
  have hc : (cut₀).grade c.1 = n + 4 := congrArg Prod.snd hci
  have hM : SelfVis (n + 4) M := by simpa only [hc] using (hp₀.orderly c).symm
  have hcle : GradedLe ((cut₀).cell c.1) (C, n + 4) := c.2
  let pc := fun e : (cut₀).belowCell c.1 =>
    p₀ ⟨e.1, e.2.trans hcle⟩
  have hpcLaw : RespectsSemanticsBelow (cutRows sem n)
      ((cut₀).cell c.1) pc := hp₀.mono hcle
  have hag₀ (e : (cut₀).below (C, n + 4)) :
      min (p₀ e) γ = min (q (oldTarget₀ e.1)) γ := by
    have he : CellScheme.below.mono
        (show GradedLe (C, n + 4) (A, n + 4) from
          ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) (E e) = oldTarget₀ e.1 :=
      Subtype.ext (faceEquiv_val sem n hA _ hCnot le_rfl e)
    simpa only [p₀, Function.comp_apply, he] using hag (E e)
  have hl : CappedLift (cutRows sem n) (hcle.trans hCU) := by
    simpa only [hci] using hleft
  obtain ⟨u, hu, hread, hcap⟩ := CanonicalRecursiveOwnerLift.exists_owner_capped_lift
    sem n hA hp (predecessorState₀) c.1 hc hpcLaw hqr hγ hγb
    (fun e => hag₀ ⟨e.1, e.2.trans hcle⟩) hpc
    hcover (hcle.trans hCU) hOU hOV hinter hl hright hU hV
  have huold (e : (cut₀).below (C, n + 4)) :
      u (oldTarget₀ e.1) = min (p₀ e) M := by
    have he : GradedLe ((cut₀).cell e.1) ((cut₀).cell c.1) := by
      rw [hci]; exact e.2
    exact hread ⟨e.1, he⟩
  have hreadPhys (e : (carrier sem n hA).below (C, n + 4)) :
      u (CellScheme.below.mono
        (show GradedLe (C, n + 4) (A, n + 4) from
          ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) e) = min (p e) M := by
    obtain ⟨d, rfl⟩ := E.surjective e
    have hd : CellScheme.below.mono
        (show GradedLe (C, n + 4) (A, n + 4) from
          ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) (E d) = oldTarget₀ d.1 :=
      Subtype.ext (faceEquiv_val sem n hA _ hCnot le_rfl d)
    rw [hd]
    exact huold d
  have hmaxPhys (e : (carrier sem n hA).below (C, n + 4))
      (he : (carrier sem n hA).grade e.1 = n + 4) : p e ≤ M := by
    obtain ⟨d, rfl⟩ := E.surjective e
    apply hmax d
    change ((carrier sem n hA).cell (E d).1).2 = n + 4 at he
    rw [faceEquiv_cell] at he
    exact he
  obtain ⟨r, hr, hrlit, hrcap, _⟩ := CanonicalRecursiveRestoration.restore
    sem n hA hp (predecessorState₀) hb hC (Nat.le_of_succ_le hCc)
    hpr hu hM hpc.le hreadPhys hmaxPhys hcap
  exact ⟨r, hr, hrlit, hrcap⟩

