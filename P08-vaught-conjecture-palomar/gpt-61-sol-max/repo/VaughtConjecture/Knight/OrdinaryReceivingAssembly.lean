/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.OrdinaryReceivingSources
import VaughtConjecture.Knight.OrdinaryPredecessorSupply
import VaughtConjecture.Knight.OrdinaryFinalBountiful
import VaughtConjecture.Knight.OrdinaryFinalInstallation

/-! # Constructed legal ordinary receiving carrier

Compose KVC's actual scope predecessor (`8ab4f5e`) with V-C's final pair
theorem (`4eb4e3e`) and the stage-correct weighted/apex installer. Neither
predecessor existence nor output bountifulness is an input. The input consists
of the two literal legal schemes, their attached plan, and reference data
whose face is that same literal overlap. The final threshold is at least four.
-/

namespace VaughtConjecture.Knight.OrdinaryReceivingAssembly
open   ExtOrd AmalgamationPlan CappedDonor CappedDonor.Ref
open  OrbitPrefixSupport SharpWitnessComposition
noncomputable section

variable {I : Type*} [Fintype I] {nP n : ℕ}
variable {B T : Finset (Fin (n + 5))} {plan : Finset (Finset (Fin (n + 5)))}
variable (W : WholeDonorBoundary.Input Finset.univ B T plan nP (n + 4) (nP + 1))
variable (R : Ref I nP (n + 4) (n + 4) W.right W.left)
variable (hunion : (Finset.univ : Finset (Fin (n + 5))) = B ∪ T)
variable (hface : ∀ i ,
  ∃ d ,
    d.1 = W.shared.g i ∧ (R.face d).1 = W.shared.f i)

include W in
def private_card :=
  OrdinaryFinalBountiful.card_S W.placeLeft W.imageLeft

include W in
def request_card :=
  OrdinaryFinalBountiful.card_S W.placeRight W.imageRight

include W in
theorem private_ne : B ≠ Finset.univ := by
  intro he
  have h := private_card W
  rw [he, Finset.card_univ, Fintype.card_fin] at h
  omega

include R in
theorem request_ne : T ≠ Finset.univ := by
  intro he
  have h := request_card W
  rw [he, Finset.card_univ, Fintype.card_fin] at h
  have := R.arity_lt
  omega

abbrev grid :=
  PairedSlotComparison.sourceGrid (n + 4) (Fintype.card (Field W.right W.left))

abbrev ceiling := CanonicalFieldLayer.ceiling (n + 4) (Field W.right W.left)

/-- The global predecessor is built on the given literal boundary. -/
def predecessor : OrdinaryPredecessorSupply.Output W (n + 4) (grid W) (ceiling W) :=
  OrdinaryPredecessorSupply.build W n (private_ne W) (request_ne W R) hunion
    (Finset.card_fin _) (private_card W) ((request_card W) ▸ R.arity_lt)
    (fun _ hz => PairedSlotComparison.sourceGrid_visible hz)
    (PairedSlotComparison.sourceGrid_visible
      (PairedSlotComparison.sourceGrid_endpoint le_rfl))
    (ofOrd_ne_top _) (PairedSlotComparison.sourceGrid_endpoint le_rfl)

local notation "predecessor₀" => predecessor W R hunion

abbrev lower a :=
  (predecessor₀).render
    (OrdinaryReceivingSources.boundary_lawful W R hface a)
    (OrdinaryReceivingSources.boundary_bound W R hface a)

local notation "lower₀" => lower W R hunion hface

theorem lower_private a d :
    lower₀ a ((predecessor₀).leftFace.map d) = a.val (.priv d) := (congrArg (lower₀ a)
    ((predecessor₀).left_map d)).trans
      (((predecessor₀).readback _ _ _).trans
        (OrdinaryReceivingSources.boundary_private W R a d))

theorem lower_request a d :
    lower₀ a ((predecessor₀).rightFace.map d) = a.val (.req d) := (congrArg (lower₀ a)
    ((predecessor₀).right_map d)).trans
      (((predecessor₀).readback _ _ _).trans
        (OrdinaryReceivingSources.boundary_request W R hface a d))

/-- All final sources use the same fixed grid and ceiling on the same predecessor. -/
def input := by
  let O := predecessor₀
  refine OrdinaryFinalCatalogue.install R O.rows (by simp) ?_
    lower₀ (fun a => (O.lawful _ _).toBelow _) (fun a d _ => O.bound _ _ d) ?_
  · intro d hd
    have hs : O.carrier.scope d = Finset.univ :=
      Finset.Subset.antisymm (Finset.subset_univ _) hd.1
    exact (not_le_of_gt (O.full_below d hs)) hd.2
  · intro a b h hh hab d _
    exact O.agreement _ _ _ _ hh (CanonicalFieldLayer.grid_bound hh)
      (OrdinaryReceivingSources.boundary_agreement W R hface hab) d

theorem lower_support (a : OrdinaryFinalCatalogue.Member R)
    d :
    Supported (n + 4) ((grid W) : Set ExtOrd) a.val (lower₀ a d) :=
  ((predecessor₀).support _ _ d).substitute
    (fun _ hz => PairedSlotComparison.sourceGrid_visible hz)
    (OrdinaryReceivingSources.boundary_support W R hface a _)

/-- New owners have own-grade short rows; every argument of any other owner
is an original field. This derives the decoder's long-row alternative. -/
theorem owners a
    (c : (predecessor₀).carrier.below (Finset.univ, n + 4)) :
    (∀ d, Short ((predecessor₀).carrier.grade c.1)
      ((predecessor₀).rows.E c.1 d)) ∨
    (∀ d : (predecessor₀).carrier.below
        ((predecessor₀).carrier.cell c.1),
      ∃ f : Field W.right W.left, lower₀ a d.1 = a.val f) := by
  rcases (predecessor₀).classification c.1 with hs | ho
  · exact Or.inl hs
  · right
    intro d
    obtain ⟨x, hx⟩ := ho d
    obtain ⟨f, hf⟩ := OrdinaryReceivingSources.boundary_field W R hface a x
    refine ⟨f, ?_⟩
    rw [← hx]
    exact ((predecessor₀).readback _ _ x).trans hf

theorem predecessor_lift CI BJ
    (hi : CI ∈ Plan.gradedPlan (predecessor₀).carrier.plan)
    (hj : BJ ∈ Plan.gradedPlan (predecessor₀).carrier.plan)
    (h : GradedLe CI BJ) (hne : ¬ GradedLe (Finset.univ, n + 4) BJ) :
    CoatomBoundaryExtension.CappedLift (predecessor₀).rows h := by
  rw [(predecessor₀).plan] at hi hj
  by_cases hs : BJ.1 = Finset.univ
  · exact (predecessor₀).lower_lift CI BJ hi hj h (by
      simp_all [VaughtConjecture.Knight.GradedLe])
  · exact?

/-- Exhaustive final-layer lifting, with the predecessor clauses discharged. -/
def bountiful :=
  OrdinaryFinalBountiful.bountiful R (input W R hunion hface) W.placeLeft W.imageLeft
    (predecessor₀).leftFace (fun _ _ => rfl) rfl rfl
    (fun a d _ => lower_support W R hunion hface a d) (owners W R hunion hface)
    (lower_private W R hunion hface) (Finset.card_fin _)
    (predecessor₀).mute (predecessor_lift W R hunion)

theorem complete_before_final J
    (hJ : J ∈ Plan.gradedPlan (predecessor₀).carrier.plan)
    (hg : J.2 ≤ n + 4) (hne : J ≠ (Finset.univ, n + 4)) :
    ∃ d, (predecessor₀).carrier.cell d = J := by
  apply (predecessor₀).complete J
  · rwa [(predecessor₀).plan] at hJ
  · grind

/-- The complete coded legal scheme, including its mute full-grade apex. -/
def semScheme : SemScheme (n + 5) :=
  OrdinaryFinalInstallation.semScheme R (input W R hunion hface)
    (predecessor₀).grade_bound (predecessor₀).consistent
    (predecessor₀).coded (bountiful W R hunion hface)
    (complete_before_final W R hunion) (fun _ _ => rfl) rfl
    (fun a d _ => lower_support W R hunion hface a d)

