/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.WholeDonorBoundary
import VaughtConjecture.Knight.RequestAttachment

/-! # Literal ordered restrictions of the inherited boundary

An occurrence-exact semantic face with a strictly increasing occurrence map
and the correct plan restricts literally to its input cell scheme. The
restricted occurrence map is the installed map, even when the input is not
an initial segment. Rows are recovered on every original lower-domain argument.

Both faces of `WholeDonorBoundary` satisfy these hypotheses. No legality of
the incomplete boundary, or of a future mixed completion, is assumed.
-/

namespace VaughtConjecture.Knight.OrderedFaceRestriction

open AmalgamationPlan   
open CellScheme.restrictFace (toCell belowMap)

variable {m n : ℕ} {B : FiniteScope n}
variable (D : SemScheme m) (K : CellScheme (ι := Fin n) Finset.univ)
  (sem : Semantics K) (f : Fin m ↪ Fin n) (hB : Finset.univ.image f = B)
  (F : ExactSemanticFace (PointImageSemantics.rows hB D.rows) sem)
  (hmono : StrictMono F.map)
  (hplan : Plan.restrictPlan K.plan B = D.scheme.plan.image (Finset.image f))

include hB hplan in
theorem visible : Finset.univ.image f ∈ K.plan := by
  have hh : B ∈ Plan.restrictPlan K.plan B := by
    rw [hplan, ← hB]
    exact Finset.mem_image.mpr ⟨_, D.scheme.isPlan.domain_mem, rfl⟩
  exact hB ▸ (Finset.mem_inter.mp hh).1

theorem scope_map c : K.scope (F.map c) ⊆ Finset.univ.image f := by
  change (K.cell (F.map c)).1 ⊆ _
  rw [F.index c]
  exact Finset.image_subset_image (Finset.subset_univ _)

local notation "scope_map₀" => scope_map D K sem f hB F

local notation "visible₀" => visible D K f hB hplan

include F hmono in
theorem card_face :
    (K.restrictFace f (visible₀)).card = D.scheme.card :=
  CellScheme.restrictFace.card_restrictFace_of_emb K f (visible₀)
    hmono (scope_map₀)
    (fun d hd => F.exhaustive d (hB ▸ hd))

local notation "card_face₀" => card_face D K sem f hB F hmono hplan

theorem toCell_eq c :
    toCell K f (visible₀)
      (Fin.cast (card_face₀).symm c) = F.map c :=
  CellScheme.restrictFace.toCell_cast_eq_of_emb K f (visible₀)
    hmono (scope_map₀) (card_face₀) c

local notation "toCell_eq₀" => toCell_eq D K sem f hB F hmono hplan

include F hmono in
variable {D K sem f hB F} in
/-- Literal cell-scheme equality, not just an equivalence of lawful sections. -/
theorem scheme_eq : K.restrictFace f (visible₀) = D.scheme := by
  refine CellScheme.ext_of_components ?_ card_face₀ ?_
  · apply Finset.image_injective (Finset.image_injective f.injective)
    rw [image_restrictFace_plan, hB, hplan]
  · intro c
    rw [CellScheme.restrictFace.cell_eq, toCell_eq₀]
    apply Prod.ext
    · apply Finset.image_injective f.injective
      rw [CellScheme.image_pullCell_fst K f (scope_map₀ c)]
      exact congrArg Prod.fst (F.index c)
    · change K.grade (F.map c) = D.scheme.grade c
      exact congrArg Prod.snd (F.index c)

private theorem E_congr {c c'} (h : c = c') x :
    sem.E c x = sem.E c' ⟨x.1, h ▸ x.2⟩ := by
  subst h
  rfl

/-- Every restricted row argument is exactly the corresponding original argument. -/
theorem row_eq c (d : D.scheme.belowCell c) :
    (sem.restrictFace f (visible₀)).E
      (Fin.cast (card_face₀).symm c)
      ⟨Fin.cast (card_face₀).symm d.1, by
        rw [CellScheme.cell_cast_of_eq (scheme_eq hmono hplan) d.1,
          CellScheme.cell_cast_of_eq (scheme_eq hmono hplan) c]
        exact d.2⟩ = D.rows.E c d := by
  refine (E_congr K sem (toCell_eq₀ c) _).trans ?_
  have hr := F.row c (PointImageSemantics.belowEquiv hB c d)
  refine (congrArg (sem.E (F.map c)) (Subtype.ext ?_)).trans hr
  exact toCell_eq₀ d.1


