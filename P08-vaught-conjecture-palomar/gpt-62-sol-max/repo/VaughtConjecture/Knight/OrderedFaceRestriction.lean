/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.WholeDonorBoundary
public import VaughtConjecture.Knight.RequestAttachment

@[expose] public section

namespace VaughtConjecture.Knight.OrderedFaceRestriction

open AmalgamationPlan Transform Value ExtOrd

open CellScheme.restrictFace (toCell belowMap)

/-- A literal semantic restriction, with its enumeration identified in the ambient carrier. -/
structure Receipt {m n : ℕ} (D : SemScheme m) (E : SemScheme n) (f : Fin m ↪ Fin n)
    (occ : Cell D.scheme → Cell E.scheme) : Prop where
  visible : Finset.univ.image f ∈ E.scheme.plan
  restrict_eq : E.restrictFace f visible = D
  occurrence : ∀ d, toCell E.scheme f visible (SemScheme.castCell restrict_eq.symm d) = occ d

section

variable {m n : ℕ} {B : Finset (Fin n)}

variable (D : SemScheme m) (K : CellScheme (ι := Fin n) Finset.univ)
  (sem : Semantics K) (f : Fin m ↪ Fin n) (hB : Finset.univ.image f = B)
  (F : ExactSemanticFace (PointImageSemantics.rows D.scheme f hB D.rows) sem)
  (hmono : StrictMono F.map)
  (hplan : Plan.restrictPlan K.plan B = D.scheme.plan.image (Finset.image f))

include hB hplan in
theorem visible : Finset.univ.image f ∈ K.plan := by
  have hh : B ∈ Plan.restrictPlan K.plan B := by
    rw [hplan, ← hB]
    exact Finset.mem_image.mpr ⟨_, D.scheme.isPlan.domain_mem, rfl⟩
  exact hB ▸ (Finset.mem_inter.mp hh).1

theorem scope_map (c : Cell D.scheme) : K.scope (F.map c) ⊆ Finset.univ.image f := by
  change (K.cell (F.map c)).1 ⊆ _
  rw [F.index c]
  exact Finset.image_subset_image (Finset.subset_univ _)

include F hmono in
theorem card_face :
    (K.restrictFace f (visible D K f hB hplan)).card = D.scheme.card :=
  CellScheme.restrictFace.card_restrictFace_of_emb K f (visible D K f hB hplan)
    hmono (scope_map D K sem f hB F)
    (fun d hd => F.exhaustive d (hB ▸ hd))

theorem toCell_eq (c : Cell D.scheme) :
    toCell K f (visible D K f hB hplan)
      (Fin.cast (card_face D K sem f hB F hmono hplan).symm c) = F.map c :=
  CellScheme.restrictFace.toCell_cast_eq_of_emb K f (visible D K f hB hplan)
    hmono (scope_map D K sem f hB F) (card_face D K sem f hB F hmono hplan) c

include F hmono in
/-- Literal cell-scheme equality, not just an equivalence of lawful sections. -/
theorem scheme_eq : K.restrictFace f (visible D K f hB hplan) = D.scheme := by
  refine CellScheme.ext_of_components ?_ (card_face D K sem f hB F hmono hplan) ?_
  · apply Finset.image_injective (Finset.image_injective f.injective)
    rw [image_restrictFace_plan, hB, hplan]
  · intro c
    rw [CellScheme.restrictFace.cell_eq, toCell_eq D K sem f hB F hmono hplan]
    apply Prod.ext
    · apply Finset.image_injective f.injective
      rw [CellScheme.image_pullCell_fst K f (scope_map D K sem f hB F c)]
      exact congrArg Prod.fst (F.index c)
    · change K.grade (F.map c) = D.scheme.grade c
      exact congrArg Prod.snd (F.index c)

private theorem E_congr {c c' : Cell K} (h : c = c') (x : K.below (K.cell c)) :
    sem.E c x = sem.E c' ⟨x.1, h ▸ x.2⟩ := by
  subst h
  rfl

/-- Every restricted row argument is exactly the corresponding original argument. -/
theorem row_eq (c : Cell D.scheme) (d : D.scheme.below (D.scheme.cell c)) :
    (sem.restrictFace f (visible D K f hB hplan)).E
      (Fin.cast (card_face D K sem f hB F hmono hplan).symm c)
      ⟨Fin.cast (card_face D K sem f hB F hmono hplan).symm d.1, by
        rw [CellScheme.cell_cast_of_eq (scheme_eq D K sem f hB F hmono hplan) d.1,
          CellScheme.cell_cast_of_eq (scheme_eq D K sem f hB F hmono hplan) c]
        exact d.2⟩ = D.rows.E c d := by
  refine (E_congr K sem (toCell_eq D K sem f hB F hmono hplan c) _).trans ?_
  have hr := F.row c (PointImageSemantics.belowEquiv D.scheme f hB c d)
  refine (congrArg (sem.E (F.map c)) (Subtype.ext ?_)).trans hr
  exact toCell_eq D K sem f hB F hmono hplan d.1

end

/-- An order-preserving exact face with the right plan realizes the literal restriction. -/
theorem of_face {m n : ℕ} (D : SemScheme m) (E : SemScheme n) (f : Fin m ↪ Fin n)
    {U : Finset (Fin n)} (hf : Finset.univ.image f = U)
    (G : ExactSemanticFace (PointImageSemantics.rows D.scheme f hf D.rows) E.rows)
    (hm : StrictMono G.map)
    (hp : Plan.restrictPlan E.scheme.plan U = D.scheme.plan.image (Finset.image f)) :
    Receipt D E f G.map := by
  have he := scheme_eq D E.scheme E.rows f hf G hm hp
  exact ⟨visible D E.scheme f hf hp,
    SemScheme.ext_of_components (congrArg CellScheme.plan he) (congrArg CellScheme.card he)
      (CellScheme.cell_cast_of_eq he) (row_eq D E.scheme E.rows f hf G hm hp),
    toCell_eq D E.scheme E.rows f hf G hm hp⟩

namespace Receipt

open TypeTower StageType

variable {m n : ℕ} {D : SemScheme m} {E : SemScheme n} {f : Fin m ↪ Fin n}
  {occ : Cell D.scheme → Cell E.scheme} (R : Receipt D E f occ)

theorem toCell_eq (d : Cell (E.restrictFace f R.visible).scheme) :
    toCell E.scheme f R.visible d = occ (SemScheme.castCell R.restrict_eq d) := by
  simpa only [SemScheme.castCell, Fin.cast_cast, Fin.cast_eq_self] using
    R.occurrence (SemScheme.castCell R.restrict_eq d)

theorem extendsDomain {γ : Ordinal.{0}} {p : S γ m} {E : SemScheme (m + 1)}
    {occ : Cell p.scheme.scheme → Cell E.scheme}
    (R : Receipt p.scheme E Fin.castSuccEmb occ) : ExtendsDomain p E :=
  ⟨R.visible, R.restrict_eq⟩

theorem labels_iff {γ : Ordinal.{0}} {q : S γ n} {occ : Cell D.scheme → Cell q.scheme.scheme}
    (R : Receipt D q.scheme f occ) (p : S γ m) (h : D = p.scheme) :
    typeMap f q = some p ↔ ∀ d, q.label (occ d) = p.label (SemScheme.castCell h d) := by
  subst D
  rw [typeMap_eq_some_iff_labels f q p R.visible R.restrict_eq]
  constructor
  · intro hl d
    have hd := hl (SemScheme.castCell R.restrict_eq.symm d)
    rw [R.occurrence] at hd
    simpa only [SemScheme.castCell, Fin.cast_cast, Fin.cast_eq_self] using hd
  · intro hl d
    simpa only [R.toCell_eq, SemScheme.castCell, Fin.cast_eq_self] using
      hl (SemScheme.castCell R.restrict_eq d)

end Receipt

end VaughtConjecture.Knight.OrderedFaceRestriction


namespace VaughtConjecture.Knight.WholeDonorBoundary.Input

open OrderedFaceRestriction

variable {l m nL nR : ℕ} {B C : Finset (Fin l)} {R : Finset (Finset (Fin l))}
  (I : Input Finset.univ B C R m nL nR) {E : SemScheme l} (h : E.scheme.plan = R)

include h

/-- A placed original face in the final carrier gives its literal restriction. -/
theorem left_receipt (G : ExactSemanticFace I.leftRows E.rows) (hm : StrictMono G.map) :
    Receipt I.left E I.placeLeft G.map :=
  of_face I.left E I.placeLeft I.imageLeft G hm (h.symm ▸ I.planLeft)

theorem right_receipt (G : ExactSemanticFace I.rightRows E.rows) (hm : StrictMono G.map) :
    Receipt I.right E I.placeRight G.map :=
  of_face I.right E I.placeRight I.imageRight G hm (h.symm ▸ I.planRight)

end VaughtConjecture.Knight.WholeDonorBoundary.Input
