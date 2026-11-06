import PalomarProof.Ordinal
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CanonicalRecursiveCoding
import VaughtConjecture.Knight.CoatomRecursiveDisplay
import VaughtConjecture.Knight.MaximalFullLayer

/-! # Complete coded coatom output with an active maximal apex

For input arities at least three, the recursive output supplies every index
below the final grade. The added final cell is activated at literal top.
Both given displays and the stage bound are retained. Ordered restriction
equations and the two small arities are not asserted here.
-/

namespace VaughtConjecture.Knight.CoatomRecursiveApex
open  Value ExtOrd AmalgamationPlan AmalgamatedBoundaryPlan
open SemSchemeBoundaryInput CoatomRecursiveInput
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {s : Step A} {m n : ℕ}
variable (I : Input s m (n + 3) (n + 3))

include I in
theorem card_eq : A.card = n + 4 := by
  have hh := I.card_left
  rw [Finset.card_erase_of_mem s.ha] at hh
  
  omega

abbrev finalHeight : n + 4 ≤ A.card := (card_eq I).ge
abbrev scheme := MaximalFullLayer.scheme (CoatomRecursiveInput.scheme I)
  (n + 3) (n + 4) (by omega) (finalHeight I)
abbrev old := MaximalFullLayer.old (CoatomRecursiveInput.scheme I)
  (n + 3) (n + 4) (by omega) (finalHeight I)
abbrev apex := MaximalFullLayer.apex (CoatomRecursiveInput.scheme I)
  (n + 3) (n + 4) (by omega) (finalHeight I)
abbrev ownerEquiv := MaximalFullLayer.ownerEquiv (CoatomRecursiveInput.scheme I)
  (n + 3) (n + 4) (grade_bound I) (by omega) (finalHeight I)
abbrev left d := old I (CoatomRecursiveDisplay.left I d)
abbrev right d := old I (CoatomRecursiveDisplay.right I d)

theorem complete : (scheme I).IsComplete := by
  apply MaximalFullLayer.complete
  intro J hJ hne
  apply complete_through I J hJ
  have hgrade := (Plan.mem_gradedPlan.mp hJ).2.2
  have hscope := (CoatomRecursiveInput.scheme I).isPlan.subset_of_mem
    (Plan.mem_gradedPlan.mp hJ).1
  have hc := Finset.card_le_card hscope
  by_contra hh
  have hsize : J.1.card = A.card := by rw [card_eq I] at hc ⊢; omega
  have he  := Finset.eq_of_subset_of_card_le hscope hsize.ge
  apply hne
  apply Prod.ext he
  rw [card_eq I] at hc
  omega

theorem exists_display {α} (hα : Order.IsSuccLimit α)
    {p} {q}
    (hp : RespectsSemantics I.left.rows p) (hq : RespectsSemantics I.right.rows q)
    (hpb : ∀ d, p d < ofOrd α ∨ p d = ⊤) (hqb : ∀ d, q d < ofOrd α ∨ q d = ⊤)
    (ha : ∀ i, p (I.shared.f i) = q (I.shared.g i)) :
    ∃ out r,
      out.IsConsistent ∧ out.IsBountiful ∧ out.IsCoded ∧ RespectsSemantics out r ∧
      (∀ d, r d < ofOrd α ∨ r d = ⊤) ∧
      (∀ c d, out.E (old I c) (ownerEquiv I c d) = (rows I).E c d) ∧
      (∀ d, r (left I d) = p d) ∧ (∀ d, r (right I d) = q d) ∧ r (apex I) = ⊤ := by
  obtain ⟨u, hu, hub, hul, hur⟩ := CoatomRecursiveDisplay.joint_bounded I hα hp hq hpb hqb ha
  obtain ⟨out, r, hc, hb, hcode, hr, he, hread, htop⟩ :=
    MaximalFullLayer.exists_active (CoatomRecursiveInput.scheme I) (rows I)
      (n + 3) (n + 4) (grade_bound I) (by omega) (finalHeight I) (by omega)
      (consistent I) (bountiful I) (CanonicalRecursiveCoding.coatom I) hu
  dsimp only [PointwiseEq, Function.comp_def] at hread
  refine ⟨out, fun d => truncExt α (r d), hc, hb, hcode, hr.truncate hα,
    fun _ => truncExt_bound, he, ?_, ?_, ?_⟩
  · intro d
    change truncExt α (r (old I (CoatomRecursiveDisplay.left I d))) = p d
    rw [hread, hul]
    exact truncExt_id_of_bound (hpb d)
  · intro d
    change truncExt α (r (old I (CoatomRecursiveDisplay.right I d))) = q d
    rw [hread, hur]
    exact truncExt_id_of_bound (hqb d)
  · simp_all

/-- Constructed output data; none of these fields is a hypothesis of the constructor. -/
structure Display (α : Ordinal₀) (p : CellLabels I.left.scheme)
    (q : CellLabels I.right.scheme) where
  rows : Semantics (scheme I)
  label : CellLabels (scheme I)
  consistent : rows.IsConsistent
  bountiful : rows.IsBountiful
  coded : rows.IsCoded
  lawful : RespectsSemantics rows label
  bounded : ∀ d, label d < ofOrd α ∨ label d = ⊤
  old_row : ∀ c d, rows.E (old I c) (ownerEquiv I c d) = (CoatomRecursiveInput.rows I).E c d
  left_read : ∀ d, label (left I d) = p d
  right_read : ∀ d, label (right I d) = q d
  top_read : label (apex I) = ⊤

def display {α} (hα : Order.IsSuccLimit α)
    {p} {q}
    (hp : RespectsSemantics I.left.rows p) (hq : RespectsSemantics I.right.rows q)
    (hpb : ∀ d, p d < ofOrd α ∨ p d = ⊤) (hqb : ∀ d, q d < ofOrd α ∨ q d = ⊤)
    (ha : ∀ i, p (I.shared.f i) = q (I.shared.g i)) : Display I α p q := by
  let result := exists_display I hα hp hq hpb hqb ha
  let out := Classical.choose result
  let r := Classical.choose (Classical.choose_spec result)
  have hs := Classical.choose_spec (Classical.choose_spec result)
  exact ⟨out, r, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1,
    hs.2.2.2.2.2.1, hs.2.2.2.2.2.2.1, hs.2.2.2.2.2.2.2.1, hs.2.2.2.2.2.2.2.2⟩

variable {α : Ordinal₀} {s' : Step (Finset.univ : Finset (Fin (n + 4)))}
  {I' : Input s' m (n + 3) (n + 3)} {p : CellLabels I'.left.scheme}
  {q : CellLabels I'.right.scheme}

/-- An actual legal stage type, including coding and completeness. -/
def Display.toType (O : Display I' α p q) : S α (n + 4) where
  scheme := ⟨scheme I', O.rows, O.coded, O.consistent, O.bountiful, complete I'⟩
  label := O.label
  label_bound := O.bounded
  respects := O.lawful

theorem Display.maximal (O : Display I' α p q) : O.toType.HasMaximalFullCell := by
  refine ⟨apex I', ?_, ?_⟩
  · exact congrArg Prod.snd (MaximalFullLayer.apex_index
      (CoatomRecursiveInput.scheme I') (by omega) (finalHeight I'))
  · intro d
    change O.label d ≤ O.label (apex I')
    rw [O.top_read]
    exact le_top

/-- Arbitrary compatible input types produce a complete coded stage type
with both literal displays and a maximal full-grade top. The two ordered
`typeMap` identities are still a separate theorem. -/
def ofCompatible (hα : Order.IsSuccLimit α) (C : CoatomPair (n + 2))
    {pa pb} (h : C.Compatible pa pb) :=
  display _ hα pa.respects pb.respects pa.label_bound pb.label_bound
    (CoatomRecursiveDisplay.compatible_labels C h)

