/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Interval
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Lattice.Lemmas
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace VaughtConjecture.AmalgamationPlan

namespace Plan

variable {α : Type*} [DecidableEq α]

/-- `IsPlan A P`: `P` is a support plan on the finite set `A` (Knight, Def. 2.1.1).

Implemented as an inductive predicate: `empty` and `singleton` are the two base plans (the full
powersets of `∅` and `{a}`), and `step` amalgamates plans `Q` on `A ∖ {a}` and `R` on
`A ∖ {b}` (`a ≠ b`) that both see `A ∖ {a, b}` and agree below it into `Q ∪ R ∪ {A}`. -/
inductive IsPlan : Finset α → Finset (Finset α) → Prop
  | empty :
      IsPlan (∅ : Finset α) {∅}
  | singleton (a : α) :
      IsPlan ({a} : Finset α) {∅, {a}}
  | step {A : Finset α} {a b : α}
      {Q R P : Finset (Finset α)}
      (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b)
      (hQ : IsPlan (A.erase a) Q)
      (hR : IsPlan (A.erase b) R)
      (h_inter_mem : ((A.erase a).erase b) ∈ Q ∧ ((A.erase a).erase b) ∈ R)
      (h_restr_eq : Q ∩ (((A.erase a).erase b).powerset) =
                    R ∩ (((A.erase a).erase b).powerset))
      (hP : P = Q ∪ R ∪ {A}) :
      IsPlan A P

/-- Restriction of a plan to a subset `B` of its domain (Knight, Def. 2.1.5): the visible
faces contained in `B`. -/
def restrictPlan (P : Finset (Finset α)) (B : Finset α) : Finset (Finset α) :=
  P ∩ B.powerset

/-- The graded plan `P̂` (Knight, Def. 2.1.8): the pairs `(B, j)` with `B` a visible face and
grade `0 < j ≤ |B|`.  These index the cells of a cell scheme over `P`. -/
def gradedPlan (P : Finset (Finset α)) : Finset (Finset α × ℕ) :=
  P.biUnion (fun B =>
    (Finset.Ioc 0 B.card).image (fun j => (B, j))
  )

/-- Membership in the graded plan, spelled out: the face is visible and the grade is positive
and at most the size of the face. -/
def MemGraded (P : Finset (Finset α)) (BJ : Finset α × ℕ) : Prop :=
  BJ.1 ∈ P ∧ 0 < BJ.2 ∧ BJ.2 ≤ BJ.1.card

theorem mem_gradedPlan {P : Finset (Finset α)} {BJ : Finset α × ℕ} :
    BJ ∈ gradedPlan P ↔ MemGraded P BJ := by
  unfold gradedPlan MemGraded
  grind

/-- Every visible face is a subset of the domain. -/
theorem IsPlan.subset_of_mem {A : Finset α} {P : Finset (Finset α)}
    (hP : IsPlan A P) {S : Finset α} (hS : S ∈ P) : S ⊆ A := by
  induction hP with
  | empty =>
    simp only [Finset.mem_singleton] at hS
    subst hS; exact Finset.empty_subset _
  | singleton a =>
    simp_all
  | step ha hb hab hQ hR h_inter_mem h_restr_eq hP ihQ ihR =>
    subst hP
    simp only [Finset.mem_union, Finset.mem_singleton] at hS
    rcases hS with (hS | hS) | rfl
    · exact (ihQ hS).trans (Finset.erase_subset _ _)
    · exact (ihR hS).trans (Finset.erase_subset _ _)
    · exact Finset.Subset.refl _

/-- The domain is a visible face. -/
theorem IsPlan.domain_mem {A : Finset α} {P : Finset (Finset α)}
    (hP : IsPlan A P) : A ∈ P := by
  induction hP with
  | empty => exact Finset.mem_singleton_self _
  | singleton a => simp
  | step ha hb hab hQ hR h_inter_mem h_restr_eq hP ihQ ihR =>
    subst hP; simp

/-- The empty face is visible. -/
theorem IsPlan.empty_mem {A : Finset α} {P : Finset (Finset α)}
    (hP : IsPlan A P) : ∅ ∈ P := by
  induction hP with
  | empty => exact Finset.mem_singleton_self _
  | singleton a => simp
  | step ha hb hab hQ hR h_inter_mem h_restr_eq hP ihQ ihR =>
    subst hP
    simp only [Finset.mem_union, Finset.mem_singleton]
    left; left; exact ihQ

/-- **Pivot rigidity** (Knight-VC `PaperExactPlanTraceGlue`): for `2 ≤ |A|` the visible
co-arity-one faces `A ∖ {z}` are exactly those at the two pivots `a ≠ b` of (any) step
derivation of the plan, the double erasure `A ∖ {a, b}` is visible, and no visible face other
than `A` contains both pivots.  So the pivot pair is determined by the plan, and every step
decomposition uses it. -/
theorem IsPlan.pivot_pair {A : Finset α} {P : Finset (Finset α)}
    (hP : IsPlan A P) (hA : 2 ≤ A.card) :
    ∃ a b, a ∈ A ∧ b ∈ A ∧ a ≠ b ∧
      (∀ z ∈ A, A.erase z ∈ P ↔ (z = a ∨ z = b)) ∧
      (A.erase a).erase b ∈ P ∧
      ∀ M ∈ P, a ∈ M → b ∈ M → M = A := by
  match hP with
  | .empty => simp at hA
  | .singleton c => simp at hA
  | .step (a := a) (b := b) ha hb hab hQ hR hmem _hre rfl =>
    refine ⟨a, b, ha, hb, hab, ?_, ?_, ?_⟩
    · intro z hz
      constructor
      · intro hzP
        rcases Finset.mem_union.mp hzP with h | h
        · rcases Finset.mem_union.mp h with hq | hr
          · left
            by_contra hne
            have haz : a ∈ A.erase z := by grind
            exact Finset.notMem_erase a A (hQ.subset_of_mem hq haz)
          · right
            by_contra hne
            have hbz : b ∈ A.erase z := by grind
            exact Finset.notMem_erase b A (hR.subset_of_mem hr hbz)
        simp_all
      · rintro (rfl | rfl)
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ hQ.domain_mem)
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hR.domain_mem)
    · simp_all
    · intro M hM haM hbM
      rcases Finset.mem_union.mp hM with h | h
      · rcases Finset.mem_union.mp h with hq | hr
        · exact absurd (hQ.subset_of_mem hq haM) (Finset.notMem_erase a A)
        · exact absurd (hR.subset_of_mem hr hbM) (Finset.notMem_erase b A)
      · exact Finset.mem_singleton.mp h

/-- Restricting to the whole domain does not change a plan. -/
theorem IsPlan.restrict_self {A : Finset α} {P : Finset (Finset α)} (h : IsPlan A P) :
    restrictPlan P A = P :=
  Finset.inter_eq_left.mpr (fun _ hS => Finset.mem_powerset.mpr (h.subset_of_mem hS))

/-- On a subset of the left face, the right input contributes only overlap cells. -/
theorem restrict_union_of_subset {A B C D : Finset α} {Q R : Finset (Finset α)}
    (hR : IsPlan C R) (hDB : D ⊆ B) (hne : ¬ A ⊆ B)
    (hc : restrictPlan Q (B ∩ C) = restrictPlan R (B ∩ C)) :
    restrictPlan (Q ∪ R ∪ {A}) D = restrictPlan Q D := by
  ext S
  simp only [restrictPlan, Finset.mem_inter, Finset.mem_powerset, Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro ⟨(hS | hS) | rfl, hSD⟩
    · exact ⟨hS, hSD⟩
    · have hm : S ∈ restrictPlan R (B ∩ C) := Finset.mem_inter.mpr
        ⟨hS, Finset.mem_powerset.mpr (Finset.subset_inter (hSD.trans hDB) (hR.subset_of_mem hS))⟩
      rw [← hc] at hm
      exact ⟨(Finset.mem_inter.mp hm).1, hSD⟩
    grind
  tauto

private theorem erase_inter (A : Finset α) (a b : α) :
    A.erase a ∩ A.erase b = (A.erase a).erase b := by grind

/-- Restriction of a plan to a visible face is again a plan (Def. 2.1.5). -/
theorem restrict_isPlan {A B : Finset α} {P : Finset (Finset α)}
    (hP : IsPlan A P) (hB : B ∈ P) : IsPlan B (restrictPlan P B) := by
  induction hP with
  | empty =>
    simp only [Finset.mem_singleton] at hB
    subst B
    solve_by_elim
  | singleton a =>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hB
    rcases hB with rfl | rfl
    · solve_by_elim
    · rw [(IsPlan.singleton a).restrict_self]
      exact IsPlan.singleton a
  | @step A a b Q R P ha hb hab hQ hR hi hc hP ihQ ihR =>
    subst P
    have hca : restrictPlan Q (A.erase a ∩ A.erase b) = restrictPlan R (A.erase a ∩ A.erase b) := by
      simpa only [restrictPlan, erase_inter] using hc
    have hna : ¬ A ⊆ A.erase a := by grind
    have hnb : ¬ A ⊆ A.erase b := by grind
    simp only [Finset.mem_union, Finset.mem_singleton] at hB
    rcases hB with (hB | hB) | rfl
    · rw [restrict_union_of_subset hR (hQ.subset_of_mem hB) hna hca]
      exact ihQ hB
    · rw [Finset.union_comm Q R, restrict_union_of_subset hQ (hR.subset_of_mem hB) hnb
        (by simpa [Finset.inter_comm (A.erase b) (A.erase a)] using hca.symm)]
      exact ihR hB
    · exact (IsPlan.step ha hb hab hQ hR hi hc rfl).restrict_self.symm ▸
        IsPlan.step ha hb hab hQ hR hi hc rfl

private theorem restrictPlan_step_erase {A : Finset α} {a b : α} {Q R : Finset (Finset α)}
    (ha : a ∈ A) (hQ : IsPlan (A.erase a) Q) (hR : IsPlan (A.erase b) R)
    (hc : Q ∩ ((A.erase a).erase b).powerset = R ∩ ((A.erase a).erase b).powerset) :
    restrictPlan (Q ∪ R ∪ {A}) (A.erase a) = Q :=
  (restrict_union_of_subset hR (Finset.Subset.refl _) (by grind)
    (by grind [restrictPlan, erase_inter])).trans hQ.restrict_self

section Image

variable {β : Type*} [DecidableEq β] {f : α → β}

private theorem image_erase_on {A : Finset α} {a : α} (ha : a ∈ A) (hf : Set.InjOn f A) :
    (A.erase a).image f = (A.image f).erase (f a) := by
  ext y
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨x, ⟨hx, hA⟩, rfl⟩
    tauto
  grind

private theorem restrict_image_on {A B : Finset α} {Q : Finset (Finset α)}
    (hQ : ∀ S ∈ Q, S ⊆ A) (hBA : B ⊆ A) (hf : Set.InjOn f A) :
    restrictPlan (Q.image (Finset.image f)) (B.image f) = (restrictPlan Q B).image (Finset.image f) := by
  ext Y
  simp only [restrictPlan, Finset.mem_inter, Finset.mem_powerset, Finset.mem_image]
  constructor
  · rintro ⟨⟨S, hS, rfl⟩, hs⟩
    exact ⟨S, ⟨hS, (Finset.image_subset_image_iff_of_injOn hf (hQ S hS) hBA).mp hs⟩, rfl⟩
  grind

/-- Injectivity is needed only on the finite domain of the plan. -/
private theorem isPlan_image_on {A : Finset α} {P : Finset (Finset α)}
    (hP : IsPlan A P) (hf : Set.InjOn f A) : IsPlan (A.image f) (P.image (Finset.image f)) := by
  induction hP with
  | empty => solve_by_elim
  | singleton a => solve_by_elim
  | @step A a b Q R P ha hb hab hQ hR hi hc hP ihQ ihR =>
    subst P
    have hfa := image_erase_on ha hf
    have hfb := image_erase_on hb hf
    have hQf := ihQ (hf.mono (Finset.erase_subset a A))
    have hRf := ihR (hf.mono (Finset.erase_subset b A))
    rw [hfa] at hQf
    rw [hfb] at hRf
    have hAb : b ∈ A.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
    have hfab : ((A.erase a).erase b).image f = ((A.image f).erase (f a)).erase (f b) := by
      rw [image_erase_on hAb (hf.mono (Finset.erase_subset a A)), hfa]
    simp only [Finset.image_union, Finset.image_singleton]
    refine IsPlan.step (Finset.mem_image_of_mem f ha) (Finset.mem_image_of_mem f hb)
      (fun h => hab (hf ha hb h)) hQf hRf ?_ ?_ rfl
    · grind
    · rw [← hfab]
      change restrictPlan _ (((A.erase a).erase b).image f) = restrictPlan _ _
      have hsub : (A.erase a).erase b ⊆ A := by grind
      rw [restrict_image_on (fun S h => (hQ.subset_of_mem h).trans (Finset.erase_subset _ _)) hsub hf,
        restrict_image_on (fun S h => (hR.subset_of_mem h).trans (Finset.erase_subset _ _)) hsub hf]
      exact congrArg (Finset.image (Finset.image f)) hc

/-- Image transport along an embedding. -/
theorem isPlan_image {A : Finset α} {P : Finset (Finset α)} (f : α ↪ β) (hP : IsPlan A P) :
    IsPlan (A.image f) (P.image (Finset.image f)) :=
  isPlan_image_on hP f.injective.injOn

/-- Preimage transport follows by taking the inverse on the finite image. -/
theorem isPlan_comap {B : Finset β} {Q : Finset (Finset β)}
    (hQ : IsPlan B Q) (f : α ↪ β) {A : Finset α} (hAB : A.image f = B) :
    IsPlan A (A.powerset.filter (fun C => C.image f ∈ Q)) := by
  classical
  by_cases hA : A.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hA] at hAB ⊢
    subst B
    simp only [Finset.powerset_empty, Finset.filter_singleton, Finset.image_empty, hQ.empty_mem, if_true]
    exact IsPlan.empty
  letI : Nonempty α := ⟨hA.choose⟩
  let g := Function.invFun f
  have hl : Function.LeftInverse g f := Function.leftInverse_invFun f.injective
  have hr (b : β) (hb : b ∈ B) : f (g b) = b := by
    rw [← hAB] at hb
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hb
    rw [hl]
  have hg : Set.InjOn g B := by
    intro x hx y hy h
    rw [← hr x hx, ← hr y hy, h]
  have roundtrip (S : Finset α) : (S.image f).image g = S := by
    rw [Finset.image_image, Finset.image_congr (f := g ∘ f) (g := id) (fun x _ => hl x), Finset.image_id]
  have hB : B.image g = A := hAB ▸ roundtrip A
  have he : Q.image (Finset.image g) = A.powerset.filter (fun C => C.image f ∈ Q) := by
    ext S
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨T, hT, rfl⟩
      have hTB := hQ.subset_of_mem hT
      refine ⟨(Finset.image_subset_image hTB).trans hB.subset, ?_⟩
      rwa [Finset.image_image, Finset.image_congr (f := f ∘ g) (g := id) (fun x hx => hr x (hTB hx)), Finset.image_id]
    tauto
  rw [← he, ← hB]
  exact isPlan_image_on hQ hg

end Image

/-- Pullback of a plan on `Fin n` along `f : Fin m ↪ Fin n` whose range is a visible face:
`{C ⊆ Fin m | f[C] ∈ P}` is a plan on `Fin m`. -/
theorem pullback_isPlan_fin {n m : ℕ} (f : Fin m ↪ Fin n)
    {P : Finset (Finset (Fin n))} (hP : IsPlan Finset.univ P)
    (hr : Finset.univ.image f ∈ P) :
    IsPlan (Finset.univ : Finset (Fin m))
      ((Finset.univ : Finset (Fin m)).powerset.filter
        (fun C => (C.image f) ∈ P)) := by
  have hres := restrict_isPlan hP hr
  have heq : (Finset.univ : Finset (Fin m)).powerset.filter (fun C => (C.image f) ∈ P) =
      (Finset.univ : Finset (Fin m)).powerset.filter
        (fun C => (C.image f) ∈ restrictPlan P (Finset.univ.image f)) := by
    ext C
    simp only [Finset.mem_filter, Finset.mem_powerset, restrictPlan, Finset.mem_inter,
      Finset.mem_powerset]
    grind
  rw [heq]
  exact isPlan_comap hres f (by simp)

/-- Partial pullback of a plan along an embedding of index sets (the plan-level shadow of the
`TypeTower` partial `pull`): for `f : Fin n ↪ Fin m` and `P` on `Fin m`, the pullback is
`{C ⊆ Fin n | f[C] ∈ P}` when the range `f[Fin n]` is a visible face of `P`, and `none`
otherwise. -/
def pullbackPlan {n m : ℕ} (f : Fin n ↪ Fin m) (P : Finset (Finset (Fin m))) :
    Option (Finset (Finset (Fin n))) :=
  if _ : Finset.univ.image f ∈ P then
    some ((Finset.univ : Finset (Fin n)).powerset.filter (fun C => (C.image f) ∈ P))
  else
    none

theorem pullbackPlan_eq_some {n m : ℕ} (f : Fin n ↪ Fin m) {P : Finset (Finset (Fin m))}
    (hr : Finset.univ.image f ∈ P) :
    pullbackPlan f P =
      some ((Finset.univ : Finset (Fin n)).powerset.filter (fun C => (C.image f) ∈ P)) :=
  dite_eq_left hr

theorem pullbackPlan_eq_none {n m : ℕ} (f : Fin n ↪ Fin m) {P : Finset (Finset (Fin m))}
    (hr : Finset.univ.image f ∉ P) :
    pullbackPlan f P = none :=
  dite_eq_right hr

/-- Pullback along the identity is the identity on plans on `Fin n`. -/
theorem pullbackPlan_refl {n : ℕ} {P : Finset (Finset (Fin n))} (hP : IsPlan Finset.univ P) :
    pullbackPlan (Function.Embedding.refl (Fin n)) P = some P := by
  have hr : Finset.univ.image (Function.Embedding.refl (Fin n)) ∈ P := by
    simpa [Function.Embedding.coe_refl] using hP.domain_mem
  rw [pullbackPlan_eq_some _ hr]
  congr 1
  ext C
  simp [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and,
    Function.Embedding.coe_refl, Finset.image_id]

/-- **Conditional composition** of pullbacks (Knight, Lemma 2.1.11 style): when the
intermediate pullback `pullbackPlan g P` is defined (i.e. the range of `g` is visible), pulling
it back further along `f` agrees with the pullback along the composite `f.trans g` — including
definedness.  Nothing is asserted when the intermediate face is invisible, which is exactly the
conditional `pull_trans` law of `TypeTower`.  Holds for an arbitrary family `P`. -/
theorem pullbackPlan_trans {ℓ m n : ℕ} (f : Fin ℓ ↪ Fin m) (g : Fin m ↪ Fin n)
    {P : Finset (Finset (Fin n))} {Q : Finset (Finset (Fin m))}
    (hQ : pullbackPlan g P = some Q) :
    pullbackPlan f Q = pullbackPlan (f.trans g) P := by
  by_cases hg : Finset.univ.image g ∈ P
  · rw [pullbackPlan_eq_some g hg, Option.some.injEq] at hQ
    subst hQ
    have key : ∀ C : Finset (Fin ℓ),
        C.image f ∈ (Finset.univ : Finset (Fin m)).powerset.filter
          (fun D => D.image g ∈ P) ↔ C.image (f.trans g) ∈ P := by
      intro C
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and,
        Finset.image_image]
      rfl
    by_cases hf : Finset.univ.image f ∈ (Finset.univ : Finset (Fin m)).powerset.filter
        (fun D => D.image g ∈ P)
    · rw [pullbackPlan_eq_some f hf, pullbackPlan_eq_some (f.trans g) ((key _).1 hf)]
      congr 1
      ext C
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and,
        Finset.image_image]
      rfl
    · rw [pullbackPlan_eq_none f hf, pullbackPlan_eq_none (f.trans g) (fun h => hf ((key _).2 h))]
  · rw [pullbackPlan_eq_none g hg] at hQ
    simp_all

section CanonicalPlan

variable [LinearOrder α]

/-- A canonical plan on a finite linearly ordered set, by well-founded recursion on the
cardinality: for `|A| ≤ 1` the base plans; for `|A| ≥ 2` the step at the two least elements
of `A`, recursing on the two one-point erasures. -/
noncomputable def canonicalPlan (A : Finset α) : Finset (Finset α) :=
  if _h0 : A.card = 0 then {∅}
  else if _h1 : A.card = 1 then {∅, A}
  else
    have hne : A.Nonempty := Finset.card_pos.mp (by omega)
    have hne' : (A.erase (A.min' hne)).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; intro h
      have := Finset.card_erase_of_mem (Finset.min'_mem A hne)
      grind
    canonicalPlan (A.erase (A.min' hne)) ∪
      canonicalPlan (A.erase ((A.erase (A.min' hne)).min' hne')) ∪ {A}
termination_by A.card
decreasing_by
  · rw [Finset.card_erase_of_mem (Finset.min'_mem A hne)]; omega
  · rw [Finset.card_erase_of_mem
      (Finset.mem_of_mem_erase (Finset.min'_mem (A.erase (A.min' hne)) hne'))]; omega

/-- If the least element of `B` is not `b ∈ B`, it is also the least element of `B ∖ {b}`. -/
private theorem min'_erase_of_ne {B : Finset α} (hne : B.Nonempty) {b : α}
    (hab : B.min' hne ≠ b)
    (hne_eb : (B.erase b).Nonempty) :
    (B.erase b).min' hne_eb = B.min' hne := by
  set a := B.min' hne
  have ha_in_eb : a ∈ B.erase b := Finset.mem_erase.mpr ⟨hab, Finset.min'_mem B hne⟩
  apply le_antisymm
  · exact Finset.min'_le (s := B.erase b) a ha_in_eb
  · apply Finset.le_min'
    intro y hy
    exact Finset.min'_le (s := B) y (Finset.mem_of_mem_erase hy)

/-- `canonicalPlan B` is a plan, and restricting it to the two recursive sub-domains recovers
the sub-plans (both claims are needed together for the induction). -/
private theorem isPlan_and_restrict_aux :
    ∀ n, ∀ (B : Finset α), B.card = n →
    IsPlan B (canonicalPlan B) ∧
    (B.card ≥ 2 →
      ∀ (hne : B.Nonempty) (hne' : (B.erase (B.min' hne)).Nonempty),
        restrictPlan (canonicalPlan B) (B.erase (B.min' hne)) =
          canonicalPlan (B.erase (B.min' hne)) ∧
        restrictPlan (canonicalPlan B)
          (B.erase ((B.erase (B.min' hne)).min' hne')) =
          canonicalPlan (B.erase ((B.erase (B.min' hne)).min' hne'))) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro B hBn
  by_cases h0 : n = 0
  · subst h0; have : B = ∅ := Finset.card_eq_zero.mp hBn; subst this
    exact ⟨by unfold canonicalPlan; solve_by_elim,
           by lia⟩
  by_cases h1 : n = 1
  · subst h1; obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hBn
    exact ⟨by unfold canonicalPlan; solve_by_elim,
           by lia⟩
  have h2 : n ≥ 2 := by omega
  have hne : B.Nonempty := Finset.card_pos.mp (by omega)
  set a := B.min' hne with ha_def
  have ha_mem : a ∈ B := Finset.min'_mem B hne
  have hne' : (B.erase a).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; grind
  set b := (B.erase a).min' hne' with hb_def
  have hb_in_ea : b ∈ B.erase a := Finset.min'_mem (B.erase a) hne'
  have hb_mem : b ∈ B := Finset.mem_of_mem_erase hb_in_ea
  have hab : a ≠ b := by grind
  set C := (B.erase a).erase b
  set Q := canonicalPlan (B.erase a) with hQ_def
  set R := canonicalPlan (B.erase b) with hR_def
  have card_ea : (B.erase a).card = n - 1 := by
    simp_all
  have card_eb : (B.erase b).card = n - 1 := by
    simp_all
  have ih_ea := ih (n - 1) (by omega) (B.erase a) card_ea
  have ih_eb := ih (n - 1) (by omega) (B.erase b) card_eb
  have hQ_plan : IsPlan (B.erase a) Q := ih_ea.1
  have hR_plan : IsPlan (B.erase b) R := ih_eb.1
  have hne_eb : (B.erase b).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; grind
  have ha_min_eb : (B.erase b).min' hne_eb = a :=
    min'_erase_of_ne hne hab hne_eb
  have hC_comm : C = (B.erase b).erase a := Finset.erase_right_comm
  have unfold_cp : canonicalPlan B = Q ∪ R ∪ {B} := by
    change canonicalPlan B = canonicalPlan (B.erase a) ∪ canonicalPlan (B.erase b) ∪ {B}
    have h0' : ¬ B.card = 0 := by omega
    have h1' : ¬ B.card = 1 := by omega
    rw [canonicalPlan, dite_eq_right h0', dite_eq_right h1']
  have card_C : C.card = n - 2 := by
    grind
  have ih_C := ih (n - 2) (by omega) C card_C
  have restrictQ_C : Q ∩ C.powerset = canonicalPlan C := by
    by_cases h_ea2 : (B.erase a).card ≥ 2
    · have hne'_ea : ((B.erase a).erase ((B.erase a).min' hne')).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]; grind
      exact (ih_ea.2 h_ea2 hne' hne'_ea).1
    · have hea1 : (B.erase a).card = 1 := by omega
      obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hea1
      have hby : b = y := by
        grind
      have hQ_val : Q = ({∅, {y}} : Finset (Finset α)) := by
        change canonicalPlan (B.erase a) = _
        conv_lhs => rw [show B.erase a = {y} from hy]; unfold canonicalPlan; simp
      have hcp0 : canonicalPlan (∅ : Finset α) = {∅} := by unfold canonicalPlan; simp
      change Q ∩ ((B.erase a).erase b).powerset = canonicalPlan ((B.erase a).erase b)
      rw [show (B.erase a).erase b = (∅ : Finset α) from by rw [hby, hy, Finset.erase_singleton]]
      rw [Finset.powerset_empty, hQ_val, hcp0]
      solve_by_elim
  have restrictR_C : R ∩ C.powerset = canonicalPlan C := by
    by_cases h_eb2 : (B.erase b).card ≥ 2
    · have hne'_eb : ((B.erase b).erase ((B.erase b).min' hne_eb)).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]; grind
      have hh := (ih_eb.2 h_eb2 hne_eb hne'_eb).1; rw [ha_min_eb] at hh
      rw [show (C : Finset α) = (B.erase b).erase a from hC_comm]; exact hh
    · have heb1 : (B.erase b).card = 1 := by omega
      obtain ⟨y, hy⟩ := Finset.card_eq_one.mp heb1
      have hay : a = y := by
        have ha_in : a ∈ ({y} : Finset α) := by grind
        exact Finset.mem_singleton.mp ha_in
      change R ∩ ((B.erase a).erase b).powerset = canonicalPlan ((B.erase a).erase b)
      rw [show ((B.erase a).erase b : Finset α) = (B.erase b).erase a from hC_comm,
          hay, hy, Finset.erase_singleton, Finset.powerset_empty]
      have : R = ({∅, {y}} : Finset (Finset α)) := by
        change canonicalPlan (B.erase b) = _; rw [hy]; unfold canonicalPlan; simp
      rw [this, show canonicalPlan (∅ : Finset α) = {∅} from by unfold canonicalPlan; simp]
      ext S; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨Or.inl h, h⟩⟩
  have h_restr_eq : Q ∩ C.powerset = R ∩ C.powerset := by
    rw [restrictQ_C, restrictR_C]
  have hC_mem_Q : C ∈ Q := (Finset.mem_inter.mp (restrictQ_C ▸ ih_C.1.domain_mem)).1
  have hC_mem_R : C ∈ R := (Finset.mem_inter.mp (restrictR_C ▸ ih_C.1.domain_mem)).1
  refine ⟨?_, ?_⟩
  · rw [unfold_cp]
    exact IsPlan.step ha_mem hb_mem hab hQ_plan hR_plan ⟨hC_mem_Q, hC_mem_R⟩ h_restr_eq rfl
  · intro _ hne₀ hne₀'
    have mem_C_of_mem_ea_eb : ∀ x, x ∈ B.erase a → x ∈ B.erase b → x ∈ C := by
      grind
    have r_sub_q : ∀ S, S ∈ R → S ⊆ B.erase a → S ∈ Q := by
      intro S hSR hS_ea
      have hS_eb : S ⊆ B.erase b := hR_plan.subset_of_mem hSR
      have hS_C : S ⊆ C := fun x hx => by solve_by_elim
      have : S ∈ R ∩ C.powerset :=
        Finset.mem_inter.mpr ⟨hSR, Finset.mem_powerset.mpr hS_C⟩
      grind
    have q_sub_r : ∀ S, S ∈ Q → S ⊆ B.erase b → S ∈ R := by
      intro S hSQ hS_eb
      have hS_ea : S ⊆ B.erase a := hQ_plan.subset_of_mem hSQ
      have hS_C : S ⊆ C := fun x hx => by solve_by_elim
      have : S ∈ Q ∩ C.powerset :=
        Finset.mem_inter.mpr ⟨hSQ, Finset.mem_powerset.mpr hS_C⟩
      grind
    constructor
    · rw [unfold_cp]; unfold restrictPlan; ext S
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton, Finset.mem_powerset]
      constructor
      · rintro ⟨(hSQ | hSR) | rfl, hS_sub⟩
        · exact hSQ
        · exact r_sub_q S hSR hS_sub
        · exact absurd (hS_sub ha_mem) (Finset.notMem_erase a _)
      · intro hSQ; exact ⟨Or.inl (Or.inl hSQ), hQ_plan.subset_of_mem hSQ⟩
    · rw [unfold_cp]; unfold restrictPlan; ext S
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton, Finset.mem_powerset]
      constructor
      · rintro ⟨(hSQ | hSR) | rfl, hS_sub⟩
        · exact q_sub_r S hSQ hS_sub
        · exact hSR
        · exact absurd (hS_sub hb_mem) (Finset.notMem_erase b _)
      · intro hSR; exact ⟨Or.inl (Or.inr hSR), hR_plan.subset_of_mem hSR⟩

/-- `canonicalPlan A` is a support plan on `A`. -/
theorem isPlan_canonicalPlan (A : Finset α) :
    IsPlan A (canonicalPlan A) :=
  (isPlan_and_restrict_aux A.card A rfl).1

end CanonicalPlan

/-- One-point extension: a plan `P` on `A` and a fresh point `x ∉ A` yield a plan `Q` on
`A ∪ {x}` in which `A` is visible and whose restriction to `A` is `P`. -/
theorem isPlan_extend_one
    {A : Finset α} {P : Finset (Finset α)} {x : α}
    (hx : x ∉ A) (hP : IsPlan A P) :
    ∃ Q : Finset (Finset α),
      IsPlan (A ∪ {x}) Q ∧ A ∈ Q ∧ restrictPlan Q A = P := by
  induction hP with
  | empty =>
    tauto
  | singleton a =>
    have hax : a ≠ x := by grind
    refine ⟨{∅, {x}} ∪ {∅, {a}} ∪ {{a} ∪ {x}}, ?_, ?_, ?_⟩
    · have ha_mem : a ∈ ({a} : Finset α) ∪ {x} :=
        Finset.mem_union_left _ (Finset.mem_singleton_self a)
      have hx_mem : x ∈ ({a} : Finset α) ∪ {x} :=
        Finset.mem_union_right _ (Finset.mem_singleton_self x)
      have h_erase_a : (({a} : Finset α) ∪ {x}).erase a = {x} := by
        simp_all
      have h_erase_x : (({a} : Finset α) ∪ {x}).erase x = {a} := by
        grind
      have h_erase_ax : ((({a} : Finset α) ∪ {x}).erase a).erase x = ∅ := by
        rw [h_erase_a, Finset.erase_singleton]
      have h_inter_mem : ∅ ∈ ({∅, {x}} : Finset (Finset α)) ∧
          ∅ ∈ ({∅, {a}} : Finset (Finset α)) := by simp
      have h_restr : ({∅, {x}} : Finset (Finset α)) ∩ (∅ : Finset α).powerset =
          ({∅, {a}} : Finset (Finset α)) ∩ (∅ : Finset α).powerset := by
        solve_by_elim
      have hQ_s : IsPlan ((({a} : Finset α) ∪ {x}).erase a) {∅, {x}} := by
        rw [h_erase_a]; exact IsPlan.singleton x
      have hR_s : IsPlan ((({a} : Finset α) ∪ {x}).erase x) {∅, {a}} := by
        rw [h_erase_x]; exact IsPlan.singleton a
      have h_inter' :
          ((({a} : Finset α) ∪ {x}).erase a).erase x ∈ ({∅, {x}} : Finset (Finset α)) ∧
          ((({a} : Finset α) ∪ {x}).erase a).erase x ∈ ({∅, {a}} : Finset (Finset α)) := by
        rw [h_erase_ax]; exact h_inter_mem
      have h_restr' : ({∅, {x}} : Finset (Finset α)) ∩
          (((({a} : Finset α) ∪ {x}).erase a).erase x).powerset =
          ({∅, {a}} : Finset (Finset α)) ∩
          (((({a} : Finset α) ∪ {x}).erase a).erase x).powerset := by
        rw [h_erase_ax]; exact h_restr
      exact IsPlan.step ha_mem hx_mem hax hQ_s hR_s h_inter' h_restr' rfl
    · simp
    · unfold restrictPlan; grind
  | @step A' a b Q₀ R₀ P' ha hb hab hQ₀ hR₀ h_inter_mem h_restr_eq hP' ihQ ihR =>
    subst hP'
    have hx_ea : x ∉ A'.erase a := by simp_all
    obtain ⟨Qext, hQext_plan, hQext_mem, hQext_restr⟩ := ihQ hx_ea
    have hax : a ≠ x := by lia
    have h_erase_x : (A' ∪ {x}).erase x = A' := by
      simp_all
    have h_erase_a : (A' ∪ {x}).erase a = (A'.erase a) ∪ {x} := by
      grind
    have h_erase_xa : ((A' ∪ {x}).erase x).erase a = A'.erase a := by
      rw [h_erase_x]
    have hea_in_P : A'.erase a ∈ Q₀ ∪ R₀ ∪ {A'} :=
      Finset.mem_union_left _ (Finset.mem_union_left _ hQ₀.domain_mem)
    have hrestr_P_ea : (Q₀ ∪ R₀ ∪ {A'}) ∩ (A'.erase a).powerset = Q₀ := by
      have := restrictPlan_step_erase ha hQ₀ hR₀ h_restr_eq
      unfold restrictPlan at this; exact this
    have hQext_restr' : Qext ∩ (A'.erase a).powerset = Q₀ := by
      unfold restrictPlan at hQext_restr; exact hQext_restr
    have h_restr_eq' : (Q₀ ∪ R₀ ∪ {A'}) ∩ (A'.erase a).powerset =
        Qext ∩ (A'.erase a).powerset := by
      rw [hrestr_P_ea, hQext_restr']
    set result := (Q₀ ∪ R₀ ∪ {A'}) ∪ Qext ∪ {A' ∪ {x}} with hresult_def
    refine ⟨result, ?_, ?_, ?_⟩
    · have hx_mem : x ∈ A' ∪ {x} := Finset.mem_union_right _ (Finset.mem_singleton_self x)
      have ha_mem : a ∈ A' ∪ {x} := Finset.mem_union_left _ ha
      have hQ_sub : IsPlan ((A' ∪ {x}).erase x) (Q₀ ∪ R₀ ∪ {A'}) := by
        rw [h_erase_x]; exact IsPlan.step ha hb hab hQ₀ hR₀ h_inter_mem h_restr_eq rfl
      have hR_sub : IsPlan ((A' ∪ {x}).erase a) Qext := by
        rw [h_erase_a]; exact hQext_plan
      have h_inter_mem' : ((A' ∪ {x}).erase x).erase a ∈ (Q₀ ∪ R₀ ∪ {A'}) ∧
          ((A' ∪ {x}).erase x).erase a ∈ Qext := by
        simp_all
      have h_restr' : (Q₀ ∪ R₀ ∪ {A'}) ∩ (((A' ∪ {x}).erase x).erase a).powerset =
          Qext ∩ (((A' ∪ {x}).erase x).erase a).powerset := by
        rw [h_erase_xa]; exact h_restr_eq'
      exact IsPlan.step hx_mem ha_mem (fun h => hax h.symm)
        hQ_sub hR_sub h_inter_mem' h_restr' hresult_def
    · simp_all
    · unfold restrictPlan; ext S
      simp only [hresult_def, Finset.mem_inter, Finset.mem_union, Finset.mem_singleton,
                  Finset.mem_powerset]
      constructor
      · rintro ⟨((((hS_Q | hS_R) | rfl) | hS_Qext) | rfl), hS_sub⟩
        · left; left; exact hS_Q
        · left; right; exact hS_R
        · right; rfl
        · have hS_sub_ext : S ⊆ (A'.erase a) ∪ {x} :=
            h_erase_a ▸ hQext_plan.subset_of_mem hS_Qext
          grind
        grind
      · rintro ((hS_Q | hS_R) | rfl)
        · grind
        · exact ⟨by lia,
                 (hR₀.subset_of_mem hS_R).trans (Finset.erase_subset _ _)⟩
        simp

end Plan

end VaughtConjecture.AmalgamationPlan
