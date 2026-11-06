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

/-! # Knight's finite support plans and visible faces

Ported from Knight-VC `KnightVC/Plans.lean` @ f7c7847d (plus `IsPlan.pivot_pair` from
`PaperExactPlanTraceGlue.lean`, `IsPlan.singleton_mem` from `PaperExactSingletonFaces.lean`,
and `IsPlan.step_cases` from `PaperExactBoundaryPreservation.lean`).

A **support plan** on a finite set `A` (Knight, Def. 2.1.1, "amalgamation plan") is a family
`P` of subsets of `A` — the **visible faces** — built by binary amalgamation: the plans on `∅`
and on singletons are the full powersets, and a plan on `A` with `|A| ≥ 2` is `Q ∪ R ∪ {A}`
where `Q`, `R` are plans on the two one-point erasures `A ∖ {a}`, `A ∖ {b}` (`a ≠ b`) that
both see the double erasure `A ∖ {a, b}` and agree below it.  `IsPlan A P` is an inductive
predicate, so most proofs are by induction on a derivation.

The calculus on plans:

* `restrictPlan P B := P ∩ 𝒫 B` (Def. 2.1.5) — restriction to a visible face is again a plan
  (`restrict_isPlan`);
* `gradedPlan P` (Def. 2.1.8, Knight's `P̂`) — the pairs `(B, j)` with `B ∈ P` and grade
  `0 < j ≤ |B|`, which index the cells of a cell scheme over `P`;
* transport along injections: preimage (`isPlan_comap`), image (`isPlan_image`), and the
  `Fin`-indexed partial pullback `pullbackPlan f P : Option _`, defined exactly when the range
  of `f` is a visible face, with the conditional composition law `pullbackPlan_trans`;
* existence: the canonical plan `canonicalPlan A` on a linearly ordered finite set
  (`isPlan_canonicalPlan`, `exists_isPlan`) and one-point extension (`isPlan_extend_one`);
* structure: every plan contains `∅`, every singleton, and its domain; on a domain with at
  least two points the pivots `a, b` of a step are determined by the plan (`pivot_pair`: the
  visible co-arity-one faces are exactly `A ∖ {a}` and `A ∖ {b}`); a plan on three or more
  points is never the full powerset (`isPlan_ne_powerset`).

Plans are the horizontal (finite-support) coordinate of Knight's construction
(`docs/DESIGN.md` §1); the stage types `S^α_A` of the Knight instance carry a plan on `A`,
and `pull` of the `TypeTower` is defined precisely on the visible faces of that plan. -/

@[expose] public noncomputable section

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
  rcases BJ with ⟨B, j⟩
  simp [gradedPlan, MemGraded]

/-! ### Basic structure of a plan -/

/-- Every visible face is a subset of the domain. -/
theorem IsPlan.subset_of_mem {A : Finset α} {P : Finset (Finset α)}
    (hP : IsPlan A P) {S : Finset α} (hS : S ∈ P) : S ⊆ A := by
  induction hP with
  | empty | singleton => simp_all
  | step _ _ _ _ _ _ _ hP ihQ ihR =>
    subst hP
    simp only [Finset.mem_union, Finset.mem_singleton] at hS
    rcases hS with (hS | hS) | rfl
    · exact (ihQ hS).trans (Finset.erase_subset _ _)
    · exact (ihR hS).trans (Finset.erase_subset _ _)
    · exact Finset.Subset.refl _

/-- The domain is a visible face. -/
theorem IsPlan.domain_mem {A : Finset α} {P : Finset (Finset α)}
    (hP : IsPlan A P) : A ∈ P := by
  induction hP <;> simp_all

/-- The empty face is visible. -/
theorem IsPlan.empty_mem {A : Finset α} {P : Finset (Finset α)}
    (hP : IsPlan A P) : ∅ ∈ P := by
  induction hP <;> simp_all

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
  | .empty | .singleton _ => simp at hA
  | .step ha hb hab hQ hR hmem _ rfl =>
    refine ⟨_, _, ha, hb, hab, fun z hz => ⟨fun hzP => ?_, ?_⟩,
      Finset.mem_union_left _ (Finset.mem_union_left _ hmem.1), fun M hM haM hbM => ?_⟩
    · simp only [Finset.mem_union, Finset.mem_singleton] at hzP
      rcases hzP with (hq | hr) | h
      · exact Or.inl (by_contra fun hne => Finset.notMem_erase _ A
          (hQ.subset_of_mem hq (Finset.mem_erase.mpr ⟨Ne.symm hne, ha⟩)))
      · exact Or.inr (by_contra fun hne => Finset.notMem_erase _ A
          (hR.subset_of_mem hr (Finset.mem_erase.mpr ⟨Ne.symm hne, hb⟩)))
      · exact absurd hz (h ▸ Finset.notMem_erase z A)
    · rintro (rfl | rfl)
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hQ.domain_mem)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hR.domain_mem)
    · simp only [Finset.mem_union, Finset.mem_singleton] at hM
      rcases hM with (hq | hr) | rfl
      · exact absurd (hQ.subset_of_mem hq haM) (Finset.notMem_erase _ A)
      · exact absurd (hR.subset_of_mem hr hbM) (Finset.notMem_erase _ A)
      · rfl

/-! ### Restriction -/

private theorem restrictPlan_self {A : Finset α} {P : Finset (Finset α)} (hP : IsPlan A P) :
    restrictPlan P A = P :=
  Finset.inter_eq_left.mpr fun _ hS => Finset.mem_powerset.mpr (hP.subset_of_mem hS)

private theorem restrictPlan_idem {P : Finset (Finset α)} {B C : Finset α} (hBC : B ⊆ C) :
    restrictPlan (restrictPlan P C) B = restrictPlan P B := by
  simp [restrictPlan, Finset.inter_assoc, Finset.inter_eq_right.mpr (Finset.powerset_mono.mpr hBC)]

/-- In a step `P = Q ∪ R ∪ {A}` at pivots `a, b`, restricting to `A ∖ {a}` recovers `Q`. -/
private theorem restrictPlan_step_erase {A : Finset α} {a b : α}
    {Q R : Finset (Finset α)}
    (ha : a ∈ A) (hQ : IsPlan (A.erase a) Q) (hR : IsPlan (A.erase b) R)
    (h_restr_eq : Q ∩ ((A.erase a).erase b).powerset =
                  R ∩ ((A.erase a).erase b).powerset) :
    restrictPlan (Q ∪ R ∪ {A}) (A.erase a) = Q := by
  ext S
  simp only [restrictPlan, Finset.mem_inter, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_powerset]
  refine ⟨?_, fun h => ⟨Or.inl (Or.inl h), hQ.subset_of_mem h⟩⟩
  rintro ⟨(hSQ | hSR) | rfl, hS_sub⟩
  · exact hSQ
  · have : S ∈ R ∩ ((A.erase a).erase b).powerset :=
      Finset.mem_inter.mpr ⟨hSR, Finset.mem_powerset.mpr
        (Finset.subset_erase.mpr ⟨hS_sub, fun hbS =>
          Finset.notMem_erase b A (hR.subset_of_mem hSR hbS)⟩)⟩
    exact (Finset.mem_inter.mp (h_restr_eq ▸ this)).1
  · exact absurd (hS_sub ha) (Finset.notMem_erase a _)

private theorem restrictPlan_step_erase_right {A : Finset α} {a b : α}
    {Q R : Finset (Finset α)}
    (hb : b ∈ A) (hQ : IsPlan (A.erase a) Q) (hR : IsPlan (A.erase b) R)
    (h_restr_eq : Q ∩ ((A.erase a).erase b).powerset =
                  R ∩ ((A.erase a).erase b).powerset) :
    restrictPlan (Q ∪ R ∪ {A}) (A.erase b) = R := by
  rw [Finset.union_comm Q R]
  rw [Finset.erase_right_comm] at h_restr_eq
  exact restrictPlan_step_erase hb hR hQ h_restr_eq.symm

/-- Restriction of a plan to a visible face is again a plan (Def. 2.1.5). -/
theorem restrict_isPlan {A B : Finset α} {P : Finset (Finset α)}
    (hP : IsPlan A P) (hB : B ∈ P) :
    IsPlan B (restrictPlan P B) := by
  induction hP with
  | empty =>
    cases Finset.mem_singleton.mp hB
    rw [restrictPlan_self IsPlan.empty]; exact IsPlan.empty
  | singleton a =>
    rcases Finset.mem_insert.mp hB with rfl | hB
    · have : restrictPlan {∅, {a}} ∅ = {∅} := by ext; simp [restrictPlan]
      exact this ▸ IsPlan.empty
    · cases Finset.mem_singleton.mp hB
      rw [restrictPlan_self (IsPlan.singleton a)]; exact IsPlan.singleton a
  | @step A a b Q R P' ha hb hab hQ hR h_inter_mem h_restr_eq hP' ihQ ihR =>
    subst hP'
    simp only [Finset.mem_union, Finset.mem_singleton] at hB
    rcases hB with (hBQ | hBR) | rfl
    · rw [← restrictPlan_idem (hQ.subset_of_mem hBQ),
          restrictPlan_step_erase ha hQ hR h_restr_eq]
      exact ihQ hBQ
    · rw [← restrictPlan_idem (hR.subset_of_mem hBR),
          restrictPlan_step_erase_right hb hQ hR h_restr_eq]
      exact ihR hBR
    · have hstep := IsPlan.step ha hb hab hQ hR h_inter_mem h_restr_eq rfl
      rw [restrictPlan_self hstep]; exact hstep

/-! ### Transport along injections -/

/-- Preimage transport: if `Q` is a plan on `B = f[A]` for an injection `f`, then
`{C ⊆ A | f[C] ∈ Q}` is a plan on `A`. -/
theorem isPlan_comap {β : Type*} [DecidableEq β]
    {B : Finset β} {Q : Finset (Finset β)}
    (hQ : IsPlan B Q) (f : α ↪ β) {A : Finset α} (hAB : A.image f = B) :
    IsPlan A (A.powerset.filter (fun C => C.image f ∈ Q)) := by
  induction hQ generalizing A with
  | empty =>
    rw [Finset.image_eq_empty] at hAB; subst hAB
    simp only [Finset.powerset_empty, Finset.filter_singleton, Finset.image_empty,
      Finset.mem_singleton, ite_true]
    exact IsPlan.empty
  | singleton b =>
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp (by
      rw [← Finset.card_image_of_injective A f.injective, hAB, Finset.card_singleton])
    cases Finset.singleton_injective (by simpa using hAB : {f a} = {b})
    have : ({a} : Finset α).powerset.filter
        (fun C => C.image f ∈ ({∅, {f a}} : Finset (Finset β))) = {∅, {a}} := by
      ext C
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert, Finset.mem_singleton,
        Finset.subset_singleton_iff]
      rcases eq_or_ne C ∅ with rfl | hne <;> simp_all
    exact this ▸ IsPlan.singleton a
  | @step B' a b Qa Qb _ ha hb hab hQa hQb h_inter_mem h_restr_eq hP ihQa ihQb =>
    subst hP
    rw [← hAB] at ha hb
    obtain ⟨a', ha'_mem, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b', hb'_mem, rfl⟩ := Finset.mem_image.mp hb
    have hab' : a' ≠ b' := fun h => hab (congrArg f h)
    have img_erase_a : (A.erase a').image f = B'.erase (f a') := by
      rw [Finset.image_erase f.injective, hAB]
    have img_erase_b : (A.erase b').image f = B'.erase (f b') := by
      rw [Finset.image_erase f.injective, hAB]
    have img_erase_ab : ((A.erase a').erase b').image f = (B'.erase (f a')).erase (f b') := by
      rw [Finset.image_erase f.injective, img_erase_a]
    have erase_ab_mem_a : (A.erase a').erase b' ∈
        (A.erase a').powerset.filter (fun C => C.image f ∈ Qa) :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.erase_subset _ _),
        img_erase_ab ▸ h_inter_mem.1⟩
    have erase_ab_mem_b : (A.erase a').erase b' ∈
        (A.erase b').powerset.filter (fun C => C.image f ∈ Qb) := by
      rw [Finset.erase_right_comm, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.erase_subset _ _, ?_⟩
      rw [Finset.image_erase f.injective, img_erase_b, Finset.erase_right_comm]
      exact h_inter_mem.2
    have restr_eq :
        (A.erase a').powerset.filter (fun C => C.image f ∈ Qa) ∩
          ((A.erase a').erase b').powerset =
        (A.erase b').powerset.filter (fun C => C.image f ∈ Qb) ∩
          ((A.erase a').erase b').powerset := by
      ext C
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_powerset]
      have hsub (hCab : C ⊆ (A.erase a').erase b') :
          C.image f ∈ ((B'.erase (f a')).erase (f b')).powerset :=
        Finset.mem_powerset.mpr (img_erase_ab ▸ Finset.image_subset_image hCab)
      have hmem (hCab : C ⊆ (A.erase a').erase b') :
          C.image f ∈ Qa ↔ C.image f ∈ Qb := by
        have := Finset.ext_iff.mp h_restr_eq (C.image f)
        simpa [hsub hCab] using this
      refine ⟨fun ⟨⟨_, h1⟩, h2⟩ => ⟨⟨?_, (hmem h2).mp h1⟩, h2⟩,
              fun ⟨⟨_, h1⟩, h2⟩ => ⟨⟨h2.trans (Finset.erase_subset _ _), (hmem h2).mpr h1⟩, h2⟩⟩
      rw [Finset.erase_right_comm] at h2
      exact h2.trans (Finset.erase_subset _ _)
    have union_eq :
        A.powerset.filter (fun C => C.image f ∈ Qa ∪ Qb ∪ {B'}) =
        (A.erase a').powerset.filter (fun C => C.image f ∈ Qa) ∪
        (A.erase b').powerset.filter (fun C => C.image f ∈ Qb) ∪
        {A} := by
      ext C
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_union, Finset.mem_singleton]
      constructor
      · rintro ⟨_, (hCQa | hCQb) | hCB'⟩
        · exact Or.inl (Or.inl ⟨(Finset.image_subset_image_iff f.injective).mp
            (img_erase_a ▸ hQa.subset_of_mem hCQa), hCQa⟩)
        · exact Or.inl (Or.inr ⟨(Finset.image_subset_image_iff f.injective).mp
            (img_erase_b ▸ hQb.subset_of_mem hCQb), hCQb⟩)
        · exact Or.inr ((Finset.image_injective f.injective).eq_iff.mp (hAB ▸ hCB'))
      · rintro ((⟨hCa, hCQa⟩ | ⟨hCb, hCQb⟩) | rfl)
        · exact ⟨hCa.trans (Finset.erase_subset _ _), Or.inl (Or.inl hCQa)⟩
        · exact ⟨hCb.trans (Finset.erase_subset _ _), Or.inl (Or.inr hCQb)⟩
        · exact ⟨Finset.Subset.refl _, Or.inr hAB⟩
    rw [union_eq]
    exact IsPlan.step ha'_mem hb'_mem hab' (ihQa img_erase_a) (ihQb img_erase_b)
      ⟨erase_ab_mem_a, erase_ab_mem_b⟩ restr_eq rfl

/-- Image transport: the image of a plan on `A` under an injection `f` is a plan on `f[A]`. -/
theorem isPlan_image {β : Type*} [DecidableEq β]
    {A : Finset α} {P : Finset (Finset α)} (f : α ↪ β)
    (hP : IsPlan A P) :
    IsPlan (A.image f) (P.image (Finset.image f)) := by
  induction hP with
  | empty =>
    simpa using IsPlan.empty
  | singleton a =>
    simpa using IsPlan.singleton (f a)
  | @step A a b Q R P' ha hb hab hQ hR h_inter_mem h_restr_eq hP' ihQ ihR =>
    subst hP'
    have img_erase_a : (A.erase a).image f = (A.image f).erase (f a) :=
      Finset.image_erase f.injective A a
    have img_erase_b : (A.erase b).image f = (A.image f).erase (f b) :=
      Finset.image_erase f.injective A b
    have img_erase_ab : ((A.erase a).erase b).image f =
        ((A.image f).erase (f a)).erase (f b) := by
      rw [Finset.image_erase f.injective, img_erase_a]
    have h_restr_eq' :
        Q.image (Finset.image f) ∩ (((A.image f).erase (f a)).erase (f b)).powerset =
        R.image (Finset.image f) ∩ (((A.image f).erase (f a)).erase (f b)).powerset := by
      rw [← img_erase_ab]
      ext S
      simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_powerset]
      refine ⟨?_, ?_⟩ <;> rintro ⟨⟨T, hT, rfl⟩, hS_sub⟩
      · have hT_inter : T ∈ Q ∩ ((A.erase a).erase b).powerset :=
          Finset.mem_inter.mpr ⟨hT, Finset.mem_powerset.mpr
            ((Finset.image_subset_image_iff f.injective).mp hS_sub)⟩
        exact ⟨⟨T, (Finset.mem_inter.mp (h_restr_eq ▸ hT_inter)).1, rfl⟩, hS_sub⟩
      · have hT_inter : T ∈ R ∩ ((A.erase a).erase b).powerset :=
          Finset.mem_inter.mpr ⟨hT, Finset.mem_powerset.mpr
            ((Finset.image_subset_image_iff f.injective).mp hS_sub)⟩
        exact ⟨⟨T, (Finset.mem_inter.mp (h_restr_eq ▸ hT_inter)).1, rfl⟩, hS_sub⟩
    rw [img_erase_a] at ihQ
    rw [img_erase_b] at ihR
    simp only [Finset.image_union, Finset.image_singleton]
    exact IsPlan.step (Finset.mem_image_of_mem f ha) (Finset.mem_image_of_mem f hb)
      (fun h => hab (f.injective h)) ihQ ihR
      ⟨img_erase_ab ▸ Finset.mem_image_of_mem _ h_inter_mem.1,
       img_erase_ab ▸ Finset.mem_image_of_mem _ h_inter_mem.2⟩
      h_restr_eq' rfl

/-! ### `Fin`-indexed pullback -/

/-- Pullback of a plan on `Fin n` along `f : Fin m ↪ Fin n` whose range is a visible face:
`{C ⊆ Fin m | f[C] ∈ P}` is a plan on `Fin m`. -/
theorem pullback_isPlan_fin {n m : ℕ} (f : Fin m ↪ Fin n)
    {P : Finset (Finset (Fin n))} (hP : IsPlan Finset.univ P)
    (hr : Finset.univ.image f ∈ P) :
    IsPlan (Finset.univ : Finset (Fin m))
      ((Finset.univ : Finset (Fin m)).powerset.filter
        (fun C => (C.image f) ∈ P)) := by
  have heq : (Finset.univ : Finset (Fin m)).powerset.filter (fun C => C.image f ∈ P) =
      (Finset.univ : Finset (Fin m)).powerset.filter
        (fun C => C.image f ∈ restrictPlan P (Finset.univ.image f)) := by
    ext C
    simp [restrictPlan, Finset.image_subset_image (Finset.subset_univ C)]
  rw [heq]
  exact isPlan_comap (restrict_isPlan hP hr) f rfl

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

/-- Pullback along the identity is the identity on plans on `Fin n`. -/
theorem pullbackPlan_refl {n : ℕ} {P : Finset (Finset (Fin n))} (hP : IsPlan Finset.univ P) :
    pullbackPlan (Function.Embedding.refl (Fin n)) P = some P := by
  have hr : Finset.univ.image (Function.Embedding.refl (Fin n)) ∈ P := by
    simpa [Function.Embedding.coe_refl] using hP.domain_mem
  rw [pullbackPlan_eq_some _ hr]
  congr 1; ext C; simp [Function.Embedding.coe_refl]

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
    simp only [pullbackPlan, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and,
      Finset.image_image]
    rfl
  · simp [pullbackPlan, hg] at hQ

/-! ### The canonical plan -/

section CanonicalPlan

variable [LinearOrder α]

/-- A canonical plan on a finite linearly ordered set, by well-founded recursion on the
cardinality: for `|A| ≤ 1` the base plans; for `|A| ≥ 2` the step at the two least elements
of `A`, recursing on the two one-point erasures. -/
def canonicalPlan (A : Finset α) : Finset (Finset α) :=
  if _h0 : A.card = 0 then {∅}
  else if _h1 : A.card = 1 then {∅, A}
  else
    have hne : A.Nonempty := Finset.card_pos.mp (by omega)
    have hne' : (A.erase (A.min' hne)).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; intro h
      have := Finset.card_erase_of_mem (Finset.min'_mem A hne)
      rw [h, Finset.card_empty] at this; omega
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
    (B.erase b).min' hne_eb = B.min' hne :=
  le_antisymm (Finset.min'_le _ _ (Finset.mem_erase.mpr ⟨hab, Finset.min'_mem B hne⟩))
    (Finset.le_min' _ _ _ fun _ hy => Finset.min'_le _ _ (Finset.mem_of_mem_erase hy))

/-- `canonicalPlan B` is a plan, and restricting it to the least-element erasure recovers
the sub-plan (both claims are needed together for the induction). -/
private theorem isPlan_and_restrict_aux (n : ℕ) :
    ∀ B : Finset α, B.card = n →
    IsPlan B (canonicalPlan B) ∧
    ∀ hne : B.Nonempty,
      restrictPlan (canonicalPlan B) (B.erase (B.min' hne)) =
        canonicalPlan (B.erase (B.min' hne)) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro B hBn
  by_cases h0 : n = 0
  · subst h0; cases Finset.card_eq_zero.mp hBn
    exact ⟨by unfold canonicalPlan; simp [IsPlan.empty], fun hne => by simp at hne⟩
  by_cases h1 : n = 1
  · subst h1; obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hBn
    refine ⟨by unfold canonicalPlan; simp [IsPlan.singleton x], fun hne => ?_⟩
    rw [Finset.min'_singleton, Finset.erase_singleton,
      show canonicalPlan ({x} : Finset α) = {∅, {x}} by unfold canonicalPlan; simp,
      show canonicalPlan (∅ : Finset α) = {∅} by unfold canonicalPlan; simp]
    ext; simp [restrictPlan]
  have hne : B.Nonempty := Finset.card_pos.mp (by omega)
  set a := B.min' hne
  have ha_mem : a ∈ B := Finset.min'_mem B hne
  have card_ea : (B.erase a).card = n - 1 := by rw [Finset.card_erase_of_mem ha_mem, hBn]
  have hne' : (B.erase a).Nonempty := Finset.card_pos.mp (by omega)
  set b := (B.erase a).min' hne'
  have hb_in_ea : b ∈ B.erase a := Finset.min'_mem (B.erase a) hne'
  have hb_mem : b ∈ B := Finset.mem_of_mem_erase hb_in_ea
  have hab : a ≠ b := (Finset.mem_erase.mp hb_in_ea).1.symm
  have card_eb : (B.erase b).card = n - 1 := by rw [Finset.card_erase_of_mem hb_mem, hBn]
  have hne_eb : (B.erase b).Nonempty := Finset.card_pos.mp (by omega)
  have ha_min_eb : (B.erase b).min' hne_eb = a := min'_erase_of_ne hne hab hne_eb
  have ih_ea := ih (n - 1) (by omega) (B.erase a) card_ea
  have ih_eb := ih (n - 1) (by omega) (B.erase b) card_eb
  set C := (B.erase a).erase b
  have card_C : C.card = n - 2 := by
    rw [Finset.card_erase_of_mem hb_in_ea, card_ea]; omega
  have ih_C := ih (n - 2) (by omega) C card_C
  have restrictQ_C : canonicalPlan (B.erase a) ∩ C.powerset = canonicalPlan C := ih_ea.2 hne'
  have restrictR_C : canonicalPlan (B.erase b) ∩ C.powerset = canonicalPlan C := by
    simpa [restrictPlan, C, Finset.erase_right_comm, ha_min_eb] using ih_eb.2 hne_eb
  have h_restr_eq : canonicalPlan (B.erase a) ∩ C.powerset =
      canonicalPlan (B.erase b) ∩ C.powerset := restrictQ_C.trans restrictR_C.symm
  have unfold_cp : canonicalPlan B =
      canonicalPlan (B.erase a) ∪ canonicalPlan (B.erase b) ∪ {B} := by
    rw [canonicalPlan, dite_eq_right (by omega), dite_eq_right (by omega)]
  refine ⟨unfold_cp ▸ IsPlan.step ha_mem hb_mem hab ih_ea.1 ih_eb.1
    ⟨(Finset.mem_inter.mp (restrictQ_C ▸ ih_C.1.domain_mem)).1,
     (Finset.mem_inter.mp (restrictR_C ▸ ih_C.1.domain_mem)).1⟩ h_restr_eq rfl,
    fun _ => unfold_cp ▸ restrictPlan_step_erase ha_mem ih_ea.1 ih_eb.1 h_restr_eq⟩

/-- `canonicalPlan A` is a support plan on `A`. -/
theorem isPlan_canonicalPlan (A : Finset α) :
    IsPlan A (canonicalPlan A) :=
  (isPlan_and_restrict_aux A.card A rfl).1

end CanonicalPlan

/-! ### One-point extension -/

/-- One-point extension: a plan `P` on `A` and a fresh point `x ∉ A` yield a plan `Q` on
`A ∪ {x}` in which `A` is visible and whose restriction to `A` is `P`. -/
theorem isPlan_extend_one
    {A : Finset α} {P : Finset (Finset α)} {x : α}
    (hx : x ∉ A) (hP : IsPlan A P) :
    ∃ Q : Finset (Finset α),
      IsPlan (A ∪ {x}) Q ∧ A ∈ Q ∧ restrictPlan Q A = P := by
  have ext_step {B P Qext} (hxB : x ∉ B) (hBP : IsPlan B P) {a} (ha : a ∈ B)
      (hea : B.erase a ∈ P) (hQext : IsPlan (B.erase a ∪ {x}) Qext)
      (hmem : B.erase a ∈ Qext) (hrestr : restrictPlan Qext (B.erase a) = restrictPlan P (B.erase a)) :
      ∃ Q, IsPlan (B ∪ {x}) Q ∧ B ∈ Q ∧ restrictPlan Q B = P := by
    have hax : a ≠ x := fun h => hxB (h ▸ ha)
    have hx_mem : x ∈ B ∪ {x} := Finset.mem_union_right _ (Finset.mem_singleton_self x)
    have h_erase_x : (B ∪ {x}).erase x = B := by
      rw [Finset.union_singleton, Finset.erase_insert hxB]
    have h_erase_a : (B ∪ {x}).erase a = B.erase a ∪ {x} := by
      rw [Finset.union_singleton, Finset.erase_insert_of_ne hax.symm, Finset.union_singleton]
    have hQ_sub : IsPlan ((B ∪ {x}).erase x) P := h_erase_x.symm ▸ hBP
    have hR_sub : IsPlan ((B ∪ {x}).erase a) Qext := h_erase_a.symm ▸ hQext
    have h_restr' : P ∩ (((B ∪ {x}).erase x).erase a).powerset =
        Qext ∩ (((B ∪ {x}).erase x).erase a).powerset := by
      rw [h_erase_x]; exact hrestr.symm
    refine ⟨P ∪ Qext ∪ {B ∪ {x}},
      IsPlan.step hx_mem (Finset.mem_union_left _ ha) hax.symm hQ_sub hR_sub
        ⟨by rwa [h_erase_x], by rwa [h_erase_x]⟩ h_restr' rfl,
      Finset.mem_union_left _ (Finset.mem_union_left _ hBP.domain_mem),
      by have := restrictPlan_step_erase hx_mem hQ_sub hR_sub h_restr'; rwa [h_erase_x] at this⟩
  have h0 : ∃ Q, IsPlan (∅ ∪ {x}) Q ∧ ∅ ∈ Q ∧ restrictPlan Q ∅ = {∅} :=
    ⟨{∅, {x}}, by rw [Finset.empty_union]; exact IsPlan.singleton x, by simp, by ext; simp [restrictPlan]⟩
  induction hP with
  | empty => exact h0
  | singleton a =>
    obtain ⟨Qext, h1, h2, h3⟩ := h0
    rw [← Finset.erase_singleton a] at h1 h2 h3
    refine ext_step hx (IsPlan.singleton a) (Finset.mem_singleton_self a) (by simp) h1 h2 ?_
    rw [h3, Finset.erase_singleton]; ext; simp [restrictPlan]
  | step ha hb hab hQ₀ hR₀ h_inter_mem h_restr_eq hP' ihQ _ =>
    subst hP'
    obtain ⟨Qext, h1, h2, h3⟩ := ihQ (fun h => hx (Finset.mem_of_mem_erase h))
    exact ext_step hx (IsPlan.step ha hb hab hQ₀ hR₀ h_inter_mem h_restr_eq rfl) ha
      (Finset.mem_union_left _ (Finset.mem_union_left _ hQ₀.domain_mem)) h1 h2
      (h3.trans (restrictPlan_step_erase ha hQ₀ hR₀ h_restr_eq).symm)
