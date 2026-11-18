/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FiniteProfileControllers
public import VaughtConjecture.Knight.SourceBlockPadding
public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.Finset.Sort

@[expose] public section

namespace VaughtConjecture.Knight.AmalgamatedBoundaryPlan

open AmalgamationPlan

variable {ι : Type*} [DecidableEq ι]

structure Step (A : Finset ι) where
  a : ι
  b : ι
  ha : a ∈ A
  hb : b ∈ A
  different : a ≠ b
  left : Finset (Finset ι)
  right : Finset (Finset ι)
  left_plan : Plan.IsPlan (A.erase a) left
  right_plan : Plan.IsPlan (A.erase b) right
  common_left : (A.erase a).erase b ∈ left
  common_right : (A.erase a).erase b ∈ right
  common : Plan.restrictPlan left ((A.erase a).erase b) =
    Plan.restrictPlan right ((A.erase a).erase b)

variable {A : Finset ι} (s : Step A)

def Step.plan : Finset (Finset ι) := s.left ∪ s.right ∪ {A}

theorem isPlan : Plan.IsPlan A s.plan :=
  Plan.IsPlan.step s.ha s.hb s.different s.left_plan s.right_plan
    ⟨s.common_left, s.common_right⟩ s.common rfl

private theorem restrict_union {A B C : Finset ι} {Q R : Finset (Finset ι)}
    (hQ : Plan.IsPlan B Q) (hR : Plan.IsPlan C R) (hne : ¬ A ⊆ B)
    (hcommon : Plan.restrictPlan Q (B ∩ C) = Plan.restrictPlan R (B ∩ C)) :
    Plan.restrictPlan (Q ∪ R ∪ {A}) B = Q := by
  ext S
  simp only [Plan.restrictPlan, Finset.mem_inter, Finset.mem_union,
    Finset.mem_singleton, Finset.mem_powerset]
  constructor
  · rintro ⟨(hS | hS) | rfl, hSB⟩
    · exact hS
    · have hc : S ∈ Plan.restrictPlan R (B ∩ C) :=
        Finset.mem_inter.mpr ⟨hS, Finset.mem_powerset.mpr
          (Finset.subset_inter hSB (hR.subset_of_mem hS))⟩
      rw [← hcommon] at hc
      exact (Finset.mem_inter.mp hc).1
    · exact False.elim (hne hSB)
  · intro hS
    exact ⟨Or.inl (Or.inl hS), hQ.subset_of_mem hS⟩

theorem erased_inter : A.erase s.a ∩ A.erase s.b = (A.erase s.a).erase s.b := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_erase]
  tauto

theorem restrict_left : Plan.restrictPlan s.plan (A.erase s.a) = s.left := by
  apply restrict_union s.left_plan s.right_plan
  · intro h
    exact Finset.notMem_erase s.a A (h s.ha)
  · rw [erased_inter]
    exact s.common

theorem restrict_right : Plan.restrictPlan s.plan (A.erase s.b) = s.right := by
  have h := restrict_union s.right_plan s.left_plan (A := A) (by
    intro h
    exact Finset.notMem_erase s.b A (h s.hb))
  have hc : Plan.restrictPlan s.right (A.erase s.b ∩ A.erase s.a) =
      Plan.restrictPlan s.left (A.erase s.b ∩ A.erase s.a) := by
    rw [Finset.inter_comm, erased_inter]
    exact s.common.symm
  simpa only [Step.plan, Finset.union_comm s.right s.left] using h hc

theorem proper_index_cover {BJ : Finset ι × ℕ}
    (hBJ : BJ ∈ Plan.gradedPlan s.plan) (hB : BJ.1 ≠ A) :
    BJ ∈ Plan.gradedPlan s.left ∨ BJ ∈ Plan.gradedPlan s.right := by
  obtain ⟨hmem, hpos, hcard⟩ := Plan.mem_gradedPlan.mp hBJ
  rcases Finset.mem_union.mp hmem with hmem | hmem
  · rcases Finset.mem_union.mp hmem with hmem | hmem
    · exact Or.inl (Plan.mem_gradedPlan.mpr ⟨hmem, hpos, hcard⟩)
    · exact Or.inr (Plan.mem_gradedPlan.mpr ⟨hmem, hpos, hcard⟩)
  · exact False.elim (hB (Finset.mem_singleton.mp hmem))

/-- A proper target and every graded source below it lie in the same old face. -/
theorem proper_pair_cover {CI BJ : Finset ι × ℕ}
    (hCI : CI ∈ Plan.gradedPlan s.plan) (hBJ : BJ ∈ Plan.gradedPlan s.plan)
    (h : GradedLe CI BJ) (hB : BJ.1 ≠ A) :
    (CI ∈ Plan.gradedPlan s.left ∧ BJ ∈ Plan.gradedPlan s.left) ∨
      (CI ∈ Plan.gradedPlan s.right ∧ BJ ∈ Plan.gradedPlan s.right) := by
  have hC := Plan.mem_gradedPlan.mp hCI
  rcases proper_index_cover s hBJ hB with hl | hr
  · refine Or.inl ⟨Plan.mem_gradedPlan.mpr ⟨?_, hC.2⟩, hl⟩
    have hc : CI.1 ∈ Plan.restrictPlan s.plan (A.erase s.a) :=
      Finset.mem_inter.mpr ⟨hC.1, Finset.mem_powerset.mpr
        (h.1.trans (s.left_plan.subset_of_mem (Plan.mem_gradedPlan.mp hl).1))⟩
    rwa [restrict_left] at hc
  · refine Or.inr ⟨Plan.mem_gradedPlan.mpr ⟨?_, hC.2⟩, hr⟩
    have hc : CI.1 ∈ Plan.restrictPlan s.plan (A.erase s.b) :=
      Finset.mem_inter.mpr ⟨hC.1, Finset.mem_powerset.mpr
        (h.1.trans (s.right_plan.subset_of_mem (Plan.mem_gradedPlan.mp hr).1))⟩
    rwa [restrict_right] at hc

/-- The uniform step data are available for every nontrivial support plan. -/
theorem exists_step {P : Finset (Finset ι)} (hP : Plan.IsPlan A P) (hA : 2 ≤ A.card) :
    ∃ s : Step A, s.plan = P := by
  cases hP with
  | empty => simp at hA
  | singleton x => simp at hA
  | step ha hb hab hQ hR hmem heq hP =>
    exact ⟨⟨_, _, ha, hb, hab, _, _, hQ, hR, hmem.1, hmem.2, heq⟩, hP.symm⟩

end VaughtConjecture.Knight.AmalgamatedBoundaryPlan

namespace VaughtConjecture.Knight.ProfileFaceUnion

variable {C X Y : Type*} (f : C ↪ X) (g : C ↪ Y)

abbrev Carrier := X ⊕ {y : Y // y ∉ Set.range g}

def left (x : X) : Carrier (X := X) g := .inl x

open Classical in
noncomputable def right (y : Y) : Carrier (X := X) g :=
  if h : y ∈ Set.range g then .inl (f h.choose) else .inr ⟨y, h⟩

theorem right_shared (c : C) : right f g (g c) = left g (f c) := by
  classical
  have h : g c ∈ Set.range g := ⟨c, rfl⟩
  rw [right, dite_eq_left h]
  exact congrArg (fun d => Sum.inl (f d)) (g.injective h.choose_spec)

theorem right_private (y : {y : Y // y ∉ Set.range g}) :
    right f g y = .inr y := by
  classical
  simp only [right, dite_eq_right y.property]

theorem overlap (x : X) (y : Y) :
    left g x = right f g y ↔ ∃ c, f c = x ∧ g c = y := by
  classical
  constructor
  · intro h
    by_cases hy : y ∈ Set.range g
    · obtain ⟨c, rfl⟩ := hy
      rw [right_shared] at h
      exact ⟨c, (Sum.inl.inj h).symm, rfl⟩
    · rw [right, dite_eq_right hy] at h
      cases h
  · rintro ⟨c, rfl, rfl⟩
    exact (right_shared f g c).symm

theorem covered (z : Carrier (X := X) g) :
    (∃ x, left g x = z) ∨ ∃ y, right f g y = z := by
  cases z with
  | inl x => exact Or.inl ⟨x, rfl⟩
  | inr y => exact Or.inr ⟨y, right_private f g y⟩

def paste {V : Type*} (p : X → V) (q : Y → V) : Carrier (X := X) g → V
  | .inl x => p x
  | .inr y => q y

theorem paste_right {V : Type*} {p : X → V} {q : Y → V}
    (h : ∀ c, p (f c) = q (g c)) (y : Y) : paste g p q (right f g y) = q y := by
  classical
  by_cases hy : y ∈ Set.range g
  · obtain ⟨c, rfl⟩ := hy
    rw [right_shared]
    exact h c
  · rw [right, dite_eq_right hy]
    rfl

end VaughtConjecture.Knight.ProfileFaceUnion

namespace VaughtConjecture.Knight.ProfileFaceGluing

open ProfileFaceUnion

noncomputable instance {C X Y : Type*} (g : C ↪ Y) [Fintype X] [Fintype Y] :
    Fintype (Carrier (X := X) g) := by
  classical
  unfold Carrier
  infer_instance

end VaughtConjecture.Knight.ProfileFaceGluing

namespace VaughtConjecture.Knight.ProfileBoundaryOrder

open ProfileFaceUnion

variable {c n m : ℕ}

def rank (f : Fin c ↪ Fin n) (x : Fin n) : ℕ :=
  (Finset.univ.filter (fun i => f i ≤ x)).card

theorem rank_mono (f : Fin c ↪ Fin n) : Monotone (rank f) := by
  intro x y hxy
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (Finset.mem_filter.mp hi).2.trans hxy⟩

theorem rank_lt_at_shared (f : Fin c ↪ Fin n) {x y : Fin n}
    (hxy : x < y) (hy : y ∈ Set.range f) : rank f x < rank f y := by
  obtain ⟨i, rfl⟩ := hy
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp hj).2.trans hxy.le⟩
  · intro he
    have hi : i ∈ Finset.univ.filter (fun j => f j ≤ f i) := by simp
    rw [← he] at hi
    exact (not_le_of_gt hxy) (Finset.mem_filter.mp hi).2

theorem rank_shared (f : Fin c ↪ Fin n) (g : Fin c ↪ Fin m)
    (hf : StrictMono f) (hg : StrictMono g) (i : Fin c) :
    rank f (f i) = rank g (g i) := by
  unfold rank
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hf.le_iff_le, hg.le_iff_le]

noncomputable def faceKey (f : Fin c ↪ Fin n) (tag : ℕ) (x : Fin n) : ℕ ×ₗ ℕ := by
  classical
  exact toLex (rank f x, if x ∈ Set.range f then 0 else tag + x.val)

theorem faceKey_strict (f : Fin c ↪ Fin n) {tag : ℕ} (htag : 0 < tag) :
    StrictMono (faceKey f tag) := by
  classical
  intro x y hxy
  change toLex (_, _) < toLex (_, _)
  rw [Prod.Lex.toLex_lt_toLex]
  by_cases hr : rank f x < rank f y
  · exact Or.inl hr
  · have he : rank f x = rank f y := le_antisymm (rank_mono f hxy.le) (le_of_not_gt hr)
    refine Or.inr ⟨he, ?_⟩
    have hy : y ∉ Set.range f := fun hy => hr (rank_lt_at_shared f hxy hy)
    rw [ite_eq_right hy]
    by_cases hx : x ∈ Set.range f
    · rw [ite_eq_left hx]
      omega
    · rw [ite_eq_right hx]
      exact Nat.add_lt_add_left hxy tag

theorem faceKey_shared (f : Fin c ↪ Fin n) (g : Fin c ↪ Fin m)
    (hf : StrictMono f) (hg : StrictMono g) (i : Fin c) :
    faceKey f 1 (f i) = faceKey g (n + 1) (g i) := by
  classical
  simp only [faceKey, Set.mem_range_self, ite_true, rank_shared f g hf hg i]

theorem faceKey_overlap (f : Fin c ↪ Fin n) (g : Fin c ↪ Fin m)
    (hf : StrictMono f) (hg : StrictMono g) (x : Fin n) (y : Fin m) :
    faceKey f 1 x = faceKey g (n + 1) y ↔ ∃ i, f i = x ∧ g i = y := by
  classical
  constructor
  · intro h
    have ho := congrArg (fun k : ℕ ×ₗ ℕ => (ofLex k).2) h
    change (if x ∈ Set.range f then 0 else 1 + x.val) =
      (if y ∈ Set.range g then 0 else n + 1 + y.val) at ho
    by_cases hx : x ∈ Set.range f
    · obtain ⟨i, rfl⟩ := hx
      have he := (faceKey_shared f g hf hg i).symm.trans h
      exact ⟨i, rfl, (faceKey_strict g (by omega : 0 < n + 1)).injective he⟩
    · rw [ite_eq_right hx] at ho
      by_cases hy : y ∈ Set.range g
      · rw [ite_eq_left hy] at ho
        omega
      · rw [ite_eq_right hy] at ho
        have := x.isLt
        omega
  · rintro ⟨i, rfl, rfl⟩
    exact faceKey_shared f g hf hg i

noncomputable def key (f : Fin c ↪ Fin n) (g : Fin c ↪ Fin m) :
    Carrier (X := Fin n) g → ℕ ×ₗ ℕ :=
  ProfileFaceUnion.paste g (faceKey f 1) (faceKey g (n + 1))

theorem key_right (f : Fin c ↪ Fin n) (g : Fin c ↪ Fin m)
    (hf : StrictMono f) (hg : StrictMono g) (y : Fin m) :
    key f g (right f g y) = faceKey g (n + 1) y :=
  paste_right f g (faceKey_shared f g hf hg) y

theorem key_injective (f : Fin c ↪ Fin n) (g : Fin c ↪ Fin m)
    (hf : StrictMono f) (hg : StrictMono g) : Function.Injective (key f g) := by
  intro x y h
  rcases x with x | x <;> rcases y with y | y
  · exact congrArg Sum.inl ((faceKey_strict f (by decide : 0 < 1)).injective h)
  · obtain ⟨i, _, hi⟩ := (faceKey_overlap f g hf hg x y.val).mp h
    exact False.elim (y.property ⟨i, hi⟩)
  · obtain ⟨i, _, hi⟩ := (faceKey_overlap f g hf hg y x.val).mp h.symm
    exact False.elim (x.property ⟨i, hi⟩)
  · exact congrArg Sum.inr (Subtype.ext
      ((faceKey_strict g (by omega : 0 < n + 1)).injective h))

noncomputable instance (f : Fin c ↪ Fin n) (g : Fin c ↪ Fin m) :
    Fintype (Set.range (key f g)) := Fintype.ofFinite _

noncomputable def keyEquiv (f : Fin c ↪ Fin n) (g : Fin c ↪ Fin m)
    (hf : StrictMono f) (hg : StrictMono g) :
    Carrier (X := Fin n) g ≃ Set.range (key f g) :=
  Equiv.ofInjective (key f g) (key_injective f g hf hg)

noncomputable def enumeration (f : Fin c ↪ Fin n) (g : Fin c ↪ Fin m)
    (hf : StrictMono f) (hg : StrictMono g) :
    Carrier (X := Fin n) g ≃ Fin (Fintype.card (Carrier (X := Fin n) g)) :=
  (keyEquiv f g hf hg).trans
    (Fintype.orderIsoFinOfCardEq _ (Fintype.card_congr (keyEquiv f g hf hg)).symm).symm.toEquiv

theorem enumeration_left (f : Fin c ↪ Fin n) (g : Fin c ↪ Fin m)
    (hf : StrictMono f) (hg : StrictMono g) :
    StrictMono (fun x => enumeration f g hf hg (left g x)) := by
  intro x y hxy
  apply (Fintype.orderIsoFinOfCardEq _
    (Fintype.card_congr (keyEquiv f g hf hg)).symm).symm.strictMono
  exact faceKey_strict f (by decide : 0 < 1) hxy

theorem enumeration_right (f : Fin c ↪ Fin n) (g : Fin c ↪ Fin m)
    (hf : StrictMono f) (hg : StrictMono g) :
    StrictMono (fun y => enumeration f g hf hg (right f g y)) := by
  intro x y hxy
  apply (Fintype.orderIsoFinOfCardEq _
    (Fintype.card_congr (keyEquiv f g hf hg)).symm).symm.strictMono
  change key f g (right f g x) < key f g (right f g y)
  rw [key_right f g hf hg, key_right f g hf hg]
  exact faceKey_strict g (by omega : 0 < n + 1) hxy

end VaughtConjecture.Knight.ProfileBoundaryOrder

namespace VaughtConjecture.Knight.AmalgamatedBoundary
open AmalgamationPlan
variable {ι : Type*} [DecidableEq ι]

def pointImage {κ : Type*} [DecidableEq κ] {B : Finset ι} {C : Finset κ}
    (D : CellScheme B) (e : ι ↪ κ) (he : B.image e = C) : CellScheme C where
  plan := D.plan.image (Finset.image e)
  isPlan := he ▸ Plan.isPlan_image e D.isPlan
  card := D.card
  cell d := ((D.scope d).image e, D.grade d)
  cell_mem d := by
    obtain ⟨hm, hp, hc⟩ := Plan.mem_gradedPlan.mp (D.cell_mem d)
    refine Plan.mem_gradedPlan.mpr ⟨Finset.mem_image.mpr ⟨_, hm, rfl⟩, hp, ?_⟩
    change D.grade d ≤ (D.scope d).card at hc
    simpa only [Finset.card_image_of_injective _ e.injective] using hc

theorem pointImage_complete {κ : Type*} [DecidableEq κ] {B : Finset ι} {C : Finset κ}
    (D : CellScheme B) (e : ι ↪ κ) (he : B.image e = C) (hD : D.IsComplete) :
    (pointImage D e he).IsComplete := by
  intro BJ hBJ
  obtain ⟨hm, hp, hc⟩ := Plan.mem_gradedPlan.mp hBJ
  obtain ⟨K, hK, hKB⟩ := Finset.mem_image.mp hm
  have hj : BJ.2 ≤ K.card := by
    rwa [← hKB, Finset.card_image_of_injective _ e.injective] at hc
  obtain ⟨d, hd⟩ := hD (K, BJ.2) (Plan.mem_gradedPlan.mpr ⟨hK, hp, hj⟩)
  exact ⟨d, by change ((D.cell d).1.image e, (D.cell d).2) = BJ; rw [hd]; exact Prod.ext hKB rfl⟩

structure Overlap {B C : Finset ι} (D : CellScheme B) (E : CellScheme C) (k : ℕ) where
  f : Fin k ↪ Cell D
  g : Fin k ↪ Cell E
  f_mono : StrictMono f
  g_mono : StrictMono g
  shared : ∀ i, D.cell (f i) = E.cell (g i)
  left_exhaustive : ∀ d, D.scope d ⊆ C → ∃ i, f i = d
  right_exhaustive : ∀ e, E.scope e ⊆ B → ∃ i, g i = e

end VaughtConjecture.Knight.AmalgamatedBoundary

namespace VaughtConjecture.Knight.OrderedFaceBoundary
open AmalgamationPlan
open AmalgamatedBoundary (Overlap)
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
variable (D : CellScheme B) (E : CellScheme C) {k : ℕ} (w : Overlap D E k)

abbrev Boundary := ProfileFaceUnion.Carrier (X := Cell D) w.g

noncomputable def index : Boundary D E w → Finset ι × ℕ :=
  ProfileFaceUnion.paste w.g D.cell E.cell

theorem index_right (e : Cell E) :
    index D E w (ProfileFaceUnion.right w.f w.g e) = E.cell e :=
  ProfileFaceUnion.paste_right w.f w.g w.shared e

theorem inside_left (z : Boundary D E w) (hz : (index D E w z).1 ⊆ B) :
    ∃ d, ProfileFaceUnion.left w.g d = z := by
  rcases ProfileFaceUnion.covered w.f w.g z with ⟨d, rfl⟩ | ⟨e, rfl⟩
  · exact ⟨d, rfl⟩
  · rw [index_right] at hz
    obtain ⟨i, rfl⟩ := w.right_exhaustive e hz
    exact ⟨w.f i, (ProfileFaceUnion.right_shared w.f w.g i).symm⟩

theorem inside_right (z : Boundary D E w) (hz : (index D E w z).1 ⊆ C) :
    ∃ e, ProfileFaceUnion.right w.f w.g e = z := by
  rcases ProfileFaceUnion.covered w.f w.g z with ⟨d, rfl⟩ | ⟨e, rfl⟩
  · obtain ⟨i, rfl⟩ := w.left_exhaustive d hz
    exact ⟨w.g i, ProfileFaceUnion.right_shared w.f w.g i⟩
  · exact ⟨e, rfl⟩

theorem below_left (d : Cell D) (z : Boundary D E w) :
    GradedLe (index D E w z) (D.cell d) ↔
      ∃ e : D.below (D.cell d), ProfileFaceUnion.left w.g e.1 = z := by
  constructor
  · intro h
    obtain ⟨e, rfl⟩ := inside_left D E w z
      (h.1.trans (D.isPlan.subset_of_mem (D.scope_mem_plan d)))
    exact ⟨⟨e, h⟩, rfl⟩
  · rintro ⟨e, rfl⟩; exact e.2

theorem below_right (d : Cell E) (z : Boundary D E w) :
    GradedLe (index D E w z) (E.cell d) ↔
      ∃ e : E.below (E.cell d), ProfileFaceUnion.right w.f w.g e.1 = z := by
  constructor
  · intro h
    obtain ⟨e, rfl⟩ := inside_right D E w z
      (h.1.trans (E.isPlan.subset_of_mem (E.scope_mem_plan d)))
    rw [index_right] at h
    exact ⟨⟨e, h⟩, rfl⟩
  · rintro ⟨e, rfl⟩; rw [index_right]; exact e.2

variable (R : Finset (Finset ι)) (hR : Plan.IsPlan A R)
variable (hD : D.plan ⊆ R) (hE : E.plan ⊆ R)

include hD hE in
theorem index_mem (z : Boundary D E w) : index D E w z ∈ Plan.gradedPlan R := by
  rcases ProfileFaceUnion.covered w.f w.g z with ⟨d, rfl⟩ | ⟨e, rfl⟩
  · obtain ⟨hm, hp, hc⟩ := Plan.mem_gradedPlan.mp (D.cell_mem d)
    exact Plan.mem_gradedPlan.mpr ⟨hD hm, hp, hc⟩
  · rw [index_right]
    obtain ⟨hm, hp, hc⟩ := Plan.mem_gradedPlan.mp (E.cell_mem e)
    exact Plan.mem_gradedPlan.mpr ⟨hE hm, hp, hc⟩

noncomputable def enumeration : Boundary D E w ≃ Fin (Fintype.card (Boundary D E w)) :=
  ProfileBoundaryOrder.enumeration w.f w.g w.f_mono w.g_mono

noncomputable def scheme : CellScheme A where
  plan := R
  isPlan := hR
  card := Fintype.card (Boundary D E w)
  cell d := index D E w ((enumeration D E w).symm d)
  cell_mem _ := index_mem D E w R hD hE _

noncomputable def leftCell (d : Cell D) : Cell (scheme D E w R hR hD hE) :=
  enumeration D E w (ProfileFaceUnion.left w.g d)

noncomputable def rightCell (e : Cell E) : Cell (scheme D E w R hR hD hE) :=
  enumeration D E w (ProfileFaceUnion.right w.f w.g e)

theorem left_index (d : Cell D) :
    (scheme D E w R hR hD hE).cell (leftCell D E w R hR hD hE d) = D.cell d := by
  change index D E w ((enumeration D E w).symm (enumeration D E w _)) = _
  rw [Equiv.symm_apply_apply]; rfl

theorem right_index (e : Cell E) :
    (scheme D E w R hR hD hE).cell (rightCell D E w R hR hD hE e) = E.cell e := by
  change index D E w ((enumeration D E w).symm (enumeration D E w _)) = _
  rw [Equiv.symm_apply_apply, index_right]

theorem left_order : StrictMono (leftCell D E w R hR hD hE) :=
  ProfileBoundaryOrder.enumeration_left w.f w.g w.f_mono w.g_mono

theorem right_order : StrictMono (rightCell D E w R hR hD hE) :=
  ProfileBoundaryOrder.enumeration_right w.f w.g w.f_mono w.g_mono

theorem left_exhaustive (c : Cell (scheme D E w R hR hD hE))
    (hc : (scheme D E w R hR hD hE).scope c ⊆ B) :
    ∃ d, leftCell D E w R hR hD hE d = c := by
  obtain ⟨d, hd⟩ := inside_left D E w ((enumeration D E w).symm c) hc
  exact ⟨d, (congrArg (enumeration D E w) hd).trans ((enumeration D E w).apply_symm_apply c)⟩

theorem right_exhaustive (c : Cell (scheme D E w R hR hD hE))
    (hc : (scheme D E w R hR hD hE).scope c ⊆ C) :
    ∃ e, rightCell D E w R hR hD hE e = c := by
  obtain ⟨e, he⟩ := inside_right D E w ((enumeration D E w).symm c) hc
  exact ⟨e, (congrArg (enumeration D E w) he).trans ((enumeration D E w).apply_symm_apply c)⟩

theorem overlap (d : Cell D) (e : Cell E) :
    leftCell D E w R hR hD hE d = rightCell D E w R hR hD hE e ↔
      ∃ i, w.f i = d ∧ w.g i = e :=
  (Equiv.apply_eq_iff_eq (enumeration D E w)).trans (ProfileFaceUnion.overlap w.f w.g d e)

noncomputable def leftBelow (d : Cell D) : D.below (D.cell d) ≃
    (scheme D E w R hR hD hE).below
      ((scheme D E w R hR hD hE).cell (leftCell D E w R hR hD hE d)) :=
  Equiv.ofBijective (fun e => ⟨leftCell D E w R hR hD hE e.1, by
    rw [left_index, left_index]; exact e.2⟩) ⟨fun _ _ h =>
      Subtype.ext ((left_order D E w R hR hD hE).injective (congrArg Subtype.val h)), fun e => by
      have he := e.2.trans (show GradedLe
        ((scheme D E w R hR hD hE).cell (leftCell D E w R hR hD hE d)) (D.cell d) from by
        rw [left_index]; exact GradedLe.refl _)
      obtain ⟨f, hf⟩ := (below_left D E w d ((enumeration D E w).symm e.1)).mp he
      exact ⟨f, Subtype.ext ((congrArg (enumeration D E w) hf).trans
        ((enumeration D E w).apply_symm_apply e.1))⟩⟩

noncomputable def rightBelow (d : Cell E) : E.below (E.cell d) ≃
    (scheme D E w R hR hD hE).below
      ((scheme D E w R hR hD hE).cell (rightCell D E w R hR hD hE d)) :=
  Equiv.ofBijective (fun e => ⟨rightCell D E w R hR hD hE e.1, by
    rw [right_index, right_index]; exact e.2⟩) ⟨fun _ _ h =>
      Subtype.ext ((right_order D E w R hR hD hE).injective (congrArg Subtype.val h)), fun e => by
      have he := e.2.trans (show GradedLe
        ((scheme D E w R hR hD hE).cell (rightCell D E w R hR hD hE d)) (E.cell d) from by
        rw [right_index]; exact GradedLe.refl _)
      obtain ⟨f, hf⟩ := (below_right D E w d ((enumeration D E w).symm e.1)).mp he
      exact ⟨f, Subtype.ext ((congrArg (enumeration D E w) hf).trans
        ((enumeration D E w).apply_symm_apply e.1))⟩⟩

theorem complete_on_input (hDc : D.IsComplete) (hEc : E.IsComplete)
    {BJ : Finset ι × ℕ}
    (hBJ : BJ ∈ Plan.gradedPlan D.plan ∨ BJ ∈ Plan.gradedPlan E.plan) :
    ∃ c, (scheme D E w R hR hD hE).cell c = BJ := by
  rcases hBJ with hl | hr
  · obtain ⟨d, hd⟩ := hDc BJ hl
    exact ⟨leftCell D E w R hR hD hE d, (left_index D E w R hR hD hE d).trans hd⟩
  · obtain ⟨e, he⟩ := hEc BJ hr
    exact ⟨rightCell D E w R hR hD hE e, (right_index D E w R hR hD hE e).trans he⟩

end VaughtConjecture.Knight.OrderedFaceBoundary

namespace VaughtConjecture.Knight.AmalgamatedBoundary
open AmalgamationPlan AmalgamatedBoundaryPlan
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} (s : Step A)
variable (D : CellScheme (A.erase s.a)) (E : CellScheme (A.erase s.b))
variable {k : ℕ} (w : Overlap D E k)

theorem left_sub (hD : D.plan = s.left) : D.plan ⊆ s.plan :=
  hD ▸ Finset.subset_union_left.trans Finset.subset_union_left

theorem right_sub (hE : E.plan = s.right) : E.plan ⊆ s.plan :=
  hE ▸ Finset.subset_union_right.trans Finset.subset_union_left

section
variable {s}
abbrev Boundary := OrderedFaceBoundary.Boundary D E w
@[reducible] noncomputable def index := OrderedFaceBoundary.index D E w
@[reducible] noncomputable def enumeration := OrderedFaceBoundary.enumeration D E w
end

theorem no_full (z : Boundary D E w) : (index D E w z).1 ≠ A := by
  rcases ProfileFaceUnion.covered w.f w.g z with ⟨d, rfl⟩ | ⟨e, rfl⟩
  · intro h
    have hs := D.isPlan.subset_of_mem (D.scope_mem_plan d)
    change D.scope d = A at h
    exact Finset.notMem_erase s.a A ((h ▸ hs) s.ha)
  · dsimp only [index]
    rw [OrderedFaceBoundary.index_right]
    intro h
    have hs := E.isPlan.subset_of_mem (E.scope_mem_plan e)
    change E.scope e = A at h
    exact Finset.notMem_erase s.b A ((h ▸ hs) s.hb)

variable (hD : D.plan = s.left) (hE : E.plan = s.right)

@[reducible] noncomputable def scheme : CellScheme A :=
  OrderedFaceBoundary.scheme D E w s.plan (isPlan s) (left_sub s D hD) (right_sub s E hE)

theorem scope_proper (c : Cell (scheme s D E w hD hE)) :
    (scheme s D E w hD hE).scope c ≠ A :=
  no_full s D E w ((enumeration D E w).symm c)

@[reducible] noncomputable def leftCell (d : Cell D) : Cell (scheme s D E w hD hE) :=
  OrderedFaceBoundary.leftCell D E w s.plan (isPlan s) (left_sub s D hD) (right_sub s E hE) d

@[reducible] noncomputable def rightCell (e : Cell E) : Cell (scheme s D E w hD hE) :=
  OrderedFaceBoundary.rightCell D E w s.plan (isPlan s) (left_sub s D hD) (right_sub s E hE) e

theorem left_index (d : Cell D) :
    (scheme s D E w hD hE).cell (leftCell s D E w hD hE d) = D.cell d :=
  OrderedFaceBoundary.left_index D E w s.plan (isPlan s) (left_sub s D hD) (right_sub s E hE) d

theorem right_index (e : Cell E) :
    (scheme s D E w hD hE).cell (rightCell s D E w hD hE e) = E.cell e :=
  OrderedFaceBoundary.right_index D E w s.plan (isPlan s) (left_sub s D hD) (right_sub s E hE) e

theorem left_order : StrictMono (leftCell s D E w hD hE) :=
  OrderedFaceBoundary.left_order D E w s.plan (isPlan s) (left_sub s D hD) (right_sub s E hE)

theorem right_order : StrictMono (rightCell s D E w hD hE) :=
  OrderedFaceBoundary.right_order D E w s.plan (isPlan s) (left_sub s D hD) (right_sub s E hE)



theorem complete_proper (hDc : D.IsComplete) (hEc : E.IsComplete)
    {BJ : Finset ι × ℕ} (hBJ : BJ ∈ Plan.gradedPlan s.plan) (hB : BJ.1 ≠ A) :
    ∃ c, (scheme s D E w hD hE).cell c = BJ :=
  OrderedFaceBoundary.complete_on_input D E w s.plan (isPlan s) (left_sub s D hD) (right_sub s E hE)
    hDc hEc ((proper_index_cover s hBJ hB).imp (hD ▸ id) (hE ▸ id))

end VaughtConjecture.Knight.AmalgamatedBoundary

namespace VaughtConjecture.Knight.AmalgamatedBoundaryRows
open AmalgamationPlan Transform Value ExtOrd
variable {ι : Type*} [DecidableEq ι]

open Classical in
noncomputable def total {B : Finset ι} {D : CellScheme B} (sem : Semantics D)
    (c d : Cell D) : ExtOrd :=
  if h : GradedLe (D.cell d) (D.cell c) then sem.E c ⟨d, h⟩ else ⊥

theorem total_below {B : Finset ι} {D : CellScheme B} (sem : Semantics D)
    (c : Cell D) (d : D.below (D.cell c)) : total sem c d.1 = sem.E c d := by
  rw [total, dite_eq_left d.2]
  exact congrArg (sem.E c) (Subtype.ext rfl)

theorem total_outside {B : Finset ι} {D : CellScheme B} (sem : Semantics D)
    (c d : Cell D) (h : ¬ GradedLe (D.cell d) (D.cell c)) : total sem c d = ⊥ := by
  simp only [total, dite_eq_right h]

section Push
variable {B C : Finset ι} {D : CellScheme B} {K : CellScheme C}
variable (f : Cell D → Cell K) (hf : Function.Injective f)
variable (hi : ∀ d, K.cell (f d) = D.cell d) (sem : Semantics D)

noncomputable def pushRow (c : Cell D) : Cell K → ExtOrd :=
  Function.extend f (total sem c) (fun _ => ⊥)

include hf in
theorem pushRow_at (c d : Cell D) : pushRow f sem c (f d) = total sem c d :=
  hf.extend_apply _ _ _

include hf hi in
theorem pushRow_outside (c : Cell D) (z : Cell K)
    (hz : ¬ GradedLe (K.cell z) (D.cell c)) : pushRow f sem c z = ⊥ := by
  classical
  by_cases h : ∃ d, f d = z
  · obtain ⟨d, rfl⟩ := h
    rw [pushRow_at f hf]
    apply total_outside
    simpa only [hi] using hz
  · exact Function.extend_apply' _ _ _ h
end Push

end VaughtConjecture.Knight.AmalgamatedBoundaryRows

namespace VaughtConjecture.Knight.OrderedFaceBoundaryRows
open AmalgamationPlan OrderedFaceBoundary Transform Value ExtOrd
open AmalgamatedBoundary (Overlap)
open AmalgamatedBoundaryRows (total total_below pushRow pushRow_at pushRow_outside)

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
variable (D : CellScheme B) (E : CellScheme C) {k : ℕ} (w : Overlap D E k)
variable (R : Finset (Finset ι)) (hR : Plan.IsPlan A R)
variable (hD : D.plan ⊆ R) (hE : E.plan ⊆ R)
variable (semD : Semantics D) (semE : Semantics E)

local notation "K" => scheme D E w R hR hD hE
local notation "l" => leftCell D E w R hR hD hE
local notation "r" => rightCell D E w R hR hD hE

def Compatible : Prop :=
  ∀ i j, total semD (w.f i) (w.f j) = total semE (w.g i) (w.g j)

theorem shared_cell (i : Fin k) : l (w.f i) = r (w.g i) :=
  (overlap D E w R hR hD hE _ _).mpr ⟨i, rfl, rfl⟩

theorem covered (c : Cell K) : (∃ d, l d = c) ∨ ∃ e, r e = c := by
  rcases ProfileFaceUnion.covered w.f w.g ((enumeration D E w).symm c) with ⟨d, hd⟩ | ⟨e, he⟩
  · exact Or.inl ⟨d, (congrArg (enumeration D E w) hd).trans
      ((enumeration D E w).apply_symm_apply c)⟩
  · exact Or.inr ⟨e, (congrArg (enumeration D E w) he).trans
      ((enumeration D E w).apply_symm_apply c)⟩

theorem pushRow_shared (hc : Compatible D E w semD semE) (i : Fin k) :
    pushRow l semD (w.f i) = pushRow r semE (w.g i) := by
  funext z
  by_cases hz : GradedLe ((K).cell z) (D.cell (w.f i))
  · have hzl : GradedLe ((K).cell z) ((K).cell (l (w.f i))) := by rw [left_index]; exact hz
    obtain ⟨d, hd⟩ := (leftBelow D E w R hR hD hE (w.f i)).surjective ⟨z, hzl⟩
    have he : l d.1 = z := congrArg Subtype.val hd
    have hdc : D.scope d.1 ⊆ C := by
      have hs : D.scope d.1 ⊆ (D.cell (w.f i)).1 := d.2.1
      have hs' : (D.cell (w.f i)).1 ⊆ (E.cell (w.g i)).1 :=
        subset_of_eq (congrArg Prod.fst (w.shared i))
      exact hs.trans (hs'.trans (E.isPlan.subset_of_mem (E.scope_mem_plan _)))
    obtain ⟨j, hj⟩ := w.left_exhaustive d.1 hdc
    rw [← he, ← hj, pushRow_at l (left_order D E w R hR hD hE).injective,
      shared_cell, pushRow_at r (right_order D E w R hR hD hE).injective]
    exact hc i j
  · rw [pushRow_outside l (left_order D E w R hR hD hE).injective
      (left_index D E w R hR hD hE) semD _ _ hz,
      pushRow_outside r (right_order D E w R hR hD hE).injective
      (right_index D E w R hR hD hE) semE]
    rwa [← w.shared]

noncomputable def table (c : Cell K) : Cell K → ExtOrd :=
  ProfileFaceUnion.paste w.g (pushRow l semD) (pushRow r semE) ((enumeration D E w).symm c)

theorem table_left (c d : Cell D) : table D E w R hR hD hE semD semE (l c) (l d) =
    total semD c d := by
  change ProfileFaceUnion.paste w.g (pushRow l semD) (pushRow r semE)
    ((enumeration D E w).symm (enumeration D E w (ProfileFaceUnion.left w.g c))) (l d) = _
  rw [Equiv.symm_apply_apply]
  exact pushRow_at l (left_order D E w R hR hD hE).injective semD c d

theorem table_right (hc : Compatible D E w semD semE) (c d : Cell E) :
    table D E w R hR hD hE semD semE (r c) (r d) = total semE c d := by
  change ProfileFaceUnion.paste w.g (pushRow l semD) (pushRow r semE)
    ((enumeration D E w).symm (enumeration D E w (ProfileFaceUnion.right w.f w.g c))) (r d) = _
  rw [Equiv.symm_apply_apply, ProfileFaceUnion.paste_right w.f w.g
    (pushRow_shared D E w R hR hD hE semD semE hc)]
  exact pushRow_at r (right_order D E w R hR hD hE).injective semE c d

variable (hc : Compatible D E w semD semE)

include hc in
theorem table_orderly (c : Cell K) (d : (K).below ((K).cell c)) :
    table D E w R hR hD hE semD semE c d.1 =
      extVisibilityReplace (table D E w R hR hD hE semD semE c d.1)
        ((K).grade d.1) ((K).grade d.1) := by
  rcases covered D E w R hR hD hE c with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · obtain ⟨e, rfl⟩ := (leftBelow D E w R hR hD hE c).surjective d
    change table D E w R hR hD hE semD semE (l c) (l e.1) =
      extVisibilityReplace (table D E w R hR hD hE semD semE (l c) (l e.1))
        ((K).cell (l e.1)).2 ((K).cell (l e.1)).2
    rw [table_left, total_below, left_index]; exact semD.orderly c e
  · obtain ⟨e, rfl⟩ := (rightBelow D E w R hR hD hE c).surjective d
    change table D E w R hR hD hE semD semE (r c) (r e.1) =
      extVisibilityReplace (table D E w R hR hD hE semD semE (r c) (r e.1))
        ((K).cell (r e.1)).2 ((K).cell (r e.1)).2
    rw [table_right D E w R hR hD hE semD semE hc, total_below, right_index]
    exact semE.orderly c e

noncomputable def rows : Semantics K where
  E c d := table D E w R hR hD hE semD semE c d.1
  orderly := table_orderly D E w R hR hD hE semD semE hc

theorem rows_left (c : Cell D) (d : D.below (D.cell c)) :
    (rows D E w R hR hD hE semD semE hc).E (l c) (leftBelow D E w R hR hD hE c d) =
      semD.E c d :=
  (table_left D E w R hR hD hE semD semE c d.1).trans (total_below semD c d)

theorem rows_right (c : Cell E) (d : E.below (E.cell c)) :
    (rows D E w R hR hD hE semD semE hc).E (r c) (rightBelow D E w R hR hD hE c d) =
      semE.E c d :=
  (table_right D E w R hR hD hE semD semE hc c d.1).trans (total_below semE c d)

end VaughtConjecture.Knight.OrderedFaceBoundaryRows

namespace VaughtConjecture.Knight.AmalgamatedBoundaryRows
open AmalgamationPlan AmalgamatedBoundaryPlan AmalgamatedBoundary
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} (s : Step A)
variable (D : CellScheme (A.erase s.a)) (E : CellScheme (A.erase s.b))
variable {k : ℕ} (w : Overlap D E k) (hD : D.plan = s.left) (hE : E.plan = s.right)
variable (semD : Semantics D) (semE : Semantics E)

@[reducible] def Compatible : Prop :=
  OrderedFaceBoundaryRows.Compatible D E w semD semE



theorem covered (c : Cell (scheme s D E w hD hE)) :
    (∃ d, leftCell s D E w hD hE d = c) ∨ ∃ e, rightCell s D E w hD hE e = c :=
  OrderedFaceBoundaryRows.covered D E w s.plan (isPlan s)
    (left_sub s D hD) (right_sub s E hE) c

@[reducible] noncomputable def rows (hc : Compatible s D E w semD semE) :
    Semantics (scheme s D E w hD hE) :=
  OrderedFaceBoundaryRows.rows D E w s.plan (isPlan s)
    (left_sub s D hD) (right_sub s E hE) semD semE hc



end VaughtConjecture.Knight.AmalgamatedBoundaryRows
