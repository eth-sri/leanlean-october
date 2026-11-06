module

/-
Copyright (c) 2025 Math_XMUM. All rights reserved.
Released under the MIT license; see THIRD_PARTY_LICENSE.txt.

Ported from math-xmum/Brouwer, commit c938f0f2b355adc9f07666c1c2c4002100406923 (2025-11-23),
Gametheory/Scarf.lean, to the project's pinned mathlib v4.19.0.
Upstream: https://github.com/math-xmum/Brouwer
Only import/API compatibility and proof elaboration changes are intended.
-/
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Tauto
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.ByContra
public import Mathlib.Tactic.Cases

public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Order.PiLex
public import Mathlib.Data.PNat.Basic
public import Mathlib.Topology.MetricSpace.Sequences
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

section fiberlemma

open Finset

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

lemma injOn_sdiff (s : Finset α) (f : α → β) (h : s.card = (Finset.image f s).card + 1) :
    ∃ a b, a ∈ s ∧ b ∈ s ∧ f a = f b ∧ a ≠ b := by
  have h_not_inj : ¬ Set.InjOn f s := fun h1 => by linarith [Finset.card_image_of_injOn h1]
  rw [Set.InjOn] at h_not_inj; push_neg at h_not_inj
  obtain ⟨a, as, b, bs, h1, h2⟩ := h_not_inj
  exact ⟨a, b, as, bs, h1, h2⟩

end fiberlemma

open Classical
open Finset

variable {T : Type*} [Inhabited T]
variable {I : Type*}

class IndexedLOrder (I T :Type*) where
  IST : I → LinearOrder T

instance : FunLike (IndexedLOrder I T) I (LinearOrder T) where
  coe := fun a => a.IST
  coe_injective := fun f g h => by cases f; cases g; congr

section
variable [IST : IndexedLOrder I T]

set_option quotPrecheck false

local notation  lhs "<[" i "]" rhs => (IST i).lt lhs rhs
local notation  lhs "≤[" i "]" rhs => (IST i).le lhs rhs

namespace IndexedLOrder
variable (σ : Finset T) (C : Finset I)

def isDominant  :=
  ∀ y, ∃ i ∈ C, ∀ x ∈ σ,  y ≤[i] x

variable {σ C} in
lemma Nonempty_of_Dominant (h : IST.isDominant σ C) : C.Nonempty :=
  let ⟨j, hj⟩ := h default; ⟨j, hj.1⟩

omit [Inhabited T] in
lemma Dominant_of_subset (σ τ : Finset T) (C : Finset I) (h1 : τ ⊆ σ) (h2 : isDominant σ C) :
    isDominant τ C := fun y =>
  let ⟨j, hj1, hj2⟩ := h2 y; ⟨j, hj1, fun x hx => hj2 x (h1 hx)⟩

omit [Inhabited T] in
lemma Dominant_of_supset (σ : Finset T) (C D: Finset I) (h1 : C ⊆ D) (h2 : isDominant σ C) :
    isDominant σ D := fun y =>
  let ⟨j, hj1, hj2⟩ := h2 y; ⟨j, h1 hj1, hj2⟩

abbrev mini {σ : Finset T} (h2 : σ.Nonempty) (i : I) : T := @Finset.min' _ (IST i) _ h2

omit [Inhabited T] in
lemma keylemma_of_dominant {σ : Finset T} {C: Finset I} (h1 : IST.isDominant σ C) (h2: σ.Nonempty): σ = C.image (mini h2) := by
  ext a; simp only [mem_image]
  refine ⟨fun ha => ?_, fun ⟨i, _, ha⟩ => ha ▸ @Finset.min'_mem _ (IST i) _ h2⟩
  obtain ⟨i, hi1, hi2⟩ := h1 a
  exact ⟨i, hi1, @le_antisymm _ (IST i).toPartialOrder _ _ (@Finset.min'_le _ (IST i) _ _ ha) (@Finset.le_min' _ (IST i) _ h2 a hi2)⟩

omit [Inhabited T] in
lemma card_le_of_domiant {σ : Finset T} {C: Finset I} (h1 : IST.isDominant σ C) : σ.card ≤ C.card := by
  by_cases h2 : σ.Nonempty
  · rw [keylemma_of_dominant h1 h2]; exact Finset.card_image_le
  · simp [not_nonempty_iff_eq_empty.mp h2]

abbrev isCell  := isDominant σ C

abbrev isRoom :=  isCell σ C ∧ C.card = σ.card

lemma sigma_nonempty_of_room {σ : Finset T} {C : Finset I} (h : isRoom σ C) : σ.Nonempty :=
  Finset.card_pos.1 (h.2 ▸ Finset.card_pos.2 (Nonempty_of_Dominant h.1))

abbrev isDoor  :=  isCell σ C ∧ C.card = σ.card + 1

variable [DecidableEq T] [DecidableEq I]

inductive isDoorof (τ : Finset T) (D : Finset I) (σ : Finset T) (C : Finset I) : Prop
  | idoor (h0 : isCell σ C) (h1 : isDoor τ D) (x :T) (h1 : x ∉ τ) (h2 : insert x τ = σ) (h3 : D = C)
  | odoor (h0 : isCell σ C) (h1 : isDoor τ D) (j :I) (h1 : j ∉ C) (h2 : τ = σ) (h3 : D = insert j C)

variable {σ C} in
omit [Inhabited T] in
lemma isRoom_of_Door (h1 : isDoorof τ D σ C) : IST.isRoom σ C := by
  rcases h1 with ⟨h0, h2, x, h3, rfl, rfl⟩ | ⟨h0, h2, j, h3, rfl, rfl⟩
  · exact ⟨h0, by rw [Finset.card_insert_of_notMem h3, h2.2]⟩
  · exact ⟨h0, by have h := h2.2; rw [Finset.card_insert_of_notMem h3] at h; omega⟩

variable (τ D) in
abbrev isOutsideDoor := IST.isDoor τ D ∧ τ = Finset.empty

variable (τ D) in
abbrev isInternalDoor := IST.isDoor τ D ∧ τ.Nonempty

omit [Inhabited T] [DecidableEq T] [DecidableEq I] in
lemma outsidedoor_singleton (i : I) : IST.isOutsideDoor Finset.empty {i} :=
  ⟨⟨fun _ => ⟨i, Finset.mem_singleton_self i, fun _ hx => False.elim (Finset.notMem_empty _ hx)⟩, rfl⟩, rfl⟩

section KeyLemma

def M_set (τ : Finset T) (D : Finset I) (i : I) (h_nonempty : τ.Nonempty) : Set T :=
  {y : T | ∀ k ∈ D, k ≠ i → mini h_nonempty k <[k] y}

def is_maximal_in_M_set (τ : Finset T) (D : Finset I) (i : I) (h_nonempty : τ.Nonempty) (x : T) : Prop :=
  x ∈ M_set τ D i h_nonempty ∧ ∀ y ∈ M_set τ D i h_nonempty, y ≤[i] x

noncomputable def m_element [Fintype T] (τ : Finset T) (D : Finset I) (i : I) (h_nonempty : τ.Nonempty)
    (h : (M_set τ D i h_nonempty).Nonempty) : T :=
  @Finset.max' _ (IST i) (M_set τ D i h_nonempty).toFinset (Set.toFinset_nonempty.mpr h)

omit[Inhabited T][DecidableEq T][DecidableEq I] in
theorem m_element_is_maximal [Fintype T] (τ : Finset T) (D : Finset I) (i : I) (h_nonempty : τ.Nonempty)
    (h : (M_set τ D i h_nonempty).Nonempty) :
    is_maximal_in_M_set τ D i h_nonempty (m_element τ D i h_nonempty h) :=
  ⟨Set.mem_toFinset.mp (@Finset.max'_mem _ (IST i) _ (Set.toFinset_nonempty.mpr h)),
   fun _ hy => @Finset.le_max' _ (IST i) _ _ (Set.mem_toFinset.mpr hy)⟩

omit [Inhabited T] in
lemma sublemma_3_1 [Fintype T] (τ : Finset T) (D : Finset I)
    (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty) :
    ∀ i ∈ D, (IST.isDominant τ (D.erase i) ↔
      (∃ a b, a ∈ D ∧ b ∈ D ∧ a ≠ b ∧
       mini h_nonempty a = mini h_nonempty b ∧
       (i = a ∨ i = b) ∧
       M_set τ D i h_nonempty = ∅)) := by
  intro i hi
  constructor
  · intro h_dom
    have h_image_card : D.card = (D.image (mini h_nonempty)).card + 1 := by
      have h_eq : D.image (mini h_nonempty) = τ := by convert (keylemma_of_dominant h_door.1 h_nonempty).symm
      rw [h_door.2, h_eq]
    obtain ⟨a, b, ha_mem, hb_mem, h_eq_mini, h_ne⟩ := injOn_sdiff D (mini h_nonempty) h_image_card
    use a, b, ha_mem, hb_mem, h_ne, h_eq_mini
    by_cases h_case : i = a ∨ i = b
    · refine ⟨h_case, ?_⟩
      ext y; simp [M_set]
      obtain ⟨k, hk_in_erase, hk_dom⟩ := h_dom y
      exact ⟨k, (Finset.mem_erase.mp hk_in_erase).2, (Finset.mem_erase.mp hk_in_erase).1, hk_dom⟩
    · push_neg at h_case
      have h_inj : Set.InjOn (mini h_nonempty) (D.erase i : Set I) := by
        apply Finset.injOn_of_card_image_eq
        have h_eq : (D.erase i).image (mini h_nonempty) = τ := by convert (keylemma_of_dominant h_dom h_nonempty).symm
        rw [h_eq, Finset.card_erase_of_mem hi, h_door.2]; simp
      exact (h_ne (h_inj (Finset.mem_erase.mpr ⟨h_case.1.symm, ha_mem⟩)
        (Finset.mem_erase.mpr ⟨h_case.2.symm, hb_mem⟩) h_eq_mini)).elim
  · rintro ⟨a, b, _, _, _, _, _, h_Mi_empty⟩ y
    simp only [M_set, Set.mem_setOf_eq, Set.eq_empty_iff_forall_notMem] at h_Mi_empty
    replace h_Mi_empty := h_Mi_empty y; push_neg at h_Mi_empty
    obtain ⟨k, hk_mem, hk_ne_i, hk_not_lt⟩ := h_Mi_empty
    exact ⟨k, Finset.mem_erase.mpr ⟨hk_ne_i, hk_mem⟩, fun x hx =>
      @le_trans _ (IST k).toPreorder _ _ _ hk_not_lt (@Finset.min'_le _ (IST k) τ x hx)⟩

omit [Inhabited T] in
lemma sublemma_3_2 [Fintype T] (τ : Finset T) (D : Finset I) (x : T)
    (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty) (h_not_mem : x ∉ τ)
    (a b : I) (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b)
    (h_eq : mini h_nonempty a = mini h_nonempty b) :
    IST.isDominant (insert x τ) D ↔
    (∃ i ∈ ({a, b} : Finset I), (M_set τ D i h_nonempty).Nonempty ∧
     is_maximal_in_M_set τ D i h_nonempty x) := by
  constructor
  · intro h_dominant
    have h_insert_nonempty : (insert x τ).Nonempty := Finset.insert_nonempty x τ
    have h_min_eq_image : D.image (mini h_insert_nonempty) = insert x τ := by
      convert (keylemma_of_dominant h_dominant h_insert_nonempty).symm
    obtain ⟨i, hi_mem, hi_eq⟩ : ∃ i ∈ D, mini h_insert_nonempty i = x :=
      Finset.mem_image.mp (by rw [h_min_eq_image]; exact Finset.mem_insert_self x τ)
    have h_inj_insert : Set.InjOn (mini h_insert_nonempty) (D : Set I) := by
      apply Finset.injOn_of_card_image_eq
      rw [h_min_eq_image, Finset.card_insert_of_notMem h_not_mem, h_door.2]
    have h_mini_eq_for_ne_i (k : I) (hk_mem : k ∈ D) (hk_ne_i : k ≠ i) :
        mini h_insert_nonempty k = mini h_nonempty k := by
      have h_cases : mini h_insert_nonempty k = mini h_nonempty k ∨ mini h_insert_nonempty k = x := by
        letI := IST k
        by_cases h : τ.min' h_nonempty ≤[k] x
        · refine Or.inl (le_antisymm (Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.min'_mem _ h_nonempty)))
            (Finset.le_min' _ _ _ fun y hy => ?_))
          rcases Finset.mem_insert.mp hy with rfl | h_mem <;> [exact h; exact Finset.min'_le _ _ h_mem]
        · refine Or.inr (le_antisymm (Finset.min'_le _ _ (Finset.mem_insert_self _ _))
            (Finset.le_min' _ _ _ fun y hy => ?_))
          rcases Finset.mem_insert.mp hy with rfl | h_mem
          · exact le_rfl
          · exact le_of_not_ge fun h_le => h (le_trans (Finset.min'_le _ _ h_mem) h_le)
      exact h_cases.resolve_right fun h_eq =>
        hk_ne_i (h_inj_insert hk_mem hi_mem (h_eq.trans hi_eq.symm))
    have hxM : x ∈ M_set τ D i h_nonempty := fun k hk_mem hk_ne_i => by
      letI := IST k
      refine lt_of_le_of_ne ?_ fun h_eq_x => h_not_mem (h_eq_x ▸ Finset.min'_mem τ h_nonempty)
      rw [← h_mini_eq_for_ne_i k hk_mem hk_ne_i]
      exact Finset.min'_le _ _ (Finset.mem_insert_self x τ)
    have h_i_in_ab : i ∈ ({a, b} : Finset I) := by
      by_contra hik
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hik
      have h_contr : mini h_insert_nonempty a = mini h_insert_nonempty b := by
        rw [h_mini_eq_for_ne_i a ha (Ne.symm hik.1), h_mini_eq_for_ne_i b hb (Ne.symm hik.2), h_eq]
      exact hab (h_inj_insert ha hb h_contr)
    refine ⟨i, h_i_in_ab, ⟨x, hxM⟩, hxM, fun y hy => ?_⟩
    obtain ⟨k, hk_in_D, h_y_le_all⟩ := h_dominant y
    by_cases hik : k = i
    · exact hik ▸ h_y_le_all x (Finset.mem_insert_self x τ)
    · letI := IST k
      exact absurd (lt_of_lt_of_le (hy k hk_in_D hik)
        (h_y_le_all _ (Finset.mem_insert_of_mem (Finset.min'_mem _ h_nonempty)))) (lt_irrefl _)
  · rintro ⟨i, hi_mem_ab, _, h_x_in_M, h_x_max⟩ y
    have h_dom_of_le_mini (m : I) (hm : m ∈ D) (hmi : m ≠ i) (hle : y ≤[m] mini h_nonempty m) :
        ∃ j ∈ D, ∀ z ∈ insert x τ, y ≤[j] z := by
      letI := IST m
      refine ⟨m, hm, fun z hz => ?_⟩
      rcases Finset.mem_insert.mp hz with rfl | h_z_in_tau
      · exact le_of_lt (lt_of_le_of_lt hle (h_x_in_M m hm hmi))
      · exact le_trans hle (Finset.min'_le τ z h_z_in_tau)
    obtain ⟨k, hk_in_D, hk_dom⟩ := h_door.1 y
    by_cases h_k_eq_i : k = i
    · subst h_k_eq_i
      letI := IST k
      by_cases h_y_le_x : y ≤[k] x
      · refine ⟨k, hk_in_D, fun z hz => ?_⟩
        rcases Finset.mem_insert.mp hz with rfl | h_z_in_tau <;> [exact h_y_le_x; exact hk_dom z h_z_in_tau]
      · have h_y_not_in_M : y ∉ M_set τ D k h_nonempty := fun hy => h_y_le_x (h_x_max y hy)
        simp only [M_set, Set.mem_setOf_eq, not_forall] at h_y_not_in_M
        obtain ⟨j, hj_in_D, hj_ne_k, hj_not_lt⟩ := h_y_not_in_M
        let := IST j
        exact h_dom_of_le_mini j hj_in_D hj_ne_k (le_of_not_gt hj_not_lt)
    · let := IST k
      exact h_dom_of_le_mini k hk_in_D h_k_eq_i (hk_dom _ (Finset.min'_mem τ h_nonempty))

omit [Inhabited T][DecidableEq T] in
lemma M_sets_disjoint [Fintype T] (τ : Finset T) (D : Finset I) (a b : I)
    (h_nonempty : τ.Nonempty) (h_door : IST.isDoor τ D) (hab : a ≠ b) :
    M_set τ D a h_nonempty ∩ M_set τ D b h_nonempty = ∅ := by
  ext y
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro h_in_a h_in_b
  obtain ⟨k, hk_in_D, hk_dom⟩ := h_door.1 y
  let := IST k
  have hle : y ≤[k] mini h_nonempty k := hk_dom _ (Finset.min'_mem _ h_nonempty)
  by_cases hka : k = a
  · exact not_le.mpr (h_in_b k hk_in_D (hka ▸ hab)) hle
  · exact not_le.mpr (h_in_a k hk_in_D hka) hle

omit [Inhabited T][DecidableEq T] in
lemma m_element_not_in_tau [Fintype T] (τ : Finset T) (D : Finset I) (i a b : I)
    (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty)
    (ha_mem : a ∈ D) (hb_mem : b ∈ D) (hab : a ≠ b)
    (h_eq_mini : mini h_nonempty a = mini h_nonempty b)
    (h_M_nonempty : (M_set τ D i h_nonempty).Nonempty)
    (h_i_is : i = a ∨ i = b) :
    m_element τ D i h_nonempty h_M_nonempty ∉ τ := by
  let m_i := m_element τ D i h_nonempty h_M_nonempty
  have h_max := (m_element_is_maximal τ D i h_nonempty h_M_nonempty).1
  intro h_m_in_tau
  obtain ⟨k, hk_mem, hk_dom⟩ := h_door.1 m_i
  let := IST k
  have h_m_le_mini : m_i ≤[k] mini h_nonempty k := hk_dom _ (Finset.min'_mem _ h_nonempty)
  by_cases hk_eq_i : k = i
  · subst hk_eq_i
    have h_m_eq_mini : m_i = mini h_nonempty k :=
      le_antisymm h_m_le_mini (Finset.min'_le τ m_i h_m_in_tau)
    rcases h_i_is with rfl | rfl
    · have hlt : mini h_nonempty b <[b] m_i := h_max b hb_mem hab.symm
      rw [h_m_eq_mini, h_eq_mini] at hlt
      let := IST b; exact lt_irrefl _ hlt
    · have hlt : mini h_nonempty a <[a] m_i := h_max a ha_mem hab
      rw [h_m_eq_mini, ← h_eq_mini] at hlt
      let := IST a; exact lt_irrefl _ hlt
  · exact not_le.mpr (h_max k hk_mem hk_eq_i) h_m_le_mini

omit [Inhabited T] in
lemma odoor_index_in_pair [Fintype T] (τ : Finset T) (D : Finset I) (C : Finset I)
    (a b j : I) (_h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty)
    (ha_mem : a ∈ D) (hb_mem : b ∈ D) (hab : a ≠ b)
    (h_eq_mini : mini h_nonempty a = mini h_nonempty b)
    (h_dom : IST.isDominant τ C) (h_room_card : C.card = τ.card)
    (_hj_not_mem : j ∉ C) (hc_eq : D = insert j C) :
    j ∈ ({a, b} : Finset I) := by
  by_contra h_not_in
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h_not_in
  have ha_in_C : a ∈ C := (Finset.mem_insert.mp (hc_eq ▸ ha_mem)).resolve_left (Ne.symm h_not_in.1)
  have hb_in_C : b ∈ C := (Finset.mem_insert.mp (hc_eq ▸ hb_mem)).resolve_left (Ne.symm h_not_in.2)
  have h_inj_C : Set.InjOn (mini h_nonempty) (C : Set I) := by
    apply Finset.injOn_of_card_image_eq
    have h_tau_eq_C_image : τ = C.image (mini h_nonempty) := by convert keylemma_of_dominant h_dom h_nonempty
    rw [← h_tau_eq_C_image, h_room_card]
  exact hab (h_inj_C ha_in_C hb_in_C h_eq_mini)

omit [Inhabited T] [DecidableEq T] [DecidableEq I] in
lemma maximal_element_unique [Fintype T] (τ : Finset T) (D : Finset I) (i : I)
    (h_nonempty : τ.Nonempty) (h_M_nonempty : (M_set τ D i h_nonempty).Nonempty)
    (x : T) (h_x_max : is_maximal_in_M_set τ D i h_nonempty x) :
    x = m_element τ D i h_nonempty h_M_nonempty := by
  have h_mi_max := m_element_is_maximal τ D i h_nonempty h_M_nonempty
  letI := IST i
  exact le_antisymm (h_mi_max.2 x h_x_max.1) (h_x_max.2 _ h_mi_max.1)

omit [Inhabited T] in
theorem internal_door_two_rooms [Fintype T] (τ : Finset T) (D : Finset I)
    (h_int_door : IST.isInternalDoor τ D) :
    ∃ (σ₁ σ₂ : Finset T) (C₁ C₂ : Finset I),
      (σ₁, C₁) ≠ (σ₂, C₂) ∧
      IST.isRoom σ₁ C₁ ∧
      IST.isRoom σ₂ C₂ ∧
      isDoorof τ D σ₁ C₁ ∧
      isDoorof τ D σ₂ C₂ ∧
      (∀ σ C, IST.isRoom σ C → isDoorof τ D σ C →
       (σ = σ₁ ∧ C = C₁) ∨ (σ = σ₂ ∧ C = C₂)) := by
  obtain ⟨h_door, h_nonempty⟩ := h_int_door
  have h_image_card : D.card = (D.image (mini h_nonempty)).card + 1 := by
    have h_eq : D.image (mini h_nonempty) = τ := by convert (keylemma_of_dominant h_door.1 h_nonempty).symm
    rw [h_door.2, h_eq]
  obtain ⟨a, b, ha_mem, hb_mem, h_eq_mini, hab⟩ := injOn_sdiff D (mini h_nonempty) h_image_card
  have h_disjoint := M_sets_disjoint τ D a b h_nonempty h_door hab
  let cand (i : I) : Finset T × Finset I :=
    if h : (M_set τ D i h_nonempty).Nonempty then (insert (m_element τ D i h_nonempty h) τ, D) else (τ, D.erase i)
  have h_cand_door {i : I} (hi : i = a ∨ i = b) : isDoorof τ D (cand i).1 (cand i).2 := by
    have hi_D : i ∈ D := by rcases hi with rfl | rfl <;> assumption
    have hi_ab : i ∈ ({a, b} : Finset I) := by rcases hi with rfl | rfl <;> simp
    dsimp [cand]; split_ifs with h
    · have h_not_mem := m_element_not_in_tau τ D i a b h_door h_nonempty ha_mem hb_mem hab h_eq_mini h hi
      exact isDoorof.idoor ((sublemma_3_2 τ D _ h_door h_nonempty h_not_mem a b ha_mem hb_mem hab h_eq_mini).mpr
        ⟨i, hi_ab, h, m_element_is_maximal τ D i h_nonempty h⟩) h_door _ h_not_mem rfl rfl
    · exact isDoorof.odoor ((sublemma_3_1 τ D h_door h_nonempty i hi_D).mpr
        ⟨a, b, ha_mem, hb_mem, hab, h_eq_mini, hi, Set.not_nonempty_iff_eq_empty.mp h⟩)
        h_door i (Finset.notMem_erase i D) rfl (Finset.insert_erase hi_D).symm
  have h_da := h_cand_door (Or.inl rfl)
  have h_db := h_cand_door (Or.inr rfl)
  refine ⟨(cand a).1, (cand b).1, (cand a).2, (cand b).2, ?_,
    isRoom_of_Door h_da, isRoom_of_Door h_db, h_da, h_db, ?_⟩
  · intro h_eq
    dsimp [cand] at h_eq
    split_ifs at h_eq with hMa hMb hMb <;> dsimp at h_eq
    · have h_ma_not_mem := m_element_not_in_tau τ D a a b h_door h_nonempty ha_mem hb_mem hab h_eq_mini hMa (Or.inl rfl)
      have h_in : m_element τ D a h_nonempty hMa ∈ insert (m_element τ D b h_nonempty hMb) τ := by
        rw [← (Prod.mk.inj h_eq).1]; exact Finset.mem_insert_self _ _
      rcases Finset.mem_insert.mp h_in with h_m_eq | h_mem
      · have h_inter : m_element τ D b h_nonempty hMb ∈ M_set τ D a h_nonempty ∩ M_set τ D b h_nonempty :=
          ⟨h_m_eq ▸ (m_element_is_maximal τ D a h_nonempty hMa).1, (m_element_is_maximal τ D b h_nonempty hMb).1⟩
        exact Set.notMem_empty _ (h_disjoint ▸ h_inter)
      · exact h_ma_not_mem h_mem
    · exact Finset.notMem_erase b D ((Prod.mk.inj h_eq).2 ▸ hb_mem)
    · exact Finset.notMem_erase a D ((Prod.mk.inj h_eq).2.symm ▸ ha_mem)
    · exact Finset.notMem_erase a D ((Prod.mk.inj h_eq).2 ▸ Finset.mem_erase.mpr ⟨hab, ha_mem⟩)
  · intro σ C h_room h_door_rel
    suffices ∃ i, (i = a ∨ i = b) ∧ σ = (cand i).1 ∧ C = (cand i).2 by
      rcases this with ⟨i, rfl | rfl, h1, h2⟩ <;> [exact Or.inl ⟨h1, h2⟩; exact Or.inr ⟨h1, h2⟩]
    rcases h_door_rel with ⟨h0, _, x, hx_not_mem, rfl, rfl⟩ | ⟨h0, _, j, hj_not_mem, rfl, hc_eq⟩
    · obtain ⟨i, hi_mem, hi_nonempty, hi_max⟩ :=
        (sublemma_3_2 τ D x h_door h_nonempty hx_not_mem a b ha_mem hb_mem hab h_eq_mini).mp h0
      refine ⟨i, by simpa using hi_mem, ?_⟩
      dsimp [cand]; rw [dif_pos hi_nonempty, ← maximal_element_unique τ D i h_nonempty hi_nonempty x hi_max]
      exact ⟨rfl, rfl⟩
    · have hj_in_ab := odoor_index_in_pair τ D C a b j h_door h_nonempty ha_mem hb_mem hab h_eq_mini h0 h_room.2 hj_not_mem hc_eq
      have hj : j = a ∨ j = b := by simpa using hj_in_ab
      have hj_D : j ∈ D := by rcases hj with rfl | rfl <;> assumption
      have h_dom_C : IST.isDominant τ (D.erase j) := by simpa [hc_eq, Finset.erase_insert hj_not_mem] using h0
      obtain ⟨_, _, _, _, _, _, _, h_M_empty⟩ := (sublemma_3_1 τ D h_door h_nonempty j hj_D).mp h_dom_C
      have hj_not : ¬(M_set τ D j h_nonempty).Nonempty := Set.not_nonempty_iff_eq_empty.mpr h_M_empty
      refine ⟨j, hj, ?_⟩
      dsimp [cand]; rw [dif_neg hj_not]
      exact ⟨rfl, hc_eq ▸ (Finset.erase_insert hj_not_mem).symm⟩

end KeyLemma

noncomputable section Scarf

open Classical

variable (c : T → I) (σ : Finset T) (C : Finset I)

def isColorful : Prop := IST.isCell σ C ∧ σ.image c   = C

def isNearlyColorful : Prop := IST.isCell σ C ∧ (C \ σ.image c).card = 1

def isTypedNC (i : I) (σ : Finset T) (C : Finset I): Prop := IST.isCell σ C ∧ (C \ (σ.image c)) = {i}

variable {c σ C}

omit [Inhabited T] [DecidableEq T] in
lemma not_colorful_of_TypedNC (h1 : isTypedNC c i σ C) : ¬ IST.isColorful c σ C := by
  intro h
  have h_diff := h1.2
  rw [← h.2, Finset.sdiff_self] at h_diff
  exact Finset.singleton_ne_empty i h_diff.symm

omit [Inhabited T] [DecidableEq T] in
lemma NC_of_TNC (h1 : isTypedNC c i σ C) : isNearlyColorful c σ C :=
  ⟨h1.1, by rw [h1.2, Finset.card_singleton]⟩

lemma Finset.eq_of_mem_of_card_one {α : Type*} [DecidableEq α] {s : Finset α} {a : α} (h_mem : a ∈ s) (h_card : s.card = 1) : s = {a} :=
  Finset.eq_singleton_iff_unique_mem.mpr ⟨h_mem, fun y hy =>
    let ⟨b, hb⟩ := Finset.card_eq_one.mp h_card
    (Finset.eq_of_mem_singleton (hb ▸ hy)).trans (Finset.eq_of_mem_singleton (hb ▸ h_mem)).symm⟩

omit [Inhabited T] [DecidableEq T] in
lemma room_of_colorful (h : IST.isColorful c σ C) : IST.isRoom σ C :=
  ⟨h.1, le_antisymm (by rw [← h.2]; exact Finset.card_image_le) (card_le_of_domiant h.1)⟩

def pick_colorful_point (h : IST.isColorful c σ C): σ := Classical.choice (sigma_nonempty_of_room (room_of_colorful h)).to_subtype

omit [Inhabited T] in
lemma sdiff_image_subset_of_door (h : isDoorof τ D σ C) : C \ σ.image c ⊆ D \ τ.image c := by
  intro y hy; simp only [Finset.mem_sdiff] at hy ⊢
  rcases h with ⟨_, _, x, _, rfl, rfl⟩ | ⟨_, _, j, _, rfl, rfl⟩
  · rw [Finset.image_insert, Finset.mem_insert, not_or] at hy; exact ⟨hy.1, hy.2.2⟩
  · exact ⟨Finset.mem_insert_of_mem hy.1, hy.2⟩

omit [Inhabited T] in
lemma NC_or_C_of_door (h1 : isTypedNC c i τ D) (h2 : isDoorof τ D σ C) : isTypedNC c i σ C ∨ isColorful c σ C := by
  have h_sigma_cell : isCell σ C := by cases h2 <;> assumption
  rcases Finset.subset_singleton_iff.mp (h1.2 ▸ sdiff_image_subset_of_door h2) with h_empty | h_eq_i
  · exact Or.inr ⟨h_sigma_cell, (Finset.eq_of_subset_of_card_le (Finset.sdiff_eq_empty_iff_subset.mp h_empty)
      ((isRoom_of_Door h2).2 ▸ Finset.card_image_le)).symm⟩
  · exact Or.inl ⟨h_sigma_cell, h_eq_i⟩

omit [Inhabited T] in
lemma isTypedNC_of_isNearlyColorful_of_isDoorof_isTypedNC (h_nc : isNearlyColorful c τ D) (h_door : isDoorof τ D σ C) (h_room_typed : isTypedNC c i σ C) : isTypedNC c i τ D :=
  ⟨h_nc.1, Finset.eq_of_mem_of_card_one (sdiff_image_subset_of_door h_door (h_room_typed.2 ▸ Finset.mem_singleton_self i)) h_nc.2⟩

omit [Inhabited T] [DecidableEq T] in
lemma card_of_NCcell (h : isNearlyColorful c σ D) : #σ = #(image c σ) ∨ #σ = #(image c σ) + 1 := by
  rcases h with ⟨h_cell, h_nc_card⟩
  have h_card_le_D : σ.card ≤ D.card := card_le_of_domiant h_cell
  have h_D_card_eq := (Finset.card_sdiff_add_card_inter D (image c σ)).symm
  rw [h_nc_card] at h_D_card_eq
  have h_inter_le_img : (D ∩ image c σ).card ≤ (image c σ).card := card_le_card Finset.inter_subset_right
  have h_img_le_sigma : (image c σ).card ≤ σ.card := card_image_le
  omega

section ImageErase

variable {T I : Type*} [DecidableEq T] [DecidableEq I]

lemma image_erase_eq_erase_image_of_unique
  (σ : Finset T) (c : T → I) {z : T} (_ : z ∈ σ)
  (uniq : ∀ ⦃w⦄, w ∈ σ → c w = c z → w = z) :
  (σ.erase z).image c = (σ.image c).erase (c z) := by
  ext i; simp only [Finset.mem_image, Finset.mem_erase]
  exact ⟨fun ⟨w, ⟨hw_ne, hw_in⟩, hcw⟩ => ⟨fun h => hw_ne (uniq hw_in (hcw.trans h)), w, hw_in, hcw⟩,
    fun ⟨hi_ne, w, hw_in, hcw⟩ => ⟨w, ⟨fun h => hi_ne (hcw ▸ congrArg c h), hw_in⟩, hcw⟩⟩

end ImageErase
variable (c σ C) in
abbrev NCdoors := {(τ,D) | isNearlyColorful c τ D ∧ isDoorof τ D σ C }

omit [DecidableEq T] [Inhabited T] IST in
lemma image_erase_collision_preserves [DecidableEq T] (σ : Finset T) (c : T → I)
    (x y : T) (hx_in_σ : x ∈ σ) (hy_in_σ : y ∈ σ) (hxy_ne : x ≠ y) (hcxy_eq : c x = c y) :
    (σ.erase x).image c = σ.image c ∧ (σ.erase y).image c = σ.image c := by
  have aux {u v : T} (hu : u ∈ σ) (hv : v ∈ σ) (huv : u ≠ v) (hc : c u = c v) :
      (σ.erase u).image c = σ.image c := by
    ext z; simp only [Finset.mem_image, Finset.mem_erase]
    refine ⟨fun ⟨w, ⟨_, hw⟩, h⟩ => ⟨w, hw, h⟩, fun ⟨w, hw, h⟩ => ?_⟩
    by_cases hw_u : w = u
    · exact ⟨v, ⟨huv.symm, hv⟩, by rw [← hc, ← hw_u, h]⟩
    · exact ⟨w, ⟨hw_u, hw⟩, h⟩
  exact ⟨aux hx_in_σ hy_in_σ hxy_ne hcxy_eq, aux hy_in_σ hx_in_σ hxy_ne.symm hcxy_eq.symm⟩

omit [DecidableEq T] [Inhabited T] in
lemma collision_door_valid [DecidableEq T] (σ : Finset T) (C : Finset I) (_ : T → I)
    (x : T) (h_cell : isCell σ C) (hx_in_σ : x ∈ σ) (h_card_eq : C.card = σ.card) :
    isDoorof (σ.erase x) C σ C := by
  apply isDoorof.idoor h_cell
  · refine ⟨Dominant_of_subset σ (σ.erase x) C (Finset.erase_subset x σ) h_cell, ?_⟩
    rw [h_card_eq, Finset.card_erase_of_mem hx_in_σ]
    exact (Nat.sub_add_cancel (Finset.card_pos.mpr ⟨x, hx_in_σ⟩)).symm
  · exact Finset.notMem_erase x σ
  · exact Finset.insert_erase hx_in_σ
  · rfl

omit [DecidableEq T] [Inhabited T] IST in
lemma sdiff_erase_of_mem (s t : Finset I) {a : I} (ha : a ∈ s) :
    s \ (t.erase a) = insert a (s \ t) := by
  ext z; simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
  exact ⟨fun ⟨hz, h⟩ => by by_cases hza : z = a <;> [exact Or.inl hza; exact Or.inr ⟨hz, fun ht => h ⟨hza, ht⟩⟩],
    fun h => h.elim (fun h => ⟨h ▸ ha, by simp [h]⟩) (fun h => ⟨h.1, fun hp => h.2 hp.2⟩)⟩

omit [DecidableEq T] [Inhabited T] in
lemma doors_of_NCroom [DecidableEq T] (h_room : isRoom σ C) (h_nc : isNearlyColorful c σ C) :
  ∃ door1 door2, door1 ≠ door2 ∧ NCdoors c σ C = {door1, door2} := by
  have h_cases := card_of_NCcell h_nc
  have h_card_eq : C.card = σ.card := h_room.2
  have h_cell : isCell σ C := h_room.1
  let img := image c σ

  cases h_cases with
  | inl h_eq =>
    have h_inj_on_σ : Set.InjOn c ↑σ := (Finset.card_image_iff).mp h_eq.symm
    have h_img_C_card_1 : (img \ C).card = 1 := by
      have h_C_sdiff := Finset.card_sdiff_add_card_inter C img
      have h_img_sdiff := Finset.card_sdiff_add_card_inter img C
      rw [h_nc.2, h_card_eq, h_eq, Finset.inter_comm] at h_C_sdiff
      linarith [h_C_sdiff, h_img_sdiff]
    obtain ⟨c_y, h_img_C_eq⟩ := Finset.card_eq_one.mp h_img_C_card_1
    have h_c_y_in_img : c_y ∈ img := (Finset.mem_sdiff.mp (by rw [h_img_C_eq]; simp)).1
    have h_c_y_notin_C : c_y ∉ C := (Finset.mem_sdiff.mp (by rw [h_img_C_eq]; simp)).2
    obtain ⟨y, h_y_in_σ, rfl⟩ := Finset.mem_image.mp h_c_y_in_img
    have h_y_unique : ∀ ⦃z⦄, z ∈ σ → c z = c y → z = y :=
      fun _ hz hcz => h_inj_on_σ hz h_y_in_σ hcz
    let door1 := (σ.erase y, C)
    let door2 := (σ, insert (c y) C)
    refine ⟨door1, door2, fun h => Finset.erase_eq_self.mp (Prod.mk.inj h).1 h_y_in_σ, ?_⟩
    ext ⟨τ, D⟩; constructor
    · rintro ⟨h_nc_door, h_is_door⟩
      cases h_is_door with
      | idoor h0 h_door x hx_notin_τ h_insert_x h_D_eq_C =>
        subst h_D_eq_C
        have h_nc_card := h_nc_door.2
        have h_x_in_σ : x ∈ σ := by rw [← h_insert_x]; exact Finset.mem_insert_self x τ
        have h_τ_eq_erase : τ = σ.erase x := by rw [← Finset.erase_insert hx_notin_τ, h_insert_x]
        rw [h_τ_eq_erase, image_erase_eq_erase_image_of_unique σ c h_x_in_σ (fun w hw hcw => h_inj_on_σ hw h_x_in_σ hcw)] at h_nc_card
        by_cases h_x_eq_y : x = y
        · subst h_x_eq_y; simp [h_τ_eq_erase, door1]
        · have h_cx_in_D : c x ∈ D := by
            by_contra h_cx_notin_C
            have h_in : c x ∈ img \ D := Finset.mem_sdiff.mpr ⟨Finset.mem_image_of_mem c h_x_in_σ, h_cx_notin_C⟩
            rw [h_img_C_eq, Finset.mem_singleton] at h_in
            exact h_x_eq_y (h_y_unique h_x_in_σ h_in)
          rw [sdiff_erase_of_mem D img h_cx_in_D,
            Finset.card_insert_of_notMem (fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_image_of_mem c h_x_in_σ)),
            h_nc.2] at h_nc_card
          omega
      | odoor h0 h_door j hj_notin_C h_τ_eq_σ h_D_eq_insert =>
        subst h_τ_eq_σ h_D_eq_insert
        have h_nc_card := h_nc_door.2
        by_cases h_j_eq_cy : j = c y
        · subst h_j_eq_cy; simp; right; rfl
        · have h_j_notin_img : j ∉ img := fun h_j_in_img => h_j_eq_cy
            (Finset.mem_singleton.mp (h_img_C_eq ▸ Finset.mem_sdiff.mpr ⟨h_j_in_img, hj_notin_C⟩))
          rw [Finset.insert_sdiff_of_notMem _ h_j_notin_img,
            Finset.card_insert_of_notMem (fun h => hj_notin_C (Finset.mem_sdiff.mp h).1), h_nc.2] at h_nc_card
          omega
    · rintro (h_eq1 | h_eq2)
      · obtain ⟨rfl, rfl⟩ : τ = σ.erase y ∧ D = C := Prod.mk.inj h_eq1
        refine ⟨⟨Dominant_of_subset _ _ D (Finset.erase_subset y σ) h_cell, ?_⟩,
          collision_door_valid σ D c y h_cell h_y_in_σ h_card_eq⟩
        rw [image_erase_eq_erase_image_of_unique σ c h_y_in_σ h_y_unique]
        have h_eq_diff : D \ (image c σ).erase (c y) = D \ image c σ := by
          ext z; simp only [Finset.mem_sdiff, Finset.mem_erase]
          exact ⟨fun ⟨h1, h2⟩ => ⟨h1, fun h_in => h2 ⟨fun h_eq => h_c_y_notin_C (h_eq ▸ h1), h_in⟩⟩,
            fun ⟨h1, h2⟩ => ⟨h1, fun ⟨_, h_in⟩ => h2 h_in⟩⟩
        rw [h_eq_diff, h_nc.2]
      · obtain ⟨rfl, rfl⟩ : τ = σ ∧ D = insert (c y) C := Prod.mk.inj h_eq2
        have h_dom : isCell τ (insert (c y) C) := Dominant_of_supset τ C _ (Finset.subset_insert _ _) h_cell
        refine ⟨⟨h_dom, ?_⟩, isDoorof.odoor h_cell ⟨h_dom, by rw [Finset.card_insert_of_notMem h_c_y_notin_C, h_card_eq]⟩ (c y) h_c_y_notin_C rfl rfl⟩
        rw [Finset.insert_sdiff_of_mem _ (Finset.mem_image_of_mem c h_y_in_σ), h_nc.2]
  | inr h_inj =>
    obtain ⟨h_cell, h_missing_card⟩ := h_nc
    obtain ⟨x, y, h_x_in_σ, h_y_in_σ, h_cxy_eq, h_xy_ne⟩ := injOn_sdiff σ c h_inj
    have h_img_subset_C : image c σ ⊆ C := by
      have h_C_card_form := (card_sdiff_add_card_inter C (image c σ)).symm
      rw [h_missing_card, h_card_eq, h_inj] at h_C_card_form
      exact Finset.inter_eq_right.mp (Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by linarith))

    let τ₁ := σ.erase x
    let τ₂ := σ.erase y
    let door1 := (τ₁, C)
    let door2 := (τ₂, C)
    have h_door1_valid : isDoorof τ₁ C σ C := collision_door_valid σ C c x h_cell h_x_in_σ h_card_eq
    have h_door2_valid : isDoorof τ₂ C σ C := collision_door_valid σ C c y h_cell h_y_in_σ h_card_eq
    have h_imgs_preserved := image_erase_collision_preserves σ c x y h_x_in_σ h_y_in_σ h_xy_ne h_cxy_eq
    have h_door1_nc : isNearlyColorful c τ₁ C :=
      ⟨Dominant_of_subset σ τ₁ C (Finset.erase_subset x σ) h_cell, by rw [h_imgs_preserved.1, h_missing_card]⟩
    have h_door2_nc : isNearlyColorful c τ₂ C :=
      ⟨Dominant_of_subset σ τ₂ C (Finset.erase_subset y σ) h_cell, by rw [h_imgs_preserved.2, h_missing_card]⟩
    have h_doors_distinct : door1 ≠ door2 := fun h_eq =>
      Finset.notMem_erase y σ ((Prod.mk.inj h_eq).1 ▸ Finset.mem_erase.mpr ⟨h_xy_ne.symm, h_y_in_σ⟩ : y ∈ τ₂)

    refine ⟨door1, door2, h_doors_distinct, ?_⟩
    ext ⟨τ, D⟩; simp [NCdoors]; constructor
    · intro ⟨h_nc_τD, h_door_τD⟩
      cases h_door_τD with
      | idoor h_cell_σC h_door_τD z h_z_notin_τ h_insert_eq h_D_eq_C =>
        rw [h_D_eq_C]
        have h_τ_eq : τ = σ.erase z := by rw [← Finset.erase_insert h_z_notin_τ, h_insert_eq]
        rw [h_τ_eq]
        have h_z_in_σ : z ∈ σ := by rw [← h_insert_eq]; exact Finset.mem_insert_self z τ
        by_cases h_z_cases : z = x ∨ z = y
        · rcases h_z_cases with rfl | rfl <;> [exact Or.inl rfl; exact Or.inr rfl]
        · exfalso
          push_neg at h_z_cases
          have h_card_is_one : (C \ (σ.erase z).image c).card = 1 := by rw [← h_D_eq_C, ← h_τ_eq]; exact h_nc_τD.2
          have hinj_x : Set.InjOn c (σ.erase x : Set T) := Finset.card_image_iff.mp
            (by rw [h_imgs_preserved.1, Finset.card_erase_of_mem h_x_in_σ, h_inj]; omega)
          have hinj_y : Set.InjOn c (σ.erase y : Set T) := Finset.card_image_iff.mp
            (by rw [h_imgs_preserved.2, Finset.card_erase_of_mem h_y_in_σ, h_inj]; omega)
          have h_uniq_z : ∀ w ∈ σ, c w = c z → w = z := fun w hw h_c_eq => by
            by_cases hwx : w = x
            · exact hinj_y (Finset.mem_erase.mpr ⟨hwx ▸ h_xy_ne, hw⟩) (Finset.mem_erase.mpr ⟨h_z_cases.2, h_z_in_σ⟩) h_c_eq
            · exact hinj_x (Finset.mem_erase.mpr ⟨hwx, hw⟩) (Finset.mem_erase.mpr ⟨h_z_cases.1, h_z_in_σ⟩) h_c_eq
          rw [image_erase_eq_erase_image_of_unique σ c h_z_in_σ h_uniq_z,
            sdiff_erase_of_mem C (image c σ) (h_img_subset_C (mem_image_of_mem c h_z_in_σ)),
            Finset.card_insert_of_notMem (by simp [mem_image_of_mem c h_z_in_σ]),
            h_missing_card] at h_card_is_one
          omega
      | odoor h_cell_σC h_door_τD j h_j_notin_C h_τ_eq_σ h_D_eq =>
        exfalso
        have h_card_is_one := h_nc_τD.2
        have h_j_notin_img : j ∉ image c σ := fun h => h_j_notin_C (h_img_subset_C h)
        rw [h_D_eq, h_τ_eq_σ, Finset.insert_sdiff_of_notMem _ h_j_notin_img,
          Finset.card_insert_of_notMem (fun h => h_j_notin_C (Finset.mem_sdiff.mp h).1),
          h_missing_card] at h_card_is_one
        omega
    · rintro (h_eq | h_eq) <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_eq
      · exact ⟨h_door1_nc, h_door1_valid⟩
      · exact ⟨h_door2_nc, h_door2_valid⟩

variable [Fintype T] [Fintype I]

variable (c) in
abbrev colorful := Finset.filter (fun (x : Finset T× Finset I) =>  IST.isColorful c x.1 x.2) univ

variable (c) in
abbrev dbcountingset (i : I):= Finset.filter (fun x : (Finset T× Finset I) × (Finset T× Finset I) => isTypedNC c i x.1.1 x.1.2 ∧ isDoorof x.1.1 x.1.2 x.2.1 x.2.2) univ

variable (c)

lemma dbcount_outside_door_odd (i : I): Odd (filter (fun x => isOutsideDoor x.1.1 x.1.2) (dbcountingset c i)).card := by
  classical
  let x_max_i : T := @Finset.max' T (IST i) Finset.univ (Finset.univ_nonempty_iff.mpr ⟨default⟩)
  have h_out : isOutsideDoor (Finset.empty : Finset T) {i} := outsidedoor_singleton i
  have h_typed_nc : isTypedNC c i Finset.empty {i} := ⟨h_out.1.1, rfl⟩
  have h_door_rel : isDoorof Finset.empty {i} {x_max_i} {i} :=
    isDoorof.idoor (fun y => ⟨i, Finset.mem_singleton_self i, fun x hx =>
      Finset.eq_of_mem_singleton hx ▸ @Finset.le_max' T (IST i) Finset.univ y (Finset.mem_univ y)⟩)
      h_out.1 x_max_i (Finset.notMem_empty _) rfl rfl
  suffices h : filter (fun x => isOutsideDoor x.1.1 x.1.2) (dbcountingset c i) = {((Finset.empty, {i}), ({x_max_i}, {i}))} by simp [h]
  ext ⟨⟨τ, D⟩, ⟨σ, C⟩⟩
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  refine ⟨fun ⟨⟨h_typed, h_door⟩, h_is_door, h_empty⟩ => ?_, fun h_eq => ?_⟩
  · subst h_empty
    have h_D_eq : D = {i} := by
      have h_eq := h_typed.2
      change D \ image c ∅ = {i} at h_eq
      simpa using h_eq
    subst h_D_eq
    rcases h_door with ⟨h_cell_σC, _, x, _, h_insert_eq, rfl⟩ | ⟨h_cell_σC, _, j, h_j_notin, rfl, h_D_insert⟩
    · subst h_insert_eq
      obtain ⟨j_dom, hj_in, hj_dom⟩ := h_cell_σC x_max_i
      obtain rfl := Finset.eq_of_mem_singleton hj_in
      have h_x_eq : x = x_max_i := @le_antisymm T (IST j_dom).toPartialOrder x x_max_i
        (@Finset.le_max' T (IST j_dom) Finset.univ x (Finset.mem_univ x))
        (hj_dom x (Finset.mem_singleton_self x))
      subst h_x_eq; rfl
    · exact (Finset.not_nonempty_empty (sigma_nonempty_of_room
        (isRoom_of_Door (isDoorof.odoor h_cell_σC h_is_door j h_j_notin rfl h_D_insert)))).elim
  · obtain ⟨h1, h2⟩ := Prod.mk.inj h_eq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    exact ⟨⟨h_typed_nc, h_door_rel⟩, h_out⟩

omit [Inhabited T] in
lemma dbcount_internal_door_even (i : I) : Even (filter (fun x => ¬ isOutsideDoor x.1.1 x.1.2) (dbcountingset c i)).card := by
  let s := filter (fun x => ¬ isOutsideDoor x.1.1 x.1.2) (dbcountingset c i)
  let t := filter (fun (x : Finset T × Finset I) => IST.isInternalDoor x.1 x.2 ∧ isTypedNC c i x.1 x.2) univ
  have fs_in_t : ∀ x ∈ s, x.1 ∈ t := fun x hx => by
    simp only [s, t, mem_filter, mem_univ, true_and] at hx ⊢
    have h_door : isDoor x.1.1 x.1.2 := by cases hx.1.2 <;> assumption
    exact ⟨⟨h_door, Finset.nonempty_iff_ne_empty.mpr fun h_e => hx.2 ⟨h_door, h_e⟩⟩, hx.1.1⟩
  have fiber_size_two : ∀ y ∈ t, (filter (fun a => a.1 = y) s).card = 2 := fun y hy => by
    simp only [t, mem_filter, mem_univ, true_and] at hy
    obtain ⟨σ₁, σ₂, C₁, C₂, h_ne, _, _, h_door₁, h_door₂, h_unique⟩ :=
      internal_door_two_rooms y.1 y.2 hy.1
    have h_not_out : ¬ isOutsideDoor y.1 y.2 := fun h => Finset.nonempty_iff_ne_empty.mp hy.1.2 h.2
    have fiber_eq : filter (fun a => a.1 = y) s = {(y, (σ₁, C₁)), (y, (σ₂, C₂))} := by
      ext ⟨y', σ, C⟩
      simp only [s, mem_filter, mem_univ, true_and, mem_insert, mem_singleton, Prod.mk.injEq]
      refine ⟨fun ⟨⟨⟨_, h_door⟩, _⟩, rfl⟩ => ?_, ?_⟩
      · rcases h_unique σ C (isRoom_of_Door h_door) h_door with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
      · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;>
          [exact ⟨⟨⟨hy.2, h_door₁⟩, h_not_out⟩, rfl⟩; exact ⟨⟨⟨hy.2, h_door₂⟩, h_not_out⟩, rfl⟩]
    rw [fiber_eq, Finset.card_pair (fun h => h_ne (Prod.mk.inj h).2)]
  rw [Finset.card_eq_sum_card_fiberwise fs_in_t, Finset.sum_const_nat fiber_size_two]
  simp only [even_two, Even.mul_left]

omit [Inhabited T] in
lemma dbcount_NCroom (i : I) : Even (filter (fun x => ¬isColorful c x.2.1 x.2.2) (dbcountingset c i)).card := by
  let s := filter (fun x => ¬isColorful c x.2.1 x.2.2) (dbcountingset c i)
  let t := filter (fun (x : Finset T × Finset I) => IST.isRoom x.1 x.2 ∧ isTypedNC c i x.1 x.2) univ
  have fs_in_t : ∀ x ∈ s, x.2 ∈ t := fun x hx => by
    simp only [s, t, mem_filter, mem_univ, true_and] at hx ⊢
    exact ⟨isRoom_of_Door hx.1.2, (NC_or_C_of_door hx.1.1 hx.1.2).resolve_right hx.2⟩
  have fiber_sizetwo : ∀ y ∈ t, #(filter (fun a => a.2 = y) s) = 2 := fun ⟨σ, C⟩ hy => by
    simp only [t, mem_filter, mem_univ, true_and] at hy
    obtain ⟨door1, door2, h_ne, h_doors_eq⟩ := doors_of_NCroom hy.1 (NC_of_TNC hy.2)
    have h_filter_eq : filter (fun a => a.2 = (σ, C)) s = {(door1, (σ, C)), (door2, (σ, C))} := by
      ext ⟨d, σ', C'⟩
      simp only [s, mem_filter, mem_univ, true_and, mem_insert, mem_singleton, Prod.mk.injEq]
      refine ⟨fun ⟨⟨⟨h_typed, h_door⟩, _⟩, rfl, rfl⟩ => ?_, ?_⟩
      · have hd : d ∈ NCdoors c σ' C' := ⟨NC_of_TNC h_typed, h_door⟩
        rw [h_doors_eq] at hd; rcases hd with rfl | rfl <;> tauto
      · have aux {d' : Finset T × Finset I} (hd' : d' ∈ NCdoors c σ C) :
            isTypedNC c i d'.1 d'.2 ∧ isDoorof d'.1 d'.2 σ C :=
          ⟨isTypedNC_of_isNearlyColorful_of_isDoorof_isTypedNC hd'.1 hd'.2 hy.2, hd'.2⟩
        rintro (⟨hd, rfl, rfl⟩ | ⟨hd, rfl, rfl⟩)
        · exact ⟨⟨hd ▸ aux (h_doors_eq ▸ Set.mem_insert door1 {door2}), not_colorful_of_TypedNC hy.2⟩, rfl, rfl⟩
        · exact ⟨⟨hd ▸ aux (h_doors_eq ▸ Set.mem_insert_of_mem door1 (Set.mem_singleton door2)), not_colorful_of_TypedNC hy.2⟩, rfl, rfl⟩
    rw [h_filter_eq]; simp [h_ne]
  rw [Finset.card_eq_sum_card_fiberwise fs_in_t, Finset.sum_const_nat fiber_sizetwo]
  simp only [even_two, Even.mul_left]

lemma typed_colorful_room_odd (i : I) :
    Odd (Finset.filter (fun (x: (Finset T × Finset I) × Finset T × Finset I) => isColorful c x.2.1 x.2.2) (dbcountingset c i)).card := by
  have h1 := dbcount_outside_door_odd c i
  have h2 := dbcount_internal_door_even c i
  have h3 := dbcount_NCroom c i
  have hpart (p : ((Finset T × Finset I) × Finset T × Finset I) → Prop) [DecidablePred p] :
      (dbcountingset c i).card = (filter p (dbcountingset c i)).card + (filter (fun a => ¬p a) (dbcountingset c i)).card := by
    nth_rw 1 [← Finset.filter_union_filter_not_eq p (dbcountingset c i)]
    exact Finset.card_union_eq_card_add_card.2 (Finset.disjoint_filter_filter_not _ _ _)
  have h4 := (hpart (fun x => isOutsideDoor x.1.1 x.1.2)).symm.trans (hpart (fun x => isColorful c x.2.1 x.2.2))
  by_contra h0
  exact Nat.not_odd_iff_even.2 (Even.add (Nat.not_odd_iff_even.1 h0) h3) (h4 ▸ Even.odd_add h2 h1)

variable [Inhabited I]

theorem Scarf : (IST.colorful c).Nonempty := by
  obtain ⟨x, hx⟩ := Finset.card_pos.1 (Odd.pos (typed_colorful_room_odd c default))
  exact ⟨x.2, mem_filter.mpr ⟨mem_univ _, (Finset.mem_filter.1 hx).2⟩⟩

end Scarf

end IndexedLOrder
end

noncomputable section

abbrev Finset.toSet {α : Type*} (s : Finset α) : Set α := s
open IndexedLOrder

variable (n l : ℕ+) (i : Fin n)

abbrev TT := {x : Πₗ (_ : Fin n), Fin (l+1) | ∑ i, (x i : ℕ)  = l}


instance TT.inhabited : Inhabited (TT n l) where
  default :=
    ⟨ fun i => if i = 0 then Fin.last l else 0,  by
      simp only [TT, Set.mem_setOf_eq]
      rw [Finset.sum_eq_single (0 : Fin n)]
      · simp
      · intro b _ hb; simp [hb]
      · simp [Fin.val_last] ⟩

instance TT.funlike : FunLike (TT n l) (Fin n) (Fin (l+1)) where
  coe := fun a => a.1
  coe_injective := by simp

variable {n l} in
def TTtostdSimplex (x : TT n l) : stdSimplex ℝ (Fin n) := ⟨fun i => x i / l, by
  rw [stdSimplex]
  constructor
  · intro;simp only[Set.coe_setOf]
    apply div_nonneg <;> simp
  · simp only [Set.coe_setOf];
    rw [<-Finset.sum_div, div_eq_one_iff_eq]
    · exact_mod_cast x.2
    · exact Iff.mpr Nat.cast_ne_zero (PNat.ne_zero l)
  ⟩

instance TT.CoestdSimplex : CoeOut (TT n l) (stdSimplex ℝ (Fin n)) where
  coe := TTtostdSimplex

variable {n l} in
abbrev TT.Ilt ( x y : TT n l) :=
  toLex (x i, x)  < toLex (y i, y)

instance TT.IST : IsStrictTotalOrder (TT n l) (TT.Ilt i) where
  trichotomous := by
    intro a b hab hba
    have h : toLex (a i, a) = toLex (b i, b) :=
      le_antisymm (le_of_not_gt hba) (le_of_not_gt hab)
    exact congrArg Prod.snd (congrArg ofLex h)
  irrefl := by simp
  trans := by
    intro a b c
    rw [TT.Ilt]
    apply lt_trans

variable {n l} in
instance TT.ILO : IndexedLOrder (Fin n) (TT n l) where
  IST := fun i => linearOrderOfSTO (TT.Ilt i)

set_option quotPrecheck false
local notation  lhs "<[" i "]" rhs => (IndexedLOrder.IST i).lt lhs rhs
local notation  lhs "≤[" i "]" rhs => (IndexedLOrder.IST i).le lhs rhs

lemma TT.Ilt_def (a b : TT n l) : (a <[i] b) ↔ TT.Ilt i a b := Iff.rfl

lemma TT.Ilt_keyprop (a b : TT n l) (h : a i < b i) : a <[i] b := by
  rw [TT.Ilt_def, Ilt, Prod.Lex.lt_iff]; simp [h]

lemma size_bound_key (σ : Finset (TT n l)) (C : Finset (Fin n)) (h : TT.ILO.isDominant σ C)
    (h2 : σ.Nonempty) :
    l < ∑ k ∈ C, (σ.image (fun x => (x k : ℕ))).min' (by simp [Finset.image_nonempty, h2]) + C.card := by
  by_contra h_not
  push_neg at h_not
  let m := fun k => (σ.image (fun x => (x k : ℕ))).min' (by simp [Finset.image_nonempty, h2])
  have h_sum_plus_one : ∑ k ∈ C, (m k + 1) ≤ l := by
    rwa [Finset.sum_add_distrib, Finset.sum_const, nsmul_one]
  let M' : Fin n → ℕ := fun k => if k ∈ C then m k + 1 else 0
  let S := ∑ k, M' k
  have h_S_le_l : S ≤ l := by simpa [S, M'] using h_sum_plus_one
  have hM'_le_S (k : Fin n) : M' k ≤ S := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  let M_coords : Fin n → ℕ := fun k => if k = 0 then M' 0 + (l - S) else M' k
  have h_M_coords_sum : ∑ k, M_coords k = l := by
    have h_split (f : Fin n → ℕ) : ∑ k, f k = f 0 + ∑ k ∈ Finset.univ.erase 0, f k := by
      rw [← Finset.sum_insert (Finset.notMem_erase 0 Finset.univ), Finset.insert_erase (Finset.mem_univ 0)]
    have sum_eq : ∑ x ∈ Finset.univ.erase 0, M_coords x = ∑ x ∈ Finset.univ.erase 0, M' x :=
      Finset.sum_congr rfl fun k hk => if_neg (Finset.ne_of_mem_erase hk)
    have h1 := h_split M'
    have h0 := hM'_le_S 0
    rw [h_split M_coords, sum_eq]; dsimp [M_coords]; omega
  have h_M_coords_bound (k : Fin n) : M_coords k ≤ l := by
    have h0 := hM'_le_S 0
    have hk := hM'_le_S k
    dsimp [M_coords]; split_ifs <;> omega
  let M : TT n l := ⟨fun k => ⟨M_coords k, Nat.lt_succ_of_le (h_M_coords_bound k)⟩, by simp [h_M_coords_sum]⟩
  obtain ⟨k, hk_in_C, hk_dom⟩ := h M
  letI : LinearOrder (TT n l) := IndexedLOrder.IST k
  let x_min := σ.min' h2
  have h_min_coord : (x_min k : ℕ) = m k := by
    refine le_antisymm ?_ (Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.min'_mem σ h2)))
    refine Finset.le_min' _ _ _ fun y hy => ?_
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    by_contra! h_lt
    exact not_lt.mpr (Finset.min'_le σ x hx) (TT.Ilt_keyprop n l k x x_min h_lt)
  have h_lt : (x_min k : ℕ) < (M k : ℕ) := by
    rw [h_min_coord]; change m k < M_coords k
    by_cases h0 : k = 0
    · subst h0; simp [M_coords, M', hk_in_C]; omega
    · simp [M_coords, M', h0, hk_in_C]
  exact not_lt.mpr (hk_dom x_min (Finset.min'_mem σ h2)) (TT.Ilt_keyprop n l k x_min M h_lt)

lemma size_bound_aux {σ : Finset (TT n l)} {C : Finset (Fin n)} (h : TT.ILO.isDominant σ C)
    (hσ : σ.Nonempty) {z : TT n l} (hz : z ∈ σ) (i : Fin n) :
    let m k := (σ.image (fun w => (w k : ℕ))).min' (by simp [Finset.image_nonempty, hσ])
    let m' := if i ∈ C then m i else 0
    m' ≤ (z i : ℕ) ∧ (z i : ℕ) - m' < C.card := by
  intro m m'
  have h_m_le (w : TT n l) (hw : w ∈ σ) (k : Fin n) : m k ≤ (w k : ℕ) :=
    Finset.min'_le _ _ (Finset.mem_image_of_mem (fun u => (u k : ℕ)) hw)
  have h_sum_z_le_l : ∑ k ∈ C, (z k : ℕ) ≤ l :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C) (by simp)).trans_eq z.2
  have h_sum_m_le_z : ∑ k ∈ C, m k ≤ ∑ k ∈ C, (z k : ℕ) :=
    Finset.sum_le_sum fun k _ => h_m_le z hz k
  have h_le_l_sub_sum : (l : ℕ) - ∑ k ∈ C, m k < C.card := by
    rw [Nat.sub_lt_iff_lt_add (h_sum_m_le_z.trans h_sum_z_le_l), add_comm]
    exact size_bound_key n l σ C h hσ
  by_cases hi : i ∈ C
  · simp only [m', hi, ↓reduceIte]
    refine ⟨h_m_le z hz i, lt_of_le_of_lt ?_ h_le_l_sub_sum⟩
    calc (z i : ℕ) - m i
      _ ≤ ∑ k ∈ C, ((z k : ℕ) - m k) := Finset.single_le_sum (fun k _ => Nat.zero_le ((z k : ℕ) - m k)) hi
      _ = (∑ k ∈ C, (z k : ℕ)) - ∑ k ∈ C, m k := Finset.sum_tsub_distrib C fun k _ => h_m_le z hz k
      _ ≤ l - ∑ k ∈ C, m k := Nat.sub_le_sub_right h_sum_z_le_l _
  · simp only [m', hi, ↓reduceIte, Nat.zero_le, Nat.sub_zero, true_and]
    have h_sum_ins : (z i : ℕ) + ∑ k ∈ C, (z k : ℕ) ≤ l := by
      rw [← Finset.sum_insert (f := fun k => (z k : ℕ)) hi]
      exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by simp)).trans_eq z.2
    exact lt_of_le_of_lt ((Nat.le_sub_of_add_le h_sum_ins).trans (Nat.sub_le_sub_left h_sum_m_le_z l)) h_le_l_sub_sum

theorem size_bound_in (σ : Finset (TT n l)) (C : Finset (Fin n)) (h : TT.ILO.isDominant σ C) :
    ∀ x ∈ σ, ∀ y ∈ σ, ∀ i : Fin n, abs ((x i : ℤ) - (y i : ℤ)) < 2 * (n + 1) := by
  intro x hx y hy i
  have hσ : σ.Nonempty := ⟨x, hx⟩
  obtain ⟨hx1, hx2⟩ := size_bound_aux n l h hσ hx i
  obtain ⟨hy1, hy2⟩ := size_bound_aux n l h hσ hy i
  have h_card_le_n : C.card ≤ n := (Finset.card_le_card (Finset.subset_univ C)).trans_eq (by simp)
  rw [abs_lt]; constructor <;> omega

theorem size_bound_out (σ : Finset (TT n l)) (C : Finset (Fin n)) (h : TT.ILO.isDominant σ C) :
    ∀ x ∈ σ, ∀ i ∉ C, (x i : ℤ) < n + 1 := by
  intro x hx i hi_not_C
  have h2 := (size_bound_aux n l h ⟨x, hx⟩ hx i).2
  simp only [hi_not_C, ↓reduceIte, Nat.sub_zero] at h2
  have h_card_le_n : C.card ≤ n := (Finset.card_le_card (Finset.subset_univ C)).trans_eq (by simp)
  omega

section Brouwer

variable (f : stdSimplex ℝ (Fin n) → stdSimplex ℝ (Fin n))

variable {n l}

instance stdSimplex.upidx (x y : stdSimplex ℝ (Fin n)) : Nonempty { i | x.1 i ≤ y.1 i} := by
  by_contra h
  have sum_lt : Finset.sum Finset.univ y.1 < Finset.sum Finset.univ x.1 :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ =>
      lt_of_not_ge fun hle => h ⟨⟨i, hle⟩⟩
  rw [x.2.2, y.2.2] at sum_lt
  exact lt_irrefl 1 sum_lt

noncomputable def stdSimplex.pick (x y : stdSimplex ℝ (Fin n)) := Classical.choice $ stdSimplex.upidx x y

def Fcolor (x : TT n l) : Fin n := stdSimplex.pick x (f x)

def room_seq (l' : ℕ) :=
  let l : PNat := ⟨l'+1,Nat.zero_lt_succ _⟩
  Classical.choice (TT.ILO.Scarf (@Fcolor n l f)).to_subtype

def room_point_seq (l' : ℕ) := pick_colorful_point
  (Finset.mem_filter.1 (room_seq f l').2).2 |>.1

section finiteness

def mk_subseq (f : ℕ → ℕ) (h : ∀ n, n < f n) : ℕ → ℕ
  | 0 => f 0
  | n+1 => f (mk_subseq f h n)

theorem exists_subseq_constant_of_finite_image {s : Finset α} (e : ℕ → α) (he : ∀ n, e n ∈ s) :
    ∃ a ∈ s, ∃ g : ℕ ↪o ℕ, (∀ n, e (g n) = a) := by
  have imgs_nonempty : (Finset.filter (fun a => ¬Set.Finite (e ⁻¹' {a})) s).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have preimages_all_finite : ∀ a ∈ s, Set.Finite (e ⁻¹' {a}) := fun a ha =>
      by_contra fun hnf => Finset.ne_empty_of_mem (Finset.mem_filter.mpr ⟨ha, hnf⟩) h
    have univ_eq : (Set.univ : Set ℕ) = ⋃ a ∈ s, e ⁻¹' {a} := by ext n; simp [he n]
    exact Set.infinite_univ (univ_eq ▸ Set.Finite.biUnion s.finite_toSet preimages_all_finite)
  obtain ⟨a, ha_filter⟩ := imgs_nonempty
  obtain ⟨a_in_s, a_inf⟩ := Finset.mem_filter.1 ha_filter
  have h_exists_larger : ∀ k : ℕ, ∃ m ∈ e ⁻¹' {a}, k < m := fun k => by
    by_contra! h_not
    exact a_inf ((Set.finite_le_nat k).subset h_not)
  choose fn hfn using h_exists_larger
  let g := mk_subseq fn (fun n => (hfn n).2)
  have hg_in : ∀ n, g n ∈ e ⁻¹' {a} := fun n => by induction n <;> exact (hfn _).1
  have hg_strict : StrictMono g := fun m n hmn => by
    induction hmn with
    | refl => exact (hfn (g m)).2
    | step _ ih => exact lt_trans ih (hfn _).2
  exact ⟨a, a_in_s, OrderEmbedding.ofStrictMono g hg_strict, hg_in⟩

end finiteness

open Topology Filter

lemma tendsto_cast_add_one_atTop {g : ℕ → ℕ} (hg : StrictMono g) :
    Tendsto (fun k => (g k : ℝ) + 1) atTop atTop :=
  Tendsto.atTop_add (tendsto_natCast_atTop_atTop.comp hg.tendsto_atTop) tendsto_const_nhds

theorem Brouwer (hf : Continuous f) : ∃ x, f x = x := by
  obtain ⟨C, _, g, h_const⟩ := exists_subseq_constant_of_finite_image (s := Finset.univ)
    (fun x => (room_seq f x).1.2) (by simp)
  obtain ⟨z, _, φ, φ_mono, h_tendsto⟩ := isCompact_univ.tendsto_subseq
    (fun l' : ℕ => Set.mem_univ (room_point_seq f (g l') : stdSimplex ℝ (Fin n)))
  let l k := g (φ k)
  have hl_mono : StrictMono l := g.strictMono.comp φ_mono
  have h_cont (i : Fin n) : Continuous (fun x : stdSimplex ℝ (Fin n) => x.1 i) :=
    (continuous_apply i).comp continuous_subtype_val
  have h_diam : Tendsto (fun k => Metric.diam (((room_seq f (l k)).1.1.image TTtostdSimplex).toSet : Set (stdSimplex ℝ (Fin n)))) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ((tendsto_const_nhds (x := 2 * ((n : ℝ) + 1))).div_atTop (tendsto_cast_add_one_atTop hl_mono))
      (fun _ => Metric.diam_nonneg) fun k => ?_
    let l_pnat : PNat := ⟨l k + 1, Nat.succ_pos _⟩
    let rs := room_seq f (l k)
    apply Metric.diam_le_of_forall_dist_le (by positivity)
    intro x hx y hy
    rcases Finset.mem_image.mp hx with ⟨x', hx', rfl⟩
    rcases Finset.mem_image.mp hy with ⟨y', hy', rfl⟩
    change ‖((TTtostdSimplex x').1 : Fin n → ℝ) - (TTtostdSimplex y').1‖ ≤ _
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    have h_bound_int := size_bound_in n l_pnat rs.1.1 rs.1.2 (Finset.mem_filter.mp rs.2).2.1 x' hx' y' hy' i
    simp only [Pi.sub_apply, Real.norm_eq_abs, TTtostdSimplex, ← sub_div, abs_div]
    have h_eq : (l_pnat : ℝ) = l k + 1 := by simp [l_pnat, PNat.mk_coe]
    rw [abs_of_pos (by positivity : (0 : ℝ) < l_pnat), h_eq,
      div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < l k + 1)]
    exact le_of_lt (by exact_mod_cast h_bound_int)
  have h_le : ∀ idx ∈ Finset.univ, z.1 idx ≤ (f z).1 idx := by
    intro idx _
    by_cases h_idx_C : idx ∈ C
    · have h_exists_point : ∀ l', ∃ y ∈ (room_seq f (g l')).1.1,
          (let l_pnat : PNat := ⟨g l' + 1, by simp⟩; @Fcolor n l_pnat f y) = idx := fun l' => by
        let l_pnat : PNat := ⟨g l' + 1, by simp⟩
        let rs := room_seq f (g l')
        have h_image_eq : rs.1.1.image (@Fcolor n l_pnat f) = rs.1.2 := (Finset.mem_filter.mp rs.2).2.2
        exact Finset.mem_image.mp (h_image_eq.symm ▸ h_const l' ▸ h_idx_C)
      let y_seq := fun l' => TTtostdSimplex (h_exists_point l').choose
      have y_seq_spec := fun l' => (h_exists_point l').choose_spec
      have h_ineq (l' : ℕ) : (f (y_seq l')).1 idx ≥ (y_seq l').1 idx := by
        let l_pnat : PNat := ⟨g l' + 1, by simp⟩
        let pt := (h_exists_point l').choose
        have h_col : (stdSimplex.pick (pt : stdSimplex ℝ (Fin n)) (f pt)).1 = idx := (y_seq_spec l').2
        exact h_col ▸ (stdSimplex.pick (pt : stdSimplex ℝ (Fin n)) (f pt)).2
      have y_seq_φ_converges_to_z : Filter.Tendsto (y_seq ∘ φ) Filter.atTop (𝓝 z) := by
        have h_bound (k : ℕ) : dist (y_seq (φ k)) ((room_point_seq f (l k) : stdSimplex ℝ (Fin n))) ≤
            Metric.diam (((room_seq f (l k)).1.1.image TTtostdSimplex).toSet) :=
          Metric.dist_le_diam_of_mem (Set.Finite.isBounded (Finset.finite_toSet _))
            (Finset.mem_image_of_mem TTtostdSimplex (y_seq_spec (φ k)).1)
            (Finset.mem_image_of_mem TTtostdSimplex (pick_colorful_point ((Finset.mem_filter.1 (room_seq f (l k)).2).2)).2)
        have h_dist := tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_diam
          (Eventually.of_forall fun _ => dist_nonneg) (Eventually.of_forall h_bound)
        rw [Metric.tendsto_nhds]
        intro ε hε
        refine (((Metric.tendsto_nhds.1 h_tendsto) (ε / 2) (half_pos hε)).and
          ((Metric.tendsto_nhds.1 h_dist) (ε / 2) (half_pos hε))).mono fun k ⟨hk1, hk2⟩ => ?_
        calc dist (y_seq (φ k)) z
          _ ≤ dist (y_seq (φ k)) (room_point_seq f (l k)) + dist (room_point_seq f (l k) : stdSimplex ℝ (Fin n)) z := dist_triangle _ _ _
          _ < ε / 2 + ε / 2 := add_lt_add (by simpa [Real.dist_eq, abs_of_nonneg dist_nonneg] using hk2) hk1
          _ = ε := add_halves ε
      exact le_of_tendsto_of_tendsto
        ((h_cont idx).continuousAt.tendsto.comp y_seq_φ_converges_to_z)
        ((h_cont idx).continuousAt.tendsto.comp (hf.continuousAt.tendsto.comp y_seq_φ_converges_to_z))
        (Eventually.of_forall fun l' => h_ineq (φ l'))
    · have h_zero : Tendsto (fun k => ((room_point_seq f (l k)) : stdSimplex ℝ (Fin n)).1 idx) atTop (𝓝 0) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
          ((tendsto_const_nhds (x := (n : ℝ) + 1)).div_atTop (tendsto_cast_add_one_atTop hl_mono))
          (fun k => ((room_point_seq f (l k)) : stdSimplex ℝ (Fin n)).2.1 idx) fun k => ?_
        let l_pnat : PNat := ⟨l k + 1, Nat.succ_pos _⟩
        let rs := room_seq f (l k)
        let colorful_proof := (Finset.mem_filter.mp rs.2).2
        have h_bound := size_bound_out n l_pnat rs.1.1 rs.1.2 colorful_proof.1
          (room_point_seq f (l k)) (pick_colorful_point colorful_proof).2 idx (h_const (φ k) ▸ h_idx_C)
        simp only [TTtostdSimplex, Subtype.coe_mk]
        have h_eq : (↑l_pnat : ℝ) = ↑(l k) + 1 := by simp [l_pnat, PNat.mk_coe]
        rw [h_eq, div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < ↑(l k) + 1)]
        exact le_of_lt (by exact_mod_cast Nat.lt_succ_of_le (Int.ofNat_le.mp (Int.le_of_lt_add_one h_bound)))
      rw [tendsto_nhds_unique ((h_cont idx).continuousAt.tendsto.comp h_tendsto) h_zero]
      exact (f z).2.1 idx
  refine ⟨z, Subtype.ext (funext fun i => ?_)⟩
  exact ((Finset.sum_eq_sum_iff_of_le h_le).mp (z.2.2.trans (f z).2.2.symm) i (Finset.mem_univ i)).symm

end Brouwer
