import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ext
import Mathlib.Tactic

/-
Copyright (c) 2025 Math_XMUM. All rights reserved.
Released under the MIT license; see THIRD_PARTY_LICENSE.txt.

Ported from math-xmum/Brouwer, commit c938f0f2b355adc9f07666c1c2c4002100406923 (2025-11-23),
Gametheory/Scarf.lean, to the project's pinned mathlib v4.19.0.
Upstream: https://github.com/math-xmum/Brouwer
Adapted to the pinned Lean/mathlib version, with proof simplifications.
-/
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Convert
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Cases



section fiberlemma

open Finset

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

lemma even_card_of_two_fibres (s : Finset α) (f : α → β)
    (h : ∀ a ∈ s, #(s.filter (fun x => f x = f a)) = 2) : Even #s := by
  have hf : ∀ y ∈ s.image f, #(s.filter (fun x => f x = y)) = 2 := by continuity
  rw [card_eq_sum_card_image f s, Finset.sum_const_nat hf]
  exact even_two.mul_left _

end fiberlemma

open Classical
open Finset

variable {T : Type*}
variable {I : Type*}

class IndexedLOrder (I T :Type*) where
  IST : I → LinearOrder T

instance : CoeFun (IndexedLOrder I T) (fun _ => I → LinearOrder T) := ⟨fun a => a.IST⟩

variable [IST : IndexedLOrder I T]

set_option quotPrecheck false

namespace IndexedLOrder

scoped notation  lhs "<[" i "]" rhs => (IndexedLOrder.IST i).lt lhs rhs
scoped notation  lhs "≤[" i "]" rhs => (IndexedLOrder.IST i).le lhs rhs

noncomputable local instance : DecidableEq T := fun _ _ => Classical.propDecidable _
variable (σ : Finset T) (C : Finset I)

def isDominant  :=
  ∀ y, ∃ i ∈ C, ∀ x ∈ σ,  y ≤[i] x

variable {σ C} in
lemma Nonempty_of_Dominant [Inhabited T] (h : IST.isDominant σ C) : C.Nonempty := by
  obtain ⟨j,hj⟩ := h default
  exact ⟨j, hj.1⟩

lemma Dominant_of_subset (σ τ : Finset T) (C : Finset I) :
  τ ⊆ σ → isDominant σ C  → isDominant τ C := by
  intro hs hd y
  obtain ⟨i, hi, h⟩ := hd y
  exact ⟨i, hi, fun x hx => h x (hs hx)⟩

lemma Dominant_of_supset (σ : Finset T) (C D: Finset I) :
  C ⊆ D → isDominant σ C  → isDominant σ D := by
  intro hs hd y
  obtain ⟨i, hi, h⟩ := hd y
  exact ⟨i, hs hi, h⟩

abbrev mini {σ : Finset T} (h2 : σ.Nonempty) (i : I) : T := @Finset.min' _ (IST i) _ h2

lemma keylemma_of_dominant {σ : Finset T} {C: Finset I} (h1 : IST.isDominant σ C) (h2: σ.Nonempty): σ  = C.image (mini h2)  :=
  by
  ext a
  constructor
  · intro ha
    obtain ⟨i,hi,h⟩ := h1 a
    letI := IST i
    exact Finset.mem_image.mpr ⟨i,hi,
      le_antisymm (Finset.min'_le σ a ha) (h _ (Finset.min'_mem σ h2))⟩
  · intro h
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
    letI := IST i
    exact Finset.min'_mem σ h2


lemma card_le_of_domiant {σ : Finset T} {C: Finset I} (h1 : IST.isDominant σ C) : σ.card  ≤  C.card  := by
  by_cases h2 : σ.Nonempty
  · rw [keylemma_of_dominant h1 h2]
    apply Finset.card_image_le
  · aesop

abbrev isCell  := isDominant σ C

abbrev isRoom :=  isCell σ C ∧ C.card = σ.card

lemma sigma_nonempty_of_room [Inhabited T] {σ : Finset T} {C : Finset I} (h : isRoom σ C) : σ.Nonempty  := by
  simpa only [← Finset.card_pos,h.2] using Nonempty_of_Dominant h.1

abbrev isDoor  :=  isCell σ C ∧ C.card = σ.card + 1

inductive isDoorof (τ : Finset T) (D : Finset I) (σ : Finset T) (C : Finset I) : Prop
  | idoor (h0 : isCell σ C) (h1 : isDoor τ D) (x :T) (h1 : x ∉ τ) (h2 : insert x τ = σ) (h3 : D = C)
  | odoor (h0 : isCell σ C) (h1 : isDoor τ D) (j :I) (h1 : j ∉ C) (h2 : τ = σ) (h3 : D = insert j C)

variable {σ C} in
lemma isRoom_of_Door (h1 : isDoorof τ D σ C) : IST.isRoom σ C := by
  cases h1 <;> grind

variable (τ D) in
abbrev isOutsideDoor := IST.isDoor τ D ∧ τ = ∅

variable (τ D) in
abbrev isInternalDoor := IST.isDoor τ D ∧ τ.Nonempty

lemma outsidedoor_singleton (i : I) : IST.isOutsideDoor ∅ {i} := by
  refine ⟨⟨?_, by simp⟩, rfl⟩
  exact fun _ => ⟨i, by simp, by simp⟩





section KeyLemma
variable (τ : Finset T) (D : Finset I)

def M_set  (i : I) (h_nonempty : τ.Nonempty) : Set T :=
  {y : T | ∀ k ∈ D, k ≠ i → mini h_nonempty k <[k] y}

def is_maximal_in_M_set  (i : I) (h_nonempty : τ.Nonempty) (x : T) : Prop :=
  x ∈ M_set τ D i h_nonempty ∧ ∀ y ∈ M_set τ D i h_nonempty, y ≤[i] x

noncomputable def m_element [Fintype T]  (i : I) (h_nonempty : τ.Nonempty)
    (h : (M_set τ D i h_nonempty).Nonempty) : T :=
  @Finset.max' _ (IST i) (M_set τ D i h_nonempty).toFinset (Set.toFinset_nonempty.mpr h)

theorem m_element_is_maximal [Fintype T]  (i : I) (h_nonempty : τ.Nonempty)
    (h : (M_set τ D i h_nonempty).Nonempty) :
    is_maximal_in_M_set τ D i h_nonempty (m_element τ D i h_nonempty h) := by
  letI := IST i
  exact ⟨Set.mem_toFinset.mp (Finset.max'_mem _ _),
    fun y hy => Finset.le_max' _ y (Set.mem_toFinset.mpr hy)⟩


lemma dominant_erase_iff  (i : I)
    (ht : τ.Nonempty) :
    IST.isDominant τ (D.erase i) ↔ M_set τ D i ht = ∅ := by
  have hn (k : I) (y : T) :
      (¬ mini ht k <[k] y) ↔ ∀ x ∈ τ, y ≤[k] x := by
    letI := IST k
    simp [mini]
  simp only [isDominant, M_set, Set.eq_empty_iff_forall_notMem,
    Set.mem_setOf_eq, Finset.mem_erase, not_forall, hn, exists_prop]
  exact forall_congr' fun y => exists_congr fun k => by tauto



lemma sublemma_3_2 [Fintype T]  (x : T)
    (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty) (h_not_mem : x ∉ τ)
    (a b : I) (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b)
    (h_eq : mini h_nonempty a = mini h_nonempty b) :
    IST.isDominant (insert x τ) D ↔
    (∃ i ∈ ({a, b} : Finset I), (M_set τ D i h_nonempty).Nonempty ∧
     is_maximal_in_M_set τ D i h_nonempty x) := by
  constructor
  · intro hd
    let hs := Finset.insert_nonempty x τ
    have he := (keylemma_of_dominant hd hs).symm
    obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp (show x ∈ D.image (mini hs) by aesop)
    have hinj : Set.InjOn (mini hs) (D : Set I) :=
      Finset.injOn_of_card_image_eq (by grind)
    have hcases (k : I) : mini hs k = x ∨ mini hs k = mini h_nonempty k := by
      letI := IST k
      rcases Finset.mem_insert.mp (Finset.min'_mem _ hs) with he | he
      · exact Or.inl he
      · right
        exact le_antisymm
          (Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.min'_mem _ h_nonempty)))
          (Finset.min'_le _ _ he)
    have hfix (k : I) (hk : k ∈ D) (hki : k ≠ i) :=
      (hcases k).resolve_left (fun hh => hki (hinj hk hi (hh.trans hix.symm)))
    have hxM : x ∈ M_set τ D i h_nonempty := by
      intro k hk hki
      letI := IST k
      have hle : mini hs k ≤[k] x := Finset.min'_le _ x (Finset.mem_insert_self x τ)
      rw [hfix k hk hki] at hle
      exact lt_of_le_of_ne hle (fun hh => h_not_mem (hh ▸ Finset.min'_mem τ h_nonempty))
    have hiab : i ∈ ({a,b} : Finset I) := by
      by_contra hn
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      exact hab (hinj ha hb (by grind))
    refine ⟨i, hiab, ⟨x, hxM⟩, hxM, ?_⟩
    intro y hyM
    obtain ⟨k, hk, hh⟩ := hd y
    letI := IST k
    by_cases hki : k = i
    · subst k
      exact hh x (Finset.mem_insert_self x τ)
    · exact (not_lt_of_ge
        (hh _ (Finset.mem_insert_of_mem (Finset.min'_mem τ h_nonempty))) (hyM k hk hki)).elim
  · rintro ⟨i, hi, _, hxM, hmax⟩ y
    have hiD : i ∈ D := by grind
    by_cases hyM : y ∈ M_set τ D i h_nonempty
    · obtain ⟨k, hk, hh⟩ := h_door.1 y
      letI := IST k
      have hki : k = i := by
        by_contra hn
        exact not_lt_of_ge
          (hh _ (Finset.min'_mem τ h_nonempty)) (hyM k hk hn)
      subst k
      refine ⟨i, hiD, ?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hmax y hyM
      · exact hh z hz
    · simp only [M_set, Set.mem_setOf_eq] at hyM
      push_neg at hyM
      obtain ⟨k, hk, hki, hh⟩ := hyM
      letI := IST k
      have hle := hh
      refine ⟨k, hk, ?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact le_trans hle
          (le_of_lt (hxM k hk hki))
      · exact le_trans hle (Finset.min'_le τ z hz)














theorem internal_door_two_rooms [Fintype T] 
    (h_int_door : IST.isInternalDoor τ D) :
    ∃ R₁ R₂ : Finset T × Finset I, R₁ ≠ R₂ ∧
      isDoorof τ D R₁.1 R₁.2 ∧ isDoorof τ D R₂.1 R₂.2 ∧
      ∀ R, isDoorof τ D R.1 R.2 → R = R₁ ∨ R = R₂ := by

  obtain ⟨hd, ht⟩ := h_int_door
  have hc : D.card = (D.image (mini ht)).card + 1 := by grind [keylemma_of_dominant]
  obtain ⟨a,ha,b,hb,hab,he⟩ := Finset.exists_ne_map_eq_of_card_image_lt
    (show #(D.image (mini ht)) < #D by omega)
  let M := fun i => M_set τ D i ht
  let R : I → Finset T × Finset I := fun i =>
    if h : (M i).Nonempty then (insert (m_element τ D i ht h) τ, D)
    else (τ, D.erase i)
  have hn i (hM : (M i).Nonempty) (hi : i = a ∨ i = b) :
      m_element τ D i ht hM ∉ τ := by
    let m := m_element τ D i ht hM
    have hm := (m_element_is_maximal τ D i ht hM).1
    intro h
    have hmmini : m ∈ D.image (mini ht) := by grind [keylemma_of_dominant]
    obtain ⟨k,hk,hek⟩ := Finset.mem_image.mp hmmini
    by_cases hki : k = i
    · subst k
      rcases hi with rfl | rfl
      · have hlt := hm b hb hab.symm
        rw [← he, hek] at hlt
        letI := IST b
        exact lt_irrefl _ hlt
      · have hlt := hm a ha hab
        rw [he, hek] at hlt
        letI := IST a
        exact lt_irrefl _ hlt
    · have hlt := hm k hk hki
      rw [hek] at hlt
      letI := IST k
      exact lt_irrefl _ hlt
  have hr i (hi : i ∈ ({a,b} : Finset I)) :
      isDoorof τ D (R i).1 (R i).2 := by
    have hi'  := by simpa using hi
    have hiD : i ∈ D := by grind
    by_cases hm : (M i).Nonempty
    · have hnot := hn i hm hi'
      have hdom := (sublemma_3_2 τ D _ hd ht hnot a b ha hb hab he).mpr
        ⟨i, hi, hm, m_element_is_maximal τ D i ht hm⟩
      dsimp only [R]; rw [dif_pos hm]
      exact isDoorof.idoor hdom hd _ hnot rfl rfl
    · have hdom := (dominant_erase_iff τ D i ht).mpr
        (Set.not_nonempty_iff_eq_empty.mp hm)
      dsimp only [R]; rw [dif_neg hm]
      exact isDoorof.odoor hdom hd i (notMem_erase i D) rfl (insert_erase hiD).symm
  have hex σ C (hrel : isDoorof τ D σ C) :
      ∃ i ∈ ({a,b} : Finset I), (σ,C) = R i := by
    cases hrel with
    | idoor hdom _ x hx hσ hC =>
      subst σ C
      obtain ⟨i,hi,hm,hmax⟩ := (sublemma_3_2 τ D x hd ht hx a b ha hb hab he).mp hdom
      refine ⟨i,hi,?_⟩
      have hxmax : x = m_element τ D i ht hm := by
        have h := m_element_is_maximal τ D i ht hm
        letI := IST i
        exact le_antisymm (h.2 x hmax.1) (hmax.2 _ h.1)
      simp only [R,M,dif_pos hm,hxmax]
    | odoor hdom _ j hj hσ hD =>
      subst σ
      have hi : j ∈ ({a,b} : Finset I) := by
        have hinj : Set.InjOn (mini ht) (C : Set I) :=
          Finset.injOn_of_card_image_eq (by grind [keylemma_of_dominant])
        by_contra hn
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
        have haC : a ∈ C := by grind
        have hbC : b ∈ C := by grind
        exact hab (hinj haC hbC he)
      have hC : C = D.erase j := by grind
      have hempty := (dominant_erase_iff τ D j ht).mp (hC ▸ hdom)
      refine ⟨j,hi,?_⟩
      simp only [R, show ¬(M j).Nonempty from Set.not_nonempty_iff_eq_empty.mpr hempty,
        ↓reduceDIte, hC]
  have hne : R a ≠ R b := by
    intro h
    by_cases hma : (M a).Nonempty <;> by_cases hmb : (M b).Nonempty
    · have hfst := congrArg Prod.fst h
      simp only [R, dif_pos hma, dif_pos hmb] at hfst
      have heq :=
        (mem_insert.mp (hfst ▸ mem_insert_self _ _)).resolve_right (hn a hma (.inl rfl))
      have hmem : m_element τ D a ht hma ∈ M a ∩ M b :=
        ⟨(m_element_is_maximal τ D a ht hma).1,
          heq ▸ (m_element_is_maximal τ D b ht hmb).1⟩
      let y := m_element τ D a ht hma
      obtain ⟨k,hk,hh⟩ := hd.1 y
      have hlt : mini ht k <[k] y := by
        by_cases hka : k = a
        · subst k; exact hmem.2 a ha hab
        · exact hmem.1 k hk hka
      letI := IST k
      exact not_lt_of_ge (hh _ (Finset.min'_mem τ ht)) hlt
    all_goals
      
      simp_all [R,Finset.erase_eq_self,Finset.erase_inj]
  refine ⟨R a,R b,hne,hr a (by simp),hr b (by simp),?_⟩
  rintro ⟨σ,C⟩ hc
  obtain ⟨i,hi,heq⟩ := hex σ C hc
  have hi'  := by simpa using hi
  rcases hi' with rfl | rfl <;> simp_all

end KeyLemma

noncomputable section Scarf


variable (c : T → I) (σ : Finset T) (C : Finset I)

def isColorful : Prop := IST.isCell σ C ∧ σ.image c   = C

def isNearlyColorful : Prop := IST.isCell σ C ∧ (C \ σ.image c).card = 1

def isTypedNC (i : I) (σ : Finset T) (C : Finset I): Prop := IST.isCell σ C ∧ (C \ (σ.image c)) = {i}

variable {c σ C}




lemma NC_of_TNC (h1 : isTypedNC c i σ C) : isNearlyColorful c σ C := ⟨h1.1, by rw [h1.2]; simp⟩


lemma room_of_colorful (h : IST.isColorful c σ C) : IST.isRoom σ C := ⟨h.1, le_antisymm (h.2 ▸ Finset.card_image_le) (card_le_of_domiant h.1)⟩

def pick_colorful_point [Inhabited T] (h : IST.isColorful c σ C): σ := Classical.choice (sigma_nonempty_of_room (room_of_colorful h)).to_subtype




lemma missing_subset_of_door (h : isDoorof τ D σ C) :
    C \ σ.image c ⊆ D \ τ.image c := by
  cases h with
  | idoor _ _ x hx he hD =>
    grind
  | odoor _ _ j hj he hD =>
    grind

lemma NC_or_C_of_door (h1 : isTypedNC c i τ D) (h2 : isDoorof τ D σ C) : isTypedNC c i σ C ∨ isColorful c σ C := by
  have hr := isRoom_of_Door h2
  have hs := missing_subset_of_door (c := c) h2
  rw [h1.2] at hs
  rcases Finset.subset_singleton_iff.mp hs with he | he
  · right
    refine ⟨hr.1, (Finset.eq_of_subset_of_card_le (Finset.sdiff_eq_empty_iff_subset.mp he) ?_).symm⟩
    exact Finset.card_image_le.trans_eq hr.2.symm
  · tauto


lemma isTypedNC_of_isNearlyColorful_of_isDoorof_isTypedNC (h_nc : isNearlyColorful c τ D) (h_door : isDoorof τ D σ C) (h_room_typed : isTypedNC c i σ C) : isTypedNC c i τ D := by
  refine ⟨h_nc.1, ?_⟩
  have hi := missing_subset_of_door  h_door
    (h_room_typed.2 ▸ Finset.mem_singleton_self i)
  exact (Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hi)
    (by simpa using h_nc.2.le)).symm


lemma card_of_NCcell (h : isNearlyColorful c σ D) : #σ = #(image c σ)  ∨  #σ = #(image c σ) + 1 := by
  have hσ := card_le_of_domiant h.1
  have hsplit := Finset.card_sdiff_add_card_inter D (σ.image c)
  have hint := Finset.card_le_card (Finset.inter_subset_right : D ∩ σ.image c ⊆ σ.image c)
  have himg := Finset.card_image_le (f := c) (s := σ)
  rw [h.2] at hsplit
  omega


variable (c σ C) in
abbrev NCdoors := {(τ,D) | isNearlyColorful c τ D ∧ isDoorof τ D σ C }

lemma collision_door_valid  (σ : Finset T) (C : Finset I)
    (x : T) (h_cell : isCell σ C) (hx_in_σ : x ∈ σ) (h_card_eq : C.card = σ.card) :
    isDoorof (σ.erase x) C σ C := isDoorof.idoor h_cell
    ⟨Dominant_of_subset σ _ C (Finset.erase_subset x σ) h_cell,
      by grind⟩
    x (Finset.notMem_erase x σ) (Finset.insert_erase hx_in_σ) rfl

lemma door_of_isDoorof (h : isDoorof τ D σ C) : isDoor τ D := by
  cases h <;> assumption

lemma nc_door_iff (hr : isNearlyColorful c σ C) (hd : isDoorof τ D σ C) :
    isNearlyColorful c τ D ↔ D \ τ.image c = C \ σ.image c := by
  have hs := missing_subset_of_door (c := c) hd
  constructor
  · intro hn
    exact (Finset.eq_of_subset_of_card_le hs (by rw [hr.2, hn.2])).symm
  · intro he
    exact ⟨(door_of_isDoorof hd).1, by rw [he, hr.2]⟩

lemma outside_door_valid (hr : isRoom σ C) {j : I} (hj : j ∉ C) :
    isDoorof σ (insert j C) σ C := by
  have hd := Dominant_of_supset σ C (insert j C) (Finset.subset_insert _ _) hr.1
  exact isDoorof.odoor hr.1 ⟨hd, by grind⟩ j hj rfl rfl

lemma nc_erase_iff (hr : isRoom σ C) (hn : isNearlyColorful c σ C) {x : T} (hx : x ∈ σ) :
    isNearlyColorful c (σ.erase x) C ↔ c x ∉ C ∨ c x ∈ (σ.erase x).image c := by
  rw [nc_door_iff hn (collision_door_valid σ C x hr.1 hx hr.2)]
  have hi : σ.image c = insert (c x) ((σ.erase x).image c) := by grind
  rw [hi,Finset.sdiff_insert,eq_comm,Finset.erase_eq_self]
  simp only [Finset.mem_sdiff,not_and_or,not_not]

lemma nc_insert_iff (hr : isRoom σ C) (hn : isNearlyColorful c σ C) {j : I} (hj : j ∉ C) :
    isNearlyColorful c σ (insert j C) ↔ j ∈ σ.image c := by
  rw [nc_door_iff hn (outside_door_valid hr hj)]
  simp only [Finset.ext_iff, Finset.mem_sdiff, Finset.mem_insert]
  grind

lemma ncdoors_iff (hr : isRoom σ C) (hn : isNearlyColorful c σ C) (p : Finset T × Finset I) :
    p ∈ NCdoors c σ C ↔
      (∃ x ∈ σ, p = (σ.erase x, C) ∧ (c x ∉ C ∨ c x ∈ (σ.erase x).image c)) ∨
      ∃ j ∈ σ.image c, j ∉ C ∧ p = (σ, insert j C) := by
  rcases p with ⟨τ,D⟩
  constructor
  · rintro ⟨h, hd⟩
    cases hd with
    | idoor _ _ x hx he hD =>
      grind [nc_erase_iff,Finset.erase_insert,Finset.mem_insert_self]
    | odoor _ _ j hj he hD =>
      grind [nc_insert_iff]
  · grind [collision_door_valid,nc_erase_iff,nc_insert_iff,outside_door_valid]

lemma doors_of_NCroom  (h_room : isRoom σ C) (h_nc : isNearlyColorful c σ C) :
  ∃ door1 door2, door1 ≠ door2 ∧ NCdoors c σ C = {door1, door2} := by
  rcases card_of_NCcell h_nc with hc | hc
  · have hinj := Finset.injOn_of_card_image_eq hc.symm
    have hcard : (σ.image c \ C).card = 1 := by
      rw [Finset.card_sdiff_comm (hc.symm.trans h_room.2.symm), h_nc.2]
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
    have hjmem : j ∈ σ.image c \ C := by grind
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hjmem).1
    have heq {z : T} (hz : z ∈ σ) :
        (c z ∉ C ∨ c z ∈ (σ.erase z).image c) ↔ z = y := by
      have hj' := Finset.ext_iff.mp hj
      simp only [Finset.mem_sdiff, Finset.mem_image, Finset.mem_singleton] at hj'
      simp only [Set.InjOn, Finset.mem_coe] at hinj
      simp only [Finset.mem_image, Finset.mem_erase]
      grind
    refine ⟨(σ.erase y,C), (σ,insert (c y) C), ?_, ?_⟩
    · aesop
    · ext p
      rw [ncdoors_iff h_room h_nc]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      grind
  · obtain ⟨x,hx,y,hy,hne,hxy⟩ := Finset.exists_ne_map_eq_of_card_image_lt
      (show #(σ.image c) < #σ by omega)
    have himg : σ.image c ⊆ C := by
      have hn := h_nc.2
      apply Finset.sdiff_eq_empty_iff_subset.mp
      apply Finset.card_eq_zero.mp
      grind
    have hp : (σ.erase x).image c = σ.image c := by grind
    have hinj : Set.InjOn c (σ.erase x : Set T) := Finset.injOn_of_card_image_eq (by grind)
    have heq {z : T} (hz : z ∈ σ) :
        (c z ∉ C ∨ c z ∈ (σ.erase z).image c) ↔ z = x ∨ z = y := by
      have hzC := himg (Finset.mem_image_of_mem c hz)
      simp only [hzC, not_true, false_or, Finset.mem_image, Finset.mem_erase]
      simp only [Set.InjOn, Finset.mem_coe, Finset.mem_erase] at hinj
      grind
    refine ⟨(σ.erase x,C), (σ.erase y,C), ?_, ?_⟩
    · grind
    · ext p
      rw [ncdoors_iff h_room h_nc]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      grind


variable [Fintype T] [Fintype I]

variable (c) in
abbrev colorful := Finset.filter (fun (x : Finset T× Finset I) =>  IST.isColorful c x.1 x.2) univ

variable (c) in
abbrev dbcountingset (i : I):= Finset.filter (fun x : (Finset T× Finset I) × (Finset T× Finset I) => isTypedNC c i x.1.1 x.1.2 ∧ isDoorof x.1.1 x.1.2 x.2.1 x.2.2) univ

lemma dominant_singleton_iff (x : T) (i : I) :
    isDominant {x} {i} ↔ ∀ y, y ≤[i] x := by simp [isDominant]

variable (c) in
lemma dbcount_outside_door' [Inhabited T] (i : I): ∃ x,  filter (fun x => isOutsideDoor x.1.1 x.1.2) (dbcountingset c i) = {x}  :=  by

  let m := @Finset.max' T (IST i) Finset.univ Finset.univ_nonempty
  have hc := (dominant_singleton_iff m i).mpr
    (fun y => @Finset.le_max' _ (IST i) _ y (Finset.mem_univ y))
  have hd :=
    isDoorof.idoor hc (outsidedoor_singleton i).1 m (by simp) (by simp) rfl
  have ht : isTypedNC c i (∅ : Finset T) {i} := ⟨(outsidedoor_singleton i).1.1, by simp⟩
  refine ⟨((∅,{i}),({m},{i})), ?_⟩
  ext p
  simp only [dbcountingset, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rcases p with ⟨⟨τ,D⟩,⟨σ,C⟩⟩
    rintro ⟨⟨htyped,hrel⟩,hout⟩
    have hτ : τ = ∅ := hout.2
    subst τ
    have hD  := by simpa using htyped.2
    subst D
    have hr := isRoom_of_Door hrel
    cases hrel with
    | idoor hcell _ x hx he hC =>
      have hσ  := by simpa using he.symm
      change ({i} : Finset I) = C at hC
      subst σ C
      have hmax := (dominant_singleton_iff x i).mp hcell
      have hxeq : x = m := @le_antisymm _ (IST i).toPartialOrder _ _
        (@Finset.le_max' _ (IST i) _ x (Finset.mem_univ x)) (hmax m)
      simp [hxeq]
    | odoor _ _ j hj he hD =>
      change (∅ : Finset T) = σ at he
      have hn : (∅ : Finset T).Nonempty := by simpa [← he] using sigma_nonempty_of_room hr
      exact (Finset.not_nonempty_empty hn).elim
  · grind [outsidedoor_singleton]


variable (c)

lemma dbcount_outside_door_odd [Inhabited T] (i : I): Odd (filter (fun x => isOutsideDoor x.1.1 x.1.2) (dbcountingset c i)).card  := by
  obtain ⟨x,hx⟩ := dbcount_outside_door' c i
  simp [hx]


lemma dbcount_internal_door_even (i : I) : Even (filter (fun x => ¬ isOutsideDoor x.1.1 x.1.2) (dbcountingset c i)).card := by
  apply even_card_of_two_fibres _ (fun x => x.1)
  intro x hx
  obtain ⟨hx,hn⟩ := mem_filter.mp hx
  obtain ⟨_,ht,hd⟩ := mem_filter.mp hx
  have hdoor := door_of_isDoorof hd
  obtain ⟨r₁,r₂,hne,hd₁,hd₂,hu⟩ := internal_door_two_rooms x.1.1 x.1.2
    ⟨hdoor, Finset.nonempty_iff_ne_empty.mpr (fun h => hn ⟨hdoor,h⟩)⟩
  apply Finset.card_eq_two.mpr
  refine ⟨(x.1,r₁),(x.1,r₂),by simpa using hne,?_⟩
  ext ⟨d,σ,C⟩
  have := hu (σ,C)
  simp only [dbcountingset, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  grind

lemma dbcount_NCroom (i : I) : Even (filter (fun x => ¬isColorful c x.2.1 x.2.2) (dbcountingset c i)).card := by
  apply even_card_of_two_fibres _ (fun x => x.2)
  intro x hx
  obtain ⟨hx,hn⟩ := mem_filter.mp hx
  obtain ⟨_,ht,hd⟩ := mem_filter.mp hx
  have hr := isRoom_of_Door hd
  have ht := (NC_or_C_of_door ht hd).resolve_right hn
  obtain ⟨d₁,d₂,hne,he⟩ := doors_of_NCroom hr (NC_of_TNC ht)
  have hm := Set.ext_iff.mp he
  simp only [NCdoors, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hm
  apply Finset.card_eq_two.mpr
  refine ⟨(d₁,x.2),(d₂,x.2),by simpa using hne,?_⟩
  ext ⟨d,r⟩
  simp only [dbcountingset, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  grind [NC_of_TNC, isTypedNC_of_isNearlyColorful_of_isDoorof_isTypedNC]


lemma typed_colorful_room_odd [Inhabited T]  (i : I): Odd (Finset.filter (fun (x: (Finset T× Finset I) × Finset T × Finset I) =>  isColorful c x.2.1 x.2.2) (dbcountingset c i)).card
:= by
  have ho := dbcount_outside_door_odd c i
  have hi := dbcount_internal_door_even c i
  have hn := dbcount_NCroom c i
  have h₁ := (dbcountingset c i).card_filter_add_card_filter_not
    (fun x => isOutsideDoor x.1.1 x.1.2)
  have h₂ := (dbcountingset c i).card_filter_add_card_filter_not
    (fun x => isColorful c x.2.1 x.2.2)
  grind

variable [Inhabited I]

theorem Scarf [Inhabited T] : (IST.colorful c).Nonempty := by
  have cardpos := Odd.pos $ typed_colorful_room_odd c default
  replace nonempty:= Finset.card_pos.1 cardpos
  obtain ⟨x,hx⟩ := nonempty
  replace hx := (Finset.mem_filter.1 hx).2
  use x.2
  simp only [mem_filter, mem_univ, hx, and_self]

end Scarf

end IndexedLOrder
