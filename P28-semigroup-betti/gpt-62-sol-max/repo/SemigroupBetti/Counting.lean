/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/
module

public import Mathlib

/-! Bounds for the three families of closed splits of the factorization fibers. -/

@[expose] public section

namespace SemigroupBetti

open Finset Finsupp

abbrev Vec := Fin 4 →₀ ℕ

/-- The generators are `m + g*a i`, with increasing normalized offsets `a` starting at zero. -/
structure GenData where
  m : ℕ
  g : ℕ
  a : Fin 4 → ℕ
  m_pos : 0 < m
  a0 : a 0 = 0
  mono : StrictMono a

namespace GenData

variable (G : GenData)

abbrev A := G.a 1
abbrev B := G.a 2
abbrev W := G.a 3

def C := G.B - G.A
def t := G.W - G.B

def n (i : Fin 4) : ℕ := G.m + G.g * G.a i

/-- Weighted degree of a factorization. -/
noncomputable abbrev nu : Vec →+ ℕ := weight G.n

attribute [local simp] weight_single

lemma nu_eq_zero (z : Vec) : G.nu z = 0 ↔ z = 0 :=
  let _ := nonTorsionWeight_of ℕ G.n fun _ => (G.m_pos.trans_le (Nat.le_add_right ..)).ne'
  weight_eq_zero_iff_eq_zero _

abbrev Fiber (d : ℕ) := {z : Vec // G.nu z = d}

lemma nu_pos (z : Vec) : 0 < G.nu z ↔ z.support.Nonempty := by
  simp [Nat.pos_iff_ne_zero, G.nu_eq_zero]

/-- The three partitions into pairs, oriented by the side containing index 1. -/
def face (k : Fin 3) (b : Bool) : Finset (Fin 4) :=
  let s : Fin 3 → Finset (Fin 4) := ![{0, 1}, {1, 3}, {1, 2}]
  if b then (s k)ᶜ else s k

lemma face_compl : ∀ k b, (face k b)ᶜ = face k (!b) := by decide
lemma face_disjoint : ∀ k b c, b ≠ c → Disjoint (face k b) (face k c) := by decide
lemma face_nonempty : ∀ k b, (face k b).Nonempty := by decide

lemma pair_sides : ∀ K L : Finset (Fin 4), 2 ≤ K.card → 2 ≤ L.card → Disjoint K L →
    ∃ k b, K = face k b ∧ L = face k (!b) := by decide

/-- Both sides have a full-support factorization, and no factorization meets both sides. -/
abbrev Fam (k : Fin 3) :=
  {d : ℕ // (∀ b, ∃ x : G.Fiber d, x.1.support = face k b) ∧
    ∀ x : G.Fiber d, ∃ b, x.1.support ⊆ face k b}

variable {G} {k : Fin 3} {b : Bool} {i j : Fin 4} {u v : Vec}

noncomputable def pick (x : G.Fam k) (b : Bool) : Vec := (x.2.1 b).choose.1

@[simp] lemma pick_spec (x : G.Fam k) (b : Bool) :
    G.nu (pick x b) = x.1 ∧ (pick x b).support = face k b :=
  ⟨(x.2.1 b).choose.2, (x.2.1 b).choose_spec⟩

lemma pick_pos (x : G.Fam k) (h : i ∈ face k b) : 0 < pick x b i :=
  Nat.pos_of_ne_zero (mem_support_iff.1 ((pick_spec x b).2.symm ▸ h))

/-- A replacement crossing the split must consume the entire factorization. -/
lemma replacement_eq (x : G.Fam k) (hle : u ≤ pick x b) (e : G.nu u = G.nu v)
    (hj : j ∉ face k b) (hv : 0 < v j) : u = pick x b := by
  obtain ⟨c, hc⟩ := x.2.2 ⟨pick x b - u + v, by
    rw [map_add, ← e, ← map_add, tsub_add_cancel_of_le hle, (pick_spec x b).1]⟩
  simp only [support_add_eq_union, union_subset_iff] at hc
  have hbc : b ≠ c := fun h => hj (h.symm ▸ hc.2 (mem_support_iff.2 hv.ne'))
  apply le_antisymm hle
  rw [← tsub_eq_zero_iff_le, ← support_eq_empty, ← disjoint_self_iff_empty]
  exact (face_disjoint k b c hbc).mono ((pick_spec x b).2 ▸ support_tsub) hc.1

private lemma same_degree_of_le {x y : G.Fam k} (hle : pick x b ≤ pick y b) :
    x = y := by
  obtain ⟨i, hi⟩ := face_nonempty k (!b)
  refine Subtype.ext ?_
  simpa using congrArg G.nu (replacement_eq y hle (by simp)
    (by simpa [← face_compl] using hi) (pick_pos x hi))

private lemma pair_coords : ∀ k b i, i ∈ face k b →
    ∃ j ≠ i, face k b = {i, j} := by decide

/-- Fixing one coordinate on a side makes the selected vectors comparable. -/
private lemma coord_inj (hi : i ∈ face k b) :
    Function.Injective (fun x : G.Fam k => pick x b i) := by
  intro x y e
  obtain ⟨j, _, hj⟩ := pair_coords k b i hi
  suffices pick x b ≤ pick y b ∨ pick y b ≤ pick x b by
    exact this.elim same_degree_of_le (fun h => (same_degree_of_le h).symm)
  simpa [Finsupp.le_iff, pick_spec, hj, e] using le_total (pick x b j) (pick y b j)

private lemma coord_card {s : Set (G.Fam k)} (hi : i ∈ face k b) {c : ℕ}
    (hc : ∀ d ∈ s, pick d b i ≤ c) : s.encard ≤ c := by
  simpa [Set.encard_Ioc] using
    Set.encard_le_encard_of_injOn (t := Set.Ioc 0 c)
      (fun d h => ⟨pick_pos d hi, hc d h⟩) (coord_inj hi).injOn

private lemma single_trade_card (hi : i ∈ face k b) {c : ℕ}
    (e : G.nu (single i c) = G.nu v) (hj : j ∉ face k b) (hv : 0 < v j) :
    ENat.card (G.Fam k) ≤ (c - 1 : ℕ) := by
  rw [← Set.encard_univ]
  refine coord_card hi fun d _ => ?_
  by_contra! h
  obtain ⟨l, hli, hl⟩ := pair_coords k b i hi
  have he := replacement_eq d (single_le_iff.2 (by omega)) e hj hv
  simpa [he, pick_spec, hl, insert_subset_iff, hli, -subset_singleton_iff] using
    (support_single_subset : (single i c).support ⊆ {i})

variable (G)

private lemma gaps : G.C + G.A = G.B ∧ G.t + G.B = G.W ∧ 0 < G.A ∧ 0 < G.t ∧ 0 < G.C := by
  have h (i : Fin 3) := G.mono (Fin.castSucc_lt_succ (i := i))
  exact ⟨Nat.sub_add_cancel (h 1).le, Nat.sub_add_cancel (h 2).le, G.a0 ▸ h 0,
    Nat.sub_pos_of_lt (h 2), Nat.sub_pos_of_lt (h 1)⟩

lemma trade1 :
    G.nu (single 1 G.B) = G.nu (single 0 G.C + single 2 G.A) := by
  simp [n, G.a0, ← G.gaps.1]
  ring

lemma trade2 :
    G.nu (single 2 (G.C + G.t)) = G.nu (single 1 G.t + single 3 G.C) := by
  simp [n, ← G.gaps.2.1, ← G.gaps.1]
  ring

lemma trade3 {p q : ℕ} (h : p * G.A = q * G.t) :
    G.nu (single 1 p + single 2 q) = G.nu (single 0 p + single 3 q) := by
  simp [n, G.a0, ← G.gaps.2.1]
  linear_combination G.g * h

local notation "𝓟" => G.Fam 0
local notation "𝓠" => G.Fam 1
local notation "ℰ" => G.Fam 2

private lemma PQ_bound {k : Fin 3} (h1 : 1 ∈ face k false) (h2 : 2 ∉ face k false) :
    ENat.card (G.Fam k) ≤ (min (G.B - 1) (G.C + G.t - 1) : ℕ) := by
  rw [(Nat.mono_cast (α := ℕ∞)).map_min]
  exact le_min (single_trade_card h1 G.trade1 h2 (by simpa using G.gaps.2.2.1))
    (single_trade_card (b := true) (by simpa [face] using h2) G.trade2 (j := 1)
      (by simpa [face] using h1) (by simpa using G.gaps.2.2.2.1))

/-- Charge a split in `12|03` to its first coordinate if that coordinate is less than
`p`; otherwise its second coordinate is at most `q`. -/
private lemma E_bound (p q : ℕ) (hp : 0 < p) (h : p * G.A = q * G.t) :
    ENat.card ℰ ≤ (p - 1 + q : ℕ) := by
  let s : Set ℰ := {d | pick d false 1 ≤ p - 1}
  rw [← Set.encard_univ, ← Set.encard_add_encard_compl s, Nat.cast_add]
  refine add_le_add (coord_card (by decide) fun _ h => h) ?_
  apply coord_card (b := false) (i := 2) (by decide)
  rintro d (hd : ¬ pick d false 1 ≤ p - 1)
  have hu : p ≤ pick d false 1 := by omega
  by_contra! hv
  have hle : single 1 p + single 2 q ≤ pick d false := by
    intro i; fin_cases i <;> simp [hu, hv.le]
  apply hv.ne
  simpa using congrArg (· 2)
    (replacement_eq d hle (G.trade3 h) (j := 0) (by decide) (by simpa using hp))

/-- In the unit-gap case the two large families cannot both attain their bounds.
A full `02`-factorization from `𝓠`, with one copy of generator 2 removed, gives a
replacement ruling out a saturated `23|01` split. -/
private lemma unit_bound (ht : G.t = 1) :
    ENat.card 𝓟 ≤ (G.C - 1 : ℕ) ∨ ENat.card 𝓠 ≤ (G.C - 1 : ℕ) := by
  by_cases! H : ∀ d : 𝓠, pick d false 3 < G.C
  · right
    rw [← Set.encard_univ]
    exact coord_card (b := false) (i := 3) (by decide) fun d _ => Nat.le_sub_one_of_lt (H d)
  obtain ⟨d, hd⟩ := H
  left
  have hu := ht ▸ G.trade2.symm
  have hle : single 1 1 + single 3 G.C ≤ pick d false := by
    have h : 1 ≤ pick d false 1 := pick_pos d (by decide)
    intro i; fin_cases i <;> simp [h, hd]
  have hdu : d.1 = (G.C + 1) * G.n 2 := by
    have e := replacement_eq d hle hu (j := 2) (by decide) (by simp)
    simpa [e, add_mul] using hu
  let r := pick d true - single 2 1
  have hr : G.nu (single 2 G.C) = G.nu r := by
    symm
    simpa [r, hdu, add_mul] using weight_sub_single_add (w := G.n)
      (pick_pos d (b := true) (i := 2) (by decide)).ne'
  exact single_trade_card (b := true) (by decide) hr (j := 0) (by decide)
    (by simpa [r, Finsupp.tsub_apply] using pick_pos d (b := true) (i := 0) (by decide))

/-- Allow four pure-power relations and one relation per closed split. Equal outer gaps
admit the shorter trade `(1, 1)`; the unit-gap case also uses the coupled bound above. -/
lemma sum_bound : 4 + ∑ k, ENat.card (G.Fam k) ≤ (2 * G.W : ℕ) := by
  rw [Fin.sum_univ_three]
  have hP := G.PQ_bound (k := 0) (by decide) (by decide)
  have hQ := G.PQ_bound (k := 1) (by decide) (by decide)
  have hE := G.E_bound _ _ G.gaps.2.2.2.1 (mul_comm _ _)
  have hS (h : G.A = G.t) : ENat.card ℰ ≤ 1 :=
    G.E_bound 1 1 (by decide) (by simpa using h)
  have hU := G.unit_bound
  generalize ENat.card 𝓟 = p, ENat.card 𝓠 = q, ENat.card ℰ = e at *
  obtain ⟨_, _, _, _, _⟩ := G.gaps
  enat_to_nat; omega

end GenData
end SemigroupBetti
