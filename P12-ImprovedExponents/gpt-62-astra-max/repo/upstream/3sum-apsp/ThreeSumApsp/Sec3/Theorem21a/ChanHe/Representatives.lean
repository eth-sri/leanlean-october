/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec3.Theorem21a.ChanHe.Collisions
public import ThreeSumApsp.Util.Index

/-! A table need not discard every colliding key. Keep the least value in each
bucket, with `2U+1` for an empty bucket. This covers all singletons, and even
a hit involving multiply occupied buckets is a genuine solution. -/
@[expose] public section
namespace ThreeSumApsp.ChanHe
open Finset

abbrev Limit (U : ℕ) : ℤ := 2 * U + 1
def residue (M : ℕ) (sg x : ℤ) := (sg*x % M).toNat
def rep (S : Finset ℤ) (M U : ℕ) (sg : ℤ) (r : ℕ) : ℤ :=
  (insert (Limit U) (S.filter (fun z => residue M sg z = r))).min' (insert_nonempty ..)

theorem rep_empty (M U : ℕ) (sg : ℤ) (r : ℕ) : rep ∅ M U sg r = Limit U := by simp [rep]

theorem rep_insert (z : ℤ) (S : Finset ℤ) (M U : ℕ) (sg : ℤ) (r : ℕ) :
    rep (insert z S) M U sg r = if r = residue M sg z then min z (rep S M U sg r) else rep S M U sg r := by
  by_cases e : residue M sg z=r
  · simp [rep,filter_insert,e,insert_comm (Limit U) z, min'_insert]
  · simp [rep,filter_insert,e,Ne.symm e]

variable {M U : ℕ} {S : Finset ℤ} {sg x : ℤ}

theorem rep_cases (h : Bdd U S) (M : ℕ) (sg : ℤ) (r : ℕ) :
    rep S M U sg r = Limit U ∨ (rep S M U sg r ∈ S ∧ |rep S M U sg r| ≤ U) := by
  have hm : rep S M U sg r ∈ insert (Limit U) (S.filter (fun z => residue M sg z = r)) := min'_mem ..
  rcases mem_insert.mp hm with e|ht
  · exact Or.inl e
  · have hh := (mem_filter.mp ht).1; exact Or.inr ⟨hh,h _ hh⟩

theorem residue_cast (hM : 1≤M) (sg z : ℤ) : (residue M sg z : ℤ) = sg*z % M := by
  simp [residue,Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega : (M:ℤ) ≠ 0))]

theorem residue_lt (hM : 1≤M) (sg z : ℤ) : residue M sg z < M :=
  Int.toNat_emod_lt hM _

/-- The representative of a noncolliding value is that value, also for negated keys. -/
theorem rep_single (hM : 1≤M) (hS : Bdd U S) (hx : x ∈ S \ heavy S M)
    (sign : sg=1 ∨ sg= -1) : rep S M U sg (residue M sg x) = x := by
  obtain ⟨xs,xh⟩ := mem_sdiff.mp hx
  have e : S.filter (fun z => residue M sg z = residue M sg x) = {x} := by
    ext z; simp only [mem_filter,mem_singleton]
    constructor
    · rintro ⟨hz,eqr⟩; by_contra ne
      have eqm := congrArg (fun r : ℕ => (r:ℤ)) eqr
      simp only [residue_cast hM] at eqm
      apply xh; refine mem_filter.mpr ⟨xs,z,hz,ne,?_⟩
      rcases sign with rfl|rfl
      · exact (natCast_dvd_sub_iff_emod_eq ..).mpr (by simpa using eqm.symm)
      · have h : (M:ℤ) ∣ -z - -x := (natCast_dvd_sub_iff_emod_eq ..).mpr (by simpa using eqm)
        convert h using 1; ring
    · rintro rfl; exact ⟨xs,rfl⟩
  have hxle := (abs_le.mp (hS x xs)).2
  have le : x ≤ Limit U := by unfold Limit; omega
  simp [rep,e,min'_insert,le]

/-- The modular instance solved at a node. -/
def modSum (M : ℕ) (X Y Z : ℕ → ℤ) := ∃ i < M, ∃ j < M, X i + Y j + Z ((i+j)%M) = 0
abbrev Node.Hit (v : Node) (U : ℕ) := modSum v.M (rep v.S₁ v.M U 1) (rep v.S₂ v.M U 1) (rep v.S₃ v.M U (-1))

variable {A B C : Finset ℤ}

theorem hit_sound (hA : Bdd U A) (hB : Bdd U B) (hC : Bdd U C) :
    (Node.mk A B C M).Hit U → HasSol A B C := by
  rintro ⟨i,-,j,-,h⟩
  dsimp at h
  rcases rep_cases hA M 1 i with e|⟨ha,ea⟩ <;>
    rcases rep_cases hB M 1 j with f|⟨hb,eb⟩ <;>
    rcases rep_cases hC M (-1) ((i+j)%M) with g|⟨hc,ec⟩
  all_goals first | exact ⟨_,ha,_,hb,_,hc,h⟩ | (simp [Limit,abs_le] at *; omega)

theorem light_hit (hM : 1≤M) (hA : Bdd U A) (hB : Bdd U B) (hC : Bdd U C) :
    HasSol (A \ heavy A M) (B \ heavy B M) (C \ heavy C M) → (Node.mk A B C M).Hit U := by
  rintro ⟨x,hx,y,hy,z,hz,eq⟩
  refine ⟨_,residue_lt hM 1 x,_,residue_lt hM 1 y,?_⟩
  have key : (residue M 1 x+residue M 1 y)%M = residue M (-1) z := by
    apply Nat.cast_injective (R:=ℤ)
    push_cast; simp only [residue_cast hM,one_mul,neg_one_mul,← Int.add_emod,show x+y = -z by omega]
  dsimp; rw [key,rep_single hM hA hx (Or.inl rfl),rep_single hM hB hy (Or.inl rfl),rep_single hM hC hz (Or.inr rfl)]; exact eq

end ThreeSumApsp.ChanHe
