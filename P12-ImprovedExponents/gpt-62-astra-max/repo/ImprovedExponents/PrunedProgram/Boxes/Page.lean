/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Spec.Sec4.Theorem30.PartialSums
public import ThreeSumApsp.Spec.Sec4.Theorem30.StarBoxes
public import ImprovedExponents.PrunedProgram.SegOn

/-! Each tile gets its own address range, with a cell for every base-11 string
of length L. Only boxes in the dynamic program are ever written or read. In
particular there is no zeroing pass proportional to the size of the range. -/

@[expose] public section
namespace Light.Sec4.BoxTable
open ThreeSumApsp ThreeSumApsp.Spec

/-- The shared stage already knows `10^L`. Its square is a convenient stride. -/
abbrev stride (L : ℕ) := (10^L)*(10^L)

theorem pow_le_stride (L : ℕ) : 11^L ≤ stride L := by
  rw [stride, ← mul_pow]; exact Nat.pow_le_pow_left (by decide) _

structure Tile where
  (L m t a b cur box page : ℕ)
  (A B : Leaf L → ℤ)

namespace Tile
variable (x : Tile)
abbrev keys (e : ℕ) := starBoxes x.L x.m x.t e
abbrev leaves (e : ℕ) := nineStrs x.L e (x.m-x.t)
abbrev val := storedD (arrT x.A) (arrT x.B)

/-- A predicate on initialized keys, imposed only on genuine boxes of the tile. -/
def Holds (μ : ℕ → ℤ) (K : ℕ → List ℕ → Prop) :=
  ∀ j l, l ∈ x.keys j → K j l → μ (x.page + ofDigitList 11 l) = x.val l

abbrev Done (μ : ℕ → ℤ) (e i : ℕ) := x.Holds μ fun j l =>
  j < e ∨ j = e ∧ l ∈ (x.keys e).take i

structure Safe (lim : Limits) : Prop where
  std : Std lim
  sizes : x.t ≤ x.m ∧ x.m ≤ x.L
  layout : x.a+10^x.L ≤ x.cur ∧ x.b+10^x.L ≤ x.cur ∧ x.cur+x.L ≤ x.box ∧
    x.box+x.L ≤ x.page ∧ x.page+stride x.L < lim.space
  bounds : ∃ A B : ℤ, (∀ τ, |x.A τ| ≤ A) ∧ (∀ τ, |x.B τ| ≤ B) ∧ 10^x.m*(A*B) ≤ lim.word

variable {x} {μ ν : ℕ → ℤ} {e i : ℕ} {K : ℕ → List ℕ → Prop}

theorem address {l} (h : l ∈ x.keys e) : ofDigitList 11 l < stride x.L := by
  have ⟨len,ds⟩ := starBoxes_digits h
  exact (ofDigitList_lt _ ds).trans_le (len ▸ pow_le_stride l.length)

theorem Holds.keep (h : x.Holds μ K) (keep : SameOn (Inside x.page (stride x.L)) μ ν := by light_keep) :
    x.Holds ν K := fun j l hl hj => (keep _ (by have := address hl; constructor <;> omega)).trans (h j l hl hj)

theorem Done.write (h : x.Done μ e i) (hi : i < (x.leaves e).length) :
    let l := starFirst e (x.leaves e)[i]
    x.Done (Function.update μ (x.page+ofDigitList 11 l) (x.val l)) e (i+1) := by
  let l := starFirst e (x.leaves e)[i]
  have hl : l ∈ x.keys e := starFirst_mem_starBoxes hi
  have hi' : i < (x.keys e).length := by simpa [keys,length_starBoxes_eq_length_nineStrs] using hi
  have atI : (x.keys e)[i] = l := List.getElem_map ..
  change x.Done (Function.update μ (x.page+ofDigitList 11 l) (x.val l)) e (i+1)
  intro j k hk hK
  by_cases eqCode : ofDigitList 11 k = ofDigitList 11 l
  · have H : k = l := by
      have hk' := digitList_ofDigitList _ (starBoxes_digits hk).2
      rwa [eqCode,(starBoxes_digits hk).1,← (starBoxes_digits hl).1,digitList_ofDigitList _ (starBoxes_digits hl).2,eq_comm] at hk'
    subst k; apply Function.update_self
  · rw [Function.update_of_ne (by omega)]
    apply h j k hk
    rcases hK with hj|⟨rfl,hm⟩
    · exact .inl hj
    · rw [List.take_succ_eq_append_getElem hi',atI] at hm
      apply Or.inr; refine ⟨rfl, ?_⟩
      simpa [show k ≠ l from fun eq => eqCode (eq ▸ rfl)] using hm

theorem Done.next (h : x.Done μ e (x.leaves e).length) : x.Done μ (e+1) 0 := by
  intro j l hl hK; simp only [List.take_zero,List.not_mem_nil,and_false,or_false] at hK
  apply h _ _ hl
  rcases Nat.lt_succ_iff_lt_or_eq.mp hK with hj|rfl
  · exact .inl hj
  · exact .inr ⟨rfl, by simpa [keys,← length_starBoxes_eq_length_nineStrs] using hl⟩

/-- Read a completed cell from the preceding level. -/
theorem Done.read (h : x.Done μ (e+1) i) {l} (hl : l ∈ x.keys e) :
    μ (x.page+ofDigitList 11 l) = dpValueD (arrT x.A) (arrT x.B) e l := by
  simpa [val,storedD,starCount_of_mem_starBoxes hl] using h e l hl (.inl (Nat.lt_succ_self e))

end Tile
end Light.Sec4.BoxTable
