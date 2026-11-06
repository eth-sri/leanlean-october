/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.Theorem30.Memory
public import ThreeSumApsp.TacticsShort

/-!
# Theorem 30, the offline form (9): preprocess, then one query for each wanted position

Theorem 30: "In particular, for every set W of positions of an N × N matrix, the entries (XY)[I, J],
(I, J) ∈ W, can be computed deterministically in time
O(L |W| ∑_{d=0}^{t} α_d + L m ρ^t/(1 - ρ) N² + N · 10^L/(√K N₀))."

wantedCore is relocatable: it receives the addresses of the matrices, of the two lists of indices,
of the output and of the free block. It meets its specification `WantedCoreSpec` in every program
that meets those of preCore and queryAt (`wantedCore_spec`): one call of preCore, then a loop whose
round asks one query and stores the answer (`wantedAsk_ends`), with the invariant `Answered`.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp

/-! ## One query for each wanted position: the invariant -/

section
variable {Ready : (ℕ → ℤ) → Prop} {Kept Quiet : ℕ → Prop} {out i : ℕ} {ans : List ℤ}
  {μ μ' μ'' : ℕ → ℤ}

/-- The invariant of a loop that asks one query after the other and stores the answers ans from the
address out on, before query i.  The memory is Ready for a query, the first i answers are in place,
and the cells in Kept outside these i cells are as in the memory μ at the start. -/
structure Answered (Ready : (ℕ → ℤ) → Prop) (Kept : ℕ → Prop) (out : ℕ) (ans : List ℤ) (μ : ℕ → ℤ)
    (i : ℕ) (μ' : ℕ → ℤ) : Prop where
  ready : Ready μ'
  answers : Seg μ' out (ans.take i)
  same : SameOn (fun a => Outside out i a ∧ Kept a) μ μ'

/-- One round: a query that leaves the cells in Quiet alone, among them the output and the cells in
Kept, and the store of its answer behind the answers that are there. -/
theorem Answered.step (h : Answered Ready Kept out ans μ i μ') (hi : i < ans.length)
    (hquery : SameOn Quiet μ' μ'') (hout : ∀ j < i, Quiet (out + j)) (hkept : ∀ a, Kept a → Quiet a)
    (hready : Ready (Function.update μ'' (out + i) ans[i])) :
    Answered Ready Kept out ans μ (i + 1) (Function.update μ'' (out + i) ans[i]) := by
  have hlen : (ans.take i).length = i := by rw [List.length_take, Nat.min_eq_left hi.le]
  refine ⟨hready, ?_, ?_⟩
  · have hsnoc := (h.answers.of_sameOn hquery fun j hj => hout j (hlen ▸ hj)).snoc ans[i]
    rw [hlen] at hsnoc
    rwa [List.take_add_one, List.getElem?_eq_getElem hi]
  · exact ((h.same.mono fun a ha => ⟨by have := ha.1; omega, ha.2⟩).then hquery
      fun a ha => ⟨ha, hkept a ha.2⟩).write tac_omega _

/-- A cell of a list that stood in the memory at the start, away from the answers and in Kept, still
holds its entry. -/
theorem Answered.read (h : Answered Ready Kept out ans μ i μ') {a j : ℕ} {l : List ℤ}
    (hl : Seg μ a l) (hj : j < l.length) (hoff : Outside out i (a + j)) (hkept : Kept (a + j)) :
    μ' (a + j) = l[j] :=
  (h.same _ ⟨hoff, hkept⟩).trans (hl.get hj)

/-- After the last round all answers are in place. -/
theorem Answered.all (h : Answered Ready Kept out ans μ ans.length μ') : Seg μ' out ans := by
  simpa using h.answers

end

/-! ## The routine -/

abbrev Proc.wantedCore : ℕ := 56

namespace WantedCore

/-- The locals of wantedCore. The first twelve are its arguments: L, m, t, N, D, the addresses of X,
of Y, of the rows and of the columns of the wanted positions, the number of positions, and the
addresses of the output and of the free block. Then come the number of the current position and the
result of a call. -/
abbrev Levels : ℕ := 0
 abbrev Inner : ℕ := 1
 abbrev Switch : ℕ := 2
 abbrev Size : ℕ := 3
 abbrev Dim : ℕ := 4
 abbrev MatX : ℕ := 5
 abbrev MatY : ℕ := 6
 abbrev Rows : ℕ := 7
 abbrev Cols : ℕ := 8
 abbrev Count : ℕ := 9
 abbrev Out : ℕ := 10
 abbrev Block : ℕ := 11
 abbrev Pos : ℕ := 12
 abbrev Res : ℕ := 13

end WantedCore

open WantedCore
/-- One round of wantedCore: ask the query for the current position and store its answer. -/
def wantedAsk : Stmt :=
  .call Proc.queryAt [M (v Rows +' v Pos), M (v Cols +' v Pos), v Block] Res ;;
  .store (v Out +' v Pos) (v Res)

open WantedCore in
/-- wantedCore(L, m, t, N, D, aX, aY, aI, aJ, w, out, b0): preprocess, then ask one query for each
wanted position and store its answer. -/
def wantedCoreBody : Stmt :=
  .call Proc.preCore [v Levels, v Inner, v Switch, v Size, v Dim, v MatX, v MatY, v Block] Res ;;
  .for Pos (v Count) wantedAsk

section
variable {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L} {aX aY aI aJ out b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ}
  {W : List (Fin p.N × Fin p.N)} {μ μ' μ'' : ℕ → ℤ}

end

end Light.Sec4