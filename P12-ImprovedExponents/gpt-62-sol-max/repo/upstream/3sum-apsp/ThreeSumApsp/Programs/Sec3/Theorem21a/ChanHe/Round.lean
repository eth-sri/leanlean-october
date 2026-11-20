/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

import ThreeSumApsp.Lang.Registers

public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.FrontFacts
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.GridContracts
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Nodes

/-!
# The reduction from 3SUM to Convolution-3SUM: one splitting

round(β, β', b, nd, val, bt, Λ, A, n, f, cx, fr) handles the splitting `(β, β', v)` of the set of
the distinct values, where `b` is 1 for `v = true` and 0 for `v = false` (for Theorem 21(a), after
[CH20, Theorem 5.1]).  The first set of the splitting holds the values whose label x + V has the
binary digit β equal to v; the second and the third hold those whose digit β differs from v and
whose digit β' is 0 and 1 (`splitA`, `splitB`).  The routine selects the three sets by their binary
digits, writes them to `A`, `A + n` and `A + 2n`, and calls the recursive
procedure on them (`round_spec`).

What the memory holds while the splittings are run through (`FrontMem`) does not depend on the 3n
cells from `A` (`FrontMem.keptBut`).  So each of the three calls of pick finds what it needs
(`FrontMem.pick_meets`), and afterwards the three sets and the rest form the memory of a node
(`FrontMem.nodeMem`).  The time is `le_tRound`, with `ChRound.treeCalls_le_pow` for the number of
calls of the recursive procedure.
-/

@[expose] public section

namespace Light.Sec3.ChanHe

open ThreeSumApsp.ChanHe Finset

variable {lim : Limits} {P : Program} {d : ℕ}

namespace RoundLocals

/-- The local variables of round: the arguments β, β', b, nd, val, bt, Λ, A, n, f, cx, fr; then
1 - b, A + n, A + 2n, and the sizes of the three sets. -/
registers [BETA, BETA', BIT, NVALUES, VAL, BITS, LAM, OUT0, NMAX, LEVELS, CTX, FREE, NBIT, OUT1,
  OUT2, SIZE0, SIZE1, SIZE2]

end RoundLocals

open RoundLocals in
/-- Select the three sets, then call the recursive solver. -/
def roundBody (pPick pNodes : ℕ) : Stmt :=
  .set NBIT (k 1 -' v BIT) ;;
  .set OUT1 (v OUT0 +' v NMAX) ;;
  .set OUT2 (v OUT1 +' v NMAX) ;;
  .call pPick [v NVALUES, v VAL, v BITS, v LAM, v BETA, v BIT, v BETA', k 0, k 0, v OUT0] SIZE0 ;;
  .call pPick [v NVALUES, v VAL, v BITS, v LAM, v BETA, v NBIT, v BETA', k 0, k 1, v OUT1] SIZE1 ;;
  .call pPick [v NVALUES, v VAL, v BITS, v LAM, v BETA, v NBIT, v BETA', k 1, k 1, v OUT2] SIZE2 ;;
  .call pNodes [v LEVELS, v OUT0, v SIZE0, v OUT1, v SIZE1, v OUT2, v SIZE2, v CTX, v FREE] 0

/-- The recursive procedure makes at most `2 · 3^f` calls. -/
theorem ChRound.treeCalls_le_pow (Q : Finset ℕ) (Λ f : ℕ) (S₁ S₂ S₃ : Finset ℤ) :
    treeCalls Q Λ f S₁ S₂ S₃ ≤ 2 * 3 ^ f := by
  have hcalls := treeCalls_le Q Λ f S₁ S₂ S₃
  have hnodes := length_nodes_le Q Λ f S₁ S₂ S₃
  omega

section front

variable {μ μ' : ℕ → ℤ} {a : FrontArgs}

/-- What the memory holds while the splittings are run through is kept if, below the free pointer,
only the 3n cells from A change. -/
theorem FrontMem.keptBut (h : FrontMem μ a)
    (hk : KeptBut μ μ' a.fr a.A (3 * a.n)) : FrontMem μ' a := by
  have ho := h.layout
  simp only [InOrder] at ho
  have hlen := h.lenD
  have hbt := length_bitTable a.V a.Λ a.D
  have hpr := h.primes.1
  exact { h with
    segVal := h.segVal.keep (by light_keep [hlen])
    segBt := h.segBt.keep (by light_keep [hbt, hlen])
    ctx := Seg.keep h.ctx (by light_keep)
    primes := ⟨hpr, h.primes.2.keep fun b hb => by
      simp only [Inside, List.length_map, length_sort, ← hpr] at hb
      exact hk b (by omega)⟩
    zero := fun i hi => (hk _ (by omega)).trans (h.zero i hi) }

/-- The same if only the 3n cells from A change at all. -/
theorem FrontMem.of_sameOutside (h : FrontMem μ a)
    (hs : SameOutside μ μ' a.A (3 * a.n)) : FrontMem μ' a :=
  h.keptBut (SameOn.mono hs fun _ hb => hb.2)

/-- pick, called for the distinct values, with the output in one of the three parts of the 3n
cells from A. -/
theorem FrontMem.pick_meets (h : FrontMem μ a) {pPick : ℕ}
    (hPick : PickSpec lim P pPick) {β β' o : ℕ} (hβ : β < a.Λ) (hβ' : β' < a.Λ) (x x' two : ℤ)
    (ho : o + a.n ≤ 3 * a.n) (hfr : a.fr ≤ lim.space) (hw : (lim.space : ℤ) ≤ lim.word)
    (hword : (8 : ℤ) ≤ lim.word) :
    Meets lim P pPick d [a.nd, a.val, a.bt, a.Λ, β, x, β', x', two, (a.A + o : ℕ)] μ (tPick a.nd)
      fun r μ' =>
      r = ((pickList a.Λ β β' x x' two a.D (bitTable a.V a.Λ a.D)).length : ℤ) ∧
        Seg μ' (a.A + o) (pickList a.Λ β β' x x' two a.D (bitTable a.V a.Λ a.D)) ∧
        SameOutside μ μ' (a.A + o) a.nd := by
  light_facts h
  simp only [InOrder] at *
  have hrows : a.D.length * a.Λ = a.nd * a.Λ := by simp_all
  rw [← h.lenD]
  exact hPick d a.val a.bt (a.A + o) a.Λ β β' x x' two a.D _ μ {
    lenTable := length_bitTable a.V a.Λ a.D
    posA := hβ
    posB := hβ'
    segSrc := h.segVal
    segTable := h.segBt
    apartSrc := by omega
    apartTable := by omega
    spaceSrc := by omega
    spaceTable := by omega
    spaceOut := by omega
    space_le := hw
    word := hword }

/-- Three subsets of the distinct values in the three parts of the 3n cells from A, with the rest of
the memory, are the memory of a node. -/
theorem FrontMem.nodeMem (h : FrontMem μ a)
    {k₁ k₂ k₃ : ℕ} {S₁ S₂ S₃ : Finset ℤ} (h₁ : SetAt μ a.A k₁ S₁) (h₂ : SetAt μ (a.A + a.n) k₂ S₂)
    (h₃ : SetAt μ (a.A + a.n + a.n) k₃ S₃) (hk₁ : k₁ ≤ a.n) (hk₂ : k₂ ≤ a.n) (hk₃ : k₃ ≤ a.n)
    (hS₁ : S₁ ⊆ a.D.toFinset) (hS₂ : S₂ ⊆ a.D.toFinset) (hS₃ : S₃ ⊆ a.D.toFinset) :
    NodeMem μ ⟨a.toEnv, ![⟨a.A, k₁, S₁⟩, ⟨a.A + a.n, k₂, S₂⟩, ⟨a.A + a.n + a.n, k₃, S₃⟩]⟩ := by
  light_facts h
  simp only [InOrder] at *
  exact
    { envOk := ⟨h.primes, h.zero, by change a.pr + a.np ≤ a.fr; omega,
        by change a.cnt + a.m * a.m ≤ a.fr; omega,
        .inl (by change a.pr + a.np ≤ a.cnt; omega)⟩
      slotOk := fun i => by
        rcases slot_cases i with rfl | rfl | rfl
        exacts [⟨h₁, hk₁, h.bdd.mono hS₁, by change a.A + k₁ ≤ a.fr; omega,
                    by light_side⟩,
          ⟨h₂, hk₂, h.bdd.mono hS₂, by change a.A + a.n + k₂ ≤ a.fr; omega,
                    by light_side⟩,
          ⟨h₃, hk₃, h.bdd.mono hS₃, by light_side,
                    by light_side⟩] }

end front

/-- The time of round covers three calls of pick and the recursion tree: 48 steps and the three
calls for the three sets, 11 steps and the tree for the last call. -/
theorem le_tRound (T : ℕ → ℕ → ℕ) {n nd : ℕ} (hnd : nd ≤ n) (V m np Λ f : ℕ)
    (S₁ S₂ S₃ : Finset ℤ) :
    59 + 3 * tPick nd + tNodes T n V m np (treeCalls (Nat.primesLE m) Λ f S₁ S₂ S₃)
      ≤ tRound T n V m np f := by
  have hpick : tPick nd ≤ tPick n := by simp only [tPick]; omega
  have htree := Nat.mul_le_mul_right (tNode T n V m np + 60)
    (ChRound.treeCalls_le_pow (Nat.primesLE m) Λ f S₁ S₂ S₃)
  light_side [tRound, tTree, tNodes, htree]

/-- **round meets its specification**, in every program that holds its body and meets the
specifications of the two routines that it calls. -/
theorem round_spec {p pPick pNodes : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}
    (hP : P[p]? = some (roundBody pPick pNodes)) (hPick : PickSpec lim P pPick)
    (hN : NodesSpec lim P pNodes T r) : RoundSpec lim P p T r := by
  intro a f β β' v μ hF hβ hβ' d H
  refine .of_body hP ?_
  have hw := H.ok.space
  have hcells := H.ok.cells
  have hword := H.ok.word
  have hdepth := H.ok.depth
  simp only [gridNeed] at hcells hword hdepth
  push_cast at hword
  have htime := le_tRound T hF.nd_le a.V a.m a.np a.Λ f (splitA a.V β v a.D.toFinset)
    (splitB a.V β β' v false a.D.toFinset) (splitB a.V β β' v true a.D.toFinset)
  unfold roundBody
  have hA := hF.layout
  have hfr : a.fr ≤ lim.space := by omega
  have hd : d < lim.depth := by omega
  have h8 : (8 : ℤ) ≤ lim.word := by omega
  simp only [InOrder] at hA
  have hndn := hF.nd_le
  have hlen : ∀ x x' two, (pickList a.Λ β β' x x' two a.D (bitTable a.V a.Λ a.D)).length ≤ a.n :=
    fun x x' two => (length_pickList_le a.Λ β β' x x' two a.D (bitTable a.V a.Λ a.D)).trans
      (hF.lenD ▸ hndn)
  -- b' := 1 - b; A₁ := A + n; A₂ := A₁ + n
  refine Ends.setToThen (if !v then 1 else 0) ?_ (by cases v <;> simp <;> omega)
  light_set (a.A + a.n : ℕ)
  light_set (a.A + a.n + a.n : ℕ)
  -- n₀ := pick(nd, val, bt, Λ, β, b, β', 0, 0, A)
  light_call (hF.pick_meets (o := 0) hPick hβ hβ' (if v then 1 else 0) 0 0
    (by omega) hfr hw h8) with _ μ₁ ⟨rfl, seg₁, same₁⟩
  have out₁ : SameOutside μ μ₁ a.A (3 * a.n) := same₁.mono (by omega) (by omega)
  have hF₁ := hF.of_sameOutside out₁
  -- n₁ := pick(nd, val, bt, Λ, β, b', β', 0, 1, A₁)
  light_call (hF₁.pick_meets (o := a.n) hPick hβ hβ' (if !v then 1 else 0) 0 1
    (by omega) hfr hw h8) with _ μ₂ ⟨rfl, seg₂, same₂⟩
  have out₂ : SameOutside μ₁ μ₂ a.A (3 * a.n) := same₂.mono (by omega) (by omega)
  have hF₂ := hF₁.of_sameOutside out₂
  -- n₂ := pick(nd, val, bt, Λ, β, b', β', 1, 1, A₂)
  light_call (hF₂.pick_meets (o := a.n + a.n) hPick hβ hβ' (if !v then 1 else 0) 1 1
    (by omega) hfr hw h8) with _ μ₃ ⟨rfl, seg₃, same₃⟩
  have out₃ : SameOutside μ₂ μ₃ a.A (3 * a.n) := same₃.mono (by omega) (by omega)
  -- The three lists are the three sets of the splitting.  (For the first set pick looks at one
  -- digit only, and the 0 stands for the value of the other digit, which it ignores.)
  obtain ⟨nodup₁, set₁⟩ := pick_splitA a.V a.Λ hβ hβ' v 0 hF.nodup
  obtain ⟨nodup₂, set₂⟩ := pick_splitB a.V a.Λ hβ hβ' v false hF.nodup
  obtain ⟨nodup₃, set₃⟩ := pick_splitB a.V a.Λ hβ hβ' v true hF.nodup
  have hlen₁ := hlen (if v then 1 else 0) 0 0
  have hlen₂ := hlen (if !v then 1 else 0) 0 1
  have out := out₁.trans (out₂.trans out₃)
  have hF₃ := hF₂.of_sameOutside out₃
  have hmem := hF₃.nodeMem
    ⟨_, rfl, (seg₁.of_sameOutside same₂ (by omega)).of_sameOutside same₃ (by omega), nodup₁, set₁⟩
    ⟨_, rfl, seg₂.of_sameOutside same₃ (by omega), nodup₂, set₂⟩
    ⟨_, rfl, Nat.add_assoc a.A a.n a.n ▸ seg₃, nodup₃, set₃⟩ hlen₁ hlen₂ (hlen _ _ _)
    (Finset.filter_subset _ _) (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  -- return nodes(f, A, n₀, A₁, n₁, A₂, n₂, cx, fr)
  light_call (hN f _ a.Λ a.cx μ₃ (d + 1)
    { mem := hmem
      ctx := hF₃.ctx
      belowCtx := by change a.cx + 6 ≤ a.fr; omega
      apartCtx := .inl (by change a.cx + 6 ≤ a.cnt; omega)
      V_pos := H.V_pos
      m_pos := H.m_pos
      lam := H.lam
      primes := H.primes
      ok := { word := by lia, cells := hcells, space := hw,
              depth := by lia } })
    using NodeArgs.calls with _ μ₂ ⟨rfl, kept⟩
  exact ⟨by rfl, out.then kept fun b hb => ⟨hb.2, hb.1⟩⟩

end Light.Sec3.ChanHe
