/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

import ThreeSumApsp.Lang.Registers

import Mathlib.Tactic.FinCases

public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.NodeMemory
public import ThreeSumApsp.Programs.Tasks
public import ThreeSumApsp.Sec3.Theorem21a.ChanHe.Sizes

/-!
# The recursion tree of the reduction from 3SUM to Convolution-3SUM

Theorem 21(a), after [CH20, Theorem 5.1].
nodes(f, s₁, l₁, s₂, l₂, s₃, l₃, cx, fr) runs through the first f levels of the recursion tree whose
root is the triple of sets at s₁, s₂, s₃ (`ChanHe.nodes`), depth first, and asks a solver of
Convolution-3SUM for the one-array instance of each node.  It returns 1 if one of the answers is
yes, and 0 if not (`nodes_spec`, by induction on f).

The proof follows the parts of the procedure.
* The parameters are read from a block in the memory (`nodesParams_ends`).
* At a node the procedure computes the modulus, writes the array at the free pointer and calls the
  solver (`c3_meets`).
* For each of the three sets in turn it writes the heavy elements of the set at the free pointer,
  where the array is no longer needed, and calls itself with the heavy elements in place of the set
  (`nodesChild_ends`, `NodesPre.child`).
* The answer is accumulated by stopping at the first successful child (`NodeArgs.yes_succ`).
The time of the assembled node is `tNodes_succ_le`.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3.ChanHe

open ThreeSumApsp.ChanHe ThreeSumApsp.Spec Finset

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Pure facts -/

/-- Convolution-3SUM holds of the list of the first `N` cells of an array if and only if `ConvOne N`
holds of the array. -/
theorem conv_range_iff (N : ℕ) (y : ℕ → ℤ) :
    Convolution3SUM (vecOf N ((List.range N).map y)) ↔ ConvOne N y := by
  have : vecOf N ((List.range N).map y) = fun i : Fin N => y i := by
    funext i
    unfold vecOf
    simp
  rw [this]
  exact convolution3SUM_iff_convOne N y

/-- The number of binary digits of the labels is at most V + 2. -/
theorem lam_le (V : ℕ) : Lam V ≤ V + 2 := by
  unfold Lam
  rcases Nat.eq_zero_or_pos V with rfl | h
  · simp
  · have : Nat.log 2 (2 * V) = Nat.log 2 V + 1 := by
      rw [Nat.mul_comm, Nat.log_mul_base (by norm_num) (by omega)]
    have h2 : Nat.log 2 V < V := Nat.log_lt_self 2 (by omega)
    omega

/-! ## The procedure -/

namespace NodesLocals

/-- The local variables of nodes: the arguments f, s₁, l₁, s₂, l₂, s₃, l₃, cx, fr; the parameters V,
m, Λ, np, pr, cnt, read from the block at cx; the modulus M; the length 8m² of the array; the free
pointer behind the array; the result of nodeArray, which is not used and is replaced by the number of heavy elements in each child; and the accumulated answer.  At the end local 0
receives the result, as in every procedure. -/
registers [LEVELS, SET1, LEN1, SET2, LEN2, SET3, LEN3, CTX, FREE, VMAX, MMAX, LAM, NPRIMES,
  PRIMES, CNT, MOD, LEN, FR2, RES / HEAVY, ANSWER]

end NodesLocals

open NodesLocals in
/-- The parameters are read from the block at cx. -/
def nodesParams : Stmt :=
  .set VMAX (M (v CTX)) ;;
  .set MMAX (M (v CTX +' k 1)) ;;
  .set LAM (M (v CTX +' k 2)) ;;
  .set NPRIMES (M (v CTX +' k 3)) ;;
  .set PRIMES (M (v CTX +' k 4)) ;;
  .set CNT (M (v CTX +' k 5))

open NodesLocals in
/-- The node itself: its modulus, its array at the free pointer, and the answer of the solver. -/
def nodesOwn (pMod pArr pC3 : ℕ) : Stmt :=
  .call pMod
      [v SET1, v LEN1, v SET2, v LEN2, v SET3, v LEN3, v LAM, v NPRIMES, v PRIMES, v CNT, v FREE]
      MOD ;;
  .set LEN (k 8 *' (v MMAX *' v MMAX)) ;;
  .set FR2 (v FREE +' v LEN) ;;
  .call pArr
      [v MOD, v SET1, v LEN1, v SET2, v LEN2, v SET3, v LEN3, v VMAX, v MMAX, v FREE, v CNT, v FR2]
      RES ;;
  .call pC3 [v LEN, k 60 *' v VMAX +' k 40, v FREE, v FR2] ANSWER

abbrev setReg (i : Fin 3) : ℕ := 1 + 2 * i.val
abbrev lenReg (i : Fin 3) : ℕ := setReg i + 1

open NodesLocals in
/-- Unless a witness has already been found, replace set `i` by its heavy elements and recurse. -/
def nodesChild (i : Fin 3) (pSelf pHeavy : ℕ) : Stmt :=
  .ite (v ANSWER =' k 0)
    (.call pHeavy [v (lenReg i), v (setReg i), v MOD, v FREE, v CNT, v FREE +' v (lenReg i)] HEAVY ;;
     .call pSelf
       ((v LEVELS -' k 1) :: (List.ofFn fun j : Fin 3 =>
         if j = i then [v FREE, v HEAVY] else [v (setReg j), v (lenReg j)]).flatten ++
         [v CTX, v FREE +' v (lenReg i)]) ANSWER)
    .skip

open NodesLocals in
/-- A triple of nonempty sets with at least one level to go. -/
def nodesMain (pSelf pMod pArr pC3 pHeavy : ℕ) : Stmt :=
  nodesParams ;; nodesOwn pMod pArr pC3 ;; nodesChild 0 pSelf pHeavy ;; nodesChild 1 pSelf pHeavy ;;
  nodesChild 2 pSelf pHeavy ;; .set LEVELS (v ANSWER)

open NodesLocals in
/-- nodes(f, s₁, l₁, s₂, l₂, s₃, l₃, cx, fr), over the procedures pSelf (itself), pMod (modulus),
pArr (nodeArray), pC3 (a solver of Convolution-3SUM), pHeavy (heavy): the answer is 0 if no level is
left or one of the sets is empty. -/
def nodesBody (pSelf pMod pArr pC3 pHeavy : ℕ) : Stmt :=
  .ite (v LEVELS =' k 0) (.set 0 (k 0)) (
  .ite (v LEN1 =' k 0) (.set 0 (k 0)) (
  .ite (v LEN2 =' k 0) (.set 0 (k 0)) (
  .ite (v LEN3 =' k 0) (.set 0 (k 0)) (nodesMain pSelf pMod pArr pC3 pHeavy))))

/-- What the procedure assumes about the program: it begins with the program of a solver of
Convolution-3SUM, holds the procedure itself, and meets the specifications of the three routines
that the procedure calls. -/
structure NodesCtx (lim : Limits) (P₀ R : Program) (p pMod pArr pC3 pHeavy : ℕ) (T : ℕ → ℕ → ℕ)
    (r : ℕ → ℕ → Need) : Prop where
  solver : Solves c3Task P₀ pC3 T r
  self : (P₀ ++ R)[p]? = some (nodesBody p pMod pArr pC3 pHeavy)
  modulus : ModulusSpec lim (P₀ ++ R) pMod
  array : NodeArraySpec lim (P₀ ++ R) pArr
  heavy : HeavySpec lim (P₀ ++ R) pHeavy

/-- The number of calls of the procedure is at most three times the number of nodes, plus one. -/
theorem treeCalls_le (Q : Finset ℕ) (Λ f : ℕ) (S₁ S₂ S₃ : Finset ℤ) :
    treeCalls Q Λ f S₁ S₂ S₃ ≤ 3 * (nodes Q Λ f S₁ S₂ S₃).length + 1 := by
  induction f generalizing S₁ S₂ S₃ <;> grind [treeCalls, nodes]

/-- The procedure is called at least once. -/
theorem one_le_treeCalls (Q : Finset ℕ) (Λ f : ℕ) (S₁ S₂ S₃ : Finset ℤ) :
    1 ≤ treeCalls Q Λ f S₁ S₂ S₃ := by
  cases f <;> grind [treeCalls]

/-! ## Needs and times -/

section needs

variable {r : ℕ → ℕ → Need} {fr n V m f l M : ℕ}

/-- What is allowed at a node covers what modulus needs. -/
theorem modulusNeed_ok (h : (nodesNeed r n V m (f + 1)).Ok lim fr d) :
    (modulusNeed n V m).Ok lim fr (d + 1) := by
  refine h.mono ?_ ?_ ?_ <;> simp only [nodesNeed] <;> omega

/-- What is allowed at a node covers what nodeArray needs behind the array. -/
theorem nodeArrayNeed_ok (h : (nodesNeed r n V m (f + 1)).Ok lim fr d) :
    (nodeArrayNeed n V m).Ok lim (fr + 8 * m ^ 2) (d + 1) := by
  refine h.mono ?_ ?_ ?_ <;> simp only [nodesNeed, nodeArrayNeed, modulusNeed] <;> omega

/-- What is allowed at a node covers what the solver needs behind the array. -/
theorem solverNeed_ok (h : (nodesNeed r n V m (f + 1)).Ok lim fr d) :
    (r (8 * m ^ 2) (60 * V + 40)).Ok lim (fr + 8 * m ^ 2) (d + 1) := by
  refine h.mono ?_ ?_ ?_ <;> simp only [nodesNeed] <;> omega

/-- What is allowed at a node covers what heavy needs behind its output. -/
theorem collNeed_ok (h : (nodesNeed r n V m (f + 1)).Ok lim fr d) (hl : l ≤ n) (hM : M ≤ m * m) :
    (collNeed l V M).Ok lim (fr + l) (d + 1) := by
  have hsucc : (f + 1) * n = f * n + n := by ring
  have hword := wordNeed_mono (V := V) hl hM
  refine h.mono ?_ ?_ ?_ <;> simp only [nodesNeed, collNeed, modulusNeed] <;> omega

/-- What is allowed at a node covers what a child needs behind its set of heavy elements. -/
theorem childNeed_ok (h : (nodesNeed r n V m (f + 1)).Ok lim fr d) (hl : l ≤ n) :
    (nodesNeed r n V m f).Ok lim (fr + l) (d + 1) := by
  have hsucc : (f + 1) * n = f * n + n := by ring
  refine h.mono ?_ ?_ ?_ <;> simp only [nodesNeed] <;> omega

private theorem tHeavy_mono {l n : ℕ} (h : l ≤ n) (V : ℕ) : tHeavy l V ≤ tHeavy n V := by
  unfold tHeavy tCount tClear
  gcongr

private theorem tModulus_mono {l₁ l₂ l₃ n : ℕ} (h₁ : l₁ ≤ n) (h₂ : l₂ ≤ n) (h₃ : l₃ ≤ n) (np V : ℕ) :
    tModulus np l₁ l₂ l₃ V ≤ tModulus np n n n V := by
  unfold tModulus tSearch tColl tCount tClear
  gcongr

private theorem tNodeArray_mono {l₁ l₂ l₃ n : ℕ} (h₁ : l₁ ≤ n) (h₂ : l₂ ≤ n) (h₃ : l₃ ≤ n) (m V : ℕ) :
    tNodeArray m l₁ l₂ l₃ V ≤ tNodeArray m n n n V := by
  unfold tNodeArray tCount tClear
  gcongr

end needs

/-! ## The parts of the procedure -/

section parts

variable {P₀ R : Program} {p pMod pArr pC3 pHeavy : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}
  {a : NodeArgs} {Λ cx f Mo : ℕ} {μ μ₀ μ' : ℕ → ℤ}

/-- What the limits allow at a node: an address fits in a word; behind the free pointer there is
room for a set and the array; the number of levels is at most the number of cells, so that it fits
in a word; the numbers up to 64 (V + 1) and 64 (m² + 1) fit in a word; and one more level of calls
is allowed. -/
structure NodesFits (lim : Limits) (d fr n V m f : ℕ) : Prop where
  space_le : (lim.space : ℤ) ≤ lim.word
  room : fr + n + 8 * (m * m) ≤ lim.space
  levels : f ≤ lim.space
  wordV : 64 * ((V : ℤ) + 1) ≤ lim.word
  wordM : 64 * ((m : ℤ) * m + 1) ≤ lim.word
  depth : d < lim.depth

/-- What the procedure assumes provides what the limits have to allow at a node. -/
theorem NodesPre.fits (H : NodesPre lim r μ a Λ cx (f + 1) d) (hn : 1 ≤ a.n) :
    NodesFits lim d a.fr a.n a.V a.m f := by
  have hcells := H.ok.cells
  have hdepth := H.ok.depth
  have hword : ((wordNeed a.n a.V (a.m * a.m) : ℕ) : ℤ) ≤ lim.word :=
    le_trans (by exact_mod_cast le_max_left _ _) H.ok.word
  simp only [nodesNeed] at hcells hdepth
  have hlevels : f ≤ f * a.n := Nat.le_mul_of_pos_right f hn
  have hsucc : (f + 1) * a.n = f * a.n + a.n := by ring
  have hsq : a.m ^ 2 = a.m * a.m := pow_two a.m
  have hone : 1 ≤ (a.n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  refine ⟨H.ok.space, by omega, by omega, ?_, ?_, by omega⟩
  · simpa using mul_le_word (x := 1) (y := 1) (z := 64 * (a.V + 1)) hword hone (by omega) le_rfl
  · have h := mul_le_word (x := 1) (y := a.m * a.m + 1) (z := 64) hword hone le_rfl (by omega)
    push_cast at h
    linarith

/-- The child satisfies the precondition at the next depth and with one fewer level. -/
theorem NodesPre.child (H : NodesPre lim r μ₀ a Λ cx (f + 1) d) (i : Fin 3)
    (kept : Kept μ₀ μ a.fr)
    (hk : KeptBut μ μ' (a.fr + (a.slot i).len) a.fr (a.slot i).len)
    (hs : SetAt μ' a.fr #(ChanHe.heavy (a.slot i).set Mo) (ChanHe.heavy (a.slot i).set Mo)) :
    NodesPre lim r μ' (a.child i Mo) Λ cx f (d + 1) :=
  { H with
    mem := (H.mem.kept kept).child i hk hs
    ctx := H.ctx.kept H.belowCtx (kept.then hk fun b hb => by omega)
    belowCtx := H.belowCtx.trans (Nat.le_add_right _ _)
    ok := childNeed_ok H.ok (H.mem.slotOk i).le }

/-- The list of the local variables of nodes: the arguments, with x for the number of levels; the
parameters that are read from the block at cx; and the list t of what has been computed since. -/
@[simp] abbrev nodesLocals (x : ℤ) (a : NodeArgs) (Λ cx : ℕ) (t : List ℤ) : List ℤ :=
  x :: a.sets ++ [(cx : ℤ), a.fr, a.V, a.m, Λ, a.np, a.pr, a.cnt] ++ t

/-- **The parameters** are read from the block at cx. -/
theorem nodesParams_ends (hctx : CtxAt μ cx a.V a.m Λ a.np a.pr a.cnt) (hcx : cx + 6 ≤ lim.space)
    (hw : (lim.space : ℤ) ≤ lim.word) {x : ℤ} :
    Ends lim P d nodesParams ⟨frame (x :: a.sets ++ [(cx : ℤ), a.fr]), μ⟩ 28 fun σ' =>
      σ' = ⟨frame (nodesLocals x a Λ cx []), μ⟩ := by
  have hV : μ cx = a.V := by simpa using hctx 0 (by simp)
  have hm : μ (cx + 1) = a.m := by simpa using hctx 1 (by simp)
  have hΛ : μ (cx + 2) = Λ := by simpa using hctx 2 (by simp)
  have hnp : μ (cx + 3) = a.np := by simpa using hctx 3 (by simp)
  have hpr : μ (cx + 4) = a.pr := by simpa using hctx 4 (by simp)
  have hcnt : μ (cx + 5) = a.cnt := by simpa using hctx 5 (by simp)
  -- the address cx + j as a natural number
  have haddr : ∀ j : ℤ, 0 ≤ j → ((cx : ℤ) + j).toNat = cx + j.toNat := fun j hj => by omega
  -- V := mem[cx]; m := mem[cx + 1]; Λ := mem[cx + 2]
  light_set a.V using hV
  light_set a.m using hm
  light_set Λ using haddr, hΛ
  -- np := mem[cx + 3]; pr := mem[cx + 4]; cnt := mem[cx + 5]
  light_set a.np using haddr, hnp
  light_set a.pr using haddr, hpr
  light_set a.cnt using haddr, hcnt
  rfl

/-- The solver of Convolution-3SUM, called for the array of a node at the free pointer. -/
theorem c3_meets (hsol : Solves c3Task P₀ pC3 T r) (hV : 1 ≤ a.V) (hm : 1 ≤ a.m)
    (hN : NodeMem μ₀ a) (harr : ∀ u < 8 * a.m ^ 2, μ (a.fr + u) = (a.node Mo).oneArray a.V u)
    (hok : (r (8 * a.m ^ 2) (60 * a.V + 40)).Ok lim (a.fr + 8 * a.m ^ 2) d) :
    Meets lim (P₀ ++ R) pC3 d
      [(8 * a.m ^ 2 : ℕ), (60 * a.V + 40 : ℕ), a.fr, (a.fr + 8 * a.m ^ 2 : ℕ)] μ
      (T (8 * a.m ^ 2) (60 * a.V + 40)) fun res μ' =>
        res = flag (ConvOne (8 * a.m ^ 2) ((a.node Mo).oneArray a.V)) ∧
          Kept μ μ' (a.fr + 8 * a.m ^ 2) := by
  have hpos : 1 ≤ a.m ^ 2 := Nat.one_le_pow _ _ hm
  refine (hsol.meets R (⟨8 * a.m ^ 2, 60 * a.V + 40, a.fr,
    (List.range (8 * a.m ^ 2)).map fun u => (a.node Mo).oneArray a.V u⟩ : VecInst)
    (a.fr + 8 * a.m ^ 2) ⟨?_, ?_, by simp, ?_, ?_, le_rfl⟩ hok).mono le_rfl ?_
  · -- the length is positive
    change 1 ≤ 8 * a.m ^ 2
    omega
  · -- the bound is positive
    change 1 ≤ 60 * a.V + 40
    omega
  · -- the list stands at fr
    intro u hu
    simp [harr u (by simpa using hu)]
  · -- its entries are bounded
    intro e he
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 he
    have := Node.abs_oneArray_le (ν := a.node Mo) (hN.slotOk 0).bdd (hN.slotOk 1).bdd (hN.slotOk 2).bdd u
    push_cast
    exact this
  · rintro _ μ' ⟨rfl, kept⟩
    exact ⟨flag_congr (conv_range_iff _ _), kept⟩

private abbrev nodesAccum (x : ℤ) (a : NodeArgs) (Λ cx Mo : ℕ) (w b : ℤ) : List ℤ :=
  nodesLocals x a Λ cx [Mo, (8 * a.m ^ 2 : ℕ), (a.fr + 8 * a.m ^ 2 : ℕ), w, b]

/-- Execute one child, preserving a previously found witness. -/
private theorem nodesChild_ends (C : NodesCtx lim P₀ R p pMod pArr pC3 pHeavy T r)
    (ih : NodesSpecAt lim (P₀ ++ R) p T r f) (H : NodesPre lim r μ₀ a Λ cx (f + 1) d)
    (hn : 1 ≤ a.n) (kept : Kept μ₀ μ a.fr) (hM1 : 1 ≤ Mo) (hM : Mo ≤ a.m * a.m)
    (i : Fin 3) {w : ℤ} {B : Prop} :
    Ends lim (P₀ ++ R) d (nodesChild i p pHeavy)
      ⟨frame (nodesAccum (f + 1 : ℕ) a Λ cx Mo w (flag B)), μ⟩
      (29 + tHeavy (a.slot i).len a.V + tNodes T a.n a.V a.m a.np ((a.child i Mo).calls Λ f))
      fun σ' => ∃ w' ν, Kept μ₀ ν a.fr ∧
        σ' = ⟨frame (nodesAccum (f + 1 : ℕ) a Λ cx Mo w'
          (flag (B ∨ (a.child i Mo).Yes Λ f))), ν⟩ := by
  have hfits := H.fits hn
  have hroom := hfits.room
  have henv := (H.mem.kept kept).envOk
  have hX := (H.mem.kept kept).slotOk i
  have hle := hX.le
  have hbelow := hX.below
  have hcard := card_heavy_le hX.set Mo
  light_facts hfits
  unfold nodesChild
  have hflag : flag B = 0 ↔ ¬ B := by by_cases h : B <;> simp [flag_of, flag_of_not, h]
  refine Ends.iteIffLast (¬ B) (fun hno => ?_) (fun hyes => ?_) (by light_side [hflag])
  · refine Ends.callToThen (C.heavy (d + 1) (a.fr + (a.slot i).len) _ _ _ _ a.fr _ _ _ μ
      ((hX.push .refl).bucket (henv.push .refl) hM1 hM)
      ⟨le_rfl, Or.inl hbelow, Or.inr henv.belowCnt⟩ (collNeed_ok H.ok hle hM)) ?_
      (ha := by rcases slot_cases i with rfl | rfl | rfl <;> light_side [setReg, lenReg])
    rintro _ ν ⟨rfl, hs, h₁⟩
    refine Ends.callTo (ih (a.child i Mo) Λ cx ν (d + 1) (H.child i kept h₁ hs)) ?_
      (ha := by
        rcases slot_cases i with rfl | rfl | rfl <;>
          light_side [setReg, lenReg, NodeArgs.child, List.ofFn_succ, Function.update_apply])
      (hT := by dsimp only [NodeArgs.child, Env.push]; fin_cases i <;> light_time [List.ofFn_succ])
    rintro _ ν' ⟨rfl, h₂⟩
    change Kept ν ν' (a.fr + (a.slot i).len) at h₂
    refine ⟨#(ChanHe.heavy (a.slot i).set Mo), ν',
      (kept.then h₁ fun c hc => by omega).then h₂ (fun c hc => by omega), ?_⟩
    simp only [hno, false_or]
    rfl
  · have hb : B := not_not.mp hyes
    exact Ends.skip ⟨w, μ, kept, by rw [flag_of hb, flag_of (Or.inl hb)]⟩

/-- Time of a node including the tests, the local work and the three subtrees. -/
theorem tNodes_succ_le (hN : NodeMem μ a) (hS : ¬ ((a.slot 0).set = ∅ ∨ (a.slot 1).set = ∅ ∨ (a.slot 2).set = ∅))
    (hMo : Mo = ChanHe.modulus (Nat.primesLE a.m) Λ (a.slot 0).set (a.slot 1).set (a.slot 2).set) :
    180 + tModulus a.np (a.slot 0).len (a.slot 1).len (a.slot 2).len a.V +
      tNodeArray a.m (a.slot 0).len (a.slot 1).len (a.slot 2).len a.V + T (8 * a.m ^ 2) (60 * a.V + 40) +
      tHeavy (a.slot 0).len a.V + tHeavy (a.slot 1).len a.V + tHeavy (a.slot 2).len a.V +
      tNodes T a.n a.V a.m a.np ((a.child 0 Mo).calls Λ f) +
      tNodes T a.n a.V a.m a.np ((a.child 1 Mo).calls Λ f) +
      tNodes T a.n a.V a.m a.np ((a.child 2 Mo).calls Λ f)
    ≤ tNodes T a.n a.V a.m a.np (a.calls Λ (f + 1)) := by
  have hmod := tModulus_mono (hN.slotOk 0).le (hN.slotOk 1).le (hN.slotOk 2).le a.np a.V
  have harr := tNodeArray_mono (hN.slotOk 0).le (hN.slotOk 1).le (hN.slotOk 2).le a.m a.V
  have hheavy₁ := tHeavy_mono (hN.slotOk 0).le a.V
  have hheavy₂ := tHeavy_mono (hN.slotOk 1).le a.V
  have hheavy₃ := tHeavy_mono (hN.slotOk 2).le a.V
  have hcalls : a.calls Λ (f + 1) =
      1 + ((a.child 0 Mo).calls Λ f + (a.child 1 Mo).calls Λ f + (a.child 2 Mo).calls Λ f) := by
    simp [NodeArgs.calls, NodeArgs.child, treeCalls, if_neg hS, ← hMo]
  simp only [hcalls, tNodes, Nat.add_mul, Nat.one_mul, tNode]
  omega

/-- The nodes of a tree with a nonempty root: the root and the nodes of the three subtrees. -/
theorem NodeArgs.yes_succ (hS : ¬ ((a.slot 0).set = ∅ ∨ (a.slot 1).set = ∅ ∨ (a.slot 2).set = ∅))
    (hMo : Mo = ChanHe.modulus (Nat.primesLE a.m) Λ (a.slot 0).set (a.slot 1).set (a.slot 2).set) :
    a.Yes Λ (f + 1) ↔ ((ConvOne (8 * a.m ^ 2) ((a.node Mo).oneArray a.V) ∨
      (a.child 0 Mo).Yes Λ f) ∨ (a.child 1 Mo).Yes Λ f) ∨ (a.child 2 Mo).Yes Λ f := by
  simp only [NodeArgs.Yes, TreeYes, NodeArgs.child, Function.update_apply, Slot.heavy,
    Env.push, nodes, if_neg hS, ← hMo, List.mem_cons, List.mem_append, or_and_right, exists_or,
    exists_eq_left, or_assoc]
  rfl

end parts

/-- **The recursion tree**: the procedure meets its specification. -/
theorem nodes_spec {P₀ R : Program} {p pMod pArr pC3 pHeavy : ℕ} {T : ℕ → ℕ → ℕ}
    {r : ℕ → ℕ → Need} (C : NodesCtx lim P₀ R p pMod pArr pC3 pHeavy T r) :
    NodesSpec lim (P₀ ++ R) p T r := by
  intro f
  induction f with
  | zero =>
    intro a Λ cx μ d H
    have hzero : (0 : ℤ) ≤ lim.word := le_trans (by positivity) H.ok.space
    -- if f = 0 then return 0
    refine .of_body C.self (Ends.iteLast (fun _ => ?_) (fun h => absurd h (by simp))
      (hT := by simp [tNodes, treeCalls]))
    exact Ends.setTo 0 ⟨by simp [flag_of_not, TreeYes, nodes], .refl⟩
      (hT := by simp [tNodes, treeCalls])
  | succ f ih =>
    intro a Λ cx μ d H
    have hzero : (0 : ℤ) ≤ lim.word := le_trans (by positivity) H.ok.space
    have htime : 60 ≤ tNodes T a.n a.V a.m a.np (a.calls Λ (f + 1)) :=
      le_trans (by omega) (Nat.le_mul_of_pos_left _ (one_le_treeCalls _ _ _ _ _ _))
    -- A triple with an empty set has no node.
    have hempty : ((a.slot 0).set = ∅ ∨ (a.slot 1).set = ∅ ∨ (a.slot 2).set = ∅) → ∀ T', 2 ≤ T' →
        Ends lim (P₀ ++ R) d (.set 0 (k 0))
          ⟨frame (((f + 1 : ℕ) : ℤ) :: a.sets ++ [(cx : ℤ), a.fr]), μ⟩ T' fun σ' =>
          σ'.loc 0 = flag (a.Yes Λ (f + 1)) ∧ Kept μ σ'.mem a.fr := fun h T' hT' =>
      Ends.setTo 0 ⟨by simp [flag_of_not, TreeYes, nodes, h], .refl⟩
    -- if f = 0, l₁ = 0, l₂ = 0 or l₃ = 0 then return 0
    refine .of_body C.self (Ends.iteLast (fun h => absurd h (by simp; omega)) fun _ => ?_)
    refine Ends.iteLast (fun h => ?_) fun h₁ => ?_
    · exact hempty (Or.inl ((H.mem.slotOk 0).set.eq_empty (by simpa using h))) _ (by light_time)
    refine Ends.iteLast (fun h => ?_) fun h₂ => ?_
    · exact hempty (Or.inr (Or.inl ((H.mem.slotOk 1).set.eq_empty (by simpa using h)))) _
        (by light_time)
    refine Ends.iteLast (fun h => ?_) fun h₃ => ?_
    · exact hempty (Or.inr (Or.inr ((H.mem.slotOk 2).set.eq_empty (by simpa using h)))) _
        (by light_time)
    have hl₁ : (a.slot 0).len ≠ 0 := by simpa using h₁
    have hS : ¬ ((a.slot 0).set = ∅ ∨ (a.slot 1).set = ∅ ∨ (a.slot 2).set = ∅) := by
      rintro (h | h | h)
      · exact hl₁ (by rw [← (H.mem.slotOk 0).set.card, h, Finset.card_empty])
      · exact h₂ (by simp [← (H.mem.slotOk 1).set.card, h])
      · exact h₃ (by simp [← (H.mem.slotOk 2).set.card, h])
    have hn : 1 ≤ a.n := by have := (H.mem.slotOk 0).le; omega
    obtain ⟨Mo, hMo⟩ :
        ∃ Mo, Mo = ChanHe.modulus (Nat.primesLE a.m) Λ (a.slot 0).set (a.slot 1).set (a.slot 2).set := ⟨_, rfl⟩
    obtain ⟨hM1, hM⟩ : 1 ≤ Mo ∧ Mo ≤ a.m * a.m := by
      have := modulus_bounds H.primes (fun q hq => Nat.prime_of_mem_primesLE hq)
        (fun q hq => Nat.le_of_mem_primesLE hq) (H.mem.slotOk 0).bdd (H.mem.slotOk 1).bdd (H.mem.slotOk 2).bdd
      rwa [← H.lam, ← hMo, pow_two] at this
    have htime := tNodes_succ_le (T := T) (f := f) H.mem hS hMo
    have hfits := H.fits hn
    have hroom := hfits.room
    light_facts H hfits
    rw [flag_congr (NodeArgs.yes_succ hS hMo)]
    unfold nodesMain
    light_piece (nodesParams_ends H.ctx (by omega) hfits.space_le) with _ rfl
    have hsq : a.m ^ 2 = a.m * a.m := pow_two a.m
    unfold nodesOwn
    -- M := modulus(s₁, l₁, s₂, l₂, s₃, l₃, Λ, np, pr, cnt, fr)
    light_call (C.modulus a Λ μ H.mem (H.lam ▸ lam_le a.V) (d + 1) (modulusNeed_ok H.ok))
      with _ ν₁ ⟨rfl, keep₁⟩
    rw [← hMo]
    -- len := 8 * (m * m); fr' := fr + len
    light_set (8 * a.m ^ 2 : ℕ) using hsq
    light_set (a.fr + 8 * a.m ^ 2 : ℕ) using hsq
    -- nodeArray(M, s₁, l₁, s₂, l₂, s₃, l₃, V, m, fr, cnt, fr')
    light_call (C.array (a.push (8 * a.m ^ 2)) Mo a.fr ν₁ ((H.mem.kept keep₁).push .refl) hM1 hM
      ⟨le_rfl, fun i => Or.inr (H.mem.slotOk i).below,
        Or.inr H.mem.envOk.belowCnt⟩ (d + 1) (nodeArrayNeed_ok H.ok))
      with _ ν₂ ⟨harr, (keep₂ : KeptBut ν₁ ν₂ (a.fr + 8 * a.m ^ 2) a.fr (8 * a.m ^ 2))⟩
    -- a₀ := c3(len, 60 V + 40, fr, fr')
    light_call (c3_meets C.solver H.V_pos H.m_pos H.mem harr (solverNeed_ok H.ok))
      with _ ν₃ ⟨rfl, keep₃⟩
    have kept₁ : Kept μ ν₃ a.fr := by light_keep
  
    light_piece (nodesChild_ends C ih H hn kept₁ hM1 hM 0) with _ ⟨_, μ₂, kept₂, rfl⟩
    light_piece (nodesChild_ends C ih H hn kept₂ hM1 hM 1) with _ ⟨_, μ₃, kept₃, rfl⟩
    light_piece (nodesChild_ends C ih H hn kept₃ hM1 hM 2) with _ ⟨_, μ₄, kept₄, rfl⟩
    refine Ends.setLast ⟨?_, kept₄⟩ (by light_time)
    rfl

end Light.Sec3.ChanHe
