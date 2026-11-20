/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Slots
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.NodeMemory
public import ThreeSumApsp.Sec3.Theorem21a.ChanHe.Sizes

/-!
# The recursion tree of the reduction from 3SUM to Convolution-3SUM

Theorem 21(a), after [CH20, Theorem 5.1].
nodes(f, s₁, l₁, s₂, l₂, s₃, l₃, cx, fr) runs through the first f levels of the recursion tree whose
root is the triple of sets at s₁, s₂, s₃ (`ChanHe.nodes`), depth first, and asks a solver of
Convolution-3SUM for the one-array instance of each node.  It returns 1 if one of the answers is
yes, and 0 if not (`nodes_spec`, by induction on f).

The text of the procedure is cut into parts, with a lemma for each.
* The parameters are read from a block in the memory (`nodesParams_ends`).
* At a node the procedure computes the modulus, writes the array at the free pointer and calls the
  solver (`nodesOwn_ends`, `c3_meets`).
* For each of the three sets in turn it writes the heavy elements of the set at the free pointer,
  where the array is no longer needed, and calls itself with the heavy elements in place of the set
  (`nodesChild₁_ends`, `nodesChild₂_ends`, `nodesChild₃_ends`; the child meets what the procedure
  assumes by `NodesPre.child₁`, `child₂`, `child₃`).
* The answer is yes if one of the four answers is (`nodesAnswer_ends`, `NodeArgs.yes_succ`).
The parts are put together in `nodesMain_ends`; the time is `tNodes_succ_le`.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3.ChanHe

open ThreeSumApsp.ChanHe ThreeSumApsp.Spec Finset

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Pure facts -/

/-- One of four answers is yes if and only if their sum is positive. -/
theorem flag_sum_pos (a b c e : Prop) : 0 < flag a + flag b + flag c + flag e ↔ a ∨ b ∨ c ∨ e := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> by_cases he : e <;>
    simp [flag_of, flag_of_not, ha, hb, hc, he]

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
pointer behind the array; the result of nodeArray, which is not used; the answer of the solver; and
for each of the three children the number of heavy elements and the answer.  At the end local 0
receives the result, as in every procedure. -/
slots 0 LEVELS SET1 LEN1 SET2 LEN2 SET3 LEN3 FREE VMAX MMAX LAM NPRIMES PRIMES CNT MOD LEN
  FR2 RES ANS0 HEAVY1 ANS1 HEAVY2 ANS2 HEAVY3 ANS3

end NodesLocals

open NodesLocals in
abbrev childTail (fr : Expr) : List Expr := [fr, v VMAX, v MMAX, v LAM, v NPRIMES, v PRIMES, v CNT]

open NodesLocals in
/-- The node itself: its modulus, its array at the free pointer, and the answer of the solver. -/
def nodesOwn (pMod pArr pC3 : ℕ) : Stmt :=
  .call pMod
      [v SET1, v LEN1, v SET2, v LEN2, v SET3, v LEN3, v LAM, v NPRIMES, v PRIMES, v CNT, v FREE]
      MOD ;;
  .set LEN (k 3 *' (v MMAX *' v MMAX)) ;;
  .set FR2 (v FREE +' v LEN) ;;
  .call pArr
      [v MOD, v SET1, v LEN1, v SET2, v LEN2, v SET3, v LEN3, v VMAX, v MMAX, v FREE]
      RES ;;
  .call pC3 [v MMAX, k 2 *' v VMAX +' k 1,v MOD, v FREE, v FR2] ANS0

open NodesLocals in
/-- The first child: the heavy elements of the first set are written at the free pointer, and the
procedure calls itself with them in place of the first set. -/
def nodesChild₁ (pSelf pHeavy : ℕ) : Stmt :=
  .call pHeavy [v LEN1, v SET1, v MOD, v FREE, v CNT, v FREE +' v LEN1] HEAVY1 ;;
  .call pSelf
      ([v LEVELS -' k 1, v FREE, v HEAVY1, v SET2, v LEN2, v SET3, v LEN3] ++ childTail (v FREE +' v LEN1))
      ANS1

open NodesLocals in
/-- The second child. -/
def nodesChild₂ (pSelf pHeavy : ℕ) : Stmt :=
  .call pHeavy [v LEN2, v SET2, v MOD, v FREE, v CNT, v FREE +' v LEN2] HEAVY2 ;;
  .call pSelf
      ([v LEVELS -' k 1, v SET1, v LEN1, v FREE, v HEAVY2, v SET3, v LEN3] ++ childTail (v FREE +' v LEN2))
      ANS2

open NodesLocals in
/-- The third child. -/
def nodesChild₃ (pSelf pHeavy : ℕ) : Stmt :=
  .call pHeavy [v LEN3, v SET3, v MOD, v FREE, v CNT, v FREE +' v LEN3] HEAVY3 ;;
  .call pSelf
      ([v LEVELS -' k 1, v SET1, v LEN1, v SET2, v LEN2, v FREE, v HEAVY3] ++ childTail (v FREE +' v LEN3))
      ANS3

open NodesLocals in
/-- The answer is yes if one of the four answers is. -/
def nodesAnswer : Stmt :=
  .ite (k 0 <' v ANS0 +' v ANS1 +' v ANS2 +' v ANS3) (.set 0 (k 1)) (.set 0 (k 0))

/-- A triple of nonempty sets with at least one level to go. -/
def nodesMain (pSelf pMod pArr pC3 pHeavy : ℕ) : Stmt :=
  nodesOwn pMod pArr pC3 ;; nodesChild₁ pSelf pHeavy ;; nodesChild₂ pSelf pHeavy ;;
  nodesChild₃ pSelf pHeavy ;; nodesAnswer

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
  solver : Solves HashTriangle.task P₀ pC3 T r
  self : (P₀ ++ R)[p]? = some (nodesBody p pMod pArr pC3 pHeavy)
  modulus : ModulusSpec lim (P₀ ++ R) pMod
  array : NodeArraySpec lim (P₀ ++ R) pArr
  heavy : HeavySpec lim (P₀ ++ R) pHeavy

/-! ## Needs and times -/

section needs

variable {r : ℕ → ℕ → Need} {fr n V m f l M : ℕ}

section
variable (h : (nodesNeed r n V m (f + 1)).Ok lim fr d)
include h

/-- What is allowed at a node covers what modulus needs. -/
theorem modulusNeed_ok :
    (modulusNeed n V m).Ok lim fr (d + 1) := by
  refine h.mono ?_ ?_ ?_ <;> simp [nodesNeed] <;> omega

/-- What is allowed at a node covers what nodeArray needs behind the array. -/
theorem nodeArrayNeed_ok :
    (nodeArrayNeed n V m).Ok lim (fr + 3 * (m * m)) (d + 1) := by
  refine h.mono ?_ ?_ ?_ <;> simp [nodesNeed, nodeArrayNeed, modulusNeed] <;> omega

/-- What is allowed at a node covers what the solver needs behind the array. -/
theorem solverNeed_ok :
    (r m (2 * V + 1)).Ok lim (fr + 3 * (m * m)) (d + 1) := by
  refine h.mono ?_ ?_ ?_ <;> simp [nodesNeed] <;> omega

/-- What is allowed at a node covers what heavy needs behind its output. -/
theorem collNeed_ok (hl : l ≤ n) (hM : M ≤ m * m) :
    (collNeed l V M).Ok lim (fr + l) (d + 1) := by
  have hsucc : (f + 1) * n = f * n + n := by ring
  have hword := wordNeed_mono (V := V) hl hM
  refine h.mono ?_ ?_ ?_ <;> simp [nodesNeed, collNeed, modulusNeed] <;> omega

/-- What is allowed at a node covers what a child needs behind its set of heavy elements. -/
theorem childNeed_ok (hl : l ≤ n) :
    (nodesNeed r n V m f).Ok lim (fr + l) (d + 1) := by
  have hsucc : (f + 1) * n = f * n + n := by ring
  refine h.mono ?_ ?_ ?_ <;> simp [nodesNeed] <;> omega

end

section
variable {l n : ℕ}
  (h : l ≤ n)
include h

/-- The time of resid grows with the lengths of the sets. -/
theorem tResid_mono (V : ℕ) : tResid l V ≤ tResid n V := by
  unfold tResid
  gcongr

/-- The time of tally grows with the lengths of the sets. -/
theorem tTally_mono : tTally l ≤ tTally n := by
  unfold tTally
  omega

/-- The time of coll grows with the lengths of the sets. -/
theorem tColl_mono (V : ℕ) : tColl l V ≤ tColl n V := by
  have hresid := tResid_mono h V
  have htally := tTally_mono h
  unfold tColl
  omega

/-- The time of heavy grows with the lengths of the sets. -/
theorem tHeavy_mono (V : ℕ) : tHeavy l V ≤ tHeavy n V := by
  have hresid := tResid_mono h V
  have htally := tTally_mono h
  unfold tHeavy
  omega

end

section
variable {l₁ l₂ l₃ n : ℕ}
  (h₁ : l₁ ≤ n)
  (h₂ : l₂ ≤ n)
  (h₃ : l₃ ≤ n)
include h₁ h₂ h₃

/-- The time of modulus grows with the lengths of the sets. -/
theorem tModulus_mono (np V : ℕ) :
    tModulus np l₁ l₂ l₃ V ≤ tModulus np n n n V := by
  have hcoll₁ := tColl_mono h₁ V
  have hcoll₂ := tColl_mono h₂ V
  have hcoll₃ := tColl_mono h₃ V
  have hsearch : tSearch np l₁ l₂ l₃ V ≤ tSearch np n n n V :=
    Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _
  unfold tModulus
  omega

/-- The time of nodeArray grows with the lengths of the sets. -/
theorem tNodeArray_mono (m V : ℕ) :
    tNodeArray m l₁ l₂ l₃ V ≤ tNodeArray m n n n V := by
  unfold tNodeArray tRep
  gcongr

end

end needs

/-! ## The parts of the procedure -/

section parts

variable {P₀ R : Program} {p pMod pArr pC3 pHeavy : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}
  {a : NodeArgs} {Λ f Mo : ℕ} {μ μ₀ μ' : ℕ → ℤ}

/-- What the limits allow at a node: an address fits in a word; behind the free pointer there is
room for a set and the array; the number of levels is at most the number of cells, so that it fits
in a word; the numbers up to 64 (V + 1) and 64 (m² + 1) fit in a word; and one more level of calls
is allowed. -/
structure NodesFits (lim : Limits) (d fr n V m f : ℕ) : Prop where
  space_le : (lim.space : ℤ) ≤ lim.word
  room : fr + n + 3 * (m * m) ≤ lim.space
  levels : f ≤ lim.space
  wordV : 64 * ((V : ℤ) + 1) ≤ lim.word
  wordM : 64 * ((m : ℤ) * m + 1) ≤ lim.word
  depth : d < lim.depth

/-- What the procedure assumes provides what the limits have to allow at a node. -/
theorem NodesPre.fits (H : NodesPre lim r μ a Λ (f + 1) d) (hn : 1 ≤ a.n) :
    NodesFits lim d a.fr a.n a.V a.m f := by
  have hcells := H.ok.cells
  have hdepth := H.ok.depth
  have hword : ((wordNeed a.n a.V (a.m * a.m) : ℕ) : ℤ) ≤ lim.word :=
    le_trans (by exact_mod_cast le_max_left _ _) H.ok.word
  simp [nodesNeed] at hcells hdepth
  have hlevels := Nat.le_mul_of_pos_right f hn
  have hsucc : (f + 1) * a.n = f * a.n + a.n := by ring
  have hsq := pow_two a.m
  have hone : 1 ≤ (a.n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  refine ⟨H.ok.space, by omega, by omega, ?_, ?_, by omega⟩
  · simpa using mul_le_word (y := 1) hword hone (by omega) le_rfl
  · have h := mul_le_word (z := 64) hword hone le_rfl (by omega)
    omega

section
variable (H : NodesPre lim r μ₀ a Λ (f + 1) d)
  (kept : Kept μ₀ μ a.fr)
include H kept

/-- The first child of a node meets what the procedure assumes, with one level less.  μ₀, μ and μ'
are the memories when the procedure is called, before heavy, and after heavy. -/
theorem NodesPre.child₁
    (hk : KeptBut μ μ' (a.fr + a.X₁.len) a.fr a.X₁.len)
    (hs : SetAt μ' a.fr #(ChanHe.heavy a.X₁.set Mo) (ChanHe.heavy a.X₁.set Mo)) :
    NodesPre lim r μ' (a.child₁ Mo) Λ f (d + 1) :=
  { H with
    mem := (H.mem.kept kept).child₁ hk hs
    ok := childNeed_ok H.ok H.mem.set₁.le }

/-- The second child of a node meets what the procedure assumes, with one level less. -/
theorem NodesPre.child₂
    (hk : KeptBut μ μ' (a.fr + a.X₂.len) a.fr a.X₂.len)
    (hs : SetAt μ' a.fr #(ChanHe.heavy a.X₂.set Mo) (ChanHe.heavy a.X₂.set Mo)) :
    NodesPre lim r μ' (a.child₂ Mo) Λ f (d + 1) :=
  { H with
    mem := (H.mem.kept kept).child₂ hk hs
    ok := childNeed_ok H.ok H.mem.set₂.le }

/-- The third child of a node meets what the procedure assumes, with one level less. -/
theorem NodesPre.child₃
    (hk : KeptBut μ μ' (a.fr + a.X₃.len) a.fr a.X₃.len)
    (hs : SetAt μ' a.fr #(ChanHe.heavy a.X₃.set Mo) (ChanHe.heavy a.X₃.set Mo)) :
    NodesPre lim r μ' (a.child₃ Mo) Λ f (d + 1) :=
  { H with
    mem := (H.mem.kept kept).child₃ hk hs
    ok := childNeed_ok H.ok H.mem.set₃.le }

end

/-- The node with the modulus `Mo`. -/
abbrev NodeArgs.node (a : NodeArgs) (Mo : ℕ) : Node := ⟨a.X₁.set, a.X₂.set, a.X₃.set, Mo⟩

/-- The list of the local variables of nodes: the arguments, with x for the number of levels; the
parameters that are read from the block at cx; and the list t of what has been computed since. -/
@[simp] abbrev nodesLocals (x : ℤ) (a : NodeArgs) (Λ : ℕ) (t : List ℤ) : List ℤ :=
  a.regs x Λ ++ t

/-- **The node itself**: the modulus is computed, the array is written at the free pointer, and the
solver answers for it. -/
theorem nodesOwn_ends (C : NodesCtx lim P₀ R p pMod pArr pC3 pHeavy T r)
    (H : NodesPre lim r μ a Λ (f + 1) d) (hn : 1 ≤ a.n)
    (hMo : Mo = ChanHe.modulus (Nat.primesLE a.m) Λ a.X₁.set a.X₂.set a.X₃.set) (hM1 : 1 ≤ Mo)
    (hM : Mo ≤ a.m * a.m) {x } :
    Ends lim (P₀ ++ R) d (nodesOwn pMod pArr pC3) ⟨frame (nodesLocals x a Λ []), μ⟩
      (47 + tModulus a.np a.X₁.len a.X₂.len a.X₃.len a.V +
        tNodeArray a.m a.X₁.len a.X₂.len a.X₃.len a.V + T a.m (2 * a.V + 1))
      fun σ' => ∃ (y : ℤ) (μ' : ℕ → ℤ), Kept μ μ' a.fr ∧
        σ' = ⟨frame (nodesLocals x a Λ [Mo, (3 * (a.m * a.m) : ℕ), (a.fr + 3 * (a.m * a.m) : ℕ), y,
          flag ((a.node Mo).Hit a.V)]), μ'⟩ := by
  have hfits := H.fits hn
  light_facts hfits
  have hsq := pow_two a.m
  light_call (C.modulus a Λ μ H.mem (H.lam ▸ lam_le a.V) (d + 1) (modulusNeed_ok H.ok))
    with _ μ₁ ⟨rfl, kept₁⟩
  rw [← hMo]
  -- len := 3 * (m * m); fr' := fr + len
  light_set (3 * (a.m * a.m) : ℕ) using hsq
  light_set (a.fr + 3 * (a.m * a.m) : ℕ) using hsq
  -- nodeArray(M, s₁, l₁, s₂, l₂, s₃, l₃, V, m, fr, cnt, fr')
  light_call (C.array a Mo μ₁ (H.mem.kept kept₁) hM1 hM _ (nodeArrayNeed_ok H.ok))
    with y μ₂ ⟨built,kept₂⟩
  light_call (C.solver.meets R (a.job Mo) a.top built (solverNeed_ok H.ok)) using HashTriangle.task with _ μ₃ ⟨rfl,kept₃⟩
  exact ⟨y,μ₃,(kept₁.trans kept₂).then kept₃ (fun b hb => by exact ⟨hb,by change b<a.fr+3*(a.m*a.m); omega⟩),rfl⟩

section
variable (C : NodesCtx lim P₀ R p pMod pArr pC3 pHeavy T r)
  (ih : NodesSpecAt lim (P₀ ++ R) p T r f)
  (H : NodesPre lim r μ₀ a Λ (f + 1) d)
  (hn : 1 ≤ a.n)
  (kept : Kept μ₀ μ a.fr)
  (hM1 : 1 ≤ Mo)
  (hM : Mo ≤ a.m * a.m)
include C ih H hn kept hM1 hM

/-- **The first child.**  Started in a memory μ that agrees below fr with the memory μ₀ in which the
procedure was called, the part leaves the number of heavy elements of the first set and the answer
for the child in HEAVY1 and ANS1, and changes no cell below fr.  x, y, z are the values of LEN, FR2,
RES, which are no longer used. -/
theorem nodesChild₁_ends
    {x y z a₀ } :
    Ends lim (P₀ ++ R) d (nodesChild₁ p pHeavy)
      ⟨frame (nodesLocals (f + 1 : ℕ) a Λ [Mo, x, y, z, a₀]), μ⟩
      (40 + tHeavy a.X₁.len a.V + tNodes T a.n a.V a.m a.np (visits f))
      fun σ' => ∃ μ' : ℕ → ℤ, Kept μ₀ μ' a.fr ∧
        σ' = ⟨frame (nodesLocals (f + 1 : ℕ) a Λ [Mo, x, y, z, a₀,
          #(ChanHe.heavy a.X₁.set Mo), flag ((a.child₁ Mo).Yes Λ f)]), μ'⟩ := by
  have hfits := H.fits hn
  have hX := (H.mem.kept kept).set₁
  have hle := hX.le
  light_facts hfits
  -- h₁ := heavy(l₁, s₁, M, fr, cnt, fr + l₁)
  light_call (C.heavy (d + 1) (a.fr + a.X₁.len) _ _ _ _ a.fr _ _ _ μ
    ((hX.push .refl).bucket ((H.mem.kept kept).envOk.push .refl) hM1 hM)
    ⟨le_rfl, Or.inl hX.below, Or.inr H.mem.envOk.belowCnt⟩ (collNeed_ok H.ok hle hM))
    with _ μ₁ ⟨rfl, hset, kept₁⟩
  -- a₁ := nodes(F - 1, fr, h₁, s₂, l₂, s₃, l₃, cx, fr + l₁), where the local LEVELS holds f + 1
  light_call (ih (a.child₁ Mo) Λ μ₁ (d + 1) (H.child₁ kept kept₁ hset))
    with _ μ₂ ⟨rfl, (kept₂ : Kept μ₁ μ₂ (a.fr + a.X₁.len))⟩
  exact ⟨μ₂, (kept.then kept₁ fun b hb => by omega).then kept₂ fun b hb => by omega, rfl⟩

/-- **The second child**: as for the first, with HEAVY2 and ANS2. -/
theorem nodesChild₂_ends
    {x y z a₀ h₁ a₁ } :
    Ends lim (P₀ ++ R) d (nodesChild₂ p pHeavy)
      ⟨frame (nodesLocals (f + 1 : ℕ) a Λ [Mo, x, y, z, a₀, h₁, a₁]), μ⟩
      (40 + tHeavy a.X₂.len a.V + tNodes T a.n a.V a.m a.np (visits f))
      fun σ' => ∃ μ' : ℕ → ℤ, Kept μ₀ μ' a.fr ∧
        σ' = ⟨frame (nodesLocals (f + 1 : ℕ) a Λ [Mo, x, y, z, a₀, h₁, a₁,
          #(ChanHe.heavy a.X₂.set Mo), flag ((a.child₂ Mo).Yes Λ f)]), μ'⟩ := by
  have hfits := H.fits hn
  have hX := (H.mem.kept kept).set₂
  have hle := hX.le
  light_facts hfits
  -- h₂ := heavy(l₂, s₂, M, fr, cnt, fr + l₂)
  light_call (C.heavy (d + 1) (a.fr + a.X₂.len) _ _ _ _ a.fr _ _ _ μ
    ((hX.push .refl).bucket ((H.mem.kept kept).envOk.push .refl) hM1 hM)
    ⟨le_rfl, Or.inl hX.below, Or.inr H.mem.envOk.belowCnt⟩ (collNeed_ok H.ok hle hM))
    with _ μ₁ ⟨rfl, hset, kept₁⟩
  -- a₂ := nodes(F - 1, s₁, l₁, fr, h₂, s₃, l₃, cx, fr + l₂), where the local LEVELS holds f + 1
  light_call (ih (a.child₂ Mo) Λ μ₁ (d + 1) (H.child₂ kept kept₁ hset))
    with _ μ₂ ⟨rfl, (kept₂ : Kept μ₁ μ₂ (a.fr + a.X₂.len))⟩
  exact ⟨μ₂, (kept.then kept₁ fun b hb => by omega).then kept₂ fun b hb => by omega, rfl⟩

/-- **The third child**: as for the first, with HEAVY3 and ANS3. -/
theorem nodesChild₃_ends
    {x y z a₀ h₁ a₁ h₂ a₂ } :
    Ends lim (P₀ ++ R) d (nodesChild₃ p pHeavy)
      ⟨frame (nodesLocals (f + 1 : ℕ) a Λ [Mo, x, y, z, a₀, h₁, a₁, h₂, a₂]), μ⟩
      (40 + tHeavy a.X₃.len a.V + tNodes T a.n a.V a.m a.np (visits f))
      fun σ' => ∃ μ' : ℕ → ℤ, Kept μ₀ μ' a.fr ∧
        σ' = ⟨frame (nodesLocals (f + 1 : ℕ) a Λ [Mo, x, y, z, a₀, h₁, a₁, h₂, a₂,
          #(ChanHe.heavy a.X₃.set Mo), flag ((a.child₃ Mo).Yes Λ f)]), μ'⟩ := by
  have hfits := H.fits hn
  have hX := (H.mem.kept kept).set₃
  have hle := hX.le
  light_facts hfits
  -- h₃ := heavy(l₃, s₃, M, fr, cnt, fr + l₃)
  light_call (C.heavy (d + 1) (a.fr + a.X₃.len) _ _ _ _ a.fr _ _ _ μ
    ((hX.push .refl).bucket ((H.mem.kept kept).envOk.push .refl) hM1 hM)
    ⟨le_rfl, Or.inl hX.below, Or.inr H.mem.envOk.belowCnt⟩ (collNeed_ok H.ok hle hM))
    with _ μ₁ ⟨rfl, hset, kept₁⟩
  -- a₃ := nodes(F - 1, s₁, l₁, s₂, l₂, fr, h₃, cx, fr + l₃), where the local LEVELS holds f + 1
  light_call (ih (a.child₃ Mo) Λ μ₁ (d + 1) (H.child₃ kept kept₁ hset))
    with _ μ₂ ⟨rfl, (kept₂ : Kept μ₁ μ₂ (a.fr + a.X₃.len))⟩
  exact ⟨μ₂, (kept.then kept₁ fun b hb => by omega).then kept₂ fun b hb => by omega, rfl⟩

end

/-- **The answer** is yes if one of the four answers is.  The lemma is stated for arbitrary locals,
so that the 26 values need not be listed; for a state that is written as a list, hloc holds by
definition and determines the four statements. -/
theorem nodesAnswer_ends {loc } {R₀ R₁ R₂ R₃ } (hword : (4 : ℤ) ≤ lim.word)
    (hloc : loc NodesLocals.ANS0 = flag R₀ ∧ loc NodesLocals.ANS1 = flag R₁ ∧
      loc NodesLocals.ANS2 = flag R₂ ∧ loc NodesLocals.ANS3 = flag R₃ := by
      exact ⟨rfl, rfl, rfl, rfl⟩) :
    Ends lim P d nodesAnswer ⟨loc, μ⟩ 12 fun σ' =>
      σ'.loc 0 = flag (R₀ ∨ R₁ ∨ R₂ ∨ R₃) ∧ σ'.mem = μ := by
  obtain ⟨e₀, e₁, e₂, e₃⟩ := hloc
  have f₀ := flag_mem R₀
  have f₁ := flag_mem R₁
  have f₂ := flag_mem R₂
  have f₃ := flag_mem R₃
  refine Ends.iteLast (fun hyes => ?_) (fun hno => ?_) (by light_side [e₀, e₁, e₂, e₃])
  · have hpos : 0 < flag R₀ + flag R₁ + flag R₂ + flag R₃ := by simp_all
    exact Ends.setLast ⟨by simp [flag_of ((flag_sum_pos _ _ _ _).1 hpos)], rfl⟩ (by simp; omega)
  · have hzero : ¬ 0 < flag R₀ + flag R₁ + flag R₂ + flag R₃ := by
      simp_all
    exact Ends.setLast ⟨by simp [flag_of_not fun h => hzero ((flag_sum_pos _ _ _ _).2 h)], rfl⟩
      (by simp; omega)

/-- The time of a node: its own work and the three subtrees.  The 178 steps are
28 + 47 + 3 · 25 + 12 for the parts of nodesMain and 16 for the four tests of nodesBody. -/
theorem tNodes_succ_le (hN : NodeMem μ a) :
    210 + tModulus a.np a.X₁.len a.X₂.len a.X₃.len a.V +
      tNodeArray a.m a.X₁.len a.X₂.len a.X₃.len a.V + T a.m (2 * a.V + 1) +
      tHeavy a.X₁.len a.V + tHeavy a.X₂.len a.V + tHeavy a.X₃.len a.V +
      tNodes T a.n a.V a.m a.np (visits f) +
      tNodes T a.n a.V a.m a.np (visits f) +
      tNodes T a.n a.V a.m a.np (visits f)
    ≤ tNodes T a.n a.V a.m a.np (visits (f+1)) := by
  have hmod := tModulus_mono hN.set₁.le hN.set₂.le hN.set₃.le a.np a.V
  have harr := tNodeArray_mono hN.set₁.le hN.set₂.le hN.set₃.le a.m a.V
  have hheavy₁ := tHeavy_mono hN.set₁.le a.V
  have hheavy₂ := tHeavy_mono hN.set₂.le a.V
  have hheavy₃ := tHeavy_mono hN.set₃.le a.V
  simp [tNodes,tNode,visits,add_mul]; linarith

/-- The nodes of a tree with a nonempty root: the root and the nodes of the three subtrees. -/
theorem NodeArgs.yes_succ (hS : ¬ (a.X₁.set = ∅ ∨ a.X₂.set = ∅ ∨ a.X₃.set = ∅))
    (hMo : Mo = ChanHe.modulus (Nat.primesLE a.m) Λ a.X₁.set a.X₂.set a.X₃.set) :
    a.Yes Λ (f + 1) ↔ (a.node Mo).Hit a.V ∨
      (a.child₁ Mo).Yes Λ f ∨ (a.child₂ Mo).Yes Λ f ∨ (a.child₃ Mo).Yes Λ f := by
  simp [TreeYes, NodeArgs.child₁, NodeArgs.child₂, NodeArgs.child₃, Slot.heavy,
    Env.push, nodes, if_neg hS, ← hMo, List.mem_cons, List.mem_append, or_and_right, exists_or,
    exists_eq_left, or_assoc]

/-- **A triple of nonempty sets with at least one level to go**: the parts, one after the other.
The four tests of nodesBody have taken 16 steps. -/
theorem nodesMain_ends (C : NodesCtx lim P₀ R p pMod pArr pC3 pHeavy T r)
    (ih : NodesSpecAt lim (P₀ ++ R) p T r f) (H : NodesPre lim r μ a Λ (f + 1) d)
    (hS : ¬ (a.X₁.set = ∅ ∨ a.X₂.set = ∅ ∨ a.X₃.set = ∅)) (hn : 1 ≤ a.n) :
    Ends lim (P₀ ++ R) d (nodesMain p pMod pArr pC3 pHeavy)
      ⟨frame (a.regs (f+1:ℕ) Λ), μ⟩
      (tNodes T a.n a.V a.m a.np (visits (f+1)) - 16) fun σ' =>
      σ'.loc 0 = flag (a.Yes Λ (f + 1)) ∧ Kept μ σ'.mem a.fr := by
  obtain ⟨Mo, hMo⟩ :
      ∃ Mo, Mo = ChanHe.modulus (Nat.primesLE a.m) Λ a.X₁.set a.X₂.set a.X₃.set := ⟨_, rfl⟩
  obtain ⟨hM1, hM⟩ : 1 ≤ Mo ∧ Mo ≤ a.m * a.m := by
    have := modulus_bounds H.primes (fun q hq => Nat.prime_of_mem_primesLE hq)
      (fun q hq => Nat.le_of_mem_primesLE hq) H.mem.set₁.bdd H.mem.set₂.bdd H.mem.set₃.bdd
    rwa [← H.lam, ← hMo, pow_two] at this
  have htime := tNodes_succ_le (T := T) (f := f) H.mem
  have hfits := H.fits hn
  light_facts H hfits
  rw [flag_congr (NodeArgs.yes_succ hS hMo)]
  -- the node itself
  light_piece (nodesOwn_ends C H hn hMo hM1 hM) with _ ⟨x, μ₁, kept₁, rfl⟩
  -- the three children
  light_piece (nodesChild₁_ends C ih H hn kept₁ hM1 hM) with _ ⟨μ₂, kept₂, rfl⟩
  light_piece (nodesChild₂_ends C ih H hn kept₂ hM1 hM) with _ ⟨μ₃, kept₃, rfl⟩
  light_piece (nodesChild₃_ends C ih H hn kept₃ hM1 hM) with _ ⟨μ₄, kept₄, rfl⟩
  -- the answer
  light_piece (nodesAnswer_ends (by omega)) with _ ⟨hres, hmem⟩
  grind

end parts

/-- **The recursion tree**: the procedure meets its specification. -/
theorem nodes_spec {P₀ R } {p pMod pArr pC3 pHeavy } {T }
    {r } (C : NodesCtx lim P₀ R p pMod pArr pC3 pHeavy T r) :
    NodesSpec lim (P₀ ++ R) p T r := by
  intro f
  induction f with
  | zero =>
    intro a Λ μ d H
    have hzero := le_trans (by rfl) H.ok.space
    -- if f = 0 then return 0
    refine .of_body C.self (Ends.iteLast (fun _ => ?_) (fun h => absurd h (by simp))
      (hT := by simp [tNodes,visits]))
    exact Ends.setTo 0 ⟨by simp [flag_of_not, TreeYes, nodes], .refl⟩
      (hT := by simp [tNodes,visits])
  | succ f ih =>
    intro a Λ μ d H
    have hzero := le_trans (by rfl) H.ok.space
    have htime : 60 ≤ tNodes T a.n a.V a.m a.np (visits (f+1)) :=
      le_trans (by omega) (Nat.le_mul_of_pos_left _ (show 0 < visits (f+1) by simp [visits]))
    -- A triple with an empty set has no node.
    have hempty : (a.X₁.set = ∅ ∨ a.X₂.set = ∅ ∨ a.X₃.set = ∅) → ∀ T', 2 ≤ T' →
        Ends lim (P₀ ++ R) d (.set 0 (k 0))
          ⟨frame (a.regs (f+1:ℕ) Λ), μ⟩ T' fun σ' =>
          σ'.loc 0 = flag (a.Yes Λ (f + 1)) ∧ Kept μ σ'.mem a.fr := fun h T' hT' =>
      Ends.setTo 0 ⟨by simp [flag_of_not, TreeYes, nodes, h], .refl⟩
    -- if f = 0, l₁ = 0, l₂ = 0 or l₃ = 0 then return 0
    refine .of_body C.self (Ends.iteLast (fun h => absurd h (by simp; omega)) fun _ => ?_)
    refine Ends.iteLast (fun h => ?_) fun h₁ => ?_
    · exact hempty (Or.inl (H.mem.set₁.set.eq_empty (by simp_all))) _ (by light_time)
    refine Ends.iteLast (fun h => ?_) fun h₂ => ?_
    · exact hempty (Or.inr (Or.inl (H.mem.set₂.set.eq_empty (by simp_all)))) _
        (by light_time)
    refine Ends.iteLast (fun h => ?_) fun h₃ => ?_
    · exact hempty (Or.inr (Or.inr (H.mem.set₃.set.eq_empty (by simp_all)))) _
        (by light_time)
    have hl₁ : a.X₁.len ≠ 0 := by simp_all
    have hS : ¬ (a.X₁.set = ∅ ∨ a.X₂.set = ∅ ∨ a.X₃.set = ∅) := by
      rintro (h | h | h)
      · exact hl₁ (by rw [← H.mem.set₁.set.card, h, Finset.card_empty])
      · exact h₂ (by simp [← H.mem.set₂.set.card, h])
      · exact h₃ (by simp [← H.mem.set₃.set.card, h])
    light_piece (nodesMain_ends C ih H hS (by have := H.mem.set₁.le; omega))

end Light.Sec3.ChanHe
