/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

import ThreeSumApsp.Lang.Registers

import ThreeSumApsp.Lang.Symbolic
public import ThreeSumApsp.Lang.Sequence

public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Buckets
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.NodeMemory

/-!
# The reduction from 3SUM to Convolution-3SUM: the array of a node

Theorem 21(a), after [CH20, Theorem 5.1].
nodeArray(M, s₁, l₁, s₂, l₂, s₃, l₃, V, m, y, cnt, fr) writes the first `8 m²` cells of the
one-array instance of the node `(S₁, S₂, S₃, M)` (`ChanHe.Node.oneArray`) to `y`
(`nodeArray_spec`).  The array consists of c = 2m² groups of four cells; cell t of group i is the
cell y + 4i + t.

* With `W = 2V + 1` and `G = 3W + 1` the padding pattern `10G, W + G, W + 3G, -W + 4G` (`padVal`) is
  written to all groups (`pad_ends`).
* Then, for each of the three sets, a pass (`placeStmt`, `place_ends`) computes the remainders of
  the numbers sg · x, where x runs through the set and sg is 1 for the first two sets and -1 for the
  third; counts them in the count table; writes sg · x + g, for every x whose remainder r has the
  count 1, to cell off of group r (and of group r + M, for the third set); and removes the
  counts again. Here g is G, 3G, 4G and off is 1, 2, 3. The invariant for `place_column` tracks
  the final contents of this column directly.
* The four kinds of cells make up the one-array instance (`oneArray_of_cells`); the parts are put
  together in `nodeArray_spec`.

The three passes are the same piece of text, which reads its parameters from local variables.  It is
not a procedure of its own, so that the depth of calls is the one that the specification allows for.

From other files: `keys M L` is the list of the remainders of the numbers of L, as natural numbers;
`arr S M pd r` is the element of S with the remainder r if there is exactly one, and the padding
value pd otherwise; `arrZ` is the same for the negatives of S, repeated at r + M; `BucketPre` is
what coll and heavy assume about a set and the count table; `Counted` says that the remainders stand
at the free pointer and that the table holds how often each occurs.
-/

@[expose] public section

namespace Light.Sec3.ChanHe

open ThreeSumApsp.ChanHe ThreeSumApsp.Spec.ChanHeArray

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The local variables -/

namespace ArrLocals

/-- The local variables of nodeArray: the arguments M, s₁, l₁, s₂, l₂, s₃, l₃, V, m, y, cnt, fr; the
numbers W and G; a counter, an address, a remainder, a value and the result of a call, which the
padding loop and the passes use; the number 2m² of groups; the parameters of a pass, which are the
sign sg, the number g that is added, the address and the length of the set, the number of the cell
in its group, and the distance to the second cell; the free pointer behind the remainders; and the
padding pattern. -/
abbrev MOD : ℕ := 0
registers from 7 [VMAX, MMAX, ARRAY, CNT, FREE, WIDTH, GAP, IDX, ADDR, KEY, VAL, RES, GROUPS,
  SIGN, SHIFT, SRC, LEN, OFF, DIST, PAD0, PAD1, PAD2, PAD3]

end ArrLocals

/-- The arguments of nodeArray. -/
structure ArrArgs : Type extends NodeArgs where
  Mo : ℕ
  y : ℕ

abbrev ArrArgs.vals (a : ArrArgs) : List ℤ :=
  (a.Mo : ℤ) :: a.sets ++ [(a.V : ℤ), a.m, a.y, a.cnt, a.fr]

/-- The padding pattern: what cell t of a group holds before the passes. -/
def padVal (V : ℕ) (t : ℕ) : ℤ :=
  if t = 0 then 10 * (6 * V + 4) else if t = 1 then (2 * V + 1) + (6 * V + 4)
  else if t = 2 then (2 * V + 1) + 3 * (6 * V + 4) else -(2 * V + 1) + 4 * (6 * V + 4)

/-- The scratch variables of the padding loop and of a pass: counter, address, remainder, value,
and the result of a call. -/
structure ArrScratch : Type where
  idx : ℤ
  ad : ℤ
  key : ℤ
  val : ℤ
  res : ℤ

/-- The list of the local variables of nodeArray, once the constants have been computed. -/
abbrev arrLocals (a : ArrArgs) (x : ArrScratch) (sg g : ℤ) (s len off δ : ℕ) : List ℤ :=
  a.vals ++ [2 * (a.V : ℤ) + 1, 6 * a.V + 4,
    x.idx, x.ad, x.key, x.val, x.res, (2 * (a.m * a.m) : ℕ), sg, g, s, len, off, δ,
    padVal a.V 0, padVal a.V 1, padVal a.V 2, padVal a.V 3]

/-! ## The padding pattern -/

open ArrLocals in
/-- For i < 2m²: the four cells of group i become the padding pattern. -/
def padStmt : Stmt :=
  .for IDX (v GROUPS) (
    .store (v ARRAY +' k 4 *' v IDX) (v PAD0) ;;
    .store (v ARRAY +' k 4 *' v IDX +' k 1) (v PAD1) ;;
    .store (v ARRAY +' k 4 *' v IDX +' k 2) (v PAD2) ;;
    .store (v ARRAY +' k 4 *' v IDX +' k 3) (v PAD3))

/-- The memory before group j is written: the groups below j hold the pattern p, and no cell outside
the c groups has changed. -/
def PadInv (μ : ℕ → ℤ) (y c : ℕ) (p : ℕ → ℤ) (j : ℕ) (μ' : ℕ → ℤ) : Prop :=
  (∀ i < j, ∀ t < 4, μ' (y + 4 * i + t) = p t) ∧ SameOutside μ μ' y (4 * c)

/-- One more group. -/
theorem PadInv.succ {μ μ' : ℕ → ℤ} {y c j : ℕ} {p : ℕ → ℤ} (h : PadInv μ y c p j μ') (hj : j < c) :
    PadInv μ y c p (j + 1) (Function.update (Function.update (Function.update (Function.update μ'
      (y + 4 * j) (p 0)) (y + 4 * j + 1) (p 1)) (y + 4 * j + 2) (p 2)) (y + 4 * j + 3) (p 3)) := by
  refine ⟨fun i hi t ht => ?_, (((h.2.update ⟨by omega, by omega⟩ _).update ⟨by omega, by omega⟩
    _).update ⟨by omega, by omega⟩ _).update ⟨by omega, by omega⟩ _⟩
  grind only [PadInv, = Function.update.eq_1, #74e5, #213d, #8995, #b584, #07a6, #7ef3, #3148, #d2e6, #83ad]

/-- **The padding pattern** is written to all groups. -/
theorem pad_ends {μ : ℕ → ℤ} {a : ArrArgs} (hw : (lim.space : ℤ) ≤ lim.word)
    (hy : a.y + 4 * (2 * (a.m * a.m)) ≤ lim.space) {x : ArrScratch} {sg g : ℤ}
    {s len off δ : ℕ} :
    Ends lim P d padStmt ⟨frame (arrLocals a x sg g s len off δ), μ⟩ (42 * (2 * (a.m * a.m)) + 6)
      fun σ' => ∃ μ', PadInv μ a.y (2 * (a.m * a.m)) (padVal a.V) (2 * (a.m * a.m)) μ' ∧
        σ' = ⟨frame (arrLocals a { x with idx := (2 * (a.m * a.m) : ℕ) } sg g s len off δ),
          μ'⟩ := by
  -- for i < 2m²
  refine Ends.forFrame (PadInv μ a.y (2 * (a.m * a.m)) (padVal a.V)) (2 * (a.m * a.m))
    ⟨fun i hi => absurd hi (by omega), .refl⟩ ?round ?done
  case round =>
    intro j μ' hj inv
    -- mem[y + 4i] := p₀; mem[y + 4i + 1] := p₁; mem[y + 4i + 2] := p₂; mem[y + 4i + 3] := p₃
    light_steps using arrLocals, padVal
    exact ⟨rfl, by simpa [padVal] using inv.succ hj⟩

  aesop

/-! ## One pass over a set -/

open ArrLocals in
/-- A round of the loop of a pass: key := mem[fr + j]; if mem[cnt + key] = 1 then
sg * mem[s + j] + g is written to the cells y + 4 key + off and y + 4 key + off + δ. -/
def placeRound : Stmt :=
  .set KEY (M (v FREE +' v IDX)) ;;
  .ite (M (v CNT +' v KEY) =' k 1)
    (.set ADDR (v ARRAY +' k 4 *' v KEY +' v OFF) ;;
     .set VAL (v SIGN *' M (v SRC +' v IDX) +' v SHIFT) ;;
     .store (v ADDR) (v VAL) ;;
     .store (v ADDR +' v DIST) (v VAL))
    .skip

open ArrLocals in
/-- The loop of a pass: a round for each j < len. -/
def placeLoop : Stmt := .for IDX (v LEN) placeRound

open ArrLocals in
/-- One pass.  The remainders of the numbers sg · x go to the cells from the free pointer and are
counted; the loop writes sg · x + g for every x whose remainder has the count 1; the counts are
removed. -/
def placeStmt (pCount pClear : ℕ) : Stmt :=
  .call pCount [v LEN, v SRC, v SIGN, v MOD, v FREE, v CNT] RES ;;
  placeLoop ;;
  .call pClear [v LEN, v FREE, v CNT] RES

/-- The time of a pass over len numbers: remainders, counting, the loop, and removing the counts. -/
def tPlace (len V : ℕ) : ℕ := tCount len V + tClear len + 45 * len + 32

/-- No cell below the free pointer has changed, except cell t of the c groups from y. -/
abbrev KeptCol (μ μ' : ℕ → ℤ) (fr y c t : ℕ) : Prop :=
  SameOn (fun b => b < fr ∧ ∀ i < c, b ≠ y + 4 * i + t) μ μ'

/-- A cell of another kind has not changed. -/
theorem KeptCol.cell {μ μ' : ℕ → ℤ} {fr y c t : ℕ} (h : KeptCol μ μ' fr y c t) {i t' : ℕ}
    (hb : y + 4 * i + t' < fr) (ht : t < 4 := by omega) (ht' : t' < 4 := by omega)
    (hne : t' ≠ t := by omega) : μ' (y + 4 * i + t') = μ (y + 4 * i + t') :=
  h _ ⟨hb, fun _ _ => by omega⟩

/-- The cells outside the array have not changed either. -/
theorem KeptCol.keptBut {μ μ' μ'' : ℕ → ℤ} {fr y c t : ℕ} (h : KeptCol μ' μ'' fr y c t)
    (hk : KeptBut μ μ' fr y (4 * c)) (ht : t < 4 := by omega) : KeptBut μ μ'' fr y (4 * c) :=
  hk.then h fun b hb => ⟨hb, hb.1, fun i hi => by have := hb.2; omega⟩

/-- Layout and word bounds for writing a column. The third column repeats the residue block. -/
private structure ColumnPre (lim : Limits) (μ : ℕ → ℤ) (d : ℕ) (a : ArrArgs) (sg g : ℤ)
    (s off shift cap c : ℕ) (L : List ℤ) : Prop where
  bucket : BucketPre lim μ d a.fr a.V a.Mo s a.cnt cap L
  sign : sg = 1 ∨ sg = -1
  belowArr : a.y + 4 * c ≤ a.fr
  apartSet : Apart a.y (4 * c) s L.length
  apartTable : Apart a.y (4 * c) a.cnt cap
  room : a.Mo + shift ≤ c
  off_lt : off < 4
  shift_eq : shift = 0 ∨ shift = a.Mo
  value_le : |g| + a.V ≤ lim.word

/-- In the active rows, a residue appears at its own row and (optionally) in the second copy. -/
private theorem row_key {i r Mo shift : ℕ} (hr : r < Mo) (hs : shift = 0 ∨ shift = Mo) :
    i < Mo + shift ∧ i % Mo = r ↔ i = r ∨ i = r + shift := by
  rcases hs with rfl | hs
  · by_cases h : i < Mo
    · simp [h, Nat.mod_eq_of_lt h]
    · simp [h, show i ≠ r by omega]
  · subst shift
    by_cases h : i < Mo
    · simp [Nat.mod_eq_of_lt h, show i < Mo + Mo by omega, show i ≠ r + Mo by omega]
    · by_cases hi : i < Mo + Mo
      · rw [Nat.mod_eq_sub_mod (by omega : Mo ≤ i), Nat.mod_eq_of_lt (by omega : i - Mo < Mo)]
        omega
      · omega

section column

variable {μ : ℕ → ℤ} {a : ArrArgs} {sg g pd : ℤ} {s off shift cap c : ℕ} {L : List ℤ}
  {pCount pClear : ℕ}

/-- Count signed residues, fill the active rows with unique values and clear the counters. -/
private theorem place_column (hR : CountSpec lim P pCount) (hT : ClearSpec lim P pClear)
    (H : ColumnPre lim μ d a sg g s off shift cap c L) (hnd : L.Nodup)
    (hpad : ∀ i < c, μ (a.y + 4 * i + off) = pd + g) (x : ArrScratch) :
    Ends lim P d (placeStmt pCount pClear) ⟨frame (arrLocals a x sg g s L.length off (4 * shift)), μ⟩
      (tPlace L.length a.V) fun σ' =>
      ∃ (x' : ArrScratch) (μ' : ℕ → ℤ),
        σ' = ⟨frame (arrLocals a x' sg g s L.length off (4 * shift)), μ'⟩ ∧
        (∀ i < c, μ' (a.y + 4 * i + off) =
          (if i < a.Mo + shift then arr (L.map (sg * ·)).toFinset a.Mo pd (i % a.Mo) else pd) + g) ∧
        KeptCol μ μ' a.fr a.y c off := by
  let S := L.map (sg * ·)
  let K := keys a.Mo S
  let F := fun r => arr S.toFinset a.Mo pd r + g
  have hnd' : S.Nodup := hnd.map fun u w huw => by
    rcases H.sign with rfl | rfl <;> simpa using huw
  have C := H.bucket
  have hM := C.modulus_pos
  have hlen : K.length = L.length := by simp [K, S]
  have hlt := keys_lt hM S
  have hword := sq_add_le_word C.ok.word
  have hsq : (0 : ℤ) ≤ (L.length : ℤ) * L.length := by positivity
  light_facts H C C.ok
  have hcells := C.ok.cells
  have hdepth := C.ok.depth
  simp only [collNeed] at hcells hdepth
  unfold placeStmt tPlace
  light_call (hR C H.sign) with res μ₂ ⟨-, counted, kept₂⟩
  let I (j : ℕ) (_ : ArrScratch) (ν : ℕ → ℤ) : Prop :=
    SameOn (fun b => ∀ i < c, b ≠ a.y + 4 * i + off) μ₂ ν ∧
    ∀ i < c, ν (a.y + 4 * i + off) =
      if i < a.Mo + shift ∧ K.count (i % a.Mo) = 1 ∧ i % a.Mo ∈ K.take j
      then F (i % a.Mo) else pd + g
  refine Ends.next _ (Ends.forShape
    (fun j w ν => ⟨frame (arrLocals a {w with idx := j} sg g s L.length off (4 * shift)), ν⟩)
    I L.length 37 {x with res := res} ⟨.refl, ?_⟩ ?_ ?_ (hT := le_rfl)) (by light_time)
  · intro i hi
    simpa using (kept₂ _ (by omega)).trans (hpad i hi)
  · intro j w ν hj inv
    obtain ⟨hkept, hinv⟩ := inv
    have hjK : j < K.length := by omega
    let r := K[j]
    have hr : r < a.Mo := hlt _ (List.getElem_mem hjK)
    have hkey : ν (a.fr + j) = (r : ℕ) := (hkept _ (fun _ _ => by omega)).trans (counted.keys.getElem hjK)
    have hcount : ν (a.cnt + r) = K.count r :=
      (hkept _ (fun _ _ => by omega)).trans (counted.counts _ (by omega))
    have hread : ν (s + j) = L[j] :=
      (hkept _ (fun _ _ => by omega)).trans ((kept₂ _ (by omega)).trans (C.list j hj))
    have hV : |sg * L[j]| ≤ (a.V : ℤ) := by
      rcases H.sign with rfl | rfl <;> simpa using C.bounded.getElem hj
    have := abs_le.1 hV
    have := abs_le.1 (le_refl |g|)
    have htake (q : ℕ) : q ∈ K.take (j + 1) ↔ q ∈ K.take j ∨ q = r := by
      rw [List.take_succ_eq_append_getElem hjK, List.mem_append, List.mem_singleton]
    unfold placeRound
    light_set r using hkey
    light_if hone hmany : K.count r = 1 using hcount
    · light_set (a.y + 4 * r + off : ℕ)
      light_set (sg * L[j] + g) using hread
      light_store (a.y + 4 * r + off) (sg * L[j] + g)
      light_store (a.y + 4 * r + off + 4 * shift) (sg * L[j] + g)
      have hval : F r = sg * L[j] + g := by
        have hv := arr_of_count_eq_one hM hnd' pd (j := j) (by simpa [S] using hj)
        simpa [F, r, K, S, keys] using congrArg (· + g) (hv (by simpa [r, K, S, keys] using hone))
      have hr' : r + shift < c := by omega
      refine ⟨⟨j, (a.y + 4 * r + off : ℕ), r, sg * L[j] + g, w.res⟩, _, rfl, ?_⟩
      refine ⟨(hkept.write (fun h => h r (by omega) rfl) _).write
        (fun h => h (r + shift) hr' (by omega)) _, fun i hi => ?_⟩
      by_cases mark : i < a.Mo + shift ∧ i % a.Mo = r
      · have := (row_key hr H.shift_eq).mp mark
        simp only [mark.1, mark.2, hone, htake, or_true, and_self, if_true, hval]
        grind [Function.update_apply]
      · rw [Function.update_of_ne (by intro h; apply mark; apply (row_key hr H.shift_eq).mpr; omega),
          Function.update_of_ne (by intro h; apply mark; apply (row_key hr H.shift_eq).mpr; omega),
          hinv i hi]
        simp only [htake]
        grind
    · light_skip
      exact ⟨{w with key := r}, ν, rfl, hkept, fun i hi => by simp only [hinv i hi, htake]; grind⟩
  · rintro w ν ⟨hkept, hinv⟩
    light_call (C.clear_meets hT hlen hlt (counted.of_sameOutside
        (hkept.mono fun _ _ _ _ => by omega) H.belowArr H.apartTable))
      with res' μ₄ ⟨zero₄, same₄⟩
    refine ⟨{w with idx := L.length, res := res'}, μ₄, rfl, fun i hi => ?_, ?_⟩
    · rw [same₄ _ (by omega), hinv i hi]
      simp only [← hlen, List.take_length]
      by_cases h : i < a.Mo + shift
      · by_cases hone : K.count (i % a.Mo) = 1
        · simp [h, hone, List.count_pos_iff.mp (show 0 < K.count (i % a.Mo) by omega), F, S]
        · simp [h, hone, arr_of_count_ne_one hM hnd' pd hone, S]
      · simp [h]
    · exact sameOn_of_zeroAt ((kept₂.then hkept fun b hb => ⟨⟨hb.1.1, hb.2⟩, hb.1.2⟩).then same₄
        fun b hb => ⟨hb, hb.2⟩) C.zero zero₄

end column

/-! ## The routine -/

open ArrLocals in
/-- The constants: W = 2V + 1, G = 3W + 1, the number 2m² of groups, and the padding pattern. -/
def arrConsts : Stmt :=
  .set WIDTH (k 2 *' v VMAX +' k 1) ;;
  .set GAP (k 3 *' v WIDTH +' k 1) ;;
  .set GROUPS (k 2 *' (v MMAX *' v MMAX)) ;;
  .set PAD0 (k 10 *' v GAP) ;;
  .set PAD1 (v WIDTH +' v GAP) ;;
  .set PAD2 (v WIDTH +' k 3 *' v GAP) ;;
  .set PAD3 (k 4 *' v GAP -' v WIDTH)

abbrev gapFactor (i : Fin 3) : ℕ := ![1, 3, 4] i

private abbrev ArrArgs.shift (a : ArrArgs) (i : Fin 3) : ℤ := gapFactor i * (6 * a.V + 4)

private abbrev passSign (i : Fin 3) : ℤ := if i = 2 then -1 else 1

private abbrev ArrArgs.duplicate (a : ArrArgs) (i : Fin 3) : ℕ := if i = 2 then a.Mo else 0

private abbrev ArrArgs.dist (a : ArrArgs) (i : Fin 3) : ℕ := 4 * a.duplicate i

open ArrLocals in
/-- Set the parameters for the pass over one of the three lists. -/
def arrSetup (i : Fin 3) : Stmt :=
  .set SIGN (if i = 2 then k 0 -' k 1 else k 1) ;;
  .set SHIFT (k (gapFactor i) *' v GAP) ;;
  .set SRC (v (1 + 2 * i.val)) ;;
  .set LEN (v (2 + 2 * i.val)) ;;
  .set OFF (k (i.val + 1)) ;;
  .set DIST (if i = 2 then k 4 *' v MOD else k 0)

/-- A pass with its parameters initialized. -/
def arrPass (pCount pClear : ℕ) (i : Fin 3) : Stmt := arrSetup i ;; placeStmt pCount pClear

/-- nodeArray(M, s₁, l₁, s₂, l₂, s₃, l₃, V, m, y, cnt, fr), over the procedures number pCount and
pClear. -/
def nodeArrayBody (pCount pClear : ℕ) : Stmt :=
  arrConsts ;; padStmt ;; Stmt.chain (arrPass pCount pClear) (List.finRange 3)

/-- What nodeArray assumes, apart from the three sets: the modulus, the count table, the place of
the array, and the limits. -/
structure ArrPre (lim : Limits) (μ : ℕ → ℤ) (d : ℕ) (a : ArrArgs) : Prop where
  modulus_pos : 1 ≤ a.Mo
  modulus_le : a.Mo ≤ a.m * a.m
  zero : ZeroAt μ a.cnt (a.m * a.m)
  belowTable : a.cnt + a.m * a.m ≤ a.fr
  belowArr : a.y + 4 * (2 * (a.m * a.m)) ≤ a.fr
  apartTable : Apart a.y (4 * (2 * (a.m * a.m))) a.cnt (a.m * a.m)
  ok : (nodeArrayNeed a.n a.V a.m).Ok lim a.fr d
  slots : ∀ i, (a.slot i).Ok μ a.toEnv
  apart : ∀ i, Apart a.y (4 * (2 * (a.m * a.m))) (a.slot i).addr (a.slot i).len

section routine

variable {μ μ' : ℕ → ℤ} {a : ArrArgs} {pCount pClear : ℕ}

/-- The inputs do not depend on the cells of the array. -/
theorem ArrPre.keptBut (h : ArrPre lim μ d a)
    (hk : KeptBut μ μ' a.fr a.y (4 * (2 * (a.m * a.m)))) : ArrPre lim μ' d a := by
  light_facts h
  refine { h with zero := fun q hq => (hk _ (by omega)).trans (h.zero q hq), slots := fun i => ?_ }
  have hi := h.slots i
  have ha := h.apart i
  have hb := hi.below
  exact { hi with set := hi.set.of_sameOn hk fun j hj => by omega }

/-- The numbers up to 64 (V + 1) fit in a word. -/
theorem ArrPre.word_le (h : ArrPre lim μ d a) : 64 * ((a.V : ℤ) + 1) ≤ lim.word := by
  simpa using mul_le_word (x := 1) (y := 1) (z := 64 * (a.V + 1)) h.ok.word
    (Nat.one_le_pow _ _ (by omega)) (by omega) le_rfl

/-- What a pass assumes, from what nodeArray assumes. -/
private theorem ArrPre.pass (h : ArrPre lim μ d a) (i : Fin 3) :
    ∃ L : List ℤ, L.length = (a.slot i).len ∧ L.Nodup ∧ L.toFinset = (a.slot i).set ∧
      ColumnPre lim μ d a (passSign i) (a.shift i) (a.slot i).addr (i.val + 1) (a.duplicate i)
        (a.m * a.m) (2 * (a.m * a.m)) L := by
  have hM := h.modulus_le
  have hword := h.word_le
  have hi := h.slots i
  have hl := hi.le
  have H : BucketMem μ a.fr a.V a.Mo (a.slot i).addr (a.slot i).len a.cnt (a.m * a.m) (a.slot i).set :=
    ⟨h.modulus_pos, hM, hi.bdd, hi.set, h.zero, hi.below, h.belowTable, hi.apart⟩
  obtain ⟨L, he, hn, hs, hL⟩ := H.exists_pre
    (h.ok.mono (wordNeed_mono hl hM) (by simp only [collNeed, nodeArrayNeed]; omega) le_rfl)
  exact ⟨L, he, hn, hs, hL, by simp only [passSign]; split <;> simp, h.belowArr, he ▸ h.apart i,
    h.apartTable, by simp only [ArrArgs.duplicate]; split <;> omega, by omega,
    by simp only [ArrArgs.duplicate]; split <;> simp, by
      fin_cases i <;> dsimp [ArrArgs.shift, gapFactor] <;> rw [abs_of_nonneg (by positivity)] <;> omega⟩

/-- **The constants** are computed. -/
theorem arrConsts_ends (h : ArrPre lim μ d a) :
    Ends lim P d arrConsts
      ⟨frame a.vals, μ⟩ 38
      fun σ' => σ' = ⟨frame (arrLocals a ⟨0, 0, 0, 0, 0⟩ 0 0 0 0 0 0), μ⟩ := by
  have hword := h.word_le
  light_facts h h.ok
  -- W := 2 V + 1; G := 3 W + 1; groups := 2 (m m)
  light_set (2 * a.V + 1)
  light_set (6 * a.V + 4)
  light_set (2 * (a.m * a.m) : ℕ)
  -- the padding pattern 10 G, W + G, W + 3 G, 4 G - W
  light_set (padVal a.V 0) using padVal
  light_set (padVal a.V 1) using padVal
  light_set (padVal a.V 2) using padVal
  light_set (padVal a.V 3) using padVal
  rfl

private theorem arrSetup_ends (h : ArrPre lim μ d a) (i : Fin 3) (x : ArrScratch)
    {sg g : ℤ} {s len off δ : ℕ} :
    Ends lim P d (arrSetup i) ⟨frame (arrLocals a x sg g s len off δ), μ⟩ 18 fun σ =>
      σ = ⟨frame (arrLocals a x (passSign i) (a.shift i) ((a.slot i).addr) ((a.slot i).len)
        (i.val + 1) (a.dist i)), μ⟩ := by
  have hword := h.word_le
  light_facts h h.ok
  fin_cases i <;> light_block using arrSetup, arrLocals, passSign, ArrArgs.shift, gapFactor

end routine

/-- **nodeArray meets its specification**, in every program that holds its body and meets the
specifications of the two routines that it calls. -/
theorem nodeArray_spec {p pCount pClear : ℕ} (hp : P[p]? = some (nodeArrayBody pCount pClear))
    (hR : CountSpec lim P pCount) (hT : ClearSpec lim P pClear) : NodeArraySpec lim P p := by
  intro a₀ M y μ N hM hMm hout d hok
  refine .of_body hp ?_
  let a : ArrArgs := ⟨a₀, M, y⟩
  have hsq : 8 * a₀.m ^ 2 = 4 * (2 * (a₀.m * a₀.m)) := by ring
  have h : ArrPre lim μ d a :=
    ⟨hM, hMm, N.envOk.zero, N.envOk.belowCnt, hsq ▸ hout.below, hsq ▸ hout.apartCnt,
      hok, N.slotOk, fun i => hsq ▸ hout.apart i⟩
  rw [hsq]
  change Ends _ _ _ _ ⟨frame a.vals, μ⟩ _ _
  let c := 2 * (a.m * a.m)
  let ν := a.node a.Mo
  let R (k : ℕ) (σ : State) := ∃ x sg g s len off δ,
    σ.loc = frame (arrLocals a x sg g s len off δ) ∧ KeptBut μ σ.mem a.fr a.y (4 * c) ∧
    ∀ j < c, ∀ t < 4, σ.mem (a.y + 4 * j + t) =
      if t ≤ k then ν.oneArray a.V (4 * j + t) else padVal a.V t
  light_facts h h.ok
  light_piece (arrConsts_ends h) using tNodeArray, sq, a with _ rfl
  light_piece (pad_ends h.ok.space (by omega)) using tNodeArray, sq, a with _ ⟨μ₀, ⟨hpad, same₀⟩, rfl⟩
  refine (Ends.chainFin _ (fun i => 18 + tPlace (a.slot i).len a.V) R ?_ ?_).mono ?_ ?_
  · rintro i ⟨_, μ'⟩ ⟨x, sg, g, s, len, off, δ, rfl, hk, hv⟩
    have hp := h.keptBut hk
    unfold arrPass
    light_piece (arrSetup_ends hp i x) with _ rfl
    rw [Nat.add_sub_cancel_left]
    obtain ⟨L, hl, hnd, hset, H⟩ := hp.pass i
    rw [← hl]
    refine (place_column (pd := passSign i * pad a.V) hR hT H hnd ?_ x).mono le_rfl ?_
    · intro j hj
      rw [hv j hj _ (by omega), if_neg (by omega)]
      fin_cases i <;> simp [padVal, pad, passSign, ArrArgs.shift, gapFactor]
    rintro _ ⟨x', μ'', rfl, hcol, hsame⟩
    refine ⟨x', _, _, _, _, _, _, rfl, hsame.keptBut hk, fun j hj t ht => ?_⟩
    by_cases ht' : t = i.val + 1
    · subst t
      dsimp only [State.mem]
      rw [if_pos le_rfl, hcol j hj]
      obtain ⟨_, h1, h2, h3⟩ := oneArray_cells ν a.V j
      have himage : (L.map (- ·)).toFinset = L.toFinset.image (- ·) := by ext; simp
      by_cases hi : i = 2
      · subst i
        change _ = ν.oneArray a.V (4 * j + 3)
        rw [h3]
        simp [ν, ArrArgs.duplicate, arrZ, passSign, himage, hset, two_mul, ArrArgs.shift, gapFactor]
      · have he : (if j < a.Mo then arr (a.slot i).set a.Mo (pad a.V) (j % a.Mo) else pad a.V) =
            arr (a.slot i).set a.Mo (pad a.V) j := by
          split_ifs with hjM
          · rw [Nat.mod_eq_of_lt hjM]
          · rw [arr_of_le h.modulus_pos _ _ (by omega)]
        simp only [ArrArgs.duplicate, passSign, if_neg hi, one_mul, List.map_id', hset, Nat.add_zero, he]
        fin_cases i <;> simp [ν, pad, ArrArgs.shift, gapFactor] at *
        · exact h1.symm
        · exact h2.symm
    · have haddr : a.y + 4 * j + t < a.fr := by dsimp [c] at hj; omega
      dsimp only
      rw [hsame.cell haddr]
      simpa only [show t ≤ i.val + 1 ↔ t ≤ i.val by omega] using hv j hj t ht
  · refine ⟨_, _, _, _, _, _, _, rfl, ?_, fun j hj t ht => ?_⟩
    · exact SameOn.mono same₀ (fun _ hb => hb.2)
    dsimp only
    rw [hpad j hj t ht]
    split_ifs with h0 <;> try rfl
    obtain rfl : t = 0 := by omega
    simpa [padVal] using (oneArray_cells ν a.V j).1.symm
  · simp [List.finRange_succ, tNodeArray, tPlace, sq, a]
    omega
  · rintro σ' ⟨_, _, _, _, _, _, _, -, hk, cols⟩
    refine ⟨fun u hu => ?_, hk⟩
    have hu' : u < 4 * c := by simpa [c, a, hsq] using hu
    have he := Nat.div_add_mod u 4
    have hm := Nat.mod_lt u (by decide : 0 < 4)
    rw [← he, ← Nat.add_assoc]
    simpa [c, show u % 4 ≤ 3 by omega] using cols (u / 4) (by omega) _ hm

end Light.Sec3.ChanHe
