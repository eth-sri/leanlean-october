module

import ThreeSumApsp.Lang.WhileShape

public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Programs.Sec4.Theorem30.FillList
public import ImprovedExponents.PrunedProgram.Tiles.Contracts
import all ThreeSumApsp.Programs.Sec4.Theorem30.FillList

@[expose] public section

/-!
# The boxes with e stars go into the trie of their tile, on pruned encodings

Upstream's `fillList_spec` proves `fillListBody` (procedure 49) under `FillListPre`, with the two
encodings of the tile as full arrays.  The routine reads an encoding cell in one place only: the
value of a box without stars is the product of the two encoded numbers at its code
(`fillValueZero`), and the code is that of a string of `nineStrs L 0 (m - t)`, whose leaf has
at most `m - t ≤ m` symbols `P₀` (`mem_nineStrs`, `card_P0Levels`).  So the same body meets the
same specification when the encodings are right at these leaves only (`FillListPreP`,
`fillListP_meets`).  The proof is upstream's with `SegOn` in place of `Seg` in the invariant of
the loop (`MemInvP`); `SegOn.get_ofDigitList` justifies each read of a pruned encoding.

Adapted from upstream `ThreeSumApsp/Programs/Sec4/Theorem30/FillList.lean` (Apache-2.0).
-/

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

open private fillAt_zero fillAt_length fillAt_succ fillAt_rep length_fillAt_le abs_getD_arrT_le
  exists_starBox from ThreeSumApsp.Programs.Sec4.Theorem30.FillList

/-! ## The bridge: the cell of the code of a string with few nines -/

/-- The cell of the code of a string of `L` digits with at most `m` nines holds the entry of the
array of the encoding: the string is the list of digits of a leaf with as many symbols `P₀` as it
has nines. -/
theorem SegOn.get_ofDigitList {L m : ℕ} {μ : ℕ → ℤ} {a : ℕ} {enc : Leaf L → ℤ}
    (h : SegOn m μ a enc) {l : List ℕ} (hl : l.length = L) (hd : ∀ d ∈ l, d < 10)
    (hc : l.count 9 ≤ m) :
    μ (a + ofDigitList 10 l) = (arrT enc).getD (ofDigitList 10 l) 0 := by
  obtain ⟨τ, rfl⟩ := exists_digitsT l hl hd
  rw [ofDigitList_digitsT, getD_arrT]
  exact h.get (by rwa [card_P0Levels])

/-- A string of `nineStrs L e (m - t)` has at most `m` nines. -/
theorem count_nine_le_of_mem_nineStrs {L m t e : ℕ} {l : List ℕ} (hl : l ∈ nineStrs L e (m - t)) :
    l.count 9 ≤ m :=
  ((mem_nineStrs l).1 hl).2.2.2.trans (Nat.sub_le m t)

/-! ## The program -/



namespace FillList

/-- The memory ν before round number i: leaf number i, if there is one, is at cur; the first i
boxes have been inserted; the two encodings are right at the leaves with few symbols `P₀`. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/FillList.lean (FillList.MemInv)
structure MemInvP (μ : ℕ → ℤ) (x : FillListArgs) (i : ℕ) (ν : ℕ → ℤ) : Prop where
  leaf : ∀ h : i < x.leaves.length, SegN ν x.cur x.leaves[i]
  trie : TrieMem ν x.tr x.cap x.fp (x.trieAt i)
  segA : SegOn x.m ν x.aA x.encA
  segB : SegOn x.m ν x.aB x.encB
  same : SameOutsideTile μ ν x.L x.tr x.cap x.fp x.cur x.box

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {x : FillListArgs}

set_option maxHeartbeats 900000 in
/-- The whole run. -/
private theorem body_spec (K : Callees lim P) (H : FillListPreP lim μ x)
    (hd : d + 2 ≤ lim.depth) :
    Ends lim P d fillListBody ⟨frame x.vals, μ⟩ (tFillList x.L x.leaves.length) fun σ' =>
        TrieMem σ'.mem x.tr x.cap x.fp (x.trieAt x.leaves.length) ∧
          SameOutsideTile μ σ'.mem x.L x.tr x.cap x.fp x.cur x.box := by
  have C := H.ctx
  light_facts C.std
  have heL : x.e ≤ x.L := by light_facts C; have := H.stars_le; omega
  have hpos := length_nineStrs_pos heL H.stars_le
  have hfirst : (nineStrs x.L x.e (x.m - x.t))[0] = nineFirst x.L x.e := getElem_nineStrs hpos
  have hlayout := C.layout
  unfold tFillList
  -- junk := nineFirst(leaf, len, stars)
  light_call (K.first x.cur x.L x.e μ heL (by omega) _ (by omega)) with res ν ⟨hleaf, hsame⟩
  -- more := 1
  light_step
  refine Ends.whileShape (fun i (z : ℤ × ℤ × ℤ × ℤ) ν' =>
    ⟨x.locals (if i < x.leaves.length then 1 else 0) z.1 z.2.1 z.2.2.1 z.2.2.2, ν'⟩)
    (fun i _ => MemInvP μ x i) x.leaves.length (tFillRound x.L) (0, 0, 0, res) ν
    ⟨fun _ => hfirst ▸ hleaf, ?_, H.segA.keep, H.segB.keep, by light_keep⟩ ?_
    (fun _ _ I => ⟨I.trie, I.same⟩) (first := by simp [hpos])
    (step := by intros; simp_all; omega) (stop := by intros; simp; omega)
    (hT := by
      change x.leaves.length * (4 + tFillRound x.L) + 4 ≤
        tNineFirst x.L + x.leaves.length * tFillStep x.L + 60 - (5 + tNineFirst x.L) - 2
      rw [tFillStep, Nat.add_comm (tFillRound x.L) 4]; omega)
  · rw [FillListArgs.trieAt, fillAt_zero]
    exact H.trie.keep
  rintro i ⟨star, value, code, junk⟩ νi hi I
  simp only [ite_eq_left hi]
  let l := x.leaves[i]
  let Ti := x.trieAt i
  let box := starFirst x.e l
  let last : ℤ := ((lastStar box).getD 0 : ℕ)
  let val := x.value Ti box
  have hleaf := List.getElem_mem hi
  have hlen := length_of_mem_nineStrs hleaf
  have hbm := starFirst_mem_starBoxes hi
  obtain ⟨hbL, hbD⟩ := starBoxes_digits hbm
  change box.length = x.L at hbL
  have hnext := nineNext_getElem x.L x.e (x.m - x.t) i hi
  have hrep := fillAt_rep H.root_ne H.rep i
  change TrieRep x.L x.lo Ti x.roots _ at hrep
  have hroom : Ti.length + 11 * x.L ≤ x.cap := by
    have hlen : Ti.length ≤ x.T.length + 11 * x.L * i := length_fillAt_le x.root i
    have := Nat.mul_le_mul_left (11 * x.L) hi
    have := H.room
    simp only [FillListArgs.boxes, length_starBoxes_eq_length_nineStrs] at this
    lia
  obtain ⟨A, B, hA, hB, hword⟩ := C.value_le
  have hab := mul_nonneg_of_abs_le hA hB
  have hsame₀ := I.same
  unfold tFillRound
  light_call (K.star x.cur x.box x.L x.e l νi (I.leaf hi) hlen (by omega) (by omega)
    (by omega) _ (by omega)) with _ νbox ⟨hbox, rfl, hs⟩
  have same : SameOutsideTile μ νbox x.L x.tr x.cap x.fp x.cur x.box := by light_keep
  have htr : TrieMem νbox x.tr x.cap x.fp Ti := I.trie.keep
  refine Ends.pieceThen (T₁ := tHorner x.L + tSumTen x.L + 18)
    (R := fun σ => ∃ code' : ℤ, σ = ⟨x.locals 1 last val code' junk, νbox⟩) ?_ ?_
  · refine Ends.iteIffLast (x.e = 0) (fun hz => ?_) (fun hz => ?_)
    · -- A leaf reads its two encoded numbers.
      have hdigits := ((mem_nineStrs l).1 hleaf).2.1
      have hnines := count_nine_le_of_mem_nineStrs hleaf
      have hbox' : SegN νbox x.box l := by simpa [hz, box, starFirst_zero] using hbox
      have hval : val = (arrT x.encA).getD (ofDigitList 10 l) 0 * (arrT x.encB).getD (ofDigitList 10 l) 0 := by
        simp only [val, FillListArgs.value, box, hz, starFirst_zero, boxValue_zero _ _ Ti x.root hdigits, leafProduct]
      rw [hval]
      have hcode : ofDigitList 10 l < 10 ^ x.L := hlen ▸ ofDigitList_lt l hdigits
      have ha := SegOn.get_ofDigitList (I.segA.keep (μ' := νbox)) hlen hdigits hnines
      have hb := SegOn.get_ofDigitList (I.segB.keep (μ' := νbox)) hlen hdigits hnines
      light_call (K.horner x.box x.L l νbox hbox' hlen hdigits (by omega) C.pow_le _ (by omega))
        with _ ν' ⟨rfl, hν'⟩
      obtain rfl : νbox = ν' := hν'.symm
      generalize ofDigitList 10 l = c at hcode ha hb ⊢
      have hprod : |(arrT x.encA).getD c 0 * (arrT x.encB).getD c 0| ≤ lim.word := by
        rw [abs_mul]
        calc
          _ ≤ A * B :=
            mul_le_mul (abs_getD_arrT_le _ hA hcode) (abs_getD_arrT_le _ hB hcode) (by positivity)
              ((abs_nonneg _).trans (abs_getD_arrT_le _ hA hcode))
          _ ≤ _ := (le_mul_of_one_le_left hab (one_le_pow₀ (by norm_num))).trans hword
      generalize (arrT x.encA).getD c 0 = y at ha hprod ⊢
      generalize (arrT x.encB).getD c 0 = z at hb hprod ⊢
      light_set (y * z) using ha, hb, abs_le.mp hprod
      exact ⟨c, rfl⟩
    · -- A box with a star reads the ten descendants of its last star.
      obtain ⟨e, he⟩ : ∃ e, x.e = e + 1 := ⟨x.e - 1, by omega⟩
      have heM := H.stars_le
      change box ∈ starBoxes x.L x.m x.t x.e at hbm
      rw [he] at hrep hbm
      obtain ⟨p, hstar⟩ := exists_starBox hA hB hrep hbm
      have hbound : (10 : ℤ) ^ (e + 1) * (A * B) ≤ lim.word :=
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hab).trans hword
      have hval : val = ((List.range 10).map fun d => trieLookup Ti x.root (box.set p d)).sum := by
        change boxValue (arrT x.encA) (arrT x.encB) Ti x.root x.e box = _
        rw [he]
        exact hstar.value
      have hlast : last = p := by simp [last, hstar.last]
      rw [hval, hlast]
      have hle := htr.le_cap
      have hsLast : lastStar (starFirst x.e l) = some p := hstar.last
      refine Ends.callTo (K.box
        { tr := x.tr, root := x.root, box := x.box, L := x.L, p := p, T := Ti, l := box } νbox
        { area := htr.seg, seg := hbox, len := hbL, star := hbL ▸ hstar.lt
          digits := hbD, walk := hstar.walk
          sums := fun j _ => (hstar.sums j).trans hbound } _ (by omega)) ?_ (ha := by light_side [hsLast, hbL])
      rintro _ _ ⟨rfl, rfl⟩
      exact ⟨code, by rw [hsLast]; rfl⟩
  · rintro _ ⟨code', rfl⟩
    have hmore : (if (nineNext x.e (x.m - x.t) l).isSome then (1 : ℤ) else 0)
        = if i + 1 < x.leaves.length then 1 else 0 := by rw [hnext]; simp
    -- Insert the computed value, then form the next leaf.
    unfold fillTailStmt
    light_call (K.insert
      { tr := x.tr, root := x.root, key := x.box, L := x.L, val := val,
        fp := x.fp, cap := x.cap, T := Ti, kl := box } νbox
      { trie := htr, seg := hbox, len := hbL, digits := hbD
        walk := hrep.insertOK x.tile H.root_ne _ hbL hbD
        room := hbL ▸ hroom } _ (by omega)) with _ νins ⟨htrie, hins⟩
    dsimp only at htrie hins
    light_call (K.next x.cur x.L x.e (x.m - x.t) l νins (I.leaf hi).keep hleaf (by omega) _
      (by omega)) with _ νnext ⟨hnextLeaf, hres, hkept⟩
    rw [hmore] at hres
    rw [hnext] at hnextLeaf
    refine ⟨⟨_, _, _, _⟩, νnext, by rw [hres]; rfl, fun h => ?_, ?_, I.segA.keep, I.segB.keep,
      by light_keep⟩
    · simp_all
    · rw [FillListArgs.trieAt, fillAt_succ x.root hi]
      exact htrie.keep

end FillList

/-- **fillList on pruned encodings** inserts the boxes with e stars, with their values, into the
trie of their tile. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/FillList.lean (fillList_spec)
theorem fillListP_meets {lim : Limits} {P : Program} (hP : P[Proc.fillList]? = some fillListBody)
    (hFirst : NineFirstSpec lim P) (hNext : NineNextSpec lim P) (hStar : StarFirstSpec lim P)
    (hHorner : HornerSpec lim P) (hInsert : InsertSpec lim P) (hBox : SumTenSpec lim P) :
    FillListSpecP lim P := by
  intro x μ pre d hd
  rw [FillListArgs.boxes, length_starBoxes_eq_length_nineStrs, ← fillAt_length]
  exact .of_body hP (FillList.body_spec ⟨hFirst, hNext, hStar, hHorner, hInsert, hBox⟩ pre hd)

end Light.Sec4
