/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Util.Types
public import Mathlib.Tactic
public import ThreeSumApsp.Util.RamArith
public import ThreeSumApsp.Lang.Auto
public import ThreeSumApsp.Lang.Lib.ArrayAt
public import ThreeSumApsp.Lang.Lib.Pass
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Spec.Sec3.Theorem17.Cyclic

/-!
# Vectors: sums, differences, and the product in ℤ[x]/(x^p - 1)

The proof of Theorem 17 computes with matrices over the ring ℤ[x]/(x^p - 1); an element of the ring
is a vector of p integers, and a ring operation takes "O(p²) word operations".

* vlin(dst, a, b, n, s): dst[i] := a[i] + s b[i] for i < n, with s = 1 or s = -1; dst may be the
  segment a itself (accumulation).  It is one pass (`vlin_spec`), and what it writes is `vadd` or
  `vsub` (`vlinList_one`, `vlinList_neg_one`).
* cconv(dst, a, b, p): dst := the cyclic convolution of a and b.  The inner loop adds up the p terms
  of one entry (`cconvEntry_spec`), the outer loop stores the p entries (`cconv_spec`).  The partial
  sums stay below p α β if the entries of a and b are bounded by α and β (`abs_convPartialSum_le`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Sums and differences -/


/-- vlin(dst, a, b, n, s): for i < n: dst[i] := a[i] + s b[i]. -/
def vlinBody  :=
  pass 5 (v 3) (v 0) (M (v 1 +' v 5) +' v 4 *' M (v 2 +' v 5))

/-- The list that vlin writes. -/
def vlinList s (A B : List ℤ) := List.zipWith (fun x y => x + s * y) A B

/-- With s = 1 it is the sum. -/
theorem vlinList_one A B : vlinList 1 A B = vadd A B := by
  simp [vlinList, vadd]

/-- With s = -1 it is the difference. -/
theorem vlinList_neg_one A B : vlinList (-1) A B = vsub A B := by
  grind [vlinList, vsub]

/-- Entry j of that list. -/
def vlinAt s (A B : List ℤ) j := A.getD j 0 + s * B.getD j 0

/-- What vlin assumes: the lists A and B of n numbers of absolute value at most V stand at a and b;
the n cells at dst lie in the memory, do not meet b, and are the cells at a or do not meet them. -/
structure VlinPre (lim : Limits) (μ : Light.Memory) (dst a b n : ℕ) (s V : ℤ) (A B : List ℤ) : Prop where
  opA : ArrayAt μ a A n V lim.space
  opB : ArrayAt μ b B n V lim.space
  sign : |s| ≤ 1
  word : 2 * V ≤ lim.word := by light_arith
  space : dst + n ≤ lim.space := by light_arith
  apartA : dst = a ∨ dst + n ≤ a ∨ a + n ≤ dst := by light_arith
  apartB : dst + n ≤ b ∨ b + n ≤ dst := by light_arith

/-- **vlin** writes a + s b to dst and changes nothing else, in at most 23 n + 6 steps. -/
theorem vlin_spec {μ } {dst a b n } {s V } {A B }
    (hw : (lim.space : ℤ) ≤ lim.word) (pre : VlinPre lim μ dst a b n s V A B) :
    Ends lim P d vlinBody ⟨frame [dst, a, b, n, s], μ⟩ (23 * n + 6) fun σ' =>
      Seg σ'.mem dst (vlinList s A B) ∧ SameOutside μ σ'.mem dst n := by
  light_facts pre pre.opA pre.opB
  refine Ends.pass (x := 3) (y := 0) (dst := dst) (n := n) (vlinAt s A B) ?round ?done hw
    pre.space rfl rfl
  case round =>
    intro j hj
    -- The two cells that round j reads have not been written yet.
    have  : wrote μ dst (vlinAt s A B) j (a + j) = A.getD j 0 :=
      (wrote_rest (by omega)).trans (pre.opA.read hj)
    have  : wrote μ dst (vlinAt s A B) j (b + j) = B.getD j 0 :=
      (wrote_rest (by omega)).trans (pre.opB.read hj)
    have  := pre.opA.read hj ▸ pre.opA.abs_read_le hj

    have  : |s * B.getD j 0| ≤ V := by
      rw [abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) pre.sign).trans (pre.opB.read hj ▸ pre.opB.abs_read_le hj)
    ram_arith [vlinAt, Limits.Addr]
  case done =>
    refine ⟨fun i hi => ?_, sameOutside_wrote (j := n) le_rfl⟩
    have hi' := by
      simp_all [vlinList] <;> omega
    change wrote μ dst (vlinAt s A B) n (dst + i) = _
    simp only [vlinList, List.getElem_zipWith]
    rw [wrote_done hi', vlinAt, List.getD_eq_getElem _ _ (by omega),
      List.getD_eq_getElem _ _ (by omega)]

/-- **vlin** as a procedure. -/
theorem vlin_meets {μ} {pVlin dst a b n} {s V} {A B}
    (hP : P[pVlin]? = some vlinBody) (hw : (lim.space : ℤ) ≤ lim.word)
    (pre : VlinPre lim μ dst a b n s V A B) :
    Meets lim P pVlin d [dst, a, b, n, s] μ (23 * n + 6) fun _ μ' =>
      Seg μ' dst (vlinList s A B) ∧ SameOutside μ μ' dst n :=
  Meets.of_body hP (vlin_spec hw pre)

/-! ## The product -/

/-- A term of the convolution. -/
def convTerm p (A B : List ℤ) r i :=
  A.getD i 0 * B.getD (if i ≤ r then r - i else r + p - i) 0

/-- The sum of the first j terms of entry r of the convolution. -/
def convPartialSum p A B r j :=
    ((List.range j).map (convTerm p A B r)).sum

/-- One more term. -/
theorem convPartialSum_succ p A B r j :
    convPartialSum p A B r (j + 1) = convPartialSum p A B r j + convTerm p A B r j :=
  List.sum_range_succ _ _

/-- The convolution is the list of these sums. -/
theorem cconv_eq_map_convPartialSum p A B :
    cconv p A B = (List.range p).map fun r => convPartialSum p A B r p := rfl

section

variable {p : ℕ} {A B : List ℤ} {α β : ℤ}

variable (leA : AbsLe A α) (leB : AbsLe B β) (hα : 0 ≤ α) (hβ : 0 ≤ β)

include leA leB hα hβ in
/-- A term is at most α β in absolute value. -/
theorem abs_convTerm_le  r i :
    |convTerm p A B r i| ≤ α * β := by
  rw [convTerm, abs_mul]
  exact mul_le_mul (AbsLe.abs_getD_le hα leA _) (AbsLe.abs_getD_le hβ leB _) (abs_nonneg _) hα

include leA leB hα hβ in
/-- A sum of j terms is at most j α β in absolute value. -/
theorem abs_convPartialSum_le
     r j :
    |convPartialSum p A B r j| ≤ j * (α * β) := by
  simpa [convPartialSum] using List.abs_sum_map_le (List.range j) (convTerm p A B r)
    fun i _ => abs_convTerm_le leA leB hα hβ r i

end


/-- One term: j := r - i or r + p - i; sum := sum + a[i] b[j]. -/
def cconvTerm  :=
  .ite (v 5 ≤' v 4) (.set 7 (v 4 -' v 5)) (.set 7 (v 4 +' v 3 -' v 5)) ;;
  .set 6 (v 6 +' M (v 1 +' v 5) *' M (v 2 +' v 7))

/-- One entry: sum := the entry number r of the convolution. -/
def cconvEntry  :=
  .set 6 (k 0) ;;
  .for 5 (v 3) cconvTerm

/-- cconv(dst, a, b, p): for r < p: dst[r] := the entry number r. -/
def cconvBody : Stmt :=
  .for 4 (v 3) (cconvEntry ;; .store (v 0 +' v 4) (v 6))

/-- What the inner loop of cconv assumes: the lists A and B of p numbers, bounded by α and β, stand
at a and b, and p α β fits in a word. -/
structure CconvPre (lim : Limits) (μ : Light.Memory) (a b p : ℕ) (α β : ℤ) (A B : List ℤ) : Prop where
  opA : ArrayAt μ a A p α lim.space
  opB : ArrayAt μ b B p β lim.space
  word : p * (α * β) ≤ lim.word
  nonnegA : 0 ≤ α := by light_arith
  nonnegB : 0 ≤ β := by light_arith
  room : 2 * p < lim.space := by light_arith

section

variable {μ : Light.Memory} {dst a b p r : ℕ} {α β : ℤ} {A B : List ℤ}

variable (hw : (lim.space : ℤ) ≤ lim.word) (pre : CconvPre lim μ a b p α β A B)

include hw pre in
/-- **One term of cconv.** -/
theorem cconvTerm_spec
    (hr : r < p) {i } (hi : i < p) (t ) :
    Ends lim P d cconvTerm ⟨frame [dst, a, b, p, r, i, convPartialSum p A B r i, t], μ⟩ 24 fun σ' =>
      ∃ t', σ' = ⟨frame [dst, a, b, p, r, i, convPartialSum p A B r (i + 1), t'], μ⟩ := by
  obtain ⟨opA, opB, hword, hα, hβ, room⟩ := pre
  light_facts opA opB
  have hreadA := opA.read hi
  have hterm := abs_le.1 (abs_convTerm_le (p := p) opA.bound opB.bound hα hβ r i)
  have hsum := abs_le.1 (abs_convPartialSum_le (p := p) opA.bound opB.bound hα hβ r (i + 1))
  have  : ((i + 1 : ℕ) : ℤ) * (α * β) ≤ lim.word :=
    (mul_le_mul_of_nonneg_right (mod_cast hi) (mul_nonneg hα hβ)).trans hword
  have  : α * β ≤ ((i + 1 : ℕ) : ℤ) * (α * β) :=
    le_mul_of_one_le_left (mul_nonneg hα hβ) (by push_cast; omega)
  rw [convPartialSum_succ] at hsum ⊢
  -- sum := sum + a[i] b[j], once j is the index of the term
  have  : ∀ j , j < p → convTerm p A B r i = A.getD i 0 * B.getD j 0 →
      Ends lim P d (.set 6 (v 6 +' M (v 1 +' v 5) *' M (v 2 +' v 7)))
        ⟨frame [dst, a, b, p, r, i, convPartialSum p A B r i, j], μ⟩ 12 fun σ' => ∃ t',
          σ' = ⟨frame [dst, a, b, p, r, i, convPartialSum p A B r i + convTerm p A B r i, t'],
            μ⟩ := by
    intro j hj hc
    have hreadB := opB.read hj
    rw [hc] at hterm hsum ⊢
    generalize A.getD i 0 = x at hreadA hterm hsum
    generalize B.getD j 0 = y at hreadB hterm hsum
    exact Ends.setTo _ ⟨j, rfl⟩ (by light_side [hreadA, hreadB])
  -- if i ≤ r then j := r - i else j := r + p - i
  refine Ends.next 12 (Ends.iteLast (fun hc => ?_) fun hc => ?_)
  · light_block [convTerm]
  · light_block [convTerm]

include hw pre in
/-- **One entry of cconv**, in at most 32 p + 8 steps. -/
theorem cconvEntry_spec
    (hr : r < p) (i₀ s₀ t₀ : ℤ) :
    Ends lim P d cconvEntry ⟨frame [dst, a, b, p, r, i₀, s₀, t₀], μ⟩ (32 * p + 8) fun σ' =>
      ∃ t, σ' = ⟨frame [dst, a, b, p, r, p, convPartialSum p A B r p, t], μ⟩ := by
  have room := pre.room
  -- sum := 0
  light_set 0
  -- for i < p: one term
  refine Ends.for (fun i σ => ∃ t, σ = ⟨frame [dst, a, b, p, r, i, convPartialSum p A B r i, t], μ⟩)
      p 24
    ⟨t₀, by simp [update_frame_setLocal, convPartialSum]⟩ ?round ?done ?bound
  case bound =>
    simp_all
  case round =>
    rintro i _ hi - ⟨t, rfl⟩
    refine (cconvTerm_spec hw pre hr hi t).mono le_rfl ?_
    rintro _ ⟨t', rfl⟩
    exact ⟨rfl, t', by simp [update_frame_setLocal]⟩
  case done => exact fun _ _ h => h

/-- The state of cconv before round r: the first r entries are written, and no cell outside dst has
changed. -/
def CconvInv (μ : Light.Memory) (dst a b p : ℕ) (A B : List ℤ) (r : ℕ) (σ : State) : Prop :=
  ∃ (i s t : ℤ) (μ' : Light.Memory), σ = ⟨frame [dst, a, b, p, r, i, s, t], μ'⟩ ∧
    (∀ e < r, μ' (dst + e) = convPartialSum p A B e p) ∧ SameOutside μ μ' dst p

include hw pre in
/-- **cconv** writes the cyclic convolution to dst and changes nothing else, in at most
32 p² + 21 p + 6 steps. -/
theorem cconv_spec
    (spaceDst : dst + p ≤ lim.space) (apartA : dst + p ≤ a ∨ a + p ≤ dst)
    (apartB : dst + p ≤ b ∨ b + p ≤ dst) :
    Ends lim P d cconvBody ⟨frame [dst, a, b, p], μ⟩ (32 * p * p + 21 * p + 6) fun σ' =>
      Seg σ'.mem dst (cconv p A B) ∧ SameOutside μ σ'.mem dst p := by
  refine Ends.for (CconvInv μ dst a b p A B) p (32 * p + 13) ?start ?round ?done ?bound
  case start =>
    exact ⟨0, 0, 0, μ, congrArg (fun loc => (⟨loc, μ⟩ : State))
      ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 3).symm),
      fun e he => absurd he (by omega), .refl⟩
  case bound =>
    rintro r _ - - ⟨i, s, t, μ', rfl, -, -⟩
    simp
  case round =>
    rintro r _ hr - ⟨i, s, t, μ', rfl, filled, rest⟩
    have pre' :=
      { pre with
        opA := pre.opA.keep, opB := pre.opB.keep }
    -- sum := the entry number r
    light_piece (cconvEntry_spec hw pre' hr i s t) with _ ⟨t', rfl⟩
    -- dst[r] := sum
    light_store (dst + r) (convPartialSum p A B r p)
    refine ⟨rfl, p, convPartialSum p A B r p, t',
      Function.update μ' (dst + r) (convPartialSum p A B r p), by simp [update_frame_setLocal],
      fun e he => ?_, rest.update ⟨by omega, by omega⟩ _⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 he with he | rfl
    · grind
    · exact Function.update_self ..
  case done =>
    rintro _ - ⟨i, s, t, μ', rfl, filled, rest⟩
    refine ⟨fun e he => ?_, rest⟩
    grind [cconv_eq_map_convPartialSum]

/-- **cconv** as a procedure. -/
theorem cconv_meets {pCconv} (hP : P[pCconv]? = some cconvBody)
    (hw : (lim.space : ℤ) ≤ lim.word) (pre : CconvPre lim μ a b p α β A B)
    (spaceDst : dst + p ≤ lim.space := by light_arith)
    (apartA : dst + p ≤ a ∨ a + p ≤ dst := by light_arith)
    (apartB : dst + p ≤ b ∨ b + p ≤ dst := by light_arith) :
    Meets lim P pCconv d [dst, a, b, p] μ (32 * p * p + 21 * p + 6) fun _ μ' =>
      Seg μ' dst (cconv p A B) ∧ SameOutside μ μ' dst p :=
  Meets.of_body hP (cconv_spec hw pre spaceDst apartA apartB)

end

end Light.Sec3
