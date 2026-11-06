module

public import ThreeSumApsp.Lang.Lib.ArrayAt
public import ThreeSumApsp.Lang.Lib.Pass
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Spec.Sec3.Theorem17.Cyclic
public import ThreeSumApsp.Spec.Sec3.Theorem17.Strassen
public import ThreeSumApsp.Lang.Lib.Seg
public import ThreeSumApsp.Lang.Lib.Copy

@[expose] public section

section
namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Sums and differences -/

namespace Vlin

/-- The local variables of vlin: the arguments dst, a, b, n, s, and the counter. -/
abbrev Dst : ℕ := 0
@[inherit_doc Dst] abbrev ArgA : ℕ := 1
@[inherit_doc Dst] abbrev ArgB : ℕ := 2
@[inherit_doc Dst] abbrev Len : ℕ := 3
@[inherit_doc Dst] abbrev Sign : ℕ := 4
@[inherit_doc Dst] abbrev Idx : ℕ := 5

end Vlin

open Vlin in
/-- vlin(dst, a, b, n, s): for i < n: dst[i] := a[i] + s b[i]. -/
def vlinBody : Stmt :=
  pass Idx (v Len) (v Dst) (M (v ArgA +' v Idx) +' v Sign *' M (v ArgB +' v Idx))

/-- The list that vlin writes. -/
def vlinList (s : ℤ) (A B : List ℤ) : List ℤ := List.zipWith (fun x y => x + s * y) A B

/-- With s = 1 it is the sum. -/
theorem vlinList_one (A B : List ℤ) : vlinList 1 A B = vadd A B := by
  simp [vlinList, vadd]

/-- With s = -1 it is the difference. -/
theorem vlinList_neg_one (A B : List ℤ) : vlinList (-1) A B = vsub A B := by
  unfold vlinList vsub
  congr 1
  funext x y
  ring

/-- Entry j of that list. -/
def vlinAt (s : ℤ) (A B : List ℤ) (j : ℕ) : ℤ := A.getD j 0 + s * B.getD j 0

/-- What vlin assumes: the lists A and B of n numbers of absolute value at most V stand at a and b;
the n cells at dst lie in the memory, do not meet b, and are the cells at a or do not meet them. -/
structure VlinPre (lim : Limits) (μ : ℕ → ℤ) (dst a b n : ℕ) (s V : ℤ) (A B : List ℤ) : Prop where
  opA : ArrayAt μ a A n V lim.space
  opB : ArrayAt μ b B n V lim.space
  sign : |s| ≤ 1
  word : 2 * V ≤ lim.word := by light_arith
  space : dst + n ≤ lim.space := by light_arith
  apartA : dst = a ∨ dst + n ≤ a ∨ a + n ≤ dst := by light_arith
  apartB : dst + n ≤ b ∨ b + n ≤ dst := by light_arith

open Vlin in
/-- **vlin** writes a + s b to dst and changes nothing else, in at most 23 n + 6 steps. -/
theorem vlin_spec {μ : ℕ → ℤ} {dst a b n : ℕ} {s V : ℤ} {A B : List ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (pre : VlinPre lim μ dst a b n s V A B) :
    Ends lim P d vlinBody ⟨frame [dst, a, b, n, s], μ⟩ (23 * n + 6) fun σ' =>
      Seg σ'.mem dst (vlinList s A B) ∧ SameOutside μ σ'.mem dst n := by
  light_facts pre pre.opA pre.opB
  refine Ends.pass (x := Len) (y := Dst) (dst := dst) (n := n) (vlinAt s A B) ?round ?done hw
    pre.space rfl rfl
  case round =>
    intro j hj
    -- The two cells that round j reads have not been written yet.
    have hreadA : wrote μ dst (vlinAt s A B) j (a + j) = A.getD j 0 :=
      (wrote_rest (by omega)).trans (pre.opA.read hj)
    have hreadB : wrote μ dst (vlinAt s A B) j (b + j) = B.getD j 0 :=
      (wrote_rest (by omega)).trans (pre.opB.read hj)
    have hx : |A.getD j 0| ≤ V := pre.opA.read hj ▸ pre.opA.abs_read_le hj
    have hy : |B.getD j 0| ≤ V := pre.opB.read hj ▸ pre.opB.abs_read_le hj
    have hsy : |s * B.getD j 0| ≤ V := by
      rw [abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) pre.sign).trans hy
    rw [abs_le] at hx hsy
    rw [vlinAt]
    generalize A.getD j 0 = x at hreadA hx
    generalize B.getD j 0 = y at hreadB hsy
    simp [Limits.Addr, abs_le, hreadA, hreadB, -abs_mul]
    omega
  case done =>
    refine ⟨fun i hi => ?_, sameOutside_wrote (j := n) le_rfl⟩
    have hi' : i < n := by
      simp only [vlinList, List.length_zipWith] at hi
      omega
    change wrote μ dst (vlinAt s A B) n (dst + i) = _
    simp only [vlinList, List.getElem_zipWith]
    rw [wrote_done hi', vlinAt, List.getD_eq_getElem _ _ (by omega),
      List.getD_eq_getElem _ _ (by omega)]

/-- **vlin** as a procedure. -/
theorem vlin_meets {μ : ℕ → ℤ} {pVlin dst a b n : ℕ} {s V : ℤ} {A B : List ℤ}
    (hP : P[pVlin]? = some vlinBody) (hw : (lim.space : ℤ) ≤ lim.word)
    (pre : VlinPre lim μ dst a b n s V A B) :
    Meets lim P pVlin d [dst, a, b, n, s] μ (23 * n + 6) fun _ μ' =>
      Seg μ' dst (vlinList s A B) ∧ SameOutside μ μ' dst n :=
  Meets.of_body hP (vlin_spec hw pre)

/-! ## The product -/

/-- A term of the convolution. -/
def convTerm (p : ℕ) (A B : List ℤ) (r i : ℕ) : ℤ :=
  A.getD i 0 * B.getD (if i ≤ r then r - i else r + p - i) 0

/-- The sum of the first j terms of entry r of the convolution. -/
def convPartialSum (p : ℕ) (A B : List ℤ) (r j : ℕ) : ℤ :=
    ((List.range j).map (convTerm p A B r)).sum

/-- One more term. -/
theorem convPartialSum_succ (p : ℕ) (A B : List ℤ) (r j : ℕ) :
    convPartialSum p A B r (j + 1) = convPartialSum p A B r j + convTerm p A B r j :=
  List.sum_range_succ _ _

/-- The convolution is the list of these sums. -/
theorem cconv_eq_map_convPartialSum (p : ℕ) (A B : List ℤ) :
    cconv p A B = (List.range p).map fun r => convPartialSum p A B r p := rfl

section bounds

variable {p : ℕ} {A B : List ℤ} {α β : ℤ}

/-- A term is at most α β in absolute value. -/
theorem abs_convTerm_le (leA : AbsLe A α) (leB : AbsLe B β) (hα : 0 ≤ α) (hβ : 0 ≤ β) (r i : ℕ) :
    |convTerm p A B r i| ≤ α * β := by
  rw [convTerm, abs_mul]
  exact mul_le_mul (AbsLe.abs_getD_le hα leA _) (AbsLe.abs_getD_le hβ leB _) (abs_nonneg _) hα

/-- A sum of j terms is at most j α β in absolute value. -/
theorem abs_convPartialSum_le (leA : AbsLe A α) (leB : AbsLe B β) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (r j : ℕ) :
    |convPartialSum p A B r j| ≤ j * (α * β) := by
  simpa [convPartialSum] using List.abs_sum_map_le (List.range j) (convTerm p A B r)
    fun i _ => abs_convTerm_le leA leB hα hβ r i

end bounds

namespace Cconv

/-- The local variables of cconv: the arguments dst, a, b, p; the number r of the entry; the number
i of the term; the sum (Acc); the index into b. -/
abbrev Dst : ℕ := 0
@[inherit_doc Dst] abbrev ArgA : ℕ := 1
@[inherit_doc Dst] abbrev ArgB : ℕ := 2
@[inherit_doc Dst] abbrev Len : ℕ := 3
@[inherit_doc Dst] abbrev Row : ℕ := 4
@[inherit_doc Dst] abbrev Idx : ℕ := 5
@[inherit_doc Dst] abbrev Acc : ℕ := 6
@[inherit_doc Dst] abbrev Jdx : ℕ := 7

end Cconv

open Cconv in
/-- One term: j := r - i or r + p - i; sum := sum + a[i] b[j]. -/
def cconvTerm : Stmt :=
  .ite (v Idx ≤' v Row) (.set Jdx (v Row -' v Idx)) (.set Jdx (v Row +' v Len -' v Idx)) ;;
  .set Acc (v Acc +' M (v ArgA +' v Idx) *' M (v ArgB +' v Jdx))

open Cconv in
/-- One entry: sum := the entry number r of the convolution. -/
def cconvEntry : Stmt :=
  .set Acc (k 0) ;;
  .for Idx (v Len) cconvTerm

open Cconv in
/-- cconv(dst, a, b, p): for r < p: dst[r] := the entry number r. -/
def cconvBody : Stmt :=
  .for Row (v Len) (cconvEntry ;; .store (v Dst +' v Row) (v Acc))

/-- What the inner loop of cconv assumes: the lists A and B of p numbers, bounded by α and β, stand
at a and b, and p α β fits in a word. -/
structure CconvPre (lim : Limits) (μ : ℕ → ℤ) (a b p : ℕ) (α β : ℤ) (A B : List ℤ) : Prop where
  opA : ArrayAt μ a A p α lim.space
  opB : ArrayAt μ b B p β lim.space
  word : p * (α * β) ≤ lim.word
  nonnegA : 0 ≤ α := by light_arith
  nonnegB : 0 ≤ β := by light_arith
  room : 2 * p < lim.space := by light_arith

section cconv

variable {μ : ℕ → ℤ} {dst a b p r : ℕ} {α β : ℤ} {A B : List ℤ}

open Cconv in
/-- **One term of cconv.** -/
theorem cconvTerm_spec (hw : (lim.space : ℤ) ≤ lim.word) (pre : CconvPre lim μ a b p α β A B)
    (hr : r < p) {i : ℕ} (hi : i < p) (t : ℤ) :
    Ends lim P d cconvTerm ⟨frame [dst, a, b, p, r, i, convPartialSum p A B r i, t], μ⟩ 24 fun σ' =>
      ∃ t', σ' = ⟨frame [dst, a, b, p, r, i, convPartialSum p A B r (i + 1), t'], μ⟩ := by
  obtain ⟨opA, opB, hword, hα, hβ, room⟩ := pre
  light_facts opA opB
  have hreadA : μ (a + i) = A.getD i 0 := opA.read hi
  have hterm := abs_le.1 (abs_convTerm_le (p := p) opA.bound opB.bound hα hβ r i)
  have hsum := abs_le.1 (abs_convPartialSum_le (p := p) opA.bound opB.bound hα hβ r (i + 1))
  have : ((i + 1 : ℕ) : ℤ) * (α * β) ≤ lim.word :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hi) (mul_nonneg hα hβ)).trans hword
  have : α * β ≤ ((i + 1 : ℕ) : ℤ) * (α * β) :=
    le_mul_of_one_le_left (mul_nonneg hα hβ) (by push_cast; omega)
  rw [convPartialSum_succ] at hsum ⊢
  -- sum := sum + a[i] b[j], once j is the index of the term
  have add : ∀ j : ℕ, j < p → convTerm p A B r i = A.getD i 0 * B.getD j 0 →
      Ends lim P d (.set Acc (v Acc +' M (v ArgA +' v Idx) *' M (v ArgB +' v Jdx)))
        ⟨frame [dst, a, b, p, r, i, convPartialSum p A B r i, j], μ⟩ 12 fun σ' => ∃ t',
          σ' = ⟨frame [dst, a, b, p, r, i, convPartialSum p A B r i + convTerm p A B r i, t'],
            μ⟩ := by
    intro j hj hc
    have hreadB : μ (b + j) = B.getD j 0 := opB.read hj
    rw [hc] at hterm hsum ⊢
    generalize A.getD i 0 = x at hreadA hterm hsum
    generalize B.getD j 0 = y at hreadB hterm hsum
    exact Ends.setTo _ ⟨j, rfl⟩ (by light_side [hreadA, hreadB])
  -- if i ≤ r then j := r - i else j := r + p - i
  refine Ends.next 12 (Ends.iteLast (fun hc => ?_) fun hc => ?_)
  · have hir : i ≤ r := by simpa using hc
    exact Ends.setTo (r - i : ℕ) (add _ (by omega) (by rw [convTerm, if_pos hir]))
  · have hir : ¬ i ≤ r := by simpa using hc
    exact Ends.setTo (r + p - i : ℕ) (add _ (by omega) (by rw [convTerm, if_neg hir]))

open Cconv in
/-- **One entry of cconv**, in at most 32 p + 8 steps. -/
theorem cconvEntry_spec (hw : (lim.space : ℤ) ≤ lim.word) (pre : CconvPre lim μ a b p α β A B)
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
    rintro i _ - - ⟨t, rfl⟩
    simp
  case round =>
    rintro i _ hi - ⟨t, rfl⟩
    refine (cconvTerm_spec hw pre hr hi t).mono le_rfl ?_
    rintro _ ⟨t', rfl⟩
    exact ⟨by simp, t', by simp [update_frame_setLocal]⟩
  case done => exact fun _ _ h => h

open Cconv in
/-- The state of cconv before round r: the first r entries are written, and no cell outside dst has
changed. -/
def CconvInv (μ : ℕ → ℤ) (dst a b p : ℕ) (A B : List ℤ) (r : ℕ) (σ : State) : Prop :=
  ∃ (i s t : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame [dst, a, b, p, r, i, s, t], μ'⟩ ∧
    (∀ e < r, μ' (dst + e) = convPartialSum p A B e p) ∧ SameOutside μ μ' dst p

open Cconv in
/-- **cconv** writes the cyclic convolution to dst and changes nothing else, in at most
32 p² + 21 p + 6 steps. -/
theorem cconv_spec (hw : (lim.space : ℤ) ≤ lim.word) (pre : CconvPre lim μ a b p α β A B)
    (spaceDst : dst + p ≤ lim.space) (apartA : dst + p ≤ a ∨ a + p ≤ dst)
    (apartB : dst + p ≤ b ∨ b + p ≤ dst) :
    Ends lim P d cconvBody ⟨frame [dst, a, b, p], μ⟩ (32 * p * p + 21 * p + 6) fun σ' =>
      Seg σ'.mem dst (cconv p A B) ∧ SameOutside μ σ'.mem dst p := by
  have room := pre.room
  -- for r < p
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
    have pre' : CconvPre lim μ' a b p α β A B :=
      { pre with
        opA := pre.opA.keep, opB := pre.opB.keep }
    -- sum := the entry number r
    light_piece (cconvEntry_spec hw pre' hr i s t) with _ ⟨t', rfl⟩
    -- dst[r] := sum
    light_store (dst + r) (convPartialSum p A B r p)
    refine ⟨by simp, p, convPartialSum p A B r p, t',
      Function.update μ' (dst + r) (convPartialSum p A B r p), by simp [update_frame_setLocal],
      fun e he => ?_, rest.update ⟨by omega, by omega⟩ _⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 he with he | rfl
    · exact (Function.update_of_ne (by omega) _ _).trans (filled e he)
    · exact Function.update_self ..
  case done =>
    rintro _ - ⟨i, s, t, μ', rfl, filled, rest⟩
    refine ⟨fun e he => ?_, rest⟩
    have he' : e < p := by simpa [cconv_eq_map_convPartialSum] using he
    simpa [cconv_eq_map_convPartialSum] using filled e he'

/-- **cconv** as a procedure. -/
theorem cconv_meets {pCconv : ℕ} (hP : P[pCconv]? = some cconvBody)
    (hw : (lim.space : ℤ) ≤ lim.word) (pre : CconvPre lim μ a b p α β A B)
    (spaceDst : dst + p ≤ lim.space := by light_arith)
    (apartA : dst + p ≤ a ∨ a + p ≤ dst := by light_arith)
    (apartB : dst + p ≤ b ∨ b + p ≤ dst := by light_arith) :
    Meets lim P pCconv d [dst, a, b, p] μ (32 * p * p + 21 * p + 6) fun _ μ' =>
      Seg μ' dst (cconv p A B) ∧ SameOutside μ μ' dst p :=
  Meets.of_body hP (cconv_spec hw pre spaceDst apartA apartB)

end cconv

end Light.Sec3
end

section
namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-- The list that vlin writes is as long as its operands. -/
theorem length_vlinList (s : ℤ) {A B : List ℤ} {n : ℕ} (hA : A.length = n) (hB : B.length = n) :
    (vlinList s A B).length = n := by
  simp [vlinList, hA, hB]

/-- With the sign 0 the first operand is kept. -/
theorem vlinList_zero {A B : List ℤ} (h : A.length = B.length) : vlinList 0 A B = A := by
  apply List.ext_getElem
  · simp [vlinList, h]
  · intro i h1 h2
    simp [vlinList]

/-- With the sign 0 and twice the same operand, the operand is kept. -/
theorem vlinList_zero_self (A : List ℤ) : vlinList 0 A A = A := vlinList_zero rfl

/-- Adding a list to zeros gives the list. -/
theorem vlinList_zeros_left {q : ℕ} {B : List ℤ} (h : B.length = q) :
    vlinList 1 (zeros q) B = B := by
  apply List.ext_getElem
  · simp [vlinList, zeros, h]
  · intro i h1 h2
    simp [vlinList, zeros]

/-- The bounds of the two operands add up. -/
theorem _root_.ThreeSumApsp.AbsLe.vlinList {s a b : ℤ} {A B : List ℤ} (hA : AbsLe A a)
    (hB : AbsLe B b)
    (hs : |s| ≤ 1) : AbsLe (vlinList s A B) (a + b) := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hiA : i < A.length := by simp only [Sec3.vlinList, List.length_zipWith] at hi; omega
  have hiB : i < B.length := by simp only [Sec3.vlinList, List.length_zipWith] at hi; omega
  simp only [Sec3.vlinList, List.getElem_zipWith]
  have hsy : |s * B[i]| ≤ b := by
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) hs).trans (hB.getElem hiB)
  exact le_trans (abs_add_le _ _) (add_le_add (hA.getElem hiA) hsy)

/-- A larger bound. -/
theorem _root_.ThreeSumApsp.AbsLe.trans_le {l : List ℤ} {a b : ℤ} (h : AbsLe l a) (hab : a ≤ b) :
    AbsLe l b := fun x hx => (h x hx).trans hab

/-- Zeros are bounded by 0. -/
theorem absLe_zeros (q : ℕ) : AbsLe (zeros q) 0 := by
  intro x hx
  simp only [zeros, List.mem_replicate] at hx
  simp [hx.2]

/-- A quarter of a list of 4 q numbers has q numbers. -/
theorem length_quarter {q t : ℕ} {l : List ℤ} (h : l.length = 4 * q) (ht : t < 4) :
    (quarter q t l).length = q := by
  have : (t + 1) * q ≤ 4 * q := Nat.mul_le_mul_right q (by omega)
  have : (t + 1) * q = t * q + q := by ring
  rw [quarter, List.length_take, List.length_drop, h]
  omega

/-- A bound for a list is a bound for its quarters. -/
theorem _root_.ThreeSumApsp.AbsLe.quarter {q t : ℕ} {l : List ℤ} {a : ℤ} (h : AbsLe l a) :
    AbsLe (quarter q t l) a :=
  fun x hx => h x (List.mem_of_mem_drop (List.mem_of_mem_take hx))

/-- A quarter of an array of 4 q numbers is an array of q numbers. -/
theorem _root_.Light.ArrayAt.quarter {μ : ℕ → ℤ} {a q t top : ℕ} {l : List ℤ} {U : ℤ}
    (h : ArrayAt μ a l (4 * q) U top) (ht : t < 4) :
    ArrayAt μ (a + t * q) (quarter q t l) q U top :=
  h.drop_take (Nat.mul_add_le_mul ht le_rfl)

/-- The list A + s B, once it stands at dst, is an array, and the bounds of A and B add up. -/
theorem _root_.Light.ArrayAt.vlinList {μ μ' : ℕ → ℤ} {a dst n top top' : ℕ} {A B : List ℤ}
    {s U V W : ℤ} (hA : ArrayAt μ a A n U top) (lenB : B.length = n) (leB : AbsLe B V)
    (hs : |s| ≤ 1) (seg : Seg μ' dst (vlinList s A B)) (hW : U + V ≤ W := by light_arith)
    (below : dst + n ≤ top' := by light_arith) : ArrayAt μ' dst (vlinList s A B) n W top' :=
  { len := length_vlinList s hA.len lenB, seg, bound := (hA.bound.vlinList leB hs).trans_le hW
    below }

/-- A product in the ring has p numbers. -/
theorem length_cconv (p : ℕ) (A B : List ℤ) : (cconv p A B).length = p := by simp [cconv]

/-- The product of two matrices of 4^j vectors has 4^j vectors. -/
theorem length_strassenList (p : ℕ) :
    ∀ (j : ℕ) (A B : List ℤ), A.length = 4 ^ j * p → B.length = 4 ^ j * p →
      (strassenList p j A B).length = 4 ^ j * p
  | 0, A, B, _, _ => by simp [strassenList, length_cconv]
  | j + 1, A, B, hA, hB => by
    have hA' : A.length = 4 * (4 ^ j * p) := by rw [hA]; ring
    have hB' : B.length = 4 * (4 ^ j * p) := by rw [hB]; ring
    have qa : ∀ t < 4, (quarter (4 ^ j * p) t A).length = 4 ^ j * p :=
      fun t ht => length_quarter hA' ht
    have qb : ∀ t < 4, (quarter (4 ^ j * p) t B).length = 4 ^ j * p :=
      fun t ht => length_quarter hB' ht
    have hs : ∀ X Y : List ℤ, X.length = 4 ^ j * p → Y.length = 4 ^ j * p →
        (strassenList p j X Y).length = 4 ^ j * p := length_strassenList p j
    have ha : ∀ X Y : List ℤ, X.length = 4 ^ j * p → Y.length = 4 ^ j * p →
        (vadd X Y).length = 4 ^ j * p :=
      fun X Y hX hY => by simp [vadd, hX, hY]
    have hb : ∀ X Y : List ℤ, X.length = 4 ^ j * p → Y.length = 4 ^ j * p →
        (vsub X Y).length = 4 ^ j * p :=
      fun X Y hX hY => by simp [vsub, hX, hY]
    simp only [strassenList, List.length_append]
    rw [ha, ha, ha, ha]
    · ring
    all_goals
      repeat' first
        | apply ha | apply hb | apply hs | exact qa _ (by omega) | exact qb _ (by omega)

/-- The product of a phase. -/
def phaseM (p j : ℕ) (sA : ℤ) (A1 A2 : List ℤ) (sB : ℤ) (B1 B2 : List ℤ) : List ℤ :=
  strassenList p j (vlinList sA A1 A2) (vlinList sB B1 B2)

/-- The bound on all the numbers that the routine forms at level `j`, for operands bounded by `α`
and `β`. -/
def strassenBound (p j : ℕ) (α β : ℤ) : ℤ := 16 ^ j * (p * α * β)

/-- The bound is not negative. -/
theorem strassenBound_nonneg {p j : ℕ} {α β : ℤ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    0 ≤ strassenBound p j α β := by
  unfold strassenBound
  positivity

/-- The bound of level j + 1 in terms of the bound of level j, for operands that are sums of two. -/
theorem strassenBound_succ (p j : ℕ) (α β : ℤ) :
    strassenBound p (j + 1) α β = 4 * strassenBound p j (2 * α) (2 * β) := by
  unfold strassenBound
  ring

/-- The bound on the entries of the product of two matrices of zeros and ones. -/
theorem strassenBound_one_one (p K : ℕ) : strassenBound p K 1 1 = ((16 ^ K * p : ℕ) : ℤ) := by
  unfold strassenBound
  push_cast
  ring

/-- The bound is at least the bound α for the first operand. -/
theorem le_strassenBound_left {p j : ℕ} {α β : ℤ} (hp : 1 ≤ p) (hα : 1 ≤ α) (hβ : 1 ≤ β) :
    α ≤ strassenBound p j α β := by
  have : (1 : ℤ) ≤ 16 ^ j := one_le_pow₀ (by norm_num)
  have : (1 : ℤ) ≤ p := by exact_mod_cast hp
  have hα0 : 0 ≤ α := by omega
  calc α = 1 * (1 * α * 1) := by ring
    _ ≤ 16 ^ j * (p * α * β) := by gcongr

/-- The bound is at least the bound β for the second operand. -/
theorem le_strassenBound_right {p j : ℕ} {α β : ℤ} (hp : 1 ≤ p) (hα : 1 ≤ α) (hβ : 1 ≤ β) :
    β ≤ strassenBound p j α β := by
  have : (1 : ℤ) ≤ 16 ^ j := one_le_pow₀ (by norm_num)
  have : (1 : ℤ) ≤ p := by exact_mod_cast hp
  have hβ0 : 0 ≤ β := by omega
  calc β = 1 * (1 * 1 * β) := by ring
    _ ≤ 16 ^ j * (p * α * β) := by gcongr

/-- A product in the ring is bounded by p α β. -/
theorem absLe_cconv {p : ℕ} {A B : List ℤ} {α β : ℤ} (leA : AbsLe A α) (leB : AbsLe B β)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) : AbsLe (cconv p A B) (p * α * β) := by
  intro x hx
  rw [cconv_eq_map_convPartialSum] at hx
  obtain ⟨r, -, rfl⟩ := List.mem_map.mp hx
  have := abs_convPartialSum_le (p := p) leA leB hα hβ r p
  rwa [← mul_assoc] at this

/-- The entries of a sum. -/
theorem _root_.ThreeSumApsp.AbsLe.vadd {X Y : List ℤ} {x y : ℤ} (hX : AbsLe X x) (hY : AbsLe Y y) :
    AbsLe (vadd X Y) (x + y) := by
  rw [← vlinList_one]
  exact hX.vlinList hY (by simp)

/-- The entries of a difference. -/
theorem _root_.ThreeSumApsp.AbsLe.vsub {X Y : List ℤ} {x y : ℤ} (hX : AbsLe X x) (hY : AbsLe Y y) :
    AbsLe (vsub X Y) (x + y) := by
  rw [← vlinList_neg_one]
  exact hX.vlinList hY (by simp)

/-- The entries of a sum of two lists with the same bound. -/
theorem _root_.ThreeSumApsp.AbsLe.vadd_self {X Y : List ℤ} {c : ℤ} (hX : AbsLe X c)
    (hY : AbsLe Y c) :
    AbsLe (vadd X Y) (2 * c) :=
  (hX.vadd hY).trans_le (by omega)

/-- The entries of a difference of two lists with the same bound. -/
theorem _root_.ThreeSumApsp.AbsLe.vsub_self {X Y : List ℤ} {c : ℤ} (hX : AbsLe X c)
    (hY : AbsLe Y c) :
    AbsLe (vsub X Y) (2 * c) :=
  (hX.vsub hY).trans_le (by omega)

/-- The entries of the result of the routine, and of the products of its phases, are bounded. -/
theorem absLe_strassenList (p : ℕ) :
    ∀ (j : ℕ) (A B : List ℤ) (α β : ℤ), AbsLe A α → AbsLe B β → 0 ≤ α → 0 ≤ β →
      AbsLe (strassenList p j A B) (strassenBound p j α β)
  | 0, A, B, α, β, leA, leB, hα, hβ => by
    simpa [strassenList, strassenBound] using absLe_cconv (p := p) leA leB hα hβ
  | j + 1, A, B, α, β, leA, leB, hα, hβ => by
    have ih : ∀ X Y : List ℤ, AbsLe X (2 * α) → AbsLe Y (2 * β) →
        AbsLe (strassenList p j X Y) (strassenBound p j (2 * α) (2 * β)) := fun X Y hX hY =>
      absLe_strassenList p j X Y _ _ hX hY (by omega) (by omega)
    have qa : ∀ t, AbsLe (quarter (4 ^ j * p) t A) α := fun t => leA.quarter
    have qb : ∀ t, AbsLe (quarter (4 ^ j * p) t B) β := fun t => leB.quarter
    have qa2 : ∀ t, AbsLe (quarter (4 ^ j * p) t A) (2 * α) := fun t => (qa t).trans_le (by omega)
    have qb2 : ∀ t, AbsLe (quarter (4 ^ j * p) t B) (2 * β) := fun t => (qb t).trans_le (by omega)
    -- the seven products of Strassen's algorithm
    have m1 := ih _ _ ((qa 0).vadd_self (qa 3)) ((qb 0).vadd_self (qb 3))
    have m2 := ih _ _ ((qa 2).vadd_self (qa 3)) (qb2 0)
    have m3 := ih _ _ (qa2 0) ((qb 1).vsub_self (qb 3))
    have m4 := ih _ _ (qa2 3) ((qb 2).vsub_self (qb 0))
    have m5 := ih _ _ ((qa 0).vadd_self (qa 1)) (qb2 3)
    have m6 := ih _ _ ((qa 2).vsub_self (qa 0)) ((qb 0).vadd_self (qb 1))
    have m7 := ih _ _ ((qa 1).vsub_self (qa 3)) ((qb 2).vadd_self (qb 3))
    have : 0 ≤ strassenBound p j (2 * α) (2 * β) :=
      strassenBound_nonneg (by omega) (by omega)
    rw [strassenBound_succ]
    simp only [strassenList]
    intro x hx
    simp only [List.mem_append] at hx
    -- each quadrant of the result is a sum of at most four of them
    rcases hx with ((hx | hx) | hx) | hx
    · exact (((m1.vadd m4).vsub m5).vadd m7).trans_le (by omega) x hx
    · exact (m3.vadd m5).trans_le (by omega) x hx
    · exact (m2.vadd m4).trans_le (by omega) x hx
    · exact (((m1.vsub m2).vadd m3).vadd m6).trans_le (by omega) x hx

/-- The product of a phase on quarters of the operands has the length of a quarter. -/
theorem length_phaseM_quarter {p j : ℕ} {A B : List ℤ} (hA : A.length = 4 * (4 ^ j * p))
    (hB : B.length = 4 * (4 ^ j * p)) (sA sB : ℤ) {t1 t2 t3 t4 : ℕ}
    (ht : t1 < 4 ∧ t2 < 4 ∧ t3 < 4 ∧ t4 < 4 := by omega) :
    (phaseM p j sA (quarter (4 ^ j * p) t1 A) (quarter (4 ^ j * p) t2 A) sB
      (quarter (4 ^ j * p) t3 B) (quarter (4 ^ j * p) t4 B)).length = 4 ^ j * p := by
  obtain ⟨h1, h2, h3, h4⟩ := ht
  exact length_strassenList p j _ _
    (length_vlinList _ (length_quarter hA h1) (length_quarter hA h2))
    (length_vlinList _ (length_quarter hB h3) (length_quarter hB h4))

/-- **The seven phases give Strassen's algorithm.** -/
theorem strassenList_succ_eq_phases (p j : ℕ) (A B : List ℤ) (hA : A.length = 4 ^ (j + 1) * p)
    (hB : B.length = 4 ^ (j + 1) * p) :
    let q := 4 ^ j * p
    let a := fun t => quarter q t A
    let b := fun t => quarter q t B
    let m1 := phaseM p j 1 (a 0) (a 3) 1 (b 0) (b 3)
    let m2 := phaseM p j 1 (a 2) (a 3) 0 (b 0) (b 0)
    let m3 := phaseM p j 0 (a 0) (a 0) (-1) (b 1) (b 3)
    let m4 := phaseM p j 0 (a 3) (a 3) (-1) (b 2) (b 0)
    let m5 := phaseM p j 1 (a 0) (a 1) 0 (b 3) (b 3)
    let m6 := phaseM p j (-1) (a 2) (a 0) 1 (b 0) (b 1)
    let m7 := phaseM p j (-1) (a 1) (a 3) 1 (b 2) (b 3)
    strassenList p (j + 1) A B
      = vlinList 1 (vlinList 0 (vlinList (-1) (vlinList 1 (vlinList 1 (zeros q) m1) m4) m5) m6) m7
        ++ vlinList 1 (vlinList 1 (zeros q) m3) m5
        ++ vlinList 1 (vlinList 1 (zeros q) m2) m4
        ++ vlinList 0 (vlinList 1 (vlinList 1 (vlinList (-1) (vlinList 1 (zeros q) m1) m2) m3) m6)
          m7 := by
  intro q a b m1 m2 m3 m4 m5 m6 m7
  have hA' : A.length = 4 * q := by rw [hA]; ring
  have hB' : B.length = 4 * q := by rw [hB]; ring
  have len1 : m1.length = q := length_phaseM_quarter hA' hB' _ _
  have len2 : m2.length = q := length_phaseM_quarter hA' hB' _ _
  have len3 : m3.length = q := length_phaseM_quarter hA' hB' _ _
  have len4 : m4.length = q := length_phaseM_quarter hA' hB' _ _
  have len5 : m5.length = q := length_phaseM_quarter hA' hB' _ _
  have len6 : m6.length = q := length_phaseM_quarter hA' hB' _ _
  have len7 : m7.length = q := length_phaseM_quarter hA' hB' _ _
  rw [vlinList_zeros_left len1, vlinList_zeros_left len3, vlinList_zeros_left len2,
    vlinList_zero (A := vlinList (-1) (vlinList 1 m1 m4) m5) (B := m6)
      (by rw [length_vlinList _ (length_vlinList _ len1 len4) len5, len6]),
    vlinList_zero (A := vlinList 1 (vlinList 1 (vlinList (-1) m1 m2) m3) m6) (B := m7)
      (by rw [length_vlinList _ (length_vlinList _ (length_vlinList _ len1 len2) len3) len6, len7])]
  simp only [m1, m2, m3, m4, m5, m6, m7, phaseM, vlinList_one, vlinList_neg_one, vlinList_zero_self]
  rfl

end Light.Sec3
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The table of the sizes of Strassen's recursion

szTable(dst, p, J) writes the sizes p, 4p, …, 4^J p of the matrices of Strassen's recursion, the
list `szList p J`, and changes nothing else (`szTable_spec`, `szTable_meets`).
-/


namespace Light.Sec3

variable {lim : Limits} {P : Program} {d : ℕ}

/-- The table of the sizes: 4^i p for i ≤ J. -/
def szList (p J : ℕ) : List ℤ := (List.range (J + 1)).map fun i : ℕ => ((4 ^ i * p : ℕ) : ℤ)

/-- The table of the sizes has J + 1 entries. -/
@[simp] theorem length_szList (p J : ℕ) : (szList p J).length = J + 1 := by simp [szList]

namespace SzTable

/-- The local variables of szTable: the arguments dst, p, J; the exponent; the entry. -/
abbrev Dst : ℕ := 0
@[inherit_doc Dst] abbrev Prime : ℕ := 1
@[inherit_doc Dst] abbrev Top : ℕ := 2
@[inherit_doc Dst] abbrev Exp : ℕ := 3
@[inherit_doc Dst] abbrev Entry : ℕ := 4

end SzTable

open SzTable in
/-- szTable(dst, p, J). -/
def szTableBody : Stmt :=
  .set Exp (k 0) ;;
  .set Entry (v Prime) ;;
  .store (v Dst) (v Entry) ;;
  .while (v Exp <' v Top) (
    .set Entry (k 4 *' v Entry) ;;
    .set Exp (v Exp +' k 1) ;;
    .store (v Dst +' v Exp) (v Entry))

/-- An upper bound on the number of steps of szTable. -/
def tSzTable (J : ℕ) : ℕ := 17 * J + 11

/-- One more entry of the table. -/
theorem szList_succ (p J : ℕ) :
    szList p (J + 1) = szList p J ++ [((4 ^ (J + 1) * p : ℕ) : ℤ)] := by
  simp [szList, List.range_succ]

/-- The state of szTable before round j: the entries p, …, 4^j p are written, the last of them is in
a local, and no cell outside the table has changed. -/
def SzInv (μ : ℕ → ℤ) (dst p J j : ℕ) (σ : State) : Prop :=
  ∃ μ', σ = ⟨frame [dst, p, J, j, (4 ^ j * p : ℕ)], μ'⟩ ∧ Seg μ' dst (szList p j) ∧
    SameOutside μ μ' dst (J + 1)

/-- **szTable** writes p, 4p, …, 4^J p and changes nothing else. -/
theorem szTable_spec {μ : ℕ → ℤ} {dst p J : ℕ} (hw : (lim.space : ℤ) ≤ lim.word)
    (h4 : (4 : ℤ) ≤ lim.word) (hdst : dst + (J + 1) ≤ lim.space)
    (hp : ((4 ^ J * p : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d szTableBody ⟨frame [dst, p, J], μ⟩ (tSzTable J) fun σ' =>
      Seg σ'.mem dst (szList p J) ∧ SameOutside μ σ'.mem dst (J + 1) := by
  have hfits : ∀ j ≤ J, ((4 ^ j * p : ℕ) : ℤ) ≤ lim.word := fun j hj =>
    le_trans (by exact_mod_cast Nat.mul_le_mul_right p (Nat.pow_le_pow_right (by norm_num) hj)) hp
  unfold tSzTable
  -- exp := 0; entry := p; dst[0] := entry
  light_set (0 : ℕ)
  light_set p
  light_store dst p
  -- while exp < J
  refine Ends.whileBlock (SzInv μ dst p J) J ?start ?round ?done
  case start =>
    refine ⟨Function.update μ dst p, by simp, ?_, SameOutside.refl.update ⟨by omega, by omega⟩ _⟩
    simpa [szList] using (Seg.nil (μ := μ) (a := dst)).snoc p
  case round =>
    rintro j _ hj ⟨μ', rfl, seg, rest⟩
    have hnext := hfits (j + 1) hj
    have hfour : 4 ^ (j + 1) * p = 4 * (4 ^ j * p) := by ring
    have haddr : ((dst : ℤ) + ((j : ℤ) + 1)).toNat = dst + (szList p j).length := by
      rw [length_szList]
      omega
    -- entry := 4 entry; exp := exp + 1; dst[exp] := entry
    refine ⟨by light_side, by light_side, ?_, Function.update μ' (dst + (szList p j).length)
      ((4 ^ (j + 1) * p : ℕ) : ℤ), ?_, szList_succ p j ▸ seg.snoc _,
      rest.update ⟨by omega, by rw [length_szList]; omega⟩ _⟩
    · rw [hfour] at hnext
      generalize 4 ^ j * p = q at hnext
      light_side
    · rw [hfour]
      simp [update_frame_setLocal, haddr]
  case done =>
    rintro _ ⟨μ', rfl, seg, rest⟩
    exact ⟨by light_side, by light_side, seg, rest⟩

/-- **szTable** as a procedure. -/
theorem szTable_meets {μ : ℕ → ℤ} {q dst p J : ℕ} (hP : P[q]? = some szTableBody)
    (hw : (lim.space : ℤ) ≤ lim.word) (h4 : (4 : ℤ) ≤ lim.word) (hdst : dst + (J + 1) ≤ lim.space)
    (hp : ((4 ^ J * p : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P q d [dst, p, J] μ (tSzTable J) fun _ μ' =>
      Seg μ' dst (szList p J) ∧ SameOutside μ μ' dst (J + 1) :=
  Meets.of_body hP (szTable_spec hw h4 hdst hp)


/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Strassen's algorithm for matrices over ℤ[x]/(x^p - 1) in Z-order

"Computing PQ takes […] O(n^{log₂ 7}) with Strassen's algorithm" (proof of Theorem 17).

strassen(dst, a, b, j, szt, p, scr): dst := a · b for 2^j × 2^j matrices whose entries are vectors
of p numbers, stored in Z-order, so that the four quadrants of a matrix are the four quarters of its
segment.  szt is the address of the table of the sizes 4^i p, and scr is scratch space.

* At level 0 the product is one product in the ring (`strassen_zero`).
* At level j + 1 the routine clears dst and runs seven phases (`strassen_succ`).  phase(a1, a2, sA,
  b1, b2, sB, c1, s1, c2, s2, j, szt, p, scr, q) forms S = a1 + sA a2 and T = b1 + sB b2 in the
  scratch space, M = S · T by a recursive call, and adds s1 M to c1 and s2 M to c2 (`phase_meets`).
* Between two phases the four quarters of dst hold four lists, and the operands and the table are in
  place (`StrInv`); a phase changes two of the lists (`phase_step`).  After the seven phases the
  four lists are the four quadrants of the product (`sevenPhases_spec`).
* `strassen_spec` is the induction on the level: the product stands at dst after at most
  `strSteps p j` steps, and nothing has changed outside dst and `strScr p j` cells of scratch space.
  The recursion `strSteps` is bounded where the running times are added up.
-/



open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The program -/

/-- The numbers of the procedures that Strassen's algorithm consists of. -/
structure StrNums : Type where
  pVlin : ℕ
  pCconv : ℕ
  pFill : ℕ
  pPhase : ℕ
  pStr : ℕ

namespace Phase

/-- The local variables of phase: the arguments a1, a2, sA, b1, b2, sB, c1, s1, c2, s2, j, szt, p,
scr, q, and a local that takes the results of the calls. -/
abbrev OpA1 : ℕ := 0
@[inherit_doc OpA1] abbrev OpA2 : ℕ := 1
@[inherit_doc OpA1] abbrev SignA : ℕ := 2
@[inherit_doc OpA1] abbrev OpB1 : ℕ := 3
@[inherit_doc OpA1] abbrev OpB2 : ℕ := 4
@[inherit_doc OpA1] abbrev SignB : ℕ := 5
@[inherit_doc OpA1] abbrev Out1 : ℕ := 6
@[inherit_doc OpA1] abbrev Sign1 : ℕ := 7
@[inherit_doc OpA1] abbrev Out2 : ℕ := 8
@[inherit_doc OpA1] abbrev Sign2 : ℕ := 9
@[inherit_doc OpA1] abbrev Level : ℕ := 10
@[inherit_doc OpA1] abbrev Sizes : ℕ := 11
@[inherit_doc OpA1] abbrev Prime : ℕ := 12
@[inherit_doc OpA1] abbrev Scr : ℕ := 13
@[inherit_doc OpA1] abbrev Size : ℕ := 14
@[inherit_doc OpA1] abbrev Res : ℕ := 15

end Phase

open Phase in
/-- The operands of a phase: S := a1 + sA a2 at scr, and T := b1 + sB b2 at scr + q. -/
def phaseOpnds (ν : StrNums) : Stmt :=
  .call ν.pVlin [v Scr, v OpA1, v OpA2, v Size, v SignA] Res ;;
  .call ν.pVlin [v Scr +' v Size, v OpB1, v OpB2, v Size, v SignB] Res

open Phase in
/-- The end of a phase: c1 := c1 + s1 M and c2 := c2 + s2 M, where M stands at scr + 2 q. -/
def phaseAccum (ν : StrNums) : Stmt :=
  .call ν.pVlin [v Out1, v Out1, v Scr +' v Size +' v Size, v Size, v Sign1] Res ;;
  .call ν.pVlin [v Out2, v Out2, v Scr +' v Size +' v Size, v Size, v Sign2] Res

open Phase in
/-- phase(a1, a2, sA, b1, b2, sB, c1, s1, c2, s2, j, szt, p, scr, q): the operands; M := S · T at
scr + 2 q, with the scratch space from scr + 3 q on; the end. -/
def phaseBody (ν : StrNums) : Stmt :=
  phaseOpnds ν ;;
  .call ν.pStr [v Scr +' v Size +' v Size, v Scr, v Scr +' v Size, v Level, v Sizes, v Prime,
    v Scr +' v Size +' v Size +' v Size] Res ;;
  phaseAccum ν

namespace Str

/-- The local variables of strassen: the arguments dst, a, b, j, szt, p, scr; the numbers q, 2q, 3q,
where q is the size of a quarter; j - 1; a local that is not used; a local that takes the results of
the calls. -/
abbrev Dst : ℕ := 0
@[inherit_doc Dst] abbrev ArgA : ℕ := 1
@[inherit_doc Dst] abbrev ArgB : ℕ := 2
@[inherit_doc Dst] abbrev Level : ℕ := 3
@[inherit_doc Dst] abbrev Sizes : ℕ := 4
@[inherit_doc Dst] abbrev Prime : ℕ := 5
@[inherit_doc Dst] abbrev Scr : ℕ := 6
@[inherit_doc Dst] abbrev Size1 : ℕ := 7
@[inherit_doc Dst] abbrev Size2 : ℕ := 8
@[inherit_doc Dst] abbrev Size3 : ℕ := 9
@[inherit_doc Dst] abbrev Below : ℕ := 10
@[inherit_doc Dst] abbrev Res : ℕ := 12

end Str

open Str in
/-- The address of the quarter number t of the segment whose address is in local x. -/
@[simp] def qAddr (x : ℕ) : ℕ → Expr
  | 0 => v x
  | 1 => v x +' v Size1
  | 2 => v x +' v Size2
  | _ => v x +' v Size3

/-- The sign 1. -/
@[simp] def sPos : Expr := k 1

/-- The sign 0. -/
@[simp] def sNil : Expr := k 0

/-- The sign -1. -/
@[simp] def sNeg : Expr := k 0 -' k 1

open Str in
/-- A call of phase from the body of strassen: the operands are the quarters number a1, a2 of a and
b1, b2 of b, and the results go to the quarters number c1, c2 of dst. -/
def phaseCall (ν : StrNums) (a1 a2 : ℕ) (sA : Expr) (b1 b2 : ℕ) (sB : Expr) (c1 : ℕ) (s1 : Expr)
    (c2 : ℕ) (s2 : Expr) : Stmt :=
  .call ν.pPhase [qAddr ArgA a1, qAddr ArgA a2, sA, qAddr ArgB b1, qAddr ArgB b2, sB, qAddr Dst c1,
    s1, qAddr Dst c2, s2, v Below, v Sizes, v Prime, v Scr, v Size1] Res

/-- The seven phases. -/
def sevenPhases (ν : StrNums) : Stmt :=
  phaseCall ν 0 3 sPos 0 3 sPos 0 sPos 3 sPos ;;
  phaseCall ν 2 3 sPos 0 0 sNil 2 sPos 3 sNeg ;;
  phaseCall ν 0 0 sNil 1 3 sNeg 1 sPos 3 sPos ;;
  phaseCall ν 3 3 sNil 2 0 sNeg 0 sPos 2 sPos ;;
  phaseCall ν 0 1 sPos 3 3 sNil 0 sNeg 1 sPos ;;
  phaseCall ν 2 0 sNeg 0 1 sPos 3 sPos 0 sNil ;;
  phaseCall ν 1 3 sNeg 2 3 sPos 0 sPos 3 sNil

open Str in
/-- strassen(dst, a, b, j, szt, p, scr). -/
def strBody (ν : StrNums) : Stmt :=
  .ite (v Level =' k 0)
    (.call ν.pCconv [v Dst, v ArgA, v ArgB, v Prime] Res)
    (.set Below (v Level -' k 1) ;;
     .set Size1 (M (v Sizes +' v Below)) ;;
     .set Size2 (v Size1 +' v Size1) ;;
     .set Size3 (v Size2 +' v Size1) ;;
     .call ν.pFill [v Dst, v Size3 +' v Size1, k 0] Res ;;
     sevenPhases ν)

/-- The procedures of Strassen's algorithm stand in the program at their numbers. -/
structure StrProg (P : Program) (ν : StrNums) : Prop where
  vlin : P[ν.pVlin]? = some vlinBody
  cconv : P[ν.pCconv]? = some cconvBody
  fill : P[ν.pFill]? = some fillBody
  phase : P[ν.pPhase]? = some (phaseBody ν)
  str : P[ν.pStr]? = some (strBody ν)

/-! ## The specification -/

/-- The scratch space of strassen at level j. -/
def strScr (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => 3 * (4 ^ j * p) + strScr p j

/-- The steps of strassen at level j.  At level j + 1, with q = 4^j p: seven phases, each with a
recursive call and 92 q further steps, and the clearing of 4 q cells in 13 steps each, so that
696 = 7 · 92 + 4 · 13; the 900 covers the steps that do not depend on q. -/
def strSteps (p : ℕ) : ℕ → ℕ
  | 0 => 32 * p * p + 21 * p + 16
  | j + 1 => 7 * strSteps p j + 696 * (4 ^ j * p) + 900


/-- The arguments of strassen other than the level, with the data behind them: the operands `A` and
`B` have `len` numbers each, bounded by `α` and `β`, and the table of sizes reaches level `J`. -/
structure StrArgs : Type where
  (dst a b szt p scr : ℕ)
  (len J : ℕ)
  (A B : List ℤ)
  (α β : ℤ)

/-- The values of the arguments of strassen at level j. -/
abbrev StrArgs.vals (x : StrArgs) (j : ℕ) : List ℤ := [x.dst, x.a, x.b, j, x.szt, x.p, x.scr]

/-- What strassen assumes at level j.  The operands have len = 4^j p numbers each.  They and the
table of sizes lie below dst, and dst lies below the scratch space. -/
structure StrPre (lim : Limits) (μ : ℕ → ℤ) (j : ℕ) (x : StrArgs) : Prop where
  size : x.len = 4 ^ j * x.p
  prime : 1 ≤ x.p
  opA : ArrayAt μ x.a x.A x.len x.α x.dst
  opB : ArrayAt μ x.b x.B x.len x.β x.dst
  table : ListAt μ x.szt (szList x.p x.J) (x.J + 1) x.dst
  oneA : 1 ≤ x.α := by light_arith
  oneB : 1 ≤ x.β := by light_arith
  word : 4 * strassenBound x.p j x.α x.β ≤ lim.word := by light_arith
  level : j ≤ x.J := by light_arith
  dstBelow : x.dst + x.len ≤ x.scr := by light_arith
  space : x.scr + strScr x.p j ≤ lim.space := by light_arith
  room : 8 * x.len < lim.space := by light_arith

/-- What strassen assumes still holds when no cell below dst has changed. -/
theorem StrPre.keep {μ μ' : ℕ → ℤ} {j : ℕ} {x : StrArgs} (pre : StrPre lim μ j x)
    (hs : Kept μ μ' x.dst := by light_keep) : StrPre lim μ' j x :=
  { pre with opA := pre.opA.keep, opB := pre.opB.keep, table := pre.table.keep }

/-- What strassen does at level j, in the program P: it writes the product to dst and changes
nothing else but the scratch space. -/
def StrSpec (lim : Limits) (P : Program) (ν : StrNums) (j : ℕ) : Prop :=
  ∀ (x : StrArgs) (μ : ℕ → ℤ), StrPre lim μ j x → ∀ d, d + 2 * j + 1 ≤ lim.depth →
    Meets lim P ν.pStr d (x.vals j) μ (strSteps x.p j) fun _ μ' =>
      Seg μ' x.dst (strassenList x.p j x.A x.B) ∧ SameOutside2 μ μ' x.dst x.len x.scr (strScr x.p j)

/-! ## A phase -/

/-- The arguments of phase other than the level, with the data behind them: the six lists that stand
at the six addresses, the bounds `α` and `β` on the operands, and the level `J` that the table of
sizes reaches. -/
structure PhaseArgs : Type where
  (a1 a2 : ℕ) (sA : ℤ) (b1 b2 : ℕ) (sB : ℤ) (c1 : ℕ) (s1 : ℤ) (c2 : ℕ) (s2 : ℤ)
  (szt p scr q J : ℕ)
  (A1 A2 B1 B2 C1 C2 : List ℤ)
  (α β : ℤ)

namespace PhaseArgs

variable (x : PhaseArgs) (j : ℕ)

/-- The values of the arguments of phase at level j. -/
abbrev vals : List ℤ :=
  [x.a1, x.a2, x.sA, x.b1, x.b2, x.sB, x.c1, x.s1, x.c2, x.s2, j, x.szt, x.p, x.scr, x.q]

/-- The first operand of the product of the phase, S = A1 + sA A2. -/
abbrev S : List ℤ := vlinList x.sA x.A1 x.A2

/-- The second operand of the product of the phase, T = B1 + sB B2. -/
abbrev T : List ℤ := vlinList x.sB x.B1 x.B2

/-- The product of the phase, M = S · T. -/
abbrev prod : List ℤ := phaseM x.p j x.sA x.A1 x.A2 x.sB x.B1 x.B2

/-- The arguments of the recursive call: S stands at scr, T at scr + q, the product goes to
scr + 2 q, and the scratch space begins at scr + 3 q. -/
@[simp] def inner : StrArgs :=
  { dst := x.scr + x.q + x.q, a := x.scr, b := x.scr + x.q, szt := x.szt, p := x.p
    scr := x.scr + x.q + x.q + x.q, len := x.q, J := x.J, A := x.S, B := x.T
    α := 2 * x.α, β := 2 * x.β }

end PhaseArgs

/-- What a phase assumes at level j + 1.  The six lists have q = 4^j p numbers each.  All of them
and the table of sizes lie below the scratch space, and the two results do not meet. -/
structure PhasePre (lim : Limits) (μ : ℕ → ℤ) (j : ℕ) (x : PhaseArgs) : Prop where
  size : x.q = 4 ^ j * x.p
  prime : 1 ≤ x.p
  opA1 : ArrayAt μ x.a1 x.A1 x.q x.α x.scr
  opA2 : ArrayAt μ x.a2 x.A2 x.q x.α x.scr
  opB1 : ArrayAt μ x.b1 x.B1 x.q x.β x.scr
  opB2 : ArrayAt μ x.b2 x.B2 x.q x.β x.scr
  out1 : ArrayAt μ x.c1 x.C1 x.q (2 * strassenBound x.p (j + 1) x.α x.β) x.scr
  out2 : ArrayAt μ x.c2 x.C2 x.q (2 * strassenBound x.p (j + 1) x.α x.β) x.scr
  table : ListAt μ x.szt (szList x.p x.J) (x.J + 1) x.scr
  signA : |x.sA| ≤ 1
  signB : |x.sB| ≤ 1
  sign1 : |x.s1| ≤ 1
  sign2 : |x.s2| ≤ 1
  oneA : 1 ≤ x.α
  oneB : 1 ≤ x.β
  word : 4 * strassenBound x.p (j + 1) x.α x.β ≤ lim.word
  space : x.scr + strScr x.p (j + 1) ≤ lim.space
  apart : Apart x.c1 x.q x.c2 x.q := by light_arith
  level : j ≤ x.J := by light_arith
  room : 8 * x.q < lim.space := by light_arith

/-- What a phase promises: s1 M has been added to the list at c1 and s2 M to the list at c2, and
nothing else has changed but the scratch space. -/
structure PhasePost (μ : ℕ → ℤ) (j : ℕ) (x : PhaseArgs) (μ' : ℕ → ℤ) : Prop where
  out1 : Seg μ' x.c1 (vlinList x.s1 x.C1 (x.prod j))
  out2 : Seg μ' x.c2 (vlinList x.s2 x.C2 (x.prod j))
  same : SameOutside3 μ μ' x.c1 x.q x.c2 x.q x.scr (strScr x.p (j + 1))

section phase

variable {ν : StrNums} {μ μ' : ℕ → ℤ} {j : ℕ} {x : PhaseArgs}

namespace PhasePre

/-- The product of a phase has q numbers. -/
theorem length_prod (pre : PhasePre lim μ j x) : (x.prod j).length = x.q := by
  have hq := pre.size
  rw [hq]
  exact length_strassenList x.p j _ _ (hq ▸ length_vlinList _ pre.opA1.len pre.opA2.len)
    (hq ▸ length_vlinList _ pre.opB1.len pre.opB2.len)

/-- The bound of level j for operands that are sums of two is not negative. -/
theorem bound_nonneg (pre : PhasePre lim μ j x) :
    0 ≤ strassenBound x.p j (2 * x.α) (2 * x.β) :=
  strassenBound_nonneg (by have := pre.oneA; omega) (by have := pre.oneB; omega)

/-- The product of a phase is bounded by strassenBound p j (2 α) (2 β). -/
theorem absLe_prod (pre : PhasePre lim μ j x) :
    AbsLe (x.prod j) (strassenBound x.p j (2 * x.α) (2 * x.β)) := by
  have hα := pre.oneA
  have hβ := pre.oneB
  exact absLe_strassenList x.p j _ _ (2 * x.α) (2 * x.β)
    ((pre.opA1.bound.vlinList pre.opA2.bound pre.signA).trans_le (by omega))
    ((pre.opB1.bound.vlinList pre.opB2.bound pre.signB).trans_le (by omega)) (by omega) (by omega)

/-- The scratch space of level j + 1: three lists of q numbers, and the scratch space of level j. -/
theorem space_inner (pre : PhasePre lim μ j x) : x.scr + (3 * x.q + strScr x.p j) ≤ lim.space := by
  have := pre.space
  rwa [strScr, ← pre.size] at this

/-- What a phase assumes still holds when no cell below scr has changed. -/
theorem keep (pre : PhasePre lim μ j x) (hs : Kept μ μ' x.scr := by light_keep) :
    PhasePre lim μ' j x :=
  { pre with
    opA1 := pre.opA1.keep, opA2 := pre.opA2.keep, opB1 := pre.opB1.keep, opB2 := pre.opB2.keep
    out1 := pre.out1.keep, out2 := pre.out2.keep, table := pre.table.keep }

/-- What the recursive call of a phase assumes, once the two operands stand in the scratch space. -/
theorem inner (pre : PhasePre lim μ j x) (segS : Seg μ x.scr x.S)
    (segT : Seg μ (x.scr + x.q) x.T) : StrPre lim μ j x.inner := by
  have := strassenBound_succ x.p j x.α x.β
  have := pre.bound_nonneg
  have := pre.space_inner
  light_facts pre
  exact
    { size := pre.size, prime := pre.prime, table := pre.table.mono
      opA := pre.opA1.vlinList pre.opA2.len pre.opA2.bound pre.signA segS
      opB := pre.opB1.vlinList pre.opB2.len pre.opB2.bound pre.signB segT }

end PhasePre

variable (prog : StrProg P ν) (hw : (lim.space : ℤ) ≤ lim.word)
include prog hw

/-- **The operands of a phase.** -/
theorem phaseOpnds_spec (pre : PhasePre lim μ j x) (hd : d < lim.depth) :
    Ends lim P d (phaseOpnds ν) ⟨frame (x.vals j), μ⟩ (46 * x.q + 28) fun σ' =>
      ∃ (r : ℤ) (μ' : ℕ → ℤ), σ' = ⟨frame (x.vals j ++ [r]), μ'⟩ ∧
        Seg μ' x.scr x.S ∧ Seg μ' (x.scr + x.q) x.T ∧ SameOutside μ μ' x.scr (2 * x.q) := by
  have := pre.space_inner
  have word := pre.word
  have hleα := le_strassenBound_left (j := j + 1) pre.prime pre.oneA pre.oneB
  have hleβ := le_strassenBound_right (j := j + 1) pre.prime pre.oneA pre.oneB
  have := length_vlinList x.sA pre.opA1.len pre.opA2.len
  light_facts pre.opA1 pre.opA2 pre.opB1 pre.opB2
  -- S := a1 + sA a2
  light_call (vlin_meets prog.vlin hw (dst := x.scr) (V := x.α)
    { opA := pre.opA1.mono, opB := pre.opA2.mono, sign := pre.signA }) with _ μ₁ ⟨segS, rest₁⟩
  -- T := b1 + sB b2
  light_call (vlin_meets prog.vlin hw (dst := x.scr + x.q) (V := x.β)
    { opA := pre.opB1.keep.mono, opB := pre.opB2.keep.mono, sign := pre.signB })
    with r μ₂ ⟨segT, rest₂⟩
  exact ⟨r, μ₂, rfl, segS.keep, segT, by light_keep⟩

/-- **The end of a phase.** -/
theorem phaseAccum_spec (pre : PhasePre lim μ j x) (segM : Seg μ (x.scr + x.q + x.q) (x.prod j))
    (hd : d < lim.depth) (r : ℤ) :
    Ends lim P d (phaseAccum ν) ⟨frame (x.vals j ++ [r]), μ⟩ (46 * x.q + 34) fun σ' =>
      Seg σ'.mem x.c1 (vlinList x.s1 x.C1 (x.prod j)) ∧
        Seg σ'.mem x.c2 (vlinList x.s2 x.C2 (x.prod j)) ∧
        SameOutside2 μ σ'.mem x.c1 x.q x.c2 x.q := by
  have space := pre.space_inner
  have word := pre.word
  have apart := pre.apart
  have := strassenBound_succ x.p j x.α x.β
  have := pre.bound_nonneg
  have := length_vlinList x.s1 pre.out1.len pre.length_prod
  light_facts pre.out1 pre.out2
  have opM : ArrayAt μ (x.scr + x.q + x.q) (x.prod j) x.q (2 * strassenBound x.p (j + 1) x.α x.β)
      lim.space :=
    { len := pre.length_prod, seg := segM, bound := pre.absLe_prod.trans_le (by omega) }
  -- c1 := c1 + s1 M
  light_call (vlin_meets prog.vlin hw (dst := x.c1)
    { opA := pre.out1.mono, opB := opM, sign := pre.sign1 }) with _ μ₁ ⟨seg1, rest₁⟩
  -- c2 := c2 + s2 M
  light_call (vlin_meets prog.vlin hw (dst := x.c2)
    { opA := pre.out2.keep.mono, opB := opM.keep, sign := pre.sign2 }) with _ μ₂ ⟨seg2, rest₂⟩
  exact ⟨seg1.keep, seg2, by light_keep⟩

/-- **A phase** adds s1 M to c1 and s2 M to c2, where M = (a1 + sA a2) · (b1 + sB b2), and changes
nothing else but the scratch space. -/
theorem phase_meets (H : StrSpec lim P ν j) (pre : PhasePre lim μ j x)
    (hd : d + 2 * j + 2 ≤ lim.depth) :
    Meets lim P ν.pPhase d (x.vals j) μ (92 * x.q + 83 + strSteps x.p j) fun _ =>
      PhasePost μ j x := by
  have := pre.space_inner
  have : strScr x.p (j + 1) = 3 * x.q + strScr x.p j := by rw [strScr, pre.size]
  refine Meets.of_body prog.phase ?_
  -- S := a1 + sA a2; T := b1 + sB b2
  light_piece (phaseOpnds_spec prog hw pre (by omega)) with _ ⟨r, μ₁, rfl, segS, segT, rest₁⟩
  -- M := S · T
  light_call (H x.inner μ₁ (pre.keep.inner segS segT) _ (by omega)) with r' μ₂ ⟨segM, rest₂⟩
  dsimp only [PhaseArgs.inner] at segM rest₂
  -- c1 := c1 + s1 M; c2 := c2 + s2 M
  light_piece (phaseAccum_spec prog hw pre.keep segM (by omega) r') with σ' ⟨seg1, seg2, rest₃⟩
  exact ⟨seg1, seg2, by light_keep⟩

end phase

/-! ## Between two phases -/

/-- A row of the table of Strassen's seven products.  With a[t], b[t] and c[t] for the quarters
number t of the operands and of the result, the product is
M = (a[a1] + sA a[a2]) · (b[b1] + sB b[b2]), and s1 M is added to c[c1] and s2 M to c[c2]. -/
structure PhaseRow : Type where
  (a1 a2 : ℕ) (sA : ℤ) (b1 b2 : ℕ) (sB : ℤ) (c1 : ℕ) (s1 : ℤ) (c2 : ℕ) (s2 : ℤ)

/-- The entries of a row are numbers of quarters and signs, and the two results are different
quarters. -/
structure PhaseRow.Ok (row : PhaseRow) : Prop where
  a1 : row.a1 < 4
  a2 : row.a2 < 4
  b1 : row.b1 < 4
  b2 : row.b2 < 4
  c1 : row.c1 < 4
  c2 : row.c2 < 4
  ne : row.c1 ≠ row.c2
  sA : |row.sA| ≤ 1
  sB : |row.sB| ≤ 1
  s1 : |row.s1| ≤ 1
  s2 : |row.s2| ≤ 1

/-- The arguments of the phase of a row, called from strassen with the arguments x, when a
quarter has q numbers and the four quarters of dst hold the lists L 0, …, L 3. -/
@[simp] def StrArgs.phase (x : StrArgs) (q : ℕ) (L : ℕ → List ℤ) (row : PhaseRow) : PhaseArgs :=
  { a1 := x.a + row.a1 * q, a2 := x.a + row.a2 * q, sA := row.sA
    b1 := x.b + row.b1 * q, b2 := x.b + row.b2 * q, sB := row.sB
    c1 := x.dst + row.c1 * q, s1 := row.s1, c2 := x.dst + row.c2 * q, s2 := row.s2
    szt := x.szt, p := x.p, scr := x.scr, q := q, J := x.J
    A1 := quarter q row.a1 x.A, A2 := quarter q row.a2 x.A
    B1 := quarter q row.b1 x.B, B2 := quarter q row.b2 x.B
    C1 := L row.c1, C2 := L row.c2, α := x.α, β := x.β }

/-- The four lists after the phase of a row. -/
def StrArgs.after (x : StrArgs) (j q : ℕ) (L : ℕ → List ℤ) (row : PhaseRow) : ℕ → List ℤ :=
  Function.update (Function.update L row.c1 (vlinList row.s1 (L row.c1) ((x.phase q L row).prod j)))
    row.c2 (vlinList row.s2 (L row.c2) ((x.phase q L row).prod j))

/-- The state of strassen at level j + 1 after κ phases: what strassen assumes still holds, and the
four quarters of dst hold the lists L 0, …, L 3, of q = 4^j p numbers each, bounded by κ times the
bound on a product. -/
structure StrInv (lim : Limits) (μ : ℕ → ℤ) (j q : ℕ) (x : StrArgs) (L : ℕ → List ℤ) (κ : ℕ) : Prop
    extends StrPre lim μ (j + 1) x where
  quarterLen : q = 4 ^ j * x.p
  out : ∀ t < 4, ArrayAt μ (x.dst + t * q) (L t) q (κ * strassenBound x.p j (2 * x.α) (2 * x.β))
    x.scr

/-- Two different quarters do not meet. -/
theorem quarter_apart {t t' : ℕ} (q : ℕ) (h : t ≠ t') :
    t * q + q ≤ t' * q ∨ t' * q + q ≤ t * q :=
  (Nat.lt_or_gt_of_ne h).imp (fun h' => Nat.mul_add_le_mul h' le_rfl)
    fun h' => Nat.mul_add_le_mul h' le_rfl

/-- A property of the four lists after two of them have been replaced. -/
theorem forall_update_update {Φ : ℕ → List ℤ → Prop} {L : ℕ → List ℤ} {t₁ t₂ : ℕ}
    {X₁ X₂ : List ℤ} (h : ∀ t < 4, t ≠ t₁ → t ≠ t₂ → Φ t (L t)) (h₁ : Φ t₁ X₁) (h₂ : Φ t₂ X₂) :
    ∀ t < 4, Φ t (Function.update (Function.update L t₁ X₁) t₂ X₂ t) := by
  intro t ht
  by_cases e₂ : t = t₂
  · rw [e₂, Function.update_self]
    exact h₂
  by_cases e₁ : t = t₁
  · rw [Function.update_of_ne e₂, e₁, Function.update_self]
    exact h₁
  · rw [Function.update_of_ne e₂, Function.update_of_ne e₁]
    exact h t ht e₁ e₂

section step

variable {ν : StrNums} {μ μ' : ℕ → ℤ} {j q κ : ℕ} {x : StrArgs} {L : ℕ → List ℤ} {row : PhaseRow}

namespace StrInv

/-- An operand has four quarters. -/
theorem size_eq (inv : StrInv lim μ j q x L κ) : x.len = 4 * q := by
  rw [inv.size, inv.quarterLen]
  ring

/-- What the phase of a row assumes holds between two phases. -/
theorem phasePre (inv : StrInv lim μ j q x L κ) (hκ : κ ≤ 7) (hr : row.Ok) :
    PhasePre lim μ j (x.phase q L row) := by
  have hB0 : 0 ≤ strassenBound x.p j (2 * x.α) (2 * x.β) :=
    strassenBound_nonneg (by have := inv.oneA; omega) (by have := inv.oneB; omega)
  have hbound : (κ : ℤ) * strassenBound x.p j (2 * x.α) (2 * x.β) ≤
      2 * strassenBound x.p (j + 1) x.α x.β := by
    rw [strassenBound_succ]
    calc (κ : ℤ) * strassenBound x.p j (2 * x.α) (2 * x.β)
        ≤ 8 * strassenBound x.p j (2 * x.α) (2 * x.β) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hκ.trans (by norm_num)) hB0
      _ = 2 * (4 * strassenBound x.p j (2 * x.α) (2 * x.β)) := by ring
  have hq := inv.size_eq
  have opA := (hq ▸ inv.opA).mono le_rfl (Nat.le_of_add_right_le inv.dstBelow)
  have opB := (hq ▸ inv.opB).mono le_rfl (Nat.le_of_add_right_le inv.dstBelow)
  have := quarter_apart q hr.ne
  light_facts inv.toStrPre
  exact
    { size := inv.quarterLen, prime := inv.prime, table := inv.table.mono
      opA1 := opA.quarter hr.a1, opA2 := opA.quarter hr.a2
      opB1 := opB.quarter hr.b1, opB2 := opB.quarter hr.b2
      out1 := (inv.out _ hr.c1).mono hbound le_rfl, out2 := (inv.out _ hr.c2).mono hbound le_rfl
      signA := hr.sA, signB := hr.sB, sign1 := hr.s1, sign2 := hr.s2
      oneA := inv.oneA, oneB := inv.oneB, word := inv.word, space := inv.space }

/-- The state after a phase: two of the four lists are replaced, the rest is as before. -/
theorem step (inv : StrInv lim μ j q x L κ) (hκ : κ ≤ 7) (hr : row.Ok)
    (post : PhasePost μ j (x.phase q L row) μ') :
    StrInv lim μ' j q x (x.after j q L row) (κ + 1) := by
  have pre := inv.phasePre hκ hr
  have : 0 ≤ strassenBound x.p j (2 * x.α) (2 * x.β) := pre.bound_nonneg
  have hsucc : ((κ + 1 : ℕ) : ℤ) * strassenBound x.p j (2 * x.α) (2 * x.β) =
      κ * strassenBound x.p j (2 * x.α) (2 * x.β) + strassenBound x.p j (2 * x.α) (2 * x.β) := by
    push_cast
    ring
  have := inv.size_eq
  have dstBelow := inv.dstBelow
  have same : SameOutside3 μ μ' (x.dst + row.c1 * q) q (x.dst + row.c2 * q) q x.scr
      (strScr x.p (j + 1)) := post.same
  have pre' : StrPre lim μ' (j + 1) x := inv.toStrPre.keep
  refine
    { toStrPre := pre'
      quarterLen := inv.quarterLen
      out := forall_update_update
        (Φ := fun t X => ArrayAt μ' (x.dst + t * q) X q _ x.scr) (fun t ht e₁ e₂ => ?_)
        ((inv.out _ hr.c1).vlinList pre.length_prod pre.absLe_prod hr.s1 post.out1 hsucc.ge
          pre.out1.below)
        ((inv.out _ hr.c2).vlinList pre.length_prod pre.absLe_prod hr.s2 post.out2 hsucc.ge
          pre.out2.below) }
  · have hapart₁ := quarter_apart q e₁
    have := quarter_apart q e₂
    have : t * q + q ≤ 4 * q := Nat.mul_add_le_mul ht le_rfl
    exact (inv.out t ht).keep.mono

end StrInv

/-- **A phase, called from the body of strassen**: with M the product of the row, s1 M is added to
the list number c1 and s2 M to the list number c2. -/
theorem phase_step (prog : StrProg P ν) (hw : (lim.space : ℤ) ≤ lim.word)
    (H : StrSpec lim P ν j) (inv : StrInv lim μ j q x L κ) (hd : d + 2 * j + 2 ≤ lim.depth)
    (row : PhaseRow) (hκ : κ ≤ 7 := by omega)
    (hr : row.Ok := by constructor <;> simp) :
    Meets lim P ν.pPhase d ((x.phase q L row).vals j) μ (92 * q + 83 + strSteps x.p j) fun _ μ' =>
      StrInv lim μ' j q x (x.after j q L row) (κ + 1) ∧
        SameOutside2 μ μ' x.dst (4 * q) x.scr (strScr x.p (j + 1)) := by
  refine (phase_meets prog hw H (inv.phasePre hκ hr) hd).mono le_rfl fun _ μ' post => ?_
  have : row.c1 * q + q ≤ 4 * q := Nat.mul_add_le_mul hr.c1 le_rfl
  have : row.c2 * q + q ≤ 4 * q := Nat.mul_add_le_mul hr.c2 le_rfl
  have same : SameOutside3 μ μ' (x.dst + row.c1 * q) q (x.dst + row.c2 * q) q x.scr
      (strScr x.p (j + 1)) := post.same
  exact ⟨inv.step hκ hr post, by light_keep⟩

end step

/-- Four lists of q numbers in the four quarters of a segment are one list. -/
theorem seg_of_quarters {μ : ℕ → ℤ} {dst q : ℕ} {L : ℕ → List ℤ}
    (seg : ∀ t < 4, Seg μ (dst + t * q) (L t)) (len : ∀ t < 4, (L t).length = q) :
    Seg μ dst (L 0 ++ L 1 ++ L 2 ++ L 3) := by
  rw [seg_append, seg_append, seg_append]
  simp only [List.length_append, len 0 (by omega), len 1 (by omega), len 2 (by omega)]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simpa using seg 0 (by omega)
  · simpa using seg 1 (by omega)
  · rw [show dst + (q + q) = dst + 2 * q by ring]
    exact seg 2 (by omega)
  · rw [show dst + (q + q + q) = dst + 3 * q by ring]
    exact seg 3 (by omega)

/-- A quarter of a cleared segment is cleared. -/
theorem seg_zeros_quarter {μ : ℕ → ℤ} {dst q t : ℕ} (h : Seg μ dst (List.replicate (4 * q) 0))
    (ht : t < 4) : Seg μ (dst + t * q) (zeros q) := by
  intro i hi
  have : i < q := by simpa [zeros] using hi
  have : t * q + q ≤ 4 * q := Nat.mul_add_le_mul ht le_rfl
  have hcell := h (t * q + i) (by simp; omega)
  rw [List.getElem_replicate, ← Nat.add_assoc] at hcell
  simpa [zeros] using hcell

/-! ## The seven phases -/

section levels

variable {ν : StrNums} {μ : ℕ → ℤ} {j q : ℕ} {x : StrArgs} (prog : StrProg P ν)
  (hw : (lim.space : ℤ) ≤ lim.word)
include prog hw

/-- **The seven phases** turn four cleared quarters into the product. -/
theorem sevenPhases_spec (H : StrSpec lim P ν j)
    (inv : StrInv lim μ j q x (fun _ => zeros q) 0) (hd : d + 2 * j + 3 ≤ lim.depth)
    (lvl z r : ℤ) :
    Ends lim P d (sevenPhases ν)
      ⟨frame [x.dst, x.a, x.b, lvl, x.szt, x.p, x.scr, q, (2 * q : ℕ), (3 * q : ℕ), j, z, r], μ⟩
      (7 * (92 * q + 123 + strSteps x.p j)) fun σ' =>
        Seg σ'.mem x.dst (strassenList x.p (j + 1) x.A x.B) ∧
        SameOutside2 μ σ'.mem x.dst x.len x.scr (strScr x.p (j + 1)) := by
  have := inv.size_eq
  have hd' : d + 1 + 2 * j + 2 ≤ lim.depth := by omega
  light_facts inv.toStrPre inv.opA inv.opB
  -- M₁ = (a₀ + a₃) (b₀ + b₃) goes to the quarters 0 and 3
  refine Ends.callToThen (phase_step prog hw H inv hd' ⟨0, 3, 1, 0, 3, 1, 0, 1, 3, 1⟩) ?_
    (hT := by simp; omega)
  rintro _ μ₁ ⟨inv₁, rest₁⟩
  -- M₂ = (a₂ + a₃) b₀ goes to 2 and, with the sign -1, to 3
  refine Ends.callToThen (phase_step prog hw H inv₁ hd' ⟨2, 3, 1, 0, 0, 0, 2, 1, 3, -1⟩) ?_
    (hT := by simp; omega)
  rintro _ μ₂ ⟨inv₂, rest₂⟩
  -- M₃ = a₀ (b₁ - b₃) goes to 1 and 3
  refine Ends.callToThen (phase_step prog hw H inv₂ hd' ⟨0, 0, 0, 1, 3, -1, 1, 1, 3, 1⟩) ?_
    (hT := by simp; omega)
  rintro _ μ₃ ⟨inv₃, rest₃⟩
  -- M₄ = a₃ (b₂ - b₀) goes to 0 and 2
  refine Ends.callToThen (phase_step prog hw H inv₃ hd' ⟨3, 3, 0, 2, 0, -1, 0, 1, 2, 1⟩) ?_
    (hT := by simp; omega)
  rintro _ μ₄ ⟨inv₄, rest₄⟩
  -- M₅ = (a₀ + a₁) b₃ goes, with the sign -1, to 0, and to 1
  refine Ends.callToThen (phase_step prog hw H inv₄ hd' ⟨0, 1, 1, 3, 3, 0, 0, -1, 1, 1⟩) ?_
    (hT := by simp; omega)
  rintro _ μ₅ ⟨inv₅, rest₅⟩
  -- M₆ = (a₂ - a₀) (b₀ + b₁) goes to 3
  refine Ends.callToThen (phase_step prog hw H inv₅ hd' ⟨2, 0, -1, 0, 1, 1, 3, 1, 0, 0⟩) ?_
    (hT := by simp; omega)
  rintro _ μ₆ ⟨inv₆, rest₆⟩
  -- M₇ = (a₁ - a₃) (b₂ + b₃) goes to 0
  refine Ends.callTo (phase_step prog hw H inv₆ hd' ⟨1, 3, -1, 2, 3, 1, 0, 1, 3, 0⟩) ?_
    (hT := by simp; omega)
  rintro _ μ₇ ⟨inv₇, rest₇⟩
  -- The four lists are the four quadrants of the product.
  have hseg := seg_of_quarters (fun t ht => (inv₇.out t ht).seg) fun t ht => (inv₇.out t ht).len
  simp only [StrArgs.after, StrArgs.phase, Function.update_apply, Nat.reduceEqDiff, reduceIte,
    OfNat.zero_ne_ofNat, OfNat.ofNat_ne_zero, OfNat.one_ne_ofNat, OfNat.ofNat_ne_one, zero_ne_one,
    one_ne_zero] at hseg
  have key := strassenList_succ_eq_phases x.p j x.A x.B (inv.opA.len.trans inv.size)
    (inv.opB.len.trans inv.size)
  simp only [← inv.quarterLen] at key
  exact ⟨key ▸ hseg, by light_keep⟩

/-! ## The two cases and the induction -/

/-- **Level 0**: one product in the ring. -/
theorem strassen_zero : StrSpec lim P ν 0 := by
  intro x μ pre d hd
  have hq : x.len = x.p := by simpa using pre.size
  have hword : (x.p : ℤ) * (x.α * x.β) ≤ lim.word := by
    have h := pre.word
    have : (0 : ℤ) ≤ x.p * (x.α * x.β) := by have := pre.oneA; have := pre.oneB; positivity
    rw [strassenBound, pow_zero, one_mul, mul_assoc] at h
    omega
  light_facts pre pre.opA pre.opB
  refine Meets.of_body prog.str ?_
  -- if j = 0 then cconv(dst, a, b, p)
  refine Ends.iteLast (fun _ => ?_) (fun hc => absurd (by simp) hc) (hT := by simp [strSteps])
  refine Ends.callTo (cconv_meets prog.cconv hw (dst := x.dst)
    { opA := (hq ▸ pre.opA).mono, opB := (hq ▸ pre.opB).mono, word := hword }) ?_
    (hT := by simp [strSteps]; omega)
  rintro _ μ' ⟨seg, rest⟩
  exact ⟨seg, by light_keep⟩

/-- **Level j + 1**: clear the result, then the seven phases. -/
theorem strassen_succ (H : StrSpec lim P ν j) : StrSpec lim P ν (j + 1) := by
  intro x μ pre d hd
  obtain ⟨q, hq⟩ : ∃ q, q = 4 ^ j * x.p := ⟨_, rfl⟩
  have hsize : x.len = 4 * q := by rw [pre.size, hq]; ring
  light_facts pre pre.opA pre.opB pre.table
  have hread : μ (x.szt + j) = q := by
    rw [pre.table.read (by omega), hq]
    simp [szList, show j < x.J + 1 by omega]
  refine Meets.of_body prog.str ?_
  rw [show strSteps x.p (j + 1) = 7 * strSteps x.p j + 696 * q + 900 by rw [strSteps, hq]]
  -- if level = 0 … else; the level is j + 1
  refine Ends.iteLast (fun hc => absurd hc (by simp; omega)) fun _ => ?_
  -- below := level - 1, which is j; q := szt[below]; q2 := q + q; q3 := q2 + q
  light_set j
  light_set q using hread
  light_set (2 * q : ℕ)
  light_set (3 * q : ℕ)
  -- fill(dst, 4 q, 0)
  light_call (fill_meets prog.fill (dst := x.dst) (n := 4 * q) (x := 0) hw (by omega))
    with r μ₁ ⟨segF, rest⟩
  have inv : StrInv lim μ₁ j q x (fun _ => zeros q) 0 :=
    { toStrPre := pre.keep
      quarterLen := hq
      out := fun t ht =>
        { len := by simp [zeros], seg := seg_zeros_quarter segF ht
          bound := by simpa using absLe_zeros q
          below := by have := Nat.mul_add_le_mul ht (le_refl q); omega } }
  -- the seven phases
  light_piece (sevenPhases_spec prog hw H inv (by omega) _ _ _) with σ' ⟨seg, rest'⟩
  exact ⟨seg, by light_keep⟩

/-- **Strassen's algorithm**, at every level. -/
theorem strassen_spec : ∀ j, StrSpec lim P ν j
  | 0 => strassen_zero prog hw
  | j + 1 => strassen_succ prog hw (strassen_spec j)

end levels

end Light.Sec3
end
