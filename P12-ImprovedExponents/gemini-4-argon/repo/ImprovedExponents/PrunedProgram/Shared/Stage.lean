module

public import ThreeSumApsp.Lang.Lib.Pass
public import ThreeSumApsp.Lang.Tactics
public import ImprovedExponents.PrunedProgram.SegOn
public import ImprovedExponents.PrunedProgram.Work
public import ThreeSumApsp.Sec2.Lemma10
public import ThreeSumApsp.Spec.Sec2.Theorem5.Arrays
public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts
public import ThreeSumApsp.Sec2.Theorem5.WordSize
public import ImprovedExponents.PrunedProgram.Procs
public import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.BandArray
public import ImprovedExponents.PrunedProgram.Shared.Contracts

@[expose] public section

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# One encoding step (step (2) of Full, Section 2.3.1)

"For each term λ of Schönhage's identity, form A_λ := ∑_s φ_λ(s) a_s and B_λ := ∑_t ψ_λ(t) b_t."
The array a is in 7 n consecutive cells at src, slice after slice; the coefficients of all the forms
are in a table at tab, seven for each term; the array A_λ is written to n cells at dst.  B_λ is
formed by the same procedure, from the array b and the table of the coefficients of the ψ_λ.

`encStepVal` is the sum that belongs in a cell, summand by summand.  Its partial sums are small
(`EncStepPre.val_bounds`), and it does not change while the cells of `dst` are written
(`EncStepPre.val_congr`).  `encStepSum_spec` forms one sum, and `encStep_meets` runs through the
cells.
-/


namespace Light.Sec2

open Finset ThreeSumApsp

namespace EncStep

/-- The local variables of encStep: the arguments src, dst, n, lam, tab; the cell j of dst; the sum;
the number s of the summand. -/
abbrev Src : ℕ := 0
@[inherit_doc Src] abbrev Dest : ℕ := 1
@[inherit_doc Src] abbrev Len : ℕ := 2
@[inherit_doc Src] abbrev TermNo : ℕ := 3
@[inherit_doc Src] abbrev Table : ℕ := 4
@[inherit_doc Src] abbrev Cell : ℕ := 5
@[inherit_doc Src] abbrev Acc : ℕ := 6
@[inherit_doc Src] abbrev Var : ℕ := 7

end EncStep

section
open EncStep

/-- One summand: Acc := Acc + tab[7 lam + s] · src[s n + j]. -/
def encStepAdd : Stmt :=
  .set Acc
    (v Acc +' M (v Table +' k 7 *' v TermNo +' v Var) *' M (v Src +' v Var *' v Len +' v Cell))

/-- The sum over s < 7 of tab[7 lam + s] · src[s n + j]. -/
def encStepSum : Stmt := .for Var (k 7) encStepAdd

/-- One cell of dst. -/
def encStepCell : Stmt := .set Acc (k 0) ;; encStepSum ;; .store (v Dest +' v Cell) (v Acc)

/-- encStep(src, dst, n, lam, tab): for j < n, dst[j] := ∑_{s < 7} tab[7 lam + s] · src[s n + j]. -/
def encStepBody : Stmt := .for Cell (v Len) encStepCell

end

/-! ## The sums -/

/-- The first s summands of what encStep writes at dst + j. -/
def encStepVal (μ : ℕ → ℤ) (src lam tab n j s : ℕ) : ℤ :=
  ∑ i ∈ range s, μ (tab + 7 * lam + i) * μ (src + i * n + j)

/-- What encStep writes at dst + c. -/
abbrev encStepOut (μ : ℕ → ℤ) (src lam tab n : ℕ) : ℕ → ℤ := fun c => encStepVal μ src lam tab n c 7

/-- One more summand. -/
theorem encStepVal_succ (μ : ℕ → ℤ) (src lam tab n j s : ℕ) :
    encStepVal μ src lam tab n j (s + 1)
      = encStepVal μ src lam tab n j s + μ (tab + 7 * lam + s) * μ (src + s * n + j) :=
  Finset.sum_range_succ ..

/-- The hypotheses of `encStep`: the seven coefficients and the array at `src` lie below the `n`
cells at `dst`, which lie in the memory; the coefficients are -1, 0 or 1, the numbers are at most
`V` in absolute value, and `7 V` fits in a word. -/
structure EncStepPre (lim : Limits) (μ : ℕ → ℤ) (src dst n lam tab : ℕ) (V : ℤ) : Prop where
  std : Std lim
  tab_le : tab + 7 * lam + 7 ≤ dst
  src_le : src + 7 * n ≤ dst
  dst_le : dst + n ≤ lim.space
  coef : ∀ i < 7, -1 ≤ μ (tab + 7 * lam + i) ∧ μ (tab + 7 * lam + i) ≤ 1
  vals : ∀ i < 7 * n, -V ≤ μ (src + i) ∧ μ (src + i) ≤ V
  word_bound : 7 * V ≤ lim.word

variable {lim : Limits} {P : Program} {d : ℕ} {μ μ' : ℕ → ℤ} {src dst n lam tab j : ℕ} {V : ℤ}

/-- The product of a coefficient in {-1, 0, 1} and a number of absolute value at most `V`. -/
theorem enc_coef_mul_bound {x y V : ℤ} (hx : -1 ≤ x ∧ x ≤ 1) (hy : -V ≤ y ∧ y ≤ V) :
    -V ≤ x * y ∧ x * y ≤ V := by
  have h : x = -1 ∨ x = 0 ∨ x = 1 := by omega
  rcases h with rfl | rfl | rfl <;> constructor <;> omega

/-- A sum of `s` numbers of absolute value at most `V` is at most `s V` in absolute value. -/
theorem enc_sum_bound {f : ℕ → ℤ} {V : ℤ} (s : ℕ) (h : ∀ i < s, -V ≤ f i ∧ f i ≤ V) :
    -(s * V) ≤ ∑ i ∈ range s, f i ∧ ∑ i ∈ range s, f i ≤ s * V := by
  induction s with
  | zero => simp
  | succ s ih =>
    have := ih fun i hi => h i (by omega)
    have := h s (by omega)
    rw [Finset.sum_range_succ, Nat.cast_succ, add_mul, one_mul]
    omega

namespace EncStepPre

/-- One summand is at most `V` in absolute value. -/
theorem summand_bounds (pre : EncStepPre lim μ src dst n lam tab V) (hj : j < n) {s : ℕ}
    (hs : s < 7) : -V ≤ μ (tab + 7 * lam + s) * μ (src + s * n + j) ∧
      μ (tab + 7 * lam + s) * μ (src + s * n + j) ≤ V := by
  have hval := pre.vals (s * n + j) (Nat.mul_add_lt_mul hs hj)
  rw [← Nat.add_assoc] at hval
  exact enc_coef_mul_bound (pre.coef s hs) hval

/-- The sum of `s` summands is at most `s V` in absolute value. -/
theorem val_bounds (pre : EncStepPre lim μ src dst n lam tab V) (hj : j < n) {s : ℕ}
    (hs : s ≤ 7) :
    -(s * V) ≤ encStepVal μ src lam tab n j s ∧ encStepVal μ src lam tab n j s ≤ s * V :=
  enc_sum_bound s fun _ hi => pre.summand_bounds hj (by omega)

/-- The hypotheses still hold when cells of `dst` have been written. -/
theorem keep (pre : EncStepPre lim μ src dst n lam tab V) (same : SameOutside μ μ' dst n) :
    EncStepPre lim μ' src dst n lam tab V := by
  light_facts pre
  exact { pre with
    coef := fun i hi => by rw [same _ (by omega)]; exact pre.coef i hi
    vals := fun i hi => by rw [same _ (by omega)]; exact pre.vals i hi }

/-- The sums do not change when cells of `dst` are written. -/
theorem val_congr (pre : EncStepPre lim μ src dst n lam tab V)
    (same : SameOutside μ μ' dst n) (hj : j < n) :
    encStepVal μ' src lam tab n j 7 = encStepVal μ src lam tab n j 7 := by
  light_facts pre
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi7 : i < 7 := Finset.mem_range.mp hi
  have : i * n + j < 7 * n := Nat.mul_add_lt_mul hi7 hj
  rw [same _ (by omega), same _ (by omega)]

end EncStepPre

/-! ## The program -/

variable {T : ℕ} {Q : State → Prop}

/-- **One sum**: the loop over the seven summands leaves the sum for cell j in the local Acc. -/
theorem encStepSum_spec (pre : EncStepPre lim μ src dst n lam tab V) (hj : j < n) {s₀ : ℤ}
    (done : Q ⟨frame [src, dst, n, lam, tab, j, encStepVal μ src lam tab n j 7, (7 : ℕ)], μ⟩)
    (hT : 202 ≤ T) :
    Ends lim P d encStepSum ⟨frame [src, dst, n, lam, tab, j, 0, s₀], μ⟩ T Q := by
  light_facts pre pre.std
  -- for Var < 7
  refine Ends.for (fun s σ => σ =
      ⟨frame [src, dst, n, lam, tab, j, encStepVal μ src lam tab n j s, s], μ⟩) 7
    encStepAdd.blockCost ?start ?round ?done ?bound (by omega) (by simp [encStepAdd]; omega)
  case start => simp [update_frame_setLocal, encStepVal]
  case done => exact fun _ _ h => h ▸ done
  case bound => exact fun s _ _ _ h => h ▸ by light_side
  case round =>
    rintro s _ hs - rfl
    -- The two cells that are read, and the sizes of the numbers.
    have : s * n + j < 7 * n := Nat.mul_add_lt_mul hs hj
    have := pre.val_bounds hj (show s ≤ 7 by omega)
    have := pre.summand_bounds hj hs
    have hnext := pre.val_bounds hj (show s + 1 ≤ 7 by omega)
    have : ((s + 1 : ℕ) : ℤ) * V ≤ 7 * V := by
      have hV : 0 ≤ V := by have := pre.vals 0 (by omega); omega
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hs) hV
    have hcoef : ((tab : ℤ) + 7 * lam + s).toNat = tab + 7 * lam + s := by omega
    have hcell : ((src : ℤ) + s * n + j).toNat = src + s * n + j := by
      rw [← Nat.cast_mul, ← Nat.cast_add, ← Nat.cast_add, Int.toNat_natCast]
    have : ((s * n : ℕ) : ℤ) = s * n := Nat.cast_mul s n
    -- Acc := Acc + tab[7 lam + Var] * src[Var n + Cell]
    unfold encStepAdd
    refine Ends.setTo (encStepVal μ src lam tab n j (s + 1)) ⟨by simp, ?_⟩ ?_
    · simp [update_frame_setLocal]
    · rw [encStepVal_succ] at hnext ⊢
      simp [Limits.Addr, abs_le, hcoef, hcell, -abs_mul]
      omega

/-- A bound on the number of steps of `encStep` on `n` cells. -/
def tEncStep (n : ℕ) : ℕ := 217 * n + 6

/-- **encStep** writes `∑_{s < 7} tab[7 lam + s] · src[s n + j]` to `dst[j]` for all `j < n` and
changes nothing else. -/
theorem encStep_meets {p : ℕ} (hp : P[p]? = some encStepBody)
    (pre : EncStepPre lim μ src dst n lam tab V) :
    Meets lim P p d [src, dst, n, lam, tab] μ (tEncStep n) fun _ μ' =>
      (∀ j < n, μ' (dst + j) = encStepVal μ src lam tab n j 7) ∧ SameOutside μ μ' dst n := by
  refine .of_body hp ?_
  light_facts pre pre.std
  -- for Cell < n: the first Cell cells of dst have been written
  refine Ends.forShape
    (fun j (s : ℤ × ℤ) μ' => ⟨frame [src, dst, n, lam, tab, j, s.1, s.2], μ'⟩)
    (fun j μ' => μ' = wrote μ dst (encStepOut μ src lam tab n) j) n 209 (0, 0) wrote_zero.symm
    ?round ?done (by rw [update_frame_setLocal, ← frame_append_zeros _ 2]; rfl)
    (hT := by simp [tEncStep]; omega)
  case done =>
    rintro s _ rfl
    exact ⟨fun j hj => wrote_done (f := encStepOut μ src lam tab n) hj,
      sameOutside_wrote (f := encStepOut μ src lam tab n) le_rfl⟩
  case round =>
    rintro j s _ hj rfl
    have same : SameOutside μ (wrote μ dst (encStepOut μ src lam tab n) j) dst n :=
      sameOutside_wrote hj.le
    unfold encStepCell
    -- Acc := 0; the sum; mem[dst + Cell] := Acc
    light_set 0
    refine Ends.next _ (encStepSum_spec (pre.keep same) hj ?_ le_rfl)
    rw [pre.val_congr same hj]
    light_store (dst + j) (encStepVal μ src lam tab n j 7)
    exact ⟨(encStepVal μ src lam tab n j 7, (7 : ℕ)), _, rfl, wrote_succ⟩




namespace Encode

end Encode

/-! ## What encode computes, how much room and how much time it needs -/

/-- The array A_lam of step (2), in terms of positions in arrays: a is the input array (7^{L+1}
numbers, seven slices of 7^L) and c the table of the coefficients (c (7 lam + s) is the coefficient
of slice number s in the term number lam). -/
def encSlice (c a : ℕ → ℤ) (L lam : ℕ) : ℕ → ℤ :=
  fun j => ∑ s ∈ range 7, c (7 * lam + s) * a (s * 7 ^ L + j)

/-- What encode computes, in terms of positions in arrays: a is the input array (7^L numbers), c the
table of the coefficients, and i < 10^L the position of a leaf. -/
def encIdx (c : ℕ → ℤ) : (L : ℕ) → (ℕ → ℤ) → ℕ → ℤ
  | 0, a, _ => a 0
  | L + 1, a, i => encIdx c L (encSlice c a L (i / 10 ^ L)) (i % 10 ^ L)

/-- The number of scratch cells that encode uses: 7^{L-1} + ⋯ + 7 + 1. -/
def scrSize : ℕ → ℕ
  | 0 => 0
  | L + 1 => 7 ^ L + scrSize L

/-! ## The hypotheses -/

/-- Where the arrays of `encode` lie: the three tables, then the output, the input and the scratch
area, one behind the other. -/
structure EncodeLayout (lim : Limits) (src out scr tab p7 p10 L : ℕ) : Prop where
  std : Std lim
  tab_le : tab + 70 ≤ out
  p7_le : p7 + L ≤ out
  p10_le : p10 + L ≤ out
  out_le : out + 10 ^ L ≤ src
  src_le : src + 7 ^ L ≤ scr
  scr_le : scr + scrSize L ≤ lim.space

/-- The hypotheses of `encode`: the layout, what the cells hold, and how large the numbers are. -/
structure EncodePre (lim : Limits) (μ : ℕ → ℤ) (src out scr tab p7 p10 : ℕ) (V : ℤ) (L : ℕ)
    (a c : ℕ → ℤ) : Prop where
  lay : EncodeLayout lim src out scr tab p7 p10 L
  srcV : ∀ j < 7 ^ L, μ (src + j) = a j
  src_bound : ∀ j < 7 ^ L, -V ≤ a j ∧ a j ≤ V
  tabV : ∀ i < 70, μ (tab + i) = c i
  coef_bound : ∀ i < 70, -1 ≤ c i ∧ c i ≤ 1
  p7V : ∀ i < L, μ (p7 + i) = ((7 ^ i : ℕ) : ℤ)
  p10V : ∀ i < L, μ (p10 + i) = ((10 ^ i : ℕ) : ℤ)
  word_bound : ((7 ^ L : ℕ) : ℤ) * V ≤ lim.word

variable {lim : Limits} {P : Program} {d : ℕ} {μ μ' μ₁ μ₂ : ℕ → ℤ}
  {src out scr tab p7 p10 L lam : ℕ} {V : ℤ} {a c : ℕ → ℤ}

/-- The layout at level `L + 1`, with the sizes in terms of `10^L`, `7^L` and `scrSize L`. -/
theorem EncodeLayout.places_succ (lay : EncodeLayout lim src out scr tab p7 p10 (L + 1)) :
    tab + 70 ≤ out ∧ p7 + (L + 1) ≤ out ∧ p10 + (L + 1) ≤ out ∧ out + 10 * 10 ^ L ≤ src ∧
      src + 7 * 7 ^ L ≤ scr ∧ scr + (7 ^ L + scrSize L) ≤ lim.space ∧
      (lim.space : ℤ) ≤ lim.word ∧ (100 : ℤ) ≤ lim.word := by
  simpa only [pow_succ', scrSize] using And.intro lay.tab_le <| And.intro lay.p7_le <|
    And.intro lay.p10_le <| And.intro lay.out_le <| And.intro lay.src_le <|
    And.intro lay.scr_le <| And.intro lay.std.space_le lay.std.const_le

/-- What has not changed at level `L + 1`, with the sizes in terms of `10^L`, `7^L` and
`scrSize L`. -/
theorem sameOutside2_succ (h : SameOutside2 μ μ' out (10 ^ (L + 1)) scr (scrSize (L + 1))) :
    SameOutside2 μ μ' out (10 * 10 ^ L) scr (7 ^ L + scrSize L) := by
  simpa only [pow_succ', scrSize] using h

/-- The layout of the recursive call for the term number `lam`: it reads the first `7^L` cells of
the scratch area, writes the part of the output below the term, and has the rest of the scratch
area. -/
theorem EncodeLayout.toRec (lay : EncodeLayout lim src out scr tab p7 p10 (L + 1))
    (hlam : lam < 10) :
    EncodeLayout lim scr (out + lam * 10 ^ L) (scr + 7 ^ L) tab p7 p10 L := by
  have := lay.places_succ
  have : lam * 10 ^ L + 10 ^ L ≤ 10 * 10 ^ L := Nat.mul_add_le_mul hlam le_rfl
  exact ⟨lay.std, by omega, by omega, by omega, by omega, by omega, by omega⟩

namespace EncodePre

/-- The bound `V` is not negative. -/
theorem V_nonneg (pre : EncodePre lim μ src out scr tab p7 p10 V L a c) : 0 ≤ V := by
  have := pre.src_bound 0 (by positivity)
  omega

/-- In the course of `encode` at level `L + 1`, the hypotheses of `encStep` hold for every term. -/
theorem toStep (pre : EncodePre lim μ src out scr tab p7 p10 V (L + 1) a c)
    (hlam : lam < 10) (same : SameOutside2 μ μ' out (10 ^ (L + 1)) scr (scrSize (L + 1))) :
    EncStepPre lim μ' src scr (7 ^ L) lam tab V := by
  have := pre.lay.places_succ
  have hkept := sameOutside2_succ same
  have hV := pre.V_nonneg
  have hword := pre.word_bound
  have : (1 : ℤ) ≤ 7 ^ L := one_le_pow₀ (by norm_num)
  rw [pow_succ'] at hword
  push_cast at hword
  exact
    { std := pre.lay.std, tab_le := by omega, src_le := by omega, dst_le := by omega
      coef := fun i hi => by
        rw [Nat.add_assoc, hkept _ (by omega), pre.tabV _ (by omega)]
        exact pre.coef_bound _ (by omega)
      vals := fun i hi => by
        rw [hkept _ (by omega), pre.srcV i (by rw [pow_succ']; omega)]
        exact pre.src_bound i (by rw [pow_succ']; omega)
      word_bound := (mul_le_mul_of_nonneg_right (by omega) hV).trans hword }

/-- After `encStep` has written `A_lam` to the scratch area, the hypotheses of `encode` hold at
level `L` for the recursive call. -/
theorem toRec (pre : EncodePre lim μ src out scr tab p7 p10 V (L + 1) a c) (hlam : lam < 10)
    (same : SameOutside2 μ μ' out (10 ^ (L + 1)) scr (scrSize (L + 1)))
    (hstep : ∀ j < 7 ^ L, μ₁ (scr + j) = encStepVal μ' src lam tab (7 ^ L) j 7)
    (same₁ : SameOutside μ' μ₁ scr (7 ^ L)) :
    EncodePre lim μ₁ scr (out + lam * 10 ^ L) (scr + 7 ^ L) tab p7 p10 (7 * V) L
      (encSlice c a L lam) c := by
  have hplaces := pre.lay.places_succ
  have hkept := sameOutside2_succ same
  have hword := pre.word_bound
  have hsrc : ∀ j < 7 * 7 ^ L, μ' (src + j) = a j := fun j hj => by
    rw [hkept _ (by omega)]
    exact pre.srcV j (by rw [pow_succ']; omega)
  have htab : ∀ i < 70, μ' (tab + i) = c i := fun i hi => by
    rw [hkept _ (by omega)]
    exact pre.tabV i hi
  exact
    { lay := pre.lay.toRec hlam
      srcV := fun j hj => by
        rw [hstep j hj]
        refine Finset.sum_congr rfl fun s hs => ?_
        have hs7 : s < 7 := Finset.mem_range.mp hs
        rw [Nat.add_assoc tab, htab (7 * lam + s) (by omega), Nat.add_assoc src,
          hsrc _ (Nat.mul_add_lt_mul hs7 hj)]
      src_bound := fun j hj => by
        simpa [encSlice] using enc_sum_bound 7 fun s hs =>
          enc_coef_mul_bound (pre.coef_bound (7 * lam + s) (by omega))
            (pre.src_bound (s * 7 ^ L + j) (by rw [pow_succ']; exact Nat.mul_add_lt_mul hs hj))
      tabV := fun i hi => by rw [same₁ _ (by omega), htab i hi]
      coef_bound := pre.coef_bound
      p7V := fun i hi => by rw [same₁ _ (by omega), hkept _ (by omega), pre.p7V i (by omega)]
      p10V := fun i hi => by rw [same₁ _ (by omega), hkept _ (by omega), pre.p10V i (by omega)]
      word_bound := by
        rw [pow_succ'] at hword
        push_cast at hword ⊢
        rwa [show (7 : ℤ) ^ L * (7 * V) = 7 * 7 ^ L * V by ring] }

end EncodePre

/-! ## One term -/

variable {pS pE : ℕ}

/-! ## The recursion -/



open ThreeSumApsp.Spec ImprovedExponents

/-! ## The recursions of the counts -/

section Counts

/-- The number of prefixes with no symbol `P₀`: `9^k`. -/
theorem prefCount_zero_right (k : ℕ) : prefCount k 0 = 9 ^ k := by
  simp [prefCount]

/-- `prefCount (k+1) 0 = 9 * prefCount k 0`. -/
theorem prefCount_succ_zero (k : ℕ) : prefCount (k + 1) 0 = 9 * prefCount k 0 := by
  rw [prefCount_zero_right, prefCount_zero_right, pow_succ, mul_comm]

/-- One term of Pascal's rule, with the factor `9` taken out. -/
theorem choose_succ_mul_pow (k i : ℕ) :
    k.choose (i + 1) * 9 ^ (k - i) = 9 * (k.choose (i + 1) * 9 ^ (k - (i + 1))) := by
  rcases Nat.lt_or_ge i k with h | h
  · have : k - i = (k - (i + 1)) + 1 := by omega
    rw [this, pow_succ]; ring
  · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

/-- Pascal's rule for the counts of prefixes: a prefix of length `k + 1` with at most `j + 1`
symbols `P₀` is one of length `k` with at most `j + 1` of them followed by one of the nine other
terms, or one with at most `j` of them followed by `P₀`. -/
theorem prefCount_succ_succ (k j : ℕ) :
    prefCount (k + 1) (j + 1) = 9 * prefCount k (j + 1) + prefCount k j := by
  unfold prefCount
  rw [sum_range_succ' (fun i => (k + 1).choose i * 9 ^ (k + 1 - i)),
    sum_range_succ' (fun i => k.choose i * 9 ^ (k - i)) (j + 1)]
  simp only [Nat.choose_zero_right, Nat.sub_zero, one_mul, Nat.choose_succ_succ, add_mul,
    Nat.succ_sub_succ_eq_sub, sum_add_distrib, mul_add, mul_sum]
  have h : ∀ i ∈ range (j + 1), k.choose (i + 1) * 9 ^ (k - i)
      = 9 * (k.choose (i + 1) * 9 ^ (k - (i + 1))) := fun i _ => choose_succ_mul_pow k i
  rw [sum_congr rfl h, pow_succ]
  ring

/-- `prefCount (k+1) j = 9 prefCount k j + prefCount k (j-1)` for `1 ≤ j`. -/
theorem prefCount_succ_left (k : ℕ) {j : ℕ} (hj : 1 ≤ j) :
    prefCount (k + 1) j = 9 * prefCount k j + prefCount k (j - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rw [prefCount_succ_succ, Nat.add_sub_cancel]

/-- The number of prefixes of length `0`: the empty one. -/
theorem prefCount_zero_left (j : ℕ) : prefCount 0 j = 1 := by
  simp [prefCount, sum_range_succ', Nat.choose_zero_succ]

/-- `encWorkP 0 j = 1`: the leaf alone. -/
theorem encWorkP_zero_left (j : ℕ) : encWorkP 0 j = 1 := by
  simp [encWorkP, prefCount_zero_left]

/-- The work below a vertex at level `n + 1`: its slice of `7^(n+1)` entries, nine children with
the same budget and one with the budget reduced by one. -/
theorem encWorkP_succ_left (n : ℕ) {j : ℕ} (hj : 1 ≤ j) :
    encWorkP (n + 1) j = 7 ^ (n + 1) + 9 * encWorkP n j + encWorkP n (j - 1) := by
  unfold encWorkP
  rw [sum_range_succ' (fun k => prefCount k j * 7 ^ (n + 1 - k)), mul_sum, prefCount_zero_left,
    Nat.sub_zero, one_mul]
  have h : ∀ k ∈ range (n + 1), prefCount (k + 1) j * 7 ^ (n + 1 - (k + 1))
      = 9 * (prefCount k j * 7 ^ (n - k)) + prefCount k (j - 1) * 7 ^ (n - k) := fun k _ => by
    rw [Nat.succ_sub_succ_eq_sub, prefCount_succ_left k hj]; ring
  rw [sum_congr rfl h, sum_add_distrib]
  ring

/-- The analogue with the budget `0`: the term `P₀` is not entered. -/
theorem encWorkP_succ_zero (n : ℕ) : encWorkP (n + 1) 0 = 7 ^ (n + 1) + 9 * encWorkP n 0 := by
  unfold encWorkP
  rw [sum_range_succ' (fun k => prefCount k 0 * 7 ^ (n + 1 - k)), mul_sum, prefCount_zero_left,
    Nat.sub_zero, one_mul]
  have h : ∀ k ∈ range (n + 1), prefCount (k + 1) 0 * 7 ^ (n + 1 - (k + 1))
      = 9 * (prefCount k 0 * 7 ^ (n - k)) := fun k _ => by
    rw [Nat.succ_sub_succ_eq_sub, prefCount_succ_zero]; ring
  rw [sum_congr rfl h]
  ring

end Counts

/-! ## The leaves -/

/-- The digit of a term is `9` exactly for `P₀`. -/
theorem termIdx_eq_nine_iff (lam : Term) : ((termIdx lam : Fin 10) : ℕ) = 9 ↔ lam = .P0 := by
  cases lam with
  | P i j => simp only [termIdx]; constructor <;> intro h <;> [omega; cases h]
  | P0 => simp [termIdx_P0]

/-- The number of symbols `P₀` of a leaf, by its first symbol. -/
theorem card_P0Levels_cons {n : ℕ} (lam : Term) (τ' : Leaf n) :
    (P0Levels (Fin.cons lam τ' : Leaf (n + 1))).card
      = (if lam = .P0 then 1 else 0) + (P0Levels τ').card := by
  simp only [P0Levels, card_filter, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

/-! ## The text -/

namespace EncodeP

/-- The local variables of encodeP: the arguments L, j, src, out, scr, tab, p7, p10; the lengths
7^{L-1} and 10^{L-1}; the number of the term; the result of a call, which is not used. -/
abbrev Level : ℕ := 0
@[inherit_doc Level] abbrev Budget : ℕ := 1
@[inherit_doc Level] abbrev Src : ℕ := 2
@[inherit_doc Level] abbrev Out : ℕ := 3
@[inherit_doc Level] abbrev Scr : ℕ := 4
@[inherit_doc Level] abbrev Table : ℕ := 5
@[inherit_doc Level] abbrev Pow7 : ℕ := 6
@[inherit_doc Level] abbrev Pow10 : ℕ := 7
@[inherit_doc Level] abbrev Len7 : ℕ := 8
@[inherit_doc Level] abbrev Len10 : ℕ := 9
@[inherit_doc Level] abbrev TermNo : ℕ := 10
@[inherit_doc Level] abbrev Res : ℕ := 11

end EncodeP

open EncodeP

/-- The two calls for one term: step (2) into the scratch area, and step (3) from there into the
part of the output that belongs to the term, with the budget reduced by `dec` (`0` for the first
nine terms, `1` for `P₀`). -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/Recursion.lean (encodeTerm)
def encodeTermP (pS pE dec : ℕ) : Stmt :=
  .call pS [v Src, v Scr, v Len7, v TermNo, v Table] Res ;;
  .call pE [v Level -' k 1, v Budget -' k dec, v Scr, v Out +' v TermNo *' v Len10,
    v Scr +' v Len7, v Table, v Pow7, v Pow10] Res

/-- encodeP(L, j, src, out, scr, tab, p7, p10): upstream's encode(L, src, out, scr, tab, p7, p10)
with the budget `j` of symbols `P₀` as its second argument.  The nine terms `λ < 9` are treated with
the budget `j`; the term `P₀` (`λ = 9`, the counter of the loop after it) is treated with the budget
`j - 1` if `j ≥ 1`, and skipped if `j = 0`.  pS and pE are the numbers that the procedures encStep
and encodeP have in the program. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/Recursion.lean (encodeBody)
def encodePBody (pS pE : ℕ) : Stmt :=
  .ite (v Level =' k 0)
    (.store (v Out) (M (v Src)))
    (.set Len7 (M (v Pow7 +' v Level -' k 1)) ;;
     .set Len10 (M (v Pow10 +' v Level -' k 1)) ;;
     .for TermNo (k 9) (encodeTermP pS pE 0) ;;
     .ite (v Budget =' k 0) .skip (encodeTermP pS pE 1))

/-! ## How much time it needs -/

/-- The time of the two calls for one term with the budget `j` below. -/
def tTermP (L j : ℕ) (t : ℕ → ℕ → ℕ) : ℕ := 27 + tEncStep (7 ^ L) + t L j

/-- A bound on the number of steps of `encodeP`: at level `L + 1`, nine times the two calls for a
term with the budget `j`, the test on the budget, the two calls for `P₀` with the budget `j - 1` if
`j ≥ 1`, and 104 steps. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/Recursion.lean (encTime)
def tEncP : ℕ → ℕ → ℕ
  | 0, _ => 8
  | L + 1, 0 => 104 + 9 * (27 + tEncStep (7 ^ L) + tEncP L 0) + 4
  | L + 1, j + 1 => 104 + 9 * (27 + tEncStep (7 ^ L) + tEncP L (j + 1))
      + (31 + tEncStep (7 ^ L) + tEncP L j)

/-- The constant of the running time of `encodeP`. -/
def cEncP : ℕ := 778

/-- The number of steps is `O(encWorkP L j)`.  The two further terms on the left make the induction
go through. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/Recursion.lean (encTime_le)
theorem tEncP_le_aux (L : ℕ) : ∀ j, tEncP L j + 724 * 7 ^ L + 46 ≤ cEncP * encWorkP L j := by
  unfold cEncP
  induction L with
  | zero => intro j; simp [tEncP, encWorkP_zero_left]
  | succ L ih =>
    intro j
    cases j with
    | zero =>
      have := ih 0
      have : 1 ≤ 7 ^ L := Nat.one_le_pow _ _ (by norm_num)
      simp only [tEncP, tEncStep, encWorkP_succ_zero, pow_succ]
      omega
    | succ j =>
      have := ih (j + 1)
      have := ih j
      have : 1 ≤ 7 ^ L := Nat.one_le_pow _ _ (by norm_num)
      rw [encWorkP_succ_left L (by omega), Nat.add_sub_cancel]
      simp only [tEncP, tEncStep, pow_succ]
      omega

/-- The time of the pruned encoder is at most `cEncP` times its work. -/
theorem tEncP_le (L j : ℕ) : tEncP L j ≤ cEncP * encWorkP L j := by
  have := tEncP_le_aux L j
  omega

/-! ## What it guarantees -/

/-- What `encodeP` with the budget `j` guarantees: the leaves with at most `j` symbols `P₀` hold the
encoding, and only the `10^L` cells of `out` and the `scrSize L` cells of the scratch area have
changed. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/Recursion.lean (EncodePost)
def EncodePostP (μ : ℕ → ℤ) (out scr L : ℕ) (a c : ℕ → ℤ) (j : ℕ) (μ' : ℕ → ℤ) : Prop :=
  (∀ τ : Leaf L, (P0Levels τ).card ≤ j → μ' (out + codeT τ) = encIdx c L a (codeT τ)) ∧
    SameOutside2 μ μ' out (10 ^ L) scr (scrSize L)

variable {lim : Limits} {P : Program} {d : ℕ} {μ μ' μ₁ μ₂ : ℕ → ℤ}
  {src out scr tab p7 p10 L lam j : ℕ} {V : ℤ} {a c : ℕ → ℤ}

/-- The part of the encoding below the term number lam is the encoding of A_lam. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/Recursion.lean (encIdx_succ)
theorem encIdx_succ' (c a : ℕ → ℤ) (L lam : ℕ) {i : ℕ} (hi : i < 10 ^ L) :
    encIdx c (L + 1) a (lam * 10 ^ L + i) = encIdx c L (encSlice c a L lam) i := by
  rw [encIdx, Nat.mul_add_div_of_lt hi, Nat.mul_add_mod_of_lt hi]

/-- What has not changed at level `L + 1`, with the sizes in terms of `10^L`, `7^L` and
`scrSize L`. -/
theorem sameOutside2_succ'
    (h : SameOutside2 μ μ' out (10 ^ (L + 1)) scr (scrSize (L + 1))) :
    SameOutside2 μ μ' out (10 * 10 ^ L) scr (7 ^ L + scrSize L) := by
  simpa only [pow_succ', scrSize] using h

/-! ## One term -/

/-- The memory before the round of the term number `lam`: the leaves with at most `j` symbols `P₀`
below the earlier terms are filled, and only the output and the scratch area have changed. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/Recursion.lean (TermsDone)
def TermsDoneP (μ : ℕ → ℤ) (out scr L : ℕ) (a c : ℕ → ℤ) (j lam : ℕ) (μ' : ℕ → ℤ) : Prop :=
  (∀ τ : Leaf (L + 1), (P0Levels τ).card ≤ j → ((termIdx (τ 0) : Fin 10) : ℕ) < lam →
    μ' (out + codeT τ) = encIdx c (L + 1) a (codeT τ)) ∧
    SameOutside2 μ μ' out (10 ^ (L + 1)) scr (scrSize (L + 1))

/-- The two calls for the term number `lam`, with the budget `j'` below, fill the leaves below it
with at most `j` symbols `P₀`, if `j' ≥ j - [lam = 9]`. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/Recursion.lean (TermsDone.step)
theorem TermsDoneP.step (lay : EncodeLayout lim src out scr tab p7 p10 (L + 1)) (hlam : lam < 10)
    (h : TermsDoneP μ out scr L a c j lam μ') (same₁ : SameOutside μ' μ₁ scr (7 ^ L)) {j' : ℕ}
    (hj' : j ≤ j' + if lam = 9 then 1 else 0)
    (hpost : EncodePostP μ₁ (out + lam * 10 ^ L) (scr + 7 ^ L) L (encSlice c a L lam) c j' μ₂) :
    TermsDoneP μ out scr L a c j (lam + 1) μ₂ := by
  have hplaces := lay.places_succ
  have hpart : lam * 10 ^ L + 10 ^ L ≤ 10 * 10 ^ L := Nat.mul_add_le_mul hlam le_rfl
  obtain ⟨hdone, same⟩ := h
  obtain ⟨hnew, same₂⟩ := hpost
  have hkept := sameOutside2_succ' same
  refine ⟨fun τ hτ hlt => ?_, ?_⟩
  · have hcode := codeT_lt τ
    have hcons : (Fin.cons (τ 0) (Fin.tail τ) : Leaf (L + 1)) = τ := Fin.cons_self_tail τ
    have hcodeT : codeT τ = ((termIdx (τ 0) : Fin 10) : ℕ) * 10 ^ L + codeT (Fin.tail τ) := by
      rw [← hcons, codeT_cons, Fin.cons_zero, Fin.tail_cons]
    have htail := codeT_lt (Fin.tail τ)
    by_cases hold : ((termIdx (τ 0) : Fin 10) : ℕ) < lam
    · -- The leaves below the earlier terms are not touched.
      have hi : codeT τ < lam * 10 ^ L := by
        rw [hcodeT]; exact Nat.mul_add_lt_mul hold htail
      rw [same₂ _ (by omega), same₁ _ (by omega), hdone τ hτ hold]
    · -- The leaves below this term.
      have heq : ((termIdx (τ 0) : Fin 10) : ℕ) = lam := by omega
      have hcard : (P0Levels τ).card
          = (if τ 0 = .P0 then 1 else 0) + (P0Levels (Fin.tail τ)).card := by
        rw [← card_P0Levels_cons, hcons]
      have hbud : (P0Levels (Fin.tail τ)).card ≤ j' := by
        by_cases h9 : lam = 9
        · have : τ 0 = .P0 := (termIdx_eq_nine_iff _).1 (heq.trans h9)
          simp only [this, ite_true, h9] at hcard hj'
          omega
        · have : τ 0 ≠ .P0 := fun h => h9 (heq.symm.trans ((termIdx_eq_nine_iff _).2 h))
          simp only [this, ite_false, h9] at hcard hj'
          omega
      rw [hcodeT, heq, ← Nat.add_assoc, hnew _ hbud, encIdx_succ' c a L lam htail]
  · simp only [pow_succ', scrSize]
    clear same
    light_keep

/-- With the budget `0`, the term `P₀` is skipped: no leaf with no symbol `P₀` lies below it. -/
theorem TermsDoneP.skip (h : TermsDoneP μ out scr L a c 0 9 μ') :
    TermsDoneP μ out scr L a c 0 10 μ' := by
  refine ⟨fun τ hτ hlt => h.1 τ hτ ?_, h.2⟩
  rcases Nat.lt_or_ge ((termIdx (τ 0) : Fin 10) : ℕ) 9 with h9 | h9
  · exact h9
  · exfalso
    have heq : ((termIdx (τ 0) : Fin 10) : ℕ) = 9 := by omega
    have hmem : (0 : Fin (L + 1)) ∈ P0Levels τ := by
      rw [P0Levels, mem_filter]
      exact ⟨mem_univ _, (termIdx_eq_nine_iff _).1 heq⟩
    have := card_pos.2 ⟨_, hmem⟩
    omega

/-- After all ten terms, the output is as `encodeP` guarantees. -/
theorem TermsDoneP.done (h : TermsDoneP μ out scr L a c j 10 μ') :
    EncodePostP μ out scr (L + 1) a c j μ' :=
  ⟨fun τ hτ => h.1 τ hτ (termIdx (τ 0)).isLt, h.2⟩

/-- The list of the local variables at level L + 1. -/
abbrev EncodeP.locals (L j src out scr tab p7 p10 lam : ℕ) (r : ℤ) : List ℤ :=
  [(L + 1 : ℕ), j, src, out, scr, tab, p7, p10, (7 ^ L : ℕ), (10 ^ L : ℕ), lam, r]

/-- The specification of encodeP at level L with every budget, for a caller at depth d. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/Recursion.lean (EncodeMeets)
def EncodeMeetsP (lim : Limits) (P : Program) (pE d tab p7 p10 L : ℕ) (c : ℕ → ℤ) : Prop :=
  ∀ (j : ℕ) (μ : ℕ → ℤ) (src out scr : ℕ) (V : ℤ) (a : ℕ → ℤ), (j : ℤ) ≤ lim.word →
    EncodePre lim μ src out scr tab p7 p10 V L a c →
    Meets lim P pE (d + 1) [L, j, src, out, scr, tab, p7, p10] μ (tEncP L j) fun _ μ' =>
      EncodePostP μ out scr L a c j μ'


/-- **One term**: step (2) and step (3) fill the leaves below the term number `lam` with at most `j`
symbols `P₀`, with the budget `j - dec` below, where `dec ≤ min j 1` and `dec = 0` if `lam ≠ 9`. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/Recursion.lean (encodeTerm_spec)
theorem encodeTermP_spec (hS : P[pS]? = some encStepBody)
    (hrec : EncodeMeetsP lim P pE d tab p7 p10 L c)
    (pre : EncodePre lim μ src out scr tab p7 p10 V (L + 1) a c) (hd : d < lim.depth)
    (hj : (j : ℤ) ≤ lim.word) (hlam : lam < 10) {dec : ℕ} (hdec : dec ≤ j) (hdec1 : dec ≤ 1)
    (hdec' : lam ≠ 9 → dec = 0) (h : TermsDoneP μ out scr L a c j lam μ') (r : ℤ) :
    Ends lim P d (encodeTermP pS pE dec) ⟨frame (locals L j src out scr tab p7 p10 lam r), μ'⟩
      (tTermP L (j - dec) tEncP) fun σ' => ∃ (r' : ℤ) (μ'' : ℕ → ℤ),
        σ' = ⟨frame (locals L j src out scr tab p7 p10 lam r'), μ''⟩ ∧
          TermsDoneP μ out scr L a c j (lam + 1) μ'' := by
  have := pre.lay.places_succ
  -- The arguments of the two calls fit in a word, by the layout and the next facts.
  have : lam * 10 ^ L + 10 ^ L ≤ 10 * 10 ^ L := Nat.mul_add_le_mul hlam le_rfl
  have : ((lam * 10 ^ L : ℕ) : ℤ) = lam * 10 ^ L := by push_cast; rfl
  have : ((7 ^ L : ℕ) : ℤ) = 7 ^ L := by push_cast; rfl
  have : ((j - dec : ℕ) : ℤ) = j - dec := by omega
  have : j ≤ (j - dec) + if lam = 9 then 1 else 0 := by
    split_ifs with h9
    · omega
    · rw [hdec' h9]; omega
  unfold encodeTermP tTermP
  -- Res := encStep(src, scr, 7^L, lam, tab)
  light_call (encStep_meets hS (EncodePre.toStep pre hlam h.2)) with r₁ μ₁ ⟨hstep, same₁⟩
  -- Res := encodeP(L, j - dec, scr, out + lam 10^L, scr + 7^L, tab, p7, p10)
  refine Ends.callTo (hrec (j - dec) _ _ _ _ _ _ (by omega)
    (EncodePre.toRec pre hlam h.2 hstep same₁)) ?_
  exact fun r₂ μ₂ hpost => ⟨r₂, μ₂, rfl, h.step pre.lay hlam same₁ this hpost⟩

/-! ## The recursion -/

/-- **A leaf**: the number is copied, whatever the budget. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/Recursion.lean (encode_leaf)
theorem encodeP_leaf (pre : EncodePre lim μ src out scr tab p7 p10 V 0 a c) :
    Ends lim P d (encodePBody pS pE) ⟨frame [(0 : ℕ), j, src, out, scr, tab, p7, p10], μ⟩
      (tEncP 0 j) fun σ' => EncodePostP μ out scr 0 a c j σ'.mem := by
  light_facts pre.lay pre.lay.std
  have hread : μ src = a 0 := pre.srcV 0 (by norm_num)
  -- if Level = 0 then mem[Out] := mem[Src]
  refine Ends.iteLast (fun _ => ?_) (fun h => absurd (by simp) h) (hT := by simp [tEncP])
  refine Ends.storeTo out (a 0) ⟨fun τ _ => ?_, by light_keep⟩
    (by light_side [hread]) (by simp [tEncP])
  have h0 : codeT τ = 0 := by have := codeT_lt τ; simpa using this
  rw [h0, Nat.add_zero]
  exact Function.update_self ..

/-- **An inner vertex**: the two lengths are read from the tables, the loop runs through the nine
terms `λ < 9`, and the term `P₀` is entered if the budget allows it. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/Recursion.lean (encode_node)
theorem encodeP_node (hS : P[pS]? = some encStepBody)
    (hrec : EncodeMeetsP lim P pE d tab p7 p10 L c)
    (pre : EncodePre lim μ src out scr tab p7 p10 V (L + 1) a c) (hd : d < lim.depth)
    (hj : (j : ℤ) ≤ lim.word) :
    Ends lim P d (encodePBody pS pE) ⟨frame [(L + 1 : ℕ), j, src, out, scr, tab, p7, p10], μ⟩
      (tEncP (L + 1) j) fun σ' => EncodePostP μ out scr (L + 1) a c j σ'.mem := by
  have hplaces := pre.lay.places_succ
  have haddr7 : ((p7 : ℤ) + ((L : ℤ) + 1) - 1).toNat = p7 + L := by omega
  have haddr10 : ((p10 : ℤ) + ((L : ℤ) + 1) - 1).toNat = p10 + L := by omega
  have hread7 := pre.p7V L (by omega)
  have hread10 := pre.p10V L (by omega)
  -- The time at this level, in both cases of the budget.
  have htime : tEncP (L + 1) j = 104 + 9 * tTermP L j tEncP
      + (4 + if j = 0 then 0 else tTermP L (j - 1) tEncP) := by
    cases j with
    | zero => simp [tEncP, tTermP]
    | succ j => simp [tEncP, tTermP]; omega
  rw [htime]
  -- if Level = 0
  refine Ends.iteLast (fun h => absurd h (by simp; omega)) (fun _ => ?_)
  -- Len7 := mem[Pow7 + Level - 1]; Len10 := mem[Pow10 + Level - 1]
  light_set (7 ^ L : ℕ) using haddr7, hread7
  light_set (10 ^ L : ℕ) using haddr10, hread10
  -- for TermNo < 9: the leaves below the earlier terms are filled
  refine Ends.next (9 * (1 + tTermP L j tEncP + 7) + 1 + 5) ?_
  refine Ends.forShape (fun lam r μ' => ⟨frame (locals L j src out scr tab p7 p10 lam r), μ'⟩)
    (TermsDoneP μ out scr L a c j) 9 (tTermP L j tEncP) 0
    ⟨fun τ _ h => absurd h (by omega), .refl⟩
    (fun lam r μ' hlam h => by
      simpa using encodeTermP_spec hS hrec pre hd hj (by omega) (Nat.zero_le j) (Nat.zero_le 1)
        (fun _ => rfl) h r)
    (fun r μ' h => ?_) (by rw [update_frame_setLocal, ← frame_append_zeros _ 1]; rfl)
  -- if Budget = 0 then skip else the two calls for P₀ with the budget j - 1
  refine Ends.iteLast (fun hc => ?_) (fun hc => ?_)
  · -- the budget is exhausted: nothing to do for P₀
    have hj : j = 0 := by simpa using hc
    subst hj
    exact Ends.skip h.skip.done
  · have hjne : j ≠ 0 := by simpa using hc
    have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.2 hjne
    refine (encodeTermP_spec hS hrec pre hd hj (by omega) hj1 le_rfl (fun h => absurd rfl h)
      h r).mono
      (by simp [hjne]; omega) ?_
    rintro σ' ⟨r', μ'', rfl, h'⟩
    exact h'.done

/-- **encodeP** is correct and takes at most `tEncP L j` steps, in every program whose procedures
number pS and pE are encStep and encodeP.  It nests calls at most L deep. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/Recursion.lean (encode_spec)
theorem encodeP_spec (hS : P[pS]? = some encStepBody) (hE : P[pE]? = some (encodePBody pS pE))
    (hd : d + L ≤ lim.depth) (hj : (j : ℤ) ≤ lim.word)
    (pre : EncodePre lim μ src out scr tab p7 p10 V L a c) :
    Ends lim P d (encodePBody pS pE) ⟨frame [L, j, src, out, scr, tab, p7, p10], μ⟩ (tEncP L j)
      fun σ' => EncodePostP μ out scr L a c j σ'.mem := by
  induction L generalizing d μ src out scr V a j with
  | zero => exact encodeP_leaf pre
  | succ L ih =>
    exact encodeP_node hS
      (fun _ _ _ _ _ _ _ hj' pre' => Meets.of_body hE (ih (by omega) hj' pre')) pre (by omega) hj

end Light.Sec2
end

section
/-!
# What encode computes, in the paper's terms

The result of encode is described by a recursion on positions in arrays (`encIdx`).  Here this is
linked with the definitions of the paper (Section 2.4.1) through arrays on strings as lists: if the
source holds an array on strings and the table holds the coefficients of the linear forms, then the
output holds the encoding of the array.

Both sides are treated at once, for an alphabet of seven variables with any coefficients:
`computeEncoding` is the procedure of Section 2.4.1 for such an alphabet,
`encIdx_eq_computeEncoding` says that the recursion on positions computes it, and `encode_str` is
the specification of encode in these terms. For the two alphabets of the paper the procedure gives
the two encodings (`computeEncoding_phi`, `computeEncoding_psi`).
-/


open ThreeSumApsp

namespace Light.Sec2

open Finset ThreeSumApsp.Spec

/-! ## From positions to strings -/

section
variable {α : Type} [Fintype α] (e : α ≃ Fin 7) (coef : Term → α → ℤ)

/-- The recursion on positions computes the procedure of Section 2.4.1, if the array and the table
of coefficients are stored by digits. -/
theorem encIdx_eq_computeEncoding {c : ℕ → ℤ}
    (hc : ∀ lam s, c (7 * (termIdx lam : ℕ) + (e s : ℕ)) = coef lam s) (L : ℕ)
    (A : (Fin L → α) → ℤ) {arr : ℕ → ℤ}
    (harr : ∀ j < 7 ^ L, arr j = A (decodeStr e L j)) {i : ℕ} (hi : i < 10 ^ L) :
    encIdx c L arr i = computeEncoding coef L A (decodeT L i) := by
  induction L generalizing arr i with
  | zero =>
    rw [encIdx, computeEncoding, harr 0 (by norm_num)]
    exact congrArg A (Subsingleton.elim _ _)
  | succ L ih =>
    -- The first digit of i is the digit of a term λ, and the rest of i is the code of a leaf below.
    have hpos : 0 < 10 ^ L := by positivity
    have hdigit : i / 10 ^ L < 10 := by rwa [Nat.div_lt_iff_lt_mul hpos, ← pow_succ']
    have hrest : i % 10 ^ L < 10 ^ L := Nat.mod_lt _ hpos
    obtain ⟨lam, hidx⟩ : ∃ lam : Term, ((termEquiv lam : Fin 10) : ℕ) = i / 10 ^ L :=
      ⟨termOfNat _, termIdx_termOfNat hdigit⟩
    have hleaf : decodeT (L + 1) i = Fin.cons lam (decodeT L (i % 10 ^ L)) := by
      have hcons := decodeStr_cons termEquiv lam hrest
      rwa [hidx, Nat.div_add_mod'] at hcons
    rw [encIdx, hleaf, computeEncoding, Fin.cons_zero, Fin.tail_cons]
    unfold encSlice
    -- Step (2) of the procedure of Section 2.4.1: the sum over the digits is the sum over the
    -- variables.
    refine ih _ (fun j hj => ?_) hrest
    rw [← Fin.sum_univ_eq_sum_range (fun s => c (7 * (i / 10 ^ L) + s) * arr (s * 7 ^ L + j)) 7,
      ← e.sum_comp fun s : Fin 7 => c (7 * (i / 10 ^ L) + (s : ℕ)) * arr ((s : ℕ) * 7 ^ L + j)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [sliceAt, ← hidx, show ((termEquiv lam : Fin 10) : ℕ) = termIdx lam from rfl, hc,
      harr _ (by rw [pow_succ']; exact Nat.mul_add_lt_mul (e s).isLt hj), decodeStr_cons e s hj]

end

/-! ## The specification of encode, on lists -/

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {src out scr tab p7 p10 L : ℕ} {V : ℤ}

/-- The hypotheses of encode hold if the source, the table of coefficients and the two tables of
powers are in their places and the numbers obey the bounds. -/
theorem EncodePre.of_seg {l T : List ℤ} (lay : EncodeLayout lim src out scr tab p7 p10 L)
    (hl : l.length = 7 ^ L) (hsrc : Seg μ src l) (hV : ∀ x ∈ l, -V ≤ x ∧ x ≤ V)
    (hT : T.length = 70) (htab : Seg μ tab T) (hc : ∀ x ∈ T, -1 ≤ x ∧ x ≤ 1)
    (h7 : ∀ i < L, μ (p7 + i) = ((7 ^ i : ℕ) : ℤ)) (h10 : ∀ i < L, μ (p10 + i) = ((10 ^ i : ℕ) : ℤ))
    (hVB : ((7 ^ L : ℕ) : ℤ) * V ≤ lim.word) :
    EncodePre lim μ src out scr tab p7 p10 V L (fun j => l.getD j 0) (fun i => T.getD i 0) :=
  { lay := lay
    srcV := fun j hj => hsrc.getD (by omega) 0
    src_bound := fun j hj => by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact hV _ (List.getElem_mem _)
    tabV := fun i hi => htab.getD (by omega) 0
    coef_bound := fun i hi => by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact hc _ (List.getElem_mem _)
    p7V := h7, p10V := h10, word_bound := hVB }




variable {lim : Limits} {P : Program} {n Lmax src dst scr tab p7 p10 : ℕ} {μ : ℕ → ℤ}

/-- The scratch area of encode has fewer than 7^L cells. -/
theorem scrSize_le (L : ℕ) : scrSize L + 1 ≤ 7 ^ L := by
  induction L with
  | zero => simp [scrSize]
  | succ L ih =>
    rw [scrSize, pow_succ]
    omega

/-- The places that the callers provide are a layout for encode. -/
theorem EncodePlaces.layout (std : Std lim)
    (h : EncodePlaces lim n Lmax src dst scr tab p7 p10 μ) :
    EncodeLayout lim src dst scr tab p7 p10 n := by
  light_facts h
  have := scrSize_le n
  exact ⟨std, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- A cell of a table of powers. -/
theorem pow_of_seg {p b : ℕ} (h : Seg μ p (powList b (Lmax + 1))) (hn : n ≤ Lmax) :
    ∀ i < n, μ (p + i) = ((b ^ i : ℕ) : ℤ) := fun i hi => by
  rw [h.get (i := i) (by simp; omega), getElem_powList]




variable {lim : Limits} {P : Program}

namespace Bands

/-- The local variables of `encodeBands`.  The arguments: `Levels` = L, `Size` = m, `Rows` = N,
`Cols` = D, `NumBlocks` = K0, `Width` = N0, `Cells` = S7 = 7^L, `Leaves` = T = 10^L and `NumBands` =
nB are the sizes of the layout; `Side` says which of the two matrices stands at `Source`, with the
steps `StepRow` and `StepCol`; `MaskTable`, `Digits3` and `Digits4` are the tables that
`bandArray` reads, `Table`, `Pow7` and `Pow10` those that `encode` reads; `Arr` and `Scratch` are
scratch areas, and the encodings are written from `Enc` on.  Then `BandNo` = β, and `Res` takes the
results of the calls. -/
abbrev Levels : ℕ := 0
@[inherit_doc Levels] abbrev Size : ℕ := 1
@[inherit_doc Levels] abbrev Rows : ℕ := 2
@[inherit_doc Levels] abbrev Cols : ℕ := 3
@[inherit_doc Levels] abbrev NumBlocks : ℕ := 4
@[inherit_doc Levels] abbrev Width : ℕ := 5
@[inherit_doc Levels] abbrev Cells : ℕ := 6
@[inherit_doc Levels] abbrev Leaves : ℕ := 7
@[inherit_doc Levels] abbrev NumBands : ℕ := 8
@[inherit_doc Levels] abbrev Side : ℕ := 9
@[inherit_doc Levels] abbrev Source : ℕ := 10
@[inherit_doc Levels] abbrev StepRow : ℕ := 11
@[inherit_doc Levels] abbrev StepCol : ℕ := 12
@[inherit_doc Levels] abbrev MaskTable : ℕ := 13
@[inherit_doc Levels] abbrev Digits3 : ℕ := 14
@[inherit_doc Levels] abbrev Digits4 : ℕ := 15
@[inherit_doc Levels] abbrev Arr : ℕ := 16
@[inherit_doc Levels] abbrev Scratch : ℕ := 17
@[inherit_doc Levels] abbrev Table : ℕ := 18
@[inherit_doc Levels] abbrev Pow7 : ℕ := 19
@[inherit_doc Levels] abbrev Pow10 : ℕ := 20
@[inherit_doc Levels] abbrev Enc : ℕ := 21
@[inherit_doc Levels] abbrev BandNo : ℕ := 22
@[inherit_doc Levels] abbrev Res : ℕ := 23

end Bands

/-! ## The arguments, and what is assumed about them -/

/-- The addresses that encodeBands gets besides that of the matrix.  mask, dig3 and dig4 are the
tables that bandArray reads, tab, p7 and p10 those that encode reads.  arr and zs are scratch, and
the encodings are written from enc on. -/
structure BandsArgs where
  (mask dig3 dig4 arr zs tab p7 p10 enc : ℕ)

/-- The arguments of encodeBands at the sizes of p, for the matrix at aA with the strides sI and
sK. -/
@[simp] def BandsArgs.vals (x : BandsArgs) (p : Par) (side aA sI sK : ℕ) : List ℤ :=
  [p.L, p.m, p.N, p.D, p.K0, p.N0, p.S7, p.T, p.nB, side, aA, sI, sK, x.mask, x.dig3, x.dig4,
    x.arr, x.zs, x.tab, x.p7, x.p10, x.enc]

/-- What encodeBands assumes besides the matrix.  Everything that is read lies below enc: the tables
of bandArray, the 70 coefficients coefs of the side, and the powers of 7 and of 10.  From enc on
follow the encodings and the two scratch areas.  V bounds the entries of the matrix. -/
structure BandsPre (lim : Limits) (p : Par) (μ : ℕ → ℤ) (x : BandsArgs) (coefs : List ℤ) (V : ℤ) :
    Prop where
  tables : BandTables p μ x.mask x.dig3 x.dig4 x.enc
  coef : Seg μ x.tab coefs
  coef_le : x.tab + 70 ≤ x.enc
  p7 : Seg μ x.p7 (powList 7 (p.L + 1))
  p7_le : x.p7 + (p.L + 1) ≤ x.enc
  p10 : Seg μ x.p10 (powList 10 (p.L + 1))
  p10_le : x.p10 + (p.L + 1) ≤ x.enc
  enc_le : x.enc + p.nB * p.T ≤ x.arr
  arr_le : x.arr + p.S7 ≤ x.zs
  zs_le : x.zs + p.S7 ≤ lim.space
  V_nonneg : 0 ≤ V
  word : 7 ^ (p.L + 1) * V ≤ lim.word

variable {p : Par} {x : BandsArgs} {coefs : List ℤ} {V : ℤ} {μ μ' : ℕ → ℤ}

/-! ## What is read does not change -/

/-- The tables that bandArray reads, in a memory that agrees below their bound. -/
theorem BandTables.congr_below {p : Par} {μ μ' : ℕ → ℤ} {mask dig3 dig4 e : ℕ}
    (h : BandTables p μ mask dig3 dig4 e) (hlow : ∀ x < e, μ' x = μ x) :
    BandTables p μ' mask dig3 dig4 e where
  hmask := fun s hs => (h.hmask s hs).congr fun i hi => hlow _ (by
    have hrow : s * p.L + p.L ≤ p.KK * p.L := Nat.mul_add_le_mul hs le_rfl
    have hend := h.mask_le
    simp at hi
    omega)
  hdig3 := fun I hI => (h.hdig3 I hI).congr fun i hi => hlow _ (by
    have hrow : I * p.Lo + p.Lo ≤ p.N * p.Lo := Nat.mul_add_le_mul hI le_rfl
    have := h.dig3_le
    simp at hi
    omega)
  hdig4 := fun x hx => (h.hdig4 x hx).congr fun i hi => hlow _ (by
    have : x * p.m + p.m ≤ p.D * p.m := Nat.mul_add_le_mul hx le_rfl
    have := h.dig4_le
    simp at hi
    omega)
  mask_le := h.mask_le
  dig3_le := h.dig3_le
  dig4_le := h.dig4_le

/-- The tables also lie below every larger bound. -/
theorem BandTables.mono {p : Par} {μ : ℕ → ℤ} {mask dig3 dig4 e e' : ℕ}
    (h : BandTables p μ mask dig3 dig4 e) (hle : e ≤ e') : BandTables p μ mask dig3 dig4 e' :=
  { h with
    mask_le := h.mask_le.trans hle
    dig3_le := h.dig3_le.trans hle
    dig4_le := h.dig4_le.trans hle }

/-- The places of the call of encode for the band β, in a memory that agrees with μ below enc. -/
theorem BandsPre.encodePlaces (pre : BandsPre lim p μ x coefs V) {β : ℕ} (hβ : β < p.nB)
    (hlow : ∀ b < x.enc, μ' b = μ b) :
    EncodePlaces lim p.L p.L x.arr (x.enc + β * p.T) x.zs x.tab x.p7 x.p10 μ' := by
  light_facts pre
  exact
    { n_le := le_rfl
      hp7 := pre.p7.congr fun i hi => hlow _ (by simp at hi; omega)
      hp10 := pre.p10.congr fun i hi => hlow _ (by simp at hi; omega)
      tab_le := by omega
      p7_le := by omega
      p10_le := by omega
      dst_le := by
        have hβT : β * p.T + p.T ≤ p.nB * p.T := Nat.mul_add_le_mul hβ le_rfl
        change x.enc + β * p.T + p.T ≤ x.arr
        omega
      src_le := pre.arr_le
      scr_le := pre.zs_le }

/-! ## The two entries -/



open ImprovedExponents

variable {lim : Limits} {P : Program} {n Lmax j src dst scr tab p7 p10 : ℕ} {μ : ℕ → ℤ}

theorem encodeP_entry {α : Type} [Fintype α] (e : α ≃ Fin 7) (coef : Term → α → ℤ)
    {T : List ℤ} (hT : T.length = 70) (hc : ∀ x ∈ T, -1 ≤ x ∧ x ≤ 1)
    (hcoef : ∀ lam s, T.getD (7 * (termIdx lam : ℕ) + (e s : ℕ)) 0 = coef lam s) (std : Std lim)
    (hS : P[pEncStep]? = some encStepBody)
    (hE : P[Proc.encodeP]? = some (encodePBody pEncStep Proc.encodeP))
    {d : ℕ} (hd : d + (n + 1) ≤ lim.depth) (hpl : EncodePlaces lim n Lmax src dst scr tab p7 p10 μ)
    (htab : Seg μ tab T) (A : (Fin n → α) → ℤ) (hsrc : Seg μ src (arrStr e A)) {V : ℤ}
    (hV : ∀ u, |A u| ≤ V) (hVB : 7 ^ (n + 1) * V ≤ lim.word) (hj : (j : ℤ) ≤ lim.word) :
    Meets lim P Proc.encodeP d [n, j, src, dst, scr, tab, p7, p10] μ (cEncP * encWorkP n j)
      fun _ μ' => SegOn j μ' dst (computeEncoding coef n A) ∧
        SameOutside2 μ μ' dst (10 ^ n) scr (7 ^ n) := by
  have hV0 : 0 ≤ V := (abs_nonneg _).trans (hV fun _ => e.symm 0)
  have hVB' : ((7 ^ n : ℕ) : ℤ) * V ≤ lim.word := by
    refine le_trans ?_ hVB
    push_cast
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)) hV0
  have := scrSize_le n
  have hbound : ∀ x ∈ arrStr e A, -V ≤ x ∧ x ≤ V := fun x hx => by
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
    exact abs_le.1 (hV _)
  have pre := EncodePre.of_seg (hpl.layout std) (length_arrStr e A) hsrc hbound hT htab hc
    (pow_of_seg hpl.hp7 hpl.n_le) (pow_of_seg hpl.hp10 hpl.n_le) hVB'
  refine .of_body hE ((encodeP_spec hS hE (by omega) hj pre).mono (tEncP_le n j)
    fun σ' h => ⟨?_, h.2.mono fun x hx => by omega⟩)
  intro τ hτ
  rw [h.1 τ hτ,
    encIdx_eq_computeEncoding e coef hcoef n A (fun i hi => getD_arrStr_of_lt e A hi) (codeT_lt τ)]
  congr 1
  exact decodeStr_codeStr termEquiv τ

/-! ## The loop -/

open Bands in
/-- encodeBandsP(L, m, N, D, K0, N0, S7, T, nB, side, aA, sI, sK, mask, dig3, dig4, arr, zs, tab,
p7, p10, enc): for each band, the input array is formed at arr and encoded with the budget m into
the T cells from enc + β T. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/AllBands.lean (encodeBandsBody)
def encodeBandsPBody : Stmt :=
  .for BandNo (v NumBands) (
    .call pBandArray [v Levels, v Size, v Rows, v Cols, v NumBlocks, v Width, v Cells, v BandNo,
      v Side, v Source, v StepRow, v StepCol, v MaskTable, v Digits3, v Digits4, v Arr] Res ;;
    .call Proc.encodeP [v Levels, v Size, v Arr, v Enc +' v BandNo *' v Leaves, v Scratch, v Table,
      v Pow7, v Pow10] Res)

/-- The time of the loop is at most the constant cB + cE + 51 times the shape of the entries. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/AllBands.lean (encodeBands_time)
theorem encodeBandsP_time (p : Par) (cB cE : ℕ) :
    p.nB * (cB * bandArrayShape p + cE * encWorkP p.L p.m + 51) + 6
      ≤ (cB + cE + 51) * (p.nB * (encWorkP p.L p.m + bandArrayShape p) + 1) := by
  have hW : 1 ≤ encWorkP p.L p.m :=
    (Nat.one_le_pow _ _ (by norm_num)).trans (pow_seven_le_encWorkP p.L p.m)
  have hfifty : p.nB * 51 ≤ p.nB * (51 * encWorkP p.L p.m) := Nat.mul_le_mul_left _ (by omega)
  generalize encWorkP p.L p.m = W at hW hfifty ⊢
  calc p.nB * (cB * bandArrayShape p + cE * W + 51) + 6
      = p.nB * (cB * bandArrayShape p) + p.nB * (cE * W) + p.nB * 51 + 6 := by ring
    _ ≤ p.nB * (cB * bandArrayShape p) + p.nB * (cE * W) + p.nB * (51 * W) + 6
        + (p.nB * (cB * W) + p.nB * ((cE + 51) * bandArrayShape p) + (cB + cE + 45)) := by omega
    _ = (cB + cE + 51) * (p.nB * (W + bandArrayShape p) + 1) := by ring

variable {p : Par} {x : BandsArgs} {coefs : List ℤ} {V : ℤ} {μ' : ℕ → ℤ}

/-- **encodeBandsP**, at the sizes of `p`, for callees described by what they do here: `HB` says
that `bandArray` leaves the list `A β` at `arr`, within `cB bandArrayShape` steps, `HE` that
`encodeP` with the budget `m` turns it into the encoding `E β` at the leaves with at most `m`
symbols `P₀` from `enc + β T`, within `cE encWorkP L m` steps; both in any memory that agrees with
`μ` below `enc`.  Then the encodings `E β` stand from `enc` on. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/AllBands.lean (encodeBands_proc)
theorem encodeBandsP_proc (std : Std lim) (hP : P[Proc.encodeBandsP]? = some encodeBandsPBody)
    {d side aA sI sK cB cE : ℕ} {A : ℕ → List ℤ} {E : ℕ → Leaf p.L → ℤ}
    (pre : BandsPre lim p μ x coefs V) (hd : d < lim.depth)
    (HB : ∀ β < p.nB, ∀ μ' : ℕ → ℤ, Kept μ μ' x.enc →
      Meets lim P pBandArray (d + 1)
        [p.L, p.m, p.N, p.D, p.K0, p.N0, p.S7, β, side, aA, sI, sK, x.mask, x.dig3, x.dig4, x.arr]
        μ' (cB * bandArrayShape p) fun _ μ'' =>
          Seg μ'' x.arr (A β) ∧ SameOutside μ' μ'' x.arr p.S7)
    (HE : ∀ β < p.nB, ∀ μ' : ℕ → ℤ, Kept μ μ' x.enc → Seg μ' x.arr (A β) →
      Meets lim P Proc.encodeP (d + 1)
        [p.L, p.m, x.arr, (x.enc + β * p.T : ℕ), x.zs, x.tab, x.p7, x.p10] μ'
        (cE * encWorkP p.L p.m) fun _ μ'' => SegOn p.m μ'' (x.enc + β * p.T) (E β) ∧
          SameOutside2 μ' μ'' (x.enc + β * p.T) (10 ^ p.L) x.zs (7 ^ p.L)) :
    Meets lim P Proc.encodeBandsP d (x.vals p side aA sI sK) μ
      ((cB + cE + 51) * (p.nB * (encWorkP p.L p.m + bandArrayShape p) + 1)) fun _ μ' =>
        (∀ β < p.nB, SegOn p.m μ' (x.enc + β * p.T) (E β)) ∧
          SameOutside μ μ' x.enc (x.zs + p.S7 - x.enc) := by
  refine .of_body hP (Ends.mono
    (T := p.nB * (cB * bandArrayShape p + cE * encWorkP p.L p.m + 51) + 6) ?_
    (encodeBandsP_time p cB cE) fun _ h => h)
  light_facts pre std
  have : p.T = 10 ^ p.L := rfl
  have : p.S7 = 7 ^ p.L := rfl
  have : p.nB ≤ p.nB * p.T := Nat.le_mul_of_pos_right _ p.one_le_T
  -- for β < nB: the encodings of the bands below β are in place
  refine Ends.forShape
    (fun β r μ' => ⟨frame [p.L, p.m, p.N, p.D, p.K0, p.N0, p.S7, p.T, p.nB, side, aA, sI, sK,
      x.mask, x.dig3, x.dig4, x.arr, x.zs, x.tab, x.p7, x.p10, x.enc, β, r], μ'⟩)
    (fun β μ' => (∀ β' < β, SegOn p.m μ' (x.enc + β' * p.T) (E β')) ∧
      SameOutside μ μ' x.enc (x.zs + p.S7 - x.enc))
    p.nB (cB * bandArrayShape p + cE * encWorkP p.L p.m + 43) 0
    ⟨fun β' h => absurd h (by omega), .refl⟩
    ?round (fun _ _ h => h) (by rw [update_frame_setLocal, ← frame_append_zeros _ 1]; rfl)
  rintro β r μ' hβ ⟨hdone, same⟩
  have hβT : β * p.T + p.T ≤ p.nB * p.T := Nat.mul_add_le_mul hβ le_rfl
  -- bandArray(L, m, N, D, K0, N0, S7, β, side, aA, sI, sK, mask, dig3, dig4, arr)
  light_call (HB β hβ μ' (by light_keep)) with r₁ μ₁ ⟨hA, same₁⟩
  -- encodeP(L, m, arr, enc + β T, zs, tab, p7, p10)
  light_call (HE β hβ μ₁ (by light_keep) hA) with r₂ μ₂ ⟨hEβ, same₂⟩
  refine ⟨r₂, μ₂, rfl, fun β' hβ' => ?_, by light_keep⟩
  rcases Nat.lt_or_ge β' β with h | h
  · -- The encodings of the earlier bands lie below enc + β T and have not been touched.
    have hβ'T : β' * p.T + p.T ≤ β * p.T := Nat.mul_add_le_mul h le_rfl
    exact (hdone β' h).keep
  · obtain rfl : β' = β := by omega
    exact hEβ

/-! ## The two entries -/

/-- encodeBandsP for the row bands of X: side = 0, the coefficients φ at tab.  The encodings are
right at the leaves with at most `m` symbols `P₀`. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/AllBands.lean (EncodeBandsLSpec)
def EncodeBandsLSpecP (lim : Limits) (P : Program) (c : ℕ) : Prop :=
  ∀ (p : Par) (hmL : p.m ≤ p.L) (x : BandsArgs) (aX : ℕ) (μ : ℕ → ℤ)
    (X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ) (V : ℤ),
    BandsPre lim p μ x Spec.phiFlat V → MatAt μ aX X → aX + p.N * p.D ≤ x.enc →
    (∀ i j, |X i j| ≤ V) →
    ∀ d, d + (p.L + 2) ≤ lim.depth → Meets lim P Proc.encodeBandsP d (x.vals p 0 aX p.D 1) μ
      (c * (p.nB * (encWorkP p.L p.m + bandArrayShape p) + 1)) fun _ μ' =>
        (∀ β < p.nB, SegOn p.m μ' (x.enc + β * p.T)
          (encodingL (bandArrayL (Spec.stdLayout hmL) X β))) ∧
          SameOutside μ μ' x.enc (x.zs + p.S7 - x.enc)

/-- The budget `m ≤ L` fits in a word, since the table of powers of 7 has `L + 1` cells below the
encodings. -/
theorem BandsPre.m_le_word (std : Std lim) (pre : BandsPre lim p μ x coefs V)
    (hmL : p.m ≤ p.L) : (p.m : ℤ) ≤ lim.word := by
  light_facts pre
  have := std.space_le
  omega

/-- **encodeBandsP** meets this entry, with every constant from cB + cEncP + 51 on. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/AllBands.lean
-- (encodeBandsL_entry)
theorem encodeBandsPL_entry (std : Std lim) (hP : P[Proc.encodeBandsP]? = some encodeBandsPBody)
    (hS : P[pEncStep]? = some encStepBody)
    (hE : P[Proc.encodeP]? = some (encodePBody pEncStep Proc.encodeP))
    {cB c : ℕ} (hB : BandArrayLSpec lim P cB) (hc : cB + cEncP + 51 ≤ c) :
    EncodeBandsLSpecP lim P c := by
  intro p hmL x aX μ X V pre hM hMle hV d hd
  light_facts pre
  refine .mono_const ?_ hc
  refine encodeBandsP_proc std hP pre (by omega)
    (A := fun β => Spec.arrL (bandArrayL (Spec.stdLayout hmL) X β))
    (E := fun β => encodingL (bandArrayL (Spec.stdLayout hmL) X β))
    (fun β hβ μ' hlow => ?_) fun β hβ μ' hlow hA => ?_
  · simpa using hB p hmL β aX x.mask x.dig3 x.dig4 x.arr μ' X (by omega)
      (hM.congr_below hlow hMle) (by omega) ((pre.tables.congr_below hlow).mono (by omega)) hβ
      _ (by omega)
  · exact computeEncoding_phi _ ▸ encodeP_entry leftEquiv phi (by decide) (by decide) phiFlat_spec
      std hS hE (by omega) (pre.encodePlaces hβ hlow)
      (pre.coef.congr fun i hi => hlow _ (by
        have := Spec.length_phiFlat
        omega))
      _ hA (abs_bandArrayL_le (Spec.stdLayout hmL) pre.V_nonneg hV β) pre.word
      (pre.m_le_word std hmL)

/-- encodeBandsP for the column bands of Y: side = 1, the coefficients ψ at tab. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/AllBands.lean (EncodeBandsRSpec)
def EncodeBandsRSpecP (lim : Limits) (P : Program) (c : ℕ) : Prop :=
  ∀ (p : Par) (hmL : p.m ≤ p.L) (x : BandsArgs) (aY : ℕ) (μ : ℕ → ℤ)
    (Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ) (V : ℤ),
    BandsPre lim p μ x Spec.psiFlat V → MatAt μ aY Y → aY + p.D * p.N ≤ x.enc →
    (∀ i j, |Y i j| ≤ V) →
    ∀ d, d + (p.L + 2) ≤ lim.depth → Meets lim P Proc.encodeBandsP d (x.vals p 1 aY 1 p.N) μ
      (c * (p.nB * (encWorkP p.L p.m + bandArrayShape p) + 1)) fun _ μ' =>
        (∀ β < p.nB, SegOn p.m μ' (x.enc + β * p.T)
          (encodingR (bandArrayR (Spec.stdLayout hmL) Y β))) ∧
          SameOutside μ μ' x.enc (x.zs + p.S7 - x.enc)

/-- **encodeBandsP** meets this entry, with every constant from cB + cEncP + 51 on. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/AllBands.lean
-- (encodeBandsR_entry)
theorem encodeBandsPR_entry (std : Std lim) (hP : P[Proc.encodeBandsP]? = some encodeBandsPBody)
    (hS : P[pEncStep]? = some encStepBody)
    (hE : P[Proc.encodeP]? = some (encodePBody pEncStep Proc.encodeP))
    {cB c : ℕ} (hB : BandArrayRSpec lim P cB) (hc : cB + cEncP + 51 ≤ c) :
    EncodeBandsRSpecP lim P c := by
  intro p hmL x aY μ Y V pre hM hMle hV d hd
  light_facts pre
  refine .mono_const ?_ hc
  refine encodeBandsP_proc std hP pre (by omega)
    (A := fun β => Spec.arrR (bandArrayR (Spec.stdLayout hmL) Y β))
    (E := fun β => encodingR (bandArrayR (Spec.stdLayout hmL) Y β))
    (fun β hβ μ' hlow => ?_) fun β hβ μ' hlow hA => ?_
  · simpa using hB p hmL β aY x.mask x.dig3 x.dig4 x.arr μ' Y (by omega)
      (hM.congr_below hlow hMle) (by omega) ((pre.tables.congr_below hlow).mono (by omega)) hβ
      _ (by omega)
  · exact computeEncoding_psi _ ▸ encodeP_entry rightEquiv psi (by decide) (by decide)
      psiFlat_spec std hS hE (by omega) (pre.encodePlaces hβ hlow)
      (pre.coef.congr fun i hi => hlow _ (by
        have := Spec.length_psiFlat
        omega))
      _ hA (abs_bandArrayR_le (Spec.stdLayout hmL) pre.V_nonneg hV β) pre.word
      (pre.m_le_word std hmL)

end Light.Sec2
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The shared stage: everything up to the encodings of all bands

shared(L, m, N, D, aX, aY, b0) fills the shared block of the memory map: the tables of powers, the
coefficients φ and ψ of Schönhage's identity (Section 2.2), the table of the K₀² subsets (Section
2.3.4), band, block and digits of every row, the digits of every column, the encodings of all row
bands of X and of all column bands of Y (Section 2.4.1), and the directory. Theorem 5 and the data
structure of Section 4 both start with it.

The body is a straight line of 36 statements and the 31 stores of the directory. It is cut into
three parts (sharedA, sharedB, sharedC). For each part there are two lemmas: one runs the text
(sharedA_spec, sharedB_spec, sharedC_spec), and one, about memories only, says that what the calls
have written is all there at the end, because each call writes above the areas of the calls before
it (SharedA.of_calls, SharedB.of_calls, SharedReady.of_calls). shared_entry puts the parts together:
if every callee meets its entry with the constant c, then shared runs within 12 c + 600 times
sharedShape (sharedTime_le). The places of the areas are those of Par.places, and their sizes those
of Par.sizes.
-/


namespace Light.Sec2

open ThreeSumApsp

variable {lim : Limits} {P : Program}

/-! ## The local variables -/

namespace Shared

/-- Local 0 of shared: L. -/
abbrev Levels : ℕ := 0
/-- Local 1 of shared: m. -/
abbrev Inner : ℕ := 1
/-- Local 2 of shared: N. -/
abbrev Rows : ℕ := 2
/-- Local 3 of shared: D. -/
abbrev Cols : ℕ := 3
/-- Local 4 of shared: the address of X. -/
abbrev AdrX : ℕ := 4
/-- Local 5 of shared: the address of Y. -/
abbrev AdrY : ℕ := 5
/-- Local 6 of shared: the base address b0 of the block. -/
abbrev Base : ℕ := 6
/-- Local 7 of shared: the address of the powers of 3. -/
abbrev AdrP3 : ℕ := 7
/-- Local 8 of shared: the address of the powers of 4. -/
abbrev AdrP4 : ℕ := 8
/-- Local 9 of shared: the address of the powers of 7. -/
abbrev AdrP7 : ℕ := 9
/-- Local 10 of shared: the address of the powers of 10. -/
abbrev AdrP10 : ℕ := 10
/-- Local 11 of shared: the address of the scratch row of Pascal's triangle. -/
abbrev AdrPas : ℕ := 11
/-- Local 12 of shared: the address of the coefficients φ. -/
abbrev AdrPhi : ℕ := 12
/-- Local 13 of shared: the address of the coefficients ψ. -/
abbrev AdrPsi : ℕ := 13
/-- Local 14 of shared: the address of the table of subsets. -/
abbrev AdrMask : ℕ := 14
/-- Local 15 of shared: the address of the bands of the rows. -/
abbrev AdrBand : ℕ := 15
/-- Local 16 of shared: the address of the blocks of the rows. -/
abbrev AdrBlock : ℕ := 16
/-- Local 17 of shared: the address of the base-3 digits. -/
abbrev AdrDig3 : ℕ := 17
/-- Local 18 of shared: the address of the base-4 digits. -/
abbrev AdrDig4 : ℕ := 18
/-- Local 19 of shared: the address of the encodings of the row bands. -/
abbrev AdrEncA : ℕ := 19
/-- Local 20 of shared: the address of the encodings of the column bands. -/
abbrev AdrEncB : ℕ := 20
/-- Local 21 of shared: the address of the input array of a band. -/
abbrev AdrArr : ℕ := 21
/-- Local 22 of shared: the address of the scratch array of encode. -/
abbrev AdrZs : ℕ := 22
/-- Local 23 of shared: the end of the block. -/
abbrev AdrEnd : ℕ := 23
/-- Local 24 of shared: L - m. -/
abbrev Outer : ℕ := 24
/-- Local 25 of shared: N₀. -/
abbrev BlockRows : ℕ := 25
/-- Local 26 of shared: K. -/
abbrev Subsets : ℕ := 26
/-- Local 27 of shared: K₀. -/
abbrev Root : ℕ := 27
/-- Local 28 of shared: K₀². -/
abbrev Table : ℕ := 28
/-- Local 29 of shared: the number of bands. -/
abbrev Bands : ℕ := 29
/-- Local 30 of shared: 10^L. -/
abbrev Leaves : ℕ := 30
/-- Local 31 of shared: 7^L. -/
abbrev Strings : ℕ := 31
/-- Local 32 of shared: takes the results of calls that return nothing. -/
abbrev Void : ℕ := 32

end Shared

open Shared

/-! ## The text -/

/-- Stores the locals of the list xs into the cells from b0 + i on. -/
def storeLocals : ℕ → List ℕ → Stmt
  | _, [] => .skip
  | i, x :: xs => .store (v Base +' k i) (v x) ;; storeLocals (i + 1) xs

/-- **storeLocals** writes the values of the locals to the cells from base + i on, changes nothing
else, and takes 5 steps for each. -/
theorem storeLocals_spec {d : ℕ} (hw : (lim.space : ℤ) ≤ lim.word) {base : ℕ} (loc : ℕ → ℤ)
    (hbase : loc Base = base) (xs : List ℕ) :
    ∀ (i : ℕ) (μ : ℕ → ℤ), base + i + xs.length ≤ lim.space →
      Ends lim P d (storeLocals i xs) ⟨loc, μ⟩ (5 * xs.length) fun σ' =>
        Seg σ'.mem (base + i) (xs.map loc) ∧ SameOutside μ σ'.mem (base + i) xs.length := by
  induction xs with
  | nil => exact fun i μ _ => Ends.skip ⟨Seg.nil, SameOutside.refl⟩
  | cons x xs ih =>
    intro i μ hsp
    rw [List.length_cons] at hsp ⊢
    have haddr : ((v Base +' k i).val ⟨loc, μ⟩).toNat = base + i := by simp [hbase]
    -- mem[base + i] := x
    refine Ends.storeThen ?_ (by light_side [hbase])
    rw [haddr]
    refine (ih (i + 1) _ (by omega)).mono (by simp; omega) ?_
    rintro σ' ⟨hs, hf⟩
    refine ⟨seg_cons.2 ⟨?_, by rw [Nat.add_assoc]; exact hs⟩, fun b hb => ?_⟩
    · rw [hf (base + i) (Or.inl (by omega)), Function.update_self]
      rfl
    · rw [hf b (by omega), Function.update_of_ne (by omega)]

/-- The first part of shared: the addresses of the first areas, the four tables of powers, and
L - m, N₀, 10^L, 7^L. -/
def sharedA : Stmt :=
  .set AdrP3 (v Base +' k 32) ;;
  .set AdrP4 (v AdrP3 +' (v Levels +' k 1)) ;;
  .set AdrP7 (v AdrP4 +' (v Levels +' k 1)) ;;
  .set AdrP10 (v AdrP7 +' (v Levels +' k 1)) ;;
  .set AdrPas (v AdrP10 +' (v Levels +' k 1)) ;;
  .set AdrPhi (v AdrPas +' (v Levels +' k 2)) ;;
  .set AdrPsi (v AdrPhi +' k 70) ;;
  .set AdrMask (v AdrPsi +' k 70) ;;
  .call pPow [k 3, v Levels, v AdrP3] Void ;;
  .call pPow [k 4, v Levels, v AdrP4] Void ;;
  .call pPow [k 7, v Levels, v AdrP7] Void ;;
  .call pPow [k 10, v Levels, v AdrP10] Void ;;
  .set Outer (v Levels -' v Inner) ;;
  .set BlockRows (M (v AdrP3 +' v Outer)) ;;
  .set Leaves (M (v AdrP10 +' v Levels)) ;;
  .set Strings (M (v AdrP7 +' v Levels)) ;;
  .skip

/-- The second part of shared: K, K₀, K₀², the coefficients, the table of subsets, band, block and
digits of every row, the digits of every column. -/
def sharedB : Stmt :=
  .call pBinom [v Levels, v Inner, v AdrPas] Subsets ;;
  .call pSqrt [v Subsets] Root ;;
  .set Table (v Root *' v Root) ;;
  .call pCoef [v AdrPhi] Void ;;
  .call pSubsets [v Levels, v Inner, v Table, v AdrMask] Void ;;
  .set AdrBand (v AdrMask +' v Table *' v Levels) ;;
  .set AdrBlock (v AdrBand +' v Rows) ;;
  .set AdrDig3 (v AdrBlock +' v Rows) ;;
  .call pCounters [v Rows, v Root, v BlockRows, v AdrBand] Void ;;
  .call pDigits [v Rows, k 3, v Outer, v AdrDig3] Void ;;
  .set AdrDig4 (v AdrDig3 +' v Rows *' v Outer) ;;
  .call pDigits [v Cols, k 4, v Inner, v AdrDig4] Void ;;
  .set AdrEncA (v AdrDig4 +' v Cols *' v Inner) ;;
  .skip

/-- The number of bands: 0 if there is no row, and else one more than the band of the last row. -/
def sharedBands : Stmt :=
  .ite (v Rows =' k 0) (.set Bands (k 0)) (.set Bands (M (v AdrBand +' (v Rows -' k 1)) +' k 1))

/-- The time of the first part, if every callee meets its entry with the constant c. -/
def sharedTimeA (c : ℕ) (p : Par) : ℕ := 4 * (c * (p.L + 1)) + 81

/-- The time of the second part. -/
def sharedTimeB (c : ℕ) (p : Par) : ℕ :=
  c * (p.L + 1) ^ 2 + c * (Nat.sqrt p.K + 1) + c + c * ((p.KK + 1) * (p.L + 1)) + c * (p.N + 1)
    + c * ((p.N + 1) * (p.Lo + 1)) + c * ((p.D + 1) * (p.m + 1)) + 65

/-- The locals at the start: the arguments, then zeros. -/
def sharedLoc0 (p : Par) (aX aY b0 : ℕ) : List ℤ :=
  [(p.L : ℤ), (p.m : ℤ), (p.N : ℤ), (p.D : ℤ), (aX : ℤ), (aY : ℤ), (b0 : ℤ), 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The locals after the first part; r is what the last call left in local 32. -/
def sharedLocA (p : Par) (aX aY b0 : ℕ) (r : ℤ) : List ℤ :=
  [(p.L : ℤ), (p.m : ℤ), (p.N : ℤ), (p.D : ℤ), (aX : ℤ), (aY : ℤ), (b0 : ℤ), (p.aP3 b0 : ℤ),
    (p.aP4 b0 : ℤ), (p.aP7 b0 : ℤ), (p.aP10 b0 : ℤ), (p.aPAS b0 : ℤ), (p.aPHI b0 : ℤ),
    (p.aPSI b0 : ℤ), (p.aMASK b0 : ℤ), 0, 0, 0, 0, 0, 0, 0, 0, 0, (p.Lo : ℤ), (p.N0 : ℤ), 0, 0, 0,
    0, (p.T : ℤ), (p.S7 : ℤ), r]

/-- The locals after the second part. -/
def sharedLocB (p : Par) (aX aY b0 : ℕ) (r : ℤ) : List ℤ :=
  [(p.L : ℤ), (p.m : ℤ), (p.N : ℤ), (p.D : ℤ), (aX : ℤ), (aY : ℤ), (b0 : ℤ), (p.aP3 b0 : ℤ),
    (p.aP4 b0 : ℤ), (p.aP7 b0 : ℤ), (p.aP10 b0 : ℤ), (p.aPAS b0 : ℤ), (p.aPHI b0 : ℤ),
    (p.aPSI b0 : ℤ), (p.aMASK b0 : ℤ), (p.aBAND b0 : ℤ), (p.aBLOCK b0 : ℤ), (p.aDIG3 b0 : ℤ),
    (p.aDIG4 b0 : ℤ), (p.aENCA b0 : ℤ), 0, 0, 0, 0, (p.Lo : ℤ), (p.N0 : ℤ), (p.K : ℤ), (p.K0 : ℤ),
    (p.KK : ℤ), 0, (p.T : ℤ), (p.S7 : ℤ), r]

/-- What the first part leaves in the memory. -/
structure SharedA (p : Par) (b0 : ℕ) (μ μ' : ℕ → ℤ) : Prop extends PowTables p b0 μ' where
  same : SameOutside μ μ' (p.aP3 b0) (p.aPAS b0 - p.aP3 b0)

/-- What the second part leaves in the memory. -/
structure SharedB (p : Par) (b0 : ℕ) (μ μ' : ℕ → ℤ) : Prop extends RowTables p b0 μ' where
  same : SameOutside μ μ' (p.aPAS b0) (p.aENCA b0 - p.aPAS b0)

/-- The entries of the routines that the shared stage calls, with their constants. -/
structure SharedCallees (lim : Limits) (P : Program) (c : ℕ) : Prop where
  pow : PowSpec lim P c
  binom : BinomSpec lim P c
  sqrt : SqrtSpec lim P c
  coef : CoefSpec lim P c
  subsets : SubsetsSpec lim P c
  counters : CountersSpec lim P c
  digits : DigitsSpec lim P c

/-- The assumption on the word size, in terms of `T = 10^L`. -/
theorem Par.ten_T_le {p : Par} (h10 : ((10 ^ (p.L + 1) : ℕ) : ℤ) ≤ lim.word) :
    10 * (p.T : ℤ) ≤ lim.word := by
  rw [pow_succ, Nat.mul_comm] at h10
  exact_mod_cast h10

/-- What the four calls of the first part leave in the memory: each writes its own area, above the
areas of the calls before it. -/
theorem SharedA.of_calls {p : Par} {b0 : ℕ} {μ μP3 μP4 μP7 μP10 : ℕ → ℤ}
    (sP3 : Seg μP3 (p.aP3 b0) (powList 3 (p.L + 1))) (fP3 : SameOutside μ μP3 (p.aP3 b0) (p.L + 1))
    (sP4 : Seg μP4 (p.aP4 b0) (powList 4 (p.L + 1)))
    (fP4 : SameOutside μP3 μP4 (p.aP4 b0) (p.L + 1))
    (sP7 : Seg μP7 (p.aP7 b0) (powList 7 (p.L + 1)))
    (fP7 : SameOutside μP4 μP7 (p.aP7 b0) (p.L + 1))
    (sP10 : Seg μP10 (p.aP10 b0) (powList 10 (p.L + 1)))
    (fP10 : SameOutside μP7 μP10 (p.aP10 b0) (p.L + 1)) : SharedA p b0 μ μP10 := by
  have := p.places b0
  have lp : ∀ b, (powList b (p.L + 1)).length = p.L + 1 := fun b => length_powList b _
  refine
    { p3 := sP3.keep (by light_keep [lp])
      p4 := sP4.keep (by light_keep [lp])
      p7 := sP7.keep (by light_keep [lp])
      p10 := sP10
      same := fun x hx => ?_ }
  rw [fP10 x (by omega), fP7 x (by omega), fP4 x (by omega), fP3 x (by omega)]

/-- The entry of pow, for a table of the powers b^0, …, b^L of a base b ≤ 10. -/
theorem SharedCallees.powTable {c : ℕ} (C : SharedCallees lim P c) {p : Par}
    (h10 : ((10 ^ (p.L + 1) : ℕ) : ℤ) ≤ lim.word) (b dst : ℕ) (μ : ℕ → ℤ)
    (one_le : 1 ≤ b := by omega) (le_ten : b ≤ 10 := by omega) (dst_pos : 1 ≤ dst := by omega)
    (dst_le : dst + (p.L + 1) ≤ lim.space := by omega) :
    ∀ d, d ≤ lim.depth → Meets lim P pPow d [b, p.L, dst] μ (c * (p.L + 1)) fun _ μ' =>
      Seg μ' dst (powList b (p.L + 1)) ∧ SameOutside μ μ' dst (p.L + 1) :=
  C.pow b p.L dst μ dst_pos dst_le one_le
    (le_trans (by exact_mod_cast Nat.pow_le_pow_left le_ten _) h10)

/-- **The first part of shared.** -/
theorem sharedA_spec (std : Std lim) {c : ℕ} (C : SharedCallees lim P c) {d : ℕ} {p : Par}
    (hmL : p.m ≤ p.L) {aX aY b0 : ℕ} (hd : d + (p.L + 3) ≤ lim.depth)
    (hsp : p.sharedEnd b0 ≤ lim.space) (h10 : ((10 ^ (p.L + 1) : ℕ) : ℤ) ≤ lim.word)
    (μ : ℕ → ℤ) :
    Ends lim P d sharedA ⟨frame (sharedLoc0 p aX aY b0), μ⟩ (sharedTimeA c p) fun σ' =>
      (∃ r, σ'.loc = frame (sharedLocA p aX aY b0 r)) ∧ SharedA p b0 μ σ'.mem := by
  have := std.space_le
  have := std.const_le
  have := p.places b0
  have := p.sizes hmL
  have := Par.ten_T_le h10
  unfold sharedA sharedTimeA sharedLoc0
  -- the addresses of the first eight areas
  light_set (p.aP3 b0 : ℕ)
  light_set (p.aP4 b0 : ℕ)
  light_set (p.aP7 b0 : ℕ)
  light_set (p.aP10 b0 : ℕ)
  light_set (p.aPAS b0 : ℕ)
  light_set (p.aPHI b0 : ℕ)
  light_set (p.aPSI b0 : ℕ)
  light_set (p.aMASK b0 : ℕ)
  -- the powers of 3, 4, 7 and 10
  light_call (C.powTable h10 3 (p.aP3 b0) μ) with rP3 μP3 ⟨sP3, fP3⟩
  light_call (C.powTable h10 4 (p.aP4 b0) μP3) with rP4 μP4 ⟨sP4, fP4⟩
  light_call (C.powTable h10 7 (p.aP7 b0) μP4) with rP7 μP7 ⟨sP7, fP7⟩
  light_call (C.powTable h10 10 (p.aP10 b0) μP7) with rP10 μP10 ⟨sP10, fP10⟩
  have hA := SharedA.of_calls sP3 fP3 sP4 fP4 sP7 fP7 sP10 fP10
  -- L - m, and then N₀ = 3^{L-m}, 10^L and 7^L from the tables
  have read : ∀ {b a i : ℕ}, Seg μP10 a (powList b (p.L + 1)) → i ≤ p.L →
      μP10 (a + i) = (b ^ i : ℕ) :=
    fun h hi => by rw [h.get (by rw [length_powList]; omega), getElem_powList]
  have hN0 : μP10 (p.aP3 b0 + p.Lo) = (p.N0 : ℕ) := read hA.p3 (by omega)
  have hT : μP10 (p.aP10 b0 + p.L) = (p.T : ℕ) := read hA.p10 le_rfl
  have hS7 : μP10 (p.aP7 b0 + p.L) = (p.S7 : ℕ) := read hA.p7 le_rfl
  light_set (p.Lo : ℕ)
  light_set (p.N0 : ℕ) using hN0
  light_set (p.T : ℕ) using hT
  light_set (p.S7 : ℕ) using hS7
  exact ⟨⟨rP10, rfl⟩, hA⟩

/-- What the six calls of the second part that write to the memory leave in it (the square root
writes nothing): each writes its own area, above the areas of the calls before it, so that all the
tables are there at the end. -/
theorem SharedB.of_calls {p : Par} {b0 : ℕ} {μ μPas μPhi μMask μBand μDig3 μDig4 : ℕ → ℤ}
    (fPas : SameOutside μ μPas (p.aPAS b0) (p.L + 2))
    (sphi : Seg μPhi (p.aPHI b0) Spec.phiFlat)
    (spsi : Seg μPhi (p.aPHI b0 + 70) Spec.psiFlat)
    (fPhi : SameOutside μPas μPhi (p.aPHI b0) 140)
    (smask : ∀ s < p.KK, SegB μMask (p.aMASK b0 + s * p.L) (Spec.unrank p.L p.m s))
    (fMask : SameOutside μPhi μMask (p.aMASK b0) (p.KK * p.L))
    (sband : ∀ I < p.N, μBand (p.aBAND b0 + I) = (I / (p.K0 * p.N0) : ℕ)
      ∧ μBand (p.aBAND b0 + p.N + I) = (I / p.N0 % p.K0 : ℕ))
    (fBand : SameOutside μMask μBand (p.aBAND b0) (2 * p.N))
    (sdig3 : ∀ I < p.N, SegN μDig3 (p.aDIG3 b0 + I * p.Lo) (ThreeSumApsp.digitList 3 p.Lo (I % 3 ^
        p.Lo)))
    (fDig3 : SameOutside μBand μDig3 (p.aDIG3 b0) (p.N * p.Lo))
    (sdig4 : ∀ x < p.D, SegN μDig4 (p.aDIG4 b0 + x * p.m) (ThreeSumApsp.digitList 4 p.m (x % 4 ^
        p.m)))
    (fDig4 : SameOutside μDig3 μDig4 (p.aDIG4 b0) (p.D * p.m)) : SharedB p b0 μ μDig4 := by
  have := p.places b0
  have := Spec.length_phiFlat
  have := Spec.length_psiFlat
  -- The last memory agrees with each earlier one below the area that was written next.
  have lowDig3 : ∀ x < p.aDIG4 b0, μDig4 x = μDig3 x := fun x hx => fDig4 x (Or.inl hx)
  have lowBand : ∀ x < p.aDIG3 b0, μDig4 x = μBand x := fun x hx => by
    rw [lowDig3 x (by omega), fDig3 x (Or.inl hx)]
  have lowMask : ∀ x < p.aBAND b0, μDig4 x = μMask x := fun x hx => by
    rw [lowBand x (by omega), fBand x (Or.inl hx)]
  have lowPhi : ∀ x < p.aMASK b0, μDig4 x = μPhi x := fun x hx => by
    rw [lowMask x (by omega), fMask x (Or.inl hx)]
  refine
    { phi := sphi.congr fun i hi => lowPhi _ (by omega)
      psi := spsi.congr fun i hi => lowPhi _ (by omega)
      mask := fun s hs => (smask s hs).congr fun i hi => lowMask _ ?_
      band := fun I hI => (lowBand _ (by omega)).trans (sband I hI).1
      block := fun I hI => (lowBand _ (by omega)).trans (sband I hI).2
      dig3 := fun I hI => (sdig3 I hI).congr fun i hi => lowDig3 _ ?_
      dig4 := fun x hx => ?_
      same := fun x hx => ?_ }
  · rw [List.length_map, Spec.length_unrank] at hi
    have := Nat.mul_add_lt_mul hs hi
    omega
  · have hi' : i < p.Lo := by simpa [ThreeSumApsp.digitList] using hi
    have := Nat.mul_add_lt_mul hI hi'
    omega
  · have h := sdig4 x hx
    rwa [Nat.mod_eq_of_lt (show x < 4 ^ p.m from hx)] at h
  · show μDig4 x = μ x
    rw [fDig4 x (by omega), fDig3 x (by omega), fBand x (by omega), fMask x (by omega),
      fPhi x (by omega), fPas x (by omega)]

/-- **The second part of shared.** -/
theorem sharedB_spec (std : Std lim) {c : ℕ} (C : SharedCallees lim P c) {d : ℕ} {p : Par}
    (hmL : p.m ≤ p.L) {aX aY b0 : ℕ} (hd : d + (p.L + 3) ≤ lim.depth)
    (hsp : p.sharedEnd b0 ≤ lim.space) (h10 : ((10 ^ (p.L + 1) : ℕ) : ℤ) ≤ lim.word)
    (μ : ℕ → ℤ) (r0 : ℤ) :
    Ends lim P d sharedB ⟨frame (sharedLocA p aX aY b0 r0), μ⟩ (sharedTimeB c p) fun σ' =>
      (∃ r, σ'.loc = frame (sharedLocB p aX aY b0 r)) ∧ SharedB p b0 μ σ'.mem := by
  have := std.space_le
  have := std.const_le
  have := p.places b0
  have := p.sizes hmL
  have : p.KK = p.K0 * p.K0 := rfl
  have := Par.ten_T_le h10
  unfold sharedB sharedTimeB sharedLocA
  -- K := binom(L, m)
  light_call (C.binom p.L p.m (p.aPAS b0) μ (by omega) hmL
    (le_trans (by exact_mod_cast p.two_pow_le_T) (by omega : (p.T : ℤ) ≤ lim.word)))
    with r μPas ⟨hr, fPas⟩
  obtain rfl : r = (p.K : ℕ) := hr
  -- K₀ := ⌊√K⌋ and K₀²
  light_call (C.sqrt p.K μPas (by push_cast; omega)) with r μPas' ⟨hr, hμ⟩
  obtain rfl : r = (p.K0 : ℕ) := hr
  obtain rfl : μPas = μPas' := hμ.symm
  light_set (p.KK : ℕ)
  -- the coefficients and the table of subsets
  light_call (C.coef (p.aPHI b0) μPas (by omega)) with rPhi μPhi ⟨sphi, spsi, fPhi⟩
  light_call (C.subsets p.L p.m p.KK (p.aMASK b0) μPhi (by omega) hmL p.KK_le_K
    (by push_cast; omega)) with rMask μMask ⟨smask, fMask⟩
  -- band and block of every row
  light_set (p.aBAND b0 : ℕ)
  light_set (p.aBLOCK b0 : ℕ)
  light_set (p.aDIG3 b0 : ℕ)
  light_call (C.counters p.N p.K0 p.N0 (p.aBAND b0) μMask (by omega) (by omega)
    (by omega) (by push_cast; omega)) with rBand μBand ⟨sband, fBand⟩
  -- the digits of every row and of every column
  light_call (C.digits p.N 3 p.Lo (p.aDIG3 b0) μBand (by omega) (by norm_num)
    (by push_cast; omega) (by omega)) with rDig3 μDig3 ⟨sdig3, fDig3⟩
  light_set (p.aDIG4 b0 : ℕ)
  light_call (C.digits p.D 4 p.m (p.aDIG4 b0) μDig3 (by omega) (by norm_num)
    (by push_cast; omega) (by omega)) with rDig4 μDig4 ⟨sdig4, fDig4⟩
  light_set (p.aENCA b0 : ℕ)
  exact ⟨⟨rDig4, rfl⟩,
    .of_calls fPas sphi spsi fPhi smask fMask sband fBand sdig3 fDig3 sdig4 fDig4⟩

/-- What bandArray reads of the tables. -/
theorem SharedTables.bandTables {p : Par} {b0 : ℕ} {μ : ℕ → ℤ} (h : SharedTables p b0 μ) :
    BandTables p μ (p.aMASK b0) (p.aDIG3 b0) (p.aDIG4 b0) (p.aENCA b0) := by
  have := p.places b0
  exact ⟨h.mask, h.dig3, h.dig4, by omega, by omega, by omega⟩

/-- The addresses that the shared stage hands to encodeBands: the coefficients stand at tab, and the
encodings are written from enc on. -/
@[simp] def Par.bandsArgs (p : Par) (b0 tab enc : ℕ) : BandsArgs where
  mask := p.aMASK b0
  dig3 := p.aDIG3 b0
  dig4 := p.aDIG4 b0
  arr := p.aARR b0
  zs := p.aZS b0
  tab := tab
  p7 := p.aP7 b0
  p10 := p.aP10 b0
  enc := enc

/-- What encodeBands assumes holds once the tables are there, for either of the two areas enc of
encodings. -/
theorem SharedTables.bandsPre {p : Par} {b0 tab enc : ℕ} {μ : ℕ → ℤ} {coefs : List ℤ} {V : ℤ}
    (h : SharedTables p b0 μ) (hsp : p.sharedEnd b0 ≤ lim.space) (hV0 : 0 ≤ V)
    (hVB : 7 ^ (p.L + 1) * V ≤ lim.word) (coef : Seg μ tab coefs) (coef_le : tab + 70 ≤ enc)
    (le_enc : p.aENCA b0 ≤ enc) (enc_le : enc + p.nB * p.T ≤ p.aARR b0) :
    BandsPre lim p μ (p.bandsArgs b0 tab enc) coefs V := by
  have := p.places b0
  exact
    { tables := h.bandTables.mono le_enc
      coef := coef
      coef_le := coef_le
      p7 := h.p7
      p7_le := show p.aP7 b0 + (p.L + 1) ≤ enc by omega
      p10 := h.p10
      p10_le := show p.aP10 b0 + (p.L + 1) ≤ enc by omega
      enc_le := enc_le
      arr_le := show p.aARR b0 + p.S7 ≤ p.aZS b0 by omega
      zs_le := show p.aZS b0 + p.S7 ≤ lim.space by omega
      V_nonneg := hV0
      word := hVB }

/-- The number of bands, from the band of the last row. -/
theorem nB_eq (p : Par) (hmL : p.m ≤ p.L) :
    (p.N = 0 → p.nB = 0) ∧ (0 < p.N → p.nB = (p.N - 1) / (p.K0 * p.N0) + 1) := by
  have hb : 0 < p.K0 * p.N0 := Nat.mul_pos (K0_pos hmL) (N0_pos _ _)
  have e : p.nB = (p.N + p.K0 * p.N0 - 1) / (p.K0 * p.N0) := rfl
  constructor
  · intro h
    rw [e, h, Nat.zero_add]
    exact Nat.div_eq_of_lt (by omega)
  · intro h
    rw [e, ← Nat.add_div_right _ hb]
    congr 1
    omega

/-- **The number of bands**: 0 if there is no row, and else one more than the band of the last
row. -/
theorem sharedBands_spec (std : Std lim) {d : ℕ} {p : Par} (hmL : p.m ≤ p.L) {aX aY b0 : ℕ}
    (hsp : p.sharedEnd b0 ≤ lim.space) (μ : ℕ → ℤ) (r0 : ℤ) (tb : SharedTables p b0 μ) :
    Ends lim P d sharedBands ⟨frame (sharedLocB p aX aY b0 r0), μ⟩ 13 fun σ' =>
      σ' = ⟨frame (setLocal (sharedLocB p aX aY b0 r0) Bands (p.nB : ℕ)), μ⟩ := by
  have := std.space_le
  have := std.const_le
  have := p.places b0
  obtain ⟨hnB0, hnB1⟩ := nB_eq p hmL
  unfold sharedBands sharedLocB
  refine Ends.iteLast (fun hN => ?_) (fun hN => ?_)
  · -- nB := 0
    have hNzero : p.N = 0 := by simpa using hN
    exact Ends.setTo (p.nB : ℕ) rfl (by simp [hnB0 hNzero]; omega)
  · -- nB := mem[BAND + (N - 1)] + 1
    have hNpos : 0 < p.N := Nat.pos_of_ne_zero (by simpa using hN)
    have hlast := tb.band (p.N - 1) (by omega)
    have haddr : ((p.aBAND b0 : ℤ) + ((p.N : ℤ) - 1)).toNat = p.aBAND b0 + (p.N - 1) := by omega
    have hle : (p.N - 1) / (p.K0 * p.N0) ≤ p.N := (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
    have hnB := hnB1 hNpos
    generalize (p.N - 1) / (p.K0 * p.N0) = q at hlast hle hnB
    exact Ends.setTo (p.nB : ℕ) rfl (by light_side [haddr, hlast, hnB])

/-- The tables of the first part are still there after the second part. -/
theorem SharedTables.of_parts {p : Par} {b0 : ℕ} {μ μA μB : ℕ → ℤ} (hA : SharedA p b0 μ μA)
    (hB : SharedB p b0 μA μB) : SharedTables p b0 μB := by
  have := p.places b0
  have lp : ∀ b, (powList b (p.L + 1)).length = p.L + 1 := fun b => length_powList b _
  exact
    { hB.toRowTables with
      p3 := hA.p3.keep (by light_keep [hB.same, lp])
      p4 := hA.p4.keep (by light_keep [hB.same, lp])
      p7 := hA.p7.keep (by light_keep [hB.same, lp])
      p10 := hA.p10.keep (by light_keep [hB.same, lp]) }



open ImprovedExponents



/-! ## The text -/

/-- The third part of the pruned shared stage: the number of bands, the last addresses, the
encodings of all bands with the pruned encoder, and the directory. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/SharedStage.lean (sharedC)
def sharedCP : Stmt :=
  sharedBands ;;
  .set AdrEncB (v AdrEncA +' v Bands *' v Leaves) ;;
  .set AdrArr (v AdrEncB +' v Bands *' v Leaves) ;;
  .set AdrZs (v AdrArr +' v Strings) ;;
  .set AdrEnd (v AdrZs +' v Strings) ;;
  .call Proc.encodeBandsP [v Levels, v Inner, v Rows, v Cols, v Root, v BlockRows, v Strings,
    v Leaves, v Bands, k 0, v AdrX, v Cols, k 1, v AdrMask, v AdrDig3, v AdrDig4, v AdrArr, v AdrZs,
    v AdrPhi, v AdrP7, v AdrP10, v AdrEncA] Void ;;
  .call Proc.encodeBandsP [v Levels, v Inner, v Rows, v Cols, v Root, v BlockRows, v Strings,
    v Leaves, v Bands, k 1, v AdrY, k 1, v Rows, v AdrMask, v AdrDig3, v AdrDig4, v AdrArr, v AdrZs,
    v AdrPsi, v AdrP7, v AdrP10, v AdrEncB] Void ;;
  storeLocals 0 [Levels, Inner, Rows, Cols, Outer, BlockRows, Subsets, Root, Table, Bands, Leaves,
    Strings, AdrX, AdrY, AdrP3, AdrP4, AdrP7, AdrP10, AdrPas, AdrPhi, AdrPsi, AdrMask, AdrBand,
    AdrBlock, AdrDig3, AdrDig4, AdrEncA, AdrEncB, AdrArr, AdrZs, AdrEnd]

/-- sharedP(L, m, N, D, aX, aY, b0): upstream's shared stage with the pruned encoder. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/SharedStage.lean (sharedBody)
def sharedPBody : Stmt := sharedA ;; sharedB ;; sharedCP

def sharedTimeCP (c : ℕ) (p : Par) : ℕ :=
  2 * (c * (p.nB * (encWorkP p.L p.m + bandArrayShape p) + 1)) + 236

theorem sharedCP_spec (std : Std lim) {c : ℕ} (bandsLP : EncodeBandsLSpecP lim P c)
    (bandsRP : EncodeBandsRSpecP lim P c) {d : ℕ} {p : Par}
    (hmL : p.m ≤ p.L) {aX aY b0 : ℕ} (hd : d + (p.L + 3) ≤ lim.depth)
    (hsp : p.sharedEnd b0 ≤ lim.space) (h10 : ((10 ^ (p.L + 1) : ℕ) : ℤ) ≤ lim.word)
    (μ : ℕ → ℤ) (r0 : ℤ) {X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ}
    {Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ} {V : ℤ} (hX : MatAt μ aX X)
    (hY : MatAt μ aY Y) (hXle : aX + p.N * p.D ≤ b0) (hYle : aY + p.D * p.N ≤ b0) (hV0 : 0 ≤ V)
    (hVX : ∀ i j, |X i j| ≤ V) (hVY : ∀ i j, |Y i j| ≤ V) (hVB : 7 ^ (p.L + 1) * V ≤ lim.word)
    (tb : SharedTables p b0 μ) :
    Ends lim P d sharedCP ⟨frame (sharedLocB p aX aY b0 r0), μ⟩ (sharedTimeCP c p) fun σ' =>
      SharedReadyP p hmL aX aY b0 X Y σ'.mem ∧ SameOutside μ σ'.mem b0 (p.sharedEnd b0 - b0) := by
  have hw := std.space_le
  have := std.const_le
  have := p.places b0
  have := p.sizes hmL
  have := Par.ten_T_le h10
  unfold sharedCP sharedTimeCP
  refine Ends.next 13 ((sharedBands_spec std hmL hsp μ r0 tb).mono le_rfl ?_)
  rintro _ rfl
  unfold sharedLocB
  light_set (p.aENCB b0 : ℕ)
  light_set (p.aARR b0 : ℕ)
  light_set (p.aZS b0 : ℕ)
  light_set (p.sharedEnd b0 : ℕ)
  have preA : BandsPre lim p μ (p.bandsArgs b0 (p.aPHI b0) (p.aENCA b0)) Spec.phiFlat V :=
    tb.bandsPre hsp hV0 hVB tb.phi (coef_le := by omega) (le_enc := le_rfl) (enc_le := by omega)
  light_call (bandsLP p hmL _ aX μ X V preA hX
    (hXle.trans (show b0 ≤ p.aENCA b0 by omega)) hVX) with rEncA μEncA ⟨sA, fEncA⟩
  have lowEncA : ∀ x < p.aENCA b0, μEncA x = μ x := fun x hx => fEncA x (Or.inl hx)
  have tbEncA : SharedTables p b0 μEncA := tb.congr fun x _ hx => lowEncA x hx
  have hYle' : aY + ThreeSumApsp.D p.m * p.N ≤ p.aENCA b0 := le_trans hYle (by omega)
  have preB : BandsPre lim p μEncA (p.bandsArgs b0 (p.aPSI b0) (p.aENCB b0)) Spec.psiFlat V :=
    tbEncA.bandsPre hsp hV0 hVB tbEncA.psi (coef_le := by omega) (le_enc := by omega)
      (enc_le := by omega)
  light_call (bandsRP p hmL _ aY μEncA Y V preB (hY.congr_below lowEncA hYle')
    (hYle.trans (show b0 ≤ p.aENCB b0 by omega)) hVY) with rEncB μEncB ⟨sB, fEncB⟩
  refine (storeLocals_spec hw (base := b0) _ (by simp) _ 0 μEncB (by simp; omega)).mono
    (by simp; omega) ?_
  rintro ⟨_, μDir⟩ ⟨sdir, fDir⟩
  dsimp only [Par.bandsArgs] at sA sB sdir fDir ⊢
  change SameOutside μ μEncA (p.aENCA b0) (p.sharedEnd b0 - p.aENCA b0) at fEncA
  change SameOutside μEncA μEncB (p.aENCB b0) (p.sharedEnd b0 - p.aENCB b0) at fEncB
  replace fDir : SameOutside μEncB μDir b0 31 := by simpa using fDir
  have above : ∀ x, p.aP3 b0 ≤ x → μDir x = μEncB x := fun x hx => fDir x (Or.inr (by omega))
  have tbDir : SharedTables p b0 μDir := tb.congr fun x h1 h2 => by
    rw [above x h1, fEncB x (Or.inl (by omega)), fEncA x (Or.inl h2)]
  refine ⟨{ tbDir with
    dir := by simpa [SegN, dirList, Par.aDIR] using sdir
    encA := fun β hβ => (sA β hβ).congr fun i hi => by
      have := Nat.mul_add_lt_mul hβ (show i < p.T from hi)
      rw [above _ (by omega), fEncB _ (Or.inl (by omega))]
    encB := fun β hβ => (sB β hβ).congr fun i hi => above _ (by omega) }, fun x hx => ?_⟩
  rw [fDir x (by omega), fEncB x (by omega), fEncA x (by omega)]

theorem sharedTimeP_le (c : ℕ) (p : Par) :
    sharedTimeA c p + (sharedTimeB c p + sharedTimeCP c p) ≤ (12 * c + 600) * sharedShapeP p := by
  unfold sharedTimeA sharedTimeB sharedTimeCP sharedShapeP
  have hL : p.L + 1 ≤ (p.L + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hN : p.N + 1 ≤ (p.N + 1) * (p.Lo + 1) := Nat.le_mul_of_pos_right _ (by omega)
  generalize (p.L + 1) ^ 2 = s, Nat.sqrt p.K + 1 = q, (p.KK + 1) * (p.L + 1) = u,
    (p.N + 1) * (p.Lo + 1) = w, (p.D + 1) * (p.m + 1) = x,
    p.nB * (encWorkP p.L p.m + bandArrayShape p) = y at hL hN ⊢
  have := Nat.mul_le_mul_left c hL
  have := Nat.mul_le_mul_left c hN
  have := Nat.mul_le_mul_left c (show 1 ≤ s by omega)
  have : c * (y + 1) = c * y + c := Nat.mul_succ c y
  have : (12 * c + 600) * (s + q + u + w + x + y) = 12 * (c * s) + 12 * (c * q)
      + 12 * (c * u) + 12 * (c * w) + 12 * (c * x) + 12 * (c * y)
      + 600 * (s + q + u + w + x + y) := by ring
  omega

theorem sharedP_entry (std : Std lim) (hP : P[Proc.sharedP]? = some sharedPBody)
    (hPB : P[Proc.encodeBandsP]? = some encodeBandsPBody)
    (hBA : P[pBandArray]? = some bandArrayBody) (hS : P[pEncStep]? = some encStepBody)
    (hE : P[Proc.encodeP]? = some (encodePBody pEncStep Proc.encodeP))
    {c : ℕ} (C : SharedCallees lim P c) (hcb : cBandArray + cEncP + 51 ≤ c)
    {c' : ℕ} (hc : 12 * c + 600 ≤ c') : SharedSpecP lim P c' := by
  intro p hmL aX aY b0 μ X Y V pre d hd
  have := p.places b0
  refine .mono_const (.of_body hP (Ends.mono ?_ (sharedTimeP_le c p) fun _ h => h)) hc
  rw [← frame_append_zeros [(p.L : ℤ), p.m, p.N, p.D, aX, aY, b0] 26]
  unfold sharedPBody
  light_piece (sharedA_spec std C hmL hd pre.space pre.ten μ)
    with ⟨locA, μA⟩ ⟨⟨rA, hlocA⟩, hA⟩
  obtain rfl : locA = _ := hlocA
  dsimp only at hA
  light_piece (sharedB_spec std C hmL hd pre.space pre.ten μA rA)
    with ⟨locB, μB⟩ ⟨⟨rB, hlocB⟩, hB⟩
  obtain rfl : locB = _ := hlocB
  dsimp only at hB
  have low : ∀ x < b0, μB x = μ x := fun x hx => by
    rw [hB.same x (Or.inl (by omega)), hA.same x (Or.inl (by omega))]
  have : 7 ^ (p.L + 1) * max V 0 ≤ lim.word := by
    rcases le_total V 0 with h | h
    · rw [max_eq_right h, mul_zero]
      exact le_trans (by norm_num) std.const_le
    · rw [max_eq_left h]
      exact pre.seven
  refine (sharedCP_spec std
    (encodeBandsPL_entry std hPB hS hE (bandArrayL_entry std hBA) hcb)
    (encodeBandsPR_entry std hPB hS hE (bandArrayR_entry std hBA) hcb)
    hmL hd pre.space pre.ten μB rB (pre.matX.congr_below low pre.belowX)
    (pre.matY.congr_below low pre.belowY) pre.belowX pre.belowY (le_max_right V 0)
    (fun i j => (pre.absX i j).trans (le_max_left _ _))
    (fun i j => (pre.absY i j).trans (le_max_left _ _)) this (.of_parts hA hB)).mono (by omega) ?_
  rintro σ' ⟨hR, hf⟩
  exact ⟨hR, fun x hx => by rw [hf x hx, hB.same x (by omega), hA.same x (by omega)]⟩

end Light.Sec2
end
