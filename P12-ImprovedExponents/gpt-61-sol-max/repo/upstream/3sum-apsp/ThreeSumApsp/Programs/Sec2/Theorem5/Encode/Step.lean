/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Util.Types
public import Mathlib.Tactic
public import ThreeSumApsp.Lang.Lib.Pass
public import ThreeSumApsp.Lang.Tactics

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

@[expose] public section

namespace Light.Sec2

open Finset


/-- One summand: Acc := Acc + tab[7 lam + s] · src[s n + j]. -/
def encStepAdd : Stmt :=
  .set 6
    (v 6 +' M (v 4 +' k 7 *' v 3 +' v 7) *' M (v 0 +' v 7 *' v 2 +' v 5))

/-- The sum over s < 7 of tab[7 lam + s] · src[s n + j]. -/
def encStepSum : Stmt := .for 7 (k 7) encStepAdd

/-- One cell of dst. -/
def encStepCell := .set 6 (k 0) ;; encStepSum ;; .store (v 1 +' v 5) (v 6)

/-- encStep(src, dst, n, lam, tab): for j < n, dst[j] := ∑_{s < 7} tab[7 lam + s] · src[s n + j]. -/
def encStepBody : Stmt := .for 5 (v 2) encStepCell

/-! ## The sums -/

/-- The first s summands of what encStep writes at dst + j. -/
def encStepVal (μ : Light.Memory) src lam tab n j s :=
  ∑ i ∈ range s, μ (tab + 7 * lam + i) * μ (src + i * n + j)

/-- What encStep writes at dst + c. -/
abbrev encStepOut μ src lam tab n := fun c => encStepVal μ src lam tab n c 7

/-- One more summand. -/
private theorem encStepVal_succ μ src lam tab n j s :
    encStepVal μ src lam tab n j (s + 1)
      = encStepVal μ src lam tab n j s + μ (tab + 7 * lam + s) * μ (src + s * n + j) :=
  Finset.sum_range_succ ..

/-- The hypotheses of `encStep`: the seven coefficients and the array at `src` lie below the `n`
cells at `dst`, which lie in the memory; the coefficients are -1, 0 or 1, the numbers are at most
`V` in absolute value, and `7 V` fits in a word. -/
structure EncStepPre (lim : Limits) (μ : Light.Memory) (src dst n lam tab : ℕ) (V : ℤ) : Prop where
  std : Std lim
  tab_le : tab + 7 * lam + 7 ≤ dst
  src_le : src + 7 * n ≤ dst
  dst_le : dst + n ≤ lim.space
  coef : ∀ i < 7, -1 ≤ μ (tab + 7 * lam + i) ∧ μ (tab + 7 * lam + i) ≤ 1
  vals : ∀ i < 7 * n, -V ≤ μ (src + i) ∧ μ (src + i) ≤ V
  word_bound : 7 * V ≤ lim.word

variable {lim : Limits} {P : Program} {d : ℕ} {μ μ' : Light.Memory} {src dst n lam tab j : ℕ} {V : ℤ}

/-- The product of a coefficient in {-1, 0, 1} and a number of absolute value at most `V`. -/
theorem enc_coef_mul_bound {x y V} (hx : -1 ≤ x ∧ x ≤ 1) (hy : -V ≤ y ∧ y ≤ V) :
    -V ≤ x * y ∧ x * y ≤ V := by

  rcases (by omega : x = -1 ∨ x = 0 ∨ x = 1) with rfl | rfl | rfl <;> constructor <;> omega

/-- A sum of `s` numbers of absolute value at most `V` is at most `s V` in absolute value. -/
theorem enc_sum_bound {f : Light.Memory} {V} s (h : ∀ i < s, -V ≤ f i ∧ f i ≤ V) :
    -(s * V) ≤ ∑ i ∈ range s, f i ∧ ∑ i ∈ range s, f i ≤ s * V := by
  induction s with
  | zero => simp
  | succ s ih =>
    have  := ih fun i hi => h i (by omega)
    have  := h s (by omega)
    rw [Finset.sum_range_succ, Nat.cast_succ, add_mul, one_mul]
    omega

namespace EncStepPre

/-- One summand is at most `V` in absolute value. -/
private def summand_bounds (pre : EncStepPre lim μ src dst n lam tab V) hj {s}
     hs := by
  have hval := pre.vals (s * n + j) (Nat.mul_add_lt_mul hs hj)
  rw [← Nat.add_assoc] at hval
  exact enc_coef_mul_bound (pre.coef s hs) hval

variable (pre : EncStepPre lim μ src dst n lam tab V)

include pre in
/-- The sum of `s` summands is at most `s V` in absolute value. -/
private theorem val_bounds  (hj : j < n) {s}
    (hs : s ≤ 7) :
    -(s * V) ≤ encStepVal μ src lam tab n j s ∧ encStepVal μ src lam tab n j s ≤ s * V :=
  enc_sum_bound s fun _ hi => pre.summand_bounds hj (by omega)

include pre in
/-- The hypotheses still hold when cells of `dst` have been written. -/
theorem keep  (same : SameOutside μ μ' dst n) :
    EncStepPre lim μ' src dst n lam tab V := by
  light_facts pre
  exact { pre with
    coef := fun i hi => by rw [same _ (by omega)]; exact pre.coef i hi
    vals := fun i hi => by rw [same _ (by omega)]; exact pre.vals i hi }

include pre in
/-- The sums do not change when cells of `dst` are written. -/
private theorem val_congr
    (same : SameOutside μ μ' dst n) (hj : j < n) :
    encStepVal μ' src lam tab n j 7 = encStepVal μ src lam tab n j 7 := by
  light_facts pre
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi7 := Finset.mem_range.mp hi
  have  := Nat.mul_add_lt_mul hi7 hj
  rw [same _ (by omega), same _ (by omega)]

end EncStepPre

/-! ## The program -/

variable {T : ℕ} {Q : State → Prop}

/-- **One sum**: the loop over the seven summands leaves the sum for cell j in the local Acc. -/
theorem encStepSum_spec (pre : EncStepPre lim μ src dst n lam tab V) (hj : j < n) {s₀}
    (done : Q ⟨frame [src, dst, n, lam, tab, j, encStepVal μ src lam tab n j 7, 7], μ⟩)
    (hT : 202 ≤ T) :
    Ends lim P d encStepSum ⟨frame [src, dst, n, lam, tab, j, 0, s₀], μ⟩ T Q := by
  light_facts pre pre.std
  -- for Var < 7
  refine Ends.for (fun s σ => σ =
      ⟨frame [src, dst, n, lam, tab, j, encStepVal μ src lam tab n j s, s], μ⟩) 7
    encStepAdd.blockCost ?start ?round ?done ?bound (by omega) (by simp [encStepAdd]; omega)
  case start => simp [update_frame_setLocal, encStepVal]
  case done => exact fun _ _ h => h ▸ done
  case bound => light_side
  case round =>
    rintro s _ hs - rfl
    -- The two cells that are read, and the sizes of the numbers.
    have  := Nat.mul_add_lt_mul hs hj
    have  := pre.summand_bounds hj hs
    have hnext := pre.val_bounds hj (show s + 1 ≤ 7 by omega)
    have  : ((s + 1 : ℕ) : ℤ) * V ≤ 7 * V := by
      gcongr <;> first | assumption | positivity | omega


    unfold encStepAdd
    refine Ends.setTo (encStepVal μ src lam tab n j (s + 1)) ⟨rfl, ?_⟩ ?_
    · simp [update_frame_setLocal]
    · rw [encStepVal_succ] at hnext ⊢
      simp [Limits.Addr, abs_le, (by omega : ((tab : ℤ) + 7 * lam + s).toNat = tab + 7 * lam + s), (by
        omega
       : ((src : ℤ) + s * n + j).toNat = src + s * n + j), -abs_mul]
      omega

/-- A bound on the number of steps of `encStep` on `n` cells. -/
def tEncStep n := 217 * n + 6

/-- **encStep** writes `∑_{s < 7} tab[7 lam + s] · src[s n + j]` to `dst[j]` for all `j < n` and
changes nothing else. -/
theorem encStep_meets {p} (hp : P[p]? = some encStepBody)
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
    aesop (add safe apply [wrote_done, sameOutside_wrote])
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

end Light.Sec2
