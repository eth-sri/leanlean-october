module

public import GradedNear.Cert.Access

/-!
# Soundness of the row relaxations

On a box interval `[a, b]` (ticks) containing `τ·TS`, a near row at the actual threshold `τ`
implies the first-order linear relaxation (case 2), and one of the two tangent relaxations
(cases 0, 1): the row's left side plus `τ²/(d/S)` is convex in `τ`, so its tangent line at the
midpoint is below it, and an affine function that is `≤ 1` somewhere on `[a, b]` is `≤ 1` at an
endpoint. Integer costs are floored and budgets ceiled, in the safe direction.

Both relaxations need the family counts `n ≥ 0` (part of `wellFormed`): the first-order budget
evaluates the family terms at the upper threshold `b`, and the tangent budget replaces each family
term by its tangent line. Without `n ≥ 0` both statements are false. The hypothesis
`k < L.rows.length` is not used: out-of-range rows default to `⟨1, []⟩`. Helpers are in
`GradedNear.Cert.RelaxAux`.
-/

@[expose] public section

namespace GradedNear.Cert

/-- The relaxed linear constraint of row `k` for case `c` on the box interval `[a, b]`. -/
def RelaxHolds (L : Leaf) (x : Fin L.cols.length → ℝ) (k : ℕ) (a b : ℤ) (c : ℕ) : Prop :=
  ∑ j, ((colCost (L.feature j k) (L.diag j k) a b c : ℤ) : ℝ) *
      x j ≤ ((rowBudget (L.row k) a b c : ℤ) : ℝ)

namespace RelaxAux

/-! ### Constants and rounding -/

lemma S_pos_int : (0 : ℤ) < S := by decide

lemma S_pos : (0 : ℝ) < S := by exact_mod_cast S_pos_int

lemma TS_pos : (0 : ℝ) < TS := by norm_num [TS]

/-- Floor division by a positive integer is at most real division. -/
lemma cast_ediv_le (a b : ℤ) (hb : 0 < b) : ((a / b : ℤ) : ℝ) ≤ (a : ℝ) / b := by
  rw [le_div_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast Int.ediv_mul_le a (ne_of_gt hb)

/-! ### Well-formed rows (including the out-of-range defaults) -/

lemma getD_prop {α : Type*} {p : α → Prop} {xs : List α} {d : α} (hd : p d)
    (h : ∀ a ∈ xs, p a) (k : ℕ) : p (xs.getD k d) := by
  rw [List.getD_eq_getElem?_getD]; cases e : xs[k]? with
  | none => exact hd
  | some a => exact h a (List.mem_of_getElem? e)

variable {L : Leaf} (hwf : wellFormed L = true)
include hwf in
lemma wf_colD (j : Fin L.cols.length) (k : ℕ) : 0 < L.diag j k := by
  simp [wellFormed] at hwf
  exact getD_prop zero_lt_one (hwf.1 _ (List.get_mem L.cols j)).2 k

include hwf in
lemma wf_row (k : ℕ) :
    0 < (L.row k).d ∧ ∀ t ∈ (L.row k).fam, 0 ≤ t.1 ∧ 0 < t.2.2 := by
  simp [wellFormed] at hwf
  apply getD_prop (p := fun r : RowHead => 0 < r.d ∧ ∀ t ∈ r.fam, 0 ≤ t.1 ∧ 0 < t.2.2)
  · simp
  · simpa using hwf.2

open Finset

/-! ### A row in the integer input coordinates

Multiply the inequality by `S` and measure the threshold in feature units. A
squared hinge then divides by its input diagonal, with no scales left in the
row. The affine minorant is in these same units.
-/

def loss {R : Type*} [LinearOrder R] [Ring R] (v t : R) := (max 0 (v-t))^2
def tgt {R : Type*} [LinearOrder R] [Ring R] (v m s : R) := loss v m - 2*max 0 (v-m)*s

lemma tangent_ineq (w m t : ℝ) : tgt w m (t-m) ≤ loss w t := by
  unfold tgt loss
  rcases le_total (w-m) 0 with h | h
  · aesop
  · rw [max_eq_right h]
    nlinarith [sq_nonneg (max 0 (w-t) - (w-m)), mul_le_mul_of_nonneg_left (le_max_right 0 (w-t)) h]

variable (L) (x : Fin L.cols.length → ℝ) (k : ℕ)
local notation "row" => L.row k

noncomputable abbrev cols (f : ℝ → ℝ) := ∑ j, x j * f (L.feature j k) / L.diag j k
noncomputable abbrev fam (r : RowHead) (f : ℝ → ℝ) := ∑ i : Fin r.fam.length,
  ((r.fam.get i).1:ℝ) * f (r.fam.get i).2.1 / (r.fam.get i).2.2

variable {a b : ℤ} {τ : ℝ} (hx : ∀ j, 0 ≤ x j)
local notation "t" => ((S:ℝ)*τ)

/-- Sum of the scalar tangents, including the radius term. -/
noncomputable abbrev tangentRow (m s : ℝ) :=
  cols L x k (tgt · m s) + fam row (tgt · m s) + (m^2 + 2*m*s)/(row).d

lemma tangentRow_affine (m s : ℝ) : let R := tangentRow L x k m; R s = R 0 + (R 1-R 0)*s := by
  have e n d w (z : ℝ) : n*tgt w m z/d = n*loss w m/d - (n*2*max 0 (w-m)/d)*z := by unfold tgt; ring
  simp only [tangentRow, cols, fam, e, sum_sub_distrib, ← sum_mul]; ring

include hwf hx in
lemma tangentRow_le (m z : ℝ) : tangentRow L x k m (z-m) ≤ cols L x k (loss · z) + fam row (loss · z) + z^2/(row).d := by
  obtain ⟨hd, hf⟩ := wf_row hwf k
  refine add_le_add (add_le_add (sum_le_sum fun j _ => ?_) (sum_le_sum fun i _ => ?_)) ?_
  · have := wf_colD hwf j k
    gcongr <;> first | apply hx | exact tangent_ineq ..
  · obtain ⟨hn,hD⟩ := hf _ (List.get_mem _ i)
    gcongr; exact tangent_ineq ..
  · gcongr; nlinarith [sq_nonneg (z-m)]

include hx hwf in
lemma relax_of_minorant (c : ℕ) (f : ℝ → ℝ) {r : ℝ}
    (h : cols L x k f + fam row f + r ≤ S)
    (cost : ∀ v D : ℤ, 0 < D → (colCost v D a b c : ℝ) ≤ f v / D)
    (budget : S - fam row f - r ≤ (rowBudget row a b c : ℝ)) : RelaxHolds L x k a b c := by
  apply le_trans (b := cols L x k f) _ (by linarith)
  refine sum_le_sum fun j _ => (mul_le_mul_of_nonneg_right (cost _ _ (wf_colD hwf j k)) (hx j)).trans_eq (by ring)

/-! ### Safe rounding -/

abbrev shift {R : Type*} [Neg R] (c : ℕ) (h : R) := if c = 0 then -h else h
abbrev mid (a b : ℤ) := (a+b)*HS
abbrev hw (a b : ℤ) := (b-a)*HS

lemma tangentCost_le (v m h : ℤ) (c : ℕ) : tangentCost v m h c * S ≤ tgt v (m*HS) (shift c (h*HS)) := by
  by_cases hx : v-m*HS ≤ 0
  · simp [tangentCost,tgt,loss,hx]
  · simp [tangentCost,tgt,loss,hx,max_eq_right (not_le.mp hx).le,shift]; split_ifs <;>
      apply (Int.ediv_mul_le _ S_pos_int.ne').trans_eq <;> ring

lemma tangentExact_eq (v m h : ℚ) (c : ℕ) : tangentExact v m h c = tgt v m (shift c h) := by
  unfold tangentExact tgt loss shift; dsimp only; rw [max_comm (v-m)]; split_ifs
  · ring
  · ring
  · aesop

lemma budget_tangent (r : RowHead) (a b : ℤ) (c : ℕ) (hc : c ≠ 2) :
    let m := (mid a b : ℝ); let s := shift c (hw a b : ℝ)
    S - fam r (tgt · m s) - (m^2+2*m*s)/r.d ≤ (rowBudget r a b c : ℝ) := by
  rw [rowBudget, ite_eq_right hc]
  have round (y : ℚ) : (y:ℝ) ≤ (⌈y⌉:ℝ) := by exact_mod_cast Int.le_ceil y
  refine le_trans (le_of_eq ?_) (round _)
  have hm (v : ℤ) : max 0 (scaled v - ((a:ℝ)+b)/(2*TS)) = max 0 ((v:ℝ)-mid a b) / S := by
    rw [← max_div_div_right S_pos.le, zero_div]; congr 1
    norm_num [mid,scaled,HS,TS,S]; ring
  simp only [fam, tangentExact_eq, ← Fin.sum_univ_fun_getElem, tgt, loss]; push_cast
  simp_rw [hm, sub_mul, sum_mul, div_div_eq_mul_div]; split_ifs <;> norm_num [mid,hw,HS,TS,S] <;> ring_nf <;> congr 1 <;> apply sum_congr rfl <;> intros <;> ring_nf

include hwf hx in
/-- On an admitted interval both the first-order row and one of its two
endpoint tangents are valid. Pass to feature units once for all three cases. -/
lemma row_relaxations (ha : 0 ≤ a) (hτa : (a:ℝ) ≤ τ*TS) (hτb : τ*TS ≤ b)
    (hrow : rowLHS L x k τ ≤ 1 - τ^2/scaled (row).d) :
    (RelaxHolds L x k a b 0 ∨ RelaxHolds L x k a b 1) ∧ RelaxHolds L x k a b 2 := by
  let tick (z : ℤ) := z*(S/TS)
  have hab : (tick a : ℝ) ≤ t ∧ t ≤ tick b := by norm_num [tick,S,TS] at *; constructor <;> linarith
  have Hrow : cols L x k (loss · t) + fam row (loss · t) + t^2/(row).d ≤ S := by
    have e (v D : ℤ) (n : ℝ) : S*(n*(max 0 (scaled v-τ))^2/scaled D) = n * loss (v:ℝ) t / D := by
      have hm : max 0 ((v:ℝ)-t) = S * max 0 (scaled v-τ) := by
        rw [mul_max_of_nonneg _ _ S_pos.le, mul_zero, mul_sub, mul_div_cancel₀ _ S_pos.ne']
      rw [loss, hm, div_div_eq_mul_div]; ring
    have h := mul_le_mul_of_nonneg_left (le_sub_iff_add_le.mp hrow) S_pos.le
    simp only [rowLHS, ← Fin.sum_univ_fun_getElem, mul_add, mul_sum, mul_one, e] at h
    convert h using 2; rw [div_div_eq_mul_div]; ring
  constructor
  · let m := (mid a b:ℝ); let h := (hw a b:ℝ); let R := tangentRow L x k m
    have H : R (t-m) ≤ S := (tangentRow_le L hwf x k hx m t).trans Hrow
    have hc (c : ℕ) (hc : c ≠ 2) (he : R (shift c h) ≤ S) : RelaxHolds L x k a b c := by
      apply relax_of_minorant L hwf x k hx c _ he _ (budget_tangent row a b c hc)
      intro v D hd
      rw [colCost, ite_eq_right hc]; refine (cast_ediv_le _ _ hd).trans ?_
      apply div_le_div_of_nonneg_right _ (by positivity)
      have H := (Int.cast_le (R := ℝ)).mpr (tangentCost_le v (a+b) (b-a) c)
      simpa [m,h,mid,hw,tgt,loss,shift] using H
    apply Or.imp (hc 0 (by decide)) (hc 1 (by decide))
    change R (-h) ≤ S ∨ R h ≤ S
    have line s : R s = R 0+(R 1-R 0)*s := tangentRow_affine L x k m s
    rw [line] at H; rw [line (-h),line h]
    have ends : -h ≤ t-m ∧ t-m ≤ h := by
      norm_num [m,h,mid,hw,tick,HS,S,TS] at hab ⊢; constructor <;> linarith
    rcases le_total 0 (R 1-R 0) with hp | hp <;> [left; right] <;> nlinarith [ends.1, ends.2]
  · obtain ⟨hd, hf⟩ := wf_row hwf k
    have low (n v D : ℤ) (hn : 0 ≤ n) (hD : 0 < D) :
        ((n*(max (v-tick b) 0)^2/D : ℤ) : ℝ) ≤ (n:ℝ)*loss (v:ℝ) t/D := by
      refine (cast_ediv_le _ _ hD).trans ?_; push_cast
      rw [loss, max_comm]; gcongr; exact hab.2
    apply relax_of_minorant L hwf x k hx 2 (loss · t) Hrow
    · intro v D hD; simpa [colCost,tick] using low 1 v D zero_le_one hD
    have hf' := sum_le_sum (s := univ) fun i _ => low _ (L.family k i).2.1 _
      (hf _ (List.get_mem _ i)).1 (hf _ (List.get_mem _ i)).2
    have hq : (((S*S*a*a)/(TS*TS*(row).d) : ℤ):ℝ) ≤ t^2/(row).d := by
      refine (cast_ediv_le _ _ (by positivity [show (0:ℤ) < TS by decide])).trans ?_
      have hdr : (0:ℝ) < (row).d := by exact_mod_cast hd
      have h1 := mul_self_le_mul_self (by exact_mod_cast ha) hτa
      norm_num [TS,S,Leaf.row] at h1 hdr ⊢; field_simp; nlinarith
    simp only [rowBudget, ↓reduceIte, Int.cast_sub, ← Fin.sum_univ_fun_getElem, Int.cast_sum]
    dsimp [fam,Leaf.family,tick] at hf' ⊢; linarith

end RelaxAux
end GradedNear.Cert
