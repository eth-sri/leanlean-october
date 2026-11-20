/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Trace.Kernel

@[expose] public section
namespace Light.Sec3.Trace.Kernel
variable {lim : Limits} {P : Program} {d j h top self mix : ℕ} {x : Task} {μ : Mem}

private theorem stages_spec (hp : P[mix]?=some (Grid.code mixCell)) (ih : Spec lim P self j)
    (H : Ok x μ (j+1) h lim d top) (rs : List Row) (good : ∀ r∈rs, |r.a.s| ≤ 1 ∧ |r.b.s| ≤ 1 ∧ |r.c.s| ≤ 1)
    (acc res : ℤ) (fits : |acc| + (rs.length:ℤ) * ((side (j+1)*h:ℕ):ℤ)^3 ≤ lim.word) :
    Ends lim P d (stages mix self rs) ⟨loc x j acc res, μ⟩ (rs.length*phaseTime j + 2) fun σ =>
      σ.loc 0 = acc + (rs.map (gain x j)).sum ∧ Untouched μ σ.mem x.fr top := by
  induction rs generalizing μ acc res with
  | nil => exact Ends.setTo acc ⟨by simp,.refl⟩
  | cons r rs step =>
    have hg := good r (.head _)
    have two : side (j+1)=side j+side j := by simp [side,pow_succ,Nat.mul_two]
    have e : side j*(2*h)=side (j+1)*h := by rw [two]; ring
    have bd := abs_tri (bdd_mix _ hg.1 (two ▸ H.a.bounded)) (bdd_mix _ hg.2.1 (two ▸ H.b.bounded))
      (bdd_mix _ hg.2.2 (two ▸ H.c.bounded))
    change |gain x j r| ≤ ((side j*(2*h):ℕ):ℤ)^3 at bd
    rw [e] at bd
    have hr := abs_add_le acc (gain x j r)
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul] at fits
    have next : |acc+gain x j r| + (rs.length:ℤ) * ((side (j+1)*h:ℕ):ℤ)^3 ≤ lim.word := by linarith
    have left : 0 ≤ (rs.length:ℤ) * ((side (j+1)*h:ℕ):ℤ)^3 := by positivity
    refine Ends.seq (phaseTime j) (rs.length*phaseTime j + 2) ((phase_spec hp ih H r hg acc res (by linarith)).mono le_rfl ?_)
      (by simp [Nat.succ_mul]; omega)
    rintro _ ⟨ν,rfl,same⟩
    refine (step (H.keep same) (fun q hq => good q (.tail _ hq)) _ _ next).mono le_rfl ?_
    rintro _ ⟨v,o⟩; exact ⟨by simpa [add_assoc] using v,same.trans o⟩

theorem spec (hp : P[mix]?=some (Grid.code mixCell)) (link : P[self]?=some (body mix self)) : ∀ j, Spec lim P self j := by
  intro j; induction j with
  | zero =>
    intro x μ d h top H
    have a := H.a.read 0 (by decide) 0 (by decide); have b := H.b.read 0 (by decide) 0 (by decide); have c := H.c.read 0 (by decide) 0 (by decide)
    have aa := H.a.below; have bb := H.b.below; have cc := H.c.below; have room := H.room
    simp only [side,pow_zero,mul_one,zero_mul,add_zero] at a b c aa bb cc room
    have ba := H.a.bounded 0 (by decide) 0 (by decide); have bd := H.b.bounded 0 (by decide) 0 (by decide); have bc := H.c.bounded 0 (by decide) 0 (by decide)
    have prod := mul_le_mul ba bd (abs_nonneg _) (by positivity)
    have all := mul_le_mul prod bc (abs_nonneg _) (by positivity)
    rw [←abs_mul] at prod; rw [←abs_mul,←abs_mul] at all
    have hw := H.word; have := H.space; have := H.hw
    simp [side] at hw
    have z : (h:ℤ)*h*h ≤ lim.word ∧ (h:ℤ)*h ≤ lim.word := by push_cast at hw; constructor <;> nlinarith
    rw [abs_le] at all prod
    apply Meets.of_body link
    refine Ends.iteLast (fun _ => ?_) (fun hn => absurd hn (by simp)) (hT:=by decide)
    refine Ends.setTo (value x 0) ⟨rfl,.refl⟩ ?_ (by decide)
    light_side [a,b,c,value,side,tri]
  | succ j ih =>
    intro x μ d h top H
    have := H.hw; have := H.space; have := H.below; have word := H.word; have room := H.room
    have two : side (j+1)=side j+side j := by simp [side,pow_succ,Nat.mul_two]
    have nle := Nat.le_mul_self (side j); have W : 1≤side j := Nat.one_le_pow _ _ (by decide)
    rw [two] at room word
    have sq : side j*side j ≤ (side j+side j)*(side j+side j) := by gcongr <;> omega
    have read := H.pow j (by omega)
    have adr : ((x.tab:ℤ) + (j+1) - 1).toNat = x.tab+j := by omega
    have budget : |(0:ℤ)| + (rows.length:ℤ)*((side (j+1)*h:ℕ):ℤ)^3 ≤ lim.word := by
      have : rows.length=7 := rfl
      rw [this,two,abs_zero,zero_add]; refine le_trans ?_ word
      exact_mod_cast Nat.mul_le_mul (by decide : 7≤16) (Nat.pow_le_pow_left (Nat.le_succ _) 3)
    have eq := tri_split (side j) x.a.values x.b.values x.c.values
    rw [← two] at eq
    apply Meets.of_body link
    refine Ends.iteLast (fun hn => absurd hn (by simp; omega)) (fun _ => ?_) (hT:=by simp [cost])
    light_set (side j) using adr,read,cost
    light_set (side j*side j:ℕ) using cost
    light_set 0 using cost
    light_set 0 using cost
    refine (stages_spec hp ih H rows (by decide) 0 0 budget).mono ?_ ?_
    · change 7 * phaseTime j + 2 ≤ _; simp [cost]
    · intro τ h; simpa [value,eq,gain] using h
/-- Seven recursive calls on squares of one quarter the area dominate the work. -/
theorem cost_le (j : ℕ) : cost j + 30000*4^j ≤ 40000*7^j := by
  induction j with
  | zero => decide
  | succ j ih =>
    have sq : side j*side j=4^j := by unfold side; rw [← mul_pow]; rfl
    have sn := Nat.le_mul_self (side j); rw [sq] at sn
    have pos : 1≤4^j := Nat.one_le_pow _ _ (by decide)
    simp only [cost,Grid.time,pow_succ 7,pow_succ 4]
    nlinarith only [ih,sn,sq,pos]
end Light.Sec3.Trace.Kernel
