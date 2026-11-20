/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
public import DOZZ.Upsilon.IntegralHolomorphy
public import DOZZ.Upsilon.StripShifts
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.HalfPlane
public import DOZZ.Upsilon.StripIdentities

/-!
# Entire continuation of the Upsilon strip function

First continue to the right using translated strips and the shift multiplier. Reflection
across the midpoint then supplies the continuation to the left.
-/

@[expose] public section
open Complex Filter Topology Set
noncomputable section
namespace DOZZ.Proofs

def upsilonRightDomain (b q : ℝ) (n : ℕ) : Set ℂ :=
  {z | n * b < z.re ∧ z.re < n * b + q}

def upsilonRightChart (b : ℝ) (F G : ℂ → ℂ) : ℕ → ℂ → ℂ
  | 0 => F
  | n + 1 => fun z => G (z - b) * upsilonRightChart b F G n (z - b)

private theorem upsilonRightDomain_open (b q : ℝ) (n : ℕ) : IsOpen (upsilonRightDomain b q n) :=
  (isOpen_re_gt _).inter (isOpen_re_lt _)

section
variable {b q : ℝ}

theorem upsilonRightDomain_succ {n : ℕ} {z : ℂ} :
    z ∈ upsilonRightDomain b q (n + 1) ↔ z - b ∈ upsilonRightDomain b q n := by
  simp only [upsilonRightDomain, mem_ofPred_eq, Nat.cast_succ, add_mul, one_mul, sub_re, ofReal_re]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

private theorem upsilonRightChart_differentiable (hb : 0 < b) {F G : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (upsilonRightDomain b q 0))
    (hG : ∀ z, 0 < z.re → DifferentiableAt ℂ G z) {n : ℕ} {z : ℂ}
    (hz : z ∈ upsilonRightDomain b q n) : DifferentiableAt ℂ (upsilonRightChart b F G n) z := by
  induction n generalizing z with
  | zero => exact hF.differentiableAt ((upsilonRightDomain_open b q 0).mem_nhds hz)
  | succ n ih =>
    have hw := upsilonRightDomain_succ.mp hz
    have hpos := (mul_nonneg (Nat.cast_nonneg n) hb.le).trans_lt hw.1
    exact ((hG (z - b) hpos).mul (ih hw)).comp z (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w - b) z)

private theorem upsilonRightChart_adjacent {F G : ℂ → ℂ}
    (hshift : ∀ w : ℂ, 0 < w.re → w.re < q - b → F (w + b) = G w * F w)
    {n : ℕ} {z : ℂ} (hz : z ∈ upsilonRightDomain b q n) (hz' : z ∈ upsilonRightDomain b q (n + 1)) :
    upsilonRightChart b F G n z = upsilonRightChart b F G (n + 1) z := by
  induction n generalizing z with
  | zero =>
    have hw := upsilonRightDomain_succ.mp hz'
    have h₀ : 0 < (z - b).re := by simpa [upsilonRightDomain] using hw.1
    simpa [upsilonRightChart] using hshift (z - b) h₀ (by
      simpa only [sub_re, ofReal_re, Nat.cast_zero, zero_mul, zero_add] using
        sub_lt_sub_right hz.2 b)
  | succ n ih =>
    change G (z - b) * upsilonRightChart b F G n (z - b) =
      G (z - b) * upsilonRightChart b F G (n + 1) (z - b)
    rw [ih (upsilonRightDomain_succ.mp hz) (upsilonRightDomain_succ.mp hz')]

end

section
variable {b q : ℝ} (hb : 0 < b)
include hb

private theorem upsilonRightChart_overlap {F G : ℂ → ℂ}
    (hshift : ∀ w : ℂ, 0 < w.re → w.re < q - b → F (w + b) = G w * F w)
    {m n : ℕ} {z : ℂ} (hm : z ∈ upsilonRightDomain b q m) (hn : z ∈ upsilonRightDomain b q n) :
    upsilonRightChart b F G m z = upsilonRightChart b F G n z := by
  wlog hmn : m ≤ n generalizing m n
  · exact (this hn hm (by omega)).symm
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    have hi : z ∈ upsilonRightDomain b q n :=
      ⟨(mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ n) hb.le).trans_lt hn.1,
       hm.2.trans_le (add_le_add_left (mul_le_mul_of_nonneg_right (show (m : ℝ) ≤ n by exact_mod_cast hmn) hb.le) q)⟩
    exact (ih hi).trans (upsilonRightChart_adjacent hshift hi hn)

theorem exists_upsilonRightDomain (hbq : b < q) (z : ℂ)
    (hz : 0 < z.re) : ∃ n : ℕ, z ∈ upsilonRightDomain b q n := by
  have h : ∃ n : ℕ, z.re ≤ ((n : ℝ) + 1) * b := by
    obtain ⟨m, hm⟩ := exists_nat_ge (z.re / b)
    exact ⟨m, ((div_le_iff₀ hb).1 hm).trans (by nlinarith)⟩
  let n := Nat.find h
  have hn := Nat.find_spec h
  refine ⟨n, ?_, ?_⟩
  · cases hn' : n with
    | zero => simpa [hn'] using hz
    | succ m =>
      have hlt := Nat.find_min h (m := m) (show m < n by omega)
      simpa only [hn', Nat.cast_succ, not_le] using hlt
  · have hn' : z.re ≤ (↑n + 1) * b := hn
    linarith [hn']

private theorem exists_right_extension (hbq : b < q) {F G : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (upsilonRightDomain b q 0))
    (hG : ∀ z, 0 < z.re → DifferentiableAt ℂ G z)
    (hshift : ∀ w : ℂ, 0 < w.re → w.re < q - b → F (w + b) = G w * F w) :
    ∃ A : ℂ → ℂ, (∀ z, 0 < z.re → DifferentiableAt ℂ A z) ∧ EqOn A F (upsilonRightDomain b q 0) := by
  classical
  let A (z : ℂ) := if h : ∃ n, z ∈ upsilonRightDomain b q n then upsilonRightChart b F G h.choose z else 0
  have heq {z n} (hn : z ∈ upsilonRightDomain b q n) : A z = upsilonRightChart b F G n z := by
    have h : ∃ i, z ∈ upsilonRightDomain b q i := ⟨n, hn⟩
    simp only [A, dite_eq_left h]
    exact upsilonRightChart_overlap hb hshift h.choose_spec hn
  refine ⟨A, fun z hz => ?_, fun z hz => heq hz⟩
  obtain ⟨n, hn⟩ := exists_upsilonRightDomain hb hbq z hz
  apply (upsilonRightChart_differentiable hb hF hG hn).congr_of_eventuallyEq
  filter_upwards [(upsilonRightDomain_open b q n).mem_nhds hn] with _ hw
  exact heq hw

end

/-- Existence of an entire Upsilon function from the strip integral, shift and reflection. -/
theorem exists_IsUpsilon {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ U : ℂ → ℂ, IsUpsilon γ U := by
  have hb : 0 < γ / 2 := half_pos hγ
  have hbq : γ / 2 < Q γ := by unfold Q; linarith [show 0 < 2 / γ by positivity]
  have hq : 0 < Q γ := hb.trans hbq
  let F (z : ℂ) := Complex.exp (upsilonLog γ z)
  have hF : DifferentiableOn ℂ F (upsilonRightDomain (γ / 2) (Q γ) 0) := by
    apply Complex.differentiable_exp.comp_differentiableOn
    simpa [upsilonRightDomain] using upsilonLog_differentiableOn hγ hγ2
  obtain ⟨A, hA, hEq⟩ := exists_right_extension hb hbq hF
    (fun z hz => upsilonBForwardFactor_differentiableAt hγ hz) (fun w hw hw' => by
      have h : Q γ - γ / 2 = 2 / γ := by unfold Q; ring
      rw [h] at hw'
      simpa [F, upsilonBForwardFactor] using exp_upsilonLog_shift_b hγ hγ2 hw hw')
  have hStrip (z : ℂ) (h₀ : 0 < z.re) (h₁ : z.re < Q γ) : A z = F z :=
    hEq (by simpa [upsilonRightDomain] using And.intro h₀ h₁)
  let U (z : ℂ) := if 0 < z.re then A z else A ((Q γ : ℂ) - z)
  have hright {z : ℂ} (hz : 0 < z.re) : U z = A z := ite_eq_left hz
  have hleft {z : ℂ} (hz : z.re < Q γ) : U z = A ((Q γ : ℂ) - z) := by
    by_cases h₀ : 0 < z.re
    · rw [hright h₀, hStrip z h₀ hz, hStrip ((Q γ : ℂ) - z) (by simpa using hz)
        (by simp [sub_re]; linarith)]
      exact congrArg Complex.exp (upsilonLog_reflect γ z h₀ hz).symm
    · exact ite_eq_right h₀
  refine ⟨U, fun z => ?_, fun z h₀ h₁ => (hright h₀).trans (hStrip z h₀ h₁)⟩
  by_cases hz : 0 < z.re
  · apply (hA z hz).congr_of_eventuallyEq
    filter_upwards [(isOpen_re_gt 0).mem_nhds hz] with _ hw
    exact hright hw
  · have hlt : z.re < Q γ := lt_of_le_of_lt (le_of_not_gt hz) hq
    apply ((hA ((Q γ : ℂ) - z) (by simpa using hlt)).comp z
        (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => (Q γ : ℂ) - w) z)).congr_of_eventuallyEq
    filter_upwards [(isOpen_re_lt (Q γ)).mem_nhds hlt] with _ hw
    exact hleft hw

end DOZZ.Proofs
end
