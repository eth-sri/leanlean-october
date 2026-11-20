/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
public import DOZZ.Upsilon.JointContinuityIntegral
import DOZZ.Upsilon.Continuation
import DOZZ.Upsilon.FullShifts
import DOZZ.Upsilon.Uniqueness
import DOZZ.Upsilon.ZeroStructure
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import DOZZ.Upsilon.StripShiftsProof

/-!
# Joint parameter and argument continuity of the entire Upsilon family

Use the translated strips from the continuation proof. On each chart the finite
shift recursion is continuous in both parameters, and reflection covers the left.
-/

@[expose] public section
open Complex Filter Set Topology
namespace DOZZ.Proofs

private theorem upsilonBForwardFactor_continuousAt {p : ℝ × ℂ}
    (hγ : 0 < p.1) (hz : 0 < p.2.re) :
    ContinuousAt (fun q : ℝ × ℂ => upsilonBForwardFactor q.1 q.2) p := by
  let a (q : ℝ × ℂ) := (q.1 / 2 : ℂ) * q.2
  have ha : ContinuousAt a p := by dsimp [a]; fun_prop
  have ha₀ : 0 < (a p).re := by simpa [a] using mul_pos (half_pos hγ) hz
  have hΓ : ContinuousAt Gamma (a p) := continuousAt_Gamma _ fun n h =>
    (Gamma_ne_zero_of_re_pos ha₀) (h ▸ Gamma_neg_nat_eq_zero n)
  have hInv : ContinuousAt (fun w => (Gamma w)⁻¹) (1 - a p) :=
    (differentiable_one_div_Gamma (1 - a p)).continuousAt
  have hArg : ContinuousAt (fun q => 1 - a q) p := continuousAt_const.sub ha
  have hComp := hInv.comp (f := fun q => 1 - a q) hArg
  have hPow : ContinuousAt (fun q : ℝ × ℂ => ((q.1 / 2 : ℝ) : ℂ) ^ (1 - (q.1 : ℂ) * q.2)) p := by
    apply ContinuousAt.cpow (by fun_prop) (by fun_prop)
    exact Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using half_pos hγ))
  simp only [upsilonBForwardFactor, lFun, div_eq_mul_inv]
  exact ((hΓ.comp ha).mul hComp).mul hPow

private noncomputable def jointChart (n : ℕ) (p : ℝ × ℂ) : ℂ :=
  upsilonRightChart (p.1 / 2) (fun z => Complex.exp (upsilonLog p.1 z))
    (upsilonBForwardFactor p.1) n p.2

private theorem jointChart_continuousAt (n : ℕ) {p : ℝ × ℂ} (hγ : 0 < p.1)
    (hn : p.2 ∈ upsilonRightDomain (p.1 / 2) (Q p.1) n) : ContinuousAt (jointChart n) p := by
  induction n generalizing p with
  | zero =>
    have hz : 0 < p.2.re ∧ p.2.re < Q p.1 := by simpa [upsilonRightDomain] using hn
    exact Complex.continuous_exp.continuousAt.comp (upsilonLog_continuousAt_joint hγ hz.1 hz.2)
  | succ n ih =>
    let T (q : ℝ × ℂ) := (q.1, q.2 - (q.1 / 2 : ℝ))
    have hd : (T p).2 ∈ upsilonRightDomain (p.1 / 2) (Q p.1) n := upsilonRightDomain_succ.mp hn
    have hpos := (mul_nonneg (Nat.cast_nonneg n) (half_pos hγ).le).trans_lt hd.1
    exact ((upsilonBForwardFactor_continuousAt (p := T p) hγ hpos).mul (ih hγ hd)).comp
      (by dsimp [T]; fun_prop : ContinuousAt T p)

private theorem IsUpsilon.eq_jointChart {γ : ℝ} {U : ℂ → ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hU : IsUpsilon γ U) (n : ℕ) {z : ℂ}
    (hn : z ∈ upsilonRightDomain (γ / 2) (Q γ) n) : U z = jointChart n (γ, z) := by
  induction n generalizing z with
  | zero =>
    have hz : 0 < z.re ∧ z.re < Q γ := by simpa [upsilonRightDomain] using hn
    exact hU.2 z hz.1 hz.2
  | succ n ih =>
    let w := z - ((γ / 2 : ℝ) : ℂ)
    have hw : w ∈ upsilonRightDomain (γ / 2) (Q γ) n := upsilonRightDomain_succ.mp hn
    have hpos := (mul_nonneg (Nat.cast_nonneg n) (half_pos hγ).le).trans_lt hw.1
    have hΓ : 0 < (((γ / 2 : ℂ) * w)).re := by simpa using mul_pos (half_pos hγ) hpos
    have hregular (m : ℕ) : (γ / 2 : ℂ) * w ≠ -(m : ℂ) := by
      intro he
      rw [he] at hΓ
      have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
      simp at hΓ
      linarith
    have hshift := IsUpsilon.shift_b hγ hγ2 hU w hregular
    rw [show w + (γ / 2 : ℂ) = z by simp [w], ih hw] at hshift
    exact hshift

/-- Joint continuity of `Υ_{γ/2}(z)` in `(γ, z)` (see [KRV, §10.6] and [KRV, §11]). -/
theorem IsUpsilon.continuousOn_uncurry {U : ℝ → ℂ → ℂ}
    (hU : ∀ γ ∈ Ioo (0 : ℝ) 2, IsUpsilon γ (U γ)) :
    ContinuousOn (Function.uncurry U) (Ioo 0 2 ×ˢ univ) := by
  intro p hp
  obtain ⟨⟨hγ, hγ2⟩, -⟩ := hp
  have hγ : 0 < p.1 := hγ
  have hγ2 : p.1 < 2 := hγ2
  have hb := half_pos hγ
  have hbq : p.1 / 2 < Q p.1 := by unfold Q; linarith [show 0 < 2 / p.1 by positivity]
  let W (q : ℝ × ℂ) := if 0 < p.2.re then q.2 else (Q q.1 : ℂ) - q.2
  have hQ : ContinuousAt (fun q : ℝ × ℂ => Q q.1) p := by
    have h := hγ.ne'
    fun_prop (disch := assumption) [Q]
  have hW : ContinuousAt W p := by
    by_cases hz : 0 < p.2.re
    · simpa only [W, ite_eq_left hz] using continuousAt_snd (p := p)
    · rw [show W = fun q => (Q q.1 : ℂ) - q.2 by simp [W, hz]]
      fun_prop
  have hpos : 0 < (W p).re := by
    by_cases hz : 0 < p.2.re
    · simpa [W, hz] using hz
    · simp [W, hz]
      linarith
  obtain ⟨n, hn⟩ := exists_upsilonRightDomain hb hbq (W p) hpos
  have hN : ContinuousAt (fun q : ℝ × ℂ => (n : ℝ) * (q.1 / 2)) p := by fun_prop
  have hRe : ContinuousAt (fun q => (W q).re) p := by fun_prop
  have hlo := hN.eventually_lt hRe hn.1
  have hhi := hRe.eventually_lt (hN.add hQ) hn.2
  have hγnear := continuousAt_fst.eventually (isOpen_Ioo.mem_nhds (show p.1 ∈ Ioo 0 2 from ⟨hγ, hγ2⟩))
  apply ContinuousAt.continuousWithinAt
  have hMap : ContinuousAt (fun q => (q.1, W q)) p := continuousAt_fst.prodMk hW
  have hChart := (jointChart_continuousAt n (p := (p.1, W p)) hγ hn).comp (f := fun q : ℝ × ℂ => (q.1, W q)) (x := p) hMap
  refine hChart.congr_of_eventuallyEq ?_
  filter_upwards [hγnear, hlo, hhi] with q hq hl hh
  have hUq := hU q.1 hq
  have he : U q.1 q.2 = U q.1 (W q) := by
    by_cases hz : 0 < p.2.re
    · simp [W, hz]
    · simpa [W, hz] using (IsUpsilon.reflect hq.1 hq.2 hUq q.2).symm
  exact he.trans (IsUpsilon.eq_jointChart hq.1 hq.2 hUq n ⟨hl, hh⟩)

end DOZZ.Proofs
end
