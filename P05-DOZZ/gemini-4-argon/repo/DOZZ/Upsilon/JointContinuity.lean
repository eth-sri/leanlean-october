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

/-!
# Joint parameter and argument continuity of the entire Upsilon family
-/

@[expose] public section

open Complex Filter MeasureTheory Set Topology

namespace DOZZ.Proofs

private noncomputable def jointShiftN (γ : ℝ) (n : ℕ) : ℂ :=
  ((n : ℝ) * (γ / 2) : ℂ)

private noncomputable def jointShiftFactor (γ : ℝ) (w : ℂ) : ℂ :=
  ((γ / 2 : ℝ) : ℂ) ^ ((γ : ℂ) * w - 1) *
    Complex.Gamma (1 - (γ / 2 : ℝ) * w) *
      (Complex.Gamma ((γ / 2 : ℝ) * w))⁻¹

private noncomputable def jointShiftChain (γ : ℝ) : ℕ → ℂ → ℂ
  | 0, _ => 1
  | n + 1, w => jointShiftFactor γ w *
      jointShiftChain γ n (w + (γ / 2 : ℝ))

private theorem jointShiftN_re γ (n : ℕ) :
    (jointShiftN γ n).re = (n : ℝ) * (γ / 2) := by
  simp [jointShiftN]

private theorem jointShiftN_succ γ n :
    jointShiftN γ (n + 1) = jointShiftN γ n + (γ / 2 : ℝ) := by
  simp [jointShiftN, Nat.cast_add]
  ring


private theorem IsUpsilon.eq_shiftChain {γ} {U}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hU : IsUpsilon γ U)
    w n (hfinal :
      0 < (w + jointShiftN γ n).re ∧ (w + jointShiftN γ n).re < Q γ) :
    U w = jointShiftChain γ n w * U (w + jointShiftN γ n) := by
  induction n generalizing w with
  | zero => simp [jointShiftN, jointShiftChain]
  | succ n ih =>
      have hfinalEq : w + jointShiftN γ (n + 1) =
          (w + (γ / 2 : ℝ)) + jointShiftN γ n := by
        rw [jointShiftN_succ]
        abel
      have : γ / 2 ≤ (n + 1 : ℝ) * (γ / 2) := by
        simpa using mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ (n + 1 : ℝ) by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)) (show 0 ≤ γ / 2 by positivity)
      have hw : w.re < 2 / γ := by
        have hlast := hfinal.2
        rw [(show (w + jointShiftN γ (n + 1)).re = w.re + (n + 1 : ℝ) * (γ / 2) by simp [Complex.add_re, jointShiftN_re])] at hlast
        calc
          w.re < Q γ - (n + 1 : ℝ) * (γ / 2) := by linarith
          _ ≤ Q γ - γ / 2 := by linarith
          _ = 2 / γ := (by unfold Q; ring)
      have hrec := IsUpsilon.shift_b_reciprocal hγ hγ2 hU w hw
      have hrest := ih (w + (γ / 2 : ℝ)) (show 0 < ((w + (γ / 2 : ℝ)) + jointShiftN γ n).re ∧ ((w + (γ / 2 : ℝ)) + jointShiftN γ n).re < Q γ by rw [← hfinalEq]; exact hfinal)
      rw [(show w + (γ / 2 : ℝ) = w + (γ / 2 : ℂ) by push_cast; ring)] at hrest
      rw [hrest] at hrec
      simpa [jointShiftChain, jointShiftFactor, hfinalEq, mul_assoc] using hrec.symm


private theorem jointShiftChain_continuousAt {γ₀} {w₀}
    (hγ₀ : 0 < γ₀) n
    (hstep : ∀ j : ℕ, j < n → (w₀ + jointShiftN γ₀ j).re < 2 / γ₀) :
    ContinuousAt (fun p : ℝ × ℂ => jointShiftChain p.1 n p.2) (γ₀, w₀) := by
  have jointShiftFactor_continuousAt {w₀ : ℂ} (hw₀ : w₀.re < 2 / γ₀) : ContinuousAt (fun p : ℝ × ℂ => jointShiftFactor p.1 p.2) (γ₀, w₀) := by
    let b : ℝ × ℂ → ℂ := fun p => ((p.1 / 2 : ℝ) : ℂ)
    let γC : ℝ × ℂ → ℂ := fun p => (p.1 : ℂ)
    let arg₁ : ℝ × ℂ → ℂ := fun p => 1 - b p * p.2
    let arg₂ : ℝ × ℂ → ℂ := fun p => b p * p.2
    let exponent : ℝ × ℂ → ℂ := fun p => γC p * p.2 - 1
    have : (γ₀ / 2) * w₀.re < 1 := by
      have hmul := mul_lt_mul_of_pos_left hw₀ (by positivity : 0 < γ₀ / 2)
      rw [(show (γ₀ / 2) * (2 / γ₀) = 1 by field_simp [hγ₀.ne'])] at hmul
      exact hmul
    have hGamma0 : ContinuousAt Complex.Gamma (arg₁ (γ₀, w₀)) :=
      Complex.continuousAt_Gamma _ (by
        intro m hm
        apply Complex.Gamma_ne_zero_of_re_pos (show 0 < (arg₁ (γ₀, w₀)).re by simp only [arg₁, Complex.sub_re, Complex.one_re, (show (b (γ₀, w₀) * w₀).re = (γ₀ / 2) * w₀.re by simp [b, Complex.mul_re])]; linarith)
        rw [hm]
        exact Complex.Gamma_neg_nat_eq_zero m)
    change ContinuousAt (fun p => b p ^ exponent p * Complex.Gamma (arg₁ p) *
      (Complex.Gamma (arg₂ p))⁻¹) (γ₀, w₀)
    exact (((show ContinuousAt b (γ₀, w₀) by fun_prop).cpow (show ContinuousAt exponent (γ₀, w₀) by dsimp [exponent]; exact ((show ContinuousAt γC (γ₀, w₀) by fun_prop).mul continuousAt_snd).sub continuousAt_const) (by rw [Complex.mem_slitPlane_iff]; left; simp [b]; positivity)).mul (hGamma0.comp (by fun_prop))).mul (((Complex.differentiable_one_div_Gamma (arg₂ (γ₀, w₀))).continuousAt).comp (by fun_prop))
  induction n generalizing w₀ with
  | zero => simpa [jointShiftChain] using (continuousAt_const : ContinuousAt (fun _ : ℝ × ℂ => (1 : ℂ)) (γ₀, w₀))
  | succ n ih =>
      have hstep' : ∀ j : ℕ, j < n →
          ((w₀ + (γ₀ / 2 : ℝ)) + jointShiftN γ₀ j).re < 2 / γ₀ := by
        intro j hj
        have h := hstep (j + 1) (by omega)
        rw [← (show (w₀ + (γ₀ / 2 : ℝ)) + jointShiftN γ₀ j = w₀ + jointShiftN γ₀ (j + 1) by rw [jointShiftN_succ]; abel)] at h
        exact h
      have hrest : ContinuousAt (fun p : ℝ × ℂ =>
          jointShiftChain p.1 n (p.2 + (p.1 / 2 : ℝ))) (γ₀, w₀) := by
        change ContinuousAt
          ((fun q : ℝ × ℂ => jointShiftChain q.1 n q.2) ∘
            (fun p : ℝ × ℂ => (p.1, p.2 + (p.1 / 2 : ℝ)))) (γ₀, w₀)
        exact ContinuousAt.comp
          (f := fun p : ℝ × ℂ => (p.1, p.2 + (p.1 / 2 : ℝ)))
          (g := fun q : ℝ × ℂ => jointShiftChain q.1 n q.2)
          (x := (γ₀, w₀)) (ih (w₀ := w₀ + (γ₀ / 2 : ℝ)) hstep') (by fun_prop)
      change ContinuousAt (fun p : ℝ × ℂ =>
        jointShiftFactor p.1 p.2 *
          jointShiftChain p.1 n (p.2 + (p.1 / 2 : ℝ))) (γ₀, w₀)
      exact (jointShiftFactor_continuousAt (by simpa [jointShiftN] using hstep 0 (by omega))).mul hrest

private noncomputable def jointChartArg (reflect : Bool) (p : ℝ × ℂ) : ℂ :=
  if reflect then (Q p.1 : ℂ) - p.2 else p.2

private noncomputable def jointShiftChart (reflect : Bool) (n : ℕ)
    (p : ℝ × ℂ) : ℂ :=
  jointShiftChain p.1 n (jointChartArg reflect p) *
    Complex.exp (upsilonLog p.1 (jointChartArg reflect p + jointShiftN p.1 n))

private theorem jointChartArg_continuousAt {γ₀} {z₀} reflect
    (hγ₀ : γ₀ ≠ 0) :
    ContinuousAt (jointChartArg reflect) (γ₀, z₀) := by
  cases reflect
  · change ContinuousAt (fun p : ℝ × ℂ => p.2) (γ₀, z₀)
    exact continuousAt_snd
  · have hQ : ContinuousAt (fun p : ℝ × ℂ => (Q p.1 : ℂ)) (γ₀, z₀) := by
      exact ContinuousAt.comp (f := fun p : ℝ × ℂ => Q p.1)
        (g := fun x : ℝ => (x : ℂ)) (x := (γ₀, z₀))
        Complex.continuous_ofReal.continuousAt (by exact ContinuousAt.comp (f := fun p : ℝ × ℂ => p.1) (g := Q) (x := (γ₀, z₀)) (by fun_prop (disch := assumption) [Q]) continuousAt_fst)
    change ContinuousAt (fun p : ℝ × ℂ => (Q p.1 : ℂ) - p.2) (γ₀, z₀)
    exact hQ.sub continuousAt_snd

private theorem jointShiftChart_continuousAt {γ₀} {z₀}
    reflect n (hγ₀ : 0 < γ₀)
    (hfinal : 0 < (jointChartArg reflect (γ₀, z₀) + jointShiftN γ₀ n).re ∧
      (jointChartArg reflect (γ₀, z₀) + jointShiftN γ₀ n).re < Q γ₀) :
    ContinuousAt (jointShiftChart reflect n) (γ₀, z₀) := by
  let w₀ := jointChartArg reflect (γ₀, z₀)
  let v₀ := w₀ + jointShiftN γ₀ n
  have hγ₀ne := hγ₀.ne'
  have hArg : ContinuousAt (jointChartArg reflect) (γ₀, z₀) :=
    jointChartArg_continuousAt reflect hγ₀ne
  have hN : ContinuousAt (fun p : ℝ × ℂ => jointShiftN p.1 n) (γ₀, z₀) := by
    dsimp [jointShiftN]
    fun_prop
  have hW := hArg.add hN
  have : jointChartArg reflect (γ₀, z₀) + jointShiftN γ₀ n = v₀ := rfl
  have hstep : ∀ j : ℕ, j < n → (w₀ + jointShiftN γ₀ j).re < 2 / γ₀ := by
    intro j hj
    have hjn : (j : ℝ) + 1 ≤ (n : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hj)
    have hb : 0 < γ₀ / 2 := by positivity
    have : (j : ℝ) * (γ₀ / 2) + γ₀ / 2 ≤ (n : ℝ) * (γ₀ / 2) := by
      calc
        (j : ℝ) * (γ₀ / 2) + γ₀ / 2 = ((j : ℝ) + 1) * (γ₀ / 2) := by ring
        _ ≤ (n : ℝ) * (γ₀ / 2) := mul_le_mul_of_nonneg_right hjn hb.le
    have hfinalRe : v₀.re = w₀.re + (n : ℝ) * (γ₀ / 2) := by
      simp [v₀, Complex.add_re, jointShiftN_re]
    have hstepRe : (w₀ + jointShiftN γ₀ j).re =
        w₀.re + (j : ℝ) * (γ₀ / 2) := by
      simp [Complex.add_re, jointShiftN_re]
    rw [hstepRe]
    have hQminus : Q γ₀ - γ₀ / 2 = 2 / γ₀ := by
      unfold Q
      ring
    calc
      w₀.re + (j : ℝ) * (γ₀ / 2) ≤ v₀.re - γ₀ / 2 := by
        rw [hfinalRe]
        linarith
      _ < Q γ₀ - γ₀ / 2 := by linarith [hfinal.2]
      _ = 2 / γ₀ := hQminus
  have hChainOuter := jointShiftChain_continuousAt hγ₀ n hstep
  have hChainMap := continuousAt_fst.prodMk hArg
  have hChain : ContinuousAt (fun p : ℝ × ℂ =>
      jointShiftChain p.1 n (jointChartArg reflect p)) (γ₀, z₀) := by
    change ContinuousAt
      ((fun q : ℝ × ℂ => jointShiftChain q.1 n q.2) ∘
        (fun p : ℝ × ℂ => (p.1, jointChartArg reflect p))) (γ₀, z₀)
    exact ContinuousAt.comp
      (f := fun p : ℝ × ℂ => (p.1, jointChartArg reflect p))
      (g := fun q : ℝ × ℂ => jointShiftChain q.1 n q.2)
      (x := (γ₀, z₀)) hChainOuter hChainMap
  have hLogOuter := upsilonLog_continuousAt_joint hγ₀ hfinal.1 hfinal.2
  have hLogMap := continuousAt_fst.prodMk hW
  have hLog : ContinuousAt (fun p : ℝ × ℂ =>
      upsilonLog p.1 (jointChartArg reflect p + jointShiftN p.1 n)) (γ₀, z₀) := by
    change ContinuousAt
      ((Function.uncurry upsilonLog) ∘
        (fun p : ℝ × ℂ => (p.1, jointChartArg reflect p + jointShiftN p.1 n)))
      (γ₀, z₀)
    exact ContinuousAt.comp
      (f := fun p : ℝ × ℂ =>
        (p.1, jointChartArg reflect p + jointShiftN p.1 n))
      (g := Function.uncurry upsilonLog) (x := (γ₀, z₀)) hLogOuter hLogMap
  change ContinuousAt (fun p : ℝ × ℂ =>
    jointShiftChain p.1 n (jointChartArg reflect p) *
      Complex.exp (upsilonLog p.1 (jointChartArg reflect p + jointShiftN p.1 n)))
    (γ₀, z₀)
  exact hChain.mul (continuous_exp.continuousAt.comp hLog)

private theorem IsUpsilon.eq_jointShiftChart {γ} {U}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hU : IsUpsilon γ U)
    reflect n z
    (hfinal : 0 < (jointChartArg reflect (γ, z) + jointShiftN γ n).re ∧
      (jointChartArg reflect (γ, z) + jointShiftN γ n).re < Q γ) :
    U z = jointShiftChart reflect n (γ, z) := by
  cases reflect with
  | false =>
      calc
        U z = jointShiftChain γ n z * U (z + jointShiftN γ n) := (IsUpsilon.eq_shiftChain hγ hγ2 hU z n (by simpa [jointChartArg] using hfinal))
        _ = jointShiftChain γ n z * Complex.exp
            (upsilonLog γ (z + jointShiftN γ n)) := by rw [(hU.2 (z + jointShiftN γ n) hfinal.1 hfinal.2)]
        _ = jointShiftChart false n (γ, z) := by
          simp [jointShiftChart, jointChartArg]
  | true =>
      let w := (Q γ : ℂ) - z
      have hchain := IsUpsilon.eq_shiftChain hγ hγ2 hU w n (by
        simpa [jointChartArg, w] using hfinal)
      calc
        U z = U w := (by simpa [w] using (_root_.DOZZ.Proofs.IsUpsilon.reflect hγ hγ2 hU z).symm)
        _ = jointShiftChain γ n w * Complex.exp (upsilonLog γ (w + jointShiftN γ n)) := by
          rw [hchain, (hU.2 (w + jointShiftN γ n) hfinal.1 hfinal.2)]
        _ = jointShiftChart true n (γ, z) := by
          simp [jointShiftChart, jointChartArg, w]

/-- Joint continuity of `Υ_{γ/2}(z)` in `(γ, z)` (see the continuity arguments in [KRV, §10.6] and
[KRV, §11]). -/
theorem IsUpsilon.continuousOn_uncurry {U : ℝ → ℂ → ℂ}
    (hU : ∀ γ ∈ Ioo (0 : ℝ) 2, IsUpsilon γ (U γ)) :
    ContinuousOn (Function.uncurry U) (Ioo 0 2 ×ˢ univ) := by
  have exists_shift_into_strip {γ} (hγ : 0 < γ) {x} (hxQ : x < Q γ) : ∃ n : ℕ, 0 < x + (n : ℝ) * (γ / 2) ∧ x + (n : ℝ) * (γ / 2) < Q γ := by
    have hb : 0 < γ / 2 := by positivity
    have hbQ : γ / 2 < Q γ := by
      unfold Q
      have : 0 < 2 / γ := by positivity
      linarith
    by_cases hx : 0 < x
    · exact ⟨0, by simpa, by simpa using hxQ⟩
    · have hx0 : x ≤ 0 := le_of_not_gt hx
      let y := -x / (γ / 2)
      let N := Nat.floor y
      let n := N + 1
      have hne : y * (γ / 2) = -x := by
        dsimp [y]
        field_simp [ne_of_gt hb]
      have hlow : 0 < x + (n : ℝ) * (γ / 2) := by
        have hmul := mul_lt_mul_of_pos_right (show y < (n : ℝ) by simpa [n] using (Nat.lt_floor_add_one y)) hb
        rw [hne] at hmul
        nlinarith
      have hnle : (n : ℝ) ≤ y + 1 := by
        calc
          (n : ℝ) = (N : ℝ) + 1 := by simp [n]
          _ ≤ y + 1 := by linarith [(Nat.floor_le (show 0 ≤ y by dsimp [y]; exact div_nonneg (neg_nonneg.mpr hx0) hb.le))]
      have hupp : x + (n : ℝ) * (γ / 2) ≤ γ / 2 := by
        have := mul_le_mul_of_nonneg_right hnle hb.le
        calc
          x + (n : ℝ) * (γ / 2) ≤ x + (y + 1) * (γ / 2) := by linarith
          _ = γ / 2 := by rw [add_mul, hne]; ring
      exact ⟨n, hlow, lt_of_le_of_lt hupp hbQ⟩
  intro p hp
  rcases hp with ⟨hγp, _⟩
  rcases hγp with ⟨hγlo, hγhi⟩
  let γ₀ := p.1
  let z₀ := p.2
  have hγ₀ : 0 < γ₀ := hγlo
  have hγ₀2 := hγhi
  have hγ₀ne : γ₀ ≠ 0 := hγ₀.ne'
  have := hU γ₀ ⟨hγ₀, hγ₀2⟩
  let reflect := if z₀.re < Q γ₀ then false else true
  have hxQ : (jointChartArg reflect p).re < Q γ₀ := by
    by_cases h : z₀.re < Q γ₀
    · simp [reflect, h, jointChartArg, γ₀, z₀]
    · have hzQ : z₀.re ≥ Q γ₀ := le_of_not_gt h
      have : 0 < Q γ₀ := by
        unfold Q
        positivity
      simp only [reflect, h, jointChartArg, γ₀, z₀, ite_false, ite_true,
        Complex.sub_re, Complex.ofReal_re]
      linarith
  obtain ⟨n, hfinal0, hfinalQ⟩ := exists_shift_into_strip hγ₀ hxQ
  let W : ℝ × ℂ → ℂ := fun q => jointChartArg reflect q + jointShiftN q.1 n
  have hQcont : ContinuousAt (fun q : ℝ × ℂ => Q q.1) p := by
    have hQγ : ContinuousAt Q γ₀ := by
      fun_prop (disch := assumption) [Q]
    exact ContinuousAt.comp (f := fun q : ℝ × ℂ => q.1) (g := Q)
      (x := p) hQγ continuousAt_fst
  have hWre := ContinuousAt.comp (f := W) (g := Complex.re) (x := p)
      Complex.continuous_re.continuousAt (by exact (jointChartArg_continuousAt (γ₀ := γ₀) (z₀ := z₀) reflect hγ₀ne).add (by dsimp [jointShiftN]; fun_prop))
  have hnear : ∀ᶠ q : ℝ × ℂ in 𝓝 p,
      0 < q.1 ∧ q.1 < 2 ∧ 0 < (W q).re ∧ (W q).re < Q q.1 := by
    have hWlo : ∀ᶠ q : ℝ × ℂ in 𝓝 p, 0 < (W q).re :=
      hWre.eventually (isOpen_Ioi.mem_nhds (by simpa [W, γ₀, z₀, jointShiftN_re,
        Complex.add_re] using hfinal0))
    have hWhi : ∀ᶠ q : ℝ × ℂ in 𝓝 p, 0 < Q q.1 - (W q).re :=
      (hQcont.sub hWre).eventually (isOpen_Ioi.mem_nhds (sub_pos.mpr (by
        simpa [W, γ₀, z₀, jointShiftN_re, Complex.add_re] using hfinalQ)))
    filter_upwards [(continuousAt_fst.eventually (isOpen_Ioi.mem_nhds hγ₀)), (continuousAt_fst.eventually (isOpen_Iio.mem_nhds (show γ₀ ∈ Iio 2 from hγ₀2))), hWlo, hWhi] with q hqlo hqhi hqWlo hqWhi
    exact ⟨hqlo, hqhi, hqWlo, by linarith⟩
  have hchart0 := jointShiftChart_continuousAt reflect n hγ₀ (by
    simpa [γ₀, z₀, jointShiftN_re, Complex.add_re] using And.intro hfinal0 hfinalQ)
  exact (hchart0.congr_of_eventuallyEq (by filter_upwards [hnear] with q hq; exact IsUpsilon.eq_jointShiftChart hq.1 hq.2.1 (hU q.1 ⟨hq.1, hq.2.1⟩) reflect n q.2 ⟨hq.2.2.1, hq.2.2.2⟩)).continuousWithinAt

end DOZZ.Proofs

end
