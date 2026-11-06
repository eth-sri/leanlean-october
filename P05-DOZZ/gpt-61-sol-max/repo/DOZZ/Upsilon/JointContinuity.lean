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

private theorem jointShiftN_re (γ : ℝ) (n : ℕ) :
    (jointShiftN γ n).re = (n : ℝ) * (γ / 2) := by
  simp [jointShiftN]

private theorem jointShiftN_succ (γ : ℝ) (n : ℕ) :
    jointShiftN γ (n + 1) = jointShiftN γ n + (γ / 2 : ℝ) := by
  simp [jointShiftN, Nat.cast_add]
  ring

private theorem exists_shift_into_strip {γ : ℝ} (hγ : 0 < γ)
    {x : ℝ} (hxQ : x < Q γ) :
    ∃ n : ℕ, 0 < x + (n : ℝ) * (γ / 2) ∧ x + (n : ℝ) * (γ / 2) < Q γ := by
  have hb : 0 < γ / 2 := by positivity
  have hbQ : γ / 2 < Q γ := by
    unfold Q
    simp_all
  by_cases hx : 0 < x
  · exact ⟨0, by simpa, by simpa using hxQ⟩
  ·
    let y := -x / (γ / 2)
    have hy0 : 0 ≤ y := by bound
    let N := Nat.floor y
    let n := N + 1
    have hfloor  := Nat.floor_le hy0
    have hfloorlt  := Nat.lt_floor_add_one y
    have hnlt : y < (n : ℝ) := by simpa [n] using hfloorlt
    have hne : y * (γ / 2) = -x := by
      dsimp [y]
      field_simp [ne_of_gt hb]
    have hlow : 0 < x + (n : ℝ) * (γ / 2) := by
      nlinarith
    have hnle : (n : ℝ) ≤ y + 1 := by
      continuity
    have hupp : x + (n : ℝ) * (γ / 2) ≤ γ / 2 := by
      nlinarith
    exact ⟨n, hlow, lt_of_le_of_lt hupp hbQ⟩

variable {γ : ℝ} {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2) (hU : IsUpsilon γ U)

include γ U hγ hγ2 hU in
private theorem IsUpsilon.eq_shiftChain
    (w : ℂ) (n : ℕ) (hfinal :
      0 < (w + jointShiftN γ n).re ∧ (w + jointShiftN γ n).re < Q γ) :
    U w = jointShiftChain γ n w * U (w + jointShiftN γ n) := by
  induction n generalizing w with
  | zero => simp [jointShiftN, jointShiftChain]
  | succ n ih =>
      have hfinalEq : w + jointShiftN γ (n + 1) =
          (w + (γ / 2 : ℝ)) + jointShiftN γ n := by
        rw [jointShiftN_succ]
        abel
      have hfinal' : 0 < ((w + (γ / 2 : ℝ)) + jointShiftN γ n).re ∧
          ((w + (γ / 2 : ℝ)) + jointShiftN γ n).re < Q γ := by
        rw [← hfinalEq]
        exact hfinal
      have hfinalRe : (w + jointShiftN γ (n + 1)).re =
          w.re + (n + 1 : ℝ) * (γ / 2) := by
        simp [Complex.add_re, jointShiftN_re]
      have hstepLen : γ / 2 ≤ (n + 1 : ℝ) * (γ / 2) := by
        simp_all
      have hQb : Q γ - γ / 2 = 2 / γ := by unfold Q; ring
      have hw : w.re < 2 / γ := by
        linarith
      have hrec := IsUpsilon.shift_b_reciprocal hγ hγ2 hU w hw
      have hrest := ih (w + (γ / 2 : ℝ)) hfinal'
      have hShiftArg : w + (γ / 2 : ℝ) = w + (γ / 2 : ℂ) := by
        push_cast
        ring
      rw [hShiftArg] at hrest
      rw [hrest] at hrec
      simpa [jointShiftChain, jointShiftFactor, hfinalEq, mul_assoc] using hrec.symm

private theorem jointShiftFactor_continuousAt {γ₀ : ℝ} {w₀ : ℂ}
    (hγ₀ : 0 < γ₀) (hw₀ : w₀.re < 2 / γ₀) :
    ContinuousAt (fun p : ℝ × ℂ => jointShiftFactor p.1 p.2) (γ₀, w₀) := by
  let b : ℝ × ℂ → ℂ := fun p => ((p.1 / 2 : ℝ) : ℂ)
  let γC : ℝ × ℂ → ℂ := fun p => (p.1 : ℂ)
  let arg₁  := fun p => 1 - b p * p.2
  let arg₂  := fun p => b p * p.2
  let exponent  := fun p => γC p * p.2 - 1
  have hb : ContinuousAt b (γ₀, w₀) := by fun_prop
  have hγC : ContinuousAt γC (γ₀, w₀) := by fun_prop

  have hbase : b (γ₀, w₀) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    simp [b]
    positivity
  have hexp : ContinuousAt exponent (γ₀, w₀) := by
    fun_prop (disch := positivity)
  have hpow  :=
    hb.cpow hexp hbase

  have hscale : (γ₀ / 2) * w₀.re < 1 := by
    field_simp at * <;> nlinarith
  have harg₁re : 0 < (arg₁ (γ₀, w₀)).re := by
    continuity
  have harg₁ : ContinuousAt arg₁ (γ₀, w₀) := by fun_prop
  have hGamma0 : ContinuousAt Complex.Gamma (arg₁ (γ₀, w₀)) :=
    Complex.continuousAt_Gamma _ (by
      intro m hm
      apply Complex.Gamma_ne_zero_of_re_pos harg₁re
      grind)
  have hGamma  :=
    hGamma0.comp harg₁
  have harg₂ : ContinuousAt arg₂ (γ₀, w₀) := by fun_prop
  have hInv0  :=
    (Complex.differentiable_one_div_Gamma (arg₂ (γ₀, w₀))).continuousAt
  have hInv  :=
    hInv0.comp harg₂
  exact (hpow.mul hGamma).mul hInv

private theorem jointShiftChain_continuousAt {γ₀ : ℝ} {w₀ : ℂ}
    (hγ₀ : 0 < γ₀) (n : ℕ)
    (hstep : ∀ j : ℕ, j < n → (w₀ + jointShiftN γ₀ j).re < 2 / γ₀) :
    ContinuousAt (fun p : ℝ × ℂ => jointShiftChain p.1 n p.2) (γ₀, w₀) := by
  induction n generalizing w₀ with
  | zero => exact (continuousAt_const : ContinuousAt (fun _ : ℝ × ℂ => (1 : ℂ)) (γ₀, w₀))
  | succ n ih =>
      have hstep0 : w₀.re < 2 / γ₀ := by simpa [jointShiftN] using hstep 0 (by omega)
      have hstep' : ∀ j : ℕ, j < n →
          ((w₀ + (γ₀ / 2 : ℝ)) + jointShiftN γ₀ j).re < 2 / γ₀ := by
        intro j hj
        have h := hstep (j + 1) (by omega)
        have heq : (w₀ + (γ₀ / 2 : ℝ)) + jointShiftN γ₀ j =
            w₀ + jointShiftN γ₀ (j + 1) := by
          rw [jointShiftN_succ]
          abel
        rw [← heq] at h
        exact h
      have hfactor  := jointShiftFactor_continuousAt hγ₀ hstep0

      have hrest : ContinuousAt (fun p : ℝ × ℂ =>
          jointShiftChain p.1 n (p.2 + (p.1 / 2 : ℝ))) (γ₀, w₀) := by
        fun_prop
      exact hfactor.mul hrest

private noncomputable def jointChartArg (reflect : Bool) (p : ℝ × ℂ) : ℂ :=
  if reflect then (Q p.1 : ℂ) - p.2 else p.2

private noncomputable def jointShiftChart (reflect : Bool) (n : ℕ)
    (p : ℝ × ℂ) : ℂ :=
  jointShiftChain p.1 n (jointChartArg reflect p) *
    Complex.exp (upsilonLog p.1 (jointChartArg reflect p + jointShiftN p.1 n))

private theorem jointChartArg_continuousAt {γ₀ : ℝ} {z₀ : ℂ} (reflect : Bool)
    (hγ₀ : γ₀ ≠ 0) :
    ContinuousAt (jointChartArg reflect) (γ₀, z₀) := by
  cases reflect
  · exact continuousAt_snd
  · have hQ : ContinuousAt (fun p : ℝ × ℂ => (Q p.1 : ℂ)) (γ₀, z₀) := by
      have hQ' : ContinuousAt (fun p : ℝ × ℂ => Q p.1) (γ₀, z₀) := by
        have hQγ : ContinuousAt Q γ₀ := by
          fun_prop (disch := assumption) [Q]
        fun_prop (disch := positivity)
      fun_prop
    exact hQ.sub continuousAt_snd

private theorem jointShiftChart_continuousAt {γ₀ : ℝ} {z₀ : ℂ}
    (reflect : Bool) (n : ℕ) (hγ₀ : 0 < γ₀)
    (hfinal : 0 < (jointChartArg reflect (γ₀, z₀) + jointShiftN γ₀ n).re ∧
      (jointChartArg reflect (γ₀, z₀) + jointShiftN γ₀ n).re < Q γ₀) :
    ContinuousAt (jointShiftChart reflect n) (γ₀, z₀) := by
  let w₀ := jointChartArg reflect (γ₀, z₀)
  let v₀ := w₀ + jointShiftN γ₀ n
  have hγ₀ne  := hγ₀.ne'
  have hArg : ContinuousAt (jointChartArg reflect) (γ₀, z₀) :=
    jointChartArg_continuousAt reflect hγ₀ne
  have hN : ContinuousAt (fun p : ℝ × ℂ => jointShiftN p.1 n) (γ₀, z₀) := by
    dsimp [jointShiftN]
    fun_prop
  have hW  := hArg.add hN

  have hstep : ∀ j : ℕ, j < n → (w₀ + jointShiftN γ₀ j).re < 2 / γ₀ := by
    intro j hj
    have hjn : (j : ℝ) + 1 ≤ (n : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hj)

    have hmon : (j : ℝ) * (γ₀ / 2) + γ₀ / 2 ≤ (n : ℝ) * (γ₀ / 2) := by
      nlinarith
    have hfinalRe : v₀.re = w₀.re + (n : ℝ) * (γ₀ / 2) := by
      simp [v₀, Complex.add_re, jointShiftN_re]
    have hstepRe : (w₀ + jointShiftN γ₀ j).re =
        w₀.re + (j : ℝ) * (γ₀ / 2) := by
      simp [Complex.add_re, jointShiftN_re]
    rw [hstepRe]
    have hQminus : Q γ₀ - γ₀ / 2 = 2 / γ₀ := by
      unfold Q
      ring
    grind
  have hChainOuter  :=
    jointShiftChain_continuousAt hγ₀ n hstep

  have hChain : ContinuousAt (fun p : ℝ × ℂ =>
      jointShiftChain p.1 n (jointChartArg reflect p)) (γ₀, z₀) := by
    fun_prop
  have hQ : ContinuousAt (fun p : ℝ × ℂ => Q p.1) (γ₀, z₀) := by
    have hQγ : ContinuousAt Q γ₀ := by
      fun_prop (disch := assumption) [Q]
    fun_prop (disch := positivity)
  have hWre  :=
    ContinuousAt.comp (f := fun p : ℝ × ℂ =>
      jointChartArg reflect p + jointShiftN p.1 n) (g := Complex.re)
      (x := (γ₀, z₀)) Complex.continuous_re.continuousAt hW

  have hLogOuter  :=
    upsilonLog_continuousAt_joint hγ₀ hfinal.1 hfinal.2

  have hLog : ContinuousAt (fun p : ℝ × ℂ =>
      upsilonLog p.1 (jointChartArg reflect p + jointShiftN p.1 n)) (γ₀, z₀) := by
    fun_prop
  exact hChain.mul (continuous_exp.continuousAt.comp hLog)

include γ U hγ hγ2 hU in
private theorem IsUpsilon.eq_jointShiftChart
    (reflect : Bool) (n : ℕ) (z : ℂ)
    (hfinal : 0 < (jointChartArg reflect (γ, z) + jointShiftN γ n).re ∧
      (jointChartArg reflect (γ, z) + jointShiftN γ n).re < Q γ) :
    U z = jointShiftChart reflect n (γ, z) := by
  cases reflect with
  | false =>
      have hchain := IsUpsilon.eq_shiftChain hγ hγ2 hU z n (hfinal)
      have hstrip := hU.2 (z + jointShiftN γ n) hfinal.1 hfinal.2
      aesop
  | true =>
      let w := (Q γ : ℂ) - z
      have hreflect  := id (Eq.symm (reflect hγ hγ2 hU z))
      have hchain := IsUpsilon.eq_shiftChain hγ hγ2 hU w n (hfinal)
      have hstrip := hU.2 (w + jointShiftN γ n) hfinal.1 hfinal.2
      aesop

/-- Joint continuity of `Υ_{γ/2}(z)` in `(γ, z)` (see the continuity arguments in [KRV, §10.6] and
[KRV, §11]). -/
theorem IsUpsilon.continuousOn_uncurry {U : ℝ → ℂ → ℂ}
    (hU : ∀ γ ∈ Ioo (0 : ℝ) 2, IsUpsilon γ (U γ)) :
    ContinuousOn (Function.uncurry U) (Ioo 0 2 ×ˢ univ) := by
  intro p hp
  rcases hp with ⟨hγp, _⟩
  rcases hγp with ⟨hγlo, hγhi⟩
  let γ₀ := p.1
  let z₀ := p.2
  have hγ₀  := hγlo
  have hγ₀2  := hγhi
  have hγ₀ne  := hγ₀.ne'

  let reflect := if z₀.re < Q γ₀ then false else true
  have hxQ : (jointChartArg reflect p).re < Q γ₀ := by
    by_cases h : z₀.re < Q γ₀
    · simp [reflect, h, jointChartArg, γ₀, z₀]
    ·
      have hQpos : 0 < Q γ₀ := by
        unfold Q
        positivity
      simp only [reflect, h, jointChartArg, γ₀, z₀, ite_false, ite_true,
        Complex.sub_re, Complex.ofReal_re]
      linarith
  obtain ⟨n, hfinal0, hfinalQ⟩ := exists_shift_into_strip hγ₀ hxQ
  let W  := fun q => jointChartArg reflect q + jointShiftN q.1 n
  have hWcont : ContinuousAt W p := by
    have hA := jointChartArg_continuousAt (γ₀ := γ₀) (z₀ := z₀) reflect hγ₀ne
    have hN : ContinuousAt (fun q : ℝ × ℂ => jointShiftN q.1 n) p := by
      dsimp [jointShiftN]
      fun_prop
    exact hA.add hN
  have hQcont : ContinuousAt (fun q : ℝ × ℂ => Q q.1) p := by
    have hQγ : ContinuousAt Q γ₀ := by
      fun_prop (disch := assumption) [Q]
    fun_prop (disch := positivity)
  have hWre  :=
    ContinuousAt.comp (f := W) (g := Complex.re) (x := p)
      Complex.continuous_re.continuousAt hWcont
  have hGapcont  :=
    hQcont.sub hWre
  have hnear : ∀ᶠ q : ℝ × ℂ in 𝓝 p,
      0 < q.1 ∧ q.1 < 2 ∧ 0 < (W q).re ∧ (W q).re < Q q.1 := by
    have hlo  :=
      continuousAt_fst.eventually (isOpen_Ioi.mem_nhds hγ₀)
    have hhi  :=
      continuousAt_fst.eventually (isOpen_Iio.mem_nhds (show γ₀ ∈ Iio 2 from hγ₀2))
    have hWlo  :=
      hWre.eventually (isOpen_Ioi.mem_nhds (by simpa [W, γ₀, z₀, jointShiftN_re,
        Complex.add_re] using hfinal0))
    have hWhi  :=
      hGapcont.eventually (isOpen_Ioi.mem_nhds (sub_pos.mpr (by
        simpa [W, γ₀, z₀, jointShiftN_re, Complex.add_re] using hfinalQ)))
    simp_all
  have hchart0 := jointShiftChart_continuousAt reflect n hγ₀ (by
    simpa [γ₀, z₀, jointShiftN_re, Complex.add_re] using And.intro hfinal0 hfinalQ)
  have heq : Function.uncurry U =ᶠ[𝓝 p] jointShiftChart reflect n := by
    filter_upwards [hnear] with q hq
    have hUq  := hU q.1 ⟨hq.1, hq.2.1⟩
    exact IsUpsilon.eq_jointShiftChart hq.1 hq.2.1 hUq reflect n q.2 ⟨hq.2.2.1, hq.2.2.2⟩
  have hAt  := hchart0.congr_of_eventuallyEq heq
  exact hAt.continuousWithinAt

end DOZZ.Proofs

end
