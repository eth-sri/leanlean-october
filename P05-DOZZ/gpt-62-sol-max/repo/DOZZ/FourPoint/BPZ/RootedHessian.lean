/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WirtingerMoment
public import DOZZ.FourPoint.Fusion.SpatialFunctions
public import DOZZ.Statements.FourPoint.GammaHalfRootKernelZ
public import DOZZ.Statements.FourPoint.GammaHalfRootKernelBar
public import DOZZ.Statements.FourPoint.GammaHalfTwoRootedP1

/-! # The `(1, 1)` entry of the expected second moment field of the degenerate mass

Take the degenerate charge `χ = γ/2`, so that `a = γχ/2 = γ²/4`, write `k` for the degenerate
four-point weight `bpzSoftWeight γ (γ/2) α₁ α₂ α₃ 0 u` (off `{0, 1}` it is the kernel
`gammaHalfKernel γ α₁ α₂ α₃ u`), `I = ∫ k dM` for its mass, `v = x - u` and `N = |v|²`. At
`ε = 0` and for a measure without atom at `u` the first and second derivative masses of the
softened mass, evaluated in the direction `1`, are given by the real parts of meromorphic
integrals. Indeed `-2a N^{a-1} Re v = -a (N^a / v + N^a / v̄)` and
`4a(a-1) N^{a-2} (Re v)² + 2a N^{a-1} = a(a-1) (N^a / v² + N^a / v̄²) + 2a² N^a / N`, so that

* `DI 1 = -a (Z + Z̄)` with `Z = ∫ k/(x - u)` and `Z̄ = conj Z`;
* `D²I 1 1 = a(a-1) (A + Ā) + 2a² B` with `A = ∫ k/(x - u)²` and `B = ∫ k/|x - u|²`.

Hence, pathwise, the `(1, 1)` entry of the second moment field
`s(s+1) I^{-s-2} DI ⊗ DI - s I^{-s-1} D²I` is the six-term expression
`-s a(a-1) I^{-s-1} (A + Ā) - 2s a² I^{-s-1} B + s(s+1) a² I^{-s-2} (Z² + 2 Z Z̄ + Z̄²)`
(`bpzRH_momField2_six`). Almost surely the Coulomb mass is the integral of `k` and `k` is the
kernel off the null set `{0, 1}`; each of the six terms is integrable (dominated by
`I^{-(s+1)} ∫ (1 + |x - u|^{-2}) k`, using the Cauchy–Schwarz bound for the squares), so the
expectation splits and gives `bpz_momField2_one_one_eq`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace DOZZ.Proofs

attribute [local instance low] bpzNormedAddCommGroupBilin bpzNormedSpaceBilin

/-! ### Pointwise identities for the derivative integrands -/

/-- Pointwise: the first derivative integrand at `ε = 0` in the direction `1`. -/
theorem bpzRH_softDeriv_one (a w : ℝ) {x z : ℂ} (hxz : x ≠ z) :
    ((w * bpzSoftDeriv a 0 x z 1 : ℝ) : ℂ) =
      -(a : ℂ) * (((Complex.normSq (x - z) ^ a * w : ℝ) : ℂ) / (x - z) +
        ((Complex.normSq (x - z) ^ a * w : ℝ) : ℂ) / conj (x - z)) := by
  have hv  := sub_ne_zero.mpr hxz
  have hN  := Complex.normSq_pos.mpr hv
  rw [bpzSoftDeriv_apply]
  simp only [Complex.one_re, Complex.one_im, mul_one, mul_zero, add_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  rw [Real.rpow_sub_one hN.ne']
  generalize x - z = v at *
  have hc : conj v ≠ 0 := (map_ne_zero _).mpr hv
  have hNc : ((Complex.normSq v : ℝ) : ℂ) = v * conj v := (Complex.mul_conj _).symm
  have hre : ((v.re : ℝ) : ℂ) = (v + conj v) / 2 := Complex.re_eq_add_conj _
  push_cast
  rw [hre, hNc]
  field_simp
  ring

/-- Pointwise: the second derivative integrand at `ε = 0` in the direction `(1, 1)`. -/
theorem bpzRH_softDeriv2_one_one (a w : ℝ) {x z : ℂ} (hxz : x ≠ z) :
    ((w * bpzSoftDeriv2 a 0 x z 1 1 : ℝ) : ℂ) =
      ((a * (a - 1) : ℝ) : ℂ) * (((Complex.normSq (x - z) ^ a * w : ℝ) : ℂ) / (x - z) ^ 2 +
        ((Complex.normSq (x - z) ^ a * w : ℝ) : ℂ) / conj (x - z) ^ 2) +
      ((2 * a ^ 2 : ℝ) : ℂ) * (((Complex.normSq (x - z) ^ a * w : ℝ) : ℂ) /
        ((‖x - z‖ ^ 2 : ℝ) : ℂ)) := by
  have hv  := sub_ne_zero.mpr hxz
  have hN  := Complex.normSq_pos.mpr hv
  rw [bpzSoftDeriv2_apply]
  simp only [Complex.one_re, Complex.one_im, mul_one, mul_zero, add_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  rw [Real.rpow_sub_one hN.ne', Real.rpow_sub hN, Real.rpow_two, ← Complex.normSq_eq_norm_sq]
  generalize x - z = v at *
  have hc : conj v ≠ 0 := (map_ne_zero _).mpr hv
  have hNc : ((Complex.normSq v : ℝ) : ℂ) = v * conj v := (Complex.mul_conj _).symm
  have hre : ((v.re : ℝ) : ℂ) = (v + conj v) / 2 := Complex.re_eq_add_conj _
  push_cast
  rw [hre, hNc]
  field_simp
  ring

/-! ### Conjugation and linearity of the expectation -/

/-- The complex conjugate of an integrable function is integrable. -/
theorem bpzRH_integrable_conj {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : Integrable f μ) : Integrable (fun x => conj (f x)) μ :=
  hf.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable hf.aestronglyMeasurable)
    (Eventually.of_forall fun x => (RCLike.norm_conj (f x)).le)

/-- The meromorphic terms of the Hessian, grouped with their conjugates. -/
noncomputable def bpzHessianCombination (a s : ℝ) (A B C D : ℂ) : ℂ :=
  let c₁ : ℂ := (-s * a * (a - 1) : ℝ)
  let c₂ : ℂ := (-2 * s * a ^ 2 : ℝ)
  let c₄ : ℂ := (s * (s + 1) * a ^ 2 : ℝ)
  let c₅ : ℂ := (2 * s * (s + 1) * a ^ 2 : ℝ)
  c₁ * A + c₂ * B + star (c₁ * A) + c₄ * C + c₅ * D + star (c₄ * C)

/-- Simultaneously scaling the inputs by a real weight scales the Hessian by that weight. -/
theorem bpzHessianCombination_mul (a s r : ℝ) (A B C D : ℂ) :
    (r : ℂ) * bpzHessianCombination a s A B C D =
      bpzHessianCombination a s (r * A) (r * B) (r * C) (r * D) := by
  simp only [bpzHessianCombination, Complex.star_def, map_mul, Complex.conj_ofReal]
  ring

/-- The Hessian combination commutes with expectation. -/
theorem integral_bpzHessianCombination {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {A B C D : Ω → ℂ}
    (hA : Integrable A P) (hB : Integrable B P) (hC : Integrable C P) (hD : Integrable D P)
    (a s : ℝ) :
    ∫ ω, bpzHessianCombination a s (A ω) (B ω) (C ω) (D ω) ∂P =
      bpzHessianCombination a s (∫ ω, A ω ∂P) (∫ ω, B ω ∂P)
        (∫ ω, C ω ∂P) (∫ ω, D ω ∂P) := by
  dsimp only [bpzHessianCombination]
  generalize ((-s * a * (a - 1) : ℝ) : ℂ) = c₁
  generalize ((-2 * s * a ^ 2 : ℝ) : ℂ) = c₂
  generalize ((s * (s + 1) * a ^ 2 : ℝ) : ℂ) = c₄
  generalize ((2 * s * (s + 1) * a ^ 2 : ℝ) : ℂ) = c₅
  have i₁ := hA.const_mul c₁
  have i₂ := hB.const_mul c₂
  have i₄ := hC.const_mul c₄
  have i₅ := hD.const_mul c₅
  have j₁ := bpzRH_integrable_conj i₁
  have j₄ := bpzRH_integrable_conj i₄
  have e₁₂ := integral_add i₁ i₂
  have e₃ := integral_add (i₁.add i₂) j₁
  have e₄ := integral_add ((i₁.add i₂).add j₁) i₄
  have e₅ := integral_add (((i₁.add i₂).add j₁).add i₄) i₅
  have e₆ := integral_add ((((i₁.add i₂).add j₁).add i₄).add i₅) j₄
  simp only [Pi.add_apply] at e₃ e₄ e₅ e₆
  simp only [Complex.star_def]
  rw [e₆, e₅, e₄, e₃, e₁₂, integral_conj, integral_conj]
  simp only [integral_const_mul]

/-! ### The pathwise six-term identity -/

section Pathwise

variable {a : ℝ} {w k : ℂ → ℝ} {m : Measure ℂ} {z : ℂ}

/-- `k / (x - z)` is integrable. -/
theorem bpzRH_integrable_div1 (H : BPZWMData a w k m z) :
    Integrable (fun x => ((k x : ℝ) : ℂ) / (x - z)) m := by
  have h := bpz_integrable_div_root H.hw H.hw0 H.hz (bpzWM_integrable_w1 H)
  simp only [bpzWM_normSq_eq H] at h
  refine h.neg.congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.neg_apply]
  rw [← neg_sub x z, div_neg, neg_neg]

/-- `k / conj (x - z)` is integrable. -/
theorem bpzRH_integrable_div1_conj (H : BPZWMData a w k m z) :
    Integrable (fun x => ((k x : ℝ) : ℂ) / conj (x - z)) m :=
  (bpzRH_integrable_conj (bpzRH_integrable_div1 H)).congr (Eventually.of_forall fun x => by
    simp)

/-- `k / (x - z)^2` is integrable. -/
theorem bpzRH_integrable_div2 (H : BPZWMData a w k m z) :
    Integrable (fun x => ((k x : ℝ) : ℂ) / (x - z) ^ 2) m := by
  have h := bpz_integrable_div_root_sq H.hw H.hw0 H.hz (bpzWM_integrable_w2 H)
  simp only [bpzWM_normSq_eq H] at h
  grind

/-- `k / conj (x - z)^2` is integrable. -/
theorem bpzRH_integrable_div2_conj (H : BPZWMData a w k m z) :
    Integrable (fun x => ((k x : ℝ) : ℂ) / conj (x - z) ^ 2) m :=
  (bpzRH_integrable_conj (bpzRH_integrable_div2 H)).congr (Eventually.of_forall fun x => by
    simp)

/-- The modulus of the mixed kernel `k / |x - z|²` is that of `k / (x - z)^2`. -/
theorem bpzRH_norm_mixed (x z : ℂ) (k : ℝ) :
    ‖(k : ℂ) / ((‖x - z‖ ^ 2 : ℝ) : ℂ)‖ = ‖(k : ℂ) / (x - z) ^ 2‖ := by
  simp

/-- `k / |x - z|²` is integrable. -/
theorem bpzRH_integrable_mixed (H : BPZWMData a w k m z) :
    Integrable (fun x => ((k x : ℝ) : ℂ) / ((‖x - z‖ ^ 2 : ℝ) : ℂ)) m := by
  refine (bpzRH_integrable_div2 H).mono ?_ (Eventually.of_forall fun x =>
    (bpzRH_norm_mixed x z (k x)).le)
  exact ((Complex.measurable_ofReal.comp (bpzWM_measurable_k H)).div
    (Complex.measurable_ofReal.comp
      ((measurable_id.sub_const z).norm.pow_const 2))).aestronglyMeasurable

/-- The first derivative mass at `ε = 0` evaluated in a direction. -/
theorem bpzRH_massDeriv_apply (H : BPZWMData a w k m z) (h : ℂ) :
    bpzSoftMassDeriv a 0 w m z h = ∫ x, w x * bpzSoftDeriv a 0 x z h ∂m := by
  have hI := bpz_integrable_softDeriv_zero H.ha H.ha1 H.hw H.hw0 H.hz (bpzWM_integrable_w1 H)
  unfold bpzSoftMassDeriv
  rw [ContinuousLinearMap.integral_apply hI h]
  rfl

/-- The second derivative mass at `ε = 0` evaluated in two directions. -/
theorem bpzRH_massDeriv2_apply (H : BPZWMData a w k m z) (h l : ℂ) :
    bpzSoftMassDeriv2 a 0 w m z h l = ∫ x, w x * bpzSoftDeriv2 a 0 x z h l ∂m := by
  have hI := bpz_integrable_softDeriv2_zero H.ha H.ha1 H.hw H.hw0 H.hz (bpzWM_integrable_w2 H)
  unfold bpzSoftMassDeriv2
  rw [ContinuousLinearMap.integral_apply hI h,
    ContinuousLinearMap.integral_apply (hI.apply_continuousLinearMap h) l]
  rfl

private theorem integral_div_pow_conj (k : ℂ → ℝ) (m : Measure ℂ) (z : ℂ) (n : ℕ) :
    ∫ x, (k x : ℂ) / conj (x - z) ^ n ∂m = conj (∫ x, (k x : ℂ) / (x - z) ^ n ∂m) := by
  rw [← integral_conj]
  simp only [map_div₀, map_pow, Complex.conj_ofReal]

/-- The first derivative mass in the direction `1` is `-a (Z + conj Z)`, `Z = ∫ k/(x - z)`. -/
theorem bpzRH_deriv_one_cast (H : BPZWMData a w k m z) :
    ((bpzSoftMassDeriv a 0 w m z 1 : ℝ) : ℂ) = -(a : ℂ) *
      ((∫ x, ((k x : ℝ) : ℂ) / (x - z) ∂m) + conj (∫ x, ((k x : ℝ) : ℂ) / (x - z) ∂m)) := by
  rw [bpzRH_massDeriv_apply H, ← integral_complex_ofReal, ← (by simpa only [pow_one] using integral_div_pow_conj k m z 1 :
      (∫ x, (k x : ℂ) / conj (x - z) ∂m) = conj (∫ x, (k x : ℂ) / (x - z) ∂m)),
    ← integral_add (bpzRH_integrable_div1 H) (bpzRH_integrable_div1_conj H),
    ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [bpz_ae_ne_of_measure_singleton H.hz] with x hx
  rw [bpzRH_softDeriv_one a (w x) hx, bpzWM_normSq_eq H x]

/-- The second derivative mass in the direction `(1, 1)` is `a(a-1) (A + conj A) + 2a² B`, with
`A = ∫ k/(x - z)²` and `B = ∫ k/|x - z|²`. -/
theorem bpzRH_deriv2_one_one_cast (H : BPZWMData a w k m z) :
    ((bpzSoftMassDeriv2 a 0 w m z 1 1 : ℝ) : ℂ) =
      ((a * (a - 1) : ℝ) : ℂ) * ((∫ x, ((k x : ℝ) : ℂ) / (x - z) ^ 2 ∂m) +
        conj (∫ x, ((k x : ℝ) : ℂ) / (x - z) ^ 2 ∂m)) +
      ((2 * a ^ 2 : ℝ) : ℂ) * ∫ x, ((k x : ℝ) : ℂ) / ((‖x - z‖ ^ 2 : ℝ) : ℂ) ∂m := by
  rw [bpzRH_massDeriv2_apply H, ← integral_complex_ofReal, ← integral_div_pow_conj,
    ← integral_add (bpzRH_integrable_div2 H) (bpzRH_integrable_div2_conj H),
    ← integral_const_mul, ← integral_const_mul, ← integral_add]
  · refine integral_congr_ae ?_
    filter_upwards [bpz_ae_ne_of_measure_singleton H.hz] with x hx
    rw [bpzRH_softDeriv2_one_one a (w x) hx, bpzWM_normSq_eq H x]
  · exact ((bpzRH_integrable_div2 H).add (bpzRH_integrable_div2_conj H)).const_mul _
  · exact (bpzRH_integrable_mixed H).const_mul _

/-- The second moment field in the direction `(1, 1)`. -/
theorem bpzRH_momField2_apply (a s : ℝ) (w : ℂ → ℝ) (m : Measure ℂ) (z : ℂ) :
    bpzMomField2 a s 0 w w m z 1 1 =
      s * (s + 1) * bpzSoftMassReal a 0 w m z ^ (-s - 2) *
          (bpzSoftMassDeriv a 0 w m z 1 * bpzSoftMassDeriv a 0 w m z 1) +
        -s * bpzSoftMassReal a 0 w m z ^ (-s - 1) * bpzSoftMassDeriv2 a 0 w m z 1 1 := by
  rfl

/-- The Hessian identity before averaging over the field. -/
theorem bpzRH_momField2_six (H : BPZWMData a w k m z) (s : ℝ) :
    let I := ∫ x, k x ∂m
    let Z := ∫ x, (k x : ℂ) / (x - z) ∂m
    (bpzMomField2 a s 0 w w m z 1 1 : ℂ) = bpzHessianCombination a s
      ((I ^ (-s - 1) : ℝ) * ∫ x, (k x : ℂ) / (x - z) ^ 2 ∂m)
      ((I ^ (-s - 1) : ℝ) * ∫ x, (k x : ℂ) / ((‖x - z‖ ^ 2 : ℝ) : ℂ) ∂m)
      ((I ^ (-s - 2) : ℝ) * Z ^ 2) ((I ^ (-s - 2) : ℝ) * Z * conj Z) := by
  dsimp only [bpzHessianCombination]
  rw [bpzRH_momField2_apply, bpzWM_softMassReal_eq H]
  have hD := bpzRH_deriv_one_cast H
  have hD2 := bpzRH_deriv2_one_one_cast H
  generalize (∫ x, ((k x : ℝ) : ℂ) / (x - z) ∂m) = Z at hD ⊢
  generalize (∫ x, ((k x : ℝ) : ℂ) / (x - z) ^ 2 ∂m) = A at hD2 ⊢
  generalize (∫ x, ((k x : ℝ) : ℂ) / ((‖x - z‖ ^ 2 : ℝ) : ℂ) ∂m) = B at hD2 ⊢
  generalize ((∫ x, k x ∂m) ^ (-s - 1) : ℝ) = I1
  generalize ((∫ x, k x ∂m) ^ (-s - 2) : ℝ) = I2
  generalize bpzSoftMassDeriv a 0 w m z 1 = D at *
  generalize bpzSoftMassDeriv2 a 0 w m z 1 1 = D2 at *
  simp only [Complex.star_def, map_mul, map_pow, Complex.conj_ofReal]
  push_cast at hD hD2 ⊢
  rw [hD, hD2]
  ring

/-- `|∫ k / |x - z|²| ≤ ∫ w |x - z|^{2a-2}`. -/
theorem bpzRH_norm_Jmixed_le (H : BPZWMData a w k m z) :
    ‖∫ x, ((k x : ℝ) : ℂ) / ((‖x - z‖ ^ 2 : ℝ) : ℂ) ∂m‖ ≤
      ∫ x, w x * ‖x - z‖ ^ (2 * a - 2) ∂m := by
  refine norm_integral_le_of_norm_le (bpzWM_integrable_w2 H) ?_
  filter_upwards [bpz_ae_ne_of_measure_singleton H.hz] with x hx
  have h := bpz_norm_div_root_pow a 2 (H.hw0 x) hx
  rw [bpzWM_normSq_eq H x] at h
  rw [bpzRH_norm_mixed, show (x - z) ^ 2 = (z - x) ^ 2 by ring]
  simpa using h.le

/-- The pathwise bound `|I^{-s-1} ∫ k/|x - z|²| ≤ I^{-(s+1)} ∫ (1 + |x - z|^{-2}) k`. -/
theorem bpzRH_norm_Tmixed_le (H : BPZWMData a w k m z) (s : ℝ) (hI : 0 < ∫ x, k x ∂m) :
    ‖(((∫ x, k x ∂m) ^ (-s - 1) : ℝ) : ℂ) *
        ∫ x, ((k x : ℝ) : ℂ) / ((‖x - z‖ ^ 2 : ℝ) : ℂ) ∂m‖ ≤
      (∫ x, k x ∂m) ^ (-(s + 1)) * ∫ x, (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x ∂m := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hI.le _),
    show -(s + 1) = -s - 1 by ring]
  exact mul_le_mul_of_nonneg_left ((bpzRH_norm_Jmixed_le H).trans (bpzWM_n2_le H))
    (Real.rpow_nonneg hI.le _)

end Pathwise

/-! ### The kernel and the Coulomb mass -/

section Kernel

variable {γ α₁ α₂ α₃ : ℝ}

/-- Off `{0, 1}` the degenerate weight at `χ = γ/2` is the kernel `gammaHalfKernel`. -/
theorem bpzRH_softWeight_eq_kernel (u : ℂ) {x : ℂ} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    bpzSoftWeight γ (γ / 2) α₁ α₂ α₃ 0 u x = gammaHalfKernel γ α₁ α₂ α₃ u x := by
  have h0  := norm_pos_iff.mpr hx0
  have h1  := norm_pos_iff.mpr (sub_ne_zero.mpr hx1)
  rw [bpzSoftWeight_zero]
  unfold bpzBaseWeight gammaHalfKernel
  rw [Real.rpow_neg h0.le, Real.rpow_neg h1.le, show γ * (γ / 2) = γ ^ 2 / 2 by ring]
  have e0 : ‖x‖ ^ (γ * α₁) ≠ 0 := (Real.rpow_pos_of_pos h0 _).ne'
  have e1 : ‖x - 1‖ ^ (γ * α₂) ≠ 0 := (Real.rpow_pos_of_pos h1 _).ne'
  field_simp

/-- Integrals against `gammaHalfKernel` are integrals against the degenerate weight, for a
measure without atoms at `0` and `1`. -/
theorem bpzRH_integral_kernel_eq {μ : Measure ℂ} (h0 : μ {0} = 0) (h1 : μ {1} = 0) (u : ℂ)
    (d : ℂ → ℂ) :
    ∫ x, (gammaHalfKernel γ α₁ α₂ α₃ u x : ℂ) / d x ∂μ =
      ∫ x, ((bpzSoftWeight γ (γ / 2) α₁ α₂ α₃ 0 u x : ℝ) : ℂ) / d x ∂μ := by
  refine integral_congr_ae ?_
  filter_upwards [bpz_ae_ne_of_measure_singleton h0, bpz_ae_ne_of_measure_singleton h1]
    with x hx0 hx1
  rw [bpzRH_softWeight_eq_kernel u hx0 hx1]

/-- For a measure without atoms at `u, 0, 1`, the Coulomb mass is the integral of the
degenerate weight. -/
theorem bpzRH_coulombMass_toReal {μ : Measure ℂ} {u : ℂ} (hu : μ {u} = 0) (h0 : μ {0} = 0)
    (h1 : μ {1} = 0) :
    (coulombMass γ μ ![-γ / 2, α₁, α₂] ![u, 0, 1] α₃).toReal =
      ∫ x, bpzSoftWeight γ (γ / 2) α₁ α₂ α₃ 0 u x ∂μ := by
  have h := coulombMass_eq_lintegral_bpzSoftWeight (γ := γ) (χ := γ / 2) (α₁ := α₁)
    (α₂ := α₂) (α₃ := α₃) μ u hu h0 h1
  rw [← neg_div] at h
  rw [h, ← bpzSoftI_eq_integral, bpzSoftI_eq_toReal]
  rfl

/-- The real powers of the Coulomb mass, for a measure without atoms at `u, 0, 1`. -/
theorem bpzRH_coulombMass_rpow_toReal {μ : Measure ℂ} {u : ℂ} (hu : μ {u} = 0) (h0 : μ {0} = 0)
    (h1 : μ {1} = 0) (r : ℝ) :
    ((coulombMass γ μ ![-γ / 2, α₁, α₂] ![u, 0, 1] α₃) ^ r).toReal =
      (∫ x, bpzSoftWeight γ (γ / 2) α₁ α₂ α₃ 0 u x ∂μ) ^ r := by
  rw [← ENNReal.toReal_rpow, bpzRH_coulombMass_toReal hu h0 h1]

/-- The root kernel integral `gammaHalfRootKernelZ` is `∫ k/(x - u)` for a measure without atoms
at `0` and `1`. -/
theorem bpzRH_Z_eq {Ω : Type*} {M : Ω → Measure ℂ} {ω : Ω} {u : ℂ} (h0 : M ω {0} = 0)
    (h1 : M ω {1} = 0) :
    gammaHalfRootKernelZ M γ α₁ α₂ α₃ ω u =
      ∫ x, ((bpzSoftWeight γ (γ / 2) α₁ α₂ α₃ 0 u x : ℝ) : ℂ) / (x - u) ∂M ω :=
  bpzRH_integral_kernel_eq h0 h1 u (fun x => x - u)

end Kernel

/-- The conjugate-root kernel integral is the conjugate of the root kernel integral. -/
theorem bpzRH_bar_eq_conj {Ω : Type*} (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ : ℝ) (ω : Ω) (z : ℂ) :
    gammaHalfRootKernelBar M γ α₁ α₂ α₃ ω z = conj (gammaHalfRootKernelZ M γ α₁ α₂ α₃ ω z) := by
  unfold gammaHalfRootKernelBar gammaHalfRootKernelZ
  rw [← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp

/-! ### Integrability of the six terms -/

section Integrability

variable {γ χ α₁ α₂ α₃ : ℝ}

/-- The root kernel integral `∫ k/(x - z) dM` is a measurable function of the chaos. -/
theorem bpzRH_measurable_Z {Ω : Type*} [MeasurableSpace Ω] {M : Ω → Measure ℂ}
    (hMm : Measurable M) {k : ℂ → ℝ} (hk : Measurable k) (z : ℂ) :
    Measurable (fun ω => ∫ x, ((k x : ℝ) : ℂ) / (x - z) ∂M ω) :=
  (bpz_stronglyMeasurable_integral_measure (f := fun x : ℂ => ((k x : ℝ) : ℂ) / (x - z))
    ((Complex.measurable_ofReal.comp hk).div
      (measurable_id.sub_const z)).stronglyMeasurable).measurable.comp hMm

/-- The mixed kernel integral `∫ k/|x - z|² dM` is a measurable function of the chaos. -/
theorem bpzRH_measurable_Jmixed {Ω : Type*} [MeasurableSpace Ω] {M : Ω → Measure ℂ}
    (hMm : Measurable M) {k : ℂ → ℝ} (hk : Measurable k) (z : ℂ) :
    Measurable (fun ω => ∫ x, ((k x : ℝ) : ℂ) / ((‖x - z‖ ^ 2 : ℝ) : ℂ) ∂M ω) :=
  (bpz_stronglyMeasurable_integral_measure
    (f := fun x : ℂ => ((k x : ℝ) : ℂ) / ((‖x - z‖ ^ 2 : ℝ) : ℂ))
    ((Complex.measurable_ofReal.comp hk).div (Complex.measurable_ofReal.comp
      ((measurable_id.sub_const z).norm.pow_const 2))).stronglyMeasurable).measurable.comp hMm

/-- `∫ k/(z - x) = -∫ k/(x - z)`. -/
theorem bpzRH_integral_div_neg (k : ℂ → ℝ) (m : Measure ℂ) (z : ℂ) :
    ∫ x, ((k x : ℝ) : ℂ) / (z - x) ∂m = -∫ x, ((k x : ℝ) : ℂ) / (x - z) ∂m := by
  rw [← integral_neg]
  grind

/-- `I^{-s-2} (∫ k/(x - z))²` is integrable. -/
theorem bpzRH_integrable_T2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (ha1 : γ * χ / 2 ≤ 1)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {s : ℝ} (hs : 0 ≤ s) {z : ℂ}
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    Integrable (fun ω =>
      (((∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^ (-s - 2) : ℝ) : ℂ) *
        (∫ x, ((bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x : ℝ) : ℂ) / (x - z) ∂M ω) ^ 2) P := by
  refine (bpzWM_integrable_T2 P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hs hz0 hz1).congr
    (Eventually.of_forall fun ω => ?_)
  simp only
  rw [bpzRH_integral_div_neg, neg_sq]

/-- `I^{-s-2} ∫ k/(x - z) · conj (∫ k/(x - z))` is integrable. -/
theorem bpzRH_integrable_T5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (ha1 : γ * χ / 2 ≤ 1)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {s : ℝ} (hs : 0 ≤ s) {z : ℂ}
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    Integrable (fun ω =>
      (((∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^ (-s - 2) : ℝ) : ℂ) *
        (∫ x, ((bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x : ℝ) : ℂ) / (x - z) ∂M ω) *
        conj (∫ x, ((bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x : ℝ) : ℂ) / (x - z) ∂M ω)) P := by
  have hT2 := bpzRH_integrable_T2 P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hs hz0 hz1
  have hkm := measurable_bpzSoftWeight (γ := γ) (χ := χ) (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) 0 z
  have hIm  :=
    (measurable_integral_measure hkm).comp hMm
  have hZ := bpzRH_measurable_Z hMm hkm z
  refine hT2.norm.mono' ?_ (Eventually.of_forall fun ω => ?_)
  · exact (((Complex.measurable_ofReal.comp (hIm.pow_const _)).mul hZ).mul
      (Complex.continuous_conj.measurable.comp hZ)).aestronglyMeasurable
  · simp only [norm_mul, RCLike.norm_conj, norm_pow]
    rw [mul_assoc, sq]

/-- `I^{-s-1} ∫ k/|x - z|²` is integrable. -/
theorem bpzRH_integrable_Tmixed {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (ha1 : γ * χ / 2 ≤ 1)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {s : ℝ} (hs : 0 ≤ s) {z : ℂ}
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    Integrable (fun ω =>
      (((∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^ (-s - 1) : ℝ) : ℂ) *
        ∫ x, ((bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x : ℝ) : ℂ) / ((‖x - z‖ ^ 2 : ℝ) : ℂ) ∂M ω) P := by
  have hdom := bpz_singular_dom_integrable (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) P X hX hγ hγ2 M hM
    hMm hχ hα₁ hα₂ hα₃ (q := s + 1) (by linarith) hz0 hz1
  have hkm := measurable_bpzSoftWeight (γ := γ) (χ := χ) (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) 0 z
  have hIm  :=
    (measurable_integral_measure hkm).comp hMm
  refine Integrable.mono' hdom ?_ ?_
  · exact ((Complex.measurable_ofReal.comp (hIm.pow_const _)).mul
      (bpzRH_measurable_Jmixed hMm hkm z)).aestronglyMeasurable
  · filter_upwards [bpzWM_good_ae P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hz0 hz1]
      with ω ⟨H, hI⟩
    exact bpzRH_norm_Tmixed_le H s hI

/-- `I^{-s-1} ∫ k/(x - z)²` is integrable. -/
theorem bpzRH_integrable_T1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (ha1 : γ * χ / 2 ≤ 1)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {s : ℝ} (hs : 0 ≤ s) {z : ℂ}
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    Integrable (fun ω =>
      (((∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^ (-s - 1) : ℝ) : ℂ) *
        ∫ x, ((bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x : ℝ) : ℂ) / (x - z) ^ 2 ∂M ω) P := by
  refine (bpzWM_integrable_T1 P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hs hz0 hz1).congr
    (Eventually.of_forall fun ω => ?_)
  simp only [show ∀ x : ℂ, (z - x) ^ 2 = (x - z) ^ 2 from fun x => by ring]

end Integrability

/-! ### The expected `(1, 1)` entry -/

/-- The Hessian computed from the four rooted expectations. -/
noncomputable def bpzRootedHessian {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ p : ℝ) (z : ℂ) : ℂ :=
  bpzHessianCombination (γ ^ 2 / 4) p
    (fusionPureSpatial P M γ α₁ α₂ α₃ p Set.univ z) (fusionMixedSpatial P M γ α₁ α₂ α₃ p Set.univ z)
    (gammaHalfTwoRootedSpatial false P M γ α₁ α₂ α₃ p z) (gammaHalfTwoRootedSpatial true P M γ α₁ α₂ α₃ p z)

/-- **The `(1, 1)` entry of the expected second moment field.** For the degenerate charge
`χ = γ/2` (so `a = γ²/4`) the `(1, 1)` entry of the expectation of the second moment field
`s(s+1) I^{-s-2} DI ⊗ DI - s I^{-s-1} D²I` of the softened mass at `ε = 0` is the six-term
combination of the fusion spatial expectations `fusionPureSpatial`, `fusionMixedSpatial`
(over the whole plane), the second-order moments of the root kernels `Z = gammaHalfRootKernelZ`,
`Z̄ = gammaHalfRootKernelBar`, and their conjugates. -/
theorem bpz_momField2_one_one_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (hMm : Measurable M) (α₁ α₂ α₃ : ℝ)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {p : ℝ} (hp : 0 ≤ p) {u : ℂ}
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    (((∫ ω, bpzMomField2 (γ * (γ / 2) / 2) p 0 (bpzBaseWeight γ (γ / 2) α₁ α₂ α₃)
        (bpzBaseWeight γ (γ / 2) α₁ α₂ α₃) (M ω) u ∂P) 1 1 : ℝ) : ℂ) =
      bpzRootedHessian P M γ α₁ α₂ α₃ p u := by
  have hχ : 0 < γ / 2 := by positivity
  have ha1 : γ * (γ / 2) / 2 ≤ 1 := by
    have h  := mul_le_mul hγ2.le hγ2.le hγ.le (by norm_num)
    linarith
  have hγ4 : γ ^ 2 / 4 = γ * (γ / 2) / 2 := by ring
  have hnoat := gmc_noAtoms_ae P X hX γ hγ hγ2 M hM hMm
  have hgood := bpzWM_good_ae P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hu0 hu1
  have hint := bpzWM_integrable_momField2 P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hp hu0 hu1
  have hL : ((∫ ω, bpzMomField2 (γ * (γ / 2) / 2) p 0 (bpzBaseWeight γ (γ / 2) α₁ α₂ α₃)
        (bpzBaseWeight γ (γ / 2) α₁ α₂ α₃) (M ω) u ∂P) 1 1 : ℝ) =
      ∫ ω, bpzMomField2 (γ * (γ / 2) / 2) p 0 (bpzBaseWeight γ (γ / 2) α₁ α₂ α₃)
        (bpzBaseWeight γ (γ / 2) α₁ α₂ α₃) (M ω) u 1 1 ∂P := by
    rw [ContinuousLinearMap.integral_apply hint 1,
      ContinuousLinearMap.integral_apply (hint.apply_continuousLinearMap 1) 1]
  rw [hL, ← integral_complex_ofReal]
  have h1c := bpzRH_integrable_T1 P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hp hu0 hu1
  have h2c := bpzRH_integrable_Tmixed P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hp hu0 hu1
  have h4c := bpzRH_integrable_T2 P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hp hu0 hu1
  have h5c := bpzRH_integrable_T5 P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hp hu0 hu1
  let I (e : ℝ) (ω : Ω) := ((coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![u, 0, 1] α₃ ^ e).toReal : ℂ)
  let J (d : ℂ → ℂ) (ω : Ω) := ∫ x, (gammaHalfKernel γ α₁ α₂ α₃ u x : ℂ) / d x ∂M ω
  let k := bpzSoftWeight γ (γ / 2) α₁ α₂ α₃ 0 u
  let A (ω : Ω) := I (-p - 1) ω * J (fun x => (x - u) ^ 2) ω
  let B (ω : Ω) := I (-p - 1) ω * J (fun x => (‖x - u‖ ^ 2 : ℝ)) ω
  let Z := fun ω => gammaHalfRootKernelZ M γ α₁ α₂ α₃ ω u
  let C (ω : Ω) := I (-p - 2) ω * Z ω ^ 2
  let D (ω : Ω) := I (-p - 2) ω * Z ω * gammaHalfRootKernelBar M γ α₁ α₂ α₃ ω u
  let W (e : ℝ) (ω : Ω) := (((∫ x, k x ∂M ω) ^ e : ℝ) : ℂ)
  let V (d : ℂ → ℂ) (ω : Ω) := ∫ x, (k x : ℂ) / d x ∂M ω
  have hI (ω : Ω) (hω : ∀ x, M ω {x} = 0) (e : ℝ) : I e ω = W e ω :=
    congrArg Complex.ofReal (bpzRH_coulombMass_rpow_toReal (hω u) (hω 0) (hω 1) e)
  have hJ (ω : Ω) (hω : ∀ x, M ω {x} = 0) (d : ℂ → ℂ) : J d ω = V d ω :=
    bpzRH_integral_kernel_eq (hω 0) (hω 1) u d
  have e₁ : A =ᵐ[P] fun ω => W (-p - 1) ω * V (fun x => (x - u) ^ 2) ω :=
    hnoat.mono fun ω hω => congrArg₂ (· * ·) (hI ω hω _) (hJ ω hω _)
  have e₂ : B =ᵐ[P] fun ω => W (-p - 1) ω * V (fun x => (‖x - u‖ ^ 2 : ℝ)) ω :=
    hnoat.mono fun ω hω => congrArg₂ (· * ·) (hI ω hω _) (hJ ω hω _)
  have e₄ : C =ᵐ[P] fun ω => W (-p - 2) ω * V (fun x => x - u) ω ^ 2 := by
    filter_upwards [hnoat] with ω hω
    change I (-p - 2) ω * Z ω ^ 2 = _
    rw [hI ω hω, show Z ω = V (fun x => x - u) ω from bpzRH_Z_eq (hω 0) (hω 1)]
  have e₅ : D =ᵐ[P] fun ω => W (-p - 2) ω * V (fun x => x - u) ω * conj (V (fun x => x - u) ω) := by
    filter_upwards [hnoat] with ω hω
    change I (-p - 2) ω * Z ω * gammaHalfRootKernelBar M γ α₁ α₂ α₃ ω u = _
    rw [hI ω hω, bpzRH_bar_eq_conj]
    simp only [Z, bpzRH_Z_eq (hω 0) (hω 1), V, k]
  have h1 : Integrable A P := h1c.congr e₁.symm
  have h2 : Integrable B P := h2c.congr e₂.symm
  have h4 : Integrable C P := h4c.congr e₄.symm
  have h5 : Integrable D P := h5c.congr e₅.symm
  have hae : (fun ω => (bpzMomField2 (γ * (γ / 2) / 2) p 0
      (bpzBaseWeight γ (γ / 2) α₁ α₂ α₃) (bpzBaseWeight γ (γ / 2) α₁ α₂ α₃) (M ω) u 1 1 : ℂ)) =ᵐ[P]
      fun ω => bpzHessianCombination (γ ^ 2 / 4) p (A ω) (B ω) (C ω) (D ω) := by
    filter_upwards [hgood, e₁, e₂, e₄, e₅] with ω ⟨H, _⟩ h₁ h₂ h₄ h₅
    rw [h₁, h₂, h₄, h₅, hγ4]
    exact bpzRH_momField2_six H p
  rw [integral_congr_ae hae, integral_bpzHessianCombination h1 h2 h4 h5]
  simp only [A, B, C, D, J, I, Z, bpzRootedHessian, gammaHalfTwoRootedSpatial, fusionPureSpatial, fusionMixedSpatial, fusionSecondSpatial, fusionSecondKernel,
    fusionSecondDenom, Bool.false_eq_true, ↓reduceIte, Measure.restrict_univ]

end DOZZ.Proofs
