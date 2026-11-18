/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WirtingerMoment
public import DOZZ.FourPoint.Fusion.SpatialFunctions
public import DOZZ.Statements.FourPoint.GammaHalfRootKernelZ
public import DOZZ.Statements.FourPoint.GammaHalfRootKernelBar

/-! # The `(1, 1)` entry of the expected second moment field of the degenerate mass -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace DOZZ.Proofs

attribute [local instance low] bpzNormedAddCommGroupBilin bpzNormedSpaceBilin

private lemma integrable_conj {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : Integrable f μ) : Integrable (fun x => conj (f x)) μ :=
  hf.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable hf.aestronglyMeasurable)
    (Eventually.of_forall fun x => (RCLike.norm_conj (f x)).le)



/-- **The `(1, 1)` entry of the expected second moment field.** -/
theorem bpz_momField2_one_one_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (hMm : Measurable M) (α₁ α₂ α₃ : ℝ)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {p : ℝ} (hp : 0 ≤ p) {u : ℂ}
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    (((∫ ω, bpzMomField2 (γ * (γ / 2) / 2) p 0 (bpzBaseWeight γ (γ / 2) α₁ α₂ α₃)
        (bpzBaseWeight γ (γ / 2) α₁ α₂ α₃) (M ω) u ∂P) 1 1 : ℝ) : ℂ) =
      ((-p * (γ ^ 2 / 4) * (γ ^ 2 / 4 - 1) : ℝ) : ℂ) *
          fusionPureSpatial P M γ α₁ α₂ α₃ p Set.univ u +
        ((-2 * p * (γ ^ 2 / 4) ^ 2 : ℝ) : ℂ) * fusionMixedSpatial P M γ α₁ α₂ α₃ p Set.univ u +
        star (((-p * (γ ^ 2 / 4) * (γ ^ 2 / 4 - 1) : ℝ) : ℂ) *
          fusionPureSpatial P M γ α₁ α₂ α₃ p Set.univ u) +
        ((p * (p + 1) * (γ ^ 2 / 4) ^ 2 : ℝ) : ℂ) *
          (∫ ω, ((ENNReal.rpow (coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![u, 0, 1] α₃)
            (-p - 2)).toReal : ℂ) * gammaHalfRootKernelZ M γ α₁ α₂ α₃ ω u ^ 2 ∂P) +
        ((2 * p * (p + 1) * (γ ^ 2 / 4) ^ 2 : ℝ) : ℂ) *
          (∫ ω, ((ENNReal.rpow (coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![u, 0, 1] α₃)
            (-p - 2)).toReal : ℂ) * gammaHalfRootKernelZ M γ α₁ α₂ α₃ ω u *
              gammaHalfRootKernelBar M γ α₁ α₂ α₃ ω u ∂P) +
        star (((p * (p + 1) * (γ ^ 2 / 4) ^ 2 : ℝ) : ℂ) *
          (∫ ω, ((ENNReal.rpow (coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![u, 0, 1] α₃)
            (-p - 2)).toReal : ℂ) * gammaHalfRootKernelZ M γ α₁ α₂ α₃ ω u ^ 2 ∂P)) := by
  have momField2_six {a : ℝ} {w k : ℂ → ℝ} {m : Measure ℂ} {z : ℂ} (H : BPZWMData a w k m z) (s : ℝ) : ((bpzMomField2 a s 0 w w m z 1 1 : ℝ) : ℂ) =
        ((-s * a * (a - 1) : ℝ) : ℂ) * ((((∫ x, k x ∂m) ^ (-s - 1) : ℝ) : ℂ) *
            ∫ x, ((k x : ℝ) : ℂ) / (x - z) ^ 2 ∂m) +
        ((-2 * s * a ^ 2 : ℝ) : ℂ) * ((((∫ x, k x ∂m) ^ (-s - 1) : ℝ) : ℂ) *
            ∫ x, ((k x : ℝ) : ℂ) / ((‖x - z‖ ^ 2 : ℝ) : ℂ) ∂m) +
        star (((-s * a * (a - 1) : ℝ) : ℂ) * ((((∫ x, k x ∂m) ^ (-s - 1) : ℝ) : ℂ) *
            ∫ x, ((k x : ℝ) : ℂ) / (x - z) ^ 2 ∂m)) +
        ((s * (s + 1) * a ^ 2 : ℝ) : ℂ) * ((((∫ x, k x ∂m) ^ (-s - 2) : ℝ) : ℂ) *
            (∫ x, ((k x : ℝ) : ℂ) / (x - z) ∂m) ^ 2) +
        ((2 * s * (s + 1) * a ^ 2 : ℝ) : ℂ) * ((((∫ x, k x ∂m) ^ (-s - 2) : ℝ) : ℂ) *
            (∫ x, ((k x : ℝ) : ℂ) / (x - z) ∂m) * conj (∫ x, ((k x : ℝ) : ℂ) / (x - z) ∂m)) +
        star (((s * (s + 1) * a ^ 2 : ℝ) : ℂ) * ((((∫ x, k x ∂m) ^ (-s - 2) : ℝ) : ℂ) *
            (∫ x, ((k x : ℝ) : ℂ) / (x - z) ∂m) ^ 2)) := by
    have idiv1 : Integrable (fun x => ((k x : ℝ) : ℂ) / (x - z)) m := by
      have h := bpz_integrable_div_root H.hw H.hw0 H.hz (bpzWM_integrable_w1 H)
      simp only [bpzWM_normSq_eq H] at h
      exact h.neg.congr (Eventually.of_forall fun x => by rw [Pi.neg_apply, ← neg_sub x z, div_neg, neg_neg])
    have idiv1c : Integrable (fun x => ((k x : ℝ) : ℂ) / conj (x - z)) m :=
      (integrable_conj idiv1).congr (Eventually.of_forall fun x => by simp only [map_div₀, Complex.conj_ofReal])
    have idiv2 : Integrable (fun x => ((k x : ℝ) : ℂ) / (x - z) ^ 2) m := by
      have h := bpz_integrable_div_root_sq H.hw H.hw0 H.hz (bpzWM_integrable_w2 H)
      simp only [bpzWM_normSq_eq H] at h
      exact h.congr (Eventually.of_forall fun x => by ring)
    have idiv2c : Integrable (fun x => ((k x : ℝ) : ℂ) / conj (x - z) ^ 2) m :=
      (integrable_conj idiv2).congr (Eventually.of_forall fun x => by simp only [map_div₀, map_pow, Complex.conj_ofReal])
    have imix : Integrable (fun x => ((k x : ℝ) : ℂ) / ((‖x - z‖ ^ 2 : ℝ) : ℂ)) m :=
      idiv2.mono (((Complex.measurable_ofReal.comp (bpzWM_measurable_k H)).div
        (Complex.measurable_ofReal.comp ((measurable_id.sub_const z).norm.pow_const 2))).aestronglyMeasurable)
        (Eventually.of_forall fun x => by simp)
    have hD : ((bpzSoftMassDeriv a 0 w m z 1 : ℝ) : ℂ) = -(a : ℂ) *
        ((∫ x, ((k x : ℝ) : ℂ) / (x - z) ∂m) + conj (∫ x, ((k x : ℝ) : ℂ) / (x - z) ∂m)) := by
      unfold bpzSoftMassDeriv
      rw [ContinuousLinearMap.integral_apply
          (bpz_integrable_softDeriv_zero H.ha H.ha1 H.hw H.hw0 H.hz (bpzWM_integrable_w1 H)) 1,
        ← integral_complex_ofReal, ← integral_conj,
        show (∫ x, conj (((k x : ℝ) : ℂ) / (x - z)) ∂m) = ∫ x, ((k x : ℝ) : ℂ) / conj (x - z) ∂m from
          integral_congr_ae (Eventually.of_forall fun x => by simp only [map_div₀, Complex.conj_ofReal]),
        ← integral_add idiv1 idiv1c, ← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [bpz_ae_ne_of_measure_singleton H.hz] with x hx
      have hv := sub_ne_zero.mpr hx
      rw [← bpzWM_normSq_eq H x]
      change ((w x * bpzSoftDeriv a 0 x z 1 : ℝ) : ℂ) = _
      rw [bpzSoftDeriv_apply]
      simp only [Complex.one_re, Complex.one_im, mul_one, mul_zero, add_zero, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      rw [Real.rpow_sub_one (Complex.normSq_pos.mpr hv).ne']
      generalize x - z = v at *
      have hcj : conj v ≠ 0 := (map_ne_zero _).mpr hv
      push_cast
      rw [Complex.re_eq_add_conj v, (Complex.mul_conj v).symm]
      field_simp [hv, hcj]; ring
    have hD2 : ((bpzSoftMassDeriv2 a 0 w m z 1 1 : ℝ) : ℂ) =
        ((a * (a - 1) : ℝ) : ℂ) * ((∫ x, ((k x : ℝ) : ℂ) / (x - z) ^ 2 ∂m) +
          conj (∫ x, ((k x : ℝ) : ℂ) / (x - z) ^ 2 ∂m)) +
        ((2 * a ^ 2 : ℝ) : ℂ) * ∫ x, ((k x : ℝ) : ℂ) / ((‖x - z‖ ^ 2 : ℝ) : ℂ) ∂m := by
      have hI := bpz_integrable_softDeriv2_zero H.ha H.ha1 H.hw H.hw0 H.hz (bpzWM_integrable_w2 H)
      have idiv2_sum : Integrable (fun x => ((k x : ℝ) : ℂ) / (x - z) ^ 2 + ((k x : ℝ) : ℂ) / conj (x - z) ^ 2) m :=
        idiv2.add idiv2c
      unfold bpzSoftMassDeriv2
      rw [ContinuousLinearMap.integral_apply hI 1,
        ContinuousLinearMap.integral_apply (hI.apply_continuousLinearMap 1) 1,
        ← integral_complex_ofReal, ← integral_conj,
        show (∫ x, conj (((k x : ℝ) : ℂ) / (x - z) ^ 2) ∂m) = ∫ x, ((k x : ℝ) : ℂ) / conj (x - z) ^ 2 ∂m from
          integral_congr_ae (Eventually.of_forall fun x => by simp only [map_div₀, map_pow, Complex.conj_ofReal]),
        ← integral_add idiv2 idiv2c, ← integral_const_mul, ← integral_const_mul,
        ← integral_add (idiv2_sum.const_mul _) (imix.const_mul _)]
      refine integral_congr_ae ?_
      filter_upwards [bpz_ae_ne_of_measure_singleton H.hz] with x hx
      have hv := sub_ne_zero.mpr hx
      have hN := Complex.normSq_pos.mpr hv
      rw [← bpzWM_normSq_eq H x]
      change ((w x * bpzSoftDeriv2 a 0 x z 1 1 : ℝ) : ℂ) = _
      rw [bpzSoftDeriv2_apply]
      simp only [Complex.one_re, Complex.one_im, mul_one, mul_zero, add_zero, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      rw [Real.rpow_sub_one hN.ne', Real.rpow_sub hN, Real.rpow_two, ← Complex.normSq_eq_norm_sq]
      generalize x - z = v at *
      have hcj : conj v ≠ 0 := (map_ne_zero _).mpr hv
      push_cast
      rw [Complex.re_eq_add_conj v, (Complex.mul_conj v).symm]
      field_simp [hv, hcj]; ring
    change ((s * (s + 1) * bpzSoftMassReal a 0 w m z ^ (-s - 2) *
        (bpzSoftMassDeriv a 0 w m z 1 * bpzSoftMassDeriv a 0 w m z 1) +
      -s * bpzSoftMassReal a 0 w m z ^ (-s - 1) * bpzSoftMassDeriv2 a 0 w m z 1 1 : ℝ) : ℂ) = _
    rw [bpzWM_softMassReal_eq H]
    generalize (∫ x, ((k x : ℝ) : ℂ) / (x - z) ∂m) = Z at hD ⊢
    generalize (∫ x, ((k x : ℝ) : ℂ) / (x - z) ^ 2 ∂m) = A at hD2 ⊢
    generalize (∫ x, ((k x : ℝ) : ℂ) / ((‖x - z‖ ^ 2 : ℝ) : ℂ) ∂m) = B at hD2 ⊢
    generalize ((∫ x, k x ∂m) ^ (-s - 1) : ℝ) = I1
    generalize ((∫ x, k x ∂m) ^ (-s - 2) : ℝ) = I2
    generalize bpzSoftMassDeriv a 0 w m z 1 = D at *
    generalize bpzSoftMassDeriv2 a 0 w m z 1 1 = D2 at *
    simp only [Complex.star_def, map_mul, map_pow, Complex.conj_ofReal]
    push_cast at hD hD2 ⊢
    rw [hD, hD2]; ring
  have integral_six {P : Measure Ω} {g1 g2 g4 g5 : Ω → ℂ} (h1 : Integrable g1 P) (h2 : Integrable g2 P) (h4 : Integrable g4 P) (h5 : Integrable g5 P) (c1 c2 c4 c5 : ℂ) : ∫ ω, (c1 * g1 ω + c2 * g2 ω + star (c1 * g1 ω) + c4 * g4 ω + c5 * g5 ω +
          star (c4 * g4 ω)) ∂P =
        c1 * ∫ ω, g1 ω ∂P + c2 * ∫ ω, g2 ω ∂P + star (c1 * ∫ ω, g1 ω ∂P) +
          c4 * ∫ ω, g4 ω ∂P + c5 * ∫ ω, g5 ω ∂P + star (c4 * ∫ ω, g4 ω ∂P) := by
    have i1 := h1.const_mul c1; have i2 := h2.const_mul c2
    have i4 := h4.const_mul c4; have i5 := h5.const_mul c5
    have j1 : Integrable (fun ω => star (c1 * g1 ω)) P := integrable_conj i1
    have j4 : Integrable (fun ω => star (c4 * g4 ω)) P := integrable_conj i4
    have s2 : Integrable (fun ω => c1 * g1 ω + c2 * g2 ω) P := i1.add i2
    have s3 : Integrable (fun ω => c1 * g1 ω + c2 * g2 ω + star (c1 * g1 ω)) P := s2.add j1
    have s4 : Integrable (fun ω => c1 * g1 ω + c2 * g2 ω + star (c1 * g1 ω) + c4 * g4 ω) P := s3.add i4
    have s5 : Integrable (fun ω => c1 * g1 ω + c2 * g2 ω + star (c1 * g1 ω) + c4 * g4 ω + c5 * g5 ω) P := s4.add i5
    rw [integral_add s5 j4, integral_add s4 i5, integral_add s3 i4, integral_add s2 j1,
      integral_add i1 i2]
    simp only [Complex.star_def, integral_conj, integral_const_mul]
  have hχ : 0 < γ / 2 := by positivity
  have ha1 : γ * (γ / 2) / 2 ≤ 1 := by nlinarith
  have hnoat := gmc_noAtoms_ae P X hX γ hγ hγ2 M hM hMm
  have hint := (bpz_wirt2L_momField2_zero P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hp hu0 hu1).1
  rw [ContinuousLinearMap.integral_apply hint 1,
    ContinuousLinearMap.integral_apply (hint.apply_continuousLinearMap 1) 1,
    ← integral_complex_ofReal]
  have hkeq {μ : Measure ℂ} (h0 : μ {0} = 0) (h1 : μ {1} = 0) (d : ℂ → ℂ) :
      ∫ x, (gammaHalfKernel γ α₁ α₂ α₃ u x : ℂ) / d x ∂μ =
        ∫ x, ((bpzSoftWeight γ (γ / 2) α₁ α₂ α₃ 0 u x : ℝ) : ℂ) / d x ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [bpz_ae_ne_of_measure_singleton h0, bpz_ae_ne_of_measure_singleton h1] with x hx0 hx1
    have hkw : bpzSoftWeight γ (γ / 2) α₁ α₂ α₃ 0 u x = gammaHalfKernel γ α₁ α₂ α₃ u x := by
      rw [bpzSoftWeight_zero]
      unfold bpzBaseWeight gammaHalfKernel
      rw [Real.rpow_neg (norm_pos_iff.mpr hx0).le,
        Real.rpow_neg (norm_pos_iff.mpr (sub_ne_zero.mpr hx1)).le,
        show γ * (γ / 2) = γ ^ 2 / 2 by ring]
      ring
    simp only [hkw]
  have hcm {μ : Measure ℂ} (hu : μ {u} = 0) (h0 : μ {0} = 0) (h1 : μ {1} = 0) (r : ℝ) :
      ((coulombMass γ μ ![-γ / 2, α₁, α₂] ![u, 0, 1] α₃) ^ r).toReal =
        (∫ x, bpzSoftWeight γ (γ / 2) α₁ α₂ α₃ 0 u x ∂μ) ^ r := by
    have h := coulombMass_eq_lintegral_bpzSoftWeight (γ := γ) (χ := γ / 2) (α₁ := α₁)
      (α₂ := α₂) (α₃ := α₃) μ u hu h0 h1
    rw [← neg_div] at h
    rw [← ENNReal.toReal_rpow, h, ← bpzSoftI_eq_integral, bpzSoftI_eq_toReal]; rfl
  have hbar (ω : Ω) : gammaHalfRootKernelBar M γ α₁ α₂ α₃ ω u = conj (gammaHalfRootKernelZ M γ α₁ α₂ α₃ ω u) := by
    unfold gammaHalfRootKernelBar gammaHalfRootKernelZ
    rw [← integral_conj]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only [Complex.star_def, map_div₀, Complex.conj_ofReal])
  have e1 (ω : Ω) (hω : ∀ x, M ω {x} = 0) :
      ((coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![u, 0, 1] α₃ ^ (-p - 1)).toReal : ℂ) *
        (∫ x in Set.univ, (gammaHalfKernel γ α₁ α₂ α₃ u x : ℂ) / (x - u) ^ 2 ∂M ω) =
      (((∫ x, bpzSoftWeight γ (γ / 2) α₁ α₂ α₃ 0 u x ∂M ω) ^ (-p - 1) : ℝ) : ℂ) *
        ∫ x, ((bpzSoftWeight γ (γ / 2) α₁ α₂ α₃ 0 u x : ℝ) : ℂ) / (x - u) ^ 2 ∂M ω := by
    rw [hcm (hω u) (hω 0) (hω 1), Measure.restrict_univ, hkeq (hω 0) (hω 1)]
  have e2 (ω : Ω) (hω : ∀ x, M ω {x} = 0) :
      ((coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![u, 0, 1] α₃ ^ (-p - 1)).toReal : ℂ) *
        (∫ x in Set.univ, (gammaHalfKernel γ α₁ α₂ α₃ u x : ℂ) / (‖x - u‖ ^ 2 : ℝ) ∂M ω) =
      (((∫ x, bpzSoftWeight γ (γ / 2) α₁ α₂ α₃ 0 u x ∂M ω) ^ (-p - 1) : ℝ) : ℂ) *
        ∫ x, ((bpzSoftWeight γ (γ / 2) α₁ α₂ α₃ 0 u x : ℝ) : ℂ) / ((‖x - u‖ ^ 2 : ℝ) : ℂ) ∂M ω := by
    rw [hcm (hω u) (hω 0) (hω 1), Measure.restrict_univ, hkeq (hω 0) (hω 1)]
  have e4 (ω : Ω) (hω : ∀ x, M ω {x} = 0) :
      ((ENNReal.rpow (coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![u, 0, 1] α₃) (-p - 2)).toReal : ℂ) *
        gammaHalfRootKernelZ M γ α₁ α₂ α₃ ω u ^ 2 =
      (((∫ x, bpzSoftWeight γ (γ / 2) α₁ α₂ α₃ 0 u x ∂M ω) ^ (-p - 2) : ℝ) : ℂ) *
        (∫ x, ((bpzSoftWeight γ (γ / 2) α₁ α₂ α₃ 0 u x : ℝ) : ℂ) / (x - u) ∂M ω) ^ 2 := by
    rw [ENNReal.rpow_eq_pow, hcm (hω u) (hω 0) (hω 1), gammaHalfRootKernelZ, hkeq (hω 0) (hω 1)]
  have e5 (ω : Ω) (hω : ∀ x, M ω {x} = 0) :
      ((ENNReal.rpow (coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![u, 0, 1] α₃) (-p - 2)).toReal : ℂ) *
        gammaHalfRootKernelZ M γ α₁ α₂ α₃ ω u * gammaHalfRootKernelBar M γ α₁ α₂ α₃ ω u =
      (((∫ x, bpzSoftWeight γ (γ / 2) α₁ α₂ α₃ 0 u x ∂M ω) ^ (-p - 2) : ℝ) : ℂ) *
        (∫ x, ((bpzSoftWeight γ (γ / 2) α₁ α₂ α₃ 0 u x : ℝ) : ℂ) / (x - u) ∂M ω) *
        conj (∫ x, ((bpzSoftWeight γ (γ / 2) α₁ α₂ α₃ 0 u x : ℝ) : ℂ) / (x - u) ∂M ω) := by
    rw [ENNReal.rpow_eq_pow, hcm (hω u) (hω 0) (hω 1), hbar, gammaHalfRootKernelZ, hkeq (hω 0) (hω 1)]
  have hkm := measurable_bpzSoftWeight (γ := γ) (χ := γ / 2) (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) 0 u
  have hgood := bpzWM_good_ae (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) P X hX hγ hγ2 M hM hMm hχ ha1
    hα₁ hα₂ hα₃ hu0 hu1
  have iT1 := ((bpzWM_integrable_T1 P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hp hu0 hu1).congr
    (Eventually.of_forall fun _ => by ring)).congr (hnoat.mono fun ω hω => (e1 ω hω).symm)
  have iTmix_raw : Integrable (fun ω =>
      (((∫ x, bpzSoftWeight γ (γ / 2) α₁ α₂ α₃ 0 u x ∂M ω) ^ (-p - 1) : ℝ) : ℂ) *
        ∫ x, ((bpzSoftWeight γ (γ / 2) α₁ α₂ α₃ 0 u x : ℝ) : ℂ) / ((‖x - u‖ ^ 2 : ℝ) : ℂ) ∂M ω) P :=
    (bpz_singular_dom_integrable (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) P X hX hγ hγ2 M hM
      hMm hχ hα₁ hα₂ hα₃ (q := p + 1) (by linarith) hu0 hu1).mono'
      (((Complex.measurable_ofReal.comp (((measurable_integral_measure hkm).comp hMm).pow_const _)).mul
        ((bpz_stronglyMeasurable_integral_measure
          ((Complex.measurable_ofReal.comp hkm).div (Complex.measurable_ofReal.comp
            ((measurable_id.sub_const u).norm.pow_const 2))).stronglyMeasurable).measurable.comp hMm)).aestronglyMeasurable)
      (hgood.mono fun ω ⟨H, hI⟩ => by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hI.le _),
          show -(p + 1) = -p - 1 by ring]
        refine mul_le_mul_of_nonneg_left ((norm_integral_le_of_norm_le (bpzWM_integrable_w2 H) ?_).trans
          (bpzWM_n2_le H)) (Real.rpow_nonneg hI.le _)
        filter_upwards [bpz_ae_ne_of_measure_singleton H.hz] with x hx
        have h := bpz_norm_div_root_pow (γ * (γ / 2) / 2) 2 (H.hw0 x) hx
        rw [bpzWM_normSq_eq H x] at h
        simpa [norm_sub_rev u x, show (x - u) ^ 2 = (u - x) ^ 2 by ring] using h.le)
  have iTmix := iTmix_raw.congr (hnoat.mono fun ω hω => (e2 ω hω).symm)
  have iT2_raw := (bpzWM_integrable_T2 P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hp hu0 hu1).congr
    (Eventually.of_forall fun ω => by
      simp only
      rw [show (∫ x, ((bpzSoftWeight γ (γ / 2) α₁ α₂ α₃ 0 u x : ℝ) : ℂ) / (u - x) ∂M ω) =
        -∫ x, ((bpzSoftWeight γ (γ / 2) α₁ α₂ α₃ 0 u x : ℝ) : ℂ) / (x - u) ∂M ω by
          rw [← integral_neg]; exact integral_congr_ae (Eventually.of_forall fun x => by
            dsimp only; rw [← neg_sub x u, div_neg]), neg_sq])
  have iT2 := iT2_raw.congr (hnoat.mono fun ω hω => (e4 ω hω).symm)
  have hZ := (bpz_stronglyMeasurable_integral_measure
    ((Complex.measurable_ofReal.comp hkm).div (measurable_id.sub_const u)).stronglyMeasurable).measurable.comp hMm
  have iT5_raw : Integrable (fun ω =>
      (((∫ x, bpzSoftWeight γ (γ / 2) α₁ α₂ α₃ 0 u x ∂M ω) ^ (-p - 2) : ℝ) : ℂ) *
        (∫ x, ((bpzSoftWeight γ (γ / 2) α₁ α₂ α₃ 0 u x : ℝ) : ℂ) / (x - u) ∂M ω) *
        conj (∫ x, ((bpzSoftWeight γ (γ / 2) α₁ α₂ α₃ 0 u x : ℝ) : ℂ) / (x - u) ∂M ω)) P :=
    iT2_raw.norm.mono'
      ((((Complex.measurable_ofReal.comp (((measurable_integral_measure hkm).comp hMm).pow_const _)).mul hZ).mul
        (Complex.continuous_conj.measurable.comp hZ)).aestronglyMeasurable)
      (Eventually.of_forall fun ω => by simp only [norm_mul, RCLike.norm_conj, norm_pow]; rw [mul_assoc, sq])
  have iT5 := iT5_raw.congr (hnoat.mono fun ω hω => (e5 ω hω).symm)
  unfold fusionPureSpatial fusionMixedSpatial
  refine (integral_congr_ae ?_).trans (integral_six iT1 iTmix iT2 iT5 _ _ _ _)
  filter_upwards [hnoat, hgood] with ω hω ⟨H, _⟩
  rw [momField2_six H p, e1 ω hω, e2 ω hω, e4 ω hω, e5 ω hω, show γ ^ 2 / 4 = γ * (γ / 2) / 2 by ring]

end DOZZ.Proofs
