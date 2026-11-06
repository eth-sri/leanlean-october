/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Mobius.InversionMoment
public import DOZZ.GMC.SharpMoments.SeibergWeight
import DOZZ.GMC.Moments.InversionLaw

/-!
# Inversion exchanges the charges at the origin and at infinity

Under `x ↦ 1/x` the ratio `|x|_+/|x|` becomes `|y|_+`, the background `|x|_+` becomes
`|y|_+/|y|`, and a nonzero root `z` becomes `1/z` with the factor `|z|^{-1}`. With the inversion
law of the chaos, the real moments of the Coulomb mass with a root at the origin (charge `β₀`)
and a charge `βinf` at infinity equal those with the two charges exchanged and the other roots
inverted, times `∏ₖ |zₖ|^{-γ αₖ q}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs









/-- **Coulomb moments through inversion**, exchanging the charges at `0` and `∞`. -/
theorem coulombMass_inv_moment_cons {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    X (hX : IsEquatorGFF P X) γ (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) {N} β₀ βinf (α : Fin N → ℝ)
    (z : Fin N → ℂ) (hz : ∀ k, z k ≠ 0) q :
    ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) (Fin.cons β₀ α : Fin (N + 1) → ℝ)
        (Fin.cons 0 z : Fin (N + 1) → ℂ) βinf) q ∂P =
      ENNReal.rpow (∏ k, ENNReal.rpow (ENNReal.ofReal ‖z k‖) (-(γ * α k))) q *
        ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) (Fin.cons βinf α : Fin (N + 1) → ℝ)
          (Fin.cons 0 (fun k => (z k)⁻¹) : Fin (N + 1) → ℂ) β₀) q ∂P := by
  have inversionZero_const_ne_top : (∏ k, ENNReal.rpow (ENNReal.ofReal ‖z k‖) (-(γ * α k))) ≠ ⊤ := ENNReal.prod_ne_top fun k _ => ENNReal.rpow_ne_top_of_ne_zero
      (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr (hz k))).ne' ENNReal.ofReal_ne_top
  have inversionZero_normPlus_inv {y} (hy : y ≠ 0) : normPlus y⁻¹ = normPlus y / ‖y‖ := by
    have hyn := norm_pos_iff.mpr hy
    unfold normPlus
    rw [norm_inv, ← max_div_div_right hyn.le, div_self hyn.ne', one_div, max_comm]
  have inversionZero_map_lintegral (μ : Measure ℂ) (h0 : μ {0} = 0) (hk : ∀ k, μ {(z k)⁻¹} = 0) : ∫⁻ x, coulombWeight γ (Fin.cons β₀ α : Fin (N + 1) → ℝ) (Fin.cons 0 z : Fin (N + 1) → ℂ) βinf x ∂μ.map (fun x => x⁻¹) = (∏ k, ENNReal.rpow (ENNReal.ofReal ‖z k‖) (-(γ * α k))) * coulombMass γ μ (Fin.cons βinf α : Fin (N + 1) → ℝ) (Fin.cons 0 (fun k => (z k)⁻¹) : Fin (N + 1) → ℂ) β₀ := by
    have coulombWeight_inv_cons {y} (hy : y ≠ 0) (hyz : ∀ k, y ≠ (z k)⁻¹) : coulombWeight γ (Fin.cons β₀ α : Fin (N + 1) → ℝ) (Fin.cons 0 z : Fin (N + 1) → ℂ) βinf y⁻¹ = (∏ k, ENNReal.rpow (ENNReal.ofReal ‖z k‖) (-(γ * α k))) * coulombWeight γ (Fin.cons βinf α : Fin (N + 1) → ℝ) (Fin.cons 0 (fun k => (z k)⁻¹) : Fin (N + 1) → ℂ) β₀ y := by
      have inversionZero_rpow_factor {a} {n} {d} (ha : 0 < a) (hn : 0 < n) (hd : 0 < d) e : ENNReal.rpow (ENNReal.ofReal (a / (n * d))) e = ENNReal.rpow (ENNReal.ofReal n) (-e) * ENNReal.rpow (ENNReal.ofReal (a / d)) e := by
        rw [coulombWeight_rpow_ofReal_div ha (mul_pos hn hd), coulombWeight_rpow_ofReal_div ha hd]
        simp only [ENNReal.rpow_eq_pow]
        rw [ENNReal.ofReal_mul hn.le,
          ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
        ring
      have inversionZero_root_ratio {w} (hw : w ≠ 0) (hyw : y ≠ w⁻¹) : normPlus y⁻¹ / ‖y⁻¹ - w‖ = normPlus y / (‖w‖ * ‖y - w⁻¹‖) := by
        rw [inversionZero_normPlus_inv hy, (show ‖y⁻¹ - w‖ = ‖w‖ * ‖y - w⁻¹‖ / ‖y‖ by rw [show y⁻¹ - w = -w * (y - w⁻¹) / y by field_simp; ring, norm_div, norm_mul, norm_neg])]
        field_simp
      have inversionZero_origin_ratio : normPlus y⁻¹ / ‖y⁻¹ - 0‖ = normPlus y := by
        rw [inversionZero_normPlus_inv hy, sub_zero, norm_inv]
        field_simp
      unfold coulombWeight
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      have hprod : ∏ k, ENNReal.rpow (ENNReal.ofReal (normPlus y⁻¹ / ‖y⁻¹ - z k‖)) (γ * α k) =
          (∏ k, ENNReal.rpow (ENNReal.ofReal ‖z k‖) (-(γ * α k))) *
            ∏ k, ENNReal.rpow (ENNReal.ofReal (normPlus y / ‖y - (z k)⁻¹‖)) (γ * α k) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [inversionZero_root_ratio (hz k) (hyz k)]
        exact inversionZero_rpow_factor (lt_of_lt_of_le one_pos (le_max_left _ _)) (norm_pos_iff.mpr (hz k))
          (norm_pos_iff.mpr (sub_ne_zero.mpr (hyz k))) _
      rw [hprod, inversionZero_origin_ratio, inversionZero_normPlus_inv hy, sub_zero]
      ring
    rw [lintegral_map (measurable_coulombWeight _ _ _ _) measurable_inv,
      coulombMass_eq_lintegral_coulombWeight,
      ← lintegral_const_mul' _ _ (inversionZero_const_ne_top)]
    apply lintegral_congr_ae
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_union_null h0 (measure_iUnion_null hk))] with y hy
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_iUnion, not_or, not_exists] at hy
    exact coulombWeight_inv_cons hy.1 fun k h => hy.2 k h
  have inversionZero_const_ne_zero : (∏ k, ENNReal.rpow (ENNReal.ofReal ‖z k‖) (-(γ * α k))) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro k _
    exact (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr (hz k)))
      ENNReal.ofReal_ne_top).ne'
  have hc0 := inversionZero_const_ne_zero
  have hct := inversionZero_const_ne_top
  have hH : Measurable fun μ : Measure ℂ =>
      ENNReal.rpow (∫⁻ x, coulombWeight γ (Fin.cons β₀ α : Fin (N + 1) → ℝ)
        (Fin.cons 0 z : Fin (N + 1) → ℂ) βinf x ∂μ) q :=
    (Measure.measurable_lintegral (measurable_coulombWeight _ _ _ _)).pow_const q
  have hlaw := equatorGFF_GMC_inversion_law P X hX γ hγ hγ2 M hM _ hH
  -- almost surely no atom at the origin or at any inverted root
  have hatoms : ∀ᵐ ω ∂P, M ω {0} = 0 ∧ ∀ k, M ω {(z k)⁻¹} = 0 := by
    have h0 := gmc_atomless_of_isGMCOf P X hX γ hγ hγ2 M hM 0
    have hk := ae_all_iff.2 fun k => gmc_atomless_of_isGMCOf P X hX γ hγ hγ2 M hM (z k)⁻¹
    filter_upwards [h0, hk] with ω h1 h2 using ⟨h1, h2⟩
  calc
    ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) (Fin.cons β₀ α : Fin (N + 1) → ℝ)
        (Fin.cons 0 z : Fin (N + 1) → ℂ) βinf) q ∂P
        = ∫⁻ ω, ENNReal.rpow (∫⁻ x, coulombWeight γ (Fin.cons β₀ α : Fin (N + 1) → ℝ)
            (Fin.cons 0 z : Fin (N + 1) → ℂ) βinf x ∂M ω) q ∂P := by
      congr 1
    _ = ∫⁻ ω, ENNReal.rpow ((∏ k, ENNReal.rpow (ENNReal.ofReal ‖z k‖) (-(γ * α k))) *
          coulombMass γ (M ω) (Fin.cons βinf α : Fin (N + 1) → ℝ)
            (Fin.cons 0 (fun k => (z k)⁻¹) : Fin (N + 1) → ℂ) β₀) q ∂P := by
      rw [← hlaw]
      apply lintegral_congr_ae
      filter_upwards [hatoms] with ω hω
      rw [inversionZero_map_lintegral (M ω) hω.1 hω.2]
    _ = ∫⁻ ω, ENNReal.rpow (∏ k, ENNReal.rpow (ENNReal.ofReal ‖z k‖) (-(γ * α k))) q *
          ENNReal.rpow (coulombMass γ (M ω) (Fin.cons βinf α : Fin (N + 1) → ℝ)
            (Fin.cons 0 (fun k => (z k)⁻¹) : Fin (N + 1) → ℂ) β₀) q ∂P := by
      congr 1
      funext ω
      exact inversionMoment_mul_rpow hc0 hct _ q
    _ = _ := lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_ne_zero hc0 hct)

end DOZZ.Proofs

end
