/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.PoleSubtracted.MassBounds
public import DOZZ.ShiftEquations.Mobius.AffineMomentInf
public import DOZZ.ShiftEquations.Mobius.InversionZero
public import DOZZ.Statements.Defs.UnitVolumeStructureConstant
import DOZZ.GMC.Moments.RhoCoulomb
import DOZZ.Correlations.Symmetry.SymmetricExtended

/-!
# The frame of the two-pole expansion

The structure constant is defined in the frame `(0, 1, ∞)`, while the pole-subtracted masses live in
the frame `(0, 2, -2)` of [KRV, (defgepsi)]. The Möbius map `ψ(y) = 2y/(y+2)` sending `0, 2, -2` to
`0, 1, ∞` is inversion, translation by `1/2`, inversion. Inversion exchanges the charges at `0` and
`∞` and costs `∏ₖ|zₖ|^{-γαₖ q}`; translations preserve the moments. With `α₂ + α₃ = 4/γ` this gives
`E[Z_ℂ(x)^{1-x/γ}] = 2^{-4(1-x/γ)} E[ρ(x, α₂, α₃)^{1-x/γ}]`, so
`C̄(x, α₂, α₃) = (2/γ) 2^{4(1-x/γ)} E[Z_ℂ(x)^{1-x/γ}]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs


theorem coulombMass_cons_zero {N} γ (μ : Measure ℂ) (α : Fin N → ℝ) z₀
    (z : Fin N → ℂ) αinf :
    coulombMass γ μ (Fin.cons 0 α : Fin (N + 1) → ℝ) (Fin.cons z₀ z : Fin (N + 1) → ℂ) αinf =
      coulombMass γ μ α z αinf := by
  have coulombWeight_cons_zero {N} γ (α : Fin N → ℝ) z₀ (z : Fin N → ℂ) αinf x : coulombWeight γ (Fin.cons 0 α : Fin (N + 1) → ℝ) (Fin.cons z₀ z : Fin (N + 1) → ℂ) αinf x = coulombWeight γ α z αinf x := by
    unfold coulombWeight
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, mul_zero, ENNReal.rpow_eq_pow, ENNReal.rpow_zero,
      one_mul]
  rw [coulombMass_eq_lintegral_coulombWeight, coulombMass_eq_lintegral_coulombWeight]
  simp_rw [coulombWeight_cons_zero]

/-- The two roots of a two-root Coulomb mass may be listed in either order. -/
theorem coulombMass_swap γ (μ : Measure ℂ) a₁ a₂ z₁ z₂ αinf :
    coulombMass γ μ ![a₁, a₂] ![z₁, z₂] αinf = coulombMass γ μ ![a₂, a₁] ![z₂, z₁] αinf := by
  rw [coulombMass_eq_lintegral_coulombWeight, coulombMass_eq_lintegral_coulombWeight]
  refine lintegral_congr fun x => ?_
  unfold coulombWeight
  rw [Fin.prod_univ_two, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring



/-- The translated roots. -/
theorem frame_translate_roots :
    (fun k => (1 : ℂ) * (![1 / 2, -1 / 2] : Fin 2 → ℂ) k + 1 / 2) = ![1, 0] := by
  funext k
  fin_cases k <;> norm_num

theorem frame_inverse_roots :
    (fun k => ((![2, -2] : Fin 2 → ℂ) k)⁻¹) = ![1 / 2, -1 / 2] := by
  funext k
  fin_cases k <;> norm_num


/-- **The frame identity** `E[Z_ℂ(x)^w] = 2^{-4w} E[ρ(x, α₂, α₃)^w]`, `w = 1 - x/γ`. -/
theorem lintegral_totalMass_rpow_eq_rho {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    X (hX : IsEquatorGFF P X) γ (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) η x :
    ∫⁻ ω, poleTotalMass γ x (2 / γ + η) (2 / γ - η) (M ω) ^ (1 - x / γ) ∂P =
      ENNReal.ofReal (2 ^ (-(4 * (1 - x / γ)))) *
        ∫⁻ ω, rho γ (M ω) x (2 / γ + η) (2 / γ - η) ^ (1 - x / γ) ∂P := by
  have frame_infSExp : -infSExp γ (![2 / γ + η, 2 / γ - η] : Fin 2 → ℝ) x = 1 - x / γ := by
    unfold infSExp
    rw [Fin.sum_univ_two, Q]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    field_simp
    ring
  have frame_inversion_constant q : ENNReal.rpow (∏ k, ENNReal.rpow (ENNReal.ofReal ‖(![2, -2] : Fin 2 → ℂ) k‖) (-(γ * (![2 / γ + η, 2 / γ - η] : Fin 2 → ℝ) k))) q = ENNReal.ofReal (2 ^ (-(4 * q))) := by
    rw [Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, norm_neg]
    rw [(show ‖(2 : ℂ)‖ = 2 by simp), ENNReal.rpow_eq_pow, ENNReal.rpow_eq_pow, ENNReal.rpow_eq_pow,
      ← ENNReal.rpow_add _ _ (by simp) ENNReal.ofReal_ne_top, ← ENNReal.rpow_mul,
      ENNReal.ofReal_rpow_of_pos (by norm_num)]
    congr 2
    field_simp
    ring
  have totalMass_eq_coulombMass (μ : Measure ℂ) (h0 : μ {0} = 0) (h2 : μ {2} = 0) (h2' : μ {-2} = 0) : poleTotalMass γ x (2 / γ + η) (2 / γ - η) μ = coulombMass γ μ (Fin.cons x ![2 / γ + η, 2 / γ - η] : Fin 3 → ℝ) (Fin.cons 0 ![2, -2] : Fin 3 → ℂ) 0 := by
    rw [poleTotalMass_eq, coulombMass_eq_lintegral_coulombWeight]
    refine lintegral_congr_ae ?_
    filter_upwards [(show ∀ᵐ y ∂μ, y ≠ 0 by rw [ae_iff]; simpa using h0), (show ∀ᵐ y ∂μ, y ≠ 2 by rw [ae_iff]; simpa using h2), (show ∀ᵐ y ∂μ, y ≠ -2 by rw [ae_iff]; simpa using h2')] with y hy0 hy1 hy2
    have hw := poleWeight_eq_coulombWeight γ η hy1 hy2
    unfold coulombWeight at hw ⊢
    rw [Fin.prod_univ_succ, hw]
    simp only [Fin.cons_zero, Fin.cons_succ, sub_zero, zeroTilt, ENNReal.ofReal_div_of_pos (norm_pos_iff.mpr hy0),
      mul_zero, ENNReal.rpow_eq_pow, ENNReal.rpow_zero, mul_one]
  have hz1 : ∀ k, (![2, -2] : Fin 2 → ℂ) k ≠ 0 := by
    intro k
    fin_cases k <;> norm_num
  have hz2 : ∀ k, (![1] : Fin 1 → ℂ) k ≠ 0 := by
    intro k
    fin_cases k
    norm_num
  -- step 0: the total mass as a three-root Coulomb mass
  have h0 : ∫⁻ ω, poleTotalMass γ x (2 / γ + η) (2 / γ - η) (M ω) ^ (1 - x / γ) ∂P =
      ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω)
        (Fin.cons x ![2 / γ + η, 2 / γ - η] : Fin 3 → ℝ)
        (Fin.cons 0 ![2, -2] : Fin 3 → ℂ) 0) (1 - x / γ) ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [gmc_atomless_of_isGMCOf P X hX γ hγ hγ2 M hM 0,
      gmc_atomless_of_isGMCOf P X hX γ hγ hγ2 M hM 2,
      gmc_atomless_of_isGMCOf P X hX γ hγ hγ2 M hM (-2)] with ω e0 e2 e2'
    rw [totalMass_eq_coulombMass (M ω) e0 e2 e2', ENNReal.rpow_eq_pow]
  -- step 1: inversion sends `x` to infinity; the zero-charge root drops
  have h1 := coulombMass_inv_moment_cons P X hX γ hγ hγ2 M hM x 0
    ![2 / γ + η, 2 / γ - η] ![2, -2] hz1 (1 - x / γ)
  rw [frame_inversion_constant (1 - x / γ), frame_inverse_roots] at h1
  simp_rw [coulombMass_cons_zero] at h1
  -- step 2: translation by `1/2`
  have h2 := coulombMass_affine_moment_inf P X hX γ hγ hγ2 M hM ![2 / γ + η, 2 / γ - η]
    ![1 / 2, -1 / 2] x 1 (1 / 2) one_ne_zero
  rw [frame_infSExp, frame_translate_roots, norm_one, Real.one_rpow, ENNReal.ofReal_one,
    one_mul] at h2
  -- step 3: the root `0` first, then inversion sends `α₃` to infinity
  have h3 := coulombMass_inv_moment_cons P X hX γ hγ hγ2 M hM (2 / γ - η) x ![2 / γ + η] ![1]
    hz2 (1 - x / γ)
  have hc3 : ENNReal.rpow (∏ k, ENNReal.rpow (ENNReal.ofReal ‖(![1] : Fin 1 → ℂ) k‖)
      (-(γ * (![2 / γ + η] : Fin 1 → ℝ) k))) (1 - x / γ) = 1 := by
    simp
  have hinv3 : (fun k => ((![1] : Fin 1 → ℂ) k)⁻¹) = ![1] := by
    funext k
    fin_cases k
    norm_num
  rw [hc3, one_mul, hinv3] at h3
  have hswap : ∀ ω, coulombMass γ (M ω) ![2 / γ + η, 2 / γ - η] ![1, 0] x =
      coulombMass γ (M ω) (Fin.cons (2 / γ - η) ![2 / γ + η] : Fin 2 → ℝ)
        (Fin.cons 0 ![1] : Fin 2 → ℂ) x :=
    fun ω => coulombMass_swap γ (M ω) (2 / γ + η) (2 / γ - η) 1 0 x
  simp_rw [hswap] at h2
  -- step 4: the structure-constant mass
  have h4 : ∫⁻ ω, rho γ (M ω) x (2 / γ + η) (2 / γ - η) ^ (1 - x / γ) ∂P =
      ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) (Fin.cons x ![2 / γ + η] : Fin 2 → ℝ)
        (Fin.cons 0 ![1] : Fin 2 → ℂ) (2 / γ - η)) (1 - x / γ) ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [gmc_rho_eq_coulombMass_ae P X hX γ hγ hγ2 M hM x (2 / γ + η)
      (2 / γ - η)] with ω hω
    rw [hω, ENNReal.rpow_eq_pow]
    rfl
  rw [h0, h1, ← h2, h3, ← h4]

/-- **The structure constant in the pole frame**:
`C̄(x, α₂, α₃) = (2/γ) (2^{4(1-x/γ)} E[Z_ℂ(x)^{1-x/γ}])`. -/
theorem unitVolumeStructureConstant_eq_frame {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    X (hX : IsEquatorGFF P X) γ (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) η x :
    unitVolumeStructureConstant P M γ x (2 / γ + η) (2 / γ - η) =
      2 / γ * (ENNReal.ofReal (2 ^ (4 * (1 - x / γ))) *
        ∫⁻ ω, poleTotalMass γ x (2 / γ + η) (2 / γ - η) (M ω) ^ (1 - x / γ) ∂P).toReal := by
  have hs : -sExp γ x (2 / γ + η) (2 / γ - η) = 1 - x / γ := by
    unfold sExp Q
    field_simp
    ring
  unfold unitVolumeStructureConstant
  rw [hs, lintegral_totalMass_rpow_eq_rho P X hX γ hγ hγ2 M hM η x, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add two_pos, add_neg_cancel,
    Real.rpow_zero, ENNReal.ofReal_one, one_mul]



/-- The structure constant of the two-pole expansion in the order of the pole frame. -/
theorem unitVolumeStructureConstant_pole_order {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    X (hX : IsEquatorGFF P X) γ (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) {η x}
    (hα : ExtendedSeiberg3 γ x (2 / γ + η) (2 / γ - η)) :
    unitVolumeStructureConstant P M γ (Q γ - η - γ / 2) x (2 / γ + η) =
      unitVolumeStructureConstant P M γ x (2 / γ + η) (2 / γ - η) := by
  have extendedSeiberg3_swap23 {γ} {a} {b} {c} (h : ExtendedSeiberg3 γ a b c) : ExtendedSeiberg3 γ a c b := by
    obtain ⟨ha, hb, hc, hs⟩ := h
    refine ⟨ha, hc, hb, ?_⟩
    rw [(show sExp γ a c b = sExp γ a b c by unfold sExp; ring_nf), min_comm (2 / γ * (Q γ - c))]
    exact hs
  have extendedSeiberg3_swap12 {γ} {a} {b} {c} (h : ExtendedSeiberg3 γ a b c) : ExtendedSeiberg3 γ b a c := by
    obtain ⟨ha, hb, hc, hs⟩ := h
    refine ⟨hb, ha, hc, ?_⟩
    rw [(show sExp γ b a c = sExp γ a b c by unfold sExp; ring_nf), min_left_comm (2 / γ * (Q γ - b))]
    exact hs
  rw [(show Q γ - η - γ / 2 = 2 / γ - η by rw [Q]; ring)]
  have h23 := extendedSeiberg3_swap23 hα
  rw [(unitVolumeStructureConstant_symmetric_extended P X M γ (2 / γ - η) x (2 / γ + η) hγ hγ2
    hX hM (extendedSeiberg3_swap12 h23)).1, (unitVolumeStructureConstant_symmetric_extended P X M γ x (2 / γ - η)
    (2 / γ + η) hγ hγ2 hX hM h23).2.1]

end DOZZ.Proofs

end
