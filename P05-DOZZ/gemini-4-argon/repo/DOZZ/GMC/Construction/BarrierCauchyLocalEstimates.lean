/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.IsCompatibleAdmissibleRegularizations
public import DOZZ.GMC.AdmissibleCoarseBarrier
public import DOZZ.GMC.AdmissibleCoarseScaleBarrier
public import DOZZ.GMC.Construction.GMCBarrierCompactTestL1
public import DOZZ.GMC.Construction.FiniteGaussianWickPairTilt
public import DOZZ.GMC.GoodBarrierL2Cauchy
public import DOZZ.GMC.PowerKernelIntegrability

/-! Mixed-cutoff barrier estimates for compatible admissible logarithmic regularizations. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- A mixed pair of fine Wick roots from two compatible admissible regularizations is controlled
by the first regularization's coarse barrier. The cutoff scales and roots may vary independently.
This is the pointwise mixed-kernel estimate used before integrating over the spatial variables. -/
theorem compatible_two_root_wick_pair_good_barrier_power_bound_BarrierCauchyLocalEstimates
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ ε₁ : ℝ)
    (Y Z : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (hZ : IsAdmissibleLogRegularization P U dens ε₁ Z)
    (hYZ : IsCompatibleAdmissibleRegularizations P U ε₀ ε₁ Y Z)
    (b₁ b₂ : Bool)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ), Real.exp (-(k : ℝ)) ≤ min ε₀ ε₁ →
      ∀ ε δ : ℝ, 0 < ε → ε ≤ min ε₀ ε₁ → ε ≤ Real.exp (-(k : ℝ)) →
        0 < δ → δ ≤ min ε₀ ε₁ → δ ≤ Real.exp (-(k : ℝ)) → ∀ κ : ℝ,
    ∀ x y : ℂ, x ∈ K → y ∈ K →
      ‖x - y‖ ≤ Real.exp (-(k : ℝ)) → 0 < ‖x - y‖ →
      ∀ ρ : ℝ, ρ = max ‖x - y‖ (max ε δ) →
      Real.log (1 / ρ) - 1 < (k : ℝ) →
      ∀ η g a : ℝ, 0 < η → η < 1 → 0 < g → a < 2 * g →
      C < (k : ℝ) → C ≤ η * (k : ℝ) →
      2 * g * C + 1 ≤ η * (2 * g - a) * (k : ℝ) →
      0 ≤ κ →
      g ^ 2 - ((1 - η) ^ 2 * (2 * g - a) ^ 2 / (2 * (1 + η))) ≤ κ →
      ∫⁻ ω, ENNReal.ofReal (Real.exp
          (g * (if b₁ then Y else Z) ω ε x - g ^ 2 / 2 * gaussianVariance P
            (fun ω => (if b₁ then Y else Z) ω ε x))) *
        ENNReal.ofReal (Real.exp
          (g * (if b₂ then Y else Z) ω δ y - g ^ 2 / 2 * gaussianVariance P
            (fun ω => (if b₂ then Y else Z) ω δ y))) *
        Set.indicator {ω | Y ω (Real.exp (-(k : ℝ))) x ≤ a * (k : ℝ)}
          (fun _ => (1 : ℝ≥0∞)) ω ∂P ≤
        ENNReal.ofReal ((Real.exp (g ^ 2 * C +
          ((1 - η) ^ 2 * (2 * g - a) ^ 2 / (2 * (1 + η)))) * ‖x - y‖ ^ (-κ))) := by
  rcases hYZ with ⟨hJoint, hCov, hCoarse, hOffDiagonal, hFixedCoarse⟩
  obtain ⟨Cv, hCv, hvar⟩ := hY.coarseVarianceBound K hK hKU
  obtain ⟨CmY, hCmY, hmixY⟩ := hY.coarseMixedBound K hK hKU
  obtain ⟨CmZ, hCmZ, hmixZ⟩ := hCoarse K hK hKU
  obtain ⟨Cyy, hCyy, hcovYY⟩ := hY.covarianceBound K hK hKU
  obtain ⟨Czz, hCzz, hcovZZ⟩ := hZ.covarianceBound K hK hKU
  obtain ⟨Cyz, hCyz, hcovYZ⟩ := hCov K hK hKU
  let C₀ : ℝ := Cv + CmY + CmZ + Cyy + Czz + Cyz
  have hC₀nonneg : 0 ≤ C₀ := by
    dsimp [C₀]
    positivity
  have hCyyC : Cyy ≤ C₀ := by dsimp [C₀]; linarith [hCv, hCmY, hCmZ, hCzz, hCyz]
  have hCyzC : Cyz ≤ C₀ := by dsimp [C₀]; linarith [hCv, hCmY, hCmZ, hCyy, hCzz]
  refine ⟨C₀, hC₀nonneg, ?_⟩
  intro k hkcut ε δ hε hεcut₀ hεcut hδ hδcut₁ hδcut κ
    x y hx hy hxy hxypos ρ hρdef hfloor
  let r : ℝ := Real.exp (-(k : ℝ))
  let q : Fin 3 → Bool × ℝ × ℂ := fun i =>
    if i = 0 then (true, r, x) else if i = 1 then (b₁, ε, x) else (b₂, δ, y)
  let V : Ω → Fin 3 → ℝ := fun ω i =>
    if (q i).1 then Y ω (q i).2.1 (q i).2.2 else Z ω (q i).2.1 (q i).2.2
  have hV : IsCenteredJointlyGaussian P V := by
    apply hJoint 3 q
    intro i
    fin_cases i
    · exact ⟨Real.exp_pos _, hkcut⟩
    · exact ⟨hε, hεcut₀⟩
    · exact ⟨hδ, hδcut₁⟩
  have hcovV₁ : |gaussianCovariance P (fun ω => V ω 0)
      (fun ω => V ω 1) - (k : ℝ)| ≤ C₀ := by
    cases b₁ with
    | false =>
        exact (show |gaussianCovariance P (fun ω => V ω 0) (fun ω => V ω 1) - (k : ℝ)| ≤ CmZ by simpa [V, q, r] using (hmixZ k (le_trans hkcut (min_le_left _ _)) ε hε (le_min (le_trans hεcut₀ (min_le_right _ _)) hεcut) x hx)).trans (by dsimp [C₀]; linarith [hCv, hCmY, hCyy, hCzz, hCyz])
    | true =>
        exact (show |gaussianCovariance P (fun ω => V ω 0) (fun ω => V ω 1) - (k : ℝ)| ≤ CmY by simpa [V, q, r] using (hmixY k (le_trans hkcut (min_le_left _ _)) ε hε hεcut x hx)).trans (by dsimp [C₀]; linarith [hCv, hCmZ, hCyy, hCzz, hCyz])
  have hlog : Real.log (1 / max ‖x - y‖ (max r δ)) = (k : ℝ) := by
    rw [(show max ‖x - y‖ (max r δ) = r by rw [max_eq_left hδcut, max_eq_right hxy])]
    simp [r]
  have hcovV₂ : |gaussianCovariance P (fun ω => V ω 0)
      (fun ω => V ω 2) - (k : ℝ)| ≤ C₀ := by
    cases b₂ with
    | false =>
        have h' : |gaussianCovariance P (fun ω => V ω 0)
            (fun ω => V ω 2) - (k : ℝ)| ≤ Cyz := by
          have hbound : |gaussianCovariance P (fun ω => V ω 0)
              (fun ω => V ω 2) - Real.log (1 / max ‖x - y‖ (max r δ))| ≤ Cyz := by
            simpa [V, q, r] using (hcovYZ r δ (Real.exp_pos _) (le_trans hkcut (min_le_left _ _)) hδ (le_trans hδcut₁ (min_le_right _ _)) x hx y hy)
          rw [hlog] at hbound
          exact hbound
        exact h'.trans hCyzC
    | true =>
        have h' : |gaussianCovariance P (fun ω => V ω 0)
            (fun ω => V ω 2) - (k : ℝ)| ≤ Cyy := by
          have hbound : |gaussianCovariance P (fun ω => V ω 0)
              (fun ω => V ω 2) - Real.log (1 / max ‖x - y‖ (max r δ))| ≤ Cyy := by
            simpa [V, q, r] using (hcovYY r δ (Real.exp_pos _) (le_trans hkcut (min_le_left _ _)) hδ (le_trans hδcut₁ (min_le_left _ _)) x hx y hy)
          rw [hlog] at hbound
          exact hbound
        exact h'.trans hCyyC
  have hcovComm (f g : Ω → ℝ) :
      gaussianCovariance P f g = gaussianCovariance P g f := by
    unfold gaussianCovariance
    apply integral_congr_ae
    exact ae_of_all P (fun ω => by ring)
  have hcovRoot : gaussianCovariance P (fun ω => V ω 1)
      (fun ω => V ω 2) ≤ Real.log (1 / ρ) + C₀ := by
    have h' : |gaussianCovariance P (fun ω => V ω 1)
        (fun ω => V ω 2) - Real.log (1 / ρ)| ≤ C₀ := by
      cases b₁ with
      | true =>
        cases b₂ with
        | true =>
          exact (show |gaussianCovariance P (fun ω => V ω 1) (fun ω => V ω 2) - Real.log (1 / ρ)| ≤ Cyy by simpa [V, q, hρdef] using (hcovYY ε δ hε (le_trans hεcut₀ (min_le_left _ _)) hδ (le_trans hδcut₁ (min_le_left _ _)) x hx y hy)).trans hCyyC
        | false =>
          exact (show |gaussianCovariance P (fun ω => V ω 1) (fun ω => V ω 2) - Real.log (1 / ρ)| ≤ Cyz by simpa [V, q, hρdef] using (hcovYZ ε δ hε (le_trans hεcut₀ (min_le_left _ _)) hδ (le_trans hδcut₁ (min_le_right _ _)) x hx y hy)).trans hCyzC
      | false =>
        cases b₂ with
        | true =>
          exact (show |gaussianCovariance P (fun ω => V ω 1) (fun ω => V ω 2) - Real.log (1 / ρ)| ≤ Cyz by simpa [V, q, hρdef, hcovComm, norm_sub_rev, max_comm] using (hcovYZ δ ε hδ (le_trans hδcut₁ (min_le_left _ _)) hε (le_trans hεcut₀ (min_le_right _ _)) y hy x hx)).trans hCyzC
        | false =>
          exact (show |gaussianCovariance P (fun ω => V ω 1) (fun ω => V ω 2) - Real.log (1 / ρ)| ≤ Czz by simpa [V, q, hρdef] using (hcovZZ ε δ hε (le_trans hεcut₀ (min_le_right _ _)) hδ (le_trans hδcut₁ (min_le_right _ _)) x hx y hy)).trans (by dsimp [C₀]; linarith [hCv, hCmY, hCmZ, hCyy, hCyz])
    have := (abs_le.mp h').2
    linarith
  intro η g a hη hη1 hg hag hCk hCeta hgap hκ hκexp
  cases b₁ <;> cases b₂ <;> simpa [V, q, r] using (finite_gaussian_wick_pair_good_barrier_power_bound P V hV 1 2 0 (by decide) g a C₀ η (k : ℝ) ‖x - y‖ ρ κ hg hag (lt_of_le_of_lt hC₀nonneg hCk) hη hη1 hCeta hgap (show |gaussianVariance P (fun ω => V ω 0) - (k : ℝ)| ≤ C₀ by exact (show |gaussianVariance P (fun ω => V ω 0) - (k : ℝ)| ≤ Cv by simpa [V, q, r] using (hvar k (le_trans hkcut (min_le_left _ _)) x hx)).trans (by dsimp [C₀]; linarith [hCmY, hCmZ, hCyy, hCzz, hCyz])) hcovV₁ hcovV₂ (show 0 < ρ by rw [hρdef]; exact lt_of_lt_of_le (lt_of_lt_of_le hε (le_max_left _ _)) (le_max_right _ _)) ((show ρ ≤ Real.exp (-(k : ℝ)) by rw [hρdef]; exact max_le hxy (max_le hεcut hδcut)).trans (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg k)))) hxypos (by rw [hρdef]; exact le_max_left _ _) hcovRoot hfloor hκ hκexp)

end DOZZ.Proofs
