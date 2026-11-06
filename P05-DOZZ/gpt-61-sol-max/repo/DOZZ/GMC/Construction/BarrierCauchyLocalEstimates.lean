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

public section

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
  let C₀  := Cv + CmY + CmZ + Cyy + Czz + Cyz
  have hC₀nonneg : 0 ≤ C₀ := by
    dsimp [C₀]
    positivity
  
  
  
  
  
  have hCyzC : Cyz ≤ C₀ := by bound
  refine ⟨C₀, hC₀nonneg, ?_⟩
  intro k hkcut ε δ hε hεcut₀ hεcut hδ hδcut₁ hδcut κ
    x y hx hy hxy hxypos ρ hρdef hfloor
  have hrhoCut : ρ ≤ Real.exp (-(k : ℝ)) := by
    bound
  have hrhoPos : 0 < ρ := by
    bound
  have hrhoLeOne  :=
    hrhoCut.trans (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg k)))
  have hdistLeRho : ‖x - y‖ ≤ ρ := by
    rw [hρdef]
    exact le_max_left _ _
  let r  := Real.exp (-(k : ℝ))
  let q : Fin 3 → Bool × ℝ × ℂ := fun i =>
    if i = 0 then (true, r, x) else if i = 1 then (b₁, ε, x) else (b₂, δ, y)
  let V  := fun ω i =>
    if (q i).1 then Y ω (q i).2.1 (q i).2.2 else Z ω (q i).2.1 (q i).2.2
  have hV : IsCenteredJointlyGaussian P V := by
    apply hJoint 3 q
    intro i
    fin_cases i
    · exact ⟨Real.exp_pos _, hkcut⟩
    · exact ⟨hε, hεcut₀⟩
    · exact ⟨hδ, hδcut₁⟩
  have hvarV : |gaussianVariance P (fun ω => V ω 0) - (k : ℝ)| ≤ C₀ := by
    have h := hvar k (le_trans hkcut (min_le_left _ _)) x hx
    grind
  have hcovV₁ : |gaussianCovariance P (fun ω => V ω 0)
      (fun ω => V ω 1) - (k : ℝ)| ≤ C₀ := by
    cases b₁ with
    | false =>
        have hεcutZ  := le_min
          (le_trans hεcut₀ (min_le_right _ _)) hεcut
        have h := hmixZ k (le_trans hkcut (min_le_left _ _)) ε hε hεcutZ x hx
        grind
    | true =>
        have h := hmixY k (le_trans hkcut (min_le_left _ _)) ε hε hεcut x hx
        grind
  have hgeom : max ‖x - y‖ (max r δ) = r := by
    rw [max_eq_left hδcut, max_eq_right hxy]
  have hlog : Real.log (1 / max ‖x - y‖ (max r δ)) = (k : ℝ) := by
    rw [hgeom]
    simp [r]
  have hcovV₂ : |gaussianCovariance P (fun ω => V ω 0)
      (fun ω => V ω 2) - (k : ℝ)| ≤ C₀ := by
    cases b₂ with
    | false =>
        have h := hcovYZ r δ (Real.exp_pos _) (le_trans hkcut (min_le_left _ _))
          hδ (le_trans hδcut₁ (min_le_right _ _)) x hx y hy
        grind
    | true =>
        have h := hcovYY r δ (Real.exp_pos _) (le_trans hkcut (min_le_left _ _))
          hδ (le_trans hδcut₁ (min_le_left _ _)) x hx y hy
        grind
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
          have h := hcovYY ε δ hε (le_trans hεcut₀ (min_le_left _ _))
            hδ (le_trans hδcut₁ (min_le_left _ _)) x hx y hy
          grind
        | false =>
          have h := hcovYZ ε δ hε (le_trans hεcut₀ (min_le_left _ _))
            hδ (le_trans hδcut₁ (min_le_right _ _)) x hx y hy
          grind
      | false =>
        cases b₂ with
        | true =>
          have h := hcovYZ δ ε hδ (le_trans hδcut₁ (min_le_left _ _))
            hε (le_trans hεcut₀ (min_le_right _ _)) y hy x hx
          have h' : |gaussianCovariance P (fun ω => V ω 1)
              (fun ω => V ω 2) - Real.log (1 / ρ)| ≤ Cyz := by
            simpa [V, q, hρdef, hcovComm, norm_sub_rev, max_comm] using h
          exact h'.trans hCyzC
        | false =>
          have h := hcovZZ ε δ hε (le_trans hεcut₀ (min_le_right _ _))
            hδ (le_trans hδcut₁ (min_le_right _ _)) x hx y hy
          grind
    have hupper := (abs_le.mp h').2
    linarith
  intro η g a hη hη1 hg hag hCk hCeta hgap hκ hκexp
  have hkpos  := lt_of_le_of_lt hC₀nonneg hCk
  have hpair := finite_gaussian_wick_pair_good_barrier_power_bound P V hV
    1 2 0 (by decide) g a C₀ η (k : ℝ) ‖x - y‖ ρ κ hg hag hkpos hη hη1
    hCeta hgap hvarV hcovV₁ hcovV₂ hrhoPos hrhoLeOne hxypos hdistLeRho hcovRoot hfloor
    hκ hκexp
  cases b₁ <;> cases b₂ <;> simpa [V, q, r] using hpair

end DOZZ.Proofs
