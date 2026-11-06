module
public import TaoTrudgianYang2025.HeathBrownModelJetCore
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-!
# Positive signed jets for Heath--Brown's derivative theorem

The sign and the positive lower constant depend only on the fixed model
parameter and derivative order. The actual model errors imply the signed
bounds; no derivative hypothesis is supplied independently of the source.
-/

noncomputable section

open Set Expdb
open scoped ContDiff

namespace TaoTrudgianYang2025

def modelPhaseJetSign (σ : ℝ) (p : ℕ) : ℝ :=
  if 0 ≤ (descPochhammer ℝ p).eval (-σ) then 1 else -1

def modelPhaseJetLower (σ : ℝ) (p : ℕ) : ℝ :=
  modelPhaseJetCoefficient σ p * (2 : ℝ)^(-σ-p) / 2

theorem modelPhaseJetCoefficient_pos {σ : ℝ} (hσ : 0 < σ) (p : ℕ) :
    0 < modelPhaseJetCoefficient σ p := by
  unfold modelPhaseJetCoefficient
  apply abs_pos.mpr
  rw [descPochhammer_eval_eq_prod_range]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  pm_322 hi i
  linarith

section
variable (σ : ℝ) (p : ℕ)
include σ p
theorem modelPhaseJetSign_abs :
    |modelPhaseJetSign σ p| = 1 := by
  unfold modelPhaseJetSign
  grind

theorem modelPhaseJetSign_coefficient :
    modelPhaseJetSign σ p * (descPochhammer ℝ p).eval (-σ) =
      modelPhaseJetCoefficient σ p := by
  unfold modelPhaseJetSign modelPhaseJetCoefficient
  split
  grind
  grind
end

section
variable {σ : ℝ} (hσ : 0 < σ)
include σ hσ
theorem modelPhaseJetLower_pos (p : ℕ) :
    0 < modelPhaseJetLower σ p := by
  unfold modelPhaseJetLower
  exact div_pos (mul_pos (modelPhaseJetCoefficient_pos hσ p)
    (Real.rpow_pos_of_pos (by norm_num) _)) (by norm_num)

theorem modelPhase_signed_referenceJet_bounds
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) (p : ℕ) :
    2*modelPhaseJetLower σ p ≤ modelPhaseJetSign σ p *
        iteratedDeriv p (modelPhase σ) u ∧
      modelPhaseJetSign σ p * iteratedDeriv p (modelPhase σ) u ≤
        modelPhaseJetCoefficient σ p := by
  pm_977 hc
  have he := iteratedDerivWithin_modelPhase σ p ⟨hu.1.le,hu.2.le⟩
  pm_6807 hc he
  rw [he,← mul_assoc,modelPhaseJetSign_coefficient]
  have hneg : -σ-(p : ℝ) ≤ 0 := by
    pm_322 hp p
    linarith
  have hlo := Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans hu.1) hu.2.le hneg
  have hhi := Real.rpow_le_one_of_one_le_of_nonpos hu.1.le hneg
  have hcoef := (modelPhaseJetCoefficient_pos hσ p).le
  constructor
  · have h := mul_le_mul_of_nonneg_left hlo hcoef
    dsimp only [modelPhaseJetLower]
    linarith
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left hhi hcoef
end

theorem approximateModelPhase_signedJet_bounds
    {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hF : IsApproximateModelPhaseFunction F σ P δ)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) (p : ℕ) (hp : p ≤ P)
    (hδ : δ ≤ min (modelPhaseJetLower σ p) 1) :
    modelPhaseJetLower σ p ≤ modelPhaseJetSign σ p * iteratedDeriv (p+1) F u ∧
      modelPhaseJetSign σ p * iteratedDeriv (p+1) F u ≤
        modelPhaseJetCoefficient σ p+1 := by
  have he := approximateModelPhase_iteratedDeriv_error hF hu p hp
  have hs : |modelPhaseJetSign σ p * iteratedDeriv (p+1) F u -
      modelPhaseJetSign σ p * iteratedDeriv p (modelPhase σ) u| ≤ δ := by
    rw [← mul_sub,abs_mul,modelPhaseJetSign_abs,one_mul]
    exact he
  rw [abs_le] at hs
  have hb := modelPhase_signed_referenceJet_bounds hσ hu p
  pm_4998 hd₀ hδ.trans hd₁
  constructor <;> linarith

end TaoTrudgianYang2025
