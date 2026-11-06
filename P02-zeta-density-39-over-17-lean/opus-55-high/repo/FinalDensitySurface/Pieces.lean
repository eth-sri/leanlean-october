module
public import FinalDensitySurface.Providers
import WeylPort.Analytic.RealLaplace

public section
set_option maxHeartbeats 0
namespace FinalDensitySurface
open MathCollab.Density

alias piece_G1 := FinalDensitySurface.provider_P1

set_option hygiene false in
macro "pf_205" x1:term:max x2:term:max x3:ident x4:ident : tactic => `(tactic| (
  by_cases hend : σ = ($x1:term/$x2:term : ℝ)
  · subst σ
    convert ($x3:ident (σ := ($x1:term/$x2:term : ℝ)) (ε := ε) (by norm_num) (by norm_num) hε) using 1
    all_goals norm_num
  · exact $x4:ident (σ := σ) (ε := ε) (by linarith) (lt_of_le_of_ne hhi hend) hε))
/-- Exact literal density statement for plotted piece G2, including its graph endpoints. -/
theorem piece_G2 {σ ε : ℝ} (hlo : (7/10 : ℝ) ≤ σ)
    (hhi : σ ≤ (19/25 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((15/(5*σ + 3))*(1-σ)) + ε) := by pf_205 19 25 provider_P3 provider_P2

alias piece_G3 := FinalDensitySurface.provider_P3

alias piece_G4 := FinalDensitySurface.provider_P4

/-- Exact literal density statement for plotted piece G5, including its graph endpoints. -/
theorem piece_G5 {σ ε : ℝ} (hlo : (13/17 : ℝ) ≤ σ)
    (hhi : σ ≤ (17/22 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((6/(5*σ - 1))*(1-σ)) + ε) := by pf_205 17 22 provider_P6 provider_P5

alias piece_G6 := FinalDensitySurface.provider_P6

/-- Exact literal density statement for plotted piece G7, including its graph endpoints. -/
theorem piece_G7 {σ ε : ℝ} (hlo : (41/53 : ℝ) ≤ σ)
    (hhi : σ ≤ (7/9 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((9/(7*σ - 1))*(1-σ)) + ε) := by
  by_cases hend : σ = (7/9 : ℝ)
  · subst σ
    convert (provider_P8 (σ := (7/9 : ℝ)) (ε := ε) (by norm_num) (by norm_num) hε) using 1
    all_goals norm_num
  · exact provider_P7 (σ := σ) (ε := ε) (by linarith) (lt_of_le_of_ne hhi hend) hε

/-- Exact literal density statement for plotted piece G8, including its graph endpoints. -/
theorem piece_G8 {σ ε : ℝ} (hlo : (7/9 : ℝ) ≤ σ)
    (hhi : σ < (23/29 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((9/(16*σ - 8))*(1-σ)) + ε) := by
  pm_3940 provider_P8

/-- Exact literal density statement for plotted piece G9, including its graph endpoints. -/
theorem piece_G9 {σ ε : ℝ} (hlo : (23/29 : ℝ) ≤ σ)
    (hhi : σ ≤ (7/8 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((3/(2*σ))*(1-σ)) + ε) := by
  pm_3940 provider_P9

section
variable {σ ε : ℝ}
include σ ε
/-- Exact literal density statement for plotted piece G10, including its graph endpoints. -/
theorem piece_G10 (hlo : (7/8 : ℝ) ≤ σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((3/(10*σ - 7))*(1-σ)) + ε) := by
  pm_3941

/-- Exact literal density statement for plotted piece B1, including its graph endpoints. -/
theorem piece_B1 (hlo : (1/2 : ℝ) ≤ σ)
    (hhi : σ ≤ (9/13 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((-3/(σ - 2))*(1-σ)) + ε) := by
  pm_3940 provider_P1

alias piece_B2 := FinalDensitySurface.provider_P11

/-- Exact literal density statement for plotted piece B3, including its graph endpoints. -/
theorem piece_B3 (hlo : (5/7 : ℝ) ≤ σ)
    (hhi : σ ≤ (11/15 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((9/4)*(1-σ)) + ε) := by
  pm_3940 provider_P12

/-- Exact literal density statement for plotted piece B4, including its graph endpoints. -/
theorem piece_B4 (hlo : (11/15 : ℝ) ≤ σ)
    (hhi : σ ≤ (3/4 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((15/(5*σ + 3))*(1-σ)) + ε) := by
  pm_3940 provider_P2

/-- Exact literal density statement for plotted piece B5, including its graph endpoints. -/
theorem piece_B5 (hlo : (3/4 : ℝ) < σ)
    (hhi : σ ≤ (7/8 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((3/(2*σ))*(1-σ)) + ε) := by
  pm_3940 provider_P13

/-- Exact literal density statement for plotted piece B6, including its graph endpoints. -/
theorem piece_B6 (hlo : (7/8 : ℝ) ≤ σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((3/(10*σ - 7))*(1-σ)) + ε) := by
  pm_3941

/-- Exact literal density statement for plotted piece O1, including its graph endpoints. -/
theorem piece_O1 (hlo : (1/2 : ℝ) ≤ σ)
    (hhi : σ ≤ (9/13 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((-3/(σ - 2))*(1-σ)) + ε) := by
  pm_3940 provider_P1

/-- Exact literal density statement for plotted piece O2, including its graph endpoints. -/
theorem piece_O2 (hlo : (9/13 : ℝ) ≤ σ)
    (hhi : σ ≤ (12/17 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((18/(7*σ+3))*(1-σ)) + ε) := by
  pm_3940 provider_P11

/-- Exact literal density statement for plotted piece O3, including its graph endpoints. -/
theorem piece_O3 (hlo : (12/17 : ℝ) ≤ σ)
    (hhi : σ ≤ (5/7 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((6/(8*σ-3))*(1-σ)) + ε) := by
  pm_3940 provider_P14

alias piece_O4 := FinalDensitySurface.provider_P15

alias piece_O5 := FinalDensitySurface.provider_P16

/-- Exact literal density statement for plotted piece O6, including its graph endpoints. -/
theorem piece_O6 (hlo : (3/4 : ℝ) < σ)
    (hhi : σ ≤ (7/9 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((3/(2*σ))*(1-σ)) + ε) := by
  pm_3940 provider_P13

alias piece_O7 := FinalDensitySurface.provider_P17

alias piece_O8 := FinalDensitySurface.provider_P18

alias piece_O9 := FinalDensitySurface.provider_P19

alias piece_O10 := FinalDensitySurface.provider_P20

alias piece_O11 := FinalDensitySurface.provider_P21

alias piece_O12 := FinalDensitySurface.provider_P22

alias piece_O13 := FinalDensitySurface.provider_P23

alias piece_O14 := FinalDensitySurface.provider_P24

alias piece_O15 := FinalDensitySurface.provider_P25

alias piece_O16 := FinalDensitySurface.provider_P26

alias piece_O17 := FinalDensitySurface.provider_P27

alias piece_O18 := FinalDensitySurface.provider_P28

/-- Exact literal density statement for plotted piece O19, including its graph endpoints. -/
theorem piece_O19 (hlo : (7/8 : ℝ) ≤ σ)
    (hhi : σ ≤ (24139/27578 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ ((1086/5537) + ε) := by
  pm_3940 provider_P29

/-- Exact literal density statement for plotted piece O20, including its graph endpoints. -/
theorem piece_O20 (hlo : (24139/27578 : ℝ) ≤ σ)
    (hhi : σ ≤ (23/26 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((24/(30*σ-11))*(1-σ)) + ε) := by
  pm_3940 provider_P30

/-- Exact literal density statement for plotted piece O21, including its graph endpoints. -/
theorem piece_O21 (hlo : (23/26 : ℝ) ≤ σ)
    (hhi : σ ≤ (17/19 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((6/(σ+3))*(1-σ)) + ε) := by
  pm_3940 provider_P31

/-- Exact literal density statement for plotted piece O22, including its graph endpoints. -/
theorem piece_O22 (hlo : (17/19 : ℝ) ≤ σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((3/(10*σ - 7))*(1-σ)) + ε) := by
  pm_3941
end

/-- One constant before all cutoffs on the full plateau range. -/
theorem uniform_P29 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (7/8 : ℝ) ≤ σ → σ ≤ 1 → 2 ≤ T →
      ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ ((1086/5537 : ℝ) + ε) := by
  pm_102 C hC h Montgomery.MonotoneCurve.seven_eighths_right_uniform hε
  pm_7432 _hhi
  exact h σ hlo T hT

section
variable {ε : ℝ} (hε : 0 < ε)
include ε hε
/-- Verified recovered-family uniform quantifier order, separate from original analytic-route status. -/
theorem uniform_P30 :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (19/22 : ℝ) ≤ σ → σ ≤ (23/26 : ℝ) → 2 ≤ T →
      ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((24/(30*σ-11))*(1-σ)) + ε) := by pm_3942 Montgomery.WrittenDensity.uniform_source_oct2_mixed_4

/-- Verified recovered-family uniform quantifier order, separate from original analytic-route status. -/
theorem uniform_P31 :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (23/26 : ℝ) ≤ σ → σ ≤ (1 : ℝ) → 2 ≤ T →
      ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((6/(σ+3))*(1-σ)) + ε) := by pm_3942 Montgomery.WrittenDensity.uniform_source_oct2_mixed_5
end

end FinalDensitySurface
