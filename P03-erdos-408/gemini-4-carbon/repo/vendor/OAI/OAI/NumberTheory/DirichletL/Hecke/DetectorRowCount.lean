module

public import OAI.NumberTheory.DirichletL.Hecke.DetectorSimultaneous

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorRowCount
open HeckeFamily HeckeDyadic

lemma card_of_energy {α : Type*} (rows : Finset α) (F : α→ℂ)
    (U p b C : ℝ) (hU : 0<U)
    (hspike : ∀ u∈rows, U^p≤‖F u‖^2)
    (henergy : ∑ u∈rows, ‖F u‖^2≤C*U^b) :
    (rows.card : ℝ)≤C*U^(b-p) := by
  have hs : (rows.card : ℝ)*U^p≤C*U^b := by
    calc
      _ = ∑ u∈rows, U^p := by simp
      _ ≤ ∑ u∈rows, ‖F u‖^2 := Finset.sum_le_sum hspike
      _ ≤ _ := henergy
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hU p)).mp
  calc
    _ ≤ C*U^b := hs
    _ = (C*U^(b-p))*U^p := by rw [mul_assoc,←Real.rpow_add hU]; congr 2; ring

theorem inverse_count {α : Type*} (rows : Finset α) (χ : α→Character)
    (W : ℝ→ℂ) (D : ℝ) (σ freq : α→ℝ) (P : α→ℂ)
    (U δ r q z εw εp εm C : ℝ) (hU : 0<U)
    (hM : ∀ u∈rows, U^(δ*r-εw)≤‖polynomial (χ u) true W D (σ u) (freq u)‖^2)
    (hP : ∀ u∈rows, U^(2*q*z-εp)≤‖P u‖^2)
    (henergy : ∑ u∈rows,
      ‖polynomial (χ u) true W D (σ u) (freq u)*P u‖^2≤C*U^(1+εm)) :
    (rows.card : ℝ)≤C*U^(1-δ*r-2*q*z+εw+εp+εm) := by
  have hs (u : α) (hu : u∈rows) :
      U^((δ*r-εw)+(2*q*z-εp))≤‖polynomial (χ u) true W D (σ u) (freq u)*P u‖^2 := by
    rw [Real.rpow_add hU,norm_mul,mul_pow]
    exact mul_le_mul (hM u hu) (hP u hu) (Real.rpow_nonneg hU.le _) (sq_nonneg _)
  have hh := card_of_energy rows _ U _ (1+εm) C hU hs henergy
  convert hh using 1; congr 2; ring

theorem plain_count {α : Type*} (rows : Finset α) (χ : α→Character)
    (W : ℝ→ℂ) (N : ℝ) (σ freq : α→ℝ) (P : α→ℂ)
    (U δ m q z εw εp εm C : ℝ) (hU : 0<U)
    (hS : ∀ u∈rows, U^(δ*m-εw)≤‖polynomial (χ u) false W N (σ u) (freq u)‖^2)
    (hP : ∀ u∈rows, U^(2*q*z-εp)≤‖P u‖^2)
    (henergy : ∑ u∈rows,
      ‖polynomial (χ u) false W N (σ u) (freq u)*
        polynomial (χ u) false W N (σ u) (freq u)*P u‖^2≤C*U^(1+εm)) :
    (rows.card : ℝ)≤C*U^(1-2*δ*m-2*q*z+2*εw+εp+εm) := by
  have hs (u : α) (hu : u∈rows) :
      U^((δ*m-εw)+(δ*m-εw)+(2*q*z-εp))≤
        ‖polynomial (χ u) false W N (σ u) (freq u)*
          polynomial (χ u) false W N (σ u) (freq u)*P u‖^2 := by
    rw [Real.rpow_add hU,Real.rpow_add hU,norm_mul,norm_mul,mul_pow,mul_pow]
    exact mul_le_mul (mul_le_mul (hS u hu) (hS u hu) (Real.rpow_nonneg hU.le _) (sq_nonneg _))
      (hP u hu) (Real.rpow_nonneg hU.le _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hh := card_of_energy rows _ U _ (1+εm) C hU hs henergy
  convert hh using 1; congr 2; ring

end SevenEighths.HeckeDetectorRowCount

end

end OAI
