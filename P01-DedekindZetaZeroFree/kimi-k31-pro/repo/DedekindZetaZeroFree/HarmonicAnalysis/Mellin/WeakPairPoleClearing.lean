module

public import Mathlib.NumberTheory.LSeries.AbstractFuncEq

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

noncomputable section

def poleCleared (P : WeakFEPair ℂ) (s : ℂ) : ℂ :=
  s * (s - 1) * P.Λ₀ s - (s - 1) * P.f₀ + s * P.ε * P.g₀

theorem weakFEPair_differentiableOn_weightOne (P : WeakFEPair ℂ) (hk : P.k = 1) :
    DifferentiableOn ℂ P.Λ {s : ℂ | s ≠ 0 ∧ s ≠ 1} := by
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  exact P.differentiableAt_Λ (Or.inl hs.1) (Or.inl (by simp_all))

theorem poleCleared_differentiable (P : WeakFEPair ℂ) (hk : P.k = 1) :
    Differentiable ℂ (poleCleared P) := by
  unfold poleCleared
  have hΛ := P.differentiable_Λ₀
  fun_prop

theorem poleCleared_eq (P : WeakFEPair ℂ) (hk : P.k = 1) :
    ∀ s : ℂ, s ≠ 0 → s ≠ 1 → poleCleared P s = s * (s - 1) * P.Λ s := by
  intro s hs₀ hs₁
  simp only [poleCleared, WeakFEPair.Λ, hk, Complex.ofReal_one, smul_eq_mul]
  have hs : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs₁)
  field_simp
  <;> ring

theorem weakFEPair_selfDual_reflection (P : WeakFEPair ℂ) (hk : P.k = 1)
    (hg : P.g = P.f) (hg₀ : P.g₀ = P.f₀) (hε : P.ε = 1) :
    ∀ s : ℂ, s ≠ 0 → s ≠ 1 → P.Λ s = P.Λ (1 - s) := by
  have hsymm : P.symm.Λ = P.Λ := by
    unfold WeakFEPair.Λ WeakFEPair.Λ₀ WeakFEPair.f_modif
    simp_all
  intro s _ _
  have h := P.functional_equation (1 - s)
  simp_all

end

end DedekindZetaZeroFree.Hecke
