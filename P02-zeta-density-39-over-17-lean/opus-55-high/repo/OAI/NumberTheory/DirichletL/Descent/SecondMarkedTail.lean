module
public import OAI.NumberTheory.DirichletL.Descent.SecondWholeCutoff
public import OAI.NumberTheory.DirichletL.Inversion.SecondPrincipalCaller
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstCauchyArithmetic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open InversePrincipalEnergy InverseSecondPrincipalCaller
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem marked_radial_uniform_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ Cm : ℝ, 0 < Cm ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → O) (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i ∈ slots, ∀ k ∈ lists i, ‖a i k‖ ≤ 1) →
      ∀ (A : Finset ι) (V : 𝓢(ℝ,ℂ)) (X M : ℝ), 0 < X →
      (∀ u, V u ≠ 0 → u ≤ Real.exp M) →
      ∀ U, ‖markedRadial p slots lists a A V X U‖ ≤
        (2:ℝ)^A.card * Cm * (X*Real.exp M)^ε * SchwartzMap.seminorm ℝ 0 0 V := by
  pm_69 Cm hCm hmark finite_primeMark_extracted_bound ε hε
  refine ⟨Cm,hCm,?_⟩
  intro ι σ _ _ p hp _ hcop slots lists a hslots ha A V X M hX hV U
  by_cases hz : V (primeProductNorm p U/X) = 0
  · simp only [markedRadial,hz,mul_zero,norm_zero]
    positivity
  · have hn : primeProductNorm p U ≤ X*Real.exp M := by
      pm_7699 hz
    pm_8850 hn0 U
    rw [markedRadial,norm_mul]
    apply (mul_le_mul (hmark p hp hcop slots lists a hslots ha A U)
      (V.norm_le_seminorm ℝ _) (norm_nonneg _) (by positivity)).trans
    gcongr

end
end SevenEighths.InverseMoment

end OAI
