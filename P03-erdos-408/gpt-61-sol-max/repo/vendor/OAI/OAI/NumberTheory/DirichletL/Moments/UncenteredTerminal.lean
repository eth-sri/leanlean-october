module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.TerminalEnergy
public import OAI.NumberTheory.DirichletL.Moments.AbsoluteEnergy

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentUncenteredTerminal
open HeckeFamily CenteredMomentAbsoluteEnergy CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentRectangle


def uncenteredProfileCoefficient {ι } [Fintype ι]
    (R : Ideal ActualEisensteinCubic.O) (ν : ι → Ideal ActualEisensteinCubic.O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (B₁ B₂ s : Ideal ActualEisensteinCubic.O) (v : Tuple ι)  :=
  (∏ j,ν j (v (Sum.inl j))*Wslot j ((Ideal.absNorm (v (Sum.inl j)):ℝ)/P j))*
    (if IsCoprime (finiteTupleProduct v) R then 1 else 0)*
    (W₁ ((Ideal.absNorm (B₁*v (Sum.inr 0)):ℝ)/X₁)*
      W₂ ((Ideal.absNorm (B₂*v (Sum.inr 1)):ℝ)/X₂))*
    (if s∣finiteTupleProduct v then 1 else 0)

def comparisonScale (b : ℝ)  := 1/(2*max 1 b)

lemma comparisonScale_pos  b  : 0<comparisonScale b := by
  
  unfold comparisonScale
  positivity

theorem comparison_first_zero (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (B I : Ideal ActualEisensteinCubic.O) (hB : B≠0) :
    W ((Ideal.absNorm (B*I):ℝ)/comparisonScale b)=0 := by
  by_contra h
  have ht := hs h
  by_cases hI : I=0
  · simp only [hI,mul_zero,map_zero,Nat.cast_zero,zero_div,Set.mem_Icc] at ht
    linarith [ht.1]
  have hn : 1≤(Ideal.absNorm (B*I):ℝ) :=
    QuadraticMainBoundary.norm_one_le (mul_ne_zero hB hI)
  have hmax : 1≤max 1 b := le_max_left _ _
  have hb : b≤max 1 b := le_max_right _ _
  have harg : (Ideal.absNorm (B*I):ℝ)/comparisonScale b=
      (Ideal.absNorm (B*I):ℝ)*(2*max 1 b) := by
    simp [comparisonScale,div_eq_mul_inv]
  rw [harg] at ht
  have hupper := ht.2
  nlinarith

theorem profileCoefficient_eq_uncentered {ι : Type*} [Fintype ι]
    (R : Ideal ActualEisensteinCubic.O) (ν : ι → Ideal ActualEisensteinCubic.O → ℂ)  Wslot   P 
     W₁ W₂  (a₁ b₁ : ℝ) (ha₁ : 0<a₁)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁)
     X₁ X₂ Y₂   B₁ B₂ s  (hB₁ : B₁≠0) :
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ (comparisonScale b₁) Y₂ B₁ B₂ s=
      uncenteredProfileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ B₁ B₂ s := by
  funext v
  simp only [profileCoefficient,idealRectangle,
    comparison_first_zero W₁ a₁ b₁ ha₁ hs₁ B₁ (v (Sum.inr 0)) hB₁,
    zero_mul,sub_zero,uncenteredProfileCoefficient]

end SevenEighths.CenteredMomentUncenteredTerminal

end

end OAI
