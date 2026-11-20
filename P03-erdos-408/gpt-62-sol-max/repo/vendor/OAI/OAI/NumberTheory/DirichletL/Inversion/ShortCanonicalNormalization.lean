module

public import OAI.NumberTheory.DirichletL.Descent.ShortReflectedPower
public import OAI.NumberTheory.DirichletL.Descent.SecondNormalizedEnergy

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseShortCanonicalNormalization
open ActualEisensteinCubic IdealMobiusDivisorSum CompletedGauss CanonicalRowCompletion InverseMoment
open InverseReflectedPhase InverseTerminalWidths CompletedHeight
local notation "Eis" => ActualEisensteinCubic.O
lemma divisor_weight_sum (K : ℕ) (L ε : ℝ) (hL : 0≤L) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (Z V : ℝ),1≤Z → 0≤V → V≤L →
      ∀ labels : Finset (Ideal Eis),
      (∀ f∈labels,f≠0 ∧ (Ideal.absNorm f:ℝ)≤Z^V) →
      (∑ f∈labels,((idealDivisors f).card:ℝ)^(9+4*K))≤C*Z^(V+ε) := by
  let n : ℕ := 9+4*K
  have hn : (0:ℝ)<n := by positivity
  let δ : ℝ := ε/((L+1)*(n:ℝ))
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨D,hD,hd⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨128*D^n,by positivity,?_⟩
  intro Z V hZ hV hVL labels hf
  have hz  := zero_lt_one.trans_le hZ
  have hbudget : L*(δ*(n:ℝ))≤ε := by
    have heq : (L+1)*(δ*(n:ℝ))=ε := by dsimp [δ]; field_simp
    nlinarith [mul_pos hδ hn]
  have hb (f : Ideal Eis) (hfl : f∈labels) :
      ((idealDivisors f).card:ℝ)^n≤D^n*Z^ε := by
    have hfN  :=
      (hf f hfl).2.trans (Real.rpow_le_rpow_of_exponent_le hZ hVL)
    calc
      _ ≤ (D*(Ideal.absNorm f:ℝ)^δ)^n := by gcongr; exact hd f (hf f hfl).1
      _ = D^n*(Ideal.absNorm f:ℝ)^(δ*(n:ℝ)) := by
        rw [mul_pow,Real.rpow_mul_natCast (Nat.cast_nonneg _)]
      _ ≤ D^n*(Z^L)^(δ*(n:ℝ)) := by gcongr
      _ = D^n*Z^(L*(δ*(n:ℝ))) := by rw [←Real.rpow_mul hz.le]
      _ ≤ _ := by gcongr
  have hc := DescentFiberCost.finite_ideal_count_real labels (Z^V)
    (Real.one_le_rpow hZ hV) (fun f hfl => (hf f hfl).1) (fun f hfl => (hf f hfl).2)
  calc
    _ ≤ ∑ _f∈labels,D^n*Z^ε := Finset.sum_le_sum (fun f hfl => hb f hfl)
    _ = (labels.card:ℝ)*(D^n*Z^ε) := by rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (128*Z^V)*(D^n*Z^ε) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = (128*D^n)*Z^(V+ε) := by rw [Real.rpow_add hz]; ring

end SevenEighths.InverseShortCanonicalNormalization

end

end OAI
