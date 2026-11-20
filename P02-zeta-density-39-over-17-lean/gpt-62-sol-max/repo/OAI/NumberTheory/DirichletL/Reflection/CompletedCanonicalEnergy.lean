module
public import OAI.NumberTheory.DirichletL.Reflection.CanonicalFrozenEnergy
public import OAI.NumberTheory.DirichletL.Reflection.CompletedFiberSource
public import OAI.NumberTheory.DirichletL.Reflection.CanonicalCellArithmetic

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

lemma maximal_prime_level_coprime (P : Ideal Eis) (hP : P.IsMaximal)
    (hg : ConcretePrimeRowBridge.goodLambda∉P) (Q₀ : Ideal Eis) (c : Eis)
    (hc : Ideal.span {c}=Ideal.span {(9:Eis)}*Q₀) (hQ : IsCoprime Q₀ P) :
    IsCoprime (Ideal.span {(9:Eis)*c}) P := by
  let S : PrimeFamily Unit := ⟨fun _ => P,fun _ => hP,fun _ => hg⟩
  exact S.level_coprime Q₀ c hc (fun _ => hQ) ()

lemma original_powerful_norm_le (J : Ideal Eis) (hJ : J≠0) :
    (Ideal.absNorm (rowPowerfulPart J):ℝ)≤(Ideal.absNorm J:ℝ) := by
  have he := congrArg (fun I : Ideal Eis => (Ideal.absNorm I:ℝ)) (row_powerful_simple_product J hJ)
  simp only [map_mul,Nat.cast_mul] at he
  have hs := QuadraticMainBoundary.norm_one_le (rowSimplePart_ne_zero J)
  have hp : (0:ℝ)≤Ideal.absNorm (rowPowerfulPart J) := Nat.cast_nonneg _
  nlinarith

/-- Transport the residual row estimate back to the original fiber, separating the
powerful-part charge from the scale exponent. -/
lemma completed_fiber_energy_transfer (parents : Finset (Ideal Eis)) (J Q : Ideal Eis)
    (hp : ∀ I∈parents, I≠0) (f : Ideal Eis→ℂ) (g : originalResidualRows parents J Q→ℂ)
    (heq : ∀ K, f (reconstructFiberRow J Q K.val)=g K) {C Z a : ℝ} (hz : 1<Z)
    (he : (∑ K, ‖g K‖^2)≤C*Z^(a-normWidth Z (rowPowerfulPart J)/2)) :
    (∑ I∈representativeRowFiber parents J Q,‖f I‖^2)≤
      C*Z^a*(Ideal.absNorm (rowPowerfulPart J):ℝ)^(-(1/2:ℝ)) := by
  rw [original_fiber_energy_reindex parents J Q hp f, ←Finset.sum_coe_sort]
  simp_rw [heq]
  apply he.trans_eq
  have hz0 := zero_lt_one.trans hz
  have hp0 := InverseMoment.actual_ideal_norm_pos (rowPowerfulPart J) (rowPowerfulPart_ne_zero J)
  rw [show a-normWidth Z (rowPowerfulPart J)/2=a+normWidth Z (rowPowerfulPart J)*(-(1/2:ℝ)) by ring,
    Real.rpow_add hz0, Real.rpow_mul hz0.le, normWidth, Real.rpow_logb hz0 (ne_of_gt hz) hp0, mul_assoc]

end
end SevenEighths.InverseReflectedPhase

end OAI
