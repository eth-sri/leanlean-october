module

public import OAI.NumberTheory.DirichletL.Descent.MarkedFourier

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped Classical
open CubicEisenstein LocalReflectionBrackets CompletedGauss
noncomputable section

section Local
variable {F : Type*} [Field F] [Fintype F]

def markedFrequencyRow (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (σ ε : Fˣ) (x h : F) : ℂ :=
  finiteAdditiveFourierCoeff ψ zeroMark h * frequencyMultiplier χ ψ σ ε x h

theorem markedFrequencyRow_units (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (σ ε : Fˣ) (x : F) :
    (∑ h : Fˣ, markedFrequencyRow χ ψ σ ε x h) =
      localReflectionActive zeroMark χ ψ σ ε x := by
  unfold markedFrequencyRow finiteAdditiveFourierCoeff frequencyMultiplier localReflectionActive localFourier
  simp only [Units.ne_zero, ite_false,  Units.val_inv_eq_inv_val,
    Finset.mul_sum, neg_mul]
  grind

def mixedFrequencyRow (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (marked : Bool) (j : ℕ) (σ ε : Fˣ) (x h : F) : ℂ :=
  if marked then markedFrequencyRow χ ψ σ ε x h else frequencyRow χ ψ j σ ε x h

end Local

noncomputable local instance markedStratumField (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] : Field (ActualEisensteinCubic.O ⧸ P) :=
  Ideal.Quotient.field P
noncomputable local instance markedStratumFintype (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] : Fintype (ActualEisensteinCubic.O ⧸ P) :=
  Fintype.ofFinite _

theorem actual_mixed_frequency_units (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda ∉ P) (hc : ringChar (ActualEisensteinCubic.O ⧸ P) ≠ 2)
    (ψ : AddChar (ActualEisensteinCubic.O ⧸ P) ℂ) (hψ : ψ.IsPrimitive) (marked : Bool)
    (j : ℕ) (hj : j < 6) (σ ε : (ActualEisensteinCubic.O ⧸ P)ˣ) (x : ActualEisensteinCubic.O ⧸ P) :
    (∑ h : (ActualEisensteinCubic.O ⧸ P)ˣ, mixedFrequencyRow (actualSextic P hg) ψ marked j σ ε x h) =
      if marked then
        (rootCard (ActualEisensteinCubic.O ⧸ P) : ℂ)⁻¹ * tau (actualSextic P hg) ψ 2 *
          (((actualSextic P hg) ^ 2)⁻¹) ((σ : ActualEisensteinCubic.O ⧸ P) * (ε : ActualEisensteinCubic.O ⧸ P) * x)
      else (((actualSextic P hg)⁻¹) ^ 2) σ *
        phase (actualSextic P hg) ψ j ε * bracket (actualSextic P hg) j x := by
  cases marked
  · simp only [mixedFrequencyRow, Bool.false_eq_true, ite_false]
    exact canonical_frequencyRow_units P hg hc ψ hψ j hj σ ε x
  · simp only [mixedFrequencyRow, ite_true]
    rw [markedFrequencyRow_units, actual_marked_active_formula P hg hc ψ hψ σ ε x]

end
end SevenEighths.InverseMoment

end OAI
