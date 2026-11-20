module

public import OAI.NumberTheory.DirichletL.Descent.SecondCellPhysical
public import OAI.NumberTheory.DirichletL.Descent.SecondPuncture
public import OAI.NumberTheory.DirichletL.Descent.SecondNormalizedEnergy

@[expose] public section

namespace OAI.SevenEighths.InverseMoment
open scoped Classical
open FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks InverseInitialClippedColumns
open InverseSecondFibers
local notation "Eis" => ActualEisensteinCubic.O

/-- A normalized second-child estimate for every occupied cell and every erased
set of slots, with the specified test and its growth bound. -/
abbrev WithSecondCellEnergy {ι σ T : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [PrincipalFamily.Maximal p]
    (hcop : PrincipalFamily.Coprime p) (hg : PrincipalFamily.Avoids p ConcretePrimeRowBridge.goodLambda)
    (pool : Finset ι) {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0)) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : BlockIndex → Finset (Ideal Eis)) (R Vlabel : BlockIndex → ℝ) (Z X ε A : ℝ) (K : ℕ)
    (W : BlockIndex → T → ℝ → ℂ) (growth : T → ℝ) : Prop :=
  ∀ d∈keys p source, ∀ t : T, ∀ J∈slots.powerset, ∀ γ∈actualSecondTriples p 1 1 (cell p source d),
    let N := max 0 (secondCellColumnExponent Z X d)
    normalizedColumnEnergy p hp hcop hg pool Ψ (actualSecondInheritedRadicalPuncture m γ)
      (slots\J) lists a ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d))
      (secondLabelWeight K) (W d t) (Z^N) Z (N+Vlabel d) ≤ A*Z^(N+Vlabel d+ε)*growth t

end OAI.SevenEighths.InverseMoment
