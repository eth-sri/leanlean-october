module
public import OAI.NumberTheory.DirichletL.Descent.ReopenedIdentification

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
local notation "O" => ActualEisensteinCubic.O

def markedReopenedCubeBin {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ))
    (Ψ : O→*ℂ) (m f z : O) (W : ℝ→ℂ) (X H₀ : ℝ)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) : ℂ :=
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  let Ψrow := rowTwist Ψ (m*excludedGenerator S) f z
  ∑ v∈Q,(largeCubeCoefficient H₀ (cubeIdeal F v)*cubeWeight Ψrow (cubeIdeal F v)*
    (Real.sqrt (X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3):ℂ)⁻¹)*
    ∑' I:Ideal O,columnWeight Ψrow I*W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3))*
      indexedIdealMark (fun i:primePool F=>i.val) slots lists a (I*cubeIdeal F v^3)

theorem original_marked_split_to_bins {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Ψ : O→*ℂ) (m f z : O) (W : ℝ→ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hX : 0<X) (hW : ∀ t,W t≠0→t≤b) (hD : b*X≤D)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let Ψrow := rowTwist Ψ (m*excludedGenerator S) f z
    let mark := indexedIdealMark (fun i:primePool F=>i.val) slots lists a
    (Real.sqrt X:ℂ)⁻¹*outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X =
      (∑' H:Ideal O,if (Ideal.absNorm H:ℝ)<H₀ then
        (UniqueFactorizationMonoid.moebius H:ℂ)*cubeWeight Ψrow H*
          markedCompletedT Ψrow W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark (H^3*I)) else 0) +
      markedReopenedCubeBin S D ((outsideIdealsUpTo S D).image (cubeIndex F)) Ψ m f z W X H₀ slots lists a := by
  rw [outsideCanonicalMarkedRow_reopened S D hbad hSp Ψ m f z W hWc b X H₀ hX hW hD]
  dsimp only
  rw [sum_outside_cubeIndex S D]
  rfl

end
end SevenEighths.InverseMoment

end OAI
