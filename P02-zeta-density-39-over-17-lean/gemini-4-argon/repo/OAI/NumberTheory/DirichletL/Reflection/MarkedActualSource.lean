module
public import OAI.NumberTheory.DirichletL.Reflection.MarkedSource

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section

abbrev markedRowFamily {σ : Type*} {m f z : Eis}
    (D : GoodMaskRowData m f z) (S : PrimeFamily σ) (Q : Ideal Eis) :=
  (freePrimeFamily D.movingIdeal (Q*Ideal.span {(72:Eis)}) D.movingSupported).sum S

theorem actual_marked_row_overlap_zero {σ : Type*} [Fintype σ]
    {m f z : Eis} (D : GoodMaskRowData m f z) (S : PrimeFamily σ)
    (Ψ : Eis→*ℂ) (Q : Ideal Eis) (hmLam : λ₀∣m) (hm2 : (2:Eis)∣m)
    (P : FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)})) (i : σ)
    (hPi : S.ideal i=P.val.val) (W : ℝ→ℂ) (X : ℝ) :
    markedCompletedT (rowTwist Ψ m f z) W X
      (fun A => ∏ i, if S.ideal i∣A then (1:ℂ) else 0)=0 := by
  rw [actual_marked_row_fixed_factor D Ψ Q hmLam hm2]
  exact markedCompletedT_free_overlap_zero D.movingIdeal (Q*Ideal.span {(72:Eis)})
    D.movingSupported S P i hPi (D.fixedFactor Ψ Q) W X
