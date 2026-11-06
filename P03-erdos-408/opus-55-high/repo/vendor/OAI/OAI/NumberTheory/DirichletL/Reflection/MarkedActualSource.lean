module

public import OAI.NumberTheory.DirichletL.Reflection.MarkedSource

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical
open CanonicalRowCompletion InverseMoment
noncomputable section

abbrev markedRowFamily {σ : Type*} {m f z : ActualEisensteinCubic.O}
    (D : GoodMaskRowData m f z) (S : PrimeFamily σ) (Q : Ideal ActualEisensteinCubic.O) :=
  (freePrimeFamily D.movingIdeal (Q*Ideal.span {(72:ActualEisensteinCubic.O)}) D.movingSupported).sum S

theorem actual_marked_row_overlap_zero {σ : Type*} [Fintype σ]
    {m f z : ActualEisensteinCubic.O} (D : GoodMaskRowData m f z) (S : PrimeFamily σ)
    (Ψ : ActualEisensteinCubic.O→*ℂ) (Q : Ideal ActualEisensteinCubic.O) (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:ActualEisensteinCubic.O)∣m)
    (P : FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:ActualEisensteinCubic.O)})) (i : σ)
    (hPi : S.ideal i=P.val.val) (W : ℝ→ℂ) (X : ℝ) :
    markedCompletedT (rowTwist Ψ m f z) W X
      (fun A => ∏ i, if S.ideal i∣A then (1:ℂ) else 0)=0 := by
  rw [actual_marked_row_fixed_factor D Ψ Q hmLam hm2]
  exact markedCompletedT_free_overlap_zero D.movingIdeal (Q*Ideal.span {(72:ActualEisensteinCubic.O)})
    D.movingSupported S P i hPi (D.fixedFactor Ψ Q) W X

end
end SevenEighths.InverseReflectedPhase

end OAI
