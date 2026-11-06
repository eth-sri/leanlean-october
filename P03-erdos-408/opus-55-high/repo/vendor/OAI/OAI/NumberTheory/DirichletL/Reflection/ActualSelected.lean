module

public import OAI.NumberTheory.DirichletL.Reflection.SelectedExpansion
public import OAI.NumberTheory.DirichletL.Reflection.MarkedActualSource

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical ContDiff
open CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
variable {σ : Type*} [Fintype σ] {m f z : ActualEisensteinCubic.O} (D : GoodMaskRowData m f z)
variable (R I F Q : Ideal ActualEisensteinCubic.O) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime (Q*Ideal.span {(72:ActualEisensteinCubic.O)}) (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
variable (S : PrimeFamily σ)
local notation "E" => D.primeFiberEquiv R I F (Q*Ideal.span {(72:ActualEisensteinCubic.O)}) hR hI hF hm hf hz hbad hcop hpow hmask
local notation "K" => rowResidualPart I (Ideal.span (Set.singleton m)*F)
local notation "hK" => rowResidualPart_admissible I (Ideal.span (Set.singleton m)*F) hbad
local notation "Pall" => PrimeFamily.sum (freePrimeFamily D.movingIdeal (Q*Ideal.span {(72:ActualEisensteinCubic.O)}) D.movingSupported) S
local notation "Jall" => Sum.elim (fun P : FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:ActualEisensteinCubic.O)}) =>
  Multiset.count (Subtype.val (Subtype.val P)) (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal)%6) (fun _ : σ => 0)

include hR hI hF hm hf hz hbad hcop hpow hmask

theorem actual_marked_selected_reflection
    (hS : Pairwise (Function.onFun IsCoprime S.ideal))
    (hSodd : ∀ i, ringChar (ActualEisensteinCubic.O⧸S.ideal i)≠2)
    (hdis : ∀ P : FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:ActualEisensteinCubic.O)}), ∀ i, S.ideal i≠P.val.val)
    (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨnorm : ∀ n, ‖Ψ n‖≤1) (hQ : Q≠0)
    (hΨperiod : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:ActualEisensteinCubic.O)∣m)
    (c : ActualEisensteinCubic.O) (hc : c≠0) [Fintype (ActualEisensteinCubic.O⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:ActualEisensteinCubic.O)}*(Q*Ideal.span {(72:ActualEisensteinCubic.O)}))
    (G : ∀ h : ActualEisensteinCubic.O⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : ActualEisensteinCubic.O) (hN : ∀ h, (9:ActualEisensteinCubic.O)*(G h).c0∣N)
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) ((Pall).ideal i))
    (C : ∀ h : ActualEisensteinCubic.O⧸Ideal.span {c}, ∀ B : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:ActualEisensteinCubic.O)})),
      ∀ T : Finset σ, ControlledStratumArithmetic
        (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:ActualEisensteinCubic.O)})).restrict B).reflected K hK (S.restrict T)).generator
        N (G h).a0 (G h).c0 (G h).mode)
    (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    markedCompletedT (rowTwist Ψ m f z) W X
      (fun A => ∏ i, if S.ideal i∣A then (1:ℂ) else 0)=
    thetaDerivativeScalar⁻¹*∑ h : ActualEisensteinCubic.O⧸Ideal.span {c}, fixedThetaRowCoeff c hc (D.fixedFactor Ψ Q) h *
      ∑ B : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:ActualEisensteinCubic.O)})), ∑ T : Finset σ,
        ((∏ b∈(Finset.univ:Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:ActualEisensteinCubic.O)})))\B,
          if completedLocalExponent R F b.val=0 then 1-(Ideal.absNorm b.val:ℂ)⁻¹ else 0)*
          ∏ t∈(Finset.univ:Finset σ)\T,(Ideal.absNorm (S.ideal t):ℂ)⁻¹)*
        mixedReflectedValue (C h B T) (G h).shape
          (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:ActualEisensteinCubic.O)})).restrict B).reflected K hK (S.restrict T)).generator_ne_zero
          (G h).denominator_ne_zero
          (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:ActualEisensteinCubic.O)})).restrict B).reflected K hK (S.restrict T)).generator_good
          (reflectedExponent (fun b : B => completedLocalExponent R F b.val.val))
          (slotIndices B (PrimeIndex K) T) W X := by
  have hQ0 : (Q*Ideal.span {(72:ActualEisensteinCubic.O)})≠0 := by
    apply mul_ne_zero hQ
    simp only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot]
    norm_num
  exact (actual_marked_row_eq_joined D S Ψ Q hmLam hm2 W X).trans
    (original_selected_reflected_expansion D R I F (Q*Ideal.span {(72:ActualEisensteinCubic.O)}) hR hI hF hm hf hz hbad hcop hpow hmask S
      hS hSodd hdis (D.fixedFactor Ψ Q) (D.fixedFactor_norm Ψ Q hΨnorm) hQ0
      (D.fixedFactor_periodic Ψ Q hΨperiod) c hc hcQ G N hN hNp C W hWcompact lo hi hlo hsupp hW X hX)
end
end SevenEighths.InverseReflectedPhase

end OAI
