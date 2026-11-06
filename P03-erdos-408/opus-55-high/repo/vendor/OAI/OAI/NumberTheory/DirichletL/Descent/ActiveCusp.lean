module

public import OAI.NumberTheory.DirichletL.Descent.CuspCongruence
public import OAI.NumberTheory.DirichletL.Descent.MarkedStratum

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped Classical
open CubicEisenstein ConcreteTraceCRT
noncomputable section
noncomputable local instance activeQuotientFintype (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] :
    Fintype (ActualEisensteinCubic.O ⧸ P) := Fintype.ofFinite _

variable {ι : Type*} [Fintype ι]

def localInactiveWeight (p : ι → ActualEisensteinCubic.O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (F : ∀ i, (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) → ℂ) (A : Finset ι) : ℂ :=
  ∏ i ∈ (Finset.univ : Finset ι) \ A,
    finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i)) (F i) 0

def localActiveWeight (p : ι → ActualEisensteinCubic.O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (F : ∀ i, (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) → ℂ)
    (A : Finset ι) (v : ∀ i : A, (ActualEisensteinCubic.O ⧸ Ideal.span {p i.val})ˣ) : ℂ :=
  ∏ i : A, finiteAdditiveFourierCoeff (quotientTrace (p i.val) (hp i.val)) (F i.val) (v i)

theorem primeFunction_fourier_by_active
    (p : ι → ActualEisensteinCubic.O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (F : ∀ i, (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) → ℂ) (n : ActualEisensteinCubic.O) :
    (∏ i, F i (Ideal.Quotient.mk _ n)) =
      ∑ A : Finset ι, localInactiveWeight p hp F A *
        ∑ v : ∀ i : A, (ActualEisensteinCubic.O ⧸ Ideal.span {p i.val})ˣ,
          localActiveWeight p hp F A v *
            ∏ i : A, quotientTrace (p i.val) (hp i.val)
              ((v i : ActualEisensteinCubic.O ⧸ Ideal.span {p i.val}) * Ideal.Quotient.mk _ n) := by
  let (i : ι) : Field (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) := Ideal.Quotient.field _
  have hpow : (Finset.univ : Finset ι).powerset = (Finset.univ : Finset (Finset ι)) := by
    ext A
    simp
  simpa only [hpow, localInactiveWeight, localActiveWeight] using
    FixedRayActiveSet.fourier_inversion_by_active_set (fun i => ActualEisensteinCubic.O ⧸ Ideal.span {p i})
      (fun i => quotientTrace (p i) (hp i))
      (fun i => GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive (p i) (hp i)) F
      (fun i => Ideal.Quotient.mk _ n)

theorem activeStratum_function_multiplier
    (p : ι → ActualEisensteinCubic.O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hprimary : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ p i - 1)
    (F : ∀ i, (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) → ℂ)
    {N a0 c0 : ActualEisensteinCubic.O} {mode : Bool}
    (D : ∀ A : Finset ι, ControlledStratumArithmetic (fun i : A => p i.val) N a0 c0 mode)
    (hN : (9 : ActualEisensteinCubic.O) * c0 ∣ N) (hc0 : c0 ≠ 0)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda ^ 2 ∣ a0 - 1 else ConcretePrimeRowBridge.goodLambda ^ 2 ∣ c0 - 1)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode)) (n : ActualEisensteinCubic.O) :
    (∑ A : Finset ι, localInactiveWeight p hp F A *
      ∑ v : ∀ i : A, (ActualEisensteinCubic.O ⧸ Ideal.span {p i.val})ˣ,
        localActiveWeight p hp F A v * ShortDraftTrace.breveE (-cuspFrequency n *
          (activeStratumDatum p hp hprimary D hN hc0 hbase s A v).point)) =
      ShortDraftTrace.breveE (-cuspFrequency n * (eisEmbedding a0 / eisEmbedding c0)) *
        ∏ i, F i (Ideal.Quotient.mk _ n) := by
  have hlocal (A : Finset ι) (v : ∀ i : A, (ActualEisensteinCubic.O ⧸ Ideal.span {p i.val})ˣ) :
      ShortDraftTrace.breveE (-cuspFrequency n *
        (activeStratumDatum p hp hprimary D hN hc0 hbase s A v).point) =
      ShortDraftTrace.breveE (-cuspFrequency n * (eisEmbedding a0 / eisEmbedding c0)) *
        ∏ i : A, quotientTrace (p i.val) (hp i.val)
          ((v i : ActualEisensteinCubic.O ⧸ Ideal.span {p i.val}) * Ideal.Quotient.mk _ n) :=
    (D A).datum_fourier_phase hN
      (primary_finset_product Finset.univ (fun i : A => p i.val) (fun i _ => hprimary i.val))
      hbase s (by grind) hc0 v n
  simp_rw [hlocal]
  rw [primeFunction_fourier_by_active p hp F n]
  simp only [Finset.mul_sum]
  grind

def fixedActiveFunctionWeight
    (p : ι → ActualEisensteinCubic.O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (F : ∀ i, (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) → ℂ)
    (c : ActualEisensteinCubic.O) (hc : c ≠ 0) [Fintype (ActualEisensteinCubic.O ⧸ Ideal.span {c})]
    (φ : ActualEisensteinCubic.O →* ℂ) (t : FixedActiveCuspIndex c p) : ℂ :=
  fixedThetaRowCoeff c hc φ t.1 * localInactiveWeight p hp F t.2.1 *
    localActiveWeight p hp F t.2.1 t.2.2

theorem fixedActiveFunction_multiplier
    (p : ι → ActualEisensteinCubic.O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hprimary : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ p i - 1)
    (F : ∀ i, (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) → ℂ)
    (c : ActualEisensteinCubic.O) (hc : c ≠ 0) [Fintype (ActualEisensteinCubic.O ⧸ Ideal.span {c})]
    (G : ∀ h : ActualEisensteinCubic.O ⧸ Ideal.span {c}, FixedFourierGeometry c h) (N : ActualEisensteinCubic.O)
    (hN : ∀ h, (9 : ActualEisensteinCubic.O) * (G h).c0 ∣ N)
    (D : ∀ h : ActualEisensteinCubic.O ⧸ Ideal.span {c}, ∀ A : Finset ι,
      ControlledStratumArithmetic (fun i : A => p i.val) N (G h).a0 (G h).c0 (G h).mode)
    (Q : Ideal ActualEisensteinCubic.O) (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : ActualEisensteinCubic.O)} * Q)
    (φ : ActualEisensteinCubic.O →* ℂ) (hφ : CanonicalCoefficientClass.FactorsModulo Q φ) (n : ActualEisensteinCubic.O) :
    (∑ t : FixedActiveCuspIndex c p, fixedActiveFunctionWeight p hp F c hc φ t *
      ShortDraftTrace.breveE (-cuspFrequency n *
        (fixedActiveCuspDatum p hp hprimary c G N hN D t).point)) =
      fixedThetaTwist φ n * ∏ i, F i (Ideal.Quotient.mk _ n) := by
  simp only [Fintype.sum_sigma, fixedActiveFunctionWeight, fixedActiveCuspDatum]
  have hf : (∑ h : ActualEisensteinCubic.O ⧸ Ideal.span {c}, fixedThetaRowCoeff c hc φ h *
      ShortDraftTrace.breveE (-cuspFrequency n * thetaFourierTranslation c h)) = fixedThetaTwist φ n := by
    simp only [fixedThetaRowCoeff]
    rw [thetaFourierTranslation_inversion c hc,
      fixedThetaQuotient_mk φ Q hφ c hcQ]
  rw [← hf, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h hh
  calc
    _ = fixedThetaRowCoeff c hc φ h *
        (∑ A : Finset ι, localInactiveWeight p hp F A *
          ∑ v : ∀ i : A, (ActualEisensteinCubic.O ⧸ Ideal.span {p i.val})ˣ,
            localActiveWeight p hp F A v * ShortDraftTrace.breveE (-cuspFrequency n *
              (activeStratumDatum p hp hprimary (D h) (hN h) (G h).denominator_ne_zero
                (G h).primary (G h).shape A v).point)) := by
      simp only [Finset.mul_sum]
      ring
    _ = _ := by
      rw [activeStratum_function_multiplier p hp hprimary F (D h) (hN h)
        (G h).denominator_ne_zero (G h).primary (G h).shape n, (G h).point]
      ring

end
end SevenEighths.InverseMoment

end OAI
