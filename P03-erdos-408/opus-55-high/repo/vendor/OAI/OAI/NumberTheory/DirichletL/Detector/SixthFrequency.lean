module

public import OAI.NumberTheory.DirichletL.Detector.SourceCoefficient

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalRowCompletion CanonicalQuadraticSieve CubicEisenstein
open CompletedGauss ConcreteTraceCRT CenteredMomentCommonSupport
open ConcretePrimeRowBridge

lemma finite_fourier_invariant_unit {R : Type*} [CommRing R] [Fintype R]
    (F : R→ℂ) (ψ : AddChar R ℂ) (u : Rˣ) (hF : ∀ x,F ((u:R)*x)=F x) (H : R) :
    (∑ x,F x*ψ (((u:R)*H)*x)) = ∑ x,F x*ψ (H*x) := by
  symm
  rw [← Equiv.sum_comp u.mulLeft (fun x=>F x*ψ (H*x))]
  simp only [Units.mulLeft_apply,hF]
  ring

lemma supported_sixth_value (A v : ActualEisensteinCubic.O) (hA : Supported (Ideal.span {A}))
    (hcop : IsCoprime A v) : idealRowHom (v^6) (Ideal.span {A})=1 := by
  rw [idealRowHom_sixth_mask _ _ hA, ite_eq_left ((Ideal.isCoprime_span_singleton_iff A v).mpr hcop)]

theorem barePhysicalFourier_sixth_frequency (A s : ActualEisensteinCubic.O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (v H : ActualEisensteinCubic.O) (hcop : IsCoprime v (A*s)) :
    barePhysicalFourier A s (supportedElement_ne_zero A hA) (supportedElement_ne_zero s hs) (v^6*H) =
      barePhysicalFourier A s (supportedElement_ne_zero A hA) (supportedElement_ne_zero s hs) H := by
  have hAs := mul_ne_zero (supportedElement_ne_zero A hA) (supportedElement_ne_zero s hs)
  let := finite_quotient_span hAs
  let : Fintype (Residue (A*s)) := Fintype.ofFinite _
  let u := residueUnit (A*s) (v^6) hcop.pow_left.symm
  have hF (x : Residue (A*s)) :
      movingQuotient A s (by grind) ((u:Residue (A*s))*x) =
        movingQuotient A s (by grind) x := by
    rw [show (u:Residue (A*s))=Ideal.Quotient.mk _ (v^6) by rfl,
      movingQuotient_unit_scale A s hs (v^6) hcop.of_mul_right_right.pow_left,
      supported_sixth_value A v hA hcop.of_mul_right_left.symm,
      supported_sixth_value s v hs hcop.of_mul_right_right.symm,inv_one,one_mul,one_mul]
  have he := finite_fourier_invariant_unit (movingQuotient A s (by grind))
    (quotientTrace (A*s) hAs) u hF (Ideal.Quotient.mk _ H)
  unfold barePhysicalFourier elementFourier
  simpa

theorem bareCongruenceCoefficient_sixth_frequency (A s : ActualEisensteinCubic.O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (v H : ActualEisensteinCubic.O) (hcop : IsCoprime v (A*s)) :
    bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) (v^6*H) =
      bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H := by
  have he := barePhysicalFourier_sixth_frequency A s hA hs v H hcop
  simp only [barePhysicalFourier_eq] at he
  have hn : (Ideal.absNorm (Ideal.span {s}):ℂ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (supportedElement_ne_zero s hs))
  simp_all

theorem bareSourceCoefficient_sixth_frequency (η : HeckeFamily.Character)
    (I : Ideal ActualEisensteinCubic.O) (hI : primaryGenerator I≠0) (A s : ActualEisensteinCubic.O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (v H : ActualEisensteinCubic.O) (hcop : IsCoprime v (A*s)) :
    bareSourceCoefficient η I hI A s (supportedElement_ne_zero A hA) (v^6*H) =
      bareSourceCoefficient η I hI A s (supportedElement_ne_zero A hA) H := by
  unfold bareSourceCoefficient correctedFiniteCoefficient reciprocityCoefficient
  rw [bareCongruenceCoefficient_sixth_frequency A s hA hs v H hcop]

theorem bareSourceCoefficient_product_frequency (η : HeckeFamily.Character) (I J : Ideal ActualEisensteinCubic.O)
    (hI : CubicSieve.Admissible I) (hJ : CubicSieve.Admissible J)
    (hIJ : CubicSieve.Admissible (I*J)) (hIJcop : IsCoprime I J)
    (n m s r : ActualEisensteinCubic.O)
    (hc : Supported (Ideal.span {primaryGenerator I})) (hd : Supported (Ideal.span {primaryGenerator J}))
    (hn : Supported (Ideal.span {n})) (hm : Supported (Ideal.span {m}))
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hpc : goodLambda^2∣primaryGenerator I-1) (hpd : goodLambda^2∣primaryGenerator J-1)
    (hpn : goodLambda^2∣n-1) (hpm : goodLambda^2∣m-1)
    (hps : goodLambda^2∣s-1) (hpr : goodLambda^2∣r-1)
    (hcop : IsCoprime ((primaryGenerator I*n^3)*s) ((primaryGenerator J*m^3)*r)) (a b : ActualEisensteinCubic.O)
    (hba : IsCoprime b ((primaryGenerator I*n^3)*s))
    (hab : IsCoprime a ((primaryGenerator J*m^3)*r)) :
    let A := primaryGenerator I*n^3
    let B := primaryGenerator J*m^3
    let hA := supportedElement_ne_zero A (supported_completed _ _ hc hn)
    let hB := supportedElement_ne_zero B (supported_completed _ _ hd hm)
    bareSourceCoefficient η (I*J) hIJ.2 (A*B) (s*r) (mul_ne_zero hA hB) ((a*b)^6) =
      bareSourceCoefficient η I hI.2 A s hA (a^6) * bareSourceCoefficient η J hJ.2 B r hB (b^6) := by
  have he := bareSourceCoefficient_product η I J hI hJ hIJ hIJcop n m s r
    hc hd hn hm hs hr hpc hpd hpn hpm hps hpr hcop ((a*b)^6)
  dsimp only at he ⊢
  have hi := bareSourceCoefficient_sixth_frequency η I hI.2 (primaryGenerator I*n^3) s
    (supported_completed _ _ hc hn) hs b (a^6) hba
  have hj := bareSourceCoefficient_sixth_frequency η J hJ.2 (primaryGenerator J*m^3) r
    (supported_completed _ _ hd hm) hr a (b^6) hab
  rw [show b^6*a^6=(a*b)^6 by ring] at hi
  rw [show a^6*b^6=(a*b)^6 by ring] at hj
  simp_all

end SevenEighths.ProbePhysical
end

end OAI
