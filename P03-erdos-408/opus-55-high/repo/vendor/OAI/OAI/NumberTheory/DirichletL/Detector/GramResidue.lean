module

public import OAI.NumberTheory.DirichletL.Detector.GramPrimeSeparation

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve RayFourExpansion
open ConcretePrimeRowBridge UniqueFactorizationMonoid
local notation "Id" => Ideal ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

theorem exists_nonexceptional_residue (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : ActualEisensteinCubic.O) (hC : C≠0) (hk0 : k≠0) (u : ActualEisensteinCubic.Oˣ) (a b : ℕ) (r : ActualEisensteinCubic.O)
    (hr : Supported (Ideal.span {r})) (hk : k=u.val*goodLambda^a*(2:ActualEisensteinCubic.O)^b*r)
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,goodLambda∉P i) (c : ι→ℕ)
    (hc : ∀i,1≤c i) (hfac : Ideal.span {C}=∏i,P i^c i)
    (p : Id) [p.IsMaximal] (hp0 : p≠0) (hgp : goodLambda∉p)
    (hchar : ringChar (ActualEisensteinCubic.O⧸p)≠2) (hfixed : ¬p∣jointFixedModulus S hS) (hcommon : ¬p∣∏i,P i)
    (he : ¬6∣(normalizedFactors (Ideal.span {r})).count p) :
    ∃(M : Id)(hM : M≠0),
      Ideal.absNorm M≤Ideal.absNorm (jointFixedModulus S hS)*
        Ideal.absNorm (Ideal.span {C})*Ideal.absNorm (Ideal.span {k}) ∧
      letI : Finite (ActualEisensteinCubic.O⧸M):=Ring.HasFiniteQuotients.finiteQuotient hM
      letI : Fintype (ActualEisensteinCubic.O⧸M):=Fintype.ofFinite _
      ∀d : ActualEisensteinCubic.O,∃A : (ActualEisensteinCubic.O⧸M)→(ActualEisensteinCubic.O⧸M)→ℂ,
        (∀n₁ n₂,A (Ideal.Quotient.mk M n₁) (Ideal.Quotient.mk M n₂)=
          jointExtension S hS σ C k u a b r hr P hg c (d*n₁) (d*n₂)) ∧
        (∀x y,‖A x y‖≤Ideal.absNorm (Ideal.span {C})) ∧
        (∑x,∑y,A x y)=0 := by
  obtain ⟨J,hJ,hcop,hJ0⟩ := exists_nonexceptional_separation (jointFixedModulus S hS)
    (∏i,P i) (Ideal.span {r}) p hr.1 hp0 hfixed hcommon
  let e := (normalizedFactors (Ideal.span {r})).count p
  let M : Id := (jointFixedModulus S hS*(∏i,P i)*J)*p^e
  have hMperiod : M=jointPeriod S hS P r := by
    rw [jointPeriod,hJ]
    dsimp [M,e]
    ring
  have hM0 := hMperiod ▸ jointPeriod_nonzero S hS C hC P c hc hfac r
    (by grind)
  refine ⟨M,hM0,?_,?_⟩
  · rw [hMperiod]
    exact jointPeriod_norm_bound S hS C k hC hk0 u a b r hk P c hc hfac
  · let : Finite (ActualEisensteinCubic.O⧸M) := Ring.HasFiniteQuotients.finiteQuotient hM0
    let : Fintype (ActualEisensteinCubic.O⧸M) := Fintype.ofFinite _
    let : Finite (ActualEisensteinCubic.O⧸jointFixedModulus S hS*(∏i,P i)*J) :=
      Ring.HasFiniteQuotients.finiteQuotient (left_ne_zero_of_mul hM0)
    let : Fintype (ActualEisensteinCubic.O⧸jointFixedModulus S hS*(∏i,P i)*J) := Fintype.ofFinite _
    let : Finite (ActualEisensteinCubic.O⧸p^e) := Ring.HasFiniteQuotients.finiteQuotient (by positivity)
    let : Fintype (ActualEisensteinCubic.O⧸p^e) := Fintype.ofFinite _
    intro d
    let A : (ActualEisensteinCubic.O⧸M)→(ActualEisensteinCubic.O⧸M)→ℂ := fun x y=>
      jointExtension S hS σ C k u a b r hr P hg c (d*x.out) (d*y.out)
    refine ⟨A,?_,?_,?_⟩
    · intro n₁ n₂
      apply jointExtension_dilation_periodic
      · rw [←hMperiod]
        exact Ideal.Quotient.eq.mp (by simp)
      · rw [←hMperiod]
        exact Ideal.Quotient.eq.mp (by simp)
    · intro x y
      rw [hfac]
      exact jointExtension_norm S hS σ C k u a b r hr P hg c hc _ _
    · exact jointExtension_mean_zero S hS σ C k u a b r hr P hg c J p hgp hchar e he hJ hcop d

end SevenEighths.ProbeGramCommon
end

end OAI
