module

public import OAI.NumberTheory.DirichletL.Descent.CanonicalLongSource
public import OAI.NumberTheory.DirichletL.Descent.GeneratorTransport
public import OAI.NumberTheory.DirichletL.Descent.SecondNormalizedEnergy

@[expose] public section

namespace OAI

noncomputable section

open scoped Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
local notation "O"=>ActualEisensteinCubic.O

theorem child_ball_unit_mem (u:ActualEisensteinCubic.Oˣ)(R:ℝ)(k:ActualEisensteinCubic.O) :
    (u:ActualEisensteinCubic.O)*k∈nonzeroChildFrequencyBall 1 R ↔ k∈nonzeroChildFrequencyBall 1 R := by
  simp only [mem_nonzeroChildFrequencyBall 1 one_ne_zero,one_mul,
    GaussGeneratorTransport.norm_eisEmbedding_unit_mul]

theorem child_ball_unit_sum {A:Type*}[AddCommMonoid A](u:ActualEisensteinCubic.Oˣ)(R:ℝ)(f:ActualEisensteinCubic.O→A) :
    ∑k∈nonzeroChildFrequencyBall 1 R,f ((u:ActualEisensteinCubic.O)*k)=
      ∑k∈nonzeroChildFrequencyBall 1 R,f k := by
  apply Finset.sum_bij (fun k _=>(u:ActualEisensteinCubic.O)*k)
  · intro k hk
    exact (child_ball_unit_mem u R k).mpr hk
  · simp
  · intro y hy
    refine ⟨((u⁻¹:ActualEisensteinCubic.Oˣ):ActualEisensteinCubic.O)*y,(child_ball_unit_mem u⁻¹ R y).mpr hy,?_⟩
    simp
  simp

variable {ι σ:Type*}[DecidableEq ι]
  (p:ι→ActualEisensteinCubic.O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,goodLambda∉Ideal.span {p i})

theorem canonical_ball_generator_energy
    (pool:Finset ι)(Ψ:ActualEisensteinCubic.O→*ℂ)(m:ActualEisensteinCubic.O)(I:Ideal ActualEisensteinCubic.O)(hI:primaryGenerator I≠0)
    (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(W:ℝ→ℂ)(X K:ℝ) :
    (∑k∈nonzeroChildFrequencyBall 1 K,
      ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator I) k slots lists a W X‖^2)=
    ∑k∈nonzeroChildFrequencyBall 1 K,
      ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (idealGenerator I) k slots lists a W X‖^2 := by
  obtain ⟨u,hu⟩:=generator_eq_unit_primary I (idealGenerator I) (span_idealGenerator I) hI
  let P:ActualEisensteinCubic.O→ℝ:=fun k=>
    ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator I) k slots lists a W X‖^2
  have hrot:=child_ball_unit_sum (u^4) K P
  have he (k:ActualEisensteinCubic.O):
      ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (idealGenerator I) k slots lists a W X‖^2=
      P (((u^4:ActualEisensteinCubic.Oˣ):ActualEisensteinCubic.O)*k) := by
    rw [hu,finiteCanonicalMarkedRow_label_transfer]
    rfl
  grind

end SevenEighths.InverseMoment

end

end OAI
