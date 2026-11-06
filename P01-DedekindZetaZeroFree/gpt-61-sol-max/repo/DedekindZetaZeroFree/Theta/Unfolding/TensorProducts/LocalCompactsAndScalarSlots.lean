module

public import DedekindZetaZeroFree.Theta.Whittaker.LocalImageFactors

@[expose] public section

noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.FourierContinuation.TensorSeedSource
set_option backward.isDefEq.respectTransparency false
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

def integerCompacts (q : KPFinitePlace F) :
    TopologicalSpace.PositiveCompacts (q.adicCompletion F) where
  carrier := (valuation (q.adicCompletion F)).integer
  isCompact' := IsNonarchimedeanLocalField.isCompact_closedBall (q.adicCompletion F) 1
  interior_nonempty' := by
    rw [(valuation (q.adicCompletion F)).isOpen_integer.interior_eq]
    exact ⟨0, by simp⟩

























theorem finiteSet_nonempty (A : SArithmeticData F) : A.Sf.Nonempty := by
  let p : Ideal ℤ := Ideal.span {(2 : ℤ)}
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : p.IsMaximal := Int.ideal_span_isMaximal_of_prime 2
  obtain ⟨P, hP, hpP⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral p (S := 𝓞 F)
  letI := hP
  letI := hpP
  let v : HeightOneSpectrum (𝓞 F) := ⟨P, inferInstance,
    Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩
  have h2 : (2 : 𝓞 F) ∈ v.asIdeal := by
    change (2 : 𝓞 F) ∈ P
    simpa using (Ideal.mem_of_liesOver P p (2 : ℤ)).mp
      (Ideal.subset_span (by simp [p]))
  refine ⟨v, A.above_six v ?_⟩
  convert P.mul_mem_left (3 : 𝓞 F) h2 using 1 <;> norm_num [v]

def scalarSlot (R : PrincipalMellin.ActualRecipe S η) : R.A.Sf :=
  ⟨(finiteSet_nonempty R.A).choose, (finiteSet_nonempty R.A).choose_spec⟩

end DedekindZetaZeroFree.FourierContinuation.TensorSeedSource

end
