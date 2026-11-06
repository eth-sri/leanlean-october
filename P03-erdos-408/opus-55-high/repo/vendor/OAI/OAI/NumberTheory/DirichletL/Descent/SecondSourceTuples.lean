module

public import OAI.NumberTheory.DirichletL.Inversion.InitialArithmetic
public import OAI.NumberTheory.DirichletL.Descent.SecondGenerator

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped Classical
open CompletedGauss
open InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen sourceIdeal_ne_zero sourceIdeal_union sourceIdeal_injective sourcePrime source_prime_dvd)
noncomputable section

@[ext] structure SecondOriginalSource (ι : Type*) (Jo Jn : ℕ) where
  q0 : Ideal ActualEisensteinCubic.O
  quotient : Ideal ActualEisensteinCubic.O
  J : Ideal ActualEisensteinCubic.O
  C : Ideal ActualEisensteinCubic.O
  s : Ideal ActualEisensteinCubic.O
  b1 : Ideal ActualEisensteinCubic.O
  A1 : Ideal ActualEisensteinCubic.O
  A2 : Ideal ActualEisensteinCubic.O
  dK : Ideal ActualEisensteinCubic.O
  J2 : Ideal ActualEisensteinCubic.O
  b2 : Ideal ActualEisensteinCubic.O
  common : Finset ι
  divisor : Finset ι
  overlap : Finset ι
  frequency : ActualEisensteinCubic.O
  oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal
  newAssigned : Fin Jn → ι

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O)
  [∀ i, (Ideal.span {p i}).IsMaximal]

def originalSecondTuple {Jo Jn : ℕ} (u v : ActualEisensteinCubic.Oˣ) (x : SecondOriginalSource ι Jo Jn) : SecondTuple Jo Jn where
  outer := ⟨x.q0,x.quotient,sourceIdeal p (x.common \ x.divisor)⟩
  core := ![x.J,x.C,sourceIdeal p x.divisor,x.s,x.b1,x.A1,x.A2,x.dK]
  commonResidual := sourceIdeal p x.overlap
  cubeResidual := x.J2
  secondCube := x.b2
  extractedCommon := sourceIdeal p x.common
  frequency := secondUnitFrequency u v x.frequency
  oldAssigned := x.oldAssigned
  newAssigned := fun i => sourcePrime p (x.newAssigned i)

structure SecondOriginalValid {Jo Jn : ℕ} (x : SecondOriginalSource ι Jo Jn) : Prop where
  j_split : x.s*x.J2 = x.J
  b_split : x.b1*x.b2 = x.q0^2*x.J2^2*x.s
  a1 : x.A1 ∣ (x.b1*x.b2).radical
  a2 : x.A2 ∣ (x.b1*x.b2).radical
  first_divisor : x.dK ∣ x.C*(x.b1*x.b2).radical
  first_generator : primaryGenerator x.dK ≠ 0
  second_subset : x.divisor ⊆ x.common
  old_support : ∀ i, (x.oldAssigned i).val ∣ x.q0*x.J*x.C*x.quotient
  new_support : ∀ i, x.newAssigned i ∈ x.common ∪ x.overlap

theorem originalSecondTuple_valid (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    {Jo Jn : ℕ} (u v : ActualEisensteinCubic.Oˣ) (x : SecondOriginalSource ι Jo Jn) (hx : SecondOriginalValid x) :
    Valid (originalSecondTuple p u v x)
      (secondChild (originalSecondTuple p u v x)).1
      (secondChild (originalSecondTuple p u v x)).2.1
      (secondChild (originalSecondTuple p u v x)).2.2 := by
  have hproduct : sourceIdeal p x.divisor * sourceIdeal p (x.common \ x.divisor) =
      sourceIdeal p x.common := by
    rw [←sourceIdeal_union p x.divisor (x.common \ x.divisor)
      (Finset.disjoint_left.mpr (by grind)),
      Finset.union_sdiff_of_subset hx.second_subset]
  refine ⟨rfl,rfl,hx.j_split,hx.b_split,hx.a1,hx.a2,hx.first_divisor,?_,hx.first_generator,?_,rfl,?_,?_⟩
  · exact hproduct
  · change primaryGenerator (sourceIdeal p x.divisor) ≠ 0
    rw [sourceIdeal_gen p hp hpr]
    exact Finset.prod_ne_zero_iff.mpr (by grind)
  · intro i
    apply (hx.old_support i).trans
    change x.q0*x.J*x.C*x.quotient ∣
      x.q0*(x.J*x.C*sourceIdeal p x.divisor*sourceIdeal p x.overlap)*x.quotient
    refine ⟨sourceIdeal p x.divisor*sourceIdeal p x.overlap,?_⟩
    ring
  · intro i
    change (sourcePrime p (x.newAssigned i)).val ∣
      (x.J*x.C*sourceIdeal p x.divisor*sourceIdeal p x.overlap)*sourceIdeal p (x.common \ x.divisor)
    have hslot : (sourcePrime p (x.newAssigned i)).val ∣
        sourceIdeal p x.common*sourceIdeal p x.overlap := by
      rcases Finset.mem_union.mp (hx.new_support i) with hi|hi
      · exact dvd_mul_of_dvd_left (source_prime_dvd p x.common _ hi) _
      · exact dvd_mul_of_dvd_right (source_prime_dvd p x.overlap _ hi) _
    apply hslot.trans
    refine ⟨x.J*x.C,?_⟩
    rw [←hproduct]
    ring

theorem originalSecondTuple_injective
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    {Jo Jn : ℕ} (u v : ActualEisensteinCubic.Oˣ) :
    Function.Injective (originalSecondTuple (Jo:=Jo) (Jn:=Jn) p u v) := by
  intro x y hxy
  have hi := sourceIdeal_injective p hinj
  have hcore (i : Fin 8) := congrArg (fun z : SecondTuple Jo Jn => z.core i) hxy
  apply SecondOriginalSource.ext
  · exact congrArg (fun z : SecondTuple Jo Jn => z.outer.q0) hxy
  · exact congrArg (fun z : SecondTuple Jo Jn => z.outer.quotient) hxy
  · exact hcore 0
  · exact hcore 1
  · exact hcore 3
  · exact hcore 4
  · exact hcore 5
  · exact hcore 6
  · exact hcore 7
  · exact congrArg SecondTuple.cubeResidual hxy
  · exact congrArg SecondTuple.secondCube hxy
  · exact hi (congrArg SecondTuple.extractedCommon hxy)
  · exact hi (hcore 2)
  · exact hi (congrArg SecondTuple.commonResidual hxy)
  · exact secondUnitFrequency_injective u v (congrArg SecondTuple.frequency hxy)
  · exact congrArg SecondTuple.oldAssigned hxy
  · funext i
    apply hinj
    exact congrArg (fun z : SecondTuple Jo Jn => (z.newAssigned i).val) hxy

end
end SevenEighths.InverseMoment

end OAI
