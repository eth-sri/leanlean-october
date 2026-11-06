module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Inversion.FirstGlobalParents
public import OAI.NumberTheory.DirichletL.Descent.GlobalParentEnergy
public import OAI.NumberTheory.DirichletL.Descent.GlobalPriorityFullAggregate

@[expose] public section

namespace OAI


open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic RayFourExpansion
open InverseFirstPriorityParents
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]{Jo:ℕ}
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem global_canonical_to_original_priority
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (outer:Finset (Source ι Jo))(pool:Finset ι)(selector:Source ι Jo→Finset ι→ℂ)
    (houter:∀x∈outer,x.quotientSupport=∅)(extra:CubeCoordinates ι→Finset ι)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ) lists  a 
     om  X t Y (hY:0<Y):
    (∑x∈outer,firstCanonicalSecondEnergy p hp hg hinj pool x.cube x.firstCommon
      negative Ψ m (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.firstDivisor)
      (fun U=>primeMark slots lists a (extra x.cube∪U)) (selector x) om X t Y) ≤
    globalPriorityOriginalEnergy p hg hp hinj extra pool (globalParentSource outer pool selector)
      (fun x=>(‖selector (eraseFirstQuotient x) x.quotientSupport‖:ℂ))
      negative Ψ m slots lists a om X t Y := le_trans (Finset.sum_le_sum fun x hx => OAI.SevenEighths.InverseMoment.first_actual_second_whole_cube_priority p hp hg hinj hc pool x.cube x.firstCommon (extra x.cube) negative Ψ m (OAI.ActualEisensteinCubic.primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor) slots lists a (selector x) om X t Y hY) (le_of_eq (OAI.SevenEighths.InverseMoment.global_second_energy_source p hg hp hinj outer pool selector houter extra negative Ψ m slots lists a om X t Y))

end SevenEighths.InverseMoment



end OAI
