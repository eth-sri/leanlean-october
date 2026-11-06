module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Detector.TupleRows

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical

local notation "Id" => Ideal ActualEisensteinCubic.O

def tuplePhysicalScalar {K } (η : HeckeFamily.Character) (p : Fin K→ActualEisensteinCubic.O)
    (J : Finset (Fin K))  :=
  (-1:ℂ)^J.card*((elementNorm (∏i∈J,p i)^(-(3/2:ℝ)):ℝ):ℂ)*
    star (HeckeFamily.elementCoeff η (∏i∈Finset.univ\J,p i))

lemma tuple_scaled_coefficient {K : ℕ}  η  (p : Fin K→ActualEisensteinCubic.O)
    (hp : ∀i,p i≠0) (J : Finset (Fin K))  W0 W1 
     X Y Z  (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)  x w z  :
    tuplePhysicalScalar η p J*
      sourceMellinWeight W0 W1 (X/elementNorm (∏i∈J,p i)) (Y/elementNorm (∏i∈J,p i))
        (Z*elementNorm (∏i∈Finset.univ\J,p i)) x w z=
    sourceMellinWeight W0 W1 X Y Z x w z*(∏i,(elementNorm (p i):ℂ)^(z-1))*
      tupleIndexedCoefficient η p J x w := by
  have ha := sourceMellinWeight_subset W0 W1 X Y Z (elementNorm (∏i∈J,p i))
    (elementNorm (∏i∈Finset.univ\J,p i)) hX hY hZ (tuple_norm_pos p hp J)
    (tuple_norm_pos p hp (Finset.univ\J))
    (star (HeckeFamily.elementCoeff η (∏i∈Finset.univ\J,p i))) x w z
  have hb := tuple_source_scalar η p hp J x w z
  grind [tuplePhysicalScalar, tupleIndexedCoefficient, sourceMellinWeight]

lemma compensatedRow_kernel_subsets  {K}   η   S 
     p  (hp : ∀i,p i≠0)  u   a   W0 W1 
     X Y Z  (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)  x w z  :
    sourceMellinWeight W0 W1 X Y Z x w z*(∏i,(elementNorm (p i):ℂ)^(z-1))*
      (a*indexedCompensatedHigh η S p u x w z)=
    ∑J∈(Finset.univ:Finset (Fin K)).powerset,tuplePhysicalScalar η p J*
      ((a*markedIdealHighSeries S (Ideal.span {∏i∈Finset.univ\J,p i}) η u x w z)*
        sourceMellinWeight W0 W1 (X/elementNorm (∏i∈J,p i)) (Y/elementNorm (∏i∈J,p i))
          (Z*elementNorm (∏i∈Finset.univ\J,p i)) x w z) := by
  unfold indexedCompensatedHigh
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  have he := tuple_scaled_coefficient η p hp J W0 W1 X Y Z hX hY hZ x w z
  grind

end SevenEighths.ProbePhysical
end

end OAI
