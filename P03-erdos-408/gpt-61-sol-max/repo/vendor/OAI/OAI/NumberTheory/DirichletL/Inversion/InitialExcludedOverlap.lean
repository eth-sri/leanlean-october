module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Inversion.InitialExcludedPool

@[expose] public section

namespace OAI



open scoped BigOperators Classical
open ActualEisensteinCubic CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
namespace SevenEighths.InverseInitialExcludedOverlap
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialExcludedPool
open HeckeFamily InverseInitialExcludedPolynomial


section
variable (A : Finset (Ideal ActualEisensteinCubic.O)) (χ : Character) (E : Finset (Ideal ActualEisensteinCubic.O)) {P j c : Ideal ActualEisensteinCubic.O} (hE : ∀Q∈E,Prime Q) (hPs : Squarefree P) (hj : j∣P) (hP : outside E P)

include hE hj hP in
theorem reconstruct_outside   
       (hc:outside E c)
    (hres:residual P j∣c):outside E (reconstruct P j c) := by
  intro Q hQ hQn
  rcases (hE Q hQ).dvd_mul.mp hQn with hQj|hQc
  · exact hP Q hQ (hQj.trans hj)
  · exact hc Q hQ (hQc.trans (idealQuotient_dvd hres))

include hE hPs hj hP in
theorem columns_filter   
        :
    columns (originalOutside A E) P j=(columns A P j).filter (outside E) := by
  ext c
  constructor
  · intro hc
    have hd:=(mem_columns hPs hj).mp hc
    apply Finset.mem_filter.mpr
    refine ⟨(mem_columns hPs hj).mpr ⟨hd.1,hd.2.1,hd.2.2.1,?_⟩,?_⟩
    · exact (Finset.mem_filter.mp hd.2.2.2).1
    · exact column_outside _ E hE hj hP (fun n hn=>(Finset.mem_filter.mp hn).2) hc
  · intro hc
    obtain ⟨hcA,hout⟩:=Finset.mem_filter.mp hc
    obtain ⟨hcs,hcj,hres,hnA⟩:=(mem_columns hPs hj).mp hcA
    exact (mem_columns hPs hj).mpr ⟨hcs,hcj,hres,
      Finset.mem_filter.mpr ⟨hnA,reconstruct_outside E hE hj hP hout hres⟩⟩

theorem deleted_zero_outside   
      I (hn:¬outside E I):
    idealCoeff (χ.excludePrimes E hE) I=0 := by
  rw [idealCoeff_excludePrimes]
  apply ite_eq_right
  intro hc
  apply hn
  intro Q hQ hd
  have hu:IsUnit Q:=(hc Q hQ).isRelPrime hd (dvd_refl Q)
  exact (hE Q hQ).not_isUnit hu

include hE hPs hj hP in
theorem residual_filtered   
        
     η (hη:∀I,¬outside E I→η I=0)
     a  W  Z r z G  u :
    residualNormalizedPolynomial A P j η a W Z r z G u=
    residualNormalizedPolynomial (originalOutside A E) P j η a W Z r z G u := by
  unfold residualNormalizedPolynomial
  rw [columns_filter A E hE hPs hj hP,Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro c hc
  grind [outside, overlapResidualCoefficient]

end

end SevenEighths.InverseInitialExcludedOverlap



end OAI
