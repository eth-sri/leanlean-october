module

public import OAI.NumberTheory.DirichletL.Inversion.InitialCompletePool
public import OAI.NumberTheory.DirichletL.Inversion.InitialExcludedPolynomial

@[expose] public section

namespace OAI

noncomputable section

open scoped Classical
open CanonicalQuadraticSieve ConcretePrimeRowBridge
namespace SevenEighths.InverseInitialExcludedPool
open InverseInitialOverlap InverseInitialCommonTuples InverseInitialCompletePool InverseInitialPoissonBridge

def outside (E:Finset (Ideal ActualEisensteinCubic.O))(I:Ideal ActualEisensteinCubic.O):Prop:=∀P∈E,¬P∣I

def originalOutside (A E:Finset (Ideal ActualEisensteinCubic.O)):Finset (Ideal ActualEisensteinCubic.O):=A.filter (outside E)

theorem column_outside (A E:Finset (Ideal ActualEisensteinCubic.O)){P j c:Ideal ActualEisensteinCubic.O}
    (hE:∀Q∈E,Prime Q)(hj:j∣P)(hP:outside E P)
    (hA:∀n∈A,outside E n)(hc:c∈columns A P j):outside E c := by
  obtain ⟨n,hn,rfl⟩:=Finset.mem_image.mp hc
  obtain ⟨hnA,hns,hg⟩:=mem_original.mp hn
  have hjn:j∣n:=hg ▸ GCDMonoid.gcd_dvd_left n P
  intro Q hQ hd
  rcases (hE Q hQ).dvd_mul.mp hd with hn|hpr
  · exact hA n hnA Q hQ (hn.trans (idealQuotient_dvd hjn))
  · exact hP Q hQ (hpr.trans (idealQuotient_dvd hj))

theorem admissible_mem_excluded_complete (E:Finset (Ideal ActualEisensteinCubic.O)){I:Ideal ActualEisensteinCubic.O}
    (hI:Admissible I)(hout:outside E I)(D:ℕ)(hD:I.absNorm≤D):
    I∈InitialMeanSquare.outsideSquarefreeIdeals E D := by
  apply Finset.mem_filter.mpr
  refine ⟨mem_outsideIdealsUpTo.mpr ⟨?_,hD,hout⟩,hI.2.1⟩
  exact Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)

theorem exists_excluded_complete_pool {κ:Type*}(A E:Finset (Ideal ActualEisensteinCubic.O))(T:Finset κ)
    (P:κ→Ideal ActualEisensteinCubic.O)(j:Ideal ActualEisensteinCubic.O)(hE:∀Q∈E,Prime Q)
    (hP:∀k∈T,Admissible (P k))(hj:∀k∈T,j∣P k)
    (hPE:∀k∈T,outside E (P k))
    (hA:∀n∈A,Squarefree n→Supported n)(bmax Xmax:ℝ)(hb:0≤bmax)(_hX:0≤Xmax):
    ∃D:ℕ,tupleColumns (originalOutside A E) T P j⊆
      InitialMeanSquare.outsideSquarefreeIdeals E D ∧
      ∀b X:ℝ,0≤b→b≤bmax→0≤X→X≤Xmax→b*X≤(D:ℝ) := by
  let D:=max (A.sup Ideal.absNorm*T.sup (fun k=>(P k).absNorm)) ⌈bmax*Xmax⌉₊
  refine ⟨D,?_,?_⟩
  · intro c hc
    obtain ⟨k,hk,hc⟩:=Finset.mem_biUnion.mp hc
    have hcA:c∈columns A (P k) j:=by
      obtain ⟨n,hn,he⟩:=Finset.mem_image.mp hc
      refine Finset.mem_image.mpr ⟨n,?_,he⟩
      obtain ⟨hnA,hns,hg⟩:=mem_original.mp hn
      exact mem_original.mpr ⟨(Finset.mem_filter.mp hnA).1,hns,hg⟩
    apply admissible_mem_excluded_complete E
      (columns_admissible A (by grind) (by grind) hA hcA)
      (column_outside _ E hE (by grind) (by grind)
        (fun n hn=>(Finset.mem_filter.mp hn).2) hc)
    exact (original_column_norm_bound A (by grind) (by grind) hcA).trans
      ((Nat.mul_le_mul_left (A.sup Ideal.absNorm)
        (Finset.le_sup (f:=fun k=>(P k).absNorm) hk)).trans (by omega))
  · intro b X hb0 hbb hX0 hXX
    apply (mul_le_mul hbb hXX hX0 hb).trans
    exact (Nat.le_ceil (bmax*Xmax)).trans (by exact_mod_cast (by omega))

end SevenEighths.InverseInitialExcludedPool

end

end OAI
