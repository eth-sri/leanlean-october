module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Inversion.InitialOverlap

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CanonicalQuadraticSieve IdealMobiusDivisorSum UniqueFactorizationMonoid
namespace SevenEighths.InverseInitialExcludedSource
open InverseInitialOverlap


def columns (S:Finset (Ideal ActualEisensteinCubic.O))(P j:Ideal ActualEisensteinCubic.O):=
  (original S P j).image (idealQuotient j)

section
variable {S : Finset (Ideal ActualEisensteinCubic.O)} (ψ : Ideal ActualEisensteinCubic.O→*ℂ) {P j n c : Ideal ActualEisensteinCubic.O} (hP : Squarefree P) (hj : j∣P) (hc : Squarefree c) (hcp : IsCoprime c P)

theorem quotient_properties  (hn:Squarefree n)(hg:gcd n P=j):
    Squarefree (idealQuotient j n) ∧ IsCoprime (idealQuotient j n) P ∧
      j*idealQuotient j n=n := by
  have hjn:j∣n:=hg ▸ GCDMonoid.gcd_dvd_left n P
  exact ⟨hn.squarefree_of_dvd (idealQuotient_dvd hjn),by
    rw [←hg];exact squarefree_quotient_gcd_coprime n P hn,idealQuotient_mul hjn⟩

include hP hj hc hcp in
theorem reconstruct_properties    
      :
    Squarefree (j*c) ∧ gcd (j*c) P=j := ⟨squarefree_mul_iff.mpr ⟨(hcp.mono (dvd_refl _) hj).symm.isRelPrime,
    hP.squarefree_of_dvd hj,hc⟩,gcd_mul_of_coprime_divisor j c P hj hcp⟩

include hP hj in
theorem mem_columns   
      :
    c∈columns S P j ↔ Squarefree c ∧ IsCoprime c P ∧ j*c∈S := by
  constructor
  · intro hc
    obtain ⟨n,hn,rfl⟩:=Finset.mem_image.mp hc
    obtain ⟨hnS,hns,hng⟩:=mem_original.mp hn
    grind [quotient_properties]
  · rintro ⟨hcs,hcp,hnS⟩
    obtain ⟨hns,hng⟩:=reconstruct_properties hP hj hcs hcp
    refine Finset.mem_image.mpr ⟨j*c,mem_original.mpr ⟨hnS,hns,hng⟩,?_⟩
    exact quotient_mul_cancel (ne_zero_of_dvd_ne_zero hP.ne_zero hj)

theorem sum_reconstruct (S:Finset (Ideal ActualEisensteinCubic.O)){P j:Ideal ActualEisensteinCubic.O}
    (_hP:Squarefree P)(_hj:j∣P)(f:Ideal ActualEisensteinCubic.O→ℂ):
    (∑n∈original S P j,f n)=∑c∈columns S P j,f (j*c) := by
  rw [columns,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [(quotient_properties (mem_original.mp hn).2.1 (mem_original.mp hn).2.2).2.2]
  · intro n hn n' hn' he
    have h1:=(quotient_properties (mem_original.mp hn).2.1 (mem_original.mp hn).2.2).2.2
    have h2:=(quotient_properties (mem_original.mp hn').2.1 (mem_original.mp hn').2.2).2.2
    rw [←h1,←h2,he]

theorem cutoff_argument (j c:Ideal ActualEisensteinCubic.O) X :
    ((j*c).absNorm:ℝ)/X=(c.absNorm:ℝ)/(X/(j.absNorm:ℝ)) := by
  rw [map_mul,Nat.cast_mul,div_div_eq_mul_div]
  ring

include hj hcp in
theorem coefficient_identity   
      :
    (moebius (j*c):ℂ)*ψ (j*c)=(moebius j:ℂ)*ψ j*((moebius c:ℂ)*ψ c) := by
  rw [((hcp.mono (dvd_refl _) hj).symm.isRelPrime).moebius_mul,Int.cast_mul,map_mul]
  ring

end

section
variable (S : Finset (Ideal ActualEisensteinCubic.O)) {P j : Ideal ActualEisensteinCubic.O} (hP : Squarefree P) (hj : j∣P) (ψ : Ideal ActualEisensteinCubic.O→*ℂ) (a : Ideal ActualEisensteinCubic.O→ℂ) (W : ℝ→ℂ) (X : ℝ)

include hP hj in
theorem polynomial_slice   
          :
    (∑n∈original S P j,(moebius n:ℂ)*ψ n*a n*W ((n.absNorm:ℝ)/X))=
    ((moebius j:ℂ)*ψ j)*∑c∈columns S P j,(moebius c:ℂ)*ψ c*a (j*c)*
      W ((c.absNorm:ℝ)/(X/(j.absNorm:ℝ))) := by
  rw [sum_reconstruct S hP hj,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [coefficient_identity ψ hj ((mem_columns hP hj).mp hc).2.1,cutoff_argument]
  ring

include hP in
theorem polynomial_decomposition    
        :
    (∑n∈S,(moebius n:ℂ)*ψ n*a n*W ((n.absNorm:ℝ)/X))=
    ∑j∈idealDivisors P,((moebius j:ℂ)*ψ j)*
      ∑c∈columns S P j,(moebius c:ℂ)*ψ c*a (j*c)*
        W ((c.absNorm:ℝ)/(X/(j.absNorm:ℝ))) := by
  have hs:(∑n∈S,(moebius n:ℂ)*ψ n*a n*W ((n.absNorm:ℝ)/X))=
      ∑n∈S.filter Squarefree,(moebius n:ℂ)*ψ n*a n*W ((n.absNorm:ℝ)/X) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hs:Squarefree n
    · rw [ite_eq_left hs]
    simp_all
  rw [hs,sum_original_partition S hP]
  apply Finset.sum_congr rfl
  intro j hj
  exact polynomial_slice S hP ((mem_idealDivisors hP.ne_zero).mp hj) ψ a W X

end

end SevenEighths.InverseInitialExcludedSource

end

end OAI
