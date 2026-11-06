module
public import OAI.NumberTheory.DirichletL.Moments.DivisorExtraction
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorTensor
open IdealMobiusDivisorSum CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open CenteredMomentHeckeExpansion CenteredMomentHeckeHeight CenteredMomentMask HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def allocationSign (D : Ideal O) (s : Finset ι) (a : Allocation D s) : ℂ :=
  ∏ P : primeSupport D, (-1:ℂ)^((a P).val.card+1)

section
variable (D : Ideal O) (s : Finset ι)
include D s
theorem allocationSign_norm (a : Allocation D s) :
    ‖allocationSign D s a‖=1 := by
  pm_545 allocationSign norm_prod norm_pow norm_neg norm_one one_pow Finset.prod_const_one

theorem allocationTerm_eq_ite (v : ι → Ideal O)
    (a : Allocation D s) :
    allocationTerm D s v a =
      if ∀ i ∈ s, selectedDivisor D s a i∣v i then allocationSign D s a else 0 := by
  pm_6696
  · rw [ite_eq_left hh]
    unfold allocationTerm allocationSign
    apply Finset.prod_congr rfl
    intro P hP
    have he : (∏ i ∈ (a P).val,if (P:Ideal O)∣v i then (1:ℂ) else 0)=1 := by
      apply Finset.prod_eq_one
      intro i hi
      have his : i ∈ s := (Finset.mem_powerset.mp (Finset.mem_of_mem_erase (a P).property)) hi
      have hPi : (P:Ideal O)∣selectedDivisor D s a i :=
        Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ P,hi⟩)
      rw [ite_eq_left (hPi.trans (hh i his))]
    grind
  · rw [ite_eq_right hh]
    by_contra hn
    exact hh (fun i _ => selectedDivisor_dvd D s v a hn i)

theorem allocationTerm_eq_product (v : ι → Ideal O)
    (a : Allocation D s) :
    allocationTerm D s v a = allocationSign D s a*
      ∏ i ∈ s, if selectedDivisor D s a i∣v i then (1:ℂ) else 0 := by
  rw [allocationTerm_eq_ite]
  pm_6696
  · rw [ite_eq_left hh,Finset.prod_eq_one (fun i hi => by rw [ite_eq_left (hh i hi)]),mul_one]
  · rw [ite_eq_right hh]
    push Not at hh
    obtain ⟨i,hi,hnd⟩ := hh
    rw [Finset.prod_eq_zero hi (by simp only [ite_eq_right hnd]),mul_zero]
end

end SevenEighths.CenteredMomentDivisorTensor

end

end OAI
