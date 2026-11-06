module
public import OAI.NumberTheory.DirichletL.PrimeRows.SmallPartition
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical

lemma bounded_dyadic_power_sum (p : ℝ) (hp : 0<p) :
    ∃C : ℝ,0<C ∧ ∀H : ℝ,0<H → ∀F : Finset ℕ,
      (∀n∈F,(2:ℝ)^n≤H) → (∑n∈F,((2:ℝ)^n)^p)≤C*H^p := by
  obtain ⟨C,hC,hmain⟩ := CompletedDyadic.kernel_sum_bound p (p+1) hp (by linarith)
  refine ⟨(2:ℝ)^(p+1)*C,by positivity,?_⟩
  pm_5854
  have hpoint (n : ℕ) (hn : n∈F) : ((2:ℝ)^n)^p≤(2:ℝ)^(p+1)*CompletedDyadic.kernelTerm H⁻¹ p (p+1) n := by
    pm_305
    have hh : (1+H⁻¹*(2:ℝ)^n)^(p+1)≤(2:ℝ)^(p+1) :=
      Real.rpow_le_rpow hd.le (by linarith) (by linarith)
    unfold CompletedDyadic.kernelTerm
    rw [←mul_div_assoc]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hd _)).mpr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hh
      (Real.rpow_nonneg (show (0:ℝ)≤(2:ℝ)^n by positivity) p)
  calc
    _ ≤ ∑n∈F,(2:ℝ)^(p+1)*CompletedDyadic.kernelTerm H⁻¹ p (p+1) n := Finset.sum_le_sum hpoint
    _ = (2:ℝ)^(p+1)*∑n∈F,CompletedDyadic.kernelTerm H⁻¹ p (p+1) n := (Finset.mul_sum _ _ _).symm
    _ ≤ (2:ℝ)^(p+1)*∑'n,CompletedDyadic.kernelTerm H⁻¹ p (p+1) n :=
      mul_le_mul_of_nonneg_left (hs.sum_le_tsum F (fun n _=>by unfold CompletedDyadic.kernelTerm;positivity)) (by positivity)
    _ ≤ (2:ℝ)^(p+1)*(C*(H⁻¹)^(-p)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by rw [Real.inv_rpow hH.le,Real.rpow_neg hH.le,inv_inv];ring

lemma retained_dyadic_partition (rows : Finset FreeRow) (H : ℝ)
    (hrows : ∀u∈rows,u.val≠1 ∧ rowNorm u≤H) :
    (smallDyadicIndices H).biUnion (fun n=>rows∩dyadicRows 1 n)=rows := by
  ext u
  constructor
  · intro hu
    obtain ⟨n,hn,hu⟩ := Finset.mem_biUnion.mp hu
    exact (Finset.mem_inter.mp hu).1
  · intro hu
    obtain ⟨n,hn⟩ := exists_dyadicRows 1 (by norm_num) u (hrows u hu).1 (rowNorm_ge_one u)
    refine Finset.mem_biUnion.mpr ⟨n,?_,Finset.mem_inter.mpr ⟨hu,hn⟩⟩
    pm_7813
    simpa only [one_mul] using hlo.trans (hrows u hu).2

lemma retained_dyadic_sum {A : Type*} [AddCommMonoid A] (rows : Finset FreeRow) (H : ℝ)
    (hrows : ∀u∈rows,u.val≠1 ∧ rowNorm u≤H) (f : FreeRow→A) :
    (∑u∈rows,f u)=∑n∈smallDyadicIndices H,∑u∈rows∩dyadicRows 1 n,f u := by
  conv_lhs => rw [←retained_dyadic_partition rows H hrows]
  apply Finset.sum_biUnion
  intro m hm n hn hmn
  exact (dyadicRows_disjoint 1 (by norm_num) hmn).mono (Finset.inter_subset_right) (Finset.inter_subset_right)

end SevenEighths.ProbeHighRowFamily

end

end OAI
