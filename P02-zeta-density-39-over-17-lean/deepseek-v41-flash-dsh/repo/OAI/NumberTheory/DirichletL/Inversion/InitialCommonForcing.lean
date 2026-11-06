module
public import OAI.NumberTheory.DirichletL.Inversion.InitialCommonPool

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge FirstCauchyArithmetic SecondPassArithmetic
namespace SevenEighths.InverseInitialCommonForcing
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge InverseInitialRayAttachment InverseInitialArithmetic InverseInitialCommonPool InverseInitialEnergyCallerWindow InverseInitialEnergyCallerSelector
local notation "Eis"=>ActualEisensteinCubic.O

theorem common_selector_window
    (W:ℝ→ℂ)(Z r z G b:ℝ)(hZ:0<Z)(hW:∀x,W x≠0→x≤b)
    {P j:Ideal Eis}(hP:Admissible P)(hj:j∣P)
    (F:Finset (Ideal Eis))(hF:∀I∈F,Admissible I)(A:Finset (primePool F)) :
    (if (∏i∈A,i.val)∈columns (originalSource Z r b) P j then
      residualOverlapWindow P j W Z z G (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)*
      rowCoprimeMask (fun i:primePool F=>i.val) A (primaryGenerator j) =
    (if residual P j∣(∏i∈A,i.val) then
      residualOverlapWindow P j W Z z G (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)*
      rowCoprimeMask (fun i:primePool F=>i.val) A (primaryGenerator j) := by
  by_cases hm : rowCoprimeMask (fun i:primePool F=>i.val) A (primaryGenerator j)=0
  · simp only [hm,mul_zero]
  by_cases hw : residualOverlapWindow P j W Z z G (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G))=0
  · simp only [hw,ite_self,zero_mul]
  have hA := InitialMeanSquare.poolProduct_admissible F hF A
  have hcop := mask_nonzero_coprime F j (admissible_of_dvd hP hj) A hm
  by_cases hd : residual P j∣(∏i∈A,i.val)
  · have hmem := (mem_columns hP.2.1 hj).mpr ⟨hA.2.1,hcop,hd,
      reconstructed_mem_originalSource W Z r z G b hZ hW hP hj hA hd hw⟩
    simp only [hd,hmem,ite_true]
  · have hn : (∏i∈A,i.val)∉columns (originalSource Z r b) P j :=
      fun h=>hd ((mem_columns hP.2.1 hj).mp h).2.2.1
    simp only [hd,hn,ite_false]

end SevenEighths.InverseInitialCommonForcing

end

end OAI
