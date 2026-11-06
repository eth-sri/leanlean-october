module

public import OAI.NumberTheory.DirichletL.PrimeRows.DyadIntegral

@[expose] public section

namespace OAI


open scoped BigOperators
namespace SevenEighths.ProbeHighRowFamily

section
variable {K : ℕ} (Z : ℝ) (hZ : 0<Z) (length : Fin K→ℝ)
include K Z hZ length

lemma selected_scale_power          r  :
    (∏i,(Z^(length i))^r)=Z^((∑i,length i)*r) := by
  simp_rw [←Real.rpow_mul hZ.le]
  rw [Finset.sum_mul,Real.rpow_sum_of_pos hZ]

lemma physical_scale_power        
     lx ly σ υ r  :
    (∏i,(Z^(length i))^r)*((Z^lx)^(1/2-r)*Z^(σ+r-1)*(Z^ly)^(υ-1))=
      Z^(σ-1+lx/2+ly*(υ-1)+(1-lx+∑i,length i)*r) := by
  rw [selected_scale_power Z hZ]
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  ring

section
variable (hlength : ∑i,length i=(1/6:ℝ))
include hlength

lemma small_source_scale        
       β e  :
    (∏i,(Z^(length i))^(17/50:ℝ))*
      ((Z^(17/48:ℝ))^(1/2-(17/50:ℝ))*Z^(β+8*e+(17/50:ℝ)-1)*
        (Z^(23/48:ℝ))^((1/2:ℝ)-1))=Z^(β-11/16-79/800+8*e) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  ring

lemma large_source_scale        
       b  :
    (∏i,(Z^(length i))^b)*
      ((Z^(17/48:ℝ))^(1/2-b)*Z^(2+b-1)*(Z^(23/48:ℝ))^((2:ℝ)-1))=
      Z^((53/32:ℝ)+(13/16:ℝ)*b) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  ring

end

end

end SevenEighths.ProbeHighRowFamily


end OAI
