module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.AmplifiedRetainedRadius
public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalDyadicRows

@[expose] public section

namespace OAI


open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstAmplifiedRadiusLower
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstScale
open CenteredMomentFirstPhysicalDyadicRows


section
variable (Z d K0 c sigma reserve Csec Tsec xi H0 : ℝ) (hZ : 1<Z) (hC : 0<Csec) (hsigma : 0≤sigma) (hreserve : 0≤reserve) (hsec : Tsec≤Csec*Z^K0) (hrow : H0≤4*frequencyRadius Tsec Z xi)

include hZ hC in
lemma base_radius_identity       :
    Z^(K0+frequencyLoss Z (32*Csec) xi)=128*Csec*Z^K0*Z^(xi/2) := by
  have h := source_enclosure_power Z (32*Csec) K0 xi 1 hZ (by positivity) zero_lt_one
  simpa only [Real.logb_one,sub_zero,div_one] using h.symm.trans (by ring)

include hZ hC hsec hrow in
lemma retained_base_le      
        :
    H0≤Z^(K0+frequencyLoss Z (32*Csec) xi) := by
  rw [base_radius_identity Z K0 Csec xi hZ hC]
  have hp : 0≤Z^(xi/2) := Real.rpow_nonneg (zero_lt_one.trans hZ).le _
  have hq : 0≤Z^K0 := Real.rpow_nonneg (zero_lt_one.trans hZ).le _
  calc
    H0≤4*(Tsec*Z^(xi/2)) := hrow
    _≤4*((Csec*Z^K0)*Z^(xi/2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsec hp) (by norm_num)
    _≤128*Csec*Z^K0*Z^(xi/2) := by nlinarith [mul_nonneg (mul_nonneg hC.le hq) hp]

include hZ hC hsigma hreserve hsec hrow in
theorem common_radii_lower  
           
       
     p   k  :
    H0≤mainCommonRadius Z d K0 c sigma (frequencyLoss Z (32*Csec) xi) reserve ∧
    H0≤errorCommonRadius Z d K0 c sigma (frequencyLoss Z (32*Csec) xi) reserve p k := by
  have hb := retained_base_le Z K0 Csec Tsec xi H0 hZ hC hsec hrow
  constructor
  · apply hb.trans
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith [le_max_right (d-c) (0:ℝ)]
  · apply hb.trans
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    grind

end

section
variable (I J E : Ideal ActualEisensteinCubic.O) (hE : E≠0) (K X Z Csec Tsec xi d c sigma reserve : ℝ) (hK : 0<K) (hX : 0<X) (hZ : 1<Z) (hC : 0<Csec) (hsigma : 0≤sigma) (hreserve : 0≤reserve) (hsec : Tsec≤Csec*firstNominalScale I J E K X)

include hE hK hX hZ hC hsigma hreserve hsec in
theorem actual_retained_radii_lower    
     
           
       
     
     n  (hn : Retained (frequencyRadius Tsec Z xi) n)  p   k  :
    dyadicScale n≤mainCommonRadius Z d (nominalLog I J E K X Z) c sigma
      (frequencyLoss Z (32*Csec) xi) reserve ∧
    dyadicScale n≤errorCommonRadius Z d (nominalLog I J E K X Z) c sigma
      (frequencyLoss Z (32*Csec) xi) reserve p k := by
  apply common_radii_lower Z d _ c sigma reserve Csec Tsec xi _ hZ hC hsigma hreserve
  · simpa only [nominalLog,Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ)
      (firstNominalScale_pos I J E hE K X hK hX)] using hsec
  · exact retained_scale_le _ n hn

include hE hK hX hZ hC hsigma hreserve hsec in
theorem active_row_reciprocals    
     
           
       
     
    (rows : Finset ActualEisensteinCubic.O) (n : Fin 4→ℤ)
    (hn : Retained (frequencyRadius Tsec Z xi) (n 1))
    (hne : (activeRows rows n).Nonempty)  p   k  :
    (mainCommonRadius Z d (nominalLog I J E K X Z) c sigma
      (frequencyLoss Z (32*Csec) xi) reserve)⁻¹≤1 ∧
    (errorCommonRadius Z d (nominalLog I J E K X Z) c sigma
      (frequencyLoss Z (32*Csec) xi) reserve p k)⁻¹≤1 := by
  have hb := actual_retained_radii_lower I J E hE K X Z Csec Tsec xi d c sigma reserve
    hK hX hZ hC hsigma hreserve hsec (n 1) hn p k
  have ho := (activeRows_scale_gt_one rows n hne).le
  exact ⟨inv_le_one_of_one_le₀ (ho.trans hb.1),inv_le_one_of_one_le₀ (ho.trans hb.2)⟩

end

end SevenEighths.CenteredMomentFirstAmplifiedRadiusLower



end OAI
