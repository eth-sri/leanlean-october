module
public import LaterPairs.Native.ExponentPairCorrelationSum
public import LaterPairs.Native.ExponentPairShiftPhase
public import TaoTrudgianYang2025.BetaDuality
public import LaterPairs.Native.HuxleyReferenceSieve
public import LaterPairs.Native.HuxleyProfileGeometry
public import GuthMaynard.AffineSource.Foundation
public import LaterPairs.Native.DoubledBlockPrefixes
public import LaterPairs.Native.ExponentPairDifferencingBound
public import LaterPairs.Native.ExponentPairShiftJets
public import LaterPairs.Native.ExponentPairShiftUniformity
public import LaterPairs.Native.ExponentPairSourceCorrelation
public import LaterPairs.Native.ExponentPairSourceWeyl
public import LaterPairs.Native.FiniteSmoothTaylor
public import LaterPairs.Native.FiniteSmoothThirdDerivative
public import LaterPairs.Native.HuxleyModelNondegeneracy
public import LaterPairs.Native.IntegerIntervalCount
public import LaterPairs.Native.ParabolaBilinearLocalization
public import LaterPairs.Native.ReciprocalSecondDerivativeBounds
public import LaterPairs.Native.RobertSargosInitialDyadicLog
public import LaterPairs.Native.SargosLocalAffineJets
public import LaterPairs.Native.SecondDerivativeComposition
public import LaterPairs.Native.SquareProductCount
public import LaterPairs.Native.ZetaSourceLogScales
public import MathCollab.Density.Stronger.PointMean.HorizontalEdges
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaAmplitudeMonotonicity
public import TaoTrudgianYang2025.BetaExpandedModelJets
public import TaoTrudgianYang2025.BetaInverseJets
public import TaoTrudgianYang2025.BetaLegendreAllOrders
public import TaoTrudgianYang2025.BetaModelJetEstimatesFull
public import TaoTrudgianYang2025.BetaStationaryMain
public import TaoTrudgianYang2025.BetaTaylorPolynomialRemainder
public import TaoTrudgianYang2025.BetaUniformity
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import TaoTrudgianYang2025.HeathBrownModelJetCore
public import TaoTrudgianYang2025.HeathBrownPhysicalPhase
public import TaoTrudgianYang2025.ModelEndpointEntry
import WeylPort.Analytic.RealLaplace

public section
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

 
                                                                    

                                                                   
                                                                        
                                                                         
                                                                     

                                                                          
                                                                         
                                                                         
                                                                            
                                                 

                                                                     
                                                                        
                                                                       
                                                                           
                                                                   
                                                                       
                                                                      
                                                                       
                                                                 
                                                                  
                                                                       
                                                                         
                                                                         
                                                                   
                                                                          
                                                                          
                                                                         
                                                                           
                                                                      
                                                                       
                                                                    
                                                                    
                                                                      
                                                                        
                                                           
                                                                       
                                                                           
                                                                      
                                                                          
                                                                           
                                                                    
                                                                          
                                                                        
                                                                          
                                                                  
                                                                         
                                                                          
                                                                        
                                                              
                                                                         
                                                                       
                                                                       
                                                                       
                                                                            
                                                                     
                                                                           
                                                                        
                                                                        
                                                                      
                                                                   
                                                                         
                                                                            
                                                                         
                                                                       
                                                                          
                                                                       
                                                                         
                                                                         
                                                                        
                                                                          
                                                                         
                                                                      
                                                                    
                                                                      
                                                                        
                                                                       
                                                                      
                                                                        
                                                                        
                                                                    
                                                                       
                                                                        
                                                                          
                                                                     
                                                                      
                                                                         
                                                                            
                                                                       
                                                                          
                                                                     
                                                                          
                                                                       
                                                                  
                                                                  
                                                                
                                                                       
                                                                      
                                                                    
                                                                      
                                                                
                                                             
                                                                      
                                                                        
                                                                       
                                                                   
                                                                       
                                                                           
                                                                         
                                                                       
                                                                       
                                                                        
                                                                     
                                                                     
                                                                       
                                                                          
                                                                     
                                                                        
                                                                           
                                                                     
                                                                          
                                                                       
                                                                       
                                                                     
                                                                     
                                                                           
                                                                         
                                                                       
                                                                           
                                                                    

                                                                     
                                         
                                                                   
                                                                 
                                                                          
                                                                            
                                                                       



open Filter
open Polynomial
open Set
open scoped Classical
open scoped ContDiff
open scoped FourierTransform
open scoped Topology

universe huxleyNarrowV
namespace TaoTrudgianYang2025.HuxleyRationalPhase
private theorem positive_difference_physical_lower_pair_compression
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ η₀ a C : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ a ≤ 1/2 ∧ 0 < C ∧
    ∀ (F : ℝ → ℝ) (η x₀ y₀ ya yb γ Δ T M : ℝ) (xa xb : Fin 2 → ℝ),
    0 < η → η ≤ η₀ → x₀∈Icc (1:ℝ) 2 → y₀∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
    0 < T → 2 ≤ M → 0 ≤ Δ →
    (∀ i, xa i∈Icc M (2*M) ∧ xb i∈Icc M (2*M)) →
    let f := fun y z => T*(F (z/M)-F (z/M+η*y))/(σ*η)
    let h := fun y z => iteratedDeriv 2 (f y) z/2
    let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
    let u := fun i => (h ya (xa i))⁻¹
    let t := fun i => (T/(2*M^2))*u i
    let bnorm := T*γ/(2*M^2)
    let H := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 F z.2-iteratedDeriv 2 F (z.2+η*z.1))/(σ*η)
    let z₀ := (y₀,(H (y₀,x₀))⁻¹)
    (∀ i, h yb (xb i)=h ya (xa i)/(γ*h ya (xa i)+1)) →
    (∀ i, |μ yb (xb i)/μ ya (xa i)*(γ*h ya (xa i)+1)^3-1| ≤ Δ) →
    (∀ i, ‖((ya,t i):ℝ × ℝ)-z₀‖ < a ∧
      ‖((yb,t i+bnorm):ℝ × ℝ)-z₀‖ < a) →
    |γ| *|h ya (xa 1)-h ya (xa 0)| ≤ C*(Δ+1/M) := by
  obtain ⟨η₀,a,C,hη₀,hηcap,ha,hac,hC,hcompression⟩ :=
    nativeHuxleyReference_positive_difference_physical_lower_endpoint_compression hσ hc hU
  pm_145 η₀ a C hη₀ hηcap ha hac hC
  intro F η x₀ y₀ ya yb γ Δ T M xa xb hη hηsmall hx₀ hy₀ hya hyb
    hf hbound htests hT hM hΔ hpoints f h μ u t bnorm H z₀ hmap hthird hends
  have hpair (i j : Fin 2) (hij : u i < u j) :
      |γ| *|h ya (xa j)-h ya (xa i)| ≤ C*(Δ+1/M) := by
    pm_2468 γ hηsmall
  pm_1531
  · have he : h ya (xa 0)=h ya (xa 1) := inv_injective heq
    rw [he,sub_self,abs_zero,mul_zero]
    pm_2580
    positivity
  pm_7185

section
variable {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U)
include σ c U hσ hc hU
private theorem positive_difference_physical_lower_reference_gap_packing :
    ∃ η₀ a C : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ 0 < C ∧
    ∀ (F : ℝ → ℝ) (η x₀ y₀ ya yb γ Δ T M R Uref : ℝ)
    (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) (xa xb : ℝ × ℝ → ℝ),
    0 < η → η ≤ η₀ → x₀∈Icc (1:ℝ) 2 → y₀∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
    0 < T → 2 ≤ M → 0 < R → 0 < Uref → γ ≠ 0 → 0 ≤ Δ →
    (∀ ab∈Gaps, xa ab∈Icc M (2*M) ∧ xb ab∈Icc M (2*M)) →
    (∀ a∈Refs, ∀ b∈Refs, a≠b → Uref/(4*R^2) ≤ |a-b|) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1<ab.2 ∧
      ∀ t∈Refs, ¬(ab.1<t ∧ t<ab.2)) →
    let f := fun y z => T*(F (z/M)-F (z/M+η*y))/(σ*η)
    let h := fun y z => iteratedDeriv 2 (f y) z/2
    let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
    let t := fun ab => (T/(2*M^2))*(h ya (xa ab))⁻¹
    let bnorm := T*γ/(2*M^2)
    let H := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 F z.2-iteratedDeriv 2 F (z.2+η*z.1))/(σ*η)
    let z₀ := (y₀,(H (y₀,x₀))⁻¹)
    (∀ ab∈Gaps, h ya (xa ab)∈Icc ab.1 ab.2) →
    (∀ ab∈Gaps, h yb (xb ab)=h ya (xa ab)/(γ*h ya (xa ab)+1)) →
    (∀ ab∈Gaps, |μ yb (xb ab)/μ ya (xa ab)*(γ*h ya (xa ab)+1)^3-1| ≤ Δ) →
    (∀ ab∈Gaps, ‖((ya,t ab):ℝ × ℝ)-z₀‖ < a ∧
      ‖((yb,t ab+bnorm):ℝ × ℝ)-z₀‖ < a) →
    (Gaps.card:ℝ) ≤ 4*C*(Δ+1/M)*R^2/(|γ| *Uref)+2 := by
  obtain ⟨η₀,a,C,hη₀,hηcap,ha,_hac,hC,hcompression⟩ :=
    positive_difference_physical_lower_pair_compression hσ hc hU
  pm_2030 η₀ a C hη₀ hηcap ha hC
  pm_620 γ hγ
  pm_2580
  pm_4888 hγpos γ abs_pos.mpr hγ
  have hdiam ab (hab : ab∈Gaps) cd (hcd : cd∈Gaps) :
      |h ya (xa ab)-h ya (xa cd)| ≤ C*(Δ+1/M)/|γ| := by
    pm_2469 γ
    change |γ| *|h ya (xa cd)-h ya (xa ab)| ≤ C*(Δ+1/M) at hh
    apply (le_div_iff₀ hγpos).mpr
    rw [mul_comm,abs_sub_comm]
    exact hh
  have hh := nativeHuxleyReference_reference_gap_count_of_closed_profile_width Refs Gaps (fun ab => h ya (xa ab))
    (by positivity : 0 < Uref/(4*R^2))
    (by positivity : 0 ≤ C*(Δ+1/M)/|γ|) hsep hgap hinside (fun ab hab cd hcd => hdiam cd hcd ab hab)
  pm_8060

                                                                  
                                                                            
private theorem positive_difference_physical_upper_pair_compression :
    ∃ a C : ℝ, 0 < a ∧ a ≤ 1/2 ∧ 0 < C ∧
    ∀ (F : ℝ → ℝ) (η x₀ y₀ ya yb b Δ T M : ℝ) (xa xb : Fin 2 → ℝ),
    0 < η → η ≤ 1/8 → x₀∈Icc (1:ℝ) 2 → y₀∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
    0 < T → 2 ≤ M → 0 ≤ Δ →
    (∀ i, xa i∈Icc M (2*M) ∧ xb i∈Icc M (2*M)) →
    let f := fun y z => T*(F (z/M)-F (z/M+η*y))/(σ*η)
    let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
    let u := fun i => iteratedDeriv 2 (f ya) (xa i)/2
    let t := fun i => (2*M^2/T)*u i
    let bnorm := 2*M^2*b/T
    let H := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 F z.2-iteratedDeriv 2 F (z.2+η*z.1))/(σ*η)
    let z₀ := (y₀,H (y₀,x₀))
    (∀ i, iteratedDeriv 2 (f yb) (xb i)/2=u i+b) →
    (∀ i, |μ yb (xb i)/μ ya (xa i)-1| ≤ Δ) →
    (∀ i, ‖((ya,t i):ℝ × ℝ)-z₀‖ < a ∧
      ‖((yb,t i+bnorm):ℝ × ℝ)-z₀‖ < a) →
    4*M^4*|b| *|u 1-u 0| ≤ C*(Δ+1/M)*T^2 := by
  obtain ⟨a,C,ha,hac,hC,hcompression⟩ :=
    nativeHuxleyReference_positive_difference_physical_upper_endpoint_compression hσ hc hU
  pm_164 a C ha hac hC
  intro F η x₀ y₀ ya yb b Δ T M xa xb hη hηmax hx₀ hy₀ hya hyb
    hf hbound htests hT hM hΔ hpoints f μ u t bnorm H z₀ hmap hthird hends
  have hpair (i j : Fin 2) (hij : u i < u j) :
      4*M^4*|b| *|u j-u i| ≤ C*(Δ+1/M)*T^2 := by
    rw [abs_of_pos (sub_pos.mpr hij)]
    pm_2468 b hηmax
  pm_1531
  · rw [heq,sub_self,abs_zero,mul_zero]
    pm_2580
    positivity
  pm_7185

private theorem positive_difference_physical_upper_reference_gap_packing :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧
    ∀ (F : ℝ → ℝ) (η x₀ y₀ ya yb b Δ T M R Uref : ℝ)
    (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) (xa xb : ℝ × ℝ → ℝ),
    0 < η → η ≤ 1/8 → x₀∈Icc (1:ℝ) 2 → y₀∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
    0 < T → 2 ≤ M → 0 < R → 0 < Uref → b ≠ 0 → 0 ≤ Δ →
    (∀ ab∈Gaps, xa ab∈Icc M (2*M) ∧ xb ab∈Icc M (2*M)) →
    (∀ a∈Refs, ∀ b∈Refs, a≠b → Uref/(4*R^2) ≤ |a-b|) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1<ab.2 ∧
      ∀ t∈Refs, ¬(ab.1<t ∧ t<ab.2)) →
    let f := fun y z => T*(F (z/M)-F (z/M+η*y))/(σ*η)
    let h := fun y z => iteratedDeriv 2 (f y) z/2
    let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
    let t := fun ab => (2*M^2/T)*h ya (xa ab)
    let bnorm := 2*M^2*b/T
    let H := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 F z.2-iteratedDeriv 2 F (z.2+η*z.1))/(σ*η)
    let z₀ := (y₀,H (y₀,x₀))
    (∀ ab∈Gaps, h ya (xa ab)∈Icc ab.1 ab.2) →
    (∀ ab∈Gaps, h yb (xb ab)=h ya (xa ab)+b) →
    (∀ ab∈Gaps, |μ yb (xb ab)/μ ya (xa ab)-1| ≤ Δ) →
    (∀ ab∈Gaps, ‖((ya,t ab):ℝ × ℝ)-z₀‖ < a ∧
      ‖((yb,t ab+bnorm):ℝ × ℝ)-z₀‖ < a) →
    (Gaps.card:ℝ) ≤ C*(Δ+1/M)*T^2*R^2/(M^4*|b| *Uref)+2 := by
  obtain ⟨a,C,ha,_hac,hC,hcompression⟩ :=
    positive_difference_physical_upper_pair_compression hσ hc hU
  refine ⟨a,C,ha,hC,?_⟩
  pm_620 b hb
  pm_2580
  pm_4888 hbpos b abs_pos.mpr hb
  have hdiam ab (hab : ab∈Gaps) cd (hcd : cd∈Gaps) :
      |h ya (xa ab)-h ya (xa cd)| ≤ C*(Δ+1/M)*T^2/(4*M^4*|b|) := by
    pm_2469 b
    change 4*M^4*|b| *|h ya (xa cd)-h ya (xa ab)| ≤ C*(Δ+1/M)*T^2 at hh
    apply (le_div_iff₀ (by positivity : 0 < 4*M^4*|b|)).mpr
    rw [mul_comm,abs_sub_comm]
    exact hh
  have hh := nativeHuxleyReference_reference_gap_count_of_closed_profile_width Refs Gaps (fun ab => h ya (xa ab))
    (by positivity : 0 < Uref/(4*R^2))
    (by positivity : 0 ≤ C*(Δ+1/M)*T^2/(4*M^4*|b|)) hsep hgap hinside (fun ab hab cd hcd => hdiam cd hcd ab hab)
  pm_8060
end

private theorem upper_reference_gap_source_scale
    {C K Tsrc E T M N R L b Uref : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hTsrc : 0 < Tsrc) (hM : 0 < M)
    (hN : 0 < N) (hR : 1 ≤ R) (hL : 0 < L) (hUref : 0 < Uref) (hb : b ≠ 0)
    (hNL : (L*N)^2 ≤ M*R) (hscale : T*N*R^2=M^3) (hsource : Tsrc ≤ E*T) :
    C*(K*R^2/(L^2*N^2)+1/M)*Tsrc^2*R^2/(M^4*|b| *Uref) ≤
      C*(K+1)*E^2*M^2/(L^2*N^4*|b| *Uref) := by
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  pm_4888 hbpos b abs_pos.mpr hb
  pm_2470
  pm_2471 herr K
  have hAmp : Tsrc^2 ≤ E^2*T^2 := by
    have hh := pow_le_pow_left₀ hTsrc.le hsource 2
    nlinarith only [hh]
  calc
    _ ≤ C*((K+1)*R^2/(L^2*N^2))*(E^2*T^2)*R^2/(M^4*|b| *Uref) := by
      pm_2680
      exact mul_le_mul (mul_le_mul_of_nonneg_left herr hC) hAmp
        (sq_nonneg Tsrc) (by positivity)
    _ = _ := by
      pm_1782
      field_simp

                                                              
                                                                        
section
variable {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
include σsrc csrc Usrc hσsrc hcsrc hUsrc
private theorem positive_difference_normalized_quartic_lower_reference_gap_packing :
    ∃ η₀ a Csrc : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ 0 < Csrc ∧
    ∀ (Fsrc : ℝ → ℝ) (η xcenter ycenter ya yb γ Tsrc : ℝ)
    (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ))
    (x : ℝ × ℝ → Fin 4 → ℝ)
    (xref e r v s : ℝ × ℝ → Fin 2 → ℝ)
    (curve : ℝ × ℝ → ℝ → Fin 2 → ℝ) (d alpha beta : ℝ × ℝ → ℝ)
    {σ δ T M N R Uref L K : ℝ} (A : Fin 2 → ℤ) {W : Fin 2 → ℝ},
    0 < η → η ≤ η₀ → xcenter∈Icc (1:ℝ) 2 → ycenter∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → γ ≠ 0 →
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let Hsrc := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc z.2-iteratedDeriv 2 Fsrc (z.2+η*z.1))/(σsrc*η)
    let center := (ycenter,(Hsrc (ycenter,xcenter))⁻¹)
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (0 < Uref) →
    (0 < L) →
    ((L*N)^2 ≤ M*R) →
    (0 ≤ K) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ a∈Refs, ∀ b∈Refs, a≠b → Uref/(4*R^2) ≤ |a-b|) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (∀ ab∈Gaps, 0 < d ab) →
    (∀ ab∈Gaps, ∀ i, xref ab i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i,
      curve ab t i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ i, r ab i≠0) →
    (∀ ab∈Gaps, ∀ i, v ab i*r ab i-e ab i*s ab i=1) →
    (∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i,
      d ab ≤ r ab i*t+s ab i ∧ r ab i*t+s ab i ≤ 2*d ab) →
    (∀ ab∈Gaps, StrictMono (x ab)) →
    (∀ ab∈Gaps,
      e ab 1=e ab 0 ∧ v ab 1=v ab 0 ∧
      r ab 1=r ab 0+γ*e ab 0 ∧ s ab 1=s ab 0+γ*v ab 0) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun ab t i => (round (curve ab t i):ℝ)-(round (xref ab i):ℝ)
    let mu := fun ab i => iteratedDeriv 3 (f i) (round (xref ab i))/6
    let nu := fun ab i => iteratedDeriv 4 (f i) (round (xref ab i))/24
    let Den := fun ab t i => r ab i*t+s ab i
    let g := fun ab => rationalPhase (mu ab 0) (r ab 0) (s ab 0) (mu ab 1) (r ab 1) (s ab 1)
    let H := fun ab => quarticPhase (mu ab 0) (nu ab 0) (r ab 0) (s ab 0)
      (mu ab 1) (nu ab 1) (r ab 1) (s ab 1)
    let Gcoord := fun ab => minorArcCoordinate (mu ab 0) (r ab 0) (s ab 0)
    let profile := fun ab t => iteratedDeriv 2 (f 0) (curve ab t 0)/2
    (∀ ab∈Gaps, ∀ i, iteratedDeriv 2 (f i) (xref ab i)/2=e ab i/r ab i) →
    (∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i,
      iteratedDeriv 2 (f i) (curve ab t i)/2=(e ab i*t+v ab i)/Den ab t i) →
    (∀ ab∈Gaps, profile ab (x ab 0)∈Ioo ab.1 ab.2 ∧
      profile ab (x ab 3)∈Ioo ab.1 ab.2) →
    (∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i, |n ab t i|^2 ≤ M*R) →
    (∀ ab∈Gaps, ∀ j : Fin 3, L*N ≤ |Gcoord ab (x ab j.succ)-Gcoord ab (x ab j.castSucc)|) →
    (∀ ab∈Gaps, ∀ j : Fin 4, |alpha ab*x ab j+beta ab-g ab (x ab j)+H ab (x ab j)| ≤
      K*R^2/|r ab 0*Gcoord ab (x ab j)|) →
    (∀ ab∈Gaps, ∀ t∈({x ab 0,x ab 3} : Finset ℝ), ∀ i,
      ‖((yp i,(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (curve ab t i)/2)⁻¹):ℝ × ℝ)-center‖ < a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*K+9*quarticReciprocalConstant σ δ)
    (Gaps.card:ℝ) ≤ 4*Csrc*(Cthird+1)*R^4/(L^2*N^2*|γ| *Uref)+2 := by
  classical
  obtain ⟨η₀,a,Csrc,hη₀,hηcap,ha,hCsrc,hcompression⟩ :=
    positive_difference_physical_lower_reference_gap_packing hσsrc hcsrc hUsrc
  pm_1747
  intro Fsrc η xcenter ycenter ya yb γ Tsrc Refs Gaps x xref e r v s curve d alpha beta
    σ δ T M N R Uref L K A W
    hη hηsmall hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hγ
    yp F Hsrc center hσ hδ hF hT hM hN hR hU hL hNL hK hA hW hsep hgap hd href hcurve hr hdet hden hmono htransport
    f n mu nu Den g H Gcoord profile hbase hpoint hends hsquare hspacing hres hlocalEnds
    κ Cphys Gamma Cthird
  pm_1138
  pm_4902 hηmax hηsmall.trans
  pm_2472
  have hcurvNe ab (hab : ab∈Gaps) t (ht : t∈Icc (x ab 0) (x ab 3)) i :
      iteratedDeriv 2 (f i) (curve ab t i)/2 ≠ 0 := by
    rw [hjet]
    have hh := (positive_difference_half_curvature_source_bounds Fsrc
      hσsrc hcsrc hUsrc hη hηmax hTsrc hM (hyp i)
      (hphysical ab hab t ht i) hreg hjets htests).1
    exact abs_pos.mp (lt_of_lt_of_le (by positivity) hh)
  have hinvMono ab (hab : ab∈Gaps) i : StrictMonoOn
      (fun t => (iteratedDeriv 2 (f i) (curve ab t i)/2)⁻¹) (Icc (x ab 0) (x ab 3)) := by
    have hnum t (ht : t∈Icc (x ab 0) (x ab 3)) : e ab i*t+v ab i ≠ 0 := by
      intro he
      have hh := hcurvNe ab hab t ht i
      rw [hpoint ab hab t ht i,he,zero_div] at hh
      exact hh rfl
    intro u hu w hw huw
    change (iteratedDeriv 2 (f i) (curve ab u i)/2)⁻¹ <
      (iteratedDeriv 2 (f i) (curve ab w i)/2)⁻¹
    rw [hpoint ab hab u hu i,hpoint ab hab w hw i,inv_div,inv_div]
    exact nativeHuxleyReference_reciprocal_fraction_strictMonoOn (hdet ab hab i) hnum hu hw huw
  have hlocal ab (hab : ab∈Gaps) t (ht : t∈Icc (x ab 0) (x ab 3)) i :
      ‖((yp i,(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (curve ab t i)/2)⁻¹):ℝ × ℝ)-center‖ < a := by
    pm_1532
    pm_7678 hl
    pm_7679 hu
    have hlo := mul_le_mul_of_nonneg_left
      ((hinvMono ab hab i).monotoneOn ⟨le_rfl,hxorder⟩ ht ht.1)
      (by positivity : 0 ≤ Tsrc/(2*M^2))
    have hhi := mul_le_mul_of_nonneg_left
      ((hinvMono ab hab i).monotoneOn ht ⟨hxorder,le_rfl⟩ ht.2)
      (by positivity : 0 ≤ Tsrc/(2*M^2))
    change max |yp i-center.1|
      |(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (curve ab (x ab 0) i)/2)⁻¹-center.2| < a at hl
    change max |yp i-center.1|
      |(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (curve ab (x ab 3) i)/2)⁻¹-center.2| < a at hu
    change max |yp i-center.1|
      |(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (curve ab t i)/2)⁻¹-center.2| < a
    pm_1738
  have hDmap ab (hab : ab∈Gaps) t :
      Den ab t 1=Den ab t 0+γ*(e ab 0*t+v ab 0) := by
    pm_1687
    ring
  have hratio ab (hab : ab∈Gaps) :
      γ*profile ab (z ab)+1=Den ab (z ab) 1/Den ab (z ab) 0 := by
    change γ*(iteratedDeriv 2 (f 0) (curve ab (z ab) 0)/2)+1=_
    rw [hpoint ab hab _ (hzcc ab hab) 0,hDmap ab hab]
    field_simp [(hdenpos ab hab _ (hzcc ab hab) 0).ne']
    ring_nf
  have hmap ab (hab : ab∈Gaps) :
      iteratedDeriv 2 (f 1) (curve ab (z ab) 1)/2=
        profile ab (z ab)/(γ*profile ab (z ab)+1) := by
    rw [hratio ab hab]
    change _=(iteratedDeriv 2 (f 0) (curve ab (z ab) 0)/2)/
      (Den ab (z ab) 1/Den ab (z ab) 0)
    rw [hpoint ab hab _ (hzcc ab hab) 1,hpoint ab hab _ (hzcc ab hab) 0,
      (htransport ab hab).1,(htransport ab hab).2.1]
    field_simp [(hdenpos ab hab _ (hzcc ab hab) 0).ne',
      (hdenpos ab hab _ (hzcc ab hab) 1).ne']
  have hinvMap ab (hab : ab∈Gaps) :
      (iteratedDeriv 2 (f 1) (curve ab (z ab) 1)/2)⁻¹=(profile ab (z ab))⁻¹+γ := by
    rw [hmap ab hab,inv_div]
    have hp : profile ab (z ab) ≠ 0 := hcurvNe ab hab _ (hzcc ab hab) 0
    rw [add_div,mul_div_cancel_right₀ γ hp,one_div,add_comm]
  have hweighted ab (hab : ab∈Gaps) :
      |munew ab (z ab) 1/munew ab (z ab) 0*(γ*profile ab (z ab)+1)^3-1| ≤
        Cthird*R^2/(L^2*N^2) := by
    have he : munew ab (z ab) 1/munew ab (z ab) 0*
        (Den ab (z ab) 1/Den ab (z ab) 0)^3=
        munew ab (z ab) 1*(Den ab (z ab) 1)^3/
          (munew ab (z ab) 0*(Den ab (z ab) 0)^3) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring_nf
    rw [hratio ab hab,he]
    exact hthird ab hab
  pm_2473
  have hcount := hcompression Fsrc η xcenter ycenter ya yb γ
    (Cthird*R^2/(L^2*N^2)) Tsrc M R Uref Refs Gaps xa xb
    hη hηsmall hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hRpos hU hγ
    (by positivity) (fun ab hab => ⟨hphysical ab hab _ (hzcc ab hab) 0,
      hphysical ab hab _ (hzcc ab hab) 1⟩) hsep hgap
    (by intro ab hab; change iteratedDeriv 2 (Src ya) (xa ab)/2∈Icc ab.1 ab.2
        rw [hua]; exact ⟨(hinside ab hab).1.le,(hinside ab hab).2.le⟩)
    (by
      intro ab hab
      pm_1748 ab
      rw [hua,hub]
      exact hmap ab hab)
    (by
      intro ab hab
      have hh := hweighted ab hab
      change |(iteratedDeriv 3 (f 1) (round (curve ab (z ab) 1))/6)/
        (iteratedDeriv 3 (f 0) (round (curve ab (z ab) 0))/6)*
        (γ*profile ab (z ab)+1)^3-1| ≤ _ at hh
      rw [hrounded,hrounded] at hh
      change |(iteratedDeriv 3 (Src yb) (round (xb ab))/6)/
        (iteratedDeriv 3 (Src ya) (round (xa ab))/6)*
        (γ*(iteratedDeriv 2 (Src ya) (xa ab)/2)+1)^3-1| ≤ _
      rw [hua]
      exact hh)
    (by
      intro ab hab
      change ‖((ya,(Tsrc/(2*M^2))*(iteratedDeriv 2 (Src ya) (xa ab)/2)⁻¹):ℝ × ℝ)-center‖ < a ∧
        ‖((yb,(Tsrc/(2*M^2))*(iteratedDeriv 2 (Src ya) (xa ab)/2)⁻¹+
          Tsrc*γ/(2*M^2)):ℝ × ℝ)-center‖ < a
      pm_6443
      · have he : (Tsrc/(2*M^2))*(profile ab (z ab))⁻¹+Tsrc*γ/(2*M^2)=
            (Tsrc/(2*M^2))*(iteratedDeriv 2 (f 1) (curve ab (z ab) 1)/2)⁻¹ := by
          rw [hinvMap ab hab]
          ring
        rw [he]
        exact hlocal ab hab _ (hzcc ab hab) 1)
  pm_2470
  pm_2471 herror Cthird
  apply hcount.trans
  calc
    _ ≤ 4*Csrc*((Cthird+1)*R^2/(L^2*N^2))*R^2/(|γ| *Uref)+2 := by
      pm_1139
    _ = _ := by ring_nf

                                                              
                                                                        
private theorem positive_difference_normalized_quartic_upper_reference_gap_packing :
    ∃ a Csrc : ℝ, 0 < a ∧ 0 < Csrc ∧
    ∀ (Fsrc : ℝ → ℝ) (η xcenter ycenter ya yb b Tsrc E : ℝ)
    (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ))
    (x : ℝ × ℝ → Fin 4 → ℝ)
    (xref e r v s : ℝ × ℝ → Fin 2 → ℝ)
    (curve : ℝ × ℝ → ℝ → Fin 2 → ℝ) (d alpha beta : ℝ × ℝ → ℝ)
    {σ δ T M N R Uref L K : ℝ} (A : Fin 2 → ℤ) {W : Fin 2 → ℝ},
    0 < η → η ≤ 1/8 → xcenter∈Icc (1:ℝ) 2 → ycenter∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → b ≠ 0 → Tsrc ≤ E*T → T*N*R^2=M^3 →
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let Hsrc := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc z.2-iteratedDeriv 2 Fsrc (z.2+η*z.1))/(σsrc*η)
    let center := (ycenter,Hsrc (ycenter,xcenter))
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (0 < Uref) →
    (0 < L) →
    ((L*N)^2 ≤ M*R) →
    (0 ≤ K) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ a∈Refs, ∀ b∈Refs, a≠b → Uref/(4*R^2) ≤ |a-b|) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (∀ ab∈Gaps, 0 < d ab) →
    (∀ ab∈Gaps, ∀ i, xref ab i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i,
      curve ab t i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ i, r ab i≠0) →
    (∀ ab∈Gaps, ∀ i, v ab i*r ab i-e ab i*s ab i=1) →
    (∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i,
      d ab ≤ r ab i*t+s ab i ∧ r ab i*t+s ab i ≤ 2*d ab) →
    (∀ ab∈Gaps, StrictMono (x ab)) →
    (∀ ab∈Gaps,
      e ab 1=e ab 0+b*r ab 0 ∧ v ab 1=v ab 0+b*s ab 0 ∧
      r ab 1=r ab 0 ∧ s ab 1=s ab 0) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun ab t i => (round (curve ab t i):ℝ)-(round (xref ab i):ℝ)
    let mu := fun ab i => iteratedDeriv 3 (f i) (round (xref ab i))/6
    let nu := fun ab i => iteratedDeriv 4 (f i) (round (xref ab i))/24
    let Den := fun ab t i => r ab i*t+s ab i
    let g := fun ab => rationalPhase (mu ab 0) (r ab 0) (s ab 0) (mu ab 1) (r ab 1) (s ab 1)
    let H := fun ab => quarticPhase (mu ab 0) (nu ab 0) (r ab 0) (s ab 0)
      (mu ab 1) (nu ab 1) (r ab 1) (s ab 1)
    let Gcoord := fun ab => minorArcCoordinate (mu ab 0) (r ab 0) (s ab 0)
    let profile := fun ab t => iteratedDeriv 2 (f 0) (curve ab t 0)/2
    (∀ ab∈Gaps, ∀ i, iteratedDeriv 2 (f i) (xref ab i)/2=e ab i/r ab i) →
    (∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i,
      iteratedDeriv 2 (f i) (curve ab t i)/2=(e ab i*t+v ab i)/Den ab t i) →
    (∀ ab∈Gaps, profile ab (x ab 0)∈Ioo ab.1 ab.2 ∧
      profile ab (x ab 3)∈Ioo ab.1 ab.2) →
    (∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i, |n ab t i|^2 ≤ M*R) →
    (∀ ab∈Gaps, ∀ j : Fin 3, L*N ≤ |Gcoord ab (x ab j.succ)-Gcoord ab (x ab j.castSucc)|) →
    (∀ ab∈Gaps, ∀ j : Fin 4, |alpha ab*x ab j+beta ab-g ab (x ab j)+H ab (x ab j)| ≤
      K*R^2/|r ab 0*Gcoord ab (x ab j)|) →
    (∀ ab∈Gaps, ∀ t∈({x ab 0,x ab 3} : Finset ℝ), ∀ i,
      ‖((yp i,(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (curve ab t i)/2)):ℝ × ℝ)-center‖ < a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*K+9*quarticReciprocalConstant σ δ)
    (Gaps.card:ℝ) ≤ Csrc*(Cthird+1)*E^2*M^2/(L^2*N^4*|b| *Uref)+2 := by
  classical
  pm_8471 hcompression positive_difference_physical_upper_reference_gap_packing
  pm_119 a Csrc ha hCsrc
  intro Fsrc η xcenter ycenter ya yb b Tsrc E Refs Gaps x xref e r v s curve d alpha beta
    σ δ T M N R Uref L K A W
    hη hηsmall hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hb hsourceScale hscale
    yp F Hsrc center hσ hδ hF hT hM hN hR hU hL hNL hK hA hW hsep hgap hd href hcurve hr hdet hden hmono htransport
    f n mu nu Den g H Gcoord profile hbase hpoint hends hsquare hspacing hres hlocalEnds
    κ Cphys Gamma Cthird
  pm_1138
  have hηmax : η ≤ 1/8 := hηsmall
  pm_2472
  have horder ab (hab : ab∈Gaps) u (hu : u∈Icc (x ab 0) (x ab 3))
      w (hw : w∈Icc (x ab 0) (x ab 3)) (huw : u ≤ w) i :
      iteratedDeriv 2 (f i) (curve ab w i)/2 ≤ iteratedDeriv 2 (f i) (curve ab u i)/2 := by
    rw [hpoint ab hab w hw i,hpoint ab hab u hu i]
    exact nativeHuxleyReference_reference_chart_fraction_antitone (hdet ab hab i)
      (hdenpos ab hab u hu i) (hdenpos ab hab w hw i) huw
  have hlocal ab (hab : ab∈Gaps) t (ht : t∈Icc (x ab 0) (x ab 3)) i :
      ‖((yp i,(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (curve ab t i)/2)):ℝ × ℝ)-center‖ < a := by
    pm_1532
    pm_7679 hl
    pm_7678 hu
    have hlo := mul_le_mul_of_nonneg_left
      (horder ab hab t ht (x ab 3) ⟨hxorder,le_rfl⟩ ht.2 i)
      (by positivity : 0 ≤ 2*M^2/Tsrc)
    have hhi := mul_le_mul_of_nonneg_left
      (horder ab hab (x ab 0) ⟨le_rfl,hxorder⟩ t ht ht.1 i)
      (by positivity : 0 ≤ 2*M^2/Tsrc)
    change max |yp i-center.1|
      |(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (curve ab (x ab 3) i)/2)-center.2| < a at hl
    change max |yp i-center.1|
      |(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (curve ab (x ab 0) i)/2)-center.2| < a at hu
    change max |yp i-center.1|
      |(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (curve ab t i)/2)-center.2| < a
    pm_1738
  have hDsame ab (hab : ab∈Gaps) t : Den ab t 1=Den ab t 0 := by
    pm_1687
  have hmap ab (hab : ab∈Gaps) :
      iteratedDeriv 2 (f 1) (curve ab (z ab) 1)/2=profile ab (z ab)+b := by
    change _=iteratedDeriv 2 (f 0) (curve ab (z ab) 0)/2+b
    rw [hpoint ab hab _ (hzcc ab hab) 1,hpoint ab hab _ (hzcc ab hab) 0,hDsame ab hab]
    pm_6662
    have hdz : r ab 0*z ab+s ab 0 ≠ 0 := (hdenpos ab hab _ (hzcc ab hab) 0).ne'
    dsimp only [Den]
    field_simp [hdz]
    ring
  have hweighted ab (hab : ab∈Gaps) :
      |munew ab (z ab) 1/munew ab (z ab) 0-1| ≤ Cthird*R^2/(L^2*N^2) := by
    have hh := hthird ab hab
    rw [hDsame ab hab] at hh
    rwa [mul_div_mul_right _ _ (pow_ne_zero 3 (hdenpos ab hab _ (hzcc ab hab) 0).ne')] at hh
  pm_2473
  have hcount := hcompression Fsrc η xcenter ycenter ya yb b
    (Cthird*R^2/(L^2*N^2)) Tsrc M R Uref Refs Gaps xa xb
    hη hηsmall hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hRpos hU hb
    (by positivity) (fun ab hab => ⟨hphysical ab hab _ (hzcc ab hab) 0,
      hphysical ab hab _ (hzcc ab hab) 1⟩) hsep hgap
    (by intro ab hab; change iteratedDeriv 2 (Src ya) (xa ab)/2∈Icc ab.1 ab.2
        rw [hua]; exact ⟨(hinside ab hab).1.le,(hinside ab hab).2.le⟩)
    (by
      intro ab hab
      change iteratedDeriv 2 (Src yb) (xb ab)/2=
        (iteratedDeriv 2 (Src ya) (xa ab)/2)+b
      rw [hua,hub]
      exact hmap ab hab)
    (by
      intro ab hab
      have hh := hweighted ab hab
      change |(iteratedDeriv 3 (f 1) (round (curve ab (z ab) 1))/6)/
        (iteratedDeriv 3 (f 0) (round (curve ab (z ab) 0))/6)-1| ≤ _ at hh
      rw [hrounded,hrounded] at hh
      change |(iteratedDeriv 3 (Src yb) (round (xb ab))/6)/
        (iteratedDeriv 3 (Src ya) (round (xa ab))/6)-1| ≤ _
      exact hh)
    (by
      intro ab hab
      change ‖((ya,(2*M^2/Tsrc)*(iteratedDeriv 2 (Src ya) (xa ab)/2)):ℝ × ℝ)-center‖ < a ∧
        ‖((yb,(2*M^2/Tsrc)*(iteratedDeriv 2 (Src ya) (xa ab)/2)+
          2*M^2*b/Tsrc):ℝ × ℝ)-center‖ < a
      pm_6443
      · have he : (2*M^2/Tsrc)*profile ab (z ab)+2*M^2*b/Tsrc=
            (2*M^2/Tsrc)*(iteratedDeriv 2 (f 1) (curve ab (z ab) 1)/2) := by
          rw [hmap ab hab]
          ring
        rw [he]
        exact hlocal ab hab _ (hzcc ab hab) 1)
  exact hcount.trans (add_le_add (upper_reference_gap_source_scale hCsrc.le hCt
    hTsrc hM hN hR hL hU hb hNL hscale hsourceScale) le_rfl)
end

                                                                      
                                                                  
                                                          
theorem positive_difference_actual_fourier_charted_triangular_long_gap_packing
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧
    ∀ (Fsrc : ℝ → ℝ) (η xcenter ycenter ya yb Tsrc E : ℝ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (Bmajor Cmajor n : ℕ)
    (S : ℝ × ℝ → Finset ℕ) (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℝ × ℝ → ℕ → Fin 2 → ℚ) (vinv : ℝ × ℝ → ℕ → Fin 2 → ℤ)
    (parity : ℝ × ℝ → ℕ → Fin 2 → Fin 2) (anchor : ℝ × ℝ → ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ}
    {x : ℝ × ℝ → ℕ → Fin 2 → ℝ},
    0 < η → η ≤ η₀ → xcenter∈Icc (1:ℝ) 2 → ycenter∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let Hsrc := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc z.2-iteratedDeriv 2 Fsrc (z.2+η*z.1))/(σsrc*η)
    let center := (ycenter,Hsrc (ycenter,xcenter))
    let centerInv := (ycenter,(Hsrc (ycenter,xcenter))⁻¹)
    (∀ ab∈Gaps, ∀ j∈S ab, ∀ i,
      ‖((yp i,(2*M^2/Tsrc)*(rat ab j i:ℝ)):ℝ × ℝ)-center‖ < a ∧
      ‖((yp i,(Tsrc/(2*M^2))*(rat ab j i:ℝ)⁻¹):ℝ × ℝ)-centerInv‖ < a) →
    (0 < n) →
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*N*R^2=M^3) →
    ((Q:ℝ)*N ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), (x ab) j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1))) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, ((rat ab) j i).den ≤ Q ∧ Q ≤ 2*((rat ab) j i).den) →
    (0 < lambda) →
    (0 ≤ Uband) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, lambda ≤ |((rat ab) j i:ℝ)| ∧ |((rat ab) j i:ℝ)| ≤ Uband) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (((rat ab) j i).den:ℤ) ∣ ((rat ab) j i).num*(vinv ab) j i-1) →
    (∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) →
    (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    (N^10 ≤ M^3*R^7) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ((rat ab) j 0:ℝ)∈Icc ab.1 ab.2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (ab : ℝ × ℝ) => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (ab : ℝ × ℝ) => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun (ab : ℝ × ℝ) => fun j i => (⌊(((rat ab) j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊(((rat ab) j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ab∈Gaps, ∀ j∈(S ab), (sourceColor ab) j 0=(sourceColor ab) j 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, iteratedDeriv 2 (f i) ((x ab) j i)/2=((rat ab) j i:ℝ)) →
    let q := fun (ab : ℝ × ℝ) => fun j i => ((rat ab) j i).den
    let mu := fun (ab : ℝ × ℝ) => fun j i => iteratedDeriv 3 (f i) (round ((x ab) j i))/6
    let ell := fun (ab : ℝ × ℝ) => fun j i => deriv (f i) (round ((x ab) j i))
    let b := fun (ab : ℝ × ℝ) => fun j i => (⌊((q ab) j i:ℝ)*(ell ab) j i⌋+((parity ab) j i:ℕ) : ℤ)
    let cround := fun (ab : ℝ × ℝ) => fun j i => round (((q ab) j i:ℝ)*(ell ab) j i)
    let tau := fun (ab : ℝ × ℝ) => fun j i => (((b ab) j i:ℝ)-((q ab) j i:ℝ)*(ell ab) j i)/2
    let dual := fun (ab : ℝ × ℝ) => fun j i => -2*(mu ab) j i*(Real.sqrt (2/(3*(mu ab) j i*((q ab) j i:ℝ))))^3
    let cloud := fun (ab : ℝ × ℝ) => fun j i => (![Int.fract (-((vinv ab) j i:ℝ)*(b ab) j i/(q ab) j i),
      Int.fract (-((vinv ab) j i:ℝ)/(q ab) j i),(dual ab) j i/Real.sqrt K₀,
      (3*(dual ab) j i*(tau ab) j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ab∈Gaps, ∀ j∈(S ab), (b ab) j 0-(cround ab) j 0=(b ab) j 1-(cround ab) j 1) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ a, |(cloud ab) j 0 a-(cloud ab) j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 →
    N ≤ R^2 →
    R ≤ N →
    N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (∀ ab∈Gaps, ∀ j∈(S ab), (Mat 2:ℝ)*((rat ab) j 0:ℝ)+Mat 3=((q ab) j 1:ℝ)/(q ab) j 0) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ((Mat 0:ℝ)*((rat ab) j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*((rat ab) j 0:ℝ)+Mat 3)=((rat ab) j 1:ℝ)) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), |((anchor ab) j:ℝ)-((rat ab) j 0:ℝ)| ≤ ε) →
    (∀ ab∈Gaps, ∀ j∈(S ab), 256*(((anchor ab) j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ab∈Gaps, ∀ j∈(S ab), 256 ≤ (2*ε)*((Q:ℝ)/3)*((anchor ab) j).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Blabels := fun ab => 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ ab∈Gaps, Blabels ab ≤ Bmajor) →
    (∀ ab∈Gaps, Ccharts ab ≤ Cmajor) →
    (∀ ab∈Gaps, m0*n ≤ (S ab).card) →
    let L := (2*κ/Cphys)*(n:ℝ)
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    ((Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) → Mat 1≠0 →
      (Gaps.card:ℝ) ≤ Cupper*(Cthird+1)*E^2*M^2/(L^2*N^4*|(Mat 1:ℝ)| *(Uref:ℝ))+2) ∧
    ((Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) → Mat 2≠0 →
      (Gaps.card:ℝ) ≤ 4*Clower*(Cthird+1)*R^4/(L^2*N^2*|(Mat 2:ℝ)| *(Uref:ℝ))+2) := by
  pm_1750 positive_difference_normalized_quartic_upper_reference_gap_packing positive_difference_normalized_quartic_lower_reference_gap_packing
  pm_1749
  intro Fsrc η xcenter ycenter ya yb Tsrc E Uref Refs Gaps Bselect
    Bmajor Cmajor n S Q K₀ inst rat vinv parity anchor Mat e r v s
    σ δ T M N R base Bcut lambda Uband θ A W x
    hη hηsmall hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hsourceScale
    yp F Hsrc center centerInv hlocal hn
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hgap
    Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor f hlevel
    q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Blabels m0 hBmajor hCmajor hblocks L Gamma Cthird
  pm_4902 hηmax hηsmall.trans
  pm_1689
  pm_116 hLp L
  pm_1693
  pm_1697
  have hall ab (hab : ab∈Gaps) :=
    physicalModelPhase_actual_fourier_charted_reference_gap_quartic_witnesses
      Uref Refs (Bselect:=Bselect) (gapLo:=ab.1) (gapHi:=ab.2)
      (S ab) Q K₀ (rat ab) (vinv ab) (parity ab) (anchor ab) Mat
      (e ab) (r ab) (v ab) (s ab)
      (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (Bcut:=Bcut)
      (lambda:=lambda) (Uband:=Uband) (θ:=θ) (F:=F) (A:=fun i => (A i:ℝ)) (W:=W) (x:=x ab)
      hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW (hx ab hab) (hwindow ab hab) (hden ab hab) hlambda hUband hθ hθmax (hcurv ab hab) (hinv ab hab) (hchart ab hab) (horientation ab hab) hBcut (hs ab hab) (hrefSet ab hab) (hparentSet ab hab) hsep (hwideL ab hab) (hwideU ab hab) hUref hBselectSize hcutMargin hselectedWrap (hreferenceDen ab hab) (hgapWidth ab hab) hRQ hselectedUpper hscaleTen (hfamilyGap ab hab)
      (hsourceColor ab hab) (hS ab hab) (hlevel ab hab) (hcolor ab hab) (hnear ab hab)
      hsmall hNR hRN hNcube hminscale hMatdet (hMatt ab hab) (hMatmap ab hab) hMatgamma
      hNtwo (hL ab hab) (hU ab hab) (hanchor ab hab) (hcut ab hab) (hcount ab hab)
  pm_1695
  pm_1698 nativeHuxleyReference_charted_selected_source_length
  · obtain ⟨ab₀,hab₀⟩ := hne
    pm_1694
    pm_1696
    have hendlevel ab (hab : ab∈Gaps) k i :
        iteratedDeriv 2 (f i) (curve ab (z ab k) i)/2=(rat ab (j ab k) i:ℝ) := by
      have hzk : z ab k∈Icc (z ab 0) (z ab 7) :=
        ⟨(hmono ab hab).monotone (by omega),(hmono ab hab).monotone (by omega)⟩
      exact (((hcurve ab hab _ hzk).2 i).2.2.2.1).trans ((hj ab hab k).2 i).symm
    constructor
    · intro htri hentry
      apply hupper Fsrc η xcenter ycenter ya yb (Mat 1) Tsrc E
        Refs Gaps z4 xref
        (fun ab i => (ep ab i:ℝ)) (fun ab i => (rp ab i:ℝ))
        (fun ab i => (vp ab i:ℝ)) (fun ab i => (sp ab i:ℝ))
        curve d alpha beta (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R)
        (Uref:=(Uref:ℝ)) (L:=L) (K:=Kres) A
        hη hηmax hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo
        (by exact_mod_cast hentry) hsourceScale hscale
        hσ hδ hF hT hM hN hR hUp hLp hNLL (hKp ab₀ hab₀) hA hW
        (by
          intro a ha b hb hne'
          calc
            (Uref:ℝ)/(4*R^2)=((Uref:ℝ)/R^2)/4 := by ring
            _ ≤ |a-b| := (hsep a ha b hb hne').le)
        hgap hd
        (fun ab hab i => (hxr ab hab i).2.1)
        (fun ab hab t ht i => ((hcurve ab hab t (hsub ab hab ht)).2 i).1)
        (fun ab hab i => by
          exact_mod_cast (mul_ne_zero_iff.mp (hxr ab hab i).1.ne').1)
        (fun ab hab i => by
          exact_mod_cast hdetp ab hab i)
        (fun ab hab t ht i => ⟨((hcurve ab hab t (hsub ab hab ht)).2 i).2.1,
          ((hcurve ab hab t (hsub ab hab ht)).2 i).2.2.1⟩)
        (fun ab hab => (hmono ab hab).comp htake)
        (by
          intro ab _
          simp [ep,rp,vp,sp,htri.1,htri.2.1,htri.2.2])
        (fun ab hab i => (hxr ab hab i).2.2.1)
        (fun ab hab t ht i => ((hcurve ab hab t (hsub ab hab ht)).2 i).2.2.2.1)
        (fun ab hab => ⟨hends ab hab 0,hends ab hab 3⟩)
        (fun ab hab t ht i => ((hcurve ab hab t (hsub ab hab ht)).2 i).2.2.2.2)
        (fun ab hab i => (mul_le_mul_of_nonneg_right (hlong ab hab) hN.le).trans
          (hspacing ab hab (⟨i.val,by omega⟩ : Fin 7)))
        (fun ab hab i => hres ab hab (take i))
      intro ab hab t ht i
      have hsample (k : Fin 8) :
          ‖((yp i,(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (curve ab (z ab k) i)/2)):ℝ × ℝ)-center‖ < aU := by
        rw [hendlevel ab hab]
        exact ((hlocal ab hab _ (hS₀ ab hab (hj ab hab k).1) i).1).trans_le
          (min_le_left _ _)
      pm_2474
    · intro htri hentry
      apply hlower Fsrc η xcenter ycenter ya yb (Mat 2) Tsrc
        Refs Gaps z4 xref
        (fun ab i => (ep ab i:ℝ)) (fun ab i => (rp ab i:ℝ))
        (fun ab i => (vp ab i:ℝ)) (fun ab i => (sp ab i:ℝ))
        curve d alpha beta (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R)
        (Uref:=(Uref:ℝ)) (L:=L) (K:=Kres) A
        hη hηsmall hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo
        (by exact_mod_cast hentry)
        hσ hδ hF hT hM hN hR hUp hLp hNLL (hKp ab₀ hab₀) hA hW
        (by
          intro a ha b hb hne'
          calc
            (Uref:ℝ)/(4*R^2)=((Uref:ℝ)/R^2)/4 := by ring
            _ ≤ |a-b| := (hsep a ha b hb hne').le)
        hgap hd
        (fun ab hab i => (hxr ab hab i).2.1)
        (fun ab hab t ht i => ((hcurve ab hab t (hsub ab hab ht)).2 i).1)
        (fun ab hab i => by
          exact_mod_cast (mul_ne_zero_iff.mp (hxr ab hab i).1.ne').1)
        (fun ab hab i => by
          exact_mod_cast hdetp ab hab i)
        (fun ab hab t ht i => ⟨((hcurve ab hab t (hsub ab hab ht)).2 i).2.1,
          ((hcurve ab hab t (hsub ab hab ht)).2 i).2.2.1⟩)
        (fun ab hab => (hmono ab hab).comp htake)
        (by
          intro ab _
          simp [ep,rp,vp,sp,htri.1,htri.2.1,htri.2.2,add_comm])
        (fun ab hab i => (hxr ab hab i).2.2.1)
        (fun ab hab t ht i => ((hcurve ab hab t (hsub ab hab ht)).2 i).2.2.2.1)
        (fun ab hab => ⟨hends ab hab 0,hends ab hab 3⟩)
        (fun ab hab t ht i => ((hcurve ab hab t (hsub ab hab ht)).2 i).2.2.2.2)
        (fun ab hab i => (mul_le_mul_of_nonneg_right (hlong ab hab) hN.le).trans
          (hspacing ab hab (⟨i.val,by omega⟩ : Fin 7)))
        (fun ab hab i => hres ab hab (take i))
      intro ab hab t ht i
      have hsample (k : Fin 8) :
          ‖((yp i,(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (curve ab (z ab k) i)/2)⁻¹):ℝ × ℝ)-centerInv‖ < aL := by
        rw [hendlevel ab hab]
        exact ((hlocal ab hab _ (hS₀ ab hab (hj ab hab k).1) i).2).trans_le
          (min_le_right _ _)
      pm_2474
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.cast_zero]
    have hδ0 := approximateModelPhase_tolerance_nonneg (hF 0)
    pm_2669
    obtain ⟨hCR,hCN⟩ := nativeHuxleyReference_physical_source_quartic_constants_nonneg hσ hδ0
    pm_1856
    constructor <;> intro _ _ <;>
      dsimp only [Cthird,Kres,Gamma,Cc,Ct,C₂,C₃] <;> positivity

private theorem original_block_mass_of_cubic_and_gap_bounds
    {ι : Type*} (Gaps : Finset ι) (S : ι → Finset ℕ) (m0 : ℕ)
    {κ L P c U Bcap Btail ac bt W₁ W₂ W₃ : ℝ}
    (hκ : 0 < κ) (hL : 0 < L) (hP : 0 < P) (hc : 0 < c) (hU : 0 < U)
    (hBcap : 0 ≤ Bcap) (hac : 0 ≤ ac) (hat : 0 ≤ bt)
    (hW₁ : 0 ≤ W₁) (hW₂ : 0 ≤ W₂) (hW₃ : 0 ≤ W₃)
    (hm0 : 0 < m0) (hS : ∀ ab∈Gaps, m0 ≤ (S ab).card)
    (hcap : ∀ ab∈Gaps, κ*c*(L*((S ab).card/m0:ℕ))^3*P ≤ ac*Bcap*W₁*W₂*W₃)
    (htail : ∀ (G : Finset ι), G ⊆ Gaps → ∀ m : ℕ, 0 < m →
      (∀ ab∈G, m0*m ≤ (S ab).card) →
      (G.card:ℝ) ≤ bt*Btail*W₁*W₂*W₃/((L*(m:ℝ))^2*P*c*U)+2) :
    (∑ ab∈Gaps, ((S ab).card:ℝ)) ≤
      4*(m0:ℝ)*((ac*max Bcap Btail*W₁*W₂*W₃/(κ*L^3*P*c))^((3:ℝ)⁻¹)+
        bt*max Bcap Btail*W₁*W₂*W₃/(L^2*P*c*U)) := by
  classical
  let Dcap := ac*max Bcap Btail*W₁*W₂*W₃
  let Dtail := bt*max Bcap Btail*W₁*W₂*W₃
  pm_82 hDcap Dcap
  pm_82 hDtail Dtail
  pm_8139 hcapMono ac Bcap Dcap le_max_left hac
  pm_8139 htailMono bt Btail Dtail le_max_right hat
  pm_2475
  have hcap' ab (hab : ab∈Gaps) : (n ab:ℝ)^3*c ≤ Dcap/(κ*L^3*P) := by
    apply (le_div_iff₀ (by positivity : 0 < κ*L^3*P)).mpr
    calc
      _ = κ*c*(L*(n ab:ℝ))^3*P := by ring
      _ ≤ Dcap := (hcap ab hab).trans hcapMono
  let Cost := Dtail/(L^2*P*c*U)
  have htail' (m : ℕ) (hm : 0 < m) :
      ((Gaps.filter (fun ab => m ≤ n ab)).card:ℝ) ≤ 2+Cost/(m:ℝ)^2 := by
    pm_1701
    calc
      _ ≤ bt*Btail*W₁*W₂*W₃/((L*(m:ℝ))^2*P*c*U)+2 := htail Long hin m hm hb
      _ ≤ Dtail/((L*(m:ℝ))^2*P*c*U)+2 :=
        add_le_add (div_le_div_of_nonneg_right htailMono (by positivity)) le_rfl
      _ = 2+Cost/(m:ℝ)^2 := by dsimp only [Cost]; ring
  have hsum := nativeHuxleyReference_finite_occupied_cubic_tail_sum Gaps n (by norm_num : (0:ℝ) ≤ 2)
    (show 0 ≤ Cost by dsimp only [Cost]; positivity)
    (show 0 ≤ Dcap/(κ*L^3*P) by positivity) hc hcap' htail'
  pm_1702
  calc
    _ ≤ 2*(m0:ℝ)*(∑ ab∈Gaps, (n ab:ℝ)) := hmass
    _ ≤ 2*(m0:ℝ)*(2*(Dcap/(κ*L^3*P)/c)^((3:ℝ)⁻¹)+2*Cost) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by dsimp only [Cost,Dcap,Dtail]; ring_nf

                                                                     
                                                                       
                                                                
theorem positive_difference_actual_fourier_charted_triangular_long_sample_mass
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧
    ∀ (Fsrc : ℝ → ℝ) (η xcenter ycenter ya yb Tsrc E : ℝ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (Bmajor Cmajor : ℕ)
    (S : ℝ × ℝ → Finset ℕ) (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℝ × ℝ → ℕ → Fin 2 → ℚ) (vinv : ℝ × ℝ → ℕ → Fin 2 → ℤ)
    (parity : ℝ × ℝ → ℕ → Fin 2 → Fin 2) (anchor : ℝ × ℝ → ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ}
    {x : ℝ × ℝ → ℕ → Fin 2 → ℝ},
    0 < η → η ≤ η₀ → xcenter∈Icc (1:ℝ) 2 → ycenter∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let Hsrc := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc z.2-iteratedDeriv 2 Fsrc (z.2+η*z.1))/(σsrc*η)
    let center := (ycenter,Hsrc (ycenter,xcenter))
    let centerInv := (ycenter,(Hsrc (ycenter,xcenter))⁻¹)
    (∀ ab∈Gaps, ∀ j∈S ab, ∀ i,
      ‖((yp i,(2*M^2/Tsrc)*(rat ab j i:ℝ)):ℝ × ℝ)-center‖ < a ∧
      ‖((yp i,(Tsrc/(2*M^2))*(rat ab j i:ℝ)⁻¹):ℝ × ℝ)-centerInv‖ < a) →
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*N*R^2=M^3) →
    ((Q:ℝ)*N ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), (x ab) j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1))) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, ((rat ab) j i).den ≤ Q ∧ Q ≤ 2*((rat ab) j i).den) →
    (0 < lambda) →
    (0 ≤ Uband) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, lambda ≤ |((rat ab) j i:ℝ)| ∧ |((rat ab) j i:ℝ)| ≤ Uband) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (((rat ab) j i).den:ℤ) ∣ ((rat ab) j i).num*(vinv ab) j i-1) →
    (∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) →
    (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    (N^10 ≤ M^3*R^7) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ((rat ab) j 0:ℝ)∈Icc ab.1 ab.2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (ab : ℝ × ℝ) => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (ab : ℝ × ℝ) => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun (ab : ℝ × ℝ) => fun j i => (⌊(((rat ab) j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊(((rat ab) j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ab∈Gaps, ∀ j∈(S ab), (sourceColor ab) j 0=(sourceColor ab) j 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, iteratedDeriv 2 (f i) ((x ab) j i)/2=((rat ab) j i:ℝ)) →
    let q := fun (ab : ℝ × ℝ) => fun j i => ((rat ab) j i).den
    let mu := fun (ab : ℝ × ℝ) => fun j i => iteratedDeriv 3 (f i) (round ((x ab) j i))/6
    let ell := fun (ab : ℝ × ℝ) => fun j i => deriv (f i) (round ((x ab) j i))
    let b := fun (ab : ℝ × ℝ) => fun j i => (⌊((q ab) j i:ℝ)*(ell ab) j i⌋+((parity ab) j i:ℕ) : ℤ)
    let cround := fun (ab : ℝ × ℝ) => fun j i => round (((q ab) j i:ℝ)*(ell ab) j i)
    let tau := fun (ab : ℝ × ℝ) => fun j i => (((b ab) j i:ℝ)-((q ab) j i:ℝ)*(ell ab) j i)/2
    let dual := fun (ab : ℝ × ℝ) => fun j i => -2*(mu ab) j i*(Real.sqrt (2/(3*(mu ab) j i*((q ab) j i:ℝ))))^3
    let cloud := fun (ab : ℝ × ℝ) => fun j i => (![Int.fract (-((vinv ab) j i:ℝ)*(b ab) j i/(q ab) j i),
      Int.fract (-((vinv ab) j i:ℝ)/(q ab) j i),(dual ab) j i/Real.sqrt K₀,
      (3*(dual ab) j i*(tau ab) j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ab∈Gaps, ∀ j∈(S ab), (b ab) j 0-(cround ab) j 0=(b ab) j 1-(cround ab) j 1) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ a, |(cloud ab) j 0 a-(cloud ab) j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 →
    N ≤ R^2 →
    R ≤ N →
    N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (∀ ab∈Gaps, ∀ j∈(S ab), (Mat 2:ℝ)*((rat ab) j 0:ℝ)+Mat 3=((q ab) j 1:ℝ)/(q ab) j 0) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ((Mat 0:ℝ)*((rat ab) j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*((rat ab) j 0:ℝ)+Mat 3)=((rat ab) j 1:ℝ)) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), |((anchor ab) j:ℝ)-((rat ab) j 0:ℝ)| ≤ ε) →
    (∀ ab∈Gaps, ∀ j∈(S ab), 256*(((anchor ab) j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ab∈Gaps, ∀ j∈(S ab), 256 ≤ (2*ε)*((Q:ℝ)/3)*((anchor ab) j).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Blabels := fun ab => 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ ab∈Gaps, Blabels ab ≤ Bmajor) →
    (∀ ab∈Gaps, Ccharts ab ≤ Cmajor) →
    (∀ ab∈Gaps, m0 ≤ (S ab).card) →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    ((Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) → Mat 1≠0 →
      (∑ ab∈Gaps, ((S ab).card:ℝ)) ≤ 4*(m0:ℝ)*
        ((2*Cupper*(Cthird+1)*E^2*M^2/(κ*Lunit^3*N^4*|(Mat 1:ℝ)|))^((3:ℝ)⁻¹)+
          Cupper*(Cthird+1)*E^2*M^2/(Lunit^2*N^4*|(Mat 1:ℝ)| *(Uref:ℝ)))) ∧
    ((Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) → Mat 2≠0 →
      (∑ ab∈Gaps, ((S ab).card:ℝ)) ≤ 4*(m0:ℝ)*
        ((8*Clower*(Cthird+1)*R^4/(κ*Lunit^3*N^2*|(Mat 2:ℝ)|))^((3:ℝ)⁻¹)+
          4*Clower*(Cthird+1)*R^4/(Lunit^2*N^2*|(Mat 2:ℝ)| *(Uref:ℝ)))) := by
  classical
  obtain ⟨ηb,ab,CUb,CLb,hηb,hηbcap,hab,hCUb,hCLb,hblock⟩ :=
    positive_difference_actual_fourier_charted_triangular_constraints hσsrc hcsrc hUsrc
  obtain ⟨ηg,ag,CUg,CLg,hηg,_hηgcap,hag,hCUg,hCLg,hgaps⟩ :=
    positive_difference_actual_fourier_charted_triangular_long_gap_packing hσsrc hcsrc hUsrc
  let CU := max CUb CUg
  let CL := max CLb CLg
  pm_2546 hCU CU hCUb.trans_le le_max_left
  pm_2546 hCL CL hCLb.trans_le le_max_left
  refine ⟨min ηb ηg,min ab ag,CU,CL,lt_min hηb hηg,
    (min_le_left _ _).trans hηbcap,lt_min hab hag,hCU,hCL,?_⟩
  intro Fsrc η xcenter ycenter ya yb Tsrc E Uref Refs Gaps Bselect
    Bmajor Cmajor S Q K₀ inst rat vinv parity anchor Mat e r v s
    σ δ T M N R base Bcut lambda Uband θ A W x
    hη hηsmall hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hsourceScale
    yp F Hsrc center centerInv hlocal
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hgap
    Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor f hlevel
    q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Blabels m0 hBmajor hCmajor hS Lunit Gamma Cthird
  pm_1689
  pm_1700
  pm_1693
  have hδ0 := approximateModelPhase_tolerance_nonneg (hF 0)
  pm_2669
  obtain ⟨hCR,hCN⟩ := nativeHuxleyReference_physical_source_quartic_constants_nonneg hσ hδ0
  pm_1856
  pm_1853
  pm_82 hK Kres
  pm_2476
  pm_2475
  have hfamily (G : Finset (ℝ × ℝ)) (hsub : G ⊆ Gaps) (m : ℕ) (hm : 0 < m)
      (hblocks : ∀ ab∈G, m0*m ≤ (S ab).card) :
      ((Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) → Mat 1≠0 →
        (G.card:ℝ) ≤ CUg*(Cthird+1)*E^2*M^2/
          ((Lunit*(m:ℝ))^2*N^4*|(Mat 1:ℝ)| *(Uref:ℝ))+2) ∧
      ((Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) → Mat 2≠0 →
        (G.card:ℝ) ≤ 4*CLg*(Cthird+1)*R^4/
          ((Lunit*(m:ℝ))^2*N^2*|(Mat 2:ℝ)| *(Uref:ℝ))+2) := by
    exact hgaps Fsrc η xcenter ycenter ya yb Tsrc E Uref Refs G
      (Bselect:=Bselect) Bmajor Cmajor m S Q K₀ rat vinv parity anchor Mat e r v s
      (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (Bcut:=Bcut)
      (lambda:=lambda) (Uband:=Uband) (θ:=θ) A (W:=W) (x:=x)
      hη (hηsmall.trans (min_le_right _ _)) hcenterx hcentery hya hyb hreg hjets htests
      hTsrc hMtwo hsourceScale
      (fun ab hab j hj i => ⟨((hlocal ab (hsub hab) j hj i).1).trans_le (min_le_right _ _),
        ((hlocal ab (hsub hab) j hj i).2).trans_le (min_le_right _ _)⟩) hm
      hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW (fun ab hab => hx ab (hsub hab)) (fun ab hab => hwindow ab (hsub hab)) (fun ab hab => hden ab (hsub hab)) hlambda hUband hθ hθmax (fun ab hab => hcurv ab (hsub hab)) (fun ab hab => hinv ab (hsub hab)) (fun ab hab => hchart ab (hsub hab)) (fun ab hab => horientation ab (hsub hab)) hBcut (fun ab hab => hs ab (hsub hab)) (fun ab hab => hrefSet ab (hsub hab)) (fun ab hab => hparentSet ab (hsub hab)) hsep (fun ab hab => hwideL ab (hsub hab)) (fun ab hab => hwideU ab (hsub hab)) hUref hBselectSize hcutMargin hselectedWrap (fun ab hab => hreferenceDen ab (hsub hab)) (fun ab hab => hgapWidth ab (hsub hab)) hRQ hselectedUpper hscaleTen (fun ab hab => hfamilyGap ab (hsub hab)) (fun ab hab => hgap ab (hsub hab))
      (fun ab hab => hsourceColor ab (hsub hab)) (fun ab hab => hlevel ab (hsub hab)) (fun ab hab => hcolor ab (hsub hab)) (fun ab hab => hnear ab (hsub hab)) hsmall hNR hRN hNcube hminscale hMatdet (fun ab hab => hMatt ab (hsub hab)) (fun ab hab => hMatmap ab (hsub hab)) hMatgamma hNtwo (fun ab hab => hL ab (hsub hab)) (fun ab hab => hU ab (hsub hab)) (fun ab hab => hanchor ab (hsub hab)) (fun ab hab => hcut ab (hsub hab)) (fun ab hab => hcount ab (hsub hab)) hsize hD hΔ hBsize (fun ab hab => hBmajor ab (hsub hab)) (fun ab hab => hCmajor ab (hsub hab)) hblocks
  have hblockBound ab (hab : ab∈Gaps) :
      ((Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) →
        κ*|(Mat 1:ℝ)| *(Lunit*(n ab:ℝ))^3*N^4 ≤ 2*CUb*(Cthird+1)*E^2*M^2) ∧
      ((Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) →
        κ*|(Mat 2:ℝ)| *(Lunit*(n ab:ℝ))^3*N^2 ≤ 8*CLb*(Cthird+1)*R^4) := by
    have hSlarge : 6+Ccharts ab*(105+544*Blabels ab) ≤ (S ab).card := by
      apply le_trans _ (hS ab hab)
      dsimp only [m0]
      gcongr
      exact hCmajor ab hab
      exact hBmajor ab hab
    have hh := hblock Fsrc η xcenter ycenter ya yb Tsrc E Uref Refs
      (Bselect:=Bselect) (gapLo:=ab.1) (gapHi:=ab.2) (S ab) Q K₀
      (rat ab) (vinv ab) (parity ab) (anchor ab) Mat (e ab) (r ab) (v ab) (s ab)
      (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (Bcut:=Bcut)
      (lambda:=lambda) (Uband:=Uband) (θ:=θ) A (W:=W) (x:=x ab)
      hη (hηsmall.trans (min_le_left _ _)) hcenterx hcentery hya hyb hreg hjets htests
      hTsrc hMtwo hsourceScale
      (fun j hj i => ⟨((hlocal ab hab j hj i).1).trans_le (min_le_left _ _),
        ((hlocal ab hab j hj i).2).trans_le (min_le_left _ _)⟩)
      hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW (hx ab hab) (hwindow ab hab) (hden ab hab) hlambda hUband hθ hθmax (hcurv ab hab) (hinv ab hab) (hchart ab hab) (horientation ab hab) hBcut (hs ab hab) (hrefSet ab hab) (hparentSet ab hab) hsep (hwideL ab hab) (hwideU ab hab) hUref hBselectSize hcutMargin hselectedWrap (hreferenceDen ab hab) (hgapWidth ab hab) hRQ hselectedUpper hscaleTen (hfamilyGap ab hab)
      (hsourceColor ab hab) hSlarge (hlevel ab hab) (hcolor ab hab) (hnear ab hab)
      hsmall hNR hRN hNcube hminscale hMatdet (hMatt ab hab) (hMatmap ab hab) hMatgamma
      hNtwo (hL ab hab) (hU ab hab) (hanchor ab hab) (hcut ab hab) (hcount ab hab)
      hsize hD hΔ hBsize
    obtain ⟨_S₀,_hS₀,_hmass,_hL,_hupper,_hlower,hblocks⟩ := hh
    exact hblocks Bmajor Cmajor (n ab) (hBmajor ab hab) (hCmajor ab hab)
      (hn ab hab).1 (hn ab hab).2.1
  constructor
  · intro htri hentry
    have hCmat : 0 < |(Mat 1:ℝ)| := abs_pos.mpr (by exact_mod_cast hentry)
    simpa only [one_mul] using
      original_block_mass_of_cubic_and_gap_bounds Gaps S m0
        (κ:=κ) (L:=Lunit) (P:=N^4) (c:=|(Mat 1:ℝ)|) (U:=(Uref:ℝ))
        (Bcap:=CUb) (Btail:=CUg) (ac:=2) (bt:=1)
        (W₁:=Cthird+1) (W₂:=E^2) (W₃:=M^2)
        hκ hunit (by positivity) hCmat hUp hCUb.le
        (by norm_num) (by norm_num) (by positivity) (sq_nonneg E) (sq_nonneg M)
        hm0 hS (fun ab hab => (hblockBound ab hab).1 htri)
        (fun G hsub m hm hb => by simpa only [one_mul] using
          (hfamily G hsub m hm hb).1 htri hentry)
  · intro htri hentry
    pm_1781 hCmat hentry
    simpa only [mul_one] using
      original_block_mass_of_cubic_and_gap_bounds Gaps S m0
        (κ:=κ) (L:=Lunit) (P:=N^2) (c:=|(Mat 2:ℝ)|) (U:=(Uref:ℝ))
        (Bcap:=CLb) (Btail:=CLg) (ac:=8) (bt:=4)
        (W₁:=Cthird+1) (W₂:=R^4) (W₃:=1)
        hκ hunit (by positivity) hCmat hUp hCLb.le
        (by norm_num) (by norm_num) (by positivity) (by positivity) (by norm_num)
        hm0 hS (fun ab hab => by simpa only [mul_one] using (hblockBound ab hab).2 htri)
        (fun G hsub m hm hb => by simpa only [mul_one] using
          (hfamily G hsub m hm hb).2 htri hentry)

                                                                     
                                                                   
                                                          
section
variable {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
include σsrc csrc Usrc hσsrc hcsrc hUsrc
theorem positive_difference_actual_fourier_triangular_closed_gap_count :
    ∃ η₀ a Cupper Clower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧
    ∀ (Fsrc : ℝ → ℝ) (η xcenter ycenter ya yb Tsrc E : ℝ)
    (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) (Mat : Fin 4 → ℤ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℝ × ℝ → Fin 2 → ℚ) (vinv : ℝ × ℝ → Fin 2 → ℤ)
    (parity : ℝ × ℝ → Fin 2 → Fin 2) (x : ℝ × ℝ → Fin 2 → ℝ)
    {σ δ T M N R U : ℝ} (A : Fin 2 → ℤ) {W : Fin 2 → ℝ},
    0 < η → η ≤ η₀ → xcenter∈Icc (1:ℝ) 2 → ycenter∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let Hsrc := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc z.2-iteratedDeriv 2 Fsrc (z.2+η*z.1))/(σsrc*η)
    let center := (ycenter,Hsrc (ycenter,xcenter))
    let centerInv := (ycenter,(Hsrc (ycenter,xcenter))⁻¹)
    (∀ ab∈Gaps, ∀ i,
      ‖((yp i,(2*M^2/Tsrc)*(rat ab i:ℝ)):ℝ × ℝ)-center‖ < a ∧
      ‖((yp i,(Tsrc/(2*M^2))*(rat ab i:ℝ)⁻¹):ℝ × ℝ)-centerInv‖ < a) →
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (0 < U) →
    (0 < Q) →
    (T*N*R^2=M^3) →
    ((Q:ℝ)*N ≤ (K₀:ℝ)*R^2) →
    (N^2 ≤ M*R) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ a∈Refs, ∀ b∈Refs, a≠b → U/(4*R^2) ≤ |a-b|) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (∀ ab∈Gaps, ∀ i, x ab i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ i, (rat ab i).den ≤ Q ∧ Q ≤ 2*(rat ab i).den) →
    (∀ ab∈Gaps, ∀ i, ((rat ab i).den:ℤ) ∣ (rat ab i).num*vinv ab i-1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ab∈Gaps, ∀ i, iteratedDeriv 2 (f i) (x ab i)/2=(rat ab i:ℝ)) →
    let q := fun ab i => (rat ab i).den
    let mu := fun ab i => iteratedDeriv 3 (f i) (round (x ab i))/6
    let ell := fun ab i => deriv (f i) (round (x ab i))
    let b := fun ab i => (⌊(q ab i:ℝ)*ell ab i⌋+(parity ab i:ℕ) : ℤ)
    let cround := fun ab i => round ((q ab i:ℝ)*ell ab i)
    let tau := fun ab i => ((b ab i:ℝ)-(q ab i:ℝ)*ell ab i)/2
    let dual := fun ab i => -2*mu ab i*(Real.sqrt (2/(3*mu ab i*(q ab i:ℝ))))^3
    let cloud := fun ab i => (![Int.fract (-(vinv ab i:ℝ)*b ab i/q ab i),
      Int.fract (-(vinv ab i:ℝ)/q ab i),dual ab i/Real.sqrt K₀,
      (3*dual ab i*tau ab i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ab∈Gaps, b ab 0-cround ab 0=b ab 1-cround ab 1) →
    (∀ ab∈Gaps, ∀ a, |cloud ab 0 a-cloud ab 1 a| ≤ 2*radius a) →
    (∀ ab∈Gaps, (Mat 2:ℝ)*(rat ab 0:ℝ)+Mat 3=(q ab 1:ℝ)/q ab 0) →
    (∀ ab∈Gaps, ((Mat 0:ℝ)*(rat ab 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat ab 0:ℝ)+Mat 3)=(rat ab 1:ℝ)) →
    (∀ ab∈Gaps, (rat ab 0:ℝ)∈Icc ab.1 ab.2) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    ((Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) → Mat 1≠0 →
      (Gaps.card:ℝ) ≤ Cupper*(B+1)*E^2*M^2/(N^4*|(Mat 1:ℝ)| *U)+2) ∧
    ((Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) → Mat 2≠0 →
      (Gaps.card:ℝ) ≤ 4*Clower*(B+1)*R^4/(N^2*|(Mat 2:ℝ)| *U)+2) := by
  pm_1750 positive_difference_physical_upper_reference_gap_packing positive_difference_physical_lower_reference_gap_packing
  pm_1749
  intro Fsrc η xcenter ycenter ya yb Tsrc E Refs Gaps Mat Q K₀ inst rat vinv parity x
    σ δ T M N R U A W
    hη hηsmall hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hsourceScale
    yp F Hsrc center centerInv hlocal
    hσ hδ hF hT hM hN hR hU hQ hscale hmesh hNscale hA hW hsep hgap hx hden hinv
    f hlevel q mu ell b cround tau dual cloud radius hcolor hnear hMatt hMatmap
    hsourceGap κ Cphys c J B
  pm_4902 hηmax hηsmall.trans
  have hRp : 0 < R := zero_lt_one.trans_le hR
  pm_1856
  have hthird ab (hab : ab∈Gaps) :
      |mu ab 1*((Mat 2:ℝ)*(iteratedDeriv 2 (f 0) (x ab 0)/2)+Mat 3)^3/mu ab 0-1| ≤ B*R^2/N^2 := by
    pm_1692 hRp
    pm_1690
  pm_2477
  have hrounded i t : iteratedDeriv 3 (f i) (round t)=
      iteratedDeriv 3 (Src (yp i)) (round ((A i:ℝ)+t)) := by
    rw [hjet,round_intCast_add,Int.cast_add]
  pm_1746
  have hphysical ab (hab : ab∈Gaps) i :
      (A i:ℝ)+x ab i∈Icc M (2*M) :=
    ⟨by linarith only [hA i,(hx ab hab i).1],
     by linarith only [hW i,(hx ab hab i).2]⟩
  let xa := fun ab => (A 0:ℝ)+x ab 0
  let xb := fun ab => (A 1:ℝ)+x ab 1
  have hua ab : iteratedDeriv 2 (Src ya) (xa ab)/2=iteratedDeriv 2 (f 0) (x ab 0)/2 :=
    (congrArg (fun t : ℝ => t/2) (hjet 0 2 (x ab 0))).symm
  have hub ab : iteratedDeriv 2 (Src yb) (xb ab)/2=iteratedDeriv 2 (f 1) (x ab 1)/2 :=
    (congrArg (fun t : ℝ => t/2) (hjet 1 2 (x ab 1))).symm
  have hcurvNe ab (hab : ab∈Gaps) i : iteratedDeriv 2 (f i) (x ab i)/2 ≠ 0 := by
    rw [hjet]
    have hh := (positive_difference_half_curvature_source_bounds Fsrc
      hσsrc hcsrc hUsrc hη hηmax hTsrc hM (hyp i)
      (hphysical ab hab i) hreg hjets htests).1
    exact abs_pos.mp (lt_of_lt_of_le (by positivity) hh)
  have hmu ab i :
      iteratedDeriv 3 (Src (yp i)) (round ((A i:ℝ)+x ab i))/6=mu ab i :=
    (congrArg (fun t : ℝ => t/6) (hrounded i (x ab i))).symm
  constructor
  · intro htri hentry
    have hb : (Mat 1:ℝ) ≠ 0 := by exact_mod_cast hentry
    have hmap ab (hab : ab∈Gaps) :
        iteratedDeriv 2 (Src yb) (xb ab)/2=
          iteratedDeriv 2 (Src ya) (xa ab)/2+(Mat 1:ℝ) := by
      pm_6676
      simpa only [htri.1,htri.2.1,htri.2.2,Int.cast_one,Int.cast_zero,
        zero_mul,one_mul,zero_add,div_one] using (hMatmap ab hab).symm
    have hp := hupper Fsrc η xcenter ycenter ya yb (Mat 1) (B*R^2/N^2)
      Tsrc M R U Refs Gaps xa xb
      hη hηmax hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hRp hU hb
      (by positivity)
      (fun ab hab => ⟨hphysical ab hab 0,hphysical ab hab 1⟩) hsep hgap
      (by
        pm_703
        exact hsourceGap ab hab)
      hmap
      (by
        intro ab hab
        change |(iteratedDeriv 3 (Src (yp 1)) (round ((A 1:ℝ)+x ab 1))/6)/
          (iteratedDeriv 3 (Src (yp 0)) (round ((A 0:ℝ)+x ab 0))/6)-1| ≤ _
        rw [hmu,hmu]
        simpa only [htri.2.1,htri.2.2,Int.cast_zero,Int.cast_one,zero_mul,
          zero_add,one_pow,mul_one] using hthird ab hab)
      (by
        intro ab hab
        change ‖((ya,(2*M^2/Tsrc)*(iteratedDeriv 2 (Src ya) (xa ab)/2)):ℝ × ℝ)-center‖ < aU ∧
          ‖((yb,(2*M^2/Tsrc)*(iteratedDeriv 2 (Src ya) (xa ab)/2)+
            2*M^2*(Mat 1:ℝ)/Tsrc):ℝ × ℝ)-center‖ < aU
        have he : (2*M^2/Tsrc)*(iteratedDeriv 2 (Src ya) (xa ab)/2)+2*M^2*(Mat 1:ℝ)/Tsrc=
            (2*M^2/Tsrc)*(iteratedDeriv 2 (Src yb) (xb ab)/2) := by
          rw [hmap ab hab]
          ring
        pm_6236
        exact ⟨((hlocal ab hab 0).1).trans_le (min_le_left _ _),
          ((hlocal ab hab 1).1).trans_le (min_le_left _ _)⟩)
    have hh := upper_reference_gap_source_scale (L:=1) hCU.le hB hTsrc hM hN hR
      (by norm_num) hU hb (by simpa only [one_mul] using hNscale) hscale hsourceScale
    have hh' : CU*(B*R^2/N^2+1/M)*Tsrc^2*R^2/(M^4*|(Mat 1:ℝ)| *U) ≤
        CU*(B+1)*E^2*M^2/(N^4*|(Mat 1:ℝ)| *U) := by
      simpa only [one_pow,one_mul] using hh
    exact hp.trans (add_le_add hh' le_rfl)
  · intro htri hentry
    have hc : (Mat 2:ℝ) ≠ 0 := by exact_mod_cast hentry
    have hmap ab (hab : ab∈Gaps) :
        iteratedDeriv 2 (Src yb) (xb ab)/2=
          (iteratedDeriv 2 (Src ya) (xa ab)/2)/
            ((Mat 2:ℝ)*(iteratedDeriv 2 (Src ya) (xa ab)/2)+1) := by
      pm_6676
      simpa only [htri.1,htri.2.1,htri.2.2,Int.cast_one,Int.cast_zero,
        one_mul,add_zero] using (hMatmap ab hab).symm
    have hinvMap ab (hab : ab∈Gaps) :
        (iteratedDeriv 2 (Src yb) (xb ab)/2)⁻¹=
          (iteratedDeriv 2 (Src ya) (xa ab)/2)⁻¹+(Mat 2:ℝ) := by
      have hn : iteratedDeriv 2 (Src ya) (xa ab)/2 ≠ 0 := by
        rw [hua]
        exact hcurvNe ab hab 0
      rw [hmap ab hab,inv_div,add_div,mul_div_cancel_right₀ _ hn,one_div,add_comm]
    have hp := hlower Fsrc η xcenter ycenter ya yb (Mat 2) (B*R^2/N^2)
      Tsrc M R U Refs Gaps xa xb
      hη hηsmall hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hRp hU hc
      (by positivity)
      (fun ab hab => ⟨hphysical ab hab 0,hphysical ab hab 1⟩) hsep hgap
      (by
        pm_703
        exact hsourceGap ab hab)
      hmap
      (by
        intro ab hab
        change |(iteratedDeriv 3 (Src (yp 1)) (round ((A 1:ℝ)+x ab 1))/6)/
          (iteratedDeriv 3 (Src (yp 0)) (round ((A 0:ℝ)+x ab 0))/6)*
          ((Mat 2:ℝ)*(iteratedDeriv 2 (Src ya) (xa ab)/2)+1)^3-1| ≤ _
        rw [hmu,hmu,hua]
        have he : mu ab 1/mu ab 0*
            ((Mat 2:ℝ)*(iteratedDeriv 2 (f 0) (x ab 0)/2)+1)^3=
            mu ab 1*((Mat 2:ℝ)*(iteratedDeriv 2 (f 0) (x ab 0)/2)+1)^3/mu ab 0 := by ring
        rw [he]
        simpa only [htri.2.2,Int.cast_one] using hthird ab hab)
      (by
        intro ab hab
        change ‖((ya,(Tsrc/(2*M^2))*(iteratedDeriv 2 (Src ya) (xa ab)/2)⁻¹):ℝ × ℝ)-centerInv‖ < aL ∧
          ‖((yb,(Tsrc/(2*M^2))*(iteratedDeriv 2 (Src ya) (xa ab)/2)⁻¹+
            Tsrc*(Mat 2:ℝ)/(2*M^2)):ℝ × ℝ)-centerInv‖ < aL
        have he : (Tsrc/(2*M^2))*(iteratedDeriv 2 (Src ya) (xa ab)/2)⁻¹+
            Tsrc*(Mat 2:ℝ)/(2*M^2)=
            (Tsrc/(2*M^2))*(iteratedDeriv 2 (Src yb) (xb ab)/2)⁻¹ := by
          rw [hinvMap ab hab]
          ring
        pm_6236
        exact ⟨((hlocal ab hab 0).2).trans_le (min_le_right _ _),
          ((hlocal ab hab 1).2).trans_le (min_le_right _ _)⟩)
    have hInv : 1/M ≤ R^2/N^2 := by
      apply (div_le_div_iff₀ hM (sq_pos_of_pos hN)).mpr
      have hRR : R ≤ R^2 := by nlinarith only [hR]
      nlinarith only [hNscale,mul_le_mul_of_nonneg_left hRR hM.le]
    have herror : B*R^2/N^2+1/M ≤ (B+1)*R^2/N^2 :=
      (add_le_add le_rfl hInv).trans_eq (by ring)
    apply hp.trans
    calc
      _ ≤ 4*CL*((B+1)*R^2/N^2)*R^2/(|(Mat 2:ℝ)| *U)+2 := by
        pm_1139
      _ = _ := by ring_nf

                                                             
                                                                     
                                                                    
theorem positive_difference_actual_fourier_charted_triangular_all_sample_mass :
    ∃ η₀ a Cupper Clower Dupper Dlower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧
    ∀ (Fsrc : ℝ → ℝ) (η xcenter ycenter ya yb Tsrc E : ℝ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (Bmajor Cmajor : ℕ)
    (S : ℝ × ℝ → Finset ℕ) (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℝ × ℝ → ℕ → Fin 2 → ℚ) (vinv : ℝ × ℝ → ℕ → Fin 2 → ℤ)
    (parity : ℝ × ℝ → ℕ → Fin 2 → Fin 2) (anchor : ℝ × ℝ → ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ}
    {x : ℝ × ℝ → ℕ → Fin 2 → ℝ},
    0 < η → η ≤ η₀ → xcenter∈Icc (1:ℝ) 2 → ycenter∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let Hsrc := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc z.2-iteratedDeriv 2 Fsrc (z.2+η*z.1))/(σsrc*η)
    let center := (ycenter,Hsrc (ycenter,xcenter))
    let centerInv := (ycenter,(Hsrc (ycenter,xcenter))⁻¹)
    (∀ ab∈Gaps, ∀ j∈S ab, ∀ i,
      ‖((yp i,(2*M^2/Tsrc)*(rat ab j i:ℝ)):ℝ × ℝ)-center‖ < a ∧
      ‖((yp i,(Tsrc/(2*M^2))*(rat ab j i:ℝ)⁻¹):ℝ × ℝ)-centerInv‖ < a) →
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*N*R^2=M^3) →
    ((Q:ℝ)*N ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), (x ab) j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1))) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, ((rat ab) j i).den ≤ Q ∧ Q ≤ 2*((rat ab) j i).den) →
    (0 < lambda) →
    (0 ≤ Uband) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, lambda ≤ |((rat ab) j i:ℝ)| ∧ |((rat ab) j i:ℝ)| ≤ Uband) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (((rat ab) j i).den:ℤ) ∣ ((rat ab) j i).num*(vinv ab) j i-1) →
    (∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) →
    (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    (N^10 ≤ M^3*R^7) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ((rat ab) j 0:ℝ)∈Icc ab.1 ab.2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (ab : ℝ × ℝ) => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (ab : ℝ × ℝ) => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun (ab : ℝ × ℝ) => fun j i => (⌊(((rat ab) j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊(((rat ab) j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ab∈Gaps, ∀ j∈(S ab), (sourceColor ab) j 0=(sourceColor ab) j 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, iteratedDeriv 2 (f i) ((x ab) j i)/2=((rat ab) j i:ℝ)) →
    let q := fun (ab : ℝ × ℝ) => fun j i => ((rat ab) j i).den
    let mu := fun (ab : ℝ × ℝ) => fun j i => iteratedDeriv 3 (f i) (round ((x ab) j i))/6
    let ell := fun (ab : ℝ × ℝ) => fun j i => deriv (f i) (round ((x ab) j i))
    let b := fun (ab : ℝ × ℝ) => fun j i => (⌊((q ab) j i:ℝ)*(ell ab) j i⌋+((parity ab) j i:ℕ) : ℤ)
    let cround := fun (ab : ℝ × ℝ) => fun j i => round (((q ab) j i:ℝ)*(ell ab) j i)
    let tau := fun (ab : ℝ × ℝ) => fun j i => (((b ab) j i:ℝ)-((q ab) j i:ℝ)*(ell ab) j i)/2
    let dual := fun (ab : ℝ × ℝ) => fun j i => -2*(mu ab) j i*(Real.sqrt (2/(3*(mu ab) j i*((q ab) j i:ℝ))))^3
    let cloud := fun (ab : ℝ × ℝ) => fun j i => (![Int.fract (-((vinv ab) j i:ℝ)*(b ab) j i/(q ab) j i),
      Int.fract (-((vinv ab) j i:ℝ)/(q ab) j i),(dual ab) j i/Real.sqrt K₀,
      (3*(dual ab) j i*(tau ab) j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ab∈Gaps, ∀ j∈(S ab), (b ab) j 0-(cround ab) j 0=(b ab) j 1-(cround ab) j 1) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ a, |(cloud ab) j 0 a-(cloud ab) j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 →
    N ≤ R^2 →
    R ≤ N →
    N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (∀ ab∈Gaps, ∀ j∈(S ab), (Mat 2:ℝ)*((rat ab) j 0:ℝ)+Mat 3=((q ab) j 1:ℝ)/(q ab) j 0) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ((Mat 0:ℝ)*((rat ab) j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*((rat ab) j 0:ℝ)+Mat 3)=((rat ab) j 1:ℝ)) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), |((anchor ab) j:ℝ)-((rat ab) j 0:ℝ)| ≤ ε) →
    (∀ ab∈Gaps, ∀ j∈(S ab), 256*(((anchor ab) j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ab∈Gaps, ∀ j∈(S ab), 256 ≤ (2*ε)*((Q:ℝ)/3)*((anchor ab) j).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Blabels := fun ab => 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ ab∈Gaps, Blabels ab ≤ Bmajor) →
    (∀ ab∈Gaps, Ccharts ab ≤ Cmajor) →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    ((Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) → Mat 1≠0 →
      (∑ ab∈Gaps, ((S ab).card:ℝ)) ≤ 4*(m0:ℝ)*
        ((2*Cupper*(Cthird+1)*E^2*M^2/(κ*Lunit^3*N^4*|(Mat 1:ℝ)|))^((3:ℝ)⁻¹)+
          Cupper*(Cthird+1)*E^2*M^2/(Lunit^2*N^4*|(Mat 1:ℝ)| *(Uref:ℝ)))+
        (m0:ℝ)*(Dupper*(B+1)*E^2*M^2/(N^4*|(Mat 1:ℝ)| *(Uref:ℝ))+2)) ∧
    ((Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) → Mat 2≠0 →
      (∑ ab∈Gaps, ((S ab).card:ℝ)) ≤ 4*(m0:ℝ)*
        ((8*Clower*(Cthird+1)*R^4/(κ*Lunit^3*N^2*|(Mat 2:ℝ)|))^((3:ℝ)⁻¹)+
          4*Clower*(Cthird+1)*R^4/(Lunit^2*N^2*|(Mat 2:ℝ)| *(Uref:ℝ)))+
        (m0:ℝ)*(4*Dlower*(B+1)*R^4/(N^2*|(Mat 2:ℝ)| *(Uref:ℝ))+2)) := by
  classical
  obtain ⟨ηl,al,CU,CL,hηl,hηlcap,hal,hCU,hCL,hlongFn⟩ :=
    positive_difference_actual_fourier_charted_triangular_long_sample_mass hσsrc hcsrc hUsrc
  obtain ⟨ηs,asrc,DU,DL,hηs,_hηscap,hasrc,hDU,hDL,hshortFn⟩ :=
    positive_difference_actual_fourier_triangular_closed_gap_count hσsrc hcsrc hUsrc
  refine ⟨min ηl ηs,min al asrc,CU,CL,DU,DL,lt_min hηl hηs,
    (min_le_left _ _).trans hηlcap,lt_min hal hasrc,hCU,hCL,hDU,hDL,?_⟩
  intro Fsrc η xcenter ycenter ya yb Tsrc E Uref Refs Gaps Bselect
    Bmajor Cmajor S Q K₀ inst rat vinv parity anchor Mat e r v s
    σ δ T M N R base Bcut lambda Uband θ A W x
    hη hηsmall hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hsourceScale
    yp F Hsrc center centerInv hlocal
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hgap
    Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor f hlevel
    q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Blabels m0 hBmajor hCmajor Lunit Gamma Cthird
  pm_1705
  have hlong :
    ((Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) → Mat 1≠0 →
      (∑ ab∈Long, ((S ab).card:ℝ)) ≤ 4*(m0:ℝ)*
        ((2*CU*(Cthird+1)*E^2*M^2/(κ*Lunit^3*N^4*|(Mat 1:ℝ)|))^((3:ℝ)⁻¹)+
          CU*(Cthird+1)*E^2*M^2/(Lunit^2*N^4*|(Mat 1:ℝ)| *(Uref:ℝ)))) ∧
    ((Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) → Mat 2≠0 →
      (∑ ab∈Long, ((S ab).card:ℝ)) ≤ 4*(m0:ℝ)*
        ((8*CL*(Cthird+1)*R^4/(κ*Lunit^3*N^2*|(Mat 2:ℝ)|))^((3:ℝ)⁻¹)+
          4*CL*(Cthird+1)*R^4/(Lunit^2*N^2*|(Mat 2:ℝ)| *(Uref:ℝ)))) := by
    exact hlongFn Fsrc η xcenter ycenter ya yb Tsrc E Uref Refs Long
      (Bselect:=Bselect) Bmajor Cmajor S Q K₀ rat vinv parity anchor Mat e r v s
      (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (Bcut:=Bcut)
      (lambda:=lambda) (Uband:=Uband) (θ:=θ) A (W:=W) (x:=x)
      hη (hηsmall.trans (min_le_left _ _)) hcenterx hcentery hya hyb hreg hjets htests
      hTsrc hMtwo hsourceScale
      (fun ab hab j hj i => ⟨((hlocal ab (hinLong hab) j hj i).1).trans_le (min_le_left _ _),
        ((hlocal ab (hinLong hab) j hj i).2).trans_le (min_le_left _ _)⟩)
      hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW (fun ab hab => hx ab (hinLong hab)) (fun ab hab => hwindow ab (hinLong hab)) (fun ab hab => hden ab (hinLong hab)) hlambda hUband hθ hθmax (fun ab hab => hcurv ab (hinLong hab)) (fun ab hab => hinv ab (hinLong hab)) (fun ab hab => hchart ab (hinLong hab)) (fun ab hab => horientation ab (hinLong hab)) hBcut (fun ab hab => hs ab (hinLong hab)) (fun ab hab => hrefSet ab (hinLong hab)) (fun ab hab => hparentSet ab (hinLong hab)) hsep (fun ab hab => hwideL ab (hinLong hab)) (fun ab hab => hwideU ab (hinLong hab)) hUref hBselectSize hcutMargin hselectedWrap (fun ab hab => hreferenceDen ab (hinLong hab)) (fun ab hab => hgapWidth ab (hinLong hab)) hRQ hselectedUpper hscaleTen (fun ab hab => hfamilyGap ab (hinLong hab)) (fun ab hab => hgap ab (hinLong hab))
      (fun ab hab => hsourceColor ab (hinLong hab)) (fun ab hab => hlevel ab (hinLong hab)) (fun ab hab => hcolor ab (hinLong hab)) (fun ab hab => hnear ab (hinLong hab)) hsmall hNR hRN hNcube hminscale hMatdet (fun ab hab => hMatt ab (hinLong hab)) (fun ab hab => hMatmap ab (hinLong hab)) hMatgamma hNtwo (fun ab hab => hL ab (hinLong hab)) (fun ab hab => hU ab (hinLong hab)) (fun ab hab => hanchor ab (hinLong hab)) (fun ab hab => hcut ab (hinLong hab)) (fun ab hab => hcount ab (hinLong hab)) hsize hD hΔ hBsize (fun ab hab => hBmajor ab (hinLong hab)) (fun ab hab => hCmajor ab (hinLong hab))
      (fun _ hab => (Finset.mem_filter.mp hab).2)
  pm_1693
  pm_1756
  have hNscale : N^2 ≤ M*R := by
    apply (mul_le_mul_iff_of_pos_right hN).mp
    calc
      _ = N^3 := by ring
      _ ≤ M*R^2 := hNcube
      _ ≤ (M*R)*N := by
        have hh := mul_le_mul_of_nonneg_left hRN (mul_nonneg hM.le (zero_lt_one.trans_le hR).le)
        nlinarith only [hh]
  have hchoose ab (hab : ab∈Short) : ∃ j, j∈S ab := (Finset.mem_filter.mp hab).2.1
  choose! j hj using hchoose
  have hshortcount :
      ((Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) → Mat 1≠0 →
        (Short.card:ℝ) ≤ DU*(B+1)*E^2*M^2/(N^4*|(Mat 1:ℝ)| *(Uref:ℝ))+2) ∧
      ((Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) → Mat 2≠0 →
        (Short.card:ℝ) ≤ 4*DL*(B+1)*R^4/(N^2*|(Mat 2:ℝ)| *(Uref:ℝ))+2) := by
    exact hshortFn Fsrc η xcenter ycenter ya yb Tsrc E Refs Short Mat Q K₀
      (fun ab => rat ab (j ab)) (fun ab => vinv ab (j ab))
      (fun ab => parity ab (j ab)) (fun ab => x ab (j ab))
      (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (U:=(Uref:ℝ)) A
      hη (hηsmall.trans (min_le_right _ _)) hcenterx hcentery hya hyb hreg hjets htests
      hTsrc hMtwo hsourceScale
      (fun ab hab i => ⟨((hlocal ab (hinShort hab) _ (hj ab hab) i).1).trans_le (min_le_right _ _),
        ((hlocal ab (hinShort hab) _ (hj ab hab) i).2).trans_le (min_le_right _ _)⟩)
      hσ hδ hF₃ hT hM hN hR hUp hQ hscale hmesh hNscale hA hW
      (by
        intro a ha b hb hne
        calc
          (Uref:ℝ)/(4*R^2)=((Uref:ℝ)/R^2)/4 := by ring
          _ ≤ |a-b| := (hsep a ha b hb hne).le)
      (fun ab hab => hgap ab (hinShort hab))
      (fun ab hab => hx ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hden ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hinv ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hlevel ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hcolor ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hnear ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hMatt ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hMatmap ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hfamilyGap ab (hinShort hab) _ (hj ab hab))
  have hshortmass : (∑ ab∈Short, ((S ab).card:ℝ)) ≤ (m0:ℝ)*(Short.card:ℝ) := by
    calc
      _ ≤ ∑ _ab∈Short, (m0:ℝ) := by
        pm_8042
      _ = _ := by simp [mul_comm]
  pm_1704
  constructor
  · intro htri hentry
    rw [hpartition]
    exact add_le_add (hlong.1 htri hentry)
      (hshortmass.trans (mul_le_mul_of_nonneg_left (hshortcount.1 htri hentry) (Nat.cast_nonneg _)))
  · intro htri hentry
    rw [hpartition]
    exact add_le_add (hlong.2 htri hentry)
      (hshortmass.trans (mul_le_mul_of_nonneg_left (hshortcount.2 htri hentry) (Nat.cast_nonneg _)))
end

                                                                
                                                                       
                                          
theorem positive_difference_source_chart_twelfth_partition
    {ι : Type*} (S : Finset ι) (F : ℝ → ℝ)
    (y z : ι → ℝ) (rat : ι → ℚ) {σ c U η T M a : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hT : 0 < T) (hM : 0 < M) (ha : 0 < a)
    (hy : ∀ i∈S, y i∈Icc (1:ℝ) 2)
    (hz : ∀ i∈S, z i∈Icc M (2*M))
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    (∀ i∈S, iteratedDeriv 2 (f (y i)) (z i)/2=(rat i:ℝ)) →
    let Hsrc := fun p : ℝ × ℝ =>
      (iteratedDeriv 2 F p.2-iteratedDeriv 2 F (p.2+η*p.1))/(σ*η)
    let u := fun i => (2*M^2/T)*(rat i:ℝ)
    let w := fun i => (T/(2*M^2))*(rat i:ℝ)⁻¹
    let color := fun i => (⌊y i/a⌋,⌊u i/a⌋,⌊w i/a⌋)
    let Cap := (4/a+3)*((6*U/σ)/a+3)*((4*σ/c)/a+3)
    ((S.image color).card:ℝ) ≤ Cap ∧
    (∀ k∈S.image color, ∃ iref∈S, color iref=k ∧
      let xcenter := z iref/M
      let ycenter := y iref
      xcenter∈Icc (1:ℝ) 2 ∧ ycenter∈Icc (1:ℝ) 2 ∧
      ∀ i∈S, color i=k →
        ‖((y i,u i):ℝ × ℝ)-(ycenter,Hsrc (ycenter,xcenter))‖ < a ∧
        ‖((y i,w i):ℝ × ℝ)-(ycenter,(Hsrc (ycenter,xcenter))⁻¹)‖ < a) ∧
    ∀ coeff : ι → ℂ, ‖∑ i∈S,coeff i‖^12 ≤
      Cap^11*∑ k∈S.image color, ‖∑ i∈S.filter (fun i => color i=k),coeff i‖^12 := by
  classical
  intro f hlevel Hsrc u w color Cap
  have hsp : 0 < 2*M^2/T := by positivity
  have hsip : 0 < T/(2*M^2) := by positivity
  have hbounds i (hi : i∈S) :
      c*T/(4*σ*M^2) ≤ |(rat i:ℝ)| ∧ |(rat i:ℝ)| ≤ (3*U/σ)*T/(2*M^2) := by
    rw [←hlevel i hi]
    exact positive_difference_half_curvature_source_bounds F hσ hc hU hη hηmax hT hM
      (hy i hi) (hz i hi) hf hbound htests
  have hu i (hi : i∈S) : |u i| ≤ 3*U/σ := by
    dsimp only [u]
    rw [abs_mul,abs_of_pos hsp]
    calc
      _ ≤ (2*M^2/T)*((3*U/σ)*T/(2*M^2)) :=
        mul_le_mul_of_nonneg_left (hbounds i hi).2 hsp.le
      _ = _ := by field_simp
  have hw i (hi : i∈S) : |w i| ≤ 2*σ/c := by
    have hp : 0 < |(rat i:ℝ)| :=
      (show 0 < c*T/(4*σ*M^2) by positivity).trans_le (hbounds i hi).1
    dsimp only [w]
    rw [abs_mul,abs_inv,abs_of_pos hsip,←div_eq_mul_inv]
    apply (div_le_iff₀ hp).mpr
    calc
      _ = (2*σ/c)*(c*T/(4*σ*M^2)) := by field_simp; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left (hbounds i hi).1 (by positivity)
  have hsource i (hi : i∈S) : Hsrc (y i,z i/M)=u i := by
    have hd := positive_difference_physical_iteratedDeriv F (T:=T) (σ:=σ) hM
      (hM.trans_le (hz i hi).1) (mul_nonneg hη.le (by linarith only [(hy i hi).1])) hf 2
    have hh := hlevel i hi
    change iteratedDeriv 2 (fun t => T*(F (t/M)-F (t/M+η*y i))/(σ*η)) (z i)/2=(rat i:ℝ) at hh
    rw [hd] at hh
    dsimp only [Hsrc,u]
    rw [←hh]
    field_simp
  have hinv i : (u i)⁻¹=w i := by
    dsimp only [u,w]
    rw [mul_inv_rev,inv_div]
    ring
  have h₁ : ((S.image (fun i => (color i).1)).card:ℝ) ≤ 4/a+3 := by
    have hh := scaled_floor_image_card (Q:=1) (δ:=a) (R:=2) S y
      (by norm_num) ha (by norm_num)
      (by intro i hi; rw [abs_of_nonneg (by linarith only [(hy i hi).1])]; simpa using (hy i hi).2)
    pm_1846
  have h₂ : ((S.image (fun i => (color i).2.1)).card:ℝ) ≤ (6*U/σ)/a+3 := by
    have hh := scaled_floor_image_card (Q:=1) (δ:=a) (R:=3*U/σ) S u
      (by norm_num) ha (by positivity) (by intro i hi; simpa only [mul_one] using hu i hi)
    pm_7758
  have h₃ : ((S.image (fun i => (color i).2.2)).card:ℝ) ≤ (4*σ/c)/a+3 := by
    have hh := scaled_floor_image_card (Q:=1) (δ:=a) (R:=2*σ/c) S w
      (by norm_num) ha (by positivity) (by intro i hi; simpa only [mul_one] using hw i hi)
    pm_7758
  have hcard : ((S.image color).card:ℝ) ≤ Cap := by
    have hsub : S.image color ⊆
        (S.image (fun i => (color i).1)) ×ˢ
          ((S.image (fun i => (color i).2.1)) ×ˢ (S.image (fun i => (color i).2.2))) := by
      pm_2532 k hk i hi
      pm_7664 hi
    pm_7459
    have hh' : ((S.image color).card:ℝ) ≤
        ((S.image (fun i => (color i).1)).card:ℝ)*
          (((S.image (fun i => (color i).2.1)).card:ℝ)*
            ((S.image (fun i => (color i).2.2)).card:ℝ)) := by exact_mod_cast hh
    apply hh'.trans
    have hm := mul_le_mul h₁ (mul_le_mul h₂ h₃ (by positivity) (by positivity))
      (by positivity) (by positivity)
    simpa only [Cap,mul_assoc] using hm
  have hsame {b d : ℝ} (he : ⌊b/a⌋=⌊d/a⌋) : |b-d| < a := by
    have hh := Int.abs_sub_lt_one_of_floor_eq_floor he
    pm_1325 ha hh
    exact (div_lt_iff₀ ha).mp hh |>.trans_eq (one_mul a)
  refine ⟨hcard,?_,?_⟩
  · intro k hk
    obtain ⟨iref,hiref,he⟩ := Finset.mem_image.mp hk
    refine ⟨iref,hiref,he,?_,hy iref hiref,?_⟩
    · exact ⟨(le_div_iff₀ hM).mpr (by simpa using (hz iref hiref).1),
        (div_le_iff₀ hM).mpr (by simpa [mul_comm] using (hz iref hiref).2)⟩
    · intro i _hi hci
      have heq : color i=color iref := hci.trans he.symm
      have hdy := hsame (congrArg Prod.fst heq)
      have hdu := hsame (congrArg (fun t : ℤ × ℤ × ℤ => t.2.1) heq)
      have hdw := hsame (congrArg (fun t : ℤ × ℤ × ℤ => t.2.2) heq)
      change max |y i-y iref| |u i-Hsrc (y iref,z iref/M)| < a ∧
        max |y i-y iref| |w i-(Hsrc (y iref,z iref/M))⁻¹| < a
      rw [hsource iref hiref,hinv]
      exact ⟨max_lt_iff.mpr ⟨hdy,hdu⟩,max_lt_iff.mpr ⟨hdy,hdw⟩⟩
  · intro coeff
    let Keys := S.image color
    let V := fun k => S.filter (fun i => color i=k)
    let g := fun k => ∑ i∈V k,coeff i
    pm_1848 k Keys i S coeff hi
    have hh : (∑ k∈Keys,‖g k‖)^12 ≤ (Keys.card:ℝ)^11*∑ k∈Keys,‖g k‖^12 := by
      pm_1905
    exact (hp.trans hh).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ Keys.card) hcard 11)
      (Finset.sum_nonneg (fun _ _ => by positivity)))

                                                                  
                                                                     
                                                                        
theorem positive_difference_actual_fourier_charted_triangular_colored_sample_mass
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower Dupper Dlower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧
    ∀ (Fsrc : ℝ → ℝ) (η ya yb Tsrc E : ℝ) (chartKey : ℤ × ℤ × ℤ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (Bmajor Cmajor : ℕ)
    (S : ℝ × ℝ → Finset ℕ) (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℝ × ℝ → ℕ → Fin 2 → ℚ) (vinv : ℝ × ℝ → ℕ → Fin 2 → ℤ)
    (parity : ℝ × ℝ → ℕ → Fin 2 → Fin 2) (anchor : ℝ × ℝ → ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ}
    {x : ℝ × ℝ → ℕ → Fin 2 → ℝ},
    0 < η → η ≤ η₀ →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let chartColor := fun ab j i =>
      (⌊yp i/a⌋,⌊((2*M^2/Tsrc)*(rat ab j i:ℝ))/a⌋,
        ⌊((Tsrc/(2*M^2))*(rat ab j i:ℝ)⁻¹)/a⌋)
    (∀ ab∈Gaps, ∀ j∈S ab, ∀ i, chartColor ab j i=chartKey) →
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*N*R^2=M^3) →
    ((Q:ℝ)*N ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), (x ab) j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1))) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, ((rat ab) j i).den ≤ Q ∧ Q ≤ 2*((rat ab) j i).den) →
    (0 < lambda) →
    (0 ≤ Uband) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, lambda ≤ |((rat ab) j i:ℝ)| ∧ |((rat ab) j i:ℝ)| ≤ Uband) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (((rat ab) j i).den:ℤ) ∣ ((rat ab) j i).num*(vinv ab) j i-1) →
    (∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) →
    (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    (N^10 ≤ M^3*R^7) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ((rat ab) j 0:ℝ)∈Icc ab.1 ab.2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (ab : ℝ × ℝ) => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (ab : ℝ × ℝ) => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun (ab : ℝ × ℝ) => fun j i => (⌊(((rat ab) j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊(((rat ab) j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ab∈Gaps, ∀ j∈(S ab), (sourceColor ab) j 0=(sourceColor ab) j 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, iteratedDeriv 2 (f i) ((x ab) j i)/2=((rat ab) j i:ℝ)) →
    let q := fun (ab : ℝ × ℝ) => fun j i => ((rat ab) j i).den
    let mu := fun (ab : ℝ × ℝ) => fun j i => iteratedDeriv 3 (f i) (round ((x ab) j i))/6
    let ell := fun (ab : ℝ × ℝ) => fun j i => deriv (f i) (round ((x ab) j i))
    let b := fun (ab : ℝ × ℝ) => fun j i => (⌊((q ab) j i:ℝ)*(ell ab) j i⌋+((parity ab) j i:ℕ) : ℤ)
    let cround := fun (ab : ℝ × ℝ) => fun j i => round (((q ab) j i:ℝ)*(ell ab) j i)
    let tau := fun (ab : ℝ × ℝ) => fun j i => (((b ab) j i:ℝ)-((q ab) j i:ℝ)*(ell ab) j i)/2
    let dual := fun (ab : ℝ × ℝ) => fun j i => -2*(mu ab) j i*(Real.sqrt (2/(3*(mu ab) j i*((q ab) j i:ℝ))))^3
    let cloud := fun (ab : ℝ × ℝ) => fun j i => (![Int.fract (-((vinv ab) j i:ℝ)*(b ab) j i/(q ab) j i),
      Int.fract (-((vinv ab) j i:ℝ)/(q ab) j i),(dual ab) j i/Real.sqrt K₀,
      (3*(dual ab) j i*(tau ab) j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ab∈Gaps, ∀ j∈(S ab), (b ab) j 0-(cround ab) j 0=(b ab) j 1-(cround ab) j 1) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ a, |(cloud ab) j 0 a-(cloud ab) j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 →
    N ≤ R^2 →
    R ≤ N →
    N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (∀ ab∈Gaps, ∀ j∈(S ab), (Mat 2:ℝ)*((rat ab) j 0:ℝ)+Mat 3=((q ab) j 1:ℝ)/(q ab) j 0) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ((Mat 0:ℝ)*((rat ab) j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*((rat ab) j 0:ℝ)+Mat 3)=((rat ab) j 1:ℝ)) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), |((anchor ab) j:ℝ)-((rat ab) j 0:ℝ)| ≤ ε) →
    (∀ ab∈Gaps, ∀ j∈(S ab), 256*(((anchor ab) j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ab∈Gaps, ∀ j∈(S ab), 256 ≤ (2*ε)*((Q:ℝ)/3)*((anchor ab) j).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Blabels := fun ab => 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ ab∈Gaps, Blabels ab ≤ Bmajor) →
    (∀ ab∈Gaps, Ccharts ab ≤ Cmajor) →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    ((Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) → Mat 1≠0 →
      (∑ ab∈Gaps, ((S ab).card:ℝ)) ≤ 4*(m0:ℝ)*
        ((2*Cupper*(Cthird+1)*E^2*M^2/(κ*Lunit^3*N^4*|(Mat 1:ℝ)|))^((3:ℝ)⁻¹)+
          Cupper*(Cthird+1)*E^2*M^2/(Lunit^2*N^4*|(Mat 1:ℝ)| *(Uref:ℝ)))+
        (m0:ℝ)*(Dupper*(B+1)*E^2*M^2/(N^4*|(Mat 1:ℝ)| *(Uref:ℝ))+2)) ∧
    ((Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) → Mat 2≠0 →
      (∑ ab∈Gaps, ((S ab).card:ℝ)) ≤ 4*(m0:ℝ)*
        ((8*Clower*(Cthird+1)*R^4/(κ*Lunit^3*N^2*|(Mat 2:ℝ)|))^((3:ℝ)⁻¹)+
          4*Clower*(Cthird+1)*R^4/(Lunit^2*N^2*|(Mat 2:ℝ)| *(Uref:ℝ)))+
        (m0:ℝ)*(4*Dlower*(B+1)*R^4/(N^2*|(Mat 2:ℝ)| *(Uref:ℝ))+2)) := by
  pm_2479 hmassFn positive_difference_actual_fourier_charted_triangular_all_sample_mass
  pm_2478
  intro Fsrc η ya yb Tsrc E chartKey Uref Refs Gaps Bselect
    Bmajor Cmajor S Q K₀ inst rat vinv parity anchor Mat e r v s
    σ δ T M N R base Bcut lambda Uband θ A W x
    hη hηsmall hya hyb hreg hjets htests hTsrc hMtwo hsourceScale
    yp F chartColor hchartColor
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hgap
    Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor f hlevel
    q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Blabels m0 hBmajor hCmajor Lunit Gamma Cthird
  pm_2477
  let Hsrc := fun p : ℝ × ℝ =>
    (iteratedDeriv 2 Fsrc p.2-iteratedDeriv 2 Fsrc (p.2+η*p.1))/(σsrc*η)
  let Points : Finset ((ℝ × ℝ) × (ℕ × Fin 2)) :=
    Gaps.biUnion (fun ab => ((S ab) ×ˢ (Finset.univ : Finset (Fin 2))).image (fun p => (ab,p)))
  let py := fun p : (ℝ × ℝ) × (ℕ × Fin 2) => yp p.2.2
  let pz := fun p : (ℝ × ℝ) × (ℕ × Fin 2) => (A p.2.2:ℝ)+x p.1 p.2.1 p.2.2
  pm_6829 pr rat
  pm_6829 pc chartColor
  have hmem ab (hab : ab∈Gaps) j (hj : j∈S ab) i : (ab,(j,i))∈Points :=
    Finset.mem_biUnion.mpr ⟨ab,hab,Finset.mem_image_of_mem _
      (Finset.mem_product.mpr ⟨hj,Finset.mem_univ i⟩)⟩
  have hmem' p (hp : p∈Points) : p.1∈Gaps ∧ p.2.1∈S p.1 := by
    obtain ⟨ab,hab,hmem⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨⟨j,i⟩,hji,rfl⟩ := Finset.mem_image.mp hmem
    exact ⟨hab,(Finset.mem_product.mp hji).1⟩
  have hpy p : py p∈Icc (1:ℝ) 2 := by
    pm_1746
    exact hyp p.2.2
  have hpz p (hp : p∈Points) : pz p∈Icc M (2*M) := by
    have hm := hmem' p hp
    have hh := hx p.1 hm.1 p.2.1 hm.2 p.2.2
    dsimp only [pz]
    exact ⟨by linarith only [hA p.2.2,hh.1],by linarith only [hW p.2.2,hh.2]⟩
  have hlevels p (hp : p∈Points) :
      iteratedDeriv 2 (Src (py p)) (pz p)/2=(pr p:ℝ) := by
    have hm := hmem' p hp
    change iteratedDeriv 2 (Src (yp p.2.2)) ((A p.2.2:ℝ)+x p.1 p.2.1 p.2.2)/2=
      (rat p.1 p.2.1 p.2.2:ℝ)
    rw [←hjet]
    exact hlevel p.1 hm.1 p.2.1 hm.2 p.2.2
  have hcolors p (hp : p∈Points) : pc p=chartKey := by
    have hm := hmem' p hp
    exact hchartColor p.1 hm.1 p.2.1 hm.2 p.2.2
  have hcentres : ∃ xcenter∈Icc (1:ℝ) 2, ∃ ycenter∈Icc (1:ℝ) 2,
      ∀ ab∈Gaps, ∀ j∈S ab, ∀ i,
        ‖((yp i,(2*M^2/Tsrc)*(rat ab j i:ℝ)):ℝ × ℝ)-
          (ycenter,Hsrc (ycenter,xcenter))‖ < a ∧
        ‖((yp i,(Tsrc/(2*M^2))*(rat ab j i:ℝ)⁻¹):ℝ × ℝ)-
          (ycenter,(Hsrc (ycenter,xcenter))⁻¹)‖ < a := by
    by_cases hne : Points.Nonempty
    · obtain ⟨p,hp⟩ := hne
      obtain ⟨_hCap,hcenters,_hMoment⟩ := positive_difference_source_chart_twelfth_partition
        Points Fsrc py pz pr hσsrc hcsrc hUsrc hη (hηsmall.trans hηcap)
        hTsrc hM ha (fun p _ => hpy p) hpz hreg hjets htests hlevels
      have hkey : chartKey∈Points.image pc := Finset.mem_image.mpr ⟨p,hp,hcolors p hp⟩
      pm_529 iref _hiref _hrefKey hxc hyc hwithin hcenters chartKey hkey
      refine ⟨pz iref/M,hxc,py iref,hyc,?_⟩
      intro ab hab j hj i
      exact hwithin (ab,(j,i)) (hmem ab hab j hj i) (hcolors _ (hmem ab hab j hj i))
    · refine ⟨1,by norm_num,1,by norm_num,?_⟩
      intro ab hab j hj i
      exact False.elim (hne ⟨(ab,(j,i)),hmem ab hab j hj i⟩)
  obtain ⟨xcenter,hcenterx,ycenter,hcentery,hlocal⟩ := hcentres
  exact hmassFn Fsrc η xcenter ycenter ya yb Tsrc E Uref Refs Gaps
    (Bselect:=Bselect) Bmajor Cmajor S Q K₀ rat vinv parity anchor Mat e r v s
    (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (Bcut:=Bcut)
    (lambda:=lambda) (Uband:=Uband) (θ:=θ) A (W:=W) (x:=x)
    hη hηsmall hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hsourceScale hlocal
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hgap
    hsourceColor hlevel hcolor hnear hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma hNtwo hL hU hanchor hcut hcount hsize hD hΔ hBsize hBmajor hCmajor

private theorem inverse_cuberoot_nat_prefix (H : ℕ) :
    (∑ n∈Finset.range H, ((n:ℝ)+1)^(-(1:ℝ)/3)) ≤
      (3/2:ℝ)*((H:ℝ)+1)^((2:ℝ)/3) := by
  have hanti : AntitoneOn (fun x : ℝ => x^(-(1:ℝ)/3)) (Icc (1:ℝ) (1+H)) := by
    intro x hx y _hy hxy
    exact Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hx.1) hxy (by norm_num)
  have hh := hanti.sum_le_integral
  rw [_root_.integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -(1:ℝ)/3))] at hh
  have hh' : (∑ n∈Finset.range H, ((n:ℝ)+1+1)^(-(1:ℝ)/3)) ≤
      (((H:ℝ)+1)^((2:ℝ)/3)-1)/((2:ℝ)/3) := by
    simpa only [Nat.cast_add,Nat.cast_one,show (-(1:ℝ)/3)+1=2/3 by norm_num,
      Real.one_rpow,add_comm (1:ℝ),add_assoc] using hh
  have hs := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.le_succ H))
    (fun n _ _ => Real.rpow_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)+1) (-(1:ℝ)/3))
  have hs' : (∑ n∈Finset.range H, ((n:ℝ)+1)^(-(1:ℝ)/3)) ≤
      (∑ n∈Finset.range H, ((n:ℝ)+1+1)^(-(1:ℝ)/3))+1 := by
    simpa only [Finset.sum_range_succ',Nat.cast_add,Nat.cast_one,Nat.cast_zero,
      zero_add,Real.one_rpow] using hs
  linarith only [hh',hs']

private theorem integer_inverse_cuberoot_sum
    (S : Finset ℤ) {D : ℝ} (hD : 0 ≤ D)
    (hS : ∀ b∈S, |(b:ℝ)| ≤ D) :
    (∑ b∈S, |(b:ℝ)|^(-(1:ℝ)/3)) ≤ 3*(D+2)^((2:ℝ)/3) := by
  classical
  let H := ⌈D⌉₊
  let f := fun b : ℤ => |(b:ℝ)|^(-(1:ℝ)/3)
  have hsub : S ⊆ Finset.Icc (-(H:ℤ)) (H:ℤ) := by
    intro b hb
    apply Finset.mem_Icc.mpr
    have hh := abs_le.mp ((hS b hb).trans (Nat.le_ceil D))
    constructor
    · exact_mod_cast hh.1
    · exact_mod_cast hh.2
  have heven : f.Even := by intro b; simp only [f,Int.cast_neg,abs_neg]
  calc
    _ ≤ ∑ b∈Finset.Icc (-(H:ℤ)) (H:ℤ),f b :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by dsimp only [f]; positivity)
    _ = 2*(∑ n∈Finset.range H, ((n:ℝ)+1)^(-(1:ℝ)/3)) := by
      rw [Finset.sum_Icc_of_even_eq_range heven,Finset.sum_range_succ']
      norm_num [f]
      apply Finset.sum_congr rfl
      intro n _
      rw [abs_of_pos (by positivity : (0:ℝ) < (n:ℝ)+1)]
    _ ≤ 3*((H:ℝ)+1)^((2:ℝ)/3) := by
      pm_8633 hh inverse_cuberoot_nat_prefix H
      linarith only [hh]
    _ ≤ _ := by
      pm_6930
      apply Real.rpow_le_rpow (by positivity) _ (by norm_num : (0:ℝ) ≤ 2/3)
      pm_7972 hh
      linarith only [hh]

private theorem integer_cubic_reciprocal_weight_sum
    (S : Finset ℤ) {D A B C : ℝ} (hD : 0 ≤ D)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hS : ∀ b∈S, b ≠ 0 ∧ |(b:ℝ)| ≤ D) :
    (∑ b∈S, ((A/|(b:ℝ)|)^((3:ℝ)⁻¹)+B/|(b:ℝ)|+C)) ≤
      3*A^((3:ℝ)⁻¹)*(D+2)^((2:ℝ)/3)+
        2*B*(3+2*Real.log (D+2))+C*(2*D+1) := by
  classical
  let H := ⌈D⌉₊
  have hsub : S ⊆ (Finset.Icc (-(H:ℤ)) (H:ℤ)).erase 0 := by
    intro b hb
    apply Finset.mem_erase.mpr
    refine ⟨(hS b hb).1,Finset.mem_Icc.mpr ?_⟩
    have hh := abs_le.mp ((hS b hb).2.trans (Nat.le_ceil D))
    constructor
    · exact_mod_cast hh.1
    · exact_mod_cast hh.2
  have hrec : ∑ b∈S, 1/|(b:ℝ)| ≤ 2*(3+2*Real.log (D+2)) := by
    have hh := (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun _ _ _ => by positivity : ∀ b∈(Finset.Icc (-(H:ℤ)) (H:ℤ)).erase 0,
        b∉S → (0:ℝ) ≤ 1/|(b:ℝ)|)).trans
      (TaoTrudgianYang2025.bourgain_integer_reciprocal_sum H)
    pm_7972 hceil
    have hlog : Real.log ((H:ℝ)+1) ≤ Real.log (D+2) :=
      Real.log_le_log (by positivity) (by linarith only [hceil])
    linarith only [hh,hlog]
  have hcard : (S.card:ℝ) ≤ 2*D+1 :=
    integer_card_le_of_abs_sub_le (a:=0) S hD
      (by intro b hb; simpa only [sub_zero] using (hS b hb).2)
  have hcube := integer_inverse_cuberoot_sum S hD (fun b hb => (hS b hb).2)
  have hfactor b :
      (A/|(b:ℝ)|)^((3:ℝ)⁻¹)=A^((3:ℝ)⁻¹)*|(b:ℝ)|^(-(1:ℝ)/3) := by
    rw [Real.div_rpow hA (abs_nonneg _)]
    rw [show -(1:ℝ)/3 = -((3:ℝ)⁻¹) by norm_num,Real.rpow_neg (abs_nonneg _)]
    exact div_eq_mul_inv _ _
  calc
    _ = A^((3:ℝ)⁻¹)*(∑ b∈S, |(b:ℝ)|^(-(1:ℝ)/3))+
        B*(∑ b∈S,1/|(b:ℝ)|)+C*(S.card:ℝ) := by
      simp_rw [hfactor]
      rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
      simp only [Finset.mul_sum,Finset.sum_const,nsmul_eq_mul,mul_one_div]
      ring
    _ ≤ A^((3:ℝ)⁻¹)*(3*(D+2)^((2:ℝ)/3))+
        B*(2*(3+2*Real.log (D+2)))+C*(2*D+1) :=
      add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hcube (Real.rpow_nonneg hA _))
        (mul_le_mul_of_nonneg_left hrec hB))
        (mul_le_mul_of_nonneg_left hcard hC)
    _ = _ := by ring

private theorem triangular_weight_normalize (m X Y Z P Q R u b : ℝ) :
    4*m*((X/(P*b))^((3:ℝ)⁻¹)+Y/(Q*b*u))+
      m*(Z/(R*b*u)+2) =
    4*m*(((X/P)/b)^((3:ℝ)⁻¹)+(Y/(Q*u)+Z/(4*R*u))/b+1/2) := by
  rw [div_div]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

private theorem physical_source_triangular_constants_nonneg
    {σ δ : ℝ} (hσ : 0 < σ) (hδ0 : 0 ≤ δ) :
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    0 ≤ B ∧ 0 ≤ Cthird := by
  intro κ Cphys c J B C₂ C₃ Ct Cc Kres Gamma Cthird
  pm_1689
  pm_2669
  pm_901
  have hCN : 0 ≤ quarticNonlinearResidualConstant σ δ := by
    dsimp only [quarticNonlinearResidualConstant]; positivity
  pm_1856
  pm_1853
  have hK : 0 ≤ Kres := div_nonneg (mul_nonneg (by norm_num)
    (add_nonneg (add_nonneg (add_nonneg
      (add_nonneg (div_nonneg (mul_nonneg (by norm_num) hB) (by norm_num))
        (mul_nonneg (mul_nonneg (by norm_num) hB) hCc))
      (mul_nonneg (by norm_num) hCt))
      (mul_nonneg (by norm_num) hCc))
      (mul_nonneg (by norm_num) hCN))) hκ.le
  pm_2476
  exact ⟨hB,hCthird⟩

                                                                 
                                                                    
                                                             
theorem positive_difference_actual_fourier_charted_triangular_translation_sample_mass
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower Dupper Dlower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧
    ∀ (Fsrc : ℝ → ℝ) (η ya yb Tsrc E Dtranslation : ℝ)
    (Translations : Finset ℤ) (chartKey : ℤ → ℤ × ℤ × ℤ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : ℤ → Finset (ℝ × ℝ)) {Bselect : ℝ}
    (Bmajor Cmajor : ℕ)
    (S : ℤ → ℝ × ℝ → Finset ℕ) (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℤ → ℝ × ℝ → ℕ → Fin 2 → ℚ) (vinv : ℤ → ℝ × ℝ → ℕ → Fin 2 → ℤ)
    (parity : ℤ → ℝ × ℝ → ℕ → Fin 2 → Fin 2) (anchor : ℤ → ℝ × ℝ → ℕ → ℚ)
    (Mat : ℤ → Fin 4 → ℤ) (e r v s : ℤ → ℝ × ℝ → ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ}
    {x : ℤ → ℝ × ℝ → ℕ → Fin 2 → ℝ},
    0 < η → η ≤ η₀ →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    0 ≤ Dtranslation →
    (∀ t∈Translations, t≠0 ∧ |(t:ℝ)| ≤ Dtranslation) →
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let chartColor := fun (t : ℤ) ab j i =>
      (⌊yp i/a⌋,⌊((2*M^2/Tsrc)*(rat t ab j i:ℝ))/a⌋,
        ⌊((Tsrc/(2*M^2))*(rat t ab j i:ℝ)⁻¹)/a⌋)
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈S t ab, ∀ i, chartColor t ab j i=chartKey t) →
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*N*R^2=M^3) →
    ((Q:ℝ)*N ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, (x t ab) j i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), (x t ab) j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1))) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, ((rat t ab) j i).den ≤ Q ∧ Q ≤ 2*((rat t ab) j i).den) →
    (0 < lambda) →
    (0 ≤ Uband) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, lambda ≤ |((rat t ab) j i:ℝ)| ∧ |((rat t ab) j i:ℝ)| ≤ Uband) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, (((rat t ab) j i).den:ℤ) ∣ ((rat t ab) j i).num*(vinv t ab) j i-1) →
    (∀ t∈Translations, ∀ ab∈Gaps t, (v t ab)*(r t ab)-(e t ab)*(s t ab)=1) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ((0:ℝ) < (r t ab) ∧ ((e t ab):ℝ)/(r t ab)=ab.1) ∨
      (((r t ab):ℝ) < 0 ∧ ((e t ab):ℝ)/(r t ab)=ab.2)) →
    (0 < Bcut) →
    (∀ t∈Translations, ∀ ab∈Gaps t, (s t ab) ≠ 0) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ((e t ab):ℝ)/(r t ab)∈Refs) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ((v t ab):ℝ)/(s t ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, (x t ab) j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, (x t ab) j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2) →
    (∀ t∈Translations, ∀ ab∈Gaps t, R^2 ≤ ((r t ab):ℝ)^2*(Uref:ℝ)) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    (N^10 ≤ M^3*R^7) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ((rat t ab) j 0:ℝ)∈Icc ab.1 ab.2) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (t : ℤ) (ab : ℝ × ℝ) => 1+(|((v t ab):ℝ)|+|((s t ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (t : ℤ) (ab : ℝ × ℝ) => 1+(|((r t ab):ℝ)| *Vheight+|((e t ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => (⌊(((rat t ab) j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊(((rat t ab) j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), (sourceColor t ab) j 0=(sourceColor t ab) j 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, iteratedDeriv 2 (f i) ((x t ab) j i)/2=((rat t ab) j i:ℝ)) →
    let q := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => ((rat t ab) j i).den
    let mu := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => iteratedDeriv 3 (f i) (round ((x t ab) j i))/6
    let ell := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => deriv (f i) (round ((x t ab) j i))
    let b := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => (⌊((q t ab) j i:ℝ)*(ell t ab) j i⌋+((parity t ab) j i:ℕ) : ℤ)
    let cround := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => round (((q t ab) j i:ℝ)*(ell t ab) j i)
    let tau := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => (((b t ab) j i:ℝ)-((q t ab) j i:ℝ)*(ell t ab) j i)/2
    let dual := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => -2*(mu t ab) j i*(Real.sqrt (2/(3*(mu t ab) j i*((q t ab) j i:ℝ))))^3
    let cloud := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => (![Int.fract (-((vinv t ab) j i:ℝ)*(b t ab) j i/(q t ab) j i),
      Int.fract (-((vinv t ab) j i:ℝ)/(q t ab) j i),(dual t ab) j i/Real.sqrt K₀,
      (3*(dual t ab) j i*(tau t ab) j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), (b t ab) j 0-(cround t ab) j 0=(b t ab) j 1-(cround t ab) j 1) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ a, |(cloud t ab) j 0 a-(cloud t ab) j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 →
    N ≤ R^2 →
    R ≤ N →
    N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    (∀ t∈Translations, Mat t 0*Mat t 3-Mat t 1*Mat t 2=1) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), (Mat t 2:ℝ)*((rat t ab) j 0:ℝ)+Mat t 3=((q t ab) j 1:ℝ)/(q t ab) j 0) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ((Mat t 0:ℝ)*((rat t ab) j 0:ℝ)+Mat t 1)/
      ((Mat t 2:ℝ)*((rat t ab) j 0:ℝ)+Mat t 3)=((rat t ab) j 1:ℝ)) →
    (∀ t∈Translations, |(Mat t 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, (x t ab) j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, (x t ab) j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), |((anchor t ab) j:ℝ)-((rat t ab) j 0:ℝ)| ≤ ε) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), 256*(((anchor t ab) j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), 256 ≤ (2*ε)*((Q:ℝ)/3)*((anchor t ab) j).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Blabels := fun (t : ℤ) ab => 6+216*(⌊Real.logb 2 (P₁ t ab*P₂ t ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ t∈Translations, ∀ ab∈Gaps t, Blabels t ab ≤ Bmajor) →
    (∀ t∈Translations, ∀ ab∈Gaps t, Ccharts ab ≤ Cmajor) →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Aupper := 2*Cupper*(Cthird+1)*E^2*M^2/(κ*Lunit^3*N^4)
    let Bupper := Cupper*(Cthird+1)*E^2*M^2/(Lunit^2*N^4*(Uref:ℝ))+
      Dupper*(B+1)*E^2*M^2/(4*N^4*(Uref:ℝ))
    let Alower := 8*Clower*(Cthird+1)*R^4/(κ*Lunit^3*N^2)
    let Blower := 4*Clower*(Cthird+1)*R^4/(Lunit^2*N^2*(Uref:ℝ))+
      (4*Dlower*(B+1)*R^4)/(4*N^2*(Uref:ℝ))
    ((∀ t∈Translations, Mat t 0=1 ∧ Mat t 2=0 ∧ Mat t 3=1 ∧ Mat t 1=t) →
      (∑ t∈Translations, ∑ ab∈Gaps t, ((S t ab).card:ℝ)) ≤ 4*(m0:ℝ)*(3*Aupper^((3:ℝ)⁻¹)*(Dtranslation+2)^((2:ℝ)/3)+
        2*Bupper*(3+2*Real.log (Dtranslation+2))+(1/2:ℝ)*(2*Dtranslation+1))) ∧
    ((∀ t∈Translations, Mat t 0=1 ∧ Mat t 1=0 ∧ Mat t 3=1 ∧ Mat t 2=t) →
      (∑ t∈Translations, ∑ ab∈Gaps t, ((S t ab).card:ℝ)) ≤ 4*(m0:ℝ)*(3*Alower^((3:ℝ)⁻¹)*(Dtranslation+2)^((2:ℝ)/3)+
        2*Blower*(3+2*Real.log (Dtranslation+2))+(1/2:ℝ)*(2*Dtranslation+1))) := by
  pm_2479 hmassFn positive_difference_actual_fourier_charted_triangular_colored_sample_mass
  pm_2478
  intro Fsrc η ya yb Tsrc E Dtranslation Translations chartKey Uref Refs Gaps Bselect
    Bmajor Cmajor S Q K₀ inst rat vinv parity anchor Mat e r v s
    σ δ T M N R base Bcut lambda Uband θ A W x
    hη hηsmall hya hyb hreg hjets htests hTsrc hMtwo hsourceScale hDtranslation hTranslations
    yp F chartColor hchartColor
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hgap
    Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor f hlevel
    q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Blabels m0 hBmajor hCmajor Lunit Gamma Cthird Aupper Bupper Alower Blower
  have hper t (ht : t∈Translations) :
    ((Mat t 0=1 ∧ Mat t 2=0 ∧ Mat t 3=1) → Mat t 1≠0 →
      (∑ ab∈Gaps t, ((S t ab).card:ℝ)) ≤ 4*(m0:ℝ)*
        ((2*CU*(Cthird+1)*E^2*M^2/(κ*Lunit^3*N^4*|(Mat t 1:ℝ)|))^((3:ℝ)⁻¹)+
          CU*(Cthird+1)*E^2*M^2/(Lunit^2*N^4*|(Mat t 1:ℝ)| *(Uref:ℝ)))+
        (m0:ℝ)*(DU*(B+1)*E^2*M^2/(N^4*|(Mat t 1:ℝ)| *(Uref:ℝ))+2)) ∧
    ((Mat t 0=1 ∧ Mat t 1=0 ∧ Mat t 3=1) → Mat t 2≠0 →
      (∑ ab∈Gaps t, ((S t ab).card:ℝ)) ≤ 4*(m0:ℝ)*
        ((8*CL*(Cthird+1)*R^4/(κ*Lunit^3*N^2*|(Mat t 2:ℝ)|))^((3:ℝ)⁻¹)+
          4*CL*(Cthird+1)*R^4/(Lunit^2*N^2*|(Mat t 2:ℝ)| *(Uref:ℝ)))+
        (m0:ℝ)*(4*DL*(B+1)*R^4/(N^2*|(Mat t 2:ℝ)| *(Uref:ℝ))+2)) := by
    exact hmassFn Fsrc η ya yb Tsrc E (chartKey t) Uref Refs (Gaps t)
      (Bselect:=Bselect) Bmajor Cmajor (S t) Q K₀ (rat t) (vinv t) (parity t) (anchor t)
      (Mat t) (e t) (r t) (v t) (s t)
      (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (Bcut:=Bcut)
      (lambda:=lambda) (Uband:=Uband) (θ:=θ) A (W:=W) (x:=x t)
      hη hηsmall hya hyb hreg hjets htests hTsrc hMtwo hsourceScale (hchartColor t ht)
      hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW (hx t ht) (hwindow t ht) (hden t ht) hlambda hUband hθ hθmax (hcurv t ht) (hinv t ht) (hchart t ht) (horientation t ht) hBcut (hs t ht) (hrefSet t ht) (hparentSet t ht) hsep (hwideL t ht) (hwideU t ht) hUref hBselectSize hcutMargin hselectedWrap (hreferenceDen t ht) (hgapWidth t ht) hRQ hselectedUpper hscaleTen (hfamilyGap t ht) (hgap t ht)
      (hsourceColor t ht) (hlevel t ht) (hcolor t ht) (hnear t ht) hsmall hNR hRN hNcube hminscale (hMatdet t ht) (hMatt t ht) (hMatmap t ht) (hMatgamma t ht) hNtwo (hL t ht) (hU t ht) (hanchor t ht) (hcut t ht) (hcount t ht) hsize hD hΔ hBsize (hBmajor t ht) (hCmajor t ht)
  pm_1689
  pm_2480
  pm_1693
  have hδ0 := approximateModelPhase_tolerance_nonneg (hF 0)
  obtain ⟨hB,hCthird⟩ := physical_source_triangular_constants_nonneg hσ hδ0
  have hthird1 : 0 ≤ Cthird+1 := add_nonneg hCthird zero_le_one
  have hB1 : 0 ≤ B+1 := add_nonneg hB zero_le_one
  pm_6107 hnumU CU Cthird hCU.le hthird1
  pm_6107 hnumDU DU B hDU.le hB1
  pm_6540 hnumL CL Cthird hCL.le hthird1
  pm_6540 hnumDL DL B hDL.le hB1
  pm_5897 hAU Aupper hnumU hBU Bupper hnumDU
  pm_5897 hAL Alower hnumL hBL Blower hnumDL
  constructor
  · intro htri
    have hweight t (ht : t∈Translations) :
        (∑ ab∈Gaps t, ((S t ab).card:ℝ)) ≤
          4*(m0:ℝ)*((Aupper/|(t:ℝ)|)^((3:ℝ)⁻¹)+Bupper/|(t:ℝ)|+1/2) := by
      have hsides := htri t ht
      have hentry : Mat t 1≠0 := by rw [hsides.2.2.2]; exact (hTranslations t ht).1
      have hh := (hper t ht).1 ⟨hsides.1,hsides.2.1,hsides.2.2.1⟩ hentry
      rw [hsides.2.2.2] at hh
      exact hh.trans_eq (triangular_weight_normalize (m0:ℝ)
        (2*CU*(Cthird+1)*E^2*M^2) (CU*(Cthird+1)*E^2*M^2) (DU*(B+1)*E^2*M^2) (κ*Lunit^3*N^4)
        (Lunit^2*N^4) (N^4) (Uref:ℝ) |(t:ℝ)|)
    pm_2481 Aupper Bupper hAU hBU
  · intro htri
    have hweight t (ht : t∈Translations) :
        (∑ ab∈Gaps t, ((S t ab).card:ℝ)) ≤
          4*(m0:ℝ)*((Alower/|(t:ℝ)|)^((3:ℝ)⁻¹)+Blower/|(t:ℝ)|+1/2) := by
      have hsides := htri t ht
      have hentry : Mat t 2≠0 := by rw [hsides.2.2.2]; exact (hTranslations t ht).1
      have hh := (hper t ht).2 ⟨hsides.1,hsides.2.1,hsides.2.2.1⟩ hentry
      rw [hsides.2.2.2] at hh
      exact hh.trans_eq (triangular_weight_normalize (m0:ℝ)
        (8*CL*(Cthird+1)*R^4) (4*CL*(Cthird+1)*R^4) (4*DL*(B+1)*R^4) (κ*Lunit^3*N^2)
        (Lunit^2*N^2) (N^2) (Uref:ℝ) |(t:ℝ)|)
    pm_2481 Alower Blower hAL hBL


private theorem rational_narrow_triangular_translation_bounds
    (p : Fin 2 → ℚ) (Mat : Fin 4 → ℤ) (Q : ℕ)
    {lambda U θ : ℝ} (hQ : 0 < Q) (hlambda : 0 < lambda)
    (hU : 0 ≤ U) (hθ : 0 < θ)
    (hcurv : ∀ i, lambda ≤ |(p i:ℝ)| ∧ |(p i:ℝ)| ≤ U)
    (hden : ∀ i, (p i).den ≤ Q ∧ Q ≤ 2*(p i).den)
    (hcolor : (⌊((p 0).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((p 0).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)=
      (⌊((p 1).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((p 1).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋))
    (hdenmap : (Mat 2:ℝ)*(p 0:ℝ)+Mat 3=((p 1).den:ℝ)/(p 0).den)
    (hmap : ((Mat 0:ℝ)*(p 0:ℝ)+Mat 1)/((Mat 2:ℝ)*(p 0:ℝ)+Mat 3)=(p 1:ℝ)) :
    ((Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) → |(Mat 1:ℝ)| ≤ θ*U) ∧
    ((Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) → |(Mat 2:ℝ)| ≤ θ/lambda) := by
  have hb := (rational_narrow_band_partition (Finset.univ : Finset (Fin 2)) p Q
    hQ hlambda hU hθ (fun i _ => hcurv i) (fun i _ => hden i)).2
    0 (Finset.mem_univ 0) 1 (Finset.mem_univ 1) hcolor
  have hxabs : 0 < |(p 0:ℝ)| := hlambda.trans_le (hcurv 0).1
  have hx : (p 0:ℝ)≠0 := abs_pos.mp hxabs
  have hdpos : (0:ℝ) < (Mat 2:ℝ)*(p 0:ℝ)+Mat 3 := by
    rw [hdenmap]
    exact div_pos (by exact_mod_cast (p 1).pos) (by exact_mod_cast (p 0).pos)
  have hnumeq : ((Mat 0:ℝ)*(p 0:ℝ)+Mat 1)/(p 0:ℝ)=
      ((p 1).num:ℝ)/(p 0).num := by
    pm_8478 hdpos.ne' hdenmap
  constructor
  · intro htri
    have hh := hb.2
    rw [←hnumeq,htri.1,Int.cast_one,one_mul] at hh
    have he : ((p 0:ℝ)+Mat 1)/(p 0:ℝ)-1=(Mat 1:ℝ)/(p 0:ℝ) := by
      field_simp
      ring
    rw [he,abs_div] at hh
    exact ((div_le_iff₀ hxabs).mp hh).trans
      (mul_le_mul_of_nonneg_left (hcurv 0).2 hθ.le)
  · intro htri
    have hh := hb.1
    rw [←hdenmap,htri.2.2,Int.cast_one,add_sub_cancel_right,abs_mul] at hh
    apply (le_div_iff₀ hlambda).mpr
    exact (mul_le_mul_of_nonneg_left (hcurv 0).1 (abs_nonneg _)).trans hh

                                                                
                                                                         
                                                                       
theorem positive_difference_actual_fourier_charted_triangular_source_cutoff_sample_mass
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower Dupper Dlower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧
    ∀ (Fsrc : ℝ → ℝ) (η ya yb Tsrc E : ℝ)
    (Translations : Finset ℤ) (chartKey : ℤ → ℤ × ℤ × ℤ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : ℤ → Finset (ℝ × ℝ)) {Bselect : ℝ}
    (Bmajor Cmajor : ℕ)
    (S : ℤ → ℝ × ℝ → Finset ℕ) (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℤ → ℝ × ℝ → ℕ → Fin 2 → ℚ) (vinv : ℤ → ℝ × ℝ → ℕ → Fin 2 → ℤ)
    (parity : ℤ → ℝ × ℝ → ℕ → Fin 2 → Fin 2) (anchor : ℤ → ℝ × ℝ → ℕ → ℚ)
    (Mat : ℤ → Fin 4 → ℤ) (e r v s : ℤ → ℝ × ℝ → ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ}
    {x : ℤ → ℝ × ℝ → ℕ → Fin 2 → ℝ},
    0 < η → η ≤ η₀ →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    (∀ t∈Translations, t≠0) →
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let chartColor := fun (t : ℤ) ab j i =>
      (⌊yp i/a⌋,⌊((2*M^2/Tsrc)*(rat t ab j i:ℝ))/a⌋,
        ⌊((Tsrc/(2*M^2))*(rat t ab j i:ℝ)⁻¹)/a⌋)
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈S t ab, ∀ i, chartColor t ab j i=chartKey t) →
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*N*R^2=M^3) →
    ((Q:ℝ)*N ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, (x t ab) j i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), (x t ab) j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1))) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, ((rat t ab) j i).den ≤ Q ∧ Q ≤ 2*((rat t ab) j i).den) →
    (0 < lambda) →
    (0 ≤ Uband) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, lambda ≤ |((rat t ab) j i:ℝ)| ∧ |((rat t ab) j i:ℝ)| ≤ Uband) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, (((rat t ab) j i).den:ℤ) ∣ ((rat t ab) j i).num*(vinv t ab) j i-1) →
    (∀ t∈Translations, ∀ ab∈Gaps t, (v t ab)*(r t ab)-(e t ab)*(s t ab)=1) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ((0:ℝ) < (r t ab) ∧ ((e t ab):ℝ)/(r t ab)=ab.1) ∨
      (((r t ab):ℝ) < 0 ∧ ((e t ab):ℝ)/(r t ab)=ab.2)) →
    (0 < Bcut) →
    (∀ t∈Translations, ∀ ab∈Gaps t, (s t ab) ≠ 0) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ((e t ab):ℝ)/(r t ab)∈Refs) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ((v t ab):ℝ)/(s t ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, (x t ab) j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, (x t ab) j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2) →
    (∀ t∈Translations, ∀ ab∈Gaps t, R^2 ≤ ((r t ab):ℝ)^2*(Uref:ℝ)) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    (N^10 ≤ M^3*R^7) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ((rat t ab) j 0:ℝ)∈Icc ab.1 ab.2) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (t : ℤ) (ab : ℝ × ℝ) => 1+(|((v t ab):ℝ)|+|((s t ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (t : ℤ) (ab : ℝ × ℝ) => 1+(|((r t ab):ℝ)| *Vheight+|((e t ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => (⌊(((rat t ab) j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊(((rat t ab) j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), (sourceColor t ab) j 0=(sourceColor t ab) j 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, iteratedDeriv 2 (f i) ((x t ab) j i)/2=((rat t ab) j i:ℝ)) →
    let q := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => ((rat t ab) j i).den
    let mu := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => iteratedDeriv 3 (f i) (round ((x t ab) j i))/6
    let ell := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => deriv (f i) (round ((x t ab) j i))
    let b := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => (⌊((q t ab) j i:ℝ)*(ell t ab) j i⌋+((parity t ab) j i:ℕ) : ℤ)
    let cround := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => round (((q t ab) j i:ℝ)*(ell t ab) j i)
    let tau := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => (((b t ab) j i:ℝ)-((q t ab) j i:ℝ)*(ell t ab) j i)/2
    let dual := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => -2*(mu t ab) j i*(Real.sqrt (2/(3*(mu t ab) j i*((q t ab) j i:ℝ))))^3
    let cloud := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => (![Int.fract (-((vinv t ab) j i:ℝ)*(b t ab) j i/(q t ab) j i),
      Int.fract (-((vinv t ab) j i:ℝ)/(q t ab) j i),(dual t ab) j i/Real.sqrt K₀,
      (3*(dual t ab) j i*(tau t ab) j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), (b t ab) j 0-(cround t ab) j 0=(b t ab) j 1-(cround t ab) j 1) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ a, |(cloud t ab) j 0 a-(cloud t ab) j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 →
    N ≤ R^2 →
    R ≤ N →
    N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    (∀ t∈Translations, Mat t 0*Mat t 3-Mat t 1*Mat t 2=1) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), (Mat t 2:ℝ)*((rat t ab) j 0:ℝ)+Mat t 3=((q t ab) j 1:ℝ)/(q t ab) j 0) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ((Mat t 0:ℝ)*((rat t ab) j 0:ℝ)+Mat t 1)/
      ((Mat t 2:ℝ)*((rat t ab) j 0:ℝ)+Mat t 3)=((rat t ab) j 1:ℝ)) →
    (∀ t∈Translations, |(Mat t 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, (x t ab) j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, (x t ab) j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), |((anchor t ab) j:ℝ)-((rat t ab) j 0:ℝ)| ≤ ε) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), 256*(((anchor t ab) j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), 256 ≤ (2*ε)*((Q:ℝ)/3)*((anchor t ab) j).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Blabels := fun (t : ℤ) ab => 6+216*(⌊Real.logb 2 (P₁ t ab*P₂ t ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ t∈Translations, ∀ ab∈Gaps t, Blabels t ab ≤ Bmajor) →
    (∀ t∈Translations, ∀ ab∈Gaps t, Ccharts ab ≤ Cmajor) →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Aupper := 2*Cupper*(Cthird+1)*E^2*M^2/(κ*Lunit^3*N^4)
    let Bupper := Cupper*(Cthird+1)*E^2*M^2/(Lunit^2*N^4*(Uref:ℝ))+
      Dupper*(B+1)*E^2*M^2/(4*N^4*(Uref:ℝ))
    let Alower := 8*Clower*(Cthird+1)*R^4/(κ*Lunit^3*N^2)
    let Blower := 4*Clower*(Cthird+1)*R^4/(Lunit^2*N^2*(Uref:ℝ))+
      (4*Dlower*(B+1)*R^4)/(4*N^2*(Uref:ℝ))
    let DupperCut := θ*Uband
    let DlowerCut := θ/lambda
    ((∀ t∈Translations, Mat t 0=1 ∧ Mat t 2=0 ∧ Mat t 3=1 ∧ Mat t 1=t) →
      (∑ t∈Translations, ∑ ab∈Gaps t, ((S t ab).card:ℝ)) ≤ 4*(m0:ℝ)*(3*Aupper^((3:ℝ)⁻¹)*(DupperCut+2)^((2:ℝ)/3)+
        2*Bupper*(3+2*Real.log (DupperCut+2))+(1/2:ℝ)*(2*DupperCut+1))) ∧
    ((∀ t∈Translations, Mat t 0=1 ∧ Mat t 1=0 ∧ Mat t 3=1 ∧ Mat t 2=t) →
      (∑ t∈Translations, ∑ ab∈Gaps t, ((S t ab).card:ℝ)) ≤ 4*(m0:ℝ)*(3*Alower^((3:ℝ)⁻¹)*(DlowerCut+2)^((2:ℝ)/3)+
        2*Blower*(3+2*Real.log (DlowerCut+2))+(1/2:ℝ)*(2*DlowerCut+1))) := by
  pm_2479 hmassFn positive_difference_actual_fourier_charted_triangular_translation_sample_mass
  pm_2478
  intro Fsrc η ya yb Tsrc E Translations chartKey Uref Refs Gaps Bselect
    Bmajor Cmajor S Q K₀ inst rat vinv parity anchor Mat e r v s
    σ δ T M N R base Bcut lambda Uband θ A W x
    hη hηsmall hya hyb hreg hjets htests hTsrc hMtwo hsourceScale hTranslations
    yp F chartColor hchartColor
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hgap
    Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor f hlevel
    q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Blabels m0 hBmajor hCmajor Lunit Gamma Cthird Aupper Bupper Alower Blower DupperCut DlowerCut
  let Occupied := Translations.filter (fun t => ∃ ab∈Gaps t, (S t ab).Nonempty)
  have hinOcc : Occupied ⊆ Translations := Finset.filter_subset _ _
  have hsum : (∑ t∈Translations, ∑ ab∈Gaps t, ((S t ab).card:ℝ)) =
      ∑ t∈Occupied, ∑ ab∈Gaps t, ((S t ab).card:ℝ) := by
    symm
    apply Finset.sum_subset hinOcc
    intro t ht hnot
    apply Finset.sum_eq_zero
    intro ab hab
    have he : ¬(S t ab).Nonempty := by
      pm_8846 hh ht
    simp only [Finset.not_nonempty_iff_eq_empty.mp he,Finset.card_empty,Nat.cast_zero]
  have hcuts t (ht : t∈Occupied) :
      ((Mat t 0=1 ∧ Mat t 2=0 ∧ Mat t 3=1) → |(Mat t 1:ℝ)| ≤ DupperCut) ∧
      ((Mat t 0=1 ∧ Mat t 1=0 ∧ Mat t 3=1) → |(Mat t 2:ℝ)| ≤ DlowerCut) := by
    obtain ⟨ab,hab,j,hj⟩ := (Finset.mem_filter.mp ht).2
    exact rational_narrow_triangular_translation_bounds (rat t ab j) (Mat t) Q
      hQ hlambda hUband hθ (hcurv t (hinOcc ht) ab hab j hj)
      (hden t (hinOcc ht) ab hab j hj) (hsourceColor t (hinOcc ht) ab hab j hj)
      (hMatt t (hinOcc ht) ab hab j hj) (hMatmap t (hinOcc ht) ab hab j hj)
  have hbound (Dlim : ℝ) (hDlim : 0 ≤ Dlim)
      (hcutoff : ∀ t∈Occupied, |(t:ℝ)| ≤ Dlim) :
    ((∀ t∈Occupied, Mat t 0=1 ∧ Mat t 2=0 ∧ Mat t 3=1 ∧ Mat t 1=t) →
      (∑ t∈Occupied, ∑ ab∈Gaps t, ((S t ab).card:ℝ)) ≤ 4*(m0:ℝ)*(3*Aupper^((3:ℝ)⁻¹)*(Dlim+2)^((2:ℝ)/3)+
        2*Bupper*(3+2*Real.log (Dlim+2))+(1/2:ℝ)*(2*Dlim+1))) ∧
    ((∀ t∈Occupied, Mat t 0=1 ∧ Mat t 1=0 ∧ Mat t 3=1 ∧ Mat t 2=t) →
      (∑ t∈Occupied, ∑ ab∈Gaps t, ((S t ab).card:ℝ)) ≤ 4*(m0:ℝ)*(3*Alower^((3:ℝ)⁻¹)*(Dlim+2)^((2:ℝ)/3)+
        2*Blower*(3+2*Real.log (Dlim+2))+(1/2:ℝ)*(2*Dlim+1))) := by
    exact hmassFn Fsrc η ya yb Tsrc E Dlim Occupied chartKey Uref Refs Gaps
      (Bselect:=Bselect) Bmajor Cmajor S Q K₀ rat vinv parity anchor Mat e r v s
      (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (Bcut:=Bcut)
      (lambda:=lambda) (Uband:=Uband) (θ:=θ) A (W:=W) (x:=x)
      hη hηsmall hya hyb hreg hjets htests hTsrc hMtwo hsourceScale hDlim
      (fun t ht => ⟨hTranslations t (hinOcc ht),hcutoff t ht⟩) (fun t ht => hchartColor t (hinOcc ht))
      hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW (fun t ht => hx t (hinOcc ht)) (fun t ht => hwindow t (hinOcc ht)) (fun t ht => hden t (hinOcc ht)) hlambda hUband hθ hθmax (fun t ht => hcurv t (hinOcc ht)) (fun t ht => hinv t (hinOcc ht)) (fun t ht => hchart t (hinOcc ht)) (fun t ht => horientation t (hinOcc ht)) hBcut (fun t ht => hs t (hinOcc ht)) (fun t ht => hrefSet t (hinOcc ht)) (fun t ht => hparentSet t (hinOcc ht)) hsep (fun t ht => hwideL t (hinOcc ht)) (fun t ht => hwideU t (hinOcc ht)) hUref hBselectSize hcutMargin hselectedWrap (fun t ht => hreferenceDen t (hinOcc ht)) (fun t ht => hgapWidth t (hinOcc ht)) hRQ hselectedUpper hscaleTen (fun t ht => hfamilyGap t (hinOcc ht)) (fun t ht => hgap t (hinOcc ht))
      (fun t ht => hsourceColor t (hinOcc ht)) (fun t ht => hlevel t (hinOcc ht)) (fun t ht => hcolor t (hinOcc ht)) (fun t ht => hnear t (hinOcc ht)) hsmall hNR hRN hNcube hminscale (fun t ht => hMatdet t (hinOcc ht)) (fun t ht => hMatt t (hinOcc ht)) (fun t ht => hMatmap t (hinOcc ht)) (fun t ht => hMatgamma t (hinOcc ht)) hNtwo (fun t ht => hL t (hinOcc ht)) (fun t ht => hU t (hinOcc ht)) (fun t ht => hanchor t (hinOcc ht)) (fun t ht => hcut t (hinOcc ht)) (fun t ht => hcount t (hinOcc ht)) hsize hD hΔ hBsize (fun t ht => hBmajor t (hinOcc ht)) (fun t ht => hCmajor t (hinOcc ht))
  constructor
  · intro htri
    have hrange : ∀ t∈Occupied, |(t:ℝ)| ≤ DupperCut := by
      intro t ht
      have hsides := htri t (hinOcc ht)
      have hh := (hcuts t ht).1 ⟨hsides.1,hsides.2.1,hsides.2.2.1⟩
      simpa only [hsides.2.2.2] using hh
    rw [hsum]
    exact (hbound DupperCut (mul_nonneg hθ.le hUband) hrange).1
      (fun t ht => htri t (hinOcc ht))
  · intro htri
    have hrange : ∀ t∈Occupied, |(t:ℝ)| ≤ DlowerCut := by
      intro t ht
      have hsides := htri t (hinOcc ht)
      have hh := (hcuts t ht).2 ⟨hsides.1,hsides.2.1,hsides.2.2.1⟩
      simpa only [hsides.2.2.2] using hh
    rw [hsum]
    exact (hbound DlowerCut (div_nonneg hθ.le hlambda.le) hrange).2
      (fun t ht => htri t (hinOcc ht))

theorem physicalModelPhase_reference_translation_window_selection
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2)))
    (entry : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℤ)
    (Mat : ℤ → Fin 4 → ℤ) (hMat : Function.Injective Mat)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ)
    (F : Fin 2 → ℝ → ℝ) (A Wlim : Fin 2 → ℝ) (za zb : ℤ → ℝ) (AlenA Alen : ℤ → ℕ)
    (N : ℕ) (Za Z : ℤ) (W : ℝ)
    {σ δ T M : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+Wlim i ≤ 2*M)
    (hbase : ∀ ij∈P, W ≤ za ij.1.1)
    (hz : ∀ ij∈P, zb ij.2.1∈Ioo 0 (Wlim 1))
    (hgeometryA : ∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ))
    (hgeometry : ∀ ij∈P, N ≤ Alen ij.2.1 ∧ Alen ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(Alen ij.2.1:ℤ)=Z+(N:ℤ)*ij.2.1+2*(N:ℤ)) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    (∀ ij∈P, ((Mat (entry ij) 0:ℝ)*h 0 (za ij.1.1)+Mat (entry ij) 1)/
      ((Mat (entry ij) 2:ℝ)*h 0 (za ij.1.1)+Mat (entry ij) 3)=h 1 (zb ij.2.1)) →
    let block := fun ij : (ℤ × Fin 2) × (ℤ × Fin 2) =>
      ⌊(za ij.1.1-W)/(N:ℝ)⌋.toNat
    let S := fun t ab => (P.filter (fun ij => entry ij=t ∧ gap ij=ab)).image block
    ∃ pick : ℤ → ℝ × ℝ → ℕ → (ℤ × Fin 2) × (ℤ × Fin 2),
      (∀ t∈P.image entry, ∀ ab∈P.image gap, ∀ j∈S t ab,
        pick t ab j∈P ∧ entry (pick t ab j)=t ∧ gap (pick t ab j)=ab ∧
        block (pick t ab j)=j ∧
        za (pick t ab j).1.1∈Icc (W+(N:ℝ)*j) (W+(N:ℝ)*((j:ℝ)+1))) ∧
      P.card ≤ 60*∑ t∈P.image entry, ∑ ab∈P.image gap, (S t ab).card := by
  classical
  intro f h hmap block S
  obtain ⟨pickM,hpick,hcard⟩ := physicalModelPhase_reference_matrix_window_selection
    P (fun ij => Mat (entry ij)) gap F A Wlim za zb AlenA Alen N Za Z W
    hσ hδ hF hT hM hN hA hW hbase hz hgeometryA hgeometry hmap
  have hS t ab : (P.filter (fun ij => Mat (entry ij)=Mat t ∧ gap ij=ab)).image block=S t ab := by
    simp only [S,hMat.eq_iff]
  have himage : P.image (fun ij => Mat (entry ij))=(P.image entry).image Mat := by
    simp only [Finset.image_image,Function.comp_def]
  refine ⟨fun t ab j => pickM (Mat t) ab j,?_,?_⟩
  · intro t ht ab hab j hj
    have hmt : Mat t∈P.image (fun ij => Mat (entry ij)) := by
      rw [himage]
      exact Finset.mem_image_of_mem Mat ht
    have hj' : j∈(P.filter (fun ij => Mat (entry ij)=Mat t ∧ gap ij=ab)).image block := by
      rw [hS]
      exact hj
    have hp := hpick (Mat t) hmt ab hab j hj'
    exact ⟨hp.1,hMat hp.2.1,hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2⟩
  · change P.card ≤ 60*∑ m∈P.image (fun ij => Mat (entry ij)), ∑ ab∈P.image gap,
        ((P.filter (fun ij => Mat (entry ij)=m ∧ gap ij=ab)).image block).card at hcard
    rw [himage,Finset.sum_image (fun _ _ _ _ he => hMat he)] at hcard
    simpa only [hS] using hcard


                                                                
                                                                       
                                                                       
theorem positive_difference_actual_fourier_triangular_original_pair_mass
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower Dupper Dlower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧
    ∀ (Fsrc : ℝ → ℝ) (η ya yb Tsrc E : ℝ) (chartKey : ℤ → ℤ × ℤ × ℤ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2))) (entry : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℤ)
    (Mat : ℤ → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ) (Bmajor Cmajor : ℕ)
    (N : ℕ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ) (Za Zb : ℤ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℚ) (vinv : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℤ)
    (parity : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → Fin 2) (anchor : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M R base Bcut lambda Uband θ : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ} {x : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℝ},
    Function.Injective Mat →
    0 < η → η ≤ η₀ →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    (∀ ij∈P, entry ij≠0) →
    (∀ ij∈P, base ≤ za ij.1.1) →
    (∀ ij∈P, x ij 0=za ij.1.1) →
    (∀ ij∈P, x ij 1=zb ij.2.1) →
    (∀ ij∈P, gap ij∈Gaps) →
    (∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ)) →
    (∀ ij∈P, N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(AlenB ij.2.1:ℤ)=Zb+(N:ℤ)*ij.2.1+2*(N:ℤ)) →
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let chartColor := fun ij i =>
      (⌊yp i/a⌋,⌊((2*M^2/Tsrc)*(rat ij i:ℝ))/a⌋,
        ⌊((Tsrc/(2*M^2))*(rat ij i:ℝ)⁻¹)/a⌋)
    (∀ ij∈P, ∀ i, chartColor ij i=chartKey (entry ij)) →
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < (N:ℝ)) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*(N:ℝ)*R^2=M^3) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ ij∈P, ∀ i, x ij i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, (rat ij i).den ≤ Q ∧ Q ≤ 2*(rat ij i).den) →
    (0 < lambda) →
    (0 ≤ Uband) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ ij∈P, ∀ i, lambda ≤ |(rat ij i:ℝ)| ∧ |(rat ij i:ℝ)| ≤ Uband) →
    (∀ ij∈P, ∀ i, ((rat ij i).den:ℤ) ∣ (rat ij i).num*vinv ij i-1) →
    (∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) →
    (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ ij∈P, ∀ i, x ij i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, x ij i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (∀ ij∈P, (rat ij 0:ℝ)∈Icc (gap ij).1 (gap ij).2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (ab : ℝ × ℝ) => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (ab : ℝ × ℝ) => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun ij i => (⌊((rat ij i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((rat ij i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ij∈P, sourceColor ij 0=sourceColor ij 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ij∈P, ∀ i, iteratedDeriv 2 (f i) (x ij i)/2=(rat ij i:ℝ)) →
    let q := fun ij i => (rat ij i).den
    let mu := fun ij i => iteratedDeriv 3 (f i) (round (x ij i))/6
    let ell := fun ij i => deriv (f i) (round (x ij i))
    let b := fun ij i => (⌊(q ij i:ℝ)*ell ij i⌋+(parity ij i:ℕ) : ℤ)
    let cround := fun ij i => round ((q ij i:ℝ)*ell ij i)
    let tau := fun ij i => ((b ij i:ℝ)-(q ij i:ℝ)*ell ij i)/2
    let dual := fun ij i => -2*mu ij i*(Real.sqrt (2/(3*mu ij i*(q ij i:ℝ))))^3
    let cloud := fun ij i => (![Int.fract (-(vinv ij i:ℝ)*b ij i/q ij i),
      Int.fract (-(vinv ij i:ℝ)/q ij i),dual ij i/Real.sqrt K₀,
      (3*dual ij i*tau ij i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ij∈P, b ij 0-cround ij 0=b ij 1-cround ij 1) →
    (∀ ij∈P, ∀ a, |cloud ij 0 a-cloud ij 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 →
    R ≤ (N:ℝ) →
    (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    (∀ t∈P.image entry, Mat t 0*Mat t 3-Mat t 1*Mat t 2=1) →
    (∀ ij∈P, (Mat (entry ij) 2:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 3=(q ij 1:ℝ)/q ij 0) →
    (∀ ij∈P, ((Mat (entry ij) 0:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 1)/
      ((Mat (entry ij) 2:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 3)=(rat ij 1:ℝ)) →
    (∀ t∈P.image entry, |(Mat t 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ ij∈P, ∀ i, x ij i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, x ij i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, |(anchor ij:ℝ)-(rat ij 0:ℝ)| ≤ ε) →
    (∀ ij∈P, 256*((anchor ij).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ij∈P, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor ij).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Blabels := fun ab => 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ ab∈Gaps, Blabels ab ≤ Bmajor) →
    (∀ ab∈Gaps, Ccharts ab ≤ Cmajor) →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Aupper := 2*Cupper*(Cthird+1)*E^2*M^2/(κ*Lunit^3*(N:ℝ)^4)
    let Bupper := Cupper*(Cthird+1)*E^2*M^2/(Lunit^2*(N:ℝ)^4*(Uref:ℝ))+
      Dupper*(B+1)*E^2*M^2/(4*(N:ℝ)^4*(Uref:ℝ))
    let Alower := 8*Clower*(Cthird+1)*R^4/(κ*Lunit^3*(N:ℝ)^2)
    let Blower := 4*Clower*(Cthird+1)*R^4/(Lunit^2*(N:ℝ)^2*(Uref:ℝ))+
      (4*Dlower*(B+1)*R^4)/(4*(N:ℝ)^2*(Uref:ℝ))
    let DupperCut := θ*Uband
    let DlowerCut := θ/lambda
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 2=0 ∧ Mat t 3=1 ∧ Mat t 1=t) →
      (P.card:ℝ) ≤ 60*(4*(m0:ℝ)*(3*Aupper^((3:ℝ)⁻¹)*(DupperCut+2)^((2:ℝ)/3)+
        2*Bupper*(3+2*Real.log (DupperCut+2))+(1/2:ℝ)*(2*DupperCut+1)))) ∧
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 1=0 ∧ Mat t 3=1 ∧ Mat t 2=t) →
      (P.card:ℝ) ≤ 60*(4*(m0:ℝ)*(3*Alower^((3:ℝ)⁻¹)*(DlowerCut+2)^((2:ℝ)/3)+
        2*Blower*(3+2*Real.log (DlowerCut+2))+(1/2:ℝ)*(2*DlowerCut+1)))) := by
  pm_2479 hmassFn positive_difference_actual_fourier_charted_triangular_source_cutoff_sample_mass
  pm_2478
  intro Fsrc η ya yb Tsrc E chartKey Uref Refs Gaps Bselect P entry Mat gap
    Bmajor Cmajor N za zb AlenA AlenB Za Zb Q K₀ inst rat vinv parity anchor e r v s
    σ δ T M R base Bcut lambda Uband θ A W x
    hMat hη hηsmall hya hyb hreg hjets htests hTsrc hMtwo hsourceScale hentry hbase hxa hxb hgapMem hgeometryA hgeometryB
    yp F chartColor hchartColor
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hgap
    Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor f hlevel
    q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Blabels m0 hBmajor hCmajor Lunit Gamma Cthird Aupper Bupper Alower Blower DupperCut DlowerCut
  have hNnat : 0 < N := by exact_mod_cast hN
  pm_1776
  pm_1717
  have hmodelMap ij (hij : ij∈P) :
      ((Mat (entry ij) 0:ℝ)*(iteratedDeriv 2 (f 0) (za ij.1.1)/2)+Mat (entry ij) 1)/
      ((Mat (entry ij) 2:ℝ)*(iteratedDeriv 2 (f 0) (za ij.1.1)/2)+Mat (entry ij) 3)=
        iteratedDeriv 2 (f 1) (zb ij.2.1)/2 := by
    pm_1005
  pm_1718
  pm_6352 t entry
  obtain ⟨pick,hpick,hpairNat⟩ := physicalModelPhase_reference_translation_window_selection
    P entry Mat hMat gap F (fun i => (A i:ℝ)) W za zb AlenA AlenB N Za Zb base
    hσ hδ hF₂ hT hM hNnat hA hW hbase hz hgeometryA hgeometryB hmodelMap
  have hdata t (ht : t∈P.image entry) ab (_hab : ab∈Gaps) j (hj : j∈S t ab) :
      pick t ab j∈P ∧ entry (pick t ab j)=t ∧ gap (pick t ab j)=ab ∧
        block (pick t ab j)=j ∧
        za (pick t ab j).1.1∈Icc (base+(N:ℝ)*j) (base+(N:ℝ)*((j:ℝ)+1)) := by
    pm_1719
    exact hpick t ht ab hab' j hj
  have hgapSub : P.image gap ⊆ Gaps := by
    pm_2532 ab hab ij hij
    exact hgapMem ij hij
  have hpairNat' : P.card ≤ 60*∑ t∈P.image entry, ∑ ab∈Gaps, (S t ab).card := by
    apply hpairNat.trans
    apply Nat.mul_le_mul_left 60
    apply Finset.sum_le_sum
    intro t _
    pm_7739
  have hpair : (P.card:ℝ) ≤ 60*(∑ t∈P.image entry, ∑ ab∈Gaps, ((S t ab).card:ℝ)) := by
    exact_mod_cast hpairNat'
  have hmass :
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 2=0 ∧ Mat t 3=1 ∧ Mat t 1=t) →
      (∑ t∈P.image entry, ∑ ab∈Gaps, ((S t ab).card:ℝ)) ≤ 4*(m0:ℝ)*(3*Aupper^((3:ℝ)⁻¹)*(DupperCut+2)^((2:ℝ)/3)+
        2*Bupper*(3+2*Real.log (DupperCut+2))+(1/2:ℝ)*(2*DupperCut+1))) ∧
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 1=0 ∧ Mat t 3=1 ∧ Mat t 2=t) →
      (∑ t∈P.image entry, ∑ ab∈Gaps, ((S t ab).card:ℝ)) ≤ 4*(m0:ℝ)*(3*Alower^((3:ℝ)⁻¹)*(DlowerCut+2)^((2:ℝ)/3)+
        2*Blower*(3+2*Real.log (DlowerCut+2))+(1/2:ℝ)*(2*DlowerCut+1))) := by
    exact hmassFn Fsrc η ya yb Tsrc E (P.image entry) chartKey Uref Refs (fun _ => Gaps)
      (Bselect:=Bselect) Bmajor Cmajor S Q K₀
      (fun t ab j => rat (pick t ab j)) (fun t ab j => vinv (pick t ab j))
      (fun t ab j => parity (pick t ab j)) (fun t ab j => anchor (pick t ab j))
      Mat (fun _ => e) (fun _ => r) (fun _ => v) (fun _ => s)
      (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=(N:ℝ)) (R:=R) (base:=base) (Bcut:=Bcut)
      (lambda:=lambda) (Uband:=Uband) (θ:=θ) A (W:=W) (x:=fun t ab j => x (pick t ab j))
      hη hηsmall hya hyb hreg hjets htests hTsrc hMtwo hsourceScale
      (by
        pm_2532 t ht ij hij
        exact hentry ij hij)
      (by
        intro t ht ab hab j hj i
        have hp := hdata t ht ab hab j hj
        have hh := hchartColor _ hp.1 i
        rw [hp.2.1] at hh
        exact hh)
      hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW (fun t ht ab hab j hj => hx _ (hdata t ht ab hab j hj).1)
      (by
        pm_2482
        pm_7392 t
        exact hp.2.2.2.2)
      (fun t ht ab hab j hj => hden _ (hdata t ht ab hab j hj).1) hlambda hUband hθ hθmax (fun t ht ab hab j hj => hcurv _ (hdata t ht ab hab j hj).1) (fun t ht ab hab j hj => hinv _ (hdata t ht ab hab j hj).1) (fun _ _ => hchart) (fun _ _ => horientation) hBcut (fun _ _ => hs) (fun _ _ => hrefSet) (fun _ _ => hparentSet) hsep (fun t ht ab hab j hj => hwideL _ (hdata t ht ab hab j hj).1) (fun t ht ab hab j hj => hwideU _ (hdata t ht ab hab j hj).1) hUref hBselectSize hcutMargin hselectedWrap (fun _ _ => hreferenceDen) (fun _ _ => hgapWidth) hRQ hselectedUpper hscaleTen
      (by
        pm_2482
        pm_7740
        exact hh)
      (fun _ _ => hgap) (fun t ht ab hab j hj => hsourceColor _ (hdata t ht ab hab j hj).1) (fun t ht ab hab j hj => hlevel _ (hdata t ht ab hab j hj).1) (fun t ht ab hab j hj => hcolor _ (hdata t ht ab hab j hj).1) (fun t ht ab hab j hj => hnear _ (hdata t ht ab hab j hj).1) hsmall hNR hRN hNcube hminscale
      hMatdet
      (by
        pm_2482
        pm_1212 hMatt
        exact hh)
      (by
        pm_2482
        pm_1212 hMatmap
        exact hh)
      hMatgamma hNtwo (fun t ht ab hab j hj => hL _ (hdata t ht ab hab j hj).1) (fun t ht ab hab j hj => hU _ (hdata t ht ab hab j hj).1) (fun t ht ab hab j hj => hanchor _ (hdata t ht ab hab j hj).1) (fun t ht ab hab j hj => hcut _ (hdata t ht ab hab j hj).1) (fun t ht ab hab j hj => hcount _ (hdata t ht ab hab j hj).1) hsize hD hΔ hBsize (fun _ _ => hBmajor) (fun _ _ => hCmajor)
  constructor
  · intro htri
    exact hpair.trans (mul_le_mul_of_nonneg_left (hmass.1 htri) (by norm_num : (0:ℝ) ≤ 60))
  · intro htri
    exact hpair.trans (mul_le_mul_of_nonneg_left (hmass.2 htri) (by norm_num : (0:ℝ) ≤ 60))



                                                                  
                                                                   
            
private theorem positive_difference_approximate_model_source_amplitude
    (Fsrc : ℝ → ℝ) {σsrc Usrc η y Tsrc T σ δ : ℝ}
    (hσsrc : 0 < σsrc) (hUsrc : 0 < Usrc)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y∈Icc (1:ℝ) 2)
    (hTsrc : 0 < Tsrc) (hT : 0 < T) (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w)
    (hjets : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) :
    let F := fun u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*y))/(σsrc*η)
    Expdb.IsApproximateModelPhaseFunction F σ 2 δ →
      modelPhaseThirdLower σ*σsrc*T/(3*Usrc) ≤ Tsrc := by
  intro F hF
  let G := fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)
  have hFu : F=fun u => (Tsrc/T)*G u := by
    funext u
    dsimp only [F,G]
    ring
  have hd : iteratedDeriv 3 F (3/2)=
      (Tsrc/T)*iteratedDeriv 3 G (3/2) := by
    rw [hFu,iteratedDeriv_const_mul_field]
  have hlow : modelPhaseThirdLower σ ≤ iteratedDeriv 3 F (3/2) := by
    pm_870 hF
  have hu := positive_jets_difference_mixed_upper Fsrc hσsrc hUsrc hη hηmax
    (by norm_num : (3/2:ℝ)∈Icc (3/4:ℝ) (9/4))
    (show y∈Icc (1/2:ℝ) 3 from
      ⟨by linarith only [hy.1],by linarith only [hy.2]⟩)
    hreg hjets 3 0 (by norm_num) (by norm_num)
  simp only [iteratedDeriv_zero] at hu
  have hupper : |iteratedDeriv 3 F (3/2)| ≤ (Tsrc/T)*(3*Usrc/σsrc) := by
    rw [hd,abs_mul,abs_of_pos (div_pos hTsrc hT)]
    exact mul_le_mul_of_nonneg_left hu (div_pos hTsrc hT).le
  have hh := hlow.trans ((le_abs_self _).trans hupper)
  have he : (Tsrc/T)*(3*Usrc/σsrc)=3*Usrc*Tsrc/(σsrc*T) := by ring
  rw [he] at hh
  have hc := (le_div_iff₀ (mul_pos hσsrc hT)).mp hh
  apply (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ) < 3) hUsrc)).mpr
  nlinarith only [hc]

                                                                  
                                                                     
public  theorem positive_difference_model_normalized_curvature_band
    (Fsrc : ℝ → ℝ) {σsrc csrc Usrc η y₀ Tsrc T E M σ δ : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy₀ : y₀∈Icc (1:ℝ) 2)
    (hTsrc : 0 < Tsrc) (hT : 0 < T) (hM : 0 < M) (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1) (hscale : Tsrc ≤ E*T)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w)
    (hjets : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) :
    let F := fun u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*y₀))/(σsrc*η)
    Expdb.IsApproximateModelPhaseFunction F σ 2 δ →
    let f := fun y z => Tsrc*(Fsrc (z/M)-Fsrc (z/M+η*y))/(σsrc*η)
    ∀ y∈Icc (1:ℝ) 2, ∀ z∈Icc M (2*M),
      csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2) ≤
        |iteratedDeriv 2 (f y) z/2| ∧
      |iteratedDeriv 2 (f y) z/2| ≤ (3*Usrc/σsrc)*E*T/(2*M^2) := by
  intro F hF f y hy z hz
  have hsource := positive_difference_approximate_model_source_amplitude Fsrc
    hσsrc hUsrc hη hηmax hy₀ hTsrc hT hσ hδ hreg hjets hF
  have hh := positive_difference_half_curvature_source_bounds Fsrc
    hσsrc hcsrc hUsrc hη hηmax hTsrc hM hy hz hreg hjets htests
  constructor
  · apply le_trans _ hh.1
    calc
      _ = (csrc/(4*σsrc*M^2))*(modelPhaseThirdLower σ*σsrc*T/(3*Usrc)) := by
        field_simp
        ring
      _ ≤ (csrc/(4*σsrc*M^2))*Tsrc :=
        mul_le_mul_of_nonneg_left hsource (by positivity)
      _ = _ := by ring
  · apply hh.2.trans
    simpa only [mul_assoc] using div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hscale (by positivity : (0:ℝ) ≤ 3*Usrc/σsrc))
      (by positivity : (0:ℝ) ≤ 2*M^2)


                                                                  
                                                                      
                                       
theorem positive_difference_actual_fourier_triangular_original_source_mass
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower Dupper Dlower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧
    ∀ (Fsrc : ℝ → ℝ) (η ya yb Tsrc E : ℝ) (chartKey : ℤ → ℤ × ℤ × ℤ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2))) (entry : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℤ)
    (Mat : ℤ → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ) (Bmajor Cmajor : ℕ)
    (N : ℕ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ) (Za Zb : ℤ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℚ) (vinv : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℤ)
    (parity : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → Fin 2) (anchor : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M R base Bcut θ : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ} {x : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℝ},
    Function.Injective Mat →
    0 < η → η ≤ η₀ →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    (∀ ij∈P, entry ij≠0) →
    (∀ ij∈P, base ≤ za ij.1.1) →
    (∀ ij∈P, x ij 0=za ij.1.1) →
    (∀ ij∈P, x ij 1=zb ij.2.1) →
    (∀ ij∈P, gap ij∈Gaps) →
    (∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ)) →
    (∀ ij∈P, N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(AlenB ij.2.1:ℤ)=Zb+(N:ℤ)*ij.2.1+2*(N:ℤ)) →
    let lambda := csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*E*T/(2*M^2)
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let chartColor := fun ij i =>
      (⌊yp i/a⌋,⌊((2*M^2/Tsrc)*(rat ij i:ℝ))/a⌋,
        ⌊((Tsrc/(2*M^2))*(rat ij i:ℝ)⁻¹)/a⌋)
    (∀ ij∈P, ∀ i, chartColor ij i=chartKey (entry ij)) →
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < (N:ℝ)) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*(N:ℝ)*R^2=M^3) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ ij∈P, ∀ i, x ij i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, (rat ij i).den ≤ Q ∧ Q ≤ 2*(rat ij i).den) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ ij∈P, ∀ i, ((rat ij i).den:ℤ) ∣ (rat ij i).num*vinv ij i-1) →
    (∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) →
    (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ ij∈P, ∀ i, x ij i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, x ij i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (∀ ij∈P, (rat ij 0:ℝ)∈Icc (gap ij).1 (gap ij).2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (ab : ℝ × ℝ) => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (ab : ℝ × ℝ) => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun ij i => (⌊((rat ij i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((rat ij i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ij∈P, sourceColor ij 0=sourceColor ij 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ij∈P, ∀ i, iteratedDeriv 2 (f i) (x ij i)/2=(rat ij i:ℝ)) →
    let q := fun ij i => (rat ij i).den
    let mu := fun ij i => iteratedDeriv 3 (f i) (round (x ij i))/6
    let ell := fun ij i => deriv (f i) (round (x ij i))
    let b := fun ij i => (⌊(q ij i:ℝ)*ell ij i⌋+(parity ij i:ℕ) : ℤ)
    let cround := fun ij i => round ((q ij i:ℝ)*ell ij i)
    let tau := fun ij i => ((b ij i:ℝ)-(q ij i:ℝ)*ell ij i)/2
    let dual := fun ij i => -2*mu ij i*(Real.sqrt (2/(3*mu ij i*(q ij i:ℝ))))^3
    let cloud := fun ij i => (![Int.fract (-(vinv ij i:ℝ)*b ij i/q ij i),
      Int.fract (-(vinv ij i:ℝ)/q ij i),dual ij i/Real.sqrt K₀,
      (3*dual ij i*tau ij i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ij∈P, b ij 0-cround ij 0=b ij 1-cround ij 1) →
    (∀ ij∈P, ∀ a, |cloud ij 0 a-cloud ij 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 →
    R ≤ (N:ℝ) →
    (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    (∀ t∈P.image entry, Mat t 0*Mat t 3-Mat t 1*Mat t 2=1) →
    (∀ ij∈P, (Mat (entry ij) 2:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 3=(q ij 1:ℝ)/q ij 0) →
    (∀ ij∈P, ((Mat (entry ij) 0:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 1)/
      ((Mat (entry ij) 2:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 3)=(rat ij 1:ℝ)) →
    (∀ t∈P.image entry, |(Mat t 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ ij∈P, ∀ i, x ij i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, x ij i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, |(anchor ij:ℝ)-(rat ij 0:ℝ)| ≤ ε) →
    (∀ ij∈P, 256*((anchor ij).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ij∈P, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor ij).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Blabels := fun ab => 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ ab∈Gaps, Blabels ab ≤ Bmajor) →
    (∀ ab∈Gaps, Ccharts ab ≤ Cmajor) →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Aupper := 2*Cupper*(Cthird+1)*E^2*M^2/(κ*Lunit^3*(N:ℝ)^4)
    let Bupper := Cupper*(Cthird+1)*E^2*M^2/(Lunit^2*(N:ℝ)^4*(Uref:ℝ))+
      Dupper*(B+1)*E^2*M^2/(4*(N:ℝ)^4*(Uref:ℝ))
    let Alower := 8*Clower*(Cthird+1)*R^4/(κ*Lunit^3*(N:ℝ)^2)
    let Blower := 4*Clower*(Cthird+1)*R^4/(Lunit^2*(N:ℝ)^2*(Uref:ℝ))+
      (4*Dlower*(B+1)*R^4)/(4*(N:ℝ)^2*(Uref:ℝ))
    let DupperCut := θ*Uband
    let DlowerCut := θ/lambda
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 2=0 ∧ Mat t 3=1 ∧ Mat t 1=t) →
      (P.card:ℝ) ≤ 60*(4*(m0:ℝ)*(3*Aupper^((3:ℝ)⁻¹)*(DupperCut+2)^((2:ℝ)/3)+
        2*Bupper*(3+2*Real.log (DupperCut+2))+(1/2:ℝ)*(2*DupperCut+1)))) ∧
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 1=0 ∧ Mat t 3=1 ∧ Mat t 2=t) →
      (P.card:ℝ) ≤ 60*(4*(m0:ℝ)*(3*Alower^((3:ℝ)⁻¹)*(DlowerCut+2)^((2:ℝ)/3)+
        2*Blower*(3+2*Real.log (DlowerCut+2))+(1/2:ℝ)*(2*DlowerCut+1)))) := by

  pm_2479 hmassFn positive_difference_actual_fourier_triangular_original_pair_mass
  pm_2478
  intro Fsrc η ya yb Tsrc E chartKey Uref Refs Gaps Bselect P entry Mat gap
    Bmajor Cmajor N za zb AlenA AlenB Za Zb Q K₀ inst rat vinv parity anchor e r v s
    σ δ T M R base Bcut θ A W x
    hMat hη hηsmall hya hyb hreg hjets htests hTsrc hMtwo hsourceScale hentry hbase hxa hxb hgapMem hgeometryA hgeometryB
    lambda Uband yp F chartColor hchartColor
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hden hθ hθmax hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hgap
    Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor f hlevel
    q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Blabels m0 hBmajor hCmajor Lunit Gamma Cthird Aupper Bupper Alower Blower DupperCut DlowerCut
  pm_2484
  pm_1626
  pm_2485
  pm_2477
  pm_2483
  exact hmassFn Fsrc η ya yb Tsrc E chartKey Uref Refs Gaps (Bselect:=Bselect)
    P entry Mat gap Bmajor Cmajor N za zb AlenA AlenB Za Zb Q K₀
    rat vinv parity anchor e r v s
    (σ:=σ) (δ:=δ) (T:=T) (M:=M) (R:=R) (base:=base) (Bcut:=Bcut)
    (lambda:=lambda) (Uband:=Uband) (θ:=θ) A (W:=W) (x:=x)
    hMat hη hηsmall hya hyb hreg hjets htests hTsrc hMtwo hsourceScale
    hentry hbase hxa hxb hgapMem hgeometryA hgeometryB hchartColor
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hden
    hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep
    hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth
    hRQ hselectedUpper hscaleTen hfamilyGap hgap
    hsourceColor hlevel hcolor hnear hsmall hNR hRN hNcube hminscale
    hMatdet hMatt hMatmap hMatgamma hNtwo hL hU hanchor hcut hcount hsize hD hΔ hBsize hBmajor hCmajor


private theorem two_thirds_cube {x : ℝ} (hx : 0 ≤ x) :
    (x^((2:ℝ)/3))^3=x^2 := by
  rw [←Real.rpow_natCast,←Real.rpow_mul hx]
  norm_num

                                                                 
                                                                        
section
variable {M N R U L : ℝ} (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
include M N R U L hM hN hR
private theorem triangular_translation_source_regime
    (hU : 0 ≤ U) (hL : 0 ≤ L) (hRN : R ≤ N)
    (hselected : U ≤ (N/R)^((2:ℝ)/3))
    (hregime : N^4 ≤ M*R^3*L^((3:ℝ)/2)) :
    N^2*U ≤ (M*R^2)^((2:ℝ)/3)*L ∧
      N^3*U ≤ M*R^2*L^((3:ℝ)/2) := by
  have hLpow : (L^((3:ℝ)/2))^2=L^3 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hL]
    norm_num
  have hN8 : N^8 ≤ M^2*R^6*L^3 := by
    calc
      _ = (N^4)^2 := by ring
      _ ≤ (M*R^3*L^((3:ℝ)/2))^2 := by gcongr
      _ = _ := by rw [mul_pow,mul_pow,hLpow]; ring
  have hUcube : U^3 ≤ (N/R)^2 := by
    calc
      _ ≤ ((N/R)^((2:ℝ)/3))^3 := by gcongr
      _ = _ := two_thirds_cube (div_nonneg hN.le hR.le)
  have hcube : (N^2*U)^3 ≤ ((M*R^2)^((2:ℝ)/3)*L)^3 := by
    calc
      _ = N^6*U^3 := by ring
      _ ≤ N^6*(N/R)^2 := mul_le_mul_of_nonneg_left hUcube (by positivity)
      _ = N^8/R^2 := by field_simp
      _ ≤ (M^2*R^6*L^3)/R^2 :=
        div_le_div_of_nonneg_right hN8 (sq_nonneg R)
      _ = _ := by rw [mul_pow,two_thirds_cube (by positivity : (0:ℝ) ≤ M*R^2)]; field_simp
  constructor
  · exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : 3≠0)).mp hcube
  · have hratio : 1 ≤ N/R := (le_div_iff₀ hR).mpr (by simpa only [one_mul] using hRN)
    have hlinear : U ≤ N/R := hselected.trans
      ((Real.rpow_le_rpow_of_exponent_le hratio (by norm_num : (2:ℝ)/3 ≤ 1)).trans_eq (Real.rpow_one _))
    calc
      _ ≤ N^3*(N/R) := mul_le_mul_of_nonneg_left hlinear (by positivity)
      _ = N^4/R := by ring
      _ ≤ (M*R^3*L^((3:ℝ)/2))/R := div_le_div_of_nonneg_right hregime hR.le
      _ = _ := by field_simp


private theorem triangular_physical_regime_costs
    (hU : 0 < U) (hL : 0 ≤ L) (hRN : R ≤ N)
    (hselected : U ≤ (N/R)^((2:ℝ)/3))
    (hregime : N^4 ≤ M*R^3*L^((3:ℝ)/2)) :
    (M^2/N^4)*(M/(N*R^2))^2 ≤ ((M^2/(N^4*U))*L)^3 ∧
    (R^4/N^2)*(N*R^2/M)^2 ≤ ((R^4/(N^2*U))*L)^3 ∧
    M/(N*R^2) ≤ (M^2/(N^4*U))*L^((3:ℝ)/2) ∧
    N*R^2/M ≤ (R^4/(N^2*U))*L^((3:ℝ)/2) := by
  obtain ⟨hfirst,hshort⟩ := triangular_translation_source_regime
    hM hN hR hU.le hL hRN hselected hregime
  have hcore : N^6*U^3 ≤ M^2*R^4*L^3 := by
    have hh := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ N^2*U) hfirst 3
    simp only [mul_pow,two_thirds_cube (by positivity : (0:ℝ) ≤ M*R^2)] at hh
    convert hh using 1 <;> ring
  pm_4898
  · rw [show (M^2/N^4)*(M/(N*R^2))^2=M^4/(N^6*R^4) by field_simp,
      show ((M^2/(N^4*U))*L)^3=M^6*L^3/(N^12*U^3) by field_simp]
    pm_23
    have hh := mul_le_mul_of_nonneg_left hcore (by positivity : (0:ℝ) ≤ M^4*N^6)
    nlinarith only [hh]
  · rw [show (R^4/N^2)*(N*R^2/M)^2=R^8/M^2 by field_simp,
      show ((R^4/(N^2*U))*L)^3=R^12*L^3/(N^6*U^3) by field_simp]
    pm_23
    have hh := mul_le_mul_of_nonneg_left hcore (by positivity : (0:ℝ) ≤ R^8)
    nlinarith only [hh]
  · rw [show (M^2/(N^4*U))*L^((3:ℝ)/2)=M^2*L^((3:ℝ)/2)/(N^4*U) by ring]
    pm_23
    have hh := mul_le_mul_of_nonneg_left hshort (by positivity : (0:ℝ) ≤ M*N)
    nlinarith only [hh]
  · rw [show (R^4/(N^2*U))*L^((3:ℝ)/2)=R^4*L^((3:ℝ)/2)/(N^2*U) by ring]
    apply (div_le_div_iff₀ hM (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_left hshort (sq_nonneg R)
    nlinarith only [hh]
end


private theorem triangular_weight_regime_absorption
    {Aconst Dconst Bconst abase dbase Cost L : ℝ}
    (hAconst : 0 ≤ Aconst) (hDconst : 0 ≤ Dconst)
    (habase : 0 ≤ abase) (hdbase : 0 ≤ dbase)
    (hCost : 0 ≤ Cost) (hL : 0 ≤ L)
    (hD : 1 ≤ Dconst*dbase)
    (hcubeBase : abase*dbase^2 ≤ (Cost*L)^3)
    (hshortBase : dbase ≤ Cost*L^((3:ℝ)/2)) :
    3*(Aconst*abase)^((3:ℝ)⁻¹)*(Dconst*dbase+2)^((2:ℝ)/3)+
        2*(Bconst*Cost)*(3+2*Real.log (Dconst*dbase+2))+
        (1/2:ℝ)*(2*(Dconst*dbase)+1) ≤
      Cost*(9*(Aconst*Dconst^2)^((3:ℝ)⁻¹)*L+
        2*Bconst*(3+2*Real.log (Dconst*dbase+2))+
        (3/2:ℝ)*Dconst*L^((3:ℝ)/2)) := by
  have hrootCube (z : ℝ) (hz : 0 ≤ z) : (z^((3:ℝ)⁻¹))^3=z := by
    simpa only [Nat.cast_ofNat] using
      Real.rpow_inv_natCast_pow hz (by norm_num : (3:ℕ)≠0)
  pm_6529 hDnonneg Dconst dbase hDconst hdbase
  have hthree : Dconst*dbase+2 ≤ 3*(Dconst*dbase) := by linarith only [hD]
  have hcube :
      ((Aconst*abase)^((3:ℝ)⁻¹)*(Dconst*dbase+2)^((2:ℝ)/3))^3 ≤
        (3*(Aconst*Dconst^2)^((3:ℝ)⁻¹)*Cost*L)^3 := by
    calc
      _ = (Aconst*abase)*(Dconst*dbase+2)^2 := by
        rw [mul_pow,hrootCube (Aconst*abase) (mul_nonneg hAconst habase),
          two_thirds_cube (by positivity)]
      _ ≤ (Aconst*abase)*(3*(Dconst*dbase))^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hthree 2) (mul_nonneg hAconst habase)
      _ = 9*(Aconst*Dconst^2)*(abase*dbase^2) := by ring
      _ ≤ 9*(Aconst*Dconst^2)*(Cost*L)^3 :=
        mul_le_mul_of_nonneg_left hcubeBase (by positivity)
      _ ≤ 27*(Aconst*Dconst^2)*(Cost*L)^3 := by
        have hh : 0 ≤ (Aconst*Dconst^2)*(Cost*L)^3 := by positivity
        nlinarith only [hh]
      _ = _ := by
        simp only [mul_pow,hrootCube (Aconst*Dconst^2) (mul_nonneg hAconst (sq_nonneg Dconst))]
        ring
  have hroot := (pow_le_pow_iff_left₀ (by positivity) (by positivity)
    (by norm_num : (3:ℕ)≠0)).mp hcube
  have hroot3 := mul_le_mul_of_nonneg_left hroot (by norm_num : (0:ℝ) ≤ 3)
  have hshort : (1/2:ℝ)*(2*(Dconst*dbase)+1) ≤
      Cost*((3/2:ℝ)*Dconst*L^((3:ℝ)/2)) := by
    have hh := mul_le_mul_of_nonneg_left hshortBase hDconst
    nlinarith only [hD,hh]
  calc
    _ ≤ 3*(3*(Aconst*Dconst^2)^((3:ℝ)⁻¹)*Cost*L)+
        2*(Bconst*Cost)*(3+2*Real.log (Dconst*dbase+2))+
        Cost*((3/2:ℝ)*Dconst*L^((3:ℝ)/2)) :=
      by simpa only [mul_assoc] using add_le_add (add_le_add hroot3 (le_refl (2*(Bconst*Cost)*(3+2*Real.log (Dconst*dbase+2))))) hshort
    _ = _ := by ring


private theorem triangular_source_weight_scale_identities
    {M N R U T σsrc csrc Usrc κ Lunit E θ CU CL DU DL Cthird B : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hT : 0 < T)
    (hscale : T*N*R^2=M^3) :
    let lambda := csrc*κ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*E*T/(2*M^2)
    let Aupper := 2*CU*(Cthird+1)*E^2*M^2/(κ*Lunit^3*N^4)
    let Bupper := CU*(Cthird+1)*E^2*M^2/(Lunit^2*N^4*U)+DU*(B+1)*E^2*M^2/(4*N^4*U)
    let Alower := 8*CL*(Cthird+1)*R^4/(κ*Lunit^3*N^2)
    let Blower := 4*CL*(Cthird+1)*R^4/(Lunit^2*N^2*U)+(4*DL*(B+1)*R^4)/(4*N^2*U)
    let AupperConst := 2*CU*(Cthird+1)*E^2/(κ*Lunit^3)
    let BupperConst := CU*(Cthird+1)*E^2/Lunit^2+DU*(B+1)*E^2/4
    let AlowerConst := 8*CL*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*CL*(Cthird+1)/Lunit^2+DL*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*E/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    Aupper=AupperConst*(M^2/N^4) ∧
    Bupper=BupperConst*(M^2/(N^4*U)) ∧
    Alower=AlowerConst*(R^4/N^2) ∧
    Blower=BlowerConst*(R^4/(N^2*U)) ∧
    θ*Uband=DupperConst*(M/(N*R^2)) ∧
    θ/lambda=DlowerConst*(N*R^2/M) := by
  intro lambda Uband Aupper Bupper Alower Blower AupperConst BupperConst
    AlowerConst BlowerConst DupperConst DlowerConst
  have hforward : T/M^2=M/(N*R^2) := by
    pm_1804
    nlinarith only [hscale]
  have hreverse : M^2/T=N*R^2/M := by
    apply (div_eq_div_iff hT.ne' hM.ne').mpr
    nlinarith only [hscale]
  pm_2486
  pm_965 Aupper AupperConst
  pm_965 Bupper BupperConst
  pm_965 Alower AlowerConst
  pm_965 Blower BlowerConst
  · calc
      _ = DupperConst*(T/M^2) := by dsimp only [Uband,DupperConst]; ring
      _ = _ := by rw [hforward]
  · calc
      _ = DlowerConst*(M^2/T) := by
        dsimp only [lambda,DlowerConst]
        simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
        ring
      _ = _ := by rw [hreverse]

private theorem triangular_original_mass_regime_assembly
    (m0 : ℕ) {M N R U T σsrc csrc Usrc κ Lunit E θ CU CL DU DL Cthird B Lregime mass : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hRpos : 0 < R) (hUp : 0 < U) (hT : 0 < T)
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hκ : 0 < κ) (hLunit : 0 < Lunit) (hE : 0 ≤ E) (hθ : 0 ≤ θ)
    (hCU : 0 ≤ CU) (hCL : 0 ≤ CL) (hDU : 0 ≤ DU) (hDL : 0 ≤ DL)
    (hCthird : 0 ≤ Cthird) (hBnonneg : 0 ≤ B)
    (hLregime : 0 ≤ Lregime) (hRN : R ≤ N) (hscale : T*N*R^2=M^3)
    (hselected : U ≤ (N/R)^((2:ℝ)/3))
    (hregime : N^4 ≤ M*R^3*Lregime^((3:ℝ)/2)) :

    let lambda := csrc*κ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*E*T/(2*M^2)
    let Aupper := 2*CU*(Cthird+1)*E^2*M^2/(κ*Lunit^3*N^4)
    let Bupper := CU*(Cthird+1)*E^2*M^2/(Lunit^2*N^4*U)+DU*(B+1)*E^2*M^2/(4*N^4*U)
    let Alower := 8*CL*(Cthird+1)*R^4/(κ*Lunit^3*N^2)
    let Blower := 4*CL*(Cthird+1)*R^4/(Lunit^2*N^2*U)+(4*DL*(B+1)*R^4)/(4*N^2*U)
    let AupperConst := 2*CU*(Cthird+1)*E^2/(κ*Lunit^3)
    let BupperConst := CU*(Cthird+1)*E^2/Lunit^2+DU*(B+1)*E^2/4
    let AlowerConst := 8*CL*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*CL*(Cthird+1)/Lunit^2+DL*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*E/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let CostUpper := M^2/(N^4*U)
    let CostLower := R^4/(N^2*U)
    let DupperCut := θ*Uband
    let DlowerCut := θ/lambda
    (mass ≤ 60*(4*(m0:ℝ)*(3*Aupper^((3:ℝ)⁻¹)*(DupperCut+2)^((2:ℝ)/3)+
        2*Bupper*(3+2*Real.log (DupperCut+2))+(1/2:ℝ)*(2*DupperCut+1))) →
      (mass=0 ∨ 1 ≤ DupperCut) →
      mass ≤ 240*(m0:ℝ)*CostUpper*
        (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)*Lregime+
          2*BupperConst*(3+2*Real.log (DupperCut+2))+
          (3/2:ℝ)*DupperConst*Lregime^((3:ℝ)/2))) ∧
    (mass ≤ 60*(4*(m0:ℝ)*(3*Alower^((3:ℝ)⁻¹)*(DlowerCut+2)^((2:ℝ)/3)+
        2*Blower*(3+2*Real.log (DlowerCut+2))+(1/2:ℝ)*(2*DlowerCut+1))) →
      (mass=0 ∨ 1 ≤ DlowerCut) →
      mass ≤ 240*(m0:ℝ)*CostLower*
        (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)*Lregime+
          2*BlowerConst*(3+2*Real.log (DlowerCut+2))+
          (3/2:ℝ)*DlowerConst*Lregime^((3:ℝ)/2))) := by
  intro lambda Uband Aupper Bupper Alower Blower AupperConst BupperConst
    AlowerConst BlowerConst DupperConst DlowerConst CostUpper CostLower DupperCut DlowerCut
  pm_1626
  pm_2485
  pm_2487
  have hphysical := triangular_physical_regime_costs hM hN hRpos hUp hLregime hRN
    hselected hregime
  have hid :
      Aupper=AupperConst*(M^2/N^4) ∧
      Bupper=BupperConst*CostUpper ∧
      Alower=AlowerConst*(R^4/N^2) ∧
      Blower=BlowerConst*CostLower ∧
      DupperCut=DupperConst*(M/(N*R^2)) ∧
      DlowerCut=DlowerConst*(N*R^2/M) :=
    triangular_source_weight_scale_identities
      (U:=U) (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) (κ:=κ)
      (Lunit:=Lunit) (E:=E) (θ:=θ) (CU:=CU) (CL:=CL) (DU:=DU) (DL:=DL)
      (Cthird:=Cthird) (B:=B) hM hN hRpos hT hscale
  constructor
  · intro hraw hnonempty
    rcases hnonempty with hzero | hDcut
    · rw [hzero]
      pm_82 hDcut0 DupperCut
      pm_6181 DupperCut
    ·
      have hw := triangular_weight_regime_absorption (Bconst:=BupperConst)
        hAU hDUc (by positivity : (0:ℝ) ≤ M^2/N^4)
        (by positivity : (0:ℝ) ≤ M/(N*R^2))
        hCostU hLregime
        (by rw [←hid.2.2.2.2.1]; exact hDcut) hphysical.1 hphysical.2.2.1
      rw [←hid.1,←hid.2.1,←hid.2.2.2.2.1] at hw
      calc
        _ ≤ 60*(4*(m0:ℝ)*(3*Aupper^((3:ℝ)⁻¹)*(DupperCut+2)^((2:ℝ)/3)+
            2*Bupper*(3+2*Real.log (DupperCut+2))+(1/2:ℝ)*(2*DupperCut+1))) := hraw
        _ ≤ 60*(4*(m0:ℝ)*(CostUpper*
            (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)*Lregime+
              2*BupperConst*(3+2*Real.log (DupperCut+2))+
              (3/2:ℝ)*DupperConst*Lregime^((3:ℝ)/2)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw (by positivity)) (by norm_num)
        _ = _ := by ring
  · intro hraw hnonempty
    rcases hnonempty with hzero | hDcut
    · rw [hzero]
      pm_82 hDcut0 DlowerCut
      pm_6181 DlowerCut
    ·
      have hw := triangular_weight_regime_absorption (Bconst:=BlowerConst)
        hAL hDLc (by positivity : (0:ℝ) ≤ R^4/N^2)
        (by positivity : (0:ℝ) ≤ N*R^2/M)
        hCostL hLregime
        (by rw [←hid.2.2.2.2.2]; exact hDcut) hphysical.2.1 hphysical.2.2.2
      rw [←hid.2.2.1,←hid.2.2.2.1,←hid.2.2.2.2.2] at hw
      calc
        _ ≤ 60*(4*(m0:ℝ)*(3*Alower^((3:ℝ)⁻¹)*(DlowerCut+2)^((2:ℝ)/3)+
            2*Blower*(3+2*Real.log (DlowerCut+2))+(1/2:ℝ)*(2*DlowerCut+1))) := hraw
        _ ≤ 60*(4*(m0:ℝ)*(CostLower*
            (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)*Lregime+
              2*BlowerConst*(3+2*Real.log (DlowerCut+2))+
              (3/2:ℝ)*DlowerConst*Lregime^((3:ℝ)/2)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw (by positivity)) (by norm_num)
        _ = _ := by ring


                                                                        
                                                                       
                                                                        
                                                            
theorem positive_difference_actual_fourier_triangular_original_source_regime_mass
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower Dupper Dlower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧
    ∀ (Fsrc : ℝ → ℝ) (η ya yb Tsrc E Lregime : ℝ) (chartKey : ℤ → ℤ × ℤ × ℤ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2))) (entry : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℤ)
    (Mat : ℤ → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ) (Bmajor Cmajor : ℕ)
    (N : ℕ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ) (Za Zb : ℤ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℚ) (vinv : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℤ)
    (parity : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → Fin 2) (anchor : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M R base Bcut θ : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ} {x : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℝ},
    Function.Injective Mat →
    0 < η → η ≤ η₀ →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    (∀ ij∈P, entry ij≠0) →
    (∀ ij∈P, base ≤ za ij.1.1) →
    (∀ ij∈P, x ij 0=za ij.1.1) →
    (∀ ij∈P, x ij 1=zb ij.2.1) →
    (∀ ij∈P, gap ij∈Gaps) →
    (∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ)) →
    (∀ ij∈P, N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(AlenB ij.2.1:ℤ)=Zb+(N:ℤ)*ij.2.1+2*(N:ℤ)) →
    0 ≤ Lregime →
    (N:ℝ)^4 ≤ M*R^3*Lregime^((3:ℝ)/2) →
    let lambda := csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*E*T/(2*M^2)
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let chartColor := fun ij i =>
      (⌊yp i/a⌋,⌊((2*M^2/Tsrc)*(rat ij i:ℝ))/a⌋,
        ⌊((Tsrc/(2*M^2))*(rat ij i:ℝ)⁻¹)/a⌋)
    (∀ ij∈P, ∀ i, chartColor ij i=chartKey (entry ij)) →
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < (N:ℝ)) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*(N:ℝ)*R^2=M^3) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ ij∈P, ∀ i, x ij i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, (rat ij i).den ≤ Q ∧ Q ≤ 2*(rat ij i).den) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ ij∈P, ∀ i, ((rat ij i).den:ℤ) ∣ (rat ij i).num*vinv ij i-1) →
    (∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) →
    (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ ij∈P, ∀ i, x ij i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, x ij i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (∀ ij∈P, (rat ij 0:ℝ)∈Icc (gap ij).1 (gap ij).2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (ab : ℝ × ℝ) => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (ab : ℝ × ℝ) => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun ij i => (⌊((rat ij i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((rat ij i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ij∈P, sourceColor ij 0=sourceColor ij 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ij∈P, ∀ i, iteratedDeriv 2 (f i) (x ij i)/2=(rat ij i:ℝ)) →
    let q := fun ij i => (rat ij i).den
    let mu := fun ij i => iteratedDeriv 3 (f i) (round (x ij i))/6
    let ell := fun ij i => deriv (f i) (round (x ij i))
    let b := fun ij i => (⌊(q ij i:ℝ)*ell ij i⌋+(parity ij i:ℕ) : ℤ)
    let cround := fun ij i => round ((q ij i:ℝ)*ell ij i)
    let tau := fun ij i => ((b ij i:ℝ)-(q ij i:ℝ)*ell ij i)/2
    let dual := fun ij i => -2*mu ij i*(Real.sqrt (2/(3*mu ij i*(q ij i:ℝ))))^3
    let cloud := fun ij i => (![Int.fract (-(vinv ij i:ℝ)*b ij i/q ij i),
      Int.fract (-(vinv ij i:ℝ)/q ij i),dual ij i/Real.sqrt K₀,
      (3*dual ij i*tau ij i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ij∈P, b ij 0-cround ij 0=b ij 1-cround ij 1) →
    (∀ ij∈P, ∀ a, |cloud ij 0 a-cloud ij 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 →
    R ≤ (N:ℝ) →
    (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    (∀ t∈P.image entry, Mat t 0*Mat t 3-Mat t 1*Mat t 2=1) →
    (∀ ij∈P, (Mat (entry ij) 2:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 3=(q ij 1:ℝ)/q ij 0) →
    (∀ ij∈P, ((Mat (entry ij) 0:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 1)/
      ((Mat (entry ij) 2:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 3)=(rat ij 1:ℝ)) →
    (∀ t∈P.image entry, |(Mat t 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ ij∈P, ∀ i, x ij i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, x ij i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, |(anchor ij:ℝ)-(rat ij 0:ℝ)| ≤ ε) →
    (∀ ij∈P, 256*((anchor ij).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ij∈P, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor ij).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Blabels := fun ab => 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ ab∈Gaps, Blabels ab ≤ Bmajor) →
    (∀ ab∈Gaps, Ccharts ab ≤ Cmajor) →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let AupperConst := 2*Cupper*(Cthird+1)*E^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*E^2/Lunit^2+Dupper*(B+1)*E^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*E/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let CostUpper := M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := R^4/((N:ℝ)^2*(Uref:ℝ))
    let DupperCut := θ*Uband
    let DlowerCut := θ/lambda
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 2=0 ∧ Mat t 3=1 ∧ Mat t 1=t) →
      (P.card:ℝ) ≤ 240*(m0:ℝ)*CostUpper*
        (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)*Lregime+
          2*BupperConst*(3+2*Real.log (DupperCut+2))+
          (3/2:ℝ)*DupperConst*Lregime^((3:ℝ)/2))) ∧
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 1=0 ∧ Mat t 3=1 ∧ Mat t 2=t) →
      (P.card:ℝ) ≤ 240*(m0:ℝ)*CostLower*
        (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)*Lregime+
          2*BlowerConst*(3+2*Real.log (DlowerCut+2))+
          (3/2:ℝ)*DlowerConst*Lregime^((3:ℝ)/2))) := by
  pm_2479 hmassFn positive_difference_actual_fourier_triangular_original_source_mass
  pm_2478
  intro Fsrc η ya yb Tsrc E Lregime chartKey Uref Refs Gaps Bselect P entry Mat gap
    Bmajor Cmajor N za zb AlenA AlenB Za Zb Q K₀ inst rat vinv parity anchor e r v s
    σ δ T M R base Bcut θ A W x
    hMat hη hηsmall hya hyb hreg hjets htests hTsrc hMtwo hsourceScale hentry hbase hxa hxb hgapMem hgeometryA hgeometryB hLregime hregime
    lambda Uband yp F chartColor hchartColor
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hden hθ hθmax hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hgap
    Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor f hlevel
    q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Blabels m0 hBmajor hCmajor Lunit Gamma Cthird AupperConst BupperConst AlowerConst BlowerConst DupperConst DlowerConst CostUpper CostLower DupperCut DlowerCut
  let Aupper := 2*CU*(Cthird+1)*E^2*M^2/(κ*Lunit^3*(N:ℝ)^4)
  let Bupper := CU*(Cthird+1)*E^2*M^2/(Lunit^2*(N:ℝ)^4*(Uref:ℝ))+
    DU*(B+1)*E^2*M^2/(4*(N:ℝ)^4*(Uref:ℝ))
  let Alower := 8*CL*(Cthird+1)*R^4/(κ*Lunit^3*(N:ℝ)^2)
  let Blower := 4*CL*(Cthird+1)*R^4/(Lunit^2*(N:ℝ)^2*(Uref:ℝ))+
    (4*DL*(B+1)*R^4)/(4*(N:ℝ)^2*(Uref:ℝ))
  pm_2484
  pm_1626
  pm_2485
  pm_2477
  pm_2483
  have hraw :
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 2=0 ∧ Mat t 3=1 ∧ Mat t 1=t) →
      (P.card:ℝ) ≤ 60*(4*(m0:ℝ)*(3*Aupper^((3:ℝ)⁻¹)*(DupperCut+2)^((2:ℝ)/3)+
        2*Bupper*(3+2*Real.log (DupperCut+2))+(1/2:ℝ)*(2*DupperCut+1)))) ∧
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 1=0 ∧ Mat t 3=1 ∧ Mat t 2=t) →
      (P.card:ℝ) ≤ 60*(4*(m0:ℝ)*(3*Alower^((3:ℝ)⁻¹)*(DlowerCut+2)^((2:ℝ)/3)+
        2*Blower*(3+2*Real.log (DlowerCut+2))+(1/2:ℝ)*(2*DlowerCut+1)))) := by
    exact hmassFn Fsrc η ya yb Tsrc E chartKey Uref Refs Gaps (Bselect:=Bselect)
      P entry Mat gap Bmajor Cmajor N za zb AlenA AlenB Za Zb Q K₀
      rat vinv parity anchor e r v s
      (σ:=σ) (δ:=δ) (T:=T) (M:=M) (R:=R) (base:=base) (Bcut:=Bcut)
      (θ:=θ) A (W:=W) (x:=x)
      hMat hη hηsmall hya hyb hreg hjets htests hTsrc hMtwo hsourceScale
      hentry hbase hxa hxb hgapMem hgeometryA hgeometryB hchartColor
      hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hden
      hθ hθmax hinv hchart horientation hBcut hs hrefSet hparentSet hsep
      hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth
      hRQ hselectedUpper hscaleTen hfamilyGap hgap
      hsourceColor hlevel hcolor hnear hsmall hNR hRN hNcube hminscale
      hMatdet hMatt hMatmap hMatgamma hNtwo hL hU hanchor hcut hcount hsize hD hΔ hBsize hBmajor hCmajor

  have hRpos : 0 < R := zero_lt_one.trans_le hR
  pm_1693
  pm_4473 hQpos Q hQ
  pm_2488
  pm_2480
  obtain ⟨hBnonneg,hCthird⟩ := physical_source_triangular_constants_nonneg hσ
    (approximateModelPhase_tolerance_nonneg (hF 0))
  have hBselOne : 1 ≤ Bselect := by
    have hh : 0 ≤ 168/modelPhaseThirdLower σ := by positivity
    linarith only [hBselectSize,hh]
  have hselected : (Uref:ℝ) ≤ ((N:ℝ)/R)^((2:ℝ)/3) := by
    calc
      _ ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect := hselectedUpper
      _ ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3) :=
        div_le_self (by positivity) hBselOne
      _ ≤ _ := Real.rpow_le_rpow (by positivity)
        (div_le_div_of_nonneg_left hN.le hRpos hRQ) (by norm_num)
  have hassembly := triangular_original_mass_regime_assembly m0
    (mass:=(P.card:ℝ)) hM hN hRpos hUp hT hσsrc hcsrc hUsrc hκ hLunit hE.le hθ.le
    hCU.le hCL.le hDU.le hDL.le hCthird hBnonneg hLregime hRN hscale hselected hregime
  have hcuts ij (hij : ij∈P) :
      ((Mat (entry ij) 0=1 ∧ Mat (entry ij) 2=0 ∧ Mat (entry ij) 3=1) →
        |(Mat (entry ij) 1:ℝ)| ≤ DupperCut) ∧
      ((Mat (entry ij) 0=1 ∧ Mat (entry ij) 1=0 ∧ Mat (entry ij) 3=1) →
        |(Mat (entry ij) 2:ℝ)| ≤ DlowerCut) :=
    rational_narrow_triangular_translation_bounds (rat ij) (Mat (entry ij)) Q
      hQ hlambda hUband hθ (hcurv ij hij) (hden ij hij)
      (hsourceColor ij hij) (hMatt ij hij) (hMatmap ij hij)
  constructor
  · intro htri
    apply hassembly.1 (hraw.1 htri)
    by_cases hne : P.Nonempty
    · obtain ⟨ij,hij⟩ := hne
      pm_7455
      have hcut := (hcuts ij hij).1 ⟨hsides.1,hsides.2.1,hsides.2.2.1⟩
      pm_2489
    pm_6677
  · intro htri
    apply hassembly.2 (hraw.2 htri)
    by_cases hne : P.Nonempty
    · obtain ⟨ij,hij⟩ := hne
      pm_7455
      have hcut := (hcuts ij hij).2 ⟨hsides.1,hsides.2.1,hsides.2.2.1⟩
      pm_2489
    pm_6677


private theorem eventually_triangular_source_log_losses {Du Dl ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in Filter.atTop,
      0 ≤ Real.log T ∧ Real.log T ≤ T^ε ∧
      (Real.log T)^((3:ℝ)/2) ≤ T^ε ∧
      (∀ d : ℝ, 0 ≤ d → d ≤ Du*T → 3+2*Real.log (d+2) ≤ T^ε) ∧
      (∀ d : ℝ, 0 ≤ d → d ≤ Dl*T → 3+2*Real.log (d+2) ≤ T^ε) := by
  filter_upwards [eventually_const_log_pow_le_rpow 7 (by norm_num) 2 hε,
    Filter.eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Filter.eventually_ge_atTop (Du+2), Filter.eventually_ge_atTop (Dl+2)]
    with T hsmall hT hlog hDu hDl
  have hlogsq : Real.log T ≤ (Real.log T)^2 := by nlinarith only [hlog]
  have hsquare : (Real.log T)^2 ≤ T^ε :=
    (by nlinarith only [sq_nonneg (Real.log T)] : (Real.log T)^2 ≤ 7*(Real.log T)^2).trans hsmall
  have hpower : (Real.log T)^((3:ℝ)/2) ≤ (Real.log T)^2 := by
    simpa only [Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_le hlog (by norm_num : (3:ℝ)/2 ≤ (2:ℝ))
  have hcut (D d : ℝ) (hD : D+2 ≤ T) (hd : 0 ≤ d) (hdT : d ≤ D*T) :
      3+2*Real.log (d+2) ≤ T^ε := by
    have hbound : d+2 ≤ T^2 := by
      calc
        _ ≤ (D+2)*T := by nlinarith only [hdT,hT]
        _ ≤ T*T := mul_le_mul_of_nonneg_right hD (zero_le_one.trans hT)
        _ = _ := pow_two T |>.symm
    have hlogd := Real.log_le_log (by linarith only [hd] : 0 < d+2) hbound
    pm_1451 Real.log_pow hlogd Nat.cast_ofNat
    exact (by nlinarith only [hlogd,hlog,hlogsq] :
      3+2*Real.log (d+2) ≤ 7*(Real.log T)^2).trans hsmall
  exact ⟨zero_le_one.trans hlog,hlogsq.trans hsquare,hpower.trans hsquare,
    fun d hd hdT => hcut Du d hDu hd hdT,
    fun d hd hdT => hcut Dl d hDl hd hdT⟩

private theorem triangular_physical_cutoff_height
    {T M N R Du Dl : ℝ} (hT : 0 < T) (hM : 1 ≤ M) (hR : 1 ≤ R)
    (hRN : R ≤ N) (hNM : N^2 ≤ M) (hscale : T*N*R^2=M^3)
    (hDu : 0 ≤ Du) (hDl : 0 ≤ Dl) :
    Du*T/M^2 ≤ Du*T ∧ Dl*M^2/T ≤ Dl*T := by
  have hNp : 1 ≤ N := hR.trans hRN
  have hMp : 0 < M := zero_lt_one.trans_le hM
  pm_1772 hNp
  have hR₂ : R^2 ≤ M :=
    (pow_le_pow_left₀ (zero_le_one.trans hR) hRN 2).trans hNM
  pm_1465 hNM' hR₂
  have hMT : M ≤ T := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hMp)).mp
    calc
      M*M^2 = M^3 := by ring
      _ = T*(N*R^2) := by nlinarith only [hscale]
      _ ≤ T*M^2 := mul_le_mul_of_nonneg_left hprod hT.le
  refine ⟨div_le_self (mul_nonneg hDu hT.le) (one_le_pow₀ hM),?_⟩
  apply (div_le_iff₀ hT).mpr
  simpa only [mul_assoc,pow_two] using
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hMp.le hMT 2) hDl

private theorem triangular_logarithmic_mass_absorption
    {T ε m Cost A B D d mass : ℝ}
    (hT : 0 < T) (hm : 0 ≤ m) (hCost : 0 ≤ Cost)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hmass : mass ≤ 240*m*Cost*
      (9*(A*D^2)^((3:ℝ)⁻¹)*Real.log T+
        2*B*(3+2*Real.log (d+2))+(3/2:ℝ)*D*(Real.log T)^((3:ℝ)/2)))
    (hmmajor : m ≤ T^(ε/2)) (hlog : Real.log T ≤ T^(ε/2))
    (hpow : (Real.log T)^((3:ℝ)/2) ≤ T^(ε/2))
    (hcut : 3+2*Real.log (d+2) ≤ T^(ε/2)) :
    mass ≤ (240*Cost*(9*(A*D^2)^((3:ℝ)⁻¹)+2*B+(3/2:ℝ)*D))*T^ε := by
  have hroot : 0 ≤ (A*D^2)^((3:ℝ)⁻¹) := by positivity
  have hterms :
      9*(A*D^2)^((3:ℝ)⁻¹)*Real.log T+
        2*B*(3+2*Real.log (d+2))+(3/2:ℝ)*D*(Real.log T)^((3:ℝ)/2) ≤
      (9*(A*D^2)^((3:ℝ)⁻¹)+2*B+(3/2:ℝ)*D)*T^(ε/2) := by
    nlinarith only [
      mul_le_mul_of_nonneg_left hlog (by positivity : (0:ℝ) ≤ 9*(A*D^2)^((3:ℝ)⁻¹)),
      mul_le_mul_of_nonneg_left hcut (by positivity : (0:ℝ) ≤ 2*B),
      mul_le_mul_of_nonneg_left hpow (by positivity : (0:ℝ) ≤ (3/2:ℝ)*D)]
  pm_7307 hproduct T ε hT
  calc
    _ ≤ 240*m*Cost*((9*(A*D^2)^((3:ℝ)⁻¹)+2*B+(3/2:ℝ)*D)*T^(ε/2)) :=
      hmass.trans (mul_le_mul_of_nonneg_left hterms (by positivity))
    _ ≤ 240*T^(ε/2)*Cost*((9*(A*D^2)^((3:ℝ)⁻¹)+2*B+(3/2:ℝ)*D)*T^(ε/2)) := by gcongr
    _ = _ := by
      calc
        _ = (240*Cost*(9*(A*D^2)^((3:ℝ)⁻¹)+2*B+(3/2:ℝ)*D))*(T^(ε/2)*T^(ε/2)) := by ring
        _ = _ := by rw [hproduct]

                                                                         
                                                                                   
                                                      
theorem eventually_positive_difference_actual_fourier_triangular_original_source_mass
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower Dupper Dlower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧
    ∀ {σ Jref εloss E θ : ℝ}, 0 < σ → 0 ≤ Jref → 0 < εloss →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (η ya yb Tsrc : ℝ) (chartKey : ℤ → ℤ × ℤ × ℤ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2))) (entry : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℤ)
    (Mat : ℤ → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ)
    (N : ℕ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ) (Za Zb : ℤ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℚ) (vinv : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℤ)
    (parity : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → Fin 2) (anchor : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {δ M R base Bcut : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ} {x : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℝ},
    Function.Injective Mat →
    0 < η → η ≤ η₀ →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    (∀ ij∈P, entry ij≠0) →
    (∀ ij∈P, base ≤ za ij.1.1) →
    (∀ ij∈P, x ij 0=za ij.1.1) →
    (∀ ij∈P, x ij 1=zb ij.2.1) →
    (∀ ij∈P, gap ij∈Gaps) →
    (∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ)) →
    (∀ ij∈P, N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(AlenB ij.2.1:ℤ)=Zb+(N:ℤ)*ij.2.1+2*(N:ℤ)) →
    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    let lambda := csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2)
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let chartColor := fun ij i =>
      (⌊yp i/a⌋,⌊((2*M^2/Tsrc)*(rat ij i:ℝ))/a⌋,
        ⌊((Tsrc/(2*M^2))*(rat ij i:ℝ)⁻¹)/a⌋)
    (∀ ij∈P, ∀ i, chartColor ij i=chartKey (entry ij)) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < (N:ℝ)) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*(N:ℝ)*R^2=M^3) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ ij∈P, ∀ i, x ij i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, (rat ij i).den ≤ Q ∧ Q ≤ 2*(rat ij i).den) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ ij∈P, ∀ i, ((rat ij i).den:ℤ) ∣ (rat ij i).num*vinv ij i-1) →
    (∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) →
    (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ ij∈P, ∀ i, x ij i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, x ij i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (∀ ij∈P, (rat ij 0:ℝ)∈Icc (gap ij).1 (gap ij).2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (Q:ℝ) ≤ (N:ℝ) → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((v ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let sourceColor := fun ij i => (⌊((rat ij i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((rat ij i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ij∈P, sourceColor ij 0=sourceColor ij 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ij∈P, ∀ i, iteratedDeriv 2 (f i) (x ij i)/2=(rat ij i:ℝ)) →
    let q := fun ij i => (rat ij i).den
    let mu := fun ij i => iteratedDeriv 3 (f i) (round (x ij i))/6
    let ell := fun ij i => deriv (f i) (round (x ij i))
    let b := fun ij i => (⌊(q ij i:ℝ)*ell ij i⌋+(parity ij i:ℕ) : ℤ)
    let cround := fun ij i => round ((q ij i:ℝ)*ell ij i)
    let tau := fun ij i => ((b ij i:ℝ)-(q ij i:ℝ)*ell ij i)/2
    let dual := fun ij i => -2*mu ij i*(Real.sqrt (2/(3*mu ij i*(q ij i:ℝ))))^3
    let cloud := fun ij i => (![Int.fract (-(vinv ij i:ℝ)*b ij i/q ij i),
      Int.fract (-(vinv ij i:ℝ)/q ij i),dual ij i/Real.sqrt K₀,
      (3*dual ij i*tau ij i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ij∈P, b ij 0-cround ij 0=b ij 1-cround ij 1) →
    (∀ ij∈P, ∀ a, |cloud ij 0 a-cloud ij 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 →
    R ≤ (N:ℝ) →
    (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    (∀ t∈P.image entry, Mat t 0*Mat t 3-Mat t 1*Mat t 2=1) →
    (∀ ij∈P, (Mat (entry ij) 2:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 3=(q ij 1:ℝ)/q ij 0) →
    (∀ ij∈P, ((Mat (entry ij) 0:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 1)/
      ((Mat (entry ij) 2:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 3)=(rat ij 1:ℝ)) →
    (∀ t∈P.image entry, |(Mat t 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ ij∈P, ∀ i, x ij i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, x ij i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, |(anchor ij:ℝ)-(rat ij 0:ℝ)| ≤ ε) →
    (∀ ij∈P, 256*((anchor ij).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ij∈P, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor ij).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let AupperConst := 2*Cupper*(Cthird+1)*E^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*E^2/Lunit^2+Dupper*(B+1)*E^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*E/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let CostUpper := M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := R^4/((N:ℝ)^2*(Uref:ℝ))
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 2=0 ∧ Mat t 3=1 ∧ Mat t 1=t) →
      (P.card:ℝ) ≤ (240*CostUpper*
        (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+
          2*BupperConst+(3/2:ℝ)*DupperConst))*T^εloss) ∧
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 1=0 ∧ Mat t 3=1 ∧ Mat t 2=t) →
      (P.card:ℝ) ≤ (240*CostLower*
        (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+
          2*BlowerConst+(3/2:ℝ)*DlowerConst))*T^εloss) := by
  pm_2479 hmassFn positive_difference_actual_fourier_triangular_original_source_regime_mass
  pm_2478
  intro σ Jref εloss E θ hσ hJref hεloss
  let Du := θ*(3*Usrc/σsrc)*E/2
  let Dl := 12*Usrc*θ/(csrc*modelPhaseThirdLower σ)
  have hhalf : 0 < εloss/2 := by positivity
  filter_upwards [nativeHuxleyReference_eventually_physical_reference_chart_budgets hσ hJref hhalf,
    eventually_triangular_source_log_losses (Du:=Du) (Dl:=Dl) hhalf]
    with T hbudgets hlogs
  intro Fsrc η ya yb Tsrc chartKey Uref Refs Gaps Bselect P entry Mat gap
    N za zb AlenA AlenB Za Zb Q K₀ inst rat vinv parity anchor e r v s
    δ M R base Bcut A W x
    hMat hη hηsmall hya hyb hreg hjets htests hTsrc hMtwo hsourceScale
    hentry hbase hxa hxb hgapMem hgeometryA hgeometryB hregime
    lambda yp F chartColor hchartColor
    hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hden hθ hθmax
    hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref
    hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
    hselectedUpper hscaleTen hfamilyGap hgap
    hQN hNM hUR hrHeight hsHeight heHeight hvHeight
    ε sourceColor hsourceColor f hlevel q mu ell b cround tau dual cloud radius
    hcolor hnear κ Cphys c J B hsmall hNR hRN hNcube hminscale
    hMatdet hMatt hMatmap hMatgamma H hNtwo hL hU hanchor hcut hcount
    C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Lunit Gamma Cthird AupperConst BupperConst AlowerConst BlowerConst
    DupperConst DlowerConst CostUpper CostLower
  pm_1727
  pm_883
  pm_1533
  let DupperCut := θ*Uband
  let DlowerCut := θ/lambda
  have hraw :
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 2=0 ∧ Mat t 3=1 ∧ Mat t 1=t) →
      (P.card:ℝ) ≤ 240*(m0:ℝ)*CostUpper*
        (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)*(Real.log T)+
          2*BupperConst*(3+2*Real.log (DupperCut+2))+
          (3/2:ℝ)*DupperConst*(Real.log T)^((3:ℝ)/2))) ∧
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 1=0 ∧ Mat t 3=1 ∧ Mat t 2=t) →
      (P.card:ℝ) ≤ 240*(m0:ℝ)*CostLower*
        (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)*(Real.log T)+
          2*BlowerConst*(3+2*Real.log (DlowerCut+2))+
          (3/2:ℝ)*DlowerConst*(Real.log T)^((3:ℝ)/2))) := by
    exact hmassFn Fsrc η ya yb Tsrc E (Real.log T) chartKey Uref Refs Gaps (Bselect:=Bselect)
      P entry Mat gap Bmajor Cmajor N za zb AlenA AlenB Za Zb Q K₀
      rat vinv parity anchor e r v s
      (σ:=σ) (δ:=δ) (T:=T) (M:=M) (R:=R) (base:=base) (Bcut:=Bcut)
      (θ:=θ) A (W:=W) (x:=x)
      hMat hη hηsmall hya hyb hreg hjets htests hTsrc hMtwo hsourceScale
      hentry hbase hxa hxb hgapMem hgeometryA hgeometryB hlogs.1 hregime hchartColor
      hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hden
      hθ hθmax hinv hchart horientation hBcut hs hrefSet hparentSet hsep
      hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth
      hRQ hselectedUpper hscaleTen hfamilyGap hgap
      hsourceColor hlevel hcolor hnear hsmall hNR hRN hNcube hminscale
      hMatdet hMatt hMatmap hMatgamma hNtwo hL hU hanchor hcut hcount
      hsize hD hΔ hBsize hBmajor hCmajor
  pm_2484
  pm_1693
  pm_2488
  pm_2480
  obtain ⟨hBnonneg,hCthird⟩ := physical_source_triangular_constants_nonneg hσ hδ₀
  pm_2487
  have hcuts := triangular_physical_cutoff_height hT
    (by linarith only [hMtwo] : 1 ≤ M) hR hRN hNM hscale hDUc hDLc
  have hupper : DupperCut ≤ DupperConst*T := by
    calc
      _ = DupperConst*T/M^2 := by
        dsimp only [DupperCut,Uband,DupperConst]
        ring
      _ ≤ _ := hcuts.1
  have hlower : DlowerCut ≤ DlowerConst*T := by
    calc
      _ = DlowerConst*M^2/T := by
        dsimp only [DlowerCut,lambda,DlowerConst,κ]
        field_simp
      _ ≤ _ := hcuts.2
  pm_2156 hupper0 DupperCut Uband
  pm_2156 hlower0 DlowerCut lambda
  constructor
  · intro htri
    exact triangular_logarithmic_mass_absorption hT (Nat.cast_nonneg m0)
      hCostU hAU hBU hDUc (hraw.1 htri) hcost hlogs.2.1 hlogs.2.2.1
      (hlogs.2.2.2.1 DupperCut hupper0 hupper)
  · intro htri
    exact triangular_logarithmic_mass_absorption hT (Nat.cast_nonneg m0)
      hCostL hAL hBL hDLc (hraw.2 htri) hcost hlogs.2.1 hlogs.2.2.1
      (hlogs.2.2.2.2 DlowerCut hlower0 hlower)


                                                                    
                                                                             
                                                                                
theorem positive_difference_actual_source_joint_twelfth_partition
    {ι : Type*} (S : Finset ι) (Fsrc : ℝ → ℝ)
    (y z : ι → ℝ) (rat : ι → ℚ) (Q : ℕ)
    {σsrc csrc Usrc η Tsrc T M E σ δ θ a : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hTsrc : 0 < Tsrc) (hT : 0 < T) (hM : 0 < M)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hscale : Tsrc ≤ E*T) (hQ : 0 < Q) (hθ : 0 < θ) (ha : 0 < a)
    (hy : ∀ i∈S, y i∈Icc (1:ℝ) 2)
    (hz : ∀ i∈S, z i∈Icc M (2*M))
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w)
    (hjets : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|)
    (hden : ∀ i∈S, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den) :
    let Fmodel := fun i u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*y i))/(σsrc*η)
    (∀ i∈S, Expdb.IsApproximateModelPhaseFunction (Fmodel i) σ 2 δ) →
    let f := fun p w => Tsrc*(Fsrc (w/M)-Fsrc (w/M+η*p))/(σsrc*η)
    (∀ i∈S, iteratedDeriv 2 (f (y i)) (z i)/2=(rat i:ℝ)) →
    let Hsrc := fun p : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc p.2-iteratedDeriv 2 Fsrc (p.2+η*p.1))/(σsrc*η)
    let lambda := csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2)
    let u := fun i => (2*M^2/Tsrc)*(rat i:ℝ)
    let w := fun i => (Tsrc/(2*M^2))*(rat i:ℝ)⁻¹
    let chart := fun i => (⌊y i/a⌋,⌊u i/a⌋,⌊w i/a⌋)
    let narrow := fun i =>
      (⌊((rat i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
       ⌊((rat i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    let qell := fun i => ((rat i).den:ℝ)*deriv (f (y i)) (round (z i))
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let offset := fun ip : ι × Fin 2 => ⌊qell ip.1⌋+(ip.2:ℕ)-round (qell ip.1)
    let color := fun ip : ι × Fin 2 => (chart ip.1,narrow ip.1,offset ip)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2*E/(σsrc*csrc*modelPhaseThirdLower σ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap
    ((V.image color).card:ℝ) ≤ Cap ∧
    (∀ key∈V.image color, ∃ iref∈S, chart iref=key.1 ∧
      let xcenter := z iref/M
      let ycenter := y iref
      xcenter∈Icc (1:ℝ) 2 ∧ ycenter∈Icc (1:ℝ) 2 ∧
      ∀ ip∈V, color ip=key →
        ‖((y ip.1,u ip.1):ℝ × ℝ)-(ycenter,Hsrc (ycenter,xcenter))‖ < a ∧
        ‖((y ip.1,w ip.1):ℝ × ℝ)-(ycenter,(Hsrc (ycenter,xcenter))⁻¹)‖ < a) ∧
    (∀ ip∈V, ∀ jp∈V, color ip=color jp →
      |((rat jp.1).den:ℝ)/(rat ip.1).den-1| ≤ θ ∧
      |((rat jp.1).num:ℝ)/(rat ip.1).num-1| ≤ θ ∧ offset ip=offset jp) ∧
    ∀ coeff : ι × Fin 2 → ℂ, ‖∑ ip∈V,coeff ip‖^12 ≤
      Cap^11*∑ key∈V.image color,
        ‖∑ ip∈V.filter (fun ip => color ip=key),coeff ip‖^12 := by
  classical
  intro Fmodel hmodel f hlevel Hsrc lambda u w chart narrow qell V offset color ChartCap NarrowCap Cap
  have hκ : 0 < modelPhaseThirdLower σ := modelPhaseThirdLower_pos hσ
  pm_7677 hscale
  pm_1626
  pm_1533
  have hband i (hi : i∈S) : lambda ≤ |(rat i:ℝ)| ∧ |(rat i:ℝ)| ≤ Uband := by
    have hb := positive_difference_model_normalized_curvature_band Fsrc
      hσsrc hcsrc hUsrc hη hηmax (hy i hi) hTsrc hT hM hσ hδ hscale
      hreg hjets htests (hmodel i hi)
    rw [←hlevel i hi]
    exact hb (y i) (hy i hi) (z i) (hz i hi)
  have hchart := positive_difference_source_chart_twelfth_partition S Fsrc y z rat
    hσsrc hcsrc hUsrc hη hηmax hTsrc hM ha hy hz hreg hjets htests hlevel
  have hnarrow := rational_narrow_band_twelfth_partition S rat Q
    (U:=Uband) hQ hlambda (by dsimp only [Uband]; positivity) hθ hband hden
  have hNcap : (4/θ+3)*(4*Uband/(lambda*θ)+3)=NarrowCap := by
    dsimp only [Uband,lambda,NarrowCap]
    field_simp
    ring
  dsimp only at hnarrow
  rw [hNcap] at hnarrow
  have hoffset := fourier_parity_round_partition S qell
  have hV (ip : ι × Fin 2) (hip : ip∈V) : ip.1∈S := (Finset.mem_product.mp hip).1
  have hsub : V.image color ⊆
      (S.image chart) ×ˢ ((S.image narrow) ×ˢ (V.image offset)) := by
    pm_2532 key hkey ip hip
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem chart (hV ip hip),
      Finset.mem_product.mpr ⟨Finset.mem_image_of_mem narrow (hV ip hip),
        Finset.mem_image_of_mem offset hip⟩⟩
  pm_82 hCnon ChartCap
  pm_82 hNnon NarrowCap
  have hcard : ((V.image color).card:ℝ) ≤ Cap := by
    pm_7459
    have hreal : ((V.image color).card:ℝ) ≤
        ((S.image chart).card:ℝ)*(((S.image narrow).card:ℝ)*((V.image offset).card:ℝ)) := by
      exact_mod_cast hh
    have ho : ((V.image offset).card:ℝ) ≤ 3 := by exact_mod_cast hoffset.2.1
    apply hreal.trans
    calc
      _ ≤ ChartCap*(NarrowCap*3) := mul_le_mul hchart.1
        (mul_le_mul hnarrow.1 ho (Nat.cast_nonneg _) hNnon)
        (by positivity) hCnon
      _ = Cap := by dsimp only [Cap]; ring
  refine ⟨hcard,?_,?_,?_⟩
  · intro key hkey
    obtain ⟨ip,hip,he⟩ := Finset.mem_image.mp hkey
    have hk : key.1∈S.image chart := by
      rw [←he]
      exact Finset.mem_image_of_mem chart (hV ip hip)
    obtain ⟨iref,hiref,hkeyref,hxcenter,hycenter,hlocal⟩ := hchart.2.1 key.1 hk
    pm_164 iref hiref hkeyref hxcenter hycenter
    intro jp hjp hjkey
    exact hlocal jp.1 (hV jp hjp) (congrArg Prod.fst hjkey)
  · intro ip hip jp hjp he
    have hn := hnarrow.2.1 ip.1 (hV ip hip) jp.1 (hV jp hjp)
      (congrArg (fun k : (ℤ × ℤ × ℤ) × (ℤ × ℤ) × ℤ => k.2.1) he)
    exact ⟨hn.1,hn.2,congrArg (fun k : (ℤ × ℤ × ℤ) × (ℤ × ℤ) × ℤ => k.2.2) he⟩
  · intro coeff
    pm_7042 Keys key coeff
    pm_1848 key Keys ip V coeff hip
    have hh : (∑ key∈Keys,‖g key‖)^12 ≤ (Keys.card:ℝ)^11*∑ key∈Keys,‖g key‖^12 := by
      pm_1905
    exact (hp.trans hh).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 11)
      (Finset.sum_nonneg (fun _ _ => by positivity)))


                                                                         
                                                                
public  theorem huxley_completed_colored_source_sieve {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (K₀ : ℕ) [NeZero K₀] (Vscale : ℝ), 1 ≤ Vscale →
      ∀ (ι : Type huxleyNarrowV) (S : Finset ι) (x : ι → Fin 4 → ℝ)
      {κ : Type*} [DecidableEq κ] (color : ι → κ) (Cap : ℝ),
      (∀ i∈S, |x i 2| ≤ Real.sqrt K₀ ∧ |x i 3| ≤ Real.sqrt K₀) →
      ((S.image color).card:ℝ) ≤ Cap →
      let w := fun i => (![Int.fract (x i 0),Int.fract (x i 1),
        x i 2/Real.sqrt K₀,x i 3/Real.sqrt K₀] : Fin 4 → ℝ)
      let radius : Fin 4 → ℝ :=
        ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2*Vscale),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
      let Fiber := fun key => S.filter (fun i => color i=key)
      let P := fun key => ((Fiber key) ×ˢ (Fiber key)).filter
        (fun ij => ∀ d, |w ij.1 d-w ij.2 d| ≤ 2*radius d)
      ∀ k : ZMod K₀,
        (∑ i∈S, ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
          GafniTao.fordAdditiveCharacter (∑ d,x i d*
            (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
              Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
          C*Vscale*(K₀:ℝ)^((12:ℝ)+ε)*Cap^11*
            ∑ key∈S.image color,((Fiber key).card:ℝ)^10*((P key).card:ℝ) := by
  classical
  obtain ⟨C,hC,hsieve⟩ := nativeHuxleyReference_huxley_completed_narrowed_source_sieve.{huxleyNarrowV} hε
  refine ⟨C,hC,?_⟩
  intro K₀ inst Vscale hV ι S x κ instKey color Cap hx hcap w radius Fiber P k
  let mass := fun i => ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
    GafniTao.fordAdditiveCharacter (∑ d,x i d*
      (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
        Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖
  let Keys := S.image color
  let g := fun key => ∑ i∈Fiber key,mass i
  have hmass i : 0 ≤ mass i := norm_nonneg _
  have hg key : 0 ≤ g key := Finset.sum_nonneg (fun i _ => hmass i)
  have he : (∑ key∈Keys,g key)=∑ i∈S,mass i :=
    Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem color hi) mass
  pm_7030 Keys g key hg
  have hh : (∑ key∈Keys,g key)^12 ≤
      (Keys.card:ℝ)^11*∑ key∈Keys,(g key)^12 := by
    pm_1905
  have hcost : (∑ i∈S,mass i)^12 ≤ Cap^11*∑ key∈Keys,(g key)^12 := by
    rw [←he]
    exact hh.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hcap 11)
      (Finset.sum_nonneg (fun key _ => pow_nonneg (hg key) 12)))
  have hfiber key : (g key)^12 ≤
      C*Vscale*(K₀:ℝ)^((12:ℝ)+ε)*((Fiber key).card:ℝ)^10*((P key).card:ℝ) := by
    exact hsieve K₀ Vscale hV ι (Fiber key) x
      (fun i hi => hx i (Finset.mem_filter.mp hi).1) k
  have hCap : 0 ≤ Cap := (Nat.cast_nonneg (S.image color).card).trans hcap
  change (∑ i∈S,mass i)^12 ≤ _
  calc
    _ ≤ Cap^11*∑ key∈Keys,(g key)^12 := hcost
    _ ≤ Cap^11*∑ key∈Keys,
        (C*Vscale*(K₀:ℝ)^((12:ℝ)+ε)*((Fiber key).card:ℝ)^10*((P key).card:ℝ)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun key _ => hfiber key))
        (pow_nonneg hCap 11)
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro key _
      ring


                                                                        
                                                                              
                                                                          
                                                              
theorem exists_positive_difference_actual_joint_source_sieve
    {εloss : ℝ} (hεloss : 0 < εloss) :
    ∃ C > (0:ℝ),
    ∀ {ι : Type huxleyNarrowV} [DecidableEq ι], ∀ (S : Finset ι) (Fsrc : ℝ → ℝ)
    (y z : ι → ℝ) (rat : ι → ℚ) (v : ι → ℤ) (Nlen : ι → ℕ)
    (Q K₀ : ℕ) [NeZero K₀] (Vscale Nphys Rphys : ℝ)
    {σsrc csrc Usrc η Tsrc T M E σ δ θ a : ℝ},
    (0 < σsrc) →
    (0 < csrc) →
    (0 < Usrc) →
    (0 < η) →
    (η ≤ 1/8) →
    (0 < Tsrc) →
    (0 < T) →
    (0 < M) →
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (Tsrc ≤ E*T) →
    (0 < Q) →
    (0 < θ) →
    (0 < a) →
    (θ < 1) →
    (∀ i∈S, y i∈Icc (1:ℝ) 2) →
    (∀ i∈S, z i∈Icc M (2*M)) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ i∈S, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den) →
    (∀ i∈S, ((rat i).den:ℤ) ∣ (rat i).num*v i-1) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (2 ≤ M) →
    (1 ≤ Vscale) →
    (0 < Nphys) →
    ((Q:ℝ)*Nphys ≤ (K₀:ℝ)*Rphys^2) →
    let Fmodel := fun i u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*y i))/(σsrc*η)
    (∀ i∈S, Expdb.IsApproximateModelPhaseFunction (Fmodel i) σ 2 δ) →
    let f := fun p w => Tsrc*(Fsrc (w/M)-Fsrc (w/M+η*p))/(σsrc*η)
    (∀ i∈S, iteratedDeriv 2 (f (y i)) (z i)/2=(rat i:ℝ)) →
    (∀ i∈S, 1 ≤ Nlen i ∧ (rat i).den ≤ Nlen i ∧
      1 ≤ (iteratedDeriv 3 (f (y i)) (round (z i))/6)*((rat i).den:ℝ)^2*Nlen i) →
    (∀ i∈S, 7*((iteratedDeriv 3 (f (y i)) (round (z i))/6)*
      ((rat i).den:ℝ)*(Nlen i:ℝ)^2) ≤ K₀) →
    let Hsrc := fun p : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc p.2-iteratedDeriv 2 Fsrc (p.2+η*p.1))/(σsrc*η)
    let lambda := csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*E*T/(2*M^2)
    let u := fun i => (2*M^2/Tsrc)*(rat i:ℝ)
    let w := fun i => (Tsrc/(2*M^2))*(rat i:ℝ)⁻¹
    let chart := fun i => (⌊y i/a⌋,⌊u i/a⌋,⌊w i/a⌋)
    let narrow := fun i =>
      (⌊((rat i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
       ⌊((rat i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    let qell := fun i => ((rat i).den:ℝ)*deriv (f (y i)) (round (z i))
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let offset := fun ip : ι × Fin 2 => ⌊qell ip.1⌋+(ip.2:ℕ)-round (qell ip.1)
    let color := fun ip : ι × Fin 2 => (chart ip.1,narrow ip.1,offset ip)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2*E/(σsrc*csrc*modelPhaseThirdLower σ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap

    let q := fun i => (rat i).den
    let μ := fun i => iteratedDeriv 3 (f (y i)) (round (z i))/6
    let ell := fun i => deriv (f (y i)) (round (z i))
    let b := fun ip : ι × Fin 2 => (⌊qell ip.1⌋+(ip.2:ℕ) : ℤ)
    let tau := fun ip : ι × Fin 2 => ((b ip:ℝ)-qell ip.1)/2
    let dual := fun i => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun ip : ι × Fin 2 =>
      (![-(v ip.1:ℝ)*b ip/q ip.1,-(v ip.1:ℝ)/q ip.1,
        dual ip.1,3*dual ip.1*tau ip/2] : Fin 4 → ℝ)
    let cloud := fun ip => (![Int.fract (x ip 0),Int.fract (x ip 1),
      x ip 2/Real.sqrt K₀,x ip 3/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2*Vscale),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    let Pall := (V ×ˢ V).filter (fun ij => ∀ d, |cloud ij.1 d-cloud ij.2 d| ≤ 2*radius d)
    let Fiber := fun key => V.filter (fun ip => color ip=key)
    let Pairs := fun key => ((Fiber key) ×ˢ (Fiber key)).filter
      (fun ij => ∀ d, |cloud ij.1 d-cloud ij.2 d| ≤ 2*radius d)
    let μ₀ := csrc*Tsrc/(12*σsrc*M^3)
    let U₀ := Usrc*Tsrc/(2*σsrc*M^3)
    let h := fun i => iteratedDeriv 2 (f (y i)) (z i)/2
    let D := (Real.sqrt K₀/(9*(K₀:ℝ))+Real.sqrt K₀/(12*(K₀:ℝ)^2))*
      Real.sqrt (U₀*(Q:ℝ)^3)
    ((V.image color).card:ℝ) ≤ Cap ∧
    (∀ key∈V.image color, ∃ iref∈S, chart iref=key.1 ∧
      let xcenter := z iref/M
      let ycenter := y iref
      xcenter∈Icc (1:ℝ) 2 ∧ ycenter∈Icc (1:ℝ) 2 ∧
      ∀ ip∈V, color ip=key →
        ‖((y ip.1,u ip.1):ℝ × ℝ)-(ycenter,Hsrc (ycenter,xcenter))‖ < a ∧
        ‖((y ip.1,w ip.1):ℝ × ℝ)-(ycenter,(Hsrc (ycenter,xcenter))⁻¹)‖ < a) ∧
    (∀ ip∈V, ∀ jp∈V, color ip=color jp →
      |((rat jp.1).den:ℝ)/(rat ip.1).den-1| ≤ θ ∧
      |((rat jp.1).num:ℝ)/(rat ip.1).num-1| ≤ θ ∧ offset ip=offset jp) ∧
    ∃ Mat : ((ι × Fin 2) × (ι × Fin 2)) → Fin 4 → ℤ,
      (∀ k : ZMod K₀,
        (∑ ip∈V, ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
          GafniTao.fordAdditiveCharacter (∑ d,x ip d*
            (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
              Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
          C*Vscale*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
            ∑ key∈V.image color,((Fiber key).card:ℝ)^10*((Pairs key).card:ℝ)) ∧
      (∀ ij∈Pall,
        Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1 ∧
        let t := (Mat ij 2:ℝ)*h ij.1.1+Mat ij 3
        t=(q ij.2.1:ℝ)/q ij.1.1 ∧ (1:ℝ)/2 ≤ t ∧ t ≤ 2 ∧
        ((Mat ij 0:ℝ)*h ij.1.1+Mat ij 1)/t=h ij.2.1 ∧
        |(Mat ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) ∧
        |μ ij.2.1/μ ij.1.1*t^3-1| ≤
          (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2) ∧
        |tau ij.1-tau ij.2| ≤ D ∧
        (∃ e₁ e₂ : ℤ,
          let F₁ := 2*(round (z ij.2.1):ℝ)-2*(Mat ij 3:ℝ)*(round (z ij.1.1):ℝ)-
            (Mat ij 2:ℝ)*ell ij.1.1
          let F₂ := ell ij.2.1-2*(Mat ij 1:ℝ)*(round (z ij.1.1):ℝ)-
            (Mat ij 0:ℝ)*ell ij.1.1
          |F₁-e₁| ≤ (q ij.2.1:ℝ)/(6*(K₀:ℝ))+|(Mat ij 2:ℝ)|/q ij.1.1 ∧
          |(F₂-e₂)-h ij.2.1*(F₁-e₁)| ≤ 2*D/q ij.2.1) ∧
        ((Q:ℝ)^2/(6*(K₀:ℝ)^2) < 1 →
          Mat ij 2=0 ∧ q ij.1.1=q ij.2.1 ∧
            (q ij.1.1:ℤ) ∣ (rat ij.2.1).num-(rat ij.1.1).num)) ∧
      (∀ ij∈Pall, |(Mat ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2*Vscale) ∧
        |(Mat ij 2:ℝ)| ≤ Rphys^4/(6*Nphys^2*Vscale)) ∧
      (∀ key, ∀ ij∈Pairs key,
        (Mat ij 0=1 ∧ Mat ij 1=0 ∧ Mat ij 2=0 ∧ Mat ij 3=1) ∨
        (Mat ij 0=1 ∧ Mat ij 3=1 ∧ Mat ij 2=0 ∧ Mat ij 1≠0 ∧
          |(Mat ij 1:ℝ)| ≤ θ*Uband) ∨
        (Mat ij 0=1 ∧ Mat ij 3=1 ∧ Mat ij 1=0 ∧ Mat ij 2≠0 ∧
          |(Mat ij 2:ℝ)| ≤ θ/lambda) ∨
        (Mat ij 1≠0 ∧ Mat ij 2≠0)) := by
  classical
  obtain ⟨C,hC,hcolored⟩ := huxley_completed_colored_source_sieve.{huxleyNarrowV} hεloss
  obtain ⟨_,_,hmatrices⟩ := exists_source_arc_fourier_narrowed_sieve_matrices.{huxleyNarrowV} hεloss
  refine ⟨C,hC,?_⟩
  intro ι inst S Fsrc y z rat v Nlen Q K₀ instK Vscale Nphys Rphys
    σsrc csrc Usrc η Tsrc T M E σ δ θ a
    hσsrc hcsrc hUsrc hη hηmax hTsrc hT hM hσ hδ hscale hQ hθ ha hθmax
    hy hz hreg hjets htests hden hinv hnegative hMtwo hVscale hNphys hmesh
    Fmodel hmodel f hlevel hminor hcomplete Hsrc lambda Uband u w chart narrow
    qell V offset color ChartCap NarrowCap Cap
    q μ ell b tau dual x cloud radius Pall Fiber Pairs μ₀ U₀ h D
  have hjoint := positive_difference_actual_source_joint_twelfth_partition S Fsrc y z rat Q
    hσsrc hcsrc hUsrc hη hηmax hTsrc hT hM hσ hδ hscale hQ hθ ha
    hy hz hreg hjets htests hden hmodel hlevel
  pm_1849
  have hμbounds i (hi : i∈S) : μ₀ ≤ μ i ∧ μ i ≤ U₀ := by
    have hb := positive_difference_rounded_cubic_scales Fsrc (T:=Tsrc) (N:=M^3/Tsrc) (R:=1)
      hσsrc hcsrc hUsrc hη hηmax (hy i hi) hreg hjets hnegative hMtwo
      (by positivity) (by norm_num) (hz i hi) (by field_simp)
    have hlo : csrc/(12*σsrc*(M^3/Tsrc)*(1:ℝ)^2)=μ₀ := by
      dsimp only [μ₀]
      field_simp
    have hhi : Usrc/(2*σsrc*(M^3/Tsrc)*(1:ℝ)^2)=U₀ := by
      dsimp only [U₀]
      field_simp
    rw [hlo,hhi] at hb
    exact hb
  obtain ⟨Mat,_hglobalSum,hglobal,hnarrow⟩ := hmatrices ι S (fun i => f (y i)) z rat v
    Q K₀ μ₀ U₀ hμ₀ hμbounds hlevel hden hinv Nlen Vscale Nphys Rphys
    hVscale hNphys hmesh hminor hcomplete
  have hbox ip (hip : ip∈V) :
      |x ip 2| ≤ Real.sqrt K₀ ∧ |x ip 3| ≤ Real.sqrt K₀ := by
    have hi := (Finset.mem_product.mp hip).1
    exact nativeHuxleyReference_huxley_actual_dual_source_box (rat ip.1).pos
      (hminor ip.1 hi).1 (hminor ip.1 hi).2.1
      (hμ₀.trans_le (hμbounds ip.1 hi).1) (hminor ip.1 hi).2.2
      (hcomplete ip.1 hi) (v ip.1) ip.2
  refine ⟨hjoint.1,hjoint.2.1,hjoint.2.2.1,Mat,?_,hglobal,hnarrow,?_⟩
  · intro k
    exact hcolored K₀ Vscale hVscale (ι × Fin 2) V x color Cap hbox hjoint.1 k
  · intro key ij hij
    have hp := Finset.mem_filter.mp hij
    pm_2490
    have hiall := (Finset.mem_product.mp hi.1).1
    have hjall := (Finset.mem_product.mp hj.1).1
    have hijall : ij∈Pall := Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hi.1,hj.1⟩,hp.2⟩
    have hsides := hjoint.2.2.1 ij.1 hi.1 ij.2 hj.1 (hi.2.trans hj.2.symm)
    pm_529 hdet ht _htlo _hthi hmap _hrest hglobal ij hijall
    simp only [hlevel ij.1.1 hiall,hlevel ij.2.1 hjall] at ht hmap
    have hlambda : 0 < lambda := by
      have hκ := modelPhaseThirdLower_pos hσ
      dsimp only [lambda]
      positivity
    have hband := positive_difference_model_normalized_curvature_band Fsrc
      hσsrc hcsrc hUsrc hη hηmax (hy ij.1.1 hiall) hTsrc hT hM hσ hδ hscale
      hreg hjets htests (hmodel ij.1.1 hiall)
    have hcurv : lambda ≤ |(rat ij.1.1:ℝ)| ∧ |(rat ij.1.1:ℝ)| ≤ Uband := by
      rw [←hlevel ij.1.1 hiall]
      exact hband _ (hy ij.1.1 hiall) _ (hz ij.1.1 hiall)
    have hx : (rat ij.1.1:ℝ)≠0 := abs_pos.mp (hlambda.trans_le hcurv.1)
    have htpos : 0 < (Mat ij 2:ℝ)*(rat ij.1.1:ℝ)+Mat ij 3 := by
      rw [ht]
      exact div_pos (by exact_mod_cast (rat ij.2.1).pos)
        (by exact_mod_cast (rat ij.1.1).pos)
    have hnumeq : ((Mat ij 0:ℝ)*(rat ij.1.1:ℝ)+Mat ij 1)/(rat ij.1.1:ℝ)=
        ((rat ij.2.1).num:ℝ)/(rat ij.1.1).num := by
      pm_8478 htpos.ne' ht
    exact narrow_band_matrix_translation_cases (Mat ij 0) (Mat ij 1) (Mat ij 2) (Mat ij 3)
      hlambda hcurv.1 hcurv.2 hθ.le hθmax hdet
      (by rw [ht]; exact hsides.1) (by rw [hnumeq]; exact hsides.2.1)


section
variable {σ c U L : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) (hL : 0 ≤ L)
include σ c U L hσ hc hU hL
private theorem positive_difference_family_bounded_action_source_scale_at_action :
    ∃ D : ℝ, 0 < D ∧
      ∀ (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
        (Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ)
        (F : ℝ → ℝ) (z : ℝ → ℤ → ℝ) (Alen : ℝ → ℤ → ℕ)
        (N : ℕ) (Z : ℝ → ℤ) (η Δ J T M : ℝ),
      0 < η → η ≤ 1/8 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 < J → (N:ℝ) ≤ M → J ≤ M →
      (∀ ij∈P,
        (ij.1.1.1∈Icc (1:ℝ) 2 ∧ z ij.1.1.1 ij.1.1.2∈Icc M (2*M)) ∧
        (ij.2.1.1∈Icc (1:ℝ) 2 ∧ z ij.2.1.1 ij.2.1.2∈Icc M (2*M))) →
      (∀ ij∈P, N ≤ Alen ij.1.1.1 ij.1.1.2 ∧ Alen ij.1.1.1 ij.1.1.2 ≤ 3*N ∧
        round (z ij.1.1.1 ij.1.1.2)+(Alen ij.1.1.1 ij.1.1.2:ℤ)=
          Z ij.1.1.1+(N:ℤ)*ij.1.1.2+2*(N:ℤ)) →
      (∀ ij∈P, N ≤ Alen ij.2.1.1 ij.2.1.2 ∧ Alen ij.2.1.1 ij.2.1.2 ≤ 3*N ∧
        round (z ij.2.1.1 ij.2.1.2)+(Alen ij.2.1.1 ij.2.1.2:ℤ)=
          Z ij.2.1.1+(N:ℤ)*ij.2.1.2+2*(N:ℤ)) →
      (∀ ij∈P, ∀ kl∈P, ij.2.1.1 ≠ kl.2.1.1 → 1 ≤ J*|ij.2.1.1-kl.2.1.1|) →
      (∀ ij∈P, Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1) →
      (∀ ij∈P, Mat ij 1 ≠ 0 ∧ Mat ij 2 ≠ 0) →
      (∀ ij∈P, |(Mat ij 2:ℝ)| * ((3*U/σ)*T/(2*M^2)) ≤ L) →
      let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
      let μ := fun y w => iteratedDeriv 3 (f y) (round w)/6
      let t := fun ij => (Mat ij 2:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 3
      (∀ ij∈P, ((Mat ij 0:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 1)/t ij=
        h ij.2.1.1 (z ij.2.1.1 ij.2.1.2)) →
      (∀ ij∈P, |t ij-1| ≤ 1/(8*(L+3))) →
      (∀ ij∈P, |((Mat ij 0:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 1)/
        h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)-1| ≤ 1/(8*(L+3))) →
      (∀ ij∈P, |μ ij.2.1.1 (z ij.2.1.1 ij.2.1.2)/
        μ ij.1.1.1 (z ij.1.1.1 ij.1.1.2)*(t ij)^3-1| ≤ Δ) →
      (P.card:ℝ) ≤ D*((P.image (fun ij => ij.1.1.1)).card:ℝ)*
        (M/(N:ℝ))*(1+Δ*J) := by
  obtain ⟨K,C,hK,hC,hcount⟩ := positive_difference_family_bounded_action_pair_count hσ hc hU
  pm_1839
  pm_2491
  pm_2546 hB B zero_lt_one.trans_le le_max_left
  pm_116 hCMat CMat
  refine ⟨60*K*(1+40*C*B)*CMat,by positivity,?_⟩
  intro P Mat F z Alen N Z η Δ J T M hη hηmax hf hbound htests hnegative
    hT hM hN hΔ hJ hNM hJM hpoints hgeometryA hgeometryB hsep hdet hnontri haction
    f h μ t hmap hden hnum hthird
  classical
  pm_1811
  pm_1815
  have hh := hcount P Mat F z Alen N Z η Δ J T M L hη hηmax hf hbound htests hnegative
    hT hM hN hΔ hJ hL hpoints hgeometryB hsep hdet hnontri haction hmap hden hnum hthird
  have hfirst := rounded_offset_family_point_count (P.image Prod.fst) z Alen N Z hMp.le hN
    (by
      pm_1830
      exact (hpoints ij hij).1.2)
    (by
      pm_1830
      exact hgeometryA ij hij)
  pm_1838
  pb_426
  calc
    (P.card:ℝ) ≤ 6*K*(1+8*C*B*(Δ+5/M)*J)*CMat*((P.image Prod.fst).card:ℝ) := hh
    _ ≤ 6*K*((1+40*C*B)*(1+Δ*J))*CMat*(10*(M/(N:ℝ))*I) := by
      gcongr
    _ = _ := by ring

private theorem positive_difference_family_type_one_source_scale_at_action :
    ∃ D : ℝ, 0 < D ∧
      ∀ (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
        (Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ)
        (F : ℝ → ℝ) (z : ℝ → ℤ → ℝ) (Alen : ℝ → ℤ → ℕ)
        (N : ℕ) (Z : ℝ → ℤ) (η Δ J T M : ℝ),
      0 < η → η ≤ 1/8 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 < J → (N:ℝ) ≤ M → J ≤ M →
      (∀ ij∈P,
        (ij.1.1.1∈Icc (1:ℝ) 2 ∧ z ij.1.1.1 ij.1.1.2∈Icc M (2*M)) ∧
        (ij.2.1.1∈Icc (1:ℝ) 2 ∧ z ij.2.1.1 ij.2.1.2∈Icc M (2*M))) →
      (∀ ij∈P, N ≤ Alen ij.1.1.1 ij.1.1.2 ∧ Alen ij.1.1.1 ij.1.1.2 ≤ 3*N ∧
        round (z ij.1.1.1 ij.1.1.2)+(Alen ij.1.1.1 ij.1.1.2:ℤ)=
          Z ij.1.1.1+(N:ℤ)*ij.1.1.2+2*(N:ℤ)) →
      (∀ ij∈P, N ≤ Alen ij.2.1.1 ij.2.1.2 ∧ Alen ij.2.1.1 ij.2.1.2 ≤ 3*N ∧
        round (z ij.2.1.1 ij.2.1.2)+(Alen ij.2.1.1 ij.2.1.2:ℤ)=
          Z ij.2.1.1+(N:ℤ)*ij.2.1.2+2*(N:ℤ)) →
      (∀ ij∈P, ∀ kl∈P, ij.2.1.1 ≠ kl.2.1.1 → 1 ≤ J*|ij.2.1.1-kl.2.1.1|) →
      (∀ ij∈P, Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1) →
      (∀ ij∈P,
        (Mat ij 0=1 ∧ Mat ij 1=0 ∧ Mat ij 2=0 ∧ Mat ij 3=1) ∨
        (Mat ij 1≠0 ∧ Mat ij 2≠0 ∧ |(Mat ij 2:ℝ)| * ((3*U/σ)*T/(2*M^2)) ≤ L)) →
      let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
      let μ := fun y w => iteratedDeriv 3 (f y) (round w)/6
      let t := fun ij => (Mat ij 2:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 3
      (∀ ij∈P, ((Mat ij 0:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 1)/t ij=
        h ij.2.1.1 (z ij.2.1.1 ij.2.1.2)) →
      (∀ ij∈P, |t ij-1| ≤ 1/(8*(L+3))) →
      (∀ ij∈P, |((Mat ij 0:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 1)/
        h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)-1| ≤ 1/(8*(L+3))) →
      (∀ ij∈P, |μ ij.2.1.1 (z ij.2.1.1 ij.2.1.2)/
        μ ij.1.1.1 (z ij.1.1.1 ij.1.1.2)*(t ij)^3-1| ≤ Δ) →
      (P.card:ℝ) ≤ D*((P.image (fun ij => ij.1.1.1)).card:ℝ)*
        (M/(N:ℝ))*(1+Δ*J) := by
  pm_114 D₀ hD₀ hzero positive_difference_family_identity_source_scale hσ hc hU
  pm_97 D₁ hD₁ hnonzero positive_difference_family_bounded_action_source_scale_at_action hσ hc hU hL
  refine ⟨D₀+D₁,add_pos hD₀ hD₁,?_⟩
  intro P Mat F z Alen N Z η Δ J T M hη hηmax hf hbound htests hnegative
    hT hM hN hΔ hJ hNM hJM hpoints hgeometryA hgeometryB hsep hdet hbranch
    f h μ t hmap hden hnum hthird
  classical
  pm_6797 P₀ P.filter P₁
  have hlo ij (hij : ij∈P₀) : ij∈P ∧ Mat ij 1=0 := Finset.mem_filter.mp hij
  have hhi ij (hij : ij∈P₁) : ij∈P ∧ Mat ij 1≠0 := Finset.mem_filter.mp hij
  have hform ij (hij : ij∈P₀) :
      Mat ij 0=1 ∧ Mat ij 1=0 ∧ Mat ij 2=0 ∧ Mat ij 3=1 := by
    rcases hbranch ij (hlo ij hij).1 with ha | ha
    · exact ha
    · exact False.elim (ha.1 (hlo ij hij).2)
  have hnontri ij (hij : ij∈P₁) :
      Mat ij 1≠0 ∧ Mat ij 2≠0 ∧ |(Mat ij 2:ℝ)| * ((3*U/σ)*T/(2*M^2)) ≤ L :=
    (hbranch ij (hhi ij hij).1).resolve_left (fun ha => (hhi ij hij).2 ha.2.1)
  have h₀ := hzero P₀ F z Alen N Z η Δ J T M hη hηmax hf hbound htests hnegative
    hT hM hN hΔ hJ hNM hJM
    (fun ij hij => hpoints ij (hlo ij hij).1)
    (fun ij hij => hgeometryA ij (hlo ij hij).1)
    (fun ij hij => hgeometryB ij (hlo ij hij).1)
    (fun ij hij kl hkl hne => hsep ij (hlo ij hij).1 kl (hlo kl hkl).1 hne)
    (by
      intro ij hij
      have ha := hform ij hij
      have hh := (hmap ij (hlo ij hij).1).symm
      dsimp only [t] at hh
      simpa only [ha.1,ha.2.1,ha.2.2.1,ha.2.2.2,Int.cast_zero,Int.cast_one,
        zero_mul,one_mul,zero_add,add_zero,div_one] using hh)
    (by
      intro ij hij
      have ha := hform ij hij
      have hh := hthird ij (hlo ij hij).1
      dsimp only [t] at hh
      simpa only [ha.2.2.1,ha.2.2.2,Int.cast_zero,Int.cast_one,zero_mul,zero_add,one_pow,mul_one]
        using hh)
  have h₁ := hnonzero P₁ Mat F z Alen N Z η Δ J T M hη hηmax hf hbound htests hnegative
    hT hM hN hΔ hJ hNM hJM
    (fun ij hij => hpoints ij (hhi ij hij).1)
    (fun ij hij => hgeometryA ij (hhi ij hij).1)
    (fun ij hij => hgeometryB ij (hhi ij hij).1)
    (fun ij hij kl hkl hne => hsep ij (hhi ij hij).1 kl (hhi kl hkl).1 hne)
    (fun ij hij => hdet ij (hhi ij hij).1)
    (fun ij hij => ⟨(hnontri ij hij).1,(hnontri ij hij).2.1⟩)
    (fun ij hij => (hnontri ij hij).2.2)
    (fun ij hij => hmap ij (hhi ij hij).1)
    (fun ij hij => hden ij (hhi ij hij).1)
    (fun ij hij => hnum ij (hhi ij hij).1)
    (fun ij hij => hthird ij (hhi ij hij).1)
  have hI₀ : ((P₀.image (fun ij => ij.1.1.1)).card:ℝ) ≤
      ((P.image (fun ij => ij.1.1.1)).card:ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.image_subset_image
      (Finset.filter_subset (fun ij => Mat ij 1=0) P))
  have hI₁ : ((P₁.image (fun ij => ij.1.1.1)).card:ℝ) ≤
      ((P.image (fun ij => ij.1.1.1)).card:ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.image_subset_image
      (Finset.filter_subset (fun ij => Mat ij 1≠0) P))
  pm_1811
  pm_1815
  pm_5002 h₀' P₀.card D₀ h₀.trans
  pm_5002 h₁' P₁.card D₁ h₁.trans
  have he : P.card=P₀.card+P₁.card := by
    exact (Finset.card_filter_add_card_filter_not (s:=P) (fun ij => Mat ij 1=0)).symm
  have heR : (P.card:ℝ)=(P₀.card:ℝ)+(P₁.card:ℝ) := by exact_mod_cast he
  rw [heR]
  calc
    _ ≤ D₀*((P.image (fun ij => ij.1.1.1)).card:ℝ)*(M/(N:ℝ))*(1+Δ*J)+
        D₁*((P.image (fun ij => ij.1.1.1)).card:ℝ)*(M/(N:ℝ))*(1+Δ*J) := add_le_add h₀' h₁'
    _ = _ := by ring
end

private theorem source_model_large_action_threshold
    {σsrc csrc Usrc E σ δ T M gamma : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hE : 0 < E) (hσ : 0 < σ) (hT : 0 < T) (hM : 0 < M)
    (hδ : δ ≤ 1) :
    let κ := modelPhaseThirdLower σ
    let lambda := csrc*κ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*E*T/(2*M^2)
    let Ratio := 18*Usrc^2*E/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)*E/κ^2)
    0 ≤ L ∧
      (L < |gamma| *Uband →
        8*Uband ≤ |gamma| *lambda^2 ∧
        64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤ |gamma| *κ^2*T) := by
  intro κ lambda Uband Ratio L
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  pm_1626
  pm_116 hUband Uband
  have hratio : Uband/lambda=Ratio := by
    dsimp only [Uband,lambda,Ratio]
    field_simp
    ring
  have hfirst : 8*Uband^2/lambda^2 ≤ L := by
    calc
      _ = 8*Ratio^2 := by rw [←hratio]; ring
      _ ≤ _ := le_max_left _ _
  have hsecond : 64*(modelPhaseJetCoefficient σ 3+1)*M^2*Uband/(κ^2*T) ≤ L := by
    calc
      _ = 32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)*E/κ^2 := by
        dsimp only [Uband]
        field_simp
        ring
      _ ≤ _ := le_max_right _ _
  refine ⟨(by dsimp only [L]; exact (by positivity : (0:ℝ) ≤ 8*Ratio^2).trans (le_max_left _ _)),?_⟩
  intro hlarge
  constructor
  · have hh := (div_le_iff₀ (sq_pos_of_pos hlambda)).mp (hfirst.trans hlarge.le)
    apply (mul_le_mul_iff_right₀ hUband).mp
    nlinarith only [hh]
  · have hh := (div_le_iff₀ (by positivity : 0 < κ^2*T)).mp (hsecond.trans hlarge.le)
    have hbound : 64*(modelPhaseJetCoefficient σ 3+1)*M^2 ≤ |gamma| *κ^2*T := by
      apply (mul_le_mul_iff_right₀ hUband).mp
      nlinarith only [hh]
    apply le_trans _ hbound
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hδ) (by norm_num : (0:ℝ) ≤ 64))
      (sq_nonneg M)


                                                                               
                                                                            
                                                                          
set_option hygiene false in
macro "pb_268" : tactic => `(tactic| (
  refine ⟨C,Dtype,hC,hDtype,?_⟩
  intro S Fsrc z rat v Nlen Q K₀ N instK Vscale Rphys Jsep Z
    η Tsrc T M δ θ a hη hηmax hTsrc hT hM hδ hscale hQ hθ ha
    hθmax hθaction hy hz hreg hjets htests hden hinv hnegative hMtwo
    hVscale hN hJsep hJM hNM hmesh hgeometry hseparation
    Fmodel hmodel f hlevel hminor hcomplete Hsrc lambda Uband u w chart narrow
    qell V offset color ChartCap NarrowCap Cap
    q μ ell b tau dual x cloud radius Pall Fiber Pairs μ₀ U₀ h D Δ))
theorem exists_positive_difference_joint_type_one_source_sieve
    {σsrc csrc Usrc E σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hE : 0 < E) (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2*E/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)*E/κ^2)
    ∃ C Dtype : ℝ, 0 < C ∧ 0 < Dtype ∧ ∀ (S : Finset (ℝ × ℤ)) (Fsrc : ℝ → ℝ)
    (z : (ℝ × ℤ) → ℝ) (rat : (ℝ × ℤ) → ℚ) (v : (ℝ × ℤ) → ℤ) (Nlen : (ℝ × ℤ) → ℕ)
    (Q K₀ N : ℕ) [NeZero K₀] (Vscale Rphys Jsep : ℝ) (Z : ℝ → ℤ)
    {η Tsrc T M δ θ a : ℝ},
    (0 < η) →
    (η ≤ 1/8) →
    (0 < Tsrc) →
    (0 < T) →
    (0 < M) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (Tsrc ≤ E*T) →
    (0 < Q) →
    (0 < θ) →
    (0 < a) →
    (θ < 1) →
    (θ ≤ 1/(8*(L+3))) →
    (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈S, z i∈Icc M (2*M)) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ i∈S, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den) →
    (∀ i∈S, ((rat i).den:ℤ) ∣ (rat i).num*v i-1) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (2 ≤ M) →
    (1 ≤ Vscale) →
    (0 < N) →
    (0 < Jsep) → (Jsep ≤ M) → ((N:ℝ) ≤ M) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*Rphys^2) →
    (∀ i∈S, N ≤ Nlen i ∧ Nlen i ≤ 3*N ∧
      round (z i)+(Nlen i:ℤ)=Z i.1+(N:ℤ)*i.2+2*(N:ℤ)) →
    (∀ i∈S, ∀ j∈S, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    let Fmodel := fun (i : ℝ × ℤ) u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*i.1))/(σsrc*η)
    (∀ i∈S, Expdb.IsApproximateModelPhaseFunction (Fmodel i) σ 2 δ) →
    let f := fun p w => Tsrc*(Fsrc (w/M)-Fsrc (w/M+η*p))/(σsrc*η)
    (∀ i∈S, iteratedDeriv 2 (f (i.1)) (z i)/2=(rat i:ℝ)) →
    (∀ i∈S, 1 ≤ Nlen i ∧ (rat i).den ≤ Nlen i ∧
      1 ≤ (iteratedDeriv 3 (f (i.1)) (round (z i))/6)*((rat i).den:ℝ)^2*Nlen i) →
    (∀ i∈S, 7*((iteratedDeriv 3 (f (i.1)) (round (z i))/6)*
      ((rat i).den:ℝ)*(Nlen i:ℝ)^2) ≤ K₀) →
    let Hsrc := fun p : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc p.2-iteratedDeriv 2 Fsrc (p.2+η*p.1))/(σsrc*η)
    let lambda := csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*E*T/(2*M^2)
    let u := fun (i : ℝ × ℤ) => (2*M^2/Tsrc)*(rat i:ℝ)
    let w := fun (i : ℝ × ℤ) => (Tsrc/(2*M^2))*(rat i:ℝ)⁻¹
    let chart := fun (i : ℝ × ℤ) => (⌊i.1/a⌋,⌊u i/a⌋,⌊w i/a⌋)
    let narrow := fun (i : ℝ × ℤ) =>
      (⌊((rat i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
       ⌊((rat i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    let qell := fun (i : ℝ × ℤ) => ((rat i).den:ℝ)*deriv (f (i.1)) (round (z i))
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let offset := fun ip : (ℝ × ℤ) × Fin 2 => ⌊qell ip.1⌋+(ip.2:ℕ)-round (qell ip.1)
    let color := fun ip : (ℝ × ℤ) × Fin 2 => (chart ip.1,narrow ip.1,offset ip)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2*E/(σsrc*csrc*modelPhaseThirdLower σ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap

    let q := fun (i : ℝ × ℤ) => (rat i).den
    let μ := fun (i : ℝ × ℤ) => iteratedDeriv 3 (f (i.1)) (round (z i))/6
    let ell := fun (i : ℝ × ℤ) => deriv (f (i.1)) (round (z i))
    let b := fun ip : (ℝ × ℤ) × Fin 2 => (⌊qell ip.1⌋+(ip.2:ℕ) : ℤ)
    let tau := fun ip : (ℝ × ℤ) × Fin 2 => ((b ip:ℝ)-qell ip.1)/2
    let dual := fun (i : ℝ × ℤ) => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun ip : (ℝ × ℤ) × Fin 2 =>
      (![-(v ip.1:ℝ)*b ip/q ip.1,-(v ip.1:ℝ)/q ip.1,
        dual ip.1,3*dual ip.1*tau ip/2] : Fin 4 → ℝ)
    let cloud := fun ip => (![Int.fract (x ip 0),Int.fract (x ip 1),
      x ip 2/Real.sqrt K₀,x ip 3/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2*Vscale),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    let Pall := (V ×ˢ V).filter (fun ij => ∀ d, |cloud ij.1 d-cloud ij.2 d| ≤ 2*radius d)
    let Fiber := fun key => V.filter (fun ip => color ip=key)
    let Pairs := fun key => ((Fiber key) ×ˢ (Fiber key)).filter
      (fun ij => ∀ d, |cloud ij.1 d-cloud ij.2 d| ≤ 2*radius d)
    let μ₀ := csrc*Tsrc/(12*σsrc*M^3)
    let U₀ := Usrc*Tsrc/(2*σsrc*M^3)
    let h := fun (i : ℝ × ℤ) => iteratedDeriv 2 (f (i.1)) (z i)/2
    let D := (Real.sqrt K₀/(9*(K₀:ℝ))+Real.sqrt K₀/(12*(K₀:ℝ)^2))*
      Real.sqrt (U₀*(Q:ℝ)^3)
    let Δ := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    ((V.image color).card:ℝ) ≤ Cap ∧
    (∀ key∈V.image color, ∃ iref∈S, chart iref=key.1 ∧
      let xcenter := z iref/M
      let ycenter := iref.1
      xcenter∈Icc (1:ℝ) 2 ∧ ycenter∈Icc (1:ℝ) 2 ∧
      ∀ ip∈V, color ip=key →
        ‖((ip.1.1,u ip.1):ℝ × ℝ)-(ycenter,Hsrc (ycenter,xcenter))‖ < a ∧
        ‖((ip.1.1,w ip.1):ℝ × ℝ)-(ycenter,(Hsrc (ycenter,xcenter))⁻¹)‖ < a) ∧
    (∀ ip∈V, ∀ jp∈V, color ip=color jp →
      |((rat jp.1).den:ℝ)/(rat ip.1).den-1| ≤ θ ∧
      |((rat jp.1).num:ℝ)/(rat ip.1).num-1| ≤ θ ∧ offset ip = offset jp) ∧
    ∃ Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ,
      (∀ k : ZMod K₀,
        (∑ ip∈V, ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
          GafniTao.fordAdditiveCharacter (∑ d,x ip d*
            (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
              Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
          C*Vscale*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
            ∑ key∈V.image color,((Fiber key).card:ℝ)^10*((Pairs key).card:ℝ)) ∧
      (∀ ij∈Pall,
        Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1 ∧
        let t := (Mat ij 2:ℝ)*h ij.1.1+Mat ij 3
        t=(q ij.2.1:ℝ)/q ij.1.1 ∧ (1:ℝ)/2 ≤ t ∧ t ≤ 2 ∧
        ((Mat ij 0:ℝ)*h ij.1.1+Mat ij 1)/t=h ij.2.1 ∧
        |(Mat ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) ∧
        |μ ij.2.1/μ ij.1.1*t^3-1| ≤
          (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2) ∧
        |tau ij.1-tau ij.2| ≤ D ∧
        (∃ e₁ e₂ : ℤ,
          let F₁ := 2*(round (z ij.2.1):ℝ)-2*(Mat ij 3:ℝ)*(round (z ij.1.1):ℝ)-
            (Mat ij 2:ℝ)*ell ij.1.1
          let F₂ := ell ij.2.1-2*(Mat ij 1:ℝ)*(round (z ij.1.1):ℝ)-
            (Mat ij 0:ℝ)*ell ij.1.1
          |F₁-e₁| ≤ (q ij.2.1:ℝ)/(6*(K₀:ℝ))+|(Mat ij 2:ℝ)|/q ij.1.1 ∧
          |(F₂-e₂)-h ij.2.1*(F₁-e₁)| ≤ 2*D/q ij.2.1) ∧
        ((Q:ℝ)^2/(6*(K₀:ℝ)^2) < 1 →
          Mat ij 2=0 ∧ q ij.1.1=q ij.2.1 ∧
            (q ij.1.1:ℤ) ∣ (rat ij.2.1).num-(rat ij.1.1).num)) ∧
      (∀ ij∈Pall, |(Mat ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2*Vscale) ∧
        |(Mat ij 2:ℝ)| ≤ Rphys^4/(6*(N:ℝ)^2*Vscale)) ∧
      (∀ key, ∀ ij∈Pairs key,
        (Mat ij 0=1 ∧ Mat ij 1=0 ∧ Mat ij 2=0 ∧ Mat ij 3=1) ∨
        (Mat ij 0=1 ∧ Mat ij 3=1 ∧ Mat ij 2=0 ∧ Mat ij 1≠0 ∧
          |(Mat ij 1:ℝ)| ≤ θ*Uband) ∨
        (Mat ij 0=1 ∧ Mat ij 3=1 ∧ Mat ij 1=0 ∧ Mat ij 2≠0 ∧
          |(Mat ij 2:ℝ)| ≤ θ/lambda) ∨
        (Mat ij 1≠0 ∧ Mat ij 2≠0)) ∧
      let TypeOne := fun key => (Pairs key).filter (fun ij =>
        (Mat ij 0=1 ∧ Mat ij 1=0 ∧ Mat ij 2=0 ∧ Mat ij 3=1) ∨
        (Mat ij 1≠0 ∧ Mat ij 2≠0 ∧ |(Mat ij 2:ℝ)| * Uband ≤ L))
      ∀ key, (((TypeOne key).card:ℝ) ≤
        Dtype*((S.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+Δ*Jsep)) ∧
        (∀ ij∈Pairs key, ij∉TypeOne key →
          (Mat ij 0=1 ∧ Mat ij 3=1 ∧ Mat ij 2=0 ∧ Mat ij 1≠0 ∧
            |(Mat ij 1:ℝ)| ≤ θ*Uband) ∨
          (Mat ij 0=1 ∧ Mat ij 3=1 ∧ Mat ij 1=0 ∧ Mat ij 2≠0 ∧
            |(Mat ij 2:ℝ)| ≤ θ/lambda) ∨
          (Mat ij 1≠0 ∧ Mat ij 2≠0 ∧
            8*Uband ≤ |(Mat ij 2:ℝ)| * lambda^2 ∧
            64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤ |(Mat ij 2:ℝ)| * κ^2*T)) := by
  classical
  intro κ Ratio L
  have hL : 0 ≤ L := by
    change 0 ≤ max (8*Ratio^2) _
    exact (by positivity : (0:ℝ) ≤ 8*Ratio^2).trans (le_max_left _ _)
  obtain ⟨C,hC,hsource⟩ := exists_positive_difference_actual_joint_source_sieve hεloss
  obtain ⟨Dtype,hDtype,hcount⟩ :=
    positive_difference_family_type_one_source_scale_at_action hσsrc hcsrc hUsrc hL
  pb_268
  pm_1815
  obtain ⟨hcard,hcharts,hratios,Mat,hfourier,hglobal,hnarrow,hclass⟩ :=
    hsource S Fsrc Prod.fst z rat v Nlen Q K₀ Vscale (N:ℝ) Rphys
      (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) (η:=η) (Tsrc:=Tsrc) (T:=T)
      (M:=M) (E:=E) (σ:=σ) (δ:=δ) (θ:=θ) (a:=a)
      hσsrc hcsrc hUsrc hη hηmax hTsrc hT hM hσ hδ hscale hQ hθ ha hθmax
      hy hz hreg hjets htests hden hinv hnegative hMtwo hVscale hNp hmesh
      hmodel hlevel hminor hcomplete
  pm_2492
  intro TypeOne key
  constructor
  · let P₁ := TypeOne key
    have hmem ij (hij : ij∈P₁) :
        ij∈Pairs key ∧
        ((Mat ij 0=1 ∧ Mat ij 1=0 ∧ Mat ij 2=0 ∧ Mat ij 3=1) ∨
          (Mat ij 1≠0 ∧ Mat ij 2≠0 ∧ |(Mat ij 2:ℝ)| * Uband ≤ L)) :=
      Finset.mem_filter.mp hij
    have hboth ij (hij : ij∈P₁) :
        ij.1.1∈S ∧ ij.2.1∈S := by
      pm_7186
      pm_1534
    have hall ij (hij : ij∈P₁) : ij∈Pall := by
      have hp := Finset.mem_filter.mp (hmem ij hij).1
      pm_2490
      pm_7757
    have hsame ij (hij : ij∈P₁) :
        |((rat ij.2.1).den:ℝ)/(rat ij.1.1).den-1| ≤ θ ∧
        |((rat ij.2.1).num:ℝ)/(rat ij.1.1).num-1| ≤ θ := by
      pm_7186
      have hi := Finset.mem_filter.mp hp.1
      have hj := Finset.mem_filter.mp hp.2
      have hh := hratios ij.1 hi.1 ij.2 hj.1 (hi.2.trans hj.2.symm)
      exact ⟨hh.1,hh.2.1⟩
    have hheight : (3*Usrc/σsrc)*Tsrc/(2*M^2) ≤ Uband := by
      have hh := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hscale (by positivity : (0:ℝ) ≤ 3*Usrc/σsrc))
        (by positivity : (0:ℝ) ≤ 2*M^2)
      simpa only [Uband,mul_assoc] using hh
    have hnum ij (hij : ij∈P₁) :
        |((Mat ij 0:ℝ)*h ij.1.1+Mat ij 1)/h ij.1.1-1| ≤ θ := by
      obtain ⟨_hdet,ht,htlo,_hthi,hmap,_hrest⟩ := hglobal ij (hall ij hij)
      have ht' : (Mat ij 2:ℝ)*h ij.1.1+Mat ij 3 =
          (q ij.2.1:ℝ)/q ij.1.1 := ht
      have htlo' : (1/2:ℝ) ≤ (Mat ij 2:ℝ)*h ij.1.1+Mat ij 3 := htlo
      have hmap' : ((Mat ij 0:ℝ)*h ij.1.1+Mat ij 1)/
          ((Mat ij 2:ℝ)*h ij.1.1+Mat ij 3) = h ij.2.1 := hmap
      have htpos : 0 < (Mat ij 2:ℝ)*h ij.1.1+Mat ij 3 :=
        (by norm_num : (0:ℝ) < 1/2).trans_le htlo'
      have hnumeq : ((Mat ij 0:ℝ)*h ij.1.1+Mat ij 1)/h ij.1.1=
          ((rat ij.2.1).num:ℝ)/(rat ij.1.1).num := by
        rw [(div_eq_iff htpos.ne').mp hmap',ht']
        simp only [h,hlevel ij.1.1 (hboth ij hij).1,hlevel ij.2.1 (hboth ij hij).2,
          q,Rat.cast_def]
        field_simp
      rw [hnumeq]
      exact (hsame ij hij).2
    pm_2493
    have hh := hcount P₁ Mat Fsrc (fun a n => z (a,n)) (fun a n => Nlen (a,n))
      N Z η Δ Jsep Tsrc M hη hηmax hreg hjets htests hnegative
      hTsrc hMtwo hN hΔ hJsep hNM hJM
      (fun ij hij => ⟨⟨hy _ (hboth ij hij).1,hz _ (hboth ij hij).1⟩,
        ⟨hy _ (hboth ij hij).2,hz _ (hboth ij hij).2⟩⟩)
      (fun ij hij => hgeometry _ (hboth ij hij).1)
      (fun ij hij => hgeometry _ (hboth ij hij).2)
      (fun ij hij kl hkl hne => hseparation _ (hboth ij hij).2 _ (hboth kl hkl).2 hne)
      (fun ij hij => (hglobal ij (hall ij hij)).1)
      (by
        intro ij hij
        rcases (hmem ij hij).2 with hid | hact
        · exact Or.inl hid
        · exact Or.inr ⟨hact.1,hact.2.1,
            (mul_le_mul_of_nonneg_left hheight (abs_nonneg _)).trans hact.2.2⟩)
      (fun ij hij => (hglobal ij (hall ij hij)).2.2.2.2.1)
      (by
        intro ij hij
        change |(Mat ij 2:ℝ)*h ij.1.1+Mat ij 3-1| ≤ 1/(8*(L+3))
        have ht : (Mat ij 2:ℝ)*h ij.1.1+Mat ij 3 =
            (q ij.2.1:ℝ)/q ij.1.1 := (hglobal ij (hall ij hij)).2.1
        rw [ht]
        exact (hsame ij hij).1.trans hθaction)
      (fun ij hij => (hnum ij hij).trans hθaction)
      (fun ij hij => (hglobal ij (hall ij hij)).2.2.2.2.2.2.1)
    have hsub : P₁.image (fun ij => ij.1.1.1) ⊆ S.image Prod.fst := by
      pm_2532 y hy ij hij
      exact Finset.mem_image_of_mem Prod.fst (hboth ij hij).1
    pm_2494 P₁.image
    exact hh.trans (by gcongr)
  · intro ij hij hnot
    pm_1100
    · exact False.elim (hnot (Finset.mem_filter.mpr ⟨hij,Or.inl hid⟩))
    · exact Or.inl hu
    · exact Or.inr (Or.inl hl)
    · have hlarge : L < |(Mat ij 2:ℝ)| * Uband := by
        by_contra hle
        exact hnot (Finset.mem_filter.mpr ⟨hij,Or.inr ⟨hn.1,hn.2,le_of_not_gt hle⟩⟩)
      have hbounds := (source_model_large_action_threshold (gamma:=(Mat ij 2:ℝ))
        hσsrc hcsrc hUsrc hE hσ hT hM (hδ.trans (min_le_right _ _))).2 hlarge
      exact Or.inr (Or.inr ⟨hn.1,hn.2,hbounds.1,hbounds.2⟩)


public  theorem actual_phase_pair_forget_card
    (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2))) (ya yb : ℝ) :
    let Fiber := P.filter (fun ij => ij.1.1.1=ya ∧ ij.2.1.1=yb)
    let forget := fun ij : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) =>
      ((ij.1.1.2,ij.1.2),(ij.2.1.2,ij.2.2))
    let embed := fun ij : (ℤ × Fin 2) × (ℤ × Fin 2) =>
      (((ya,ij.1.1),ij.1.2),((yb,ij.2.1),ij.2.2))
    (Fiber.image forget).card=Fiber.card ∧
      ∀ ij, ij∈Fiber.image forget ↔ embed ij∈P := by
  classical
  intro Fiber forget embed
  have hback ij (hij : ij∈Fiber) : embed (forget ij)=ij := by
    rcases ij with ⟨⟨⟨a,n⟩,ip⟩,⟨⟨b,m⟩,jp⟩⟩
    have he := (Finset.mem_filter.mp hij).2
    pm_594 he
    rfl
  constructor
  · apply Finset.card_image_of_injOn
    pm_1017
  · intro ij
    constructor
    · intro hij
      pm_6444
      exact (Finset.mem_filter.mp hkl).1
    · intro hij
      exact Finset.mem_image.mpr ⟨embed ij,Finset.mem_filter.mpr ⟨hij,by constructor <;> rfl⟩,rfl⟩

section
variable (S : Finset (ℝ × ℤ)) (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
include S P
private theorem actual_phase_pair_sum_card
    (hP : ∀ ij∈P, ij.1.1∈S ∧ ij.2.1∈S) :
    let Y := S.image Prod.fst
    let forget := fun ij : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) =>
      ((ij.1.1.2,ij.1.2),(ij.2.1.2,ij.2.2))
    (P.card:ℝ)=∑ ab∈Y ×ˢ Y,
      (((P.filter (fun ij => ij.1.1.1=ab.1 ∧ ij.2.1.1=ab.2)).image forget).card:ℝ) := by
  classical
  intro Y forget
  pm_2495
  have hmaps : Set.MapsTo phase (P : Set _) (Y ×ˢ Y : Finset _) := by
    intro ij hij
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem Prod.fst (hP ij hij).1,
       Finset.mem_image_of_mem Prod.fst (hP ij hij).2⟩
  have hcard := Finset.card_eq_sum_card_fiberwise hmaps
  have heq ab : (P.filter (fun ij => phase ij=ab)).card=
      ((P.filter (fun ij => ij.1.1.1=ab.1 ∧ ij.2.1.1=ab.2)).image forget).card := by
    rw [(actual_phase_pair_forget_card P ab.1 ab.2).1]
    congr 1
    all_goals
      rcases ab with ⟨ya,yb⟩
      ext ij
      simp only [Finset.mem_filter,phase,Prod.mk.injEq]
  rw [Finset.sum_congr rfl (fun ab _ => heq ab)] at hcard
  exact_mod_cast hcard


private theorem actual_type_one_phase_pair_partition
    (Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ)
    (small : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Prop)
    [DecidablePred small]
    (hP : ∀ ij∈P, ij.1.1∈S ∧ ij.2.1∈S) :
    let TypeOne := P.filter small
    let Rest := P.filter (fun ij => ¬small ij)
    let Upper := Rest.filter (fun ij => Mat ij 2=0)
    let NonUpper := Rest.filter (fun ij => Mat ij 2≠0)
    let Lower := NonUpper.filter (fun ij => Mat ij 1=0)
    let Large := NonUpper.filter (fun ij => Mat ij 1≠0)
    let Y := S.image Prod.fst
    let forget := fun ij : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) =>
      ((ij.1.1.2,ij.1.2),(ij.2.1.2,ij.2.2))
    let phaseFiber := fun (E : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2))) ab =>
      (E.filter (fun ij => ij.1.1.1=ab.1 ∧ ij.2.1.1=ab.2)).image forget
    (P.card:ℝ)=(TypeOne.card:ℝ)+∑ ab∈Y ×ˢ Y,
      (((phaseFiber Upper ab).card:ℝ)+((phaseFiber Lower ab).card:ℝ)+
        ((phaseFiber Large ab).card:ℝ)) := by
  classical
  intro TypeOne Rest Upper NonUpper Lower Large Y forget phaseFiber
  have hfirst : TypeOne.card+Rest.card=P.card :=
    Finset.card_filter_add_card_filter_not small
  pm_7866 hsecond Upper.card NonUpper.card Rest.card hthird Lower.card Large.card
  have hsum : (P.card:ℝ)=(TypeOne.card:ℝ)+
      ((Upper.card:ℝ)+(Lower.card:ℝ)+(Large.card:ℝ)) := by
    exact_mod_cast (by omega : P.card=TypeOne.card+(Upper.card+Lower.card+Large.card))
  have hUpper := actual_phase_pair_sum_card S Upper (fun ij hij =>
    hP ij (Finset.mem_filter.mp (Finset.mem_filter.mp hij).1).1)
  pm_5949 hLower Lower
  pm_5949 hLarge Large
  rw [hsum,hUpper,hLower,hLarge]
  simp only [Finset.sum_add_distrib]
  rfl
end


                                                                           
                                                                         
set_option hygiene false in
macro "pc_428" x1:ident : tactic => `(tactic| (
  obtain ⟨C,Dtype,hC,hDtype,hsource⟩ :=
    $x1:ident hσsrc hcsrc hUsrc hE hσ hεloss))
theorem exists_positive_difference_joint_type_decomposed_source_sieve
    {σsrc csrc Usrc E σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hE : 0 < E) (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2*E/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)*E/κ^2)
    ∃ C Dtype : ℝ, 0 < C ∧ 0 < Dtype ∧ ∀ (S : Finset (ℝ × ℤ)) (Fsrc : ℝ → ℝ)
    (z : (ℝ × ℤ) → ℝ) (rat : (ℝ × ℤ) → ℚ) (v : (ℝ × ℤ) → ℤ) (Nlen : (ℝ × ℤ) → ℕ)
    (Q K₀ N : ℕ) [NeZero K₀] (Vscale Rphys Jsep : ℝ) (Z : ℝ → ℤ)
    {η Tsrc T M δ θ a : ℝ},
    (0 < η) →
    (η ≤ 1/8) →
    (0 < Tsrc) →
    (0 < T) →
    (0 < M) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (Tsrc ≤ E*T) →
    (0 < Q) →
    (0 < θ) →
    (0 < a) →
    (θ < 1) →
    (θ ≤ 1/(8*(L+3))) →
    (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈S, z i∈Icc M (2*M)) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ i∈S, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den) →
    (∀ i∈S, ((rat i).den:ℤ) ∣ (rat i).num*v i-1) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (2 ≤ M) →
    (1 ≤ Vscale) →
    (0 < N) →
    (0 < Jsep) → (Jsep ≤ M) → ((N:ℝ) ≤ M) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*Rphys^2) →
    (∀ i∈S, N ≤ Nlen i ∧ Nlen i ≤ 3*N ∧
      round (z i)+(Nlen i:ℤ)=Z i.1+(N:ℤ)*i.2+2*(N:ℤ)) →
    (∀ i∈S, ∀ j∈S, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    let Fmodel := fun (i : ℝ × ℤ) u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*i.1))/(σsrc*η)
    (∀ i∈S, Expdb.IsApproximateModelPhaseFunction (Fmodel i) σ 2 δ) →
    let f := fun p w => Tsrc*(Fsrc (w/M)-Fsrc (w/M+η*p))/(σsrc*η)
    (∀ i∈S, iteratedDeriv 2 (f (i.1)) (z i)/2=(rat i:ℝ)) →
    (∀ i∈S, 1 ≤ Nlen i ∧ (rat i).den ≤ Nlen i ∧
      1 ≤ (iteratedDeriv 3 (f (i.1)) (round (z i))/6)*((rat i).den:ℝ)^2*Nlen i) →
    (∀ i∈S, 7*((iteratedDeriv 3 (f (i.1)) (round (z i))/6)*
      ((rat i).den:ℝ)*(Nlen i:ℝ)^2) ≤ K₀) →
    let Hsrc := fun p : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc p.2-iteratedDeriv 2 Fsrc (p.2+η*p.1))/(σsrc*η)
    let lambda := csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*E*T/(2*M^2)
    let u := fun (i : ℝ × ℤ) => (2*M^2/Tsrc)*(rat i:ℝ)
    let w := fun (i : ℝ × ℤ) => (Tsrc/(2*M^2))*(rat i:ℝ)⁻¹
    let chart := fun (i : ℝ × ℤ) => (⌊i.1/a⌋,⌊u i/a⌋,⌊w i/a⌋)
    let narrow := fun (i : ℝ × ℤ) =>
      (⌊((rat i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
       ⌊((rat i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    let qell := fun (i : ℝ × ℤ) => ((rat i).den:ℝ)*deriv (f (i.1)) (round (z i))
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let offset := fun ip : (ℝ × ℤ) × Fin 2 => ⌊qell ip.1⌋+(ip.2:ℕ)-round (qell ip.1)
    let color := fun ip : (ℝ × ℤ) × Fin 2 => (chart ip.1,narrow ip.1,offset ip)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2*E/(σsrc*csrc*modelPhaseThirdLower σ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap

    let q := fun (i : ℝ × ℤ) => (rat i).den
    let μ := fun (i : ℝ × ℤ) => iteratedDeriv 3 (f (i.1)) (round (z i))/6
    let ell := fun (i : ℝ × ℤ) => deriv (f (i.1)) (round (z i))
    let b := fun ip : (ℝ × ℤ) × Fin 2 => (⌊qell ip.1⌋+(ip.2:ℕ) : ℤ)
    let tau := fun ip : (ℝ × ℤ) × Fin 2 => ((b ip:ℝ)-qell ip.1)/2
    let dual := fun (i : ℝ × ℤ) => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun ip : (ℝ × ℤ) × Fin 2 =>
      (![-(v ip.1:ℝ)*b ip/q ip.1,-(v ip.1:ℝ)/q ip.1,
        dual ip.1,3*dual ip.1*tau ip/2] : Fin 4 → ℝ)
    let cloud := fun ip => (![Int.fract (x ip 0),Int.fract (x ip 1),
      x ip 2/Real.sqrt K₀,x ip 3/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2*Vscale),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    let Pall := (V ×ˢ V).filter (fun ij => ∀ d, |cloud ij.1 d-cloud ij.2 d| ≤ 2*radius d)
    let Fiber := fun key => V.filter (fun ip => color ip=key)
    let Pairs := fun key => ((Fiber key) ×ˢ (Fiber key)).filter
      (fun ij => ∀ d, |cloud ij.1 d-cloud ij.2 d| ≤ 2*radius d)
    let μ₀ := csrc*Tsrc/(12*σsrc*M^3)
    let U₀ := Usrc*Tsrc/(2*σsrc*M^3)
    let h := fun (i : ℝ × ℤ) => iteratedDeriv 2 (f (i.1)) (z i)/2
    let D := (Real.sqrt K₀/(9*(K₀:ℝ))+Real.sqrt K₀/(12*(K₀:ℝ)^2))*
      Real.sqrt (U₀*(Q:ℝ)^3)
    let Δ := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    ((V.image color).card:ℝ) ≤ Cap ∧
    (∀ key∈V.image color, ∃ iref∈S, chart iref=key.1 ∧
      let xcenter := z iref/M
      let ycenter := iref.1
      xcenter∈Icc (1:ℝ) 2 ∧ ycenter∈Icc (1:ℝ) 2 ∧
      ∀ ip∈V, color ip=key →
        ‖((ip.1.1,u ip.1):ℝ × ℝ)-(ycenter,Hsrc (ycenter,xcenter))‖ < a ∧
        ‖((ip.1.1,w ip.1):ℝ × ℝ)-(ycenter,(Hsrc (ycenter,xcenter))⁻¹)‖ < a) ∧
    (∀ ip∈V, ∀ jp∈V, color ip=color jp →
      |((rat jp.1).den:ℝ)/(rat ip.1).den-1| ≤ θ ∧
      |((rat jp.1).num:ℝ)/(rat ip.1).num-1| ≤ θ ∧ offset ip = offset jp) ∧
    ∃ Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ,
      (∀ k : ZMod K₀,
        (∑ ip∈V, ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
          GafniTao.fordAdditiveCharacter (∑ d,x ip d*
            (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
              Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
          C*Vscale*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
            ∑ key∈V.image color,((Fiber key).card:ℝ)^10*((Pairs key).card:ℝ)) ∧
      (∀ ij∈Pall,
        Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1 ∧
        let t := (Mat ij 2:ℝ)*h ij.1.1+Mat ij 3
        t=(q ij.2.1:ℝ)/q ij.1.1 ∧ (1:ℝ)/2 ≤ t ∧ t ≤ 2 ∧
        ((Mat ij 0:ℝ)*h ij.1.1+Mat ij 1)/t=h ij.2.1 ∧
        |(Mat ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) ∧
        |μ ij.2.1/μ ij.1.1*t^3-1| ≤
          (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2) ∧
        |tau ij.1-tau ij.2| ≤ D ∧
        (∃ e₁ e₂ : ℤ,
          let F₁ := 2*(round (z ij.2.1):ℝ)-2*(Mat ij 3:ℝ)*(round (z ij.1.1):ℝ)-
            (Mat ij 2:ℝ)*ell ij.1.1
          let F₂ := ell ij.2.1-2*(Mat ij 1:ℝ)*(round (z ij.1.1):ℝ)-
            (Mat ij 0:ℝ)*ell ij.1.1
          |F₁-e₁| ≤ (q ij.2.1:ℝ)/(6*(K₀:ℝ))+|(Mat ij 2:ℝ)|/q ij.1.1 ∧
          |(F₂-e₂)-h ij.2.1*(F₁-e₁)| ≤ 2*D/q ij.2.1) ∧
        ((Q:ℝ)^2/(6*(K₀:ℝ)^2) < 1 →
          Mat ij 2=0 ∧ q ij.1.1=q ij.2.1 ∧
            (q ij.1.1:ℤ) ∣ (rat ij.2.1).num-(rat ij.1.1).num)) ∧
      (∀ ij∈Pall, |(Mat ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2*Vscale) ∧
        |(Mat ij 2:ℝ)| ≤ Rphys^4/(6*(N:ℝ)^2*Vscale)) ∧
      (∀ key, ∀ ij∈Pairs key,
        (Mat ij 0=1 ∧ Mat ij 1=0 ∧ Mat ij 2=0 ∧ Mat ij 3=1) ∨
        (Mat ij 0=1 ∧ Mat ij 3=1 ∧ Mat ij 2=0 ∧ Mat ij 1≠0 ∧
          |(Mat ij 1:ℝ)| ≤ θ*Uband) ∨
        (Mat ij 0=1 ∧ Mat ij 3=1 ∧ Mat ij 1=0 ∧ Mat ij 2≠0 ∧
          |(Mat ij 2:ℝ)| ≤ θ/lambda) ∨
        (Mat ij 1≠0 ∧ Mat ij 2≠0)) ∧
      let TypeOne := fun key => (Pairs key).filter (fun ij =>
        (Mat ij 0=1 ∧ Mat ij 1=0 ∧ Mat ij 2=0 ∧ Mat ij 3=1) ∨
        (Mat ij 1≠0 ∧ Mat ij 2≠0 ∧ |(Mat ij 2:ℝ)| * Uband ≤ L))
      let Rest := fun key => (Pairs key).filter (fun ij => ij∉TypeOne key)
      let Upper := fun key => (Rest key).filter (fun ij => Mat ij 2=0)
      let NonUpper := fun key => (Rest key).filter (fun ij => Mat ij 2≠0)
      let Lower := fun key => (NonUpper key).filter (fun ij => Mat ij 1=0)
      let Large := fun key => (NonUpper key).filter (fun ij => Mat ij 1≠0)
      let Y := S.image Prod.fst
      let forget := fun ij : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) =>
        ((ij.1.1.2,ij.1.2),(ij.2.1.2,ij.2.2))
      let phaseFiber := fun (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2))) ab =>
        (P.filter (fun ij => ij.1.1.1=ab.1 ∧ ij.2.1.1=ab.2)).image forget
      (∀ key, (((TypeOne key).card:ℝ) ≤
        Dtype*((S.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+Δ*Jsep)) ∧
        (∀ ij∈Pairs key, ij∉TypeOne key →
          (Mat ij 0=1 ∧ Mat ij 3=1 ∧ Mat ij 2=0 ∧ Mat ij 1≠0 ∧
            |(Mat ij 1:ℝ)| ≤ θ*Uband) ∨
          (Mat ij 0=1 ∧ Mat ij 3=1 ∧ Mat ij 1=0 ∧ Mat ij 2≠0 ∧
            |(Mat ij 2:ℝ)| ≤ θ/lambda) ∨
          (Mat ij 1≠0 ∧ Mat ij 2≠0 ∧
            8*Uband ≤ |(Mat ij 2:ℝ)| * lambda^2 ∧
            64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤ |(Mat ij 2:ℝ)| * κ^2*T))) ∧
      (∀ key, ((Pairs key).card:ℝ)=((TypeOne key).card:ℝ)+∑ ab∈Y ×ˢ Y,
        (((phaseFiber (Upper key) ab).card:ℝ)+((phaseFiber (Lower key) ab).card:ℝ)+
          ((phaseFiber (Large key) ab).card:ℝ))) ∧
      (∀ k : ZMod K₀,
        (∑ ip∈V, ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
          GafniTao.fordAdditiveCharacter (∑ d,x ip d*
            (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
              Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
          C*Vscale*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
            ∑ key∈V.image color,((Fiber key).card:ℝ)^10*
              (Dtype*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δ*Jsep)+∑ ab∈Y ×ˢ Y,
                (((phaseFiber (Upper key) ab).card:ℝ)+((phaseFiber (Lower key) ab).card:ℝ)+
                  ((phaseFiber (Large key) ab).card:ℝ)))) := by
  classical
  intro κ Ratio L
  pc_428 exists_positive_difference_joint_type_one_source_sieve
  pb_268
  pm_2496 htype
  pm_2492
  intro TypeOne Rest Upper NonUpper Lower Large Y forget phaseFiber
  have hsplit key : ((Pairs key).card:ℝ)=((TypeOne key).card:ℝ)+∑ ab∈Y ×ˢ Y,
      (((phaseFiber (Upper key) ab).card:ℝ)+((phaseFiber (Lower key) ab).card:ℝ)+
        ((phaseFiber (Large key) ab).card:ℝ)) := by
    have hP ij (hij : ij∈Pairs key) : ij.1.1∈S ∧ ij.2.1∈S := by
      have hp := Finset.mem_product.mp (Finset.mem_filter.mp hij).1
      pm_1534
    have hh := actual_type_one_phase_pair_partition S (Pairs key) Mat
      (fun ij => ij∈TypeOne key) hP
    have hsmall' : (Pairs key).filter (fun ij => ij∈TypeOne key)=TypeOne key := by
      ext ij
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2,fun h => ⟨(Finset.mem_filter.mp h).1,h⟩⟩
    change ((Pairs key).card:ℝ)=
      (((Pairs key).filter (fun ij => ij∈TypeOne key)).card:ℝ)+_ at hh
    rw [hsmall'] at hh
    exact hh
  refine ⟨htype,hsplit,?_⟩
  intro k
  pm_2279 hCap Cap Nat.cast_nonneg hcard
  have hVs : 0 ≤ Vscale := zero_le_one.trans hVscale
  apply (hfourier k).trans
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (mul_nonneg (mul_nonneg hC.le hVs)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (pow_nonneg hCap 11))
  apply Finset.sum_le_sum
  intro key _
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg (Fiber key).card) 10)
  rw [hsplit]
  exact add_le_add (htype key).1 le_rfl


                                                                         
                                                                                   
                                                      
theorem eventually_positive_difference_global_triangular_source_mass
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower Dupper Dlower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧
    ∀ {σ Jref εloss E θ : ℝ}, 0 < σ → 0 ≤ Jref → 0 < εloss →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (η ya yb Tsrc : ℝ) (chartKey : ℤ → ℤ × ℤ × ℤ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2))) (entry : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℤ)
    (Mat : ℤ → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ)
    (N : ℕ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ) (Za Zb : ℤ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℚ) (vinv : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℤ)
    (parity : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → Fin 2) (anchor : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {δ M R base Bcut : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ},
    let x := fun ij : (ℤ × Fin 2) × (ℤ × Fin 2) => (![za ij.1.1,zb ij.2.1] : Fin 2 → ℝ)
    let xlocal := fun ij i => x ij i-(A i:ℝ)
    Function.Injective Mat →
    0 < η → η ≤ η₀ →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    (∀ ij∈P, entry ij≠0) →
    (∀ ij∈P, base ≤ za ij.1.1-(A 0:ℝ)) →
    (∀ ij∈P, gap ij∈Gaps) →
    (∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ)) →
    (∀ ij∈P, N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(AlenB ij.2.1:ℤ)=Zb+(N:ℤ)*ij.2.1+2*(N:ℤ)) →
    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    let lambda := csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2)
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let chartColor := fun ij i =>
      (⌊yp i/a⌋,⌊((2*M^2/Tsrc)*(rat ij i:ℝ))/a⌋,
        ⌊((Tsrc/(2*M^2))*(rat ij i:ℝ)⁻¹)/a⌋)
    (∀ ij∈P, ∀ i, chartColor ij i=chartKey (entry ij)) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < (N:ℝ)) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*(N:ℝ)*R^2=M^3) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ ij∈P, ∀ i, xlocal ij i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, (rat ij i).den ≤ Q ∧ Q ≤ 2*(rat ij i).den) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ ij∈P, ∀ i, ((rat ij i).den:ℤ) ∣ (rat ij i).num*vinv ij i-1) →
    (∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) →
    (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ ij∈P, ∀ i, xlocal ij i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, xlocal ij i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (∀ ij∈P, (rat ij 0:ℝ)∈Icc (gap ij).1 (gap ij).2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (Q:ℝ) ≤ (N:ℝ) → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((v ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let sourceColor := fun ij i => (⌊((rat ij i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((rat ij i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ij∈P, sourceColor ij 0=sourceColor ij 1) →
    let f := fun (i : Fin 2) w => Tsrc*(Fsrc (w/M)-Fsrc (w/M+η*yp i))/(σsrc*η)
    (∀ ij∈P, ∀ i, iteratedDeriv 2 (f i) (x ij i)/2=(rat ij i:ℝ)) →
    let q := fun ij i => (rat ij i).den
    let mu := fun ij i => iteratedDeriv 3 (f i) (round (x ij i))/6
    let ell := fun ij i => deriv (f i) (round (x ij i))
    let b := fun ij i => (⌊(q ij i:ℝ)*ell ij i⌋+(parity ij i:ℕ) : ℤ)
    let cround := fun ij i => round ((q ij i:ℝ)*ell ij i)
    let tau := fun ij i => ((b ij i:ℝ)-(q ij i:ℝ)*ell ij i)/2
    let dual := fun ij i => -2*mu ij i*(Real.sqrt (2/(3*mu ij i*(q ij i:ℝ))))^3
    let cloud := fun ij i => (![Int.fract (-(vinv ij i:ℝ)*b ij i/q ij i),
      Int.fract (-(vinv ij i:ℝ)/q ij i),dual ij i/Real.sqrt K₀,
      (3*dual ij i*tau ij i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ij∈P, b ij 0-cround ij 0=b ij 1-cround ij 1) →
    (∀ ij∈P, ∀ a, |cloud ij 0 a-cloud ij 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 →
    R ≤ (N:ℝ) →
    (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    (∀ t∈P.image entry, Mat t 0*Mat t 3-Mat t 1*Mat t 2=1) →
    (∀ ij∈P, (Mat (entry ij) 2:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 3=(q ij 1:ℝ)/q ij 0) →
    (∀ ij∈P, ((Mat (entry ij) 0:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 1)/
      ((Mat (entry ij) 2:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 3)=(rat ij 1:ℝ)) →
    (∀ t∈P.image entry, |(Mat t 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ ij∈P, ∀ i, xlocal ij i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, xlocal ij i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, |(anchor ij:ℝ)-(rat ij 0:ℝ)| ≤ ε) →
    (∀ ij∈P, 256*((anchor ij).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ij∈P, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor ij).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let AupperConst := 2*Cupper*(Cthird+1)*E^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*E^2/Lunit^2+Dupper*(B+1)*E^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*E/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let CostUpper := M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := R^4/((N:ℝ)^2*(Uref:ℝ))
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 2=0 ∧ Mat t 3=1 ∧ Mat t 1=t) →
      (P.card:ℝ) ≤ (240*CostUpper*
        (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+
          2*BupperConst+(3/2:ℝ)*DupperConst))*T^εloss) ∧
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 1=0 ∧ Mat t 3=1 ∧ Mat t 2=t) →
      (P.card:ℝ) ≤ (240*CostLower*
        (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+
          2*BlowerConst+(3/2:ℝ)*DlowerConst))*T^εloss) := by
  pm_2479 hmassFn eventually_positive_difference_actual_fourier_triangular_original_source_mass
  pm_2478
  pm_702
  intro Fsrc η ya yb Tsrc chartKey Uref Refs Gaps Bselect P entry Mat gap
    N za zb AlenA AlenB Za Zb Q K₀ inst rat vinv parity anchor e r v s
    δ M R base Bcut A W x xlocal
    hMat hη hηsmall hya hyb hreg hjets htests hTsrc hMtwo hsourceScale
    hentry hbase hgapMem hgeometryA hgeometryB hregime
    lambda yp F chartColor hchartColor
    hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hden hθ hθmax
    hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref
    hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
    hselectedUpper hscaleTen hfamilyGap hgap
    hQN hNM hUR hrHeight hsHeight heHeight hvHeight
    ε sourceColor hsourceColor f hlevel q mu ell b cround tau dual cloud radius
    hcolor hnear κ Cphys c J B hsmall hNR hRN hNcube hminscale
    hMatdet hMatt hMatmap hMatgamma H hNtwo hL hU hanchor hcut hcount
    C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Lunit Gamma Cthird AupperConst BupperConst AlowerConst BlowerConst
    DupperConst DlowerConst CostUpper CostLower

  pm_2499
  pm_2497
  apply hmass Fsrc η ya yb Tsrc chartKey Uref Refs Gaps (Bselect:=Bselect)
    P entry Mat gap N (fun n => za n-(A 0:ℝ)) (fun n => zb n-(A 1:ℝ))
    AlenA AlenB (Za-A 0) (Zb-A 1) Q K₀ rat vinv parity anchor e r v s
    (δ:=δ) (M:=M) (R:=R) (base:=base) (Bcut:=Bcut) A (W:=W) (x:=xlocal)
    hMat hη hηsmall hya hyb hreg hjets htests hTsrc hMtwo hsourceScale
    hentry hbase (by intro ij _; rfl) (by intro ij _; rfl)
    hgapMem hgeomA hgeomB hregime hchartColor
    hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hden hθ hθmax
    hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref
    hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
    hselectedUpper hscaleTen hfamilyGap hgap hQN hNM hUR hrHeight hsHeight heHeight hvHeight
    hsourceColor
    (by intro ij hij i; rw [show iteratedDeriv 2 (heathBrownPhysicalPhase (F i) T M (A i) 1)
      (xlocal ij i)=iteratedDeriv 2 (f i) (x ij i) from hjet ij i 2]; exact hlevel ij hij i)
    (by
      pm_2498
      exact hcolor ij hij)
    (by
      pm_2500
      exact hnear ij hij d)
    hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    hNtwo hL hU hanchor hcut hcount hsize hD hΔ hBsize


public  theorem eventually_positive_difference_global_large_entry_source_mass
    {σ Jref εloss : ℝ} (hσ : 0 < σ) (hJref : 0 ≤ Jref) (hεloss : 0 < εloss) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (σsrc η Tsrc ya yb : ℝ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2))) (Mat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ)
    (Q K₀ : ℕ) [NeZero K₀]
    (N : ℕ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ) (Za Zb : ℤ)
    (rat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℚ)
    (vinv : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℤ)
    (parity : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → Fin 2)
    (anchor : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {δ M R base Bcut lambda Uband θ V : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ},
    let x := fun ij : (ℤ × Fin 2) × (ℤ × Fin 2) => (![za ij.1.1,zb ij.2.1] : Fin 2 → ℝ)
    let xlocal := fun ij i => x ij i-(A i:ℝ)
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    (∀ ij∈P, base ≤ za ij.1.1-(A 0:ℝ)) →
    (∀ ij∈P, gap ij∈Gaps) →
    (∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ)) →
    (∀ ij∈P, N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(AlenB ij.2.1:ℤ)=Zb+(N:ℤ)*ij.2.1+2*(N:ℤ)) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < (N:ℝ)) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*(N:ℝ)*R^2=M^3) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ (A i:ℝ)) →
    (∀ i, (A i:ℝ)+W i ≤ 2*M) →
    (∀ ij∈P, ∀ i, xlocal ij i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, (rat ij i).den ≤ Q ∧ Q ≤ 2*(rat ij i).den) →
    (0 < lambda) →
    (0 ≤ Uband) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ ij∈P, ∀ i, lambda ≤ |(rat ij i:ℝ)| ∧ |(rat ij i:ℝ)| ≤ Uband) →
    (∀ ij∈P, ∀ i, ((rat ij i).den:ℤ) ∣ (rat ij i).num*vinv ij i-1) →
    (∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) →
    (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ ij∈P, ∀ i, xlocal ij i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, xlocal ij i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (∀ ij∈P, (rat ij 0:ℝ)∈Icc (gap ij).1 (gap ij).2) →
    (∀ ij∈P, Mat ij 2 ≠ 0) →
    (∀ ij∈P, 64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat ij 2:ℝ)| *(modelPhaseThirdLower σ)^2*T) →
    (∀ ij∈P, 8*Uband ≤ |(Mat ij 2:ℝ)| *lambda^2) →
    (1 ≤ V) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (Q:ℝ) ≤ (N:ℝ) → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((v ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let sourceColor := fun ij i => (⌊((rat ij i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((rat ij i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ij∈P, sourceColor ij 0=sourceColor ij 1) →
    let f := fun (i : Fin 2) w => Tsrc*(Fsrc (w/M)-Fsrc (w/M+η*yp i))/(σsrc*η)
    (∀ ij∈P, ∀ i, iteratedDeriv 2 (f i) (x ij i)/2=(rat ij i:ℝ)) →
    let q := fun ij i => (rat ij i).den
    let mu := fun ij i => iteratedDeriv 3 (f i) (round (x ij i))/6
    let ell := fun ij i => deriv (f i) (round (x ij i))
    let b := fun ij i => (⌊(q ij i:ℝ)*ell ij i⌋+(parity ij i:ℕ) : ℤ)
    let cround := fun ij i => round ((q ij i:ℝ)*ell ij i)
    let tau := fun ij i => ((b ij i:ℝ)-(q ij i:ℝ)*ell ij i)/2
    let dual := fun ij i => -2*mu ij i*(Real.sqrt (2/(3*mu ij i*(q ij i:ℝ))))^3
    let cloud := fun ij i => (![Int.fract (-(vinv ij i:ℝ)*b ij i/q ij i),
      Int.fract (-(vinv ij i:ℝ)/q ij i),dual ij i/Real.sqrt K₀,
      (3*dual ij i*tau ij i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ij∈P, b ij 0-cround ij 0=b ij 1-cround ij 1) →
    (∀ ij∈P, ∀ a, |cloud ij 0 a-cloud ij 1 a| ≤ 2*radius a) →
    (∀ ij∈P,
      |cloud ij 0 1-cloud ij 1 1| ≤ 1/(6*(K₀:ℝ)^2*V)) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 →
    R ≤ (N:ℝ) →
    (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    (∀ ij∈P, Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1) →
    (∀ ij∈P, (Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3=(q ij 1:ℝ)/q ij 0) →
    (∀ ij∈P, ((Mat ij 0:ℝ)*(rat ij 0:ℝ)+Mat ij 1)/
      ((Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3)=(rat ij 1:ℝ)) →
    (∀ ij∈P, |(Mat ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ ij∈P, ∀ i, xlocal ij i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, xlocal ij i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, |(anchor ij:ℝ)-(rat ij 0:ℝ)| ≤ ε) →
    (∀ ij∈P, 256*((anchor ij).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ij∈P, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor ij).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    V=(Uref:ℝ)^((3:ℝ)/2) →
    ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Uref:ℝ) →
    V*(P.card:ℝ) ≤
      (2*Bselect*60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
        (Cmain+Ctail)*((Q:ℝ)/(N:ℝ))^((2:ℝ)/3))*T^εloss := by
  pm_5380 eventually_physicalModelPhase_actual_fourier_original_pair_mass hmass
  intro Fsrc σsrc η Tsrc ya yb Uref Refs Gaps Bselect P Mat gap Q K₀ _ N za zb AlenA AlenB Za Zb
    rat vinv parity anchor e r v s δ M R base Bcut lambda Uband θ V A W x xlocal yp F
    hbase hgapMem hgeometryA hgeometryB hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hc hlarge haction hV hgap
    hQN hNM hUR hrHeight hsHeight heHeight hvHeight
    ε sourceColor hsourceColor f hlevel q mu ell b cround tau dual cloud radius
    hcolor hnear hnearNarrow κ Cphys c J B hsmall hNR hRN hNcube hminscale
    hMatdet hMatt hMatmap hMatgamma H hNtwo hL hU hanchor hcut hcount
    C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Lunit Gamma Cthird Cpack Cfirst Cgap Cmain Ctail hvchoice hUlo
  pm_2499
  pm_2497
  apply hmass Uref Refs Gaps (Bselect:=Bselect) P Mat gap Q K₀ N
    (fun n => za n-(A 0:ℝ)) (fun n => zb n-(A 1:ℝ))
    AlenA AlenB (Za-A 0) (Zb-A 1) rat vinv parity anchor e r v s
    (δ:=δ) (M:=M) (R:=R) (base:=base) (Bcut:=Bcut)
    (lambda:=lambda) (Uband:=Uband) (θ:=θ) (V:=V) (F:=F)
    (A:=fun i => (A i:ℝ)) (W:=W) (x:=xlocal)
    hbase (by intro ij _; rfl) (by intro ij _; rfl) hgapMem hgeomA hgeomB
    hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hden hlambda hUband hθ hθmax hcurv
    hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref
    hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
    hselectedUpper hscaleTen hfamilyGap hc hlarge haction hV hgap
    hQN hNM hUR hrHeight hsHeight heHeight hvHeight hsourceColor
    (by intro ij hij i; rw [show iteratedDeriv 2 (heathBrownPhysicalPhase (F i) T M (A i) 1)
      (xlocal ij i)=iteratedDeriv 2 (f i) (x ij i) from hjet ij i 2]; exact hlevel ij hij i)
    (by
      pm_2498
      exact hcolor ij hij)
    (by
      pm_2500
      exact hnear ij hij d)
    (by
      pm_2501
      exact hnearNarrow ij hij)
    hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    hNtwo hL hU hanchor hcut hcount hsize hD hΔ hBsize hvchoice hUlo

-- Generated closures: source context is replayed in the next part.
end TaoTrudgianYang2025.HuxleyRationalPhase
end
