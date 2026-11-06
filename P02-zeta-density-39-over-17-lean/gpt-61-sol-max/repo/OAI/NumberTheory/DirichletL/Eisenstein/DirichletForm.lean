module
import Mathlib
public import OAI.NumberTheory.DirichletL.GaussSum.ReflectedBranches

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
                        
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
                     
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
           
                    
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
                    
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
           
                    
                    
                                                       
                                     
                    
                       
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
                                                               
                                                               
                                                               
                                                               
                       
                                     
                    
open Filter Asymptotics Ideal NumberField
           
                                     
                    
                                     
                    
                                     
                    
                       
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
                                  
                                  
open scoped BigOperators Classical SchwartzMap ContDiff
                                                       
                                  
                                                       
                                  
                                                       
                                                       
                                                       
                                  
                                                       
open MeasureTheory Set
                        
                                  
                                  
open ActualEisensteinCubic UniqueFactorizationMonoid
                        

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal MatrixGroups

namespace CubicEisenstein

def kernelTestPartial (f : kernelSmoothTests) (w : HyperbolicSpace) (j : Fin 3) : ℂ :=
  fderiv ℝ (kernelTestField f) (hyperbolicEuclideanCoordinates w) (EuclideanSpace.basisFun (Fin 3) ℝ j)

lemma kernelTestPartial_add (f g : kernelSmoothTests) (w : HyperbolicSpace) (j : Fin 3) :
    kernelTestPartial (f+g) w j=kernelTestPartial f w j+kernelTestPartial g w j := by
  unfold kernelTestPartial
  have he : kernelTestField (f+g)=kernelTestField f+kernelTestField g := rfl
  rw [he,fderiv_add ((kernelTestField_contDiffAt f _ (hyperbolicHeight_pos w)).differentiableAt (by simp))
    ((kernelTestField_contDiffAt g _ (hyperbolicHeight_pos w)).differentiableAt (by simp))]
  rfl

lemma kernelTestPartial_smul (c : ℂ) (f : kernelSmoothTests) (w : HyperbolicSpace) (j : Fin 3) :
    kernelTestPartial (c•f) w j=c*kernelTestPartial f w j := by
  unfold kernelTestPartial
  have he : kernelTestField (c•f)=c•kernelTestField f := rfl
  rw [he,fderiv_const_smul ((kernelTestField_contDiffAt f _ (hyperbolicHeight_pos w)).differentiableAt (by simp))]
  rfl

lemma kernelTestEnergyDensity_eq_partials (f : kernelSmoothTests) (w : HyperbolicSpace) :
    kernelTestEnergyDensity f w=(hyperbolicHeight w)^2*∑j:Fin 3,‖kernelTestPartial f w j‖^2 := by
  have hd := ((kernelTestField_contDiffAt f (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w)).differentiableAt (by simp)).hasFDerivAt
  have hr := (Complex.reCLM.hasFDerivAt.comp (hyperbolicEuclideanCoordinates w) hd).fderiv
  have hi := (Complex.imCLM.hasFDerivAt.comp (hyperbolicEuclideanCoordinates w) hd).fderiv
  change fderiv ℝ (fun p => (kernelTestField f p).re) (hyperbolicEuclideanCoordinates w)=_ at hr
  change fderiv ℝ (fun p => (kernelTestField f p).im) (hyperbolicEuclideanCoordinates w)=_ at hi
  unfold kernelTestEnergyDensity euclideanScalarDirichletDensity
  rw [hr,hi,(EuclideanSpace.basisFun (Fin 3) ℝ).norm_dual,
    (EuclideanSpace.basisFun (Fin 3) ℝ).norm_dual,←mul_add,←Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  change (kernelTestPartial f w j).re^2+(kernelTestPartial f w j).im^2=‖kernelTestPartial f w j‖^2
  simpa only [Complex.normSq_apply,pow_two] using Complex.normSq_eq_norm_sq (kernelTestPartial f w j)

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal MatrixGroups InnerProductSpace

def kernelGradientAt (w : HyperbolicSpace) : kernelSmoothTests→ₗ[ℂ]EuclideanSpace ℂ (Fin 3) where
  toFun f := WithLp.toLp 2 (fun j => (hyperbolicHeight w:ℂ)*kernelTestPartial f w j)
  map_add' f g := by
    apply (WithLp.equiv 2 (Fin 3→ℂ)).injective
    funext j
    simp [kernelTestPartial_add,mul_add]
  map_smul' c f := by
    apply (WithLp.equiv 2 (Fin 3→ℂ)).injective
    funext j
    simp [kernelTestPartial_smul,smul_eq_mul,mul_left_comm]

lemma kernelGradientAt_norm_sq (w : HyperbolicSpace) (f : kernelSmoothTests) :
    ‖kernelGradientAt w f‖^2=kernelTestEnergyDensity f w := by
  rw [PiLp.norm_sq_eq_of_L2,kernelTestEnergyDensity_eq_partials]
  change (∑j:Fin 3,‖(hyperbolicHeight w:ℂ)*kernelTestPartial f w j‖^2)=_
  simp only [norm_mul, norm_real, Real.norm_of_nonneg (hyperbolicHeight_pos w).le, mul_pow, mul_sum]

section
variable (f g : kernelSmoothTests)
include f g

def kernelDirichletPairDensity  (q : KernelQuotient) : ℂ :=
  ((kernelQuotientEnergyDensity (f+g) q:ℂ)-(kernelQuotientEnergyDensity (f-g) q:ℂ)+
    ((kernelQuotientEnergyDensity (f-Complex.I•g) q:ℂ)-
      (kernelQuotientEnergyDensity (f+Complex.I•g) q:ℂ))*Complex.I)/4

lemma kernelDirichletPairDensity_coordinate  (w : HyperbolicSpace) :
    kernelDirichletPairDensity f g (integralOrbitProjection globalKubotaKernel w)=
      inner ℂ (kernelGradientAt w f) (kernelGradientAt w g) := by
  rw [inner_eq_sum_norm_sq_div_four]
  simp only [←map_add,←map_sub,←map_smul,RCLike.ofReal_eq_complex_ofReal,←Complex.ofReal_pow,kernelGradientAt_norm_sq]
  rfl

lemma kernelDirichletPairDensity_integrable  :
    Integrable (kernelDirichletPairDensity f g) (integralQuotientVolume globalKubotaKernel) := by
  have hf : ∀h : kernelSmoothTests,Integrable (fun q => (kernelQuotientEnergyDensity h q:ℂ))
      (integralQuotientVolume globalKubotaKernel) := fun h =>
    (kernelQuotientEnergyDensity_integrable h).ofReal
  exact ((hf (f+g)).sub (hf (f-g)) |>.add (((hf (f-Complex.I•g)).sub (hf (f+Complex.I•g))).mul_const _)).div_const _
end


lemma kernelDirichletPairDensity_add_right (f g h : kernelSmoothTests) (q : KernelQuotient) :
    kernelDirichletPairDensity f (g+h) q=kernelDirichletPairDensity f g q+kernelDirichletPairDensity f h q := by
  induction q using Quotient.inductionOn with
  | _ w => simp only [←show integralOrbitProjection globalKubotaKernel w=Quotient.mk _ w from rfl,
      kernelDirichletPairDensity_coordinate,map_add,inner_add_right]

lemma kernelDirichletPairDensity_smul_right (c : ℂ) (f g : kernelSmoothTests) (q : KernelQuotient) :
    kernelDirichletPairDensity f (c•g) q=c*kernelDirichletPairDensity f g q := by
  induction q using Quotient.inductionOn with
  | _ w => simp only [←show integralOrbitProjection globalKubotaKernel w=Quotient.mk _ w from rfl,
      kernelDirichletPairDensity_coordinate,map_smul,inner_smul_right]

lemma kernelDirichletPairDensity_conj (f g : kernelSmoothTests) (q : KernelQuotient) :
    star (kernelDirichletPairDensity g f q)=kernelDirichletPairDensity f g q := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change star (kernelDirichletPairDensity g f (integralOrbitProjection globalKubotaKernel w))=
      kernelDirichletPairDensity f g (integralOrbitProjection globalKubotaKernel w)
    rw [kernelDirichletPairDensity_coordinate,kernelDirichletPairDensity_coordinate]
    exact inner_conj_symm _ _

lemma kernelDirichletPairDensity_self (f : kernelSmoothTests) (q : KernelQuotient) :
    kernelDirichletPairDensity f f q=(kernelQuotientEnergyDensity f q:ℂ) := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change kernelDirichletPairDensity f f (integralOrbitProjection globalKubotaKernel w)=_
    rw [kernelDirichletPairDensity_coordinate,inner_self_eq_norm_sq_to_K,RCLike.ofReal_eq_complex_ofReal,←Complex.ofReal_pow,kernelGradientAt_norm_sq]
    rfl

def kernelDirichletForm (f g : kernelSmoothTests) : ℂ :=
  ∫q,kernelDirichletPairDensity f g q ∂integralQuotientVolume globalKubotaKernel

lemma kernelDirichletForm_add_right (f g h : kernelSmoothTests) :
    kernelDirichletForm f (g+h)=kernelDirichletForm f g+kernelDirichletForm f h := by
  unfold kernelDirichletForm
  simp_rw [kernelDirichletPairDensity_add_right]
  exact integral_add (kernelDirichletPairDensity_integrable f g) (kernelDirichletPairDensity_integrable f h)

lemma kernelDirichletForm_smul_right (c : ℂ) (f g : kernelSmoothTests) :
    kernelDirichletForm f (c•g)=c*kernelDirichletForm f g := by
  unfold kernelDirichletForm
  simp_rw [kernelDirichletPairDensity_smul_right]
  exact integral_const_mul _ _

lemma kernelDirichletForm_conj (f g : kernelSmoothTests) :
    star (kernelDirichletForm g f)=kernelDirichletForm f g := by
  unfold kernelDirichletForm
  simp only [Complex.star_def]
  rw [←integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (kernelDirichletPairDensity_conj f g)

lemma kernelDirichletForm_self (f : kernelSmoothTests) :
    kernelDirichletForm f f=(kernelDirichletEnergy f:ℂ) := by
  unfold kernelDirichletForm kernelDirichletEnergy
  simp_rw [kernelDirichletPairDensity_self]
  exact integral_complex_ofReal

end CubicEisenstein

namespace CompletedGauss

section

open scoped BigOperators Classical SchwartzMap
open MeasureTheory

theorem finite_integral_energy_bound {κ : Type*} [Fintype κ]
    (b : ℝ→ℂ) (φ : κ→ℝ→ℂ) (E : ℝ) (hE : 0≤E)
    (hb : Integrable (fun t => ‖b t‖))
    (hφ : ∀k,Integrable (fun t => b t*φ k t))
    (hbound : ∀t,(∑k,‖φ k t‖^2)≤E) :
    (∑k,‖∫t : ℝ,b t*φ k t‖^2)≤E*(∫t : ℝ,‖b t‖)^2 := by
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : κ => ℂ)
  let F : ℝ→EuclideanSpace ℂ κ := fun t => e.symm (fun k => b t*φ k t)
  have hF (t : ℝ) : ‖F t‖≤‖b t‖*Real.sqrt E := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [EuclideanSpace.norm_sq_eq,mul_pow,Real.sq_sqrt hE]
    change (∑k,‖b t*φ k t‖^2)≤‖b t‖^2*E
    simp only [norm_mul,mul_pow,←Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hbound t) (sq_nonneg _)
  have he : (∫t : ℝ,F t)=e.symm (fun k => ∫t : ℝ,b t*φ k t) := by
    rw [show F=(fun t => e.symm (fun k => b t*φ k t)) from rfl,e.symm.integral_comp_comm]
    congr 1
    funext k
    exact eval_integral hφ k
  have hn : ‖e.symm (fun k => ∫t : ℝ,b t*φ k t)‖≤(∫t : ℝ,‖b t‖)*Real.sqrt E := by
    rw [←he,←integral_mul_const]
    exact norm_integral_le_of_norm_le (hb.mul_const _) (Filter.Eventually.of_forall hF)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [EuclideanSpace.norm_sq_eq,mul_pow,Real.sq_sqrt hE] at hs
  simpa [e,mul_comm] using hs

open CanonicalQuadraticSieve ActualEisensteinCubic

end

section
open ActualEisensteinCubic CanonicalQuadraticSieve

section
variable (S : Finset (Ideal O)) (Q A T : Ideal O)
include S Q A T

def completedRowFiber  : Finset (Ideal O) :=
  S.filter (fun I => rowPowerfulPart I=A ∧ rowMaskPart I Q=T)

theorem rowResidualPart_injective_on_fiber 
    (hS : ∀I∈S,I≠0) : Set.InjOn (fun I => rowResidualPart I Q) (completedRowFiber S Q A T) := by
  intro I hI J hJ he
  change rowResidualPart I Q=rowResidualPart J Q at he
  obtain ⟨hIS,hIA,hIT⟩ := Finset.mem_filter.mp hI
  obtain ⟨hJS,hJA,hJT⟩ := Finset.mem_filter.mp hJ
  calc
    I = rowPowerfulPart I*rowMaskPart I Q*rowResidualPart I Q := (row_powerful_mask_residual_product I Q (hS I hIS)).symm
    _ = rowPowerfulPart J*rowMaskPart J Q*rowResidualPart J Q := by rw [hIA,hJA,hIT,hJT,he]
    _ = J := row_powerful_mask_residual_product J Q (hS J hJS)

theorem completedRowFiber_residual_range 
    (hbad : ∀P∈fixedBadPrimes,P∣Q) (K : ℝ)
    (hS : ∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) (I : Ideal O)
    (hI : I∈completedRowFiber S Q A T) :
    rowResidualPart I Q∈idealRange (K/((Ideal.absNorm A:ℝ)*(Ideal.absNorm T:ℝ))) := by
  obtain ⟨hIS,hIA,hIT⟩ := Finset.mem_filter.mp hI
  apply mem_idealRange.mpr
  refine ⟨rowResidualPart_admissible I Q hbad,?_⟩
  rw [rowResidualPart_norm I Q (hS I hIS).1,hIA,hIT]
  exact div_le_div_of_nonneg_right (hS I hIS).2 (by positivity)
end


end

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic CanonicalQuadraticSieve

end CompletedGauss

open scoped BigOperators Classical SchwartzMap ContDiff

namespace InitialMeanSquare
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open FirstPassCubeLabels (primeProductNorm columnLog)





variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})






