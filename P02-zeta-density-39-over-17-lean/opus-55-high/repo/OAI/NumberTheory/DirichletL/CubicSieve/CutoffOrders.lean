module
public import OAI.NumberTheory.DirichletL.Eisenstein.BarrierPotential
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section

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
open scoped Classical
open scoped Classical SchwartzMap ContDiff
open MeasureTheory Set
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped Classical SchwartzMap

namespace SecondPassArithmetic

end SecondPassArithmetic

namespace CanonicalUnitEuler
open ActualEisensteinCubic
open CompletedGauss (actualSextic)
open ConcreteTraceCRT (eisEmbedding)

theorem sixth_roots_reduce_injective (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (hg : lambda∉P) (hc : ringChar (ActualEisensteinCubic.O⧸P)≠2) {x y : ActualEisensteinCubic.O}
    (hx : x^6=1) (hy : y^6=1)
    (hxy : Ideal.Quotient.mk P x=Ideal.Quotient.mk P y) : x=y := by
  pm_5266
  have hs : x^2=y^2 := cubic_roots_reduce_injective P hg
    (by simpa only [←pow_mul] using hx)
    (by simpa only [←pow_mul] using hy)
    (by simpa only [map_pow] using congrArg (fun z : ActualEisensteinCubic.O⧸P=>z^2) hxy)
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hs with h|h
  · exact h
  · have hy0 : Ideal.Quotient.mk P y≠0 := by
      intro hz
      have he := congrArg (Ideal.Quotient.mk P) hy
      simp only [map_pow,map_one,hz,zero_pow (by decide : (6:ℕ)≠0)] at he
      exact zero_ne_one he
    have he : -(Ideal.Quotient.mk P y)=Ideal.Quotient.mk P y := by
      simpa only [h,map_neg] using hxy
    have htwo : (2 : ActualEisensteinCubic.O⧸P)*Ideal.Quotient.mk P y=0 := by linear_combination -he
    exact False.elim ((Ring.two_ne_zero hc) ((mul_eq_zero.mp htwo).resolve_right hy0))

lemma unit_pow_six (u : ActualEisensteinCubic.Oˣ) : (u.val : ActualEisensteinCubic.O)^6=1 := by
  have h := pow_card_eq_one' (x:=u)
  rw [PrimaryIdealUnitReindex.card_units_eq_six] at h
  exact congrArg Units.val h

theorem actualSextic_unit_euler (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (hg : lambda∉P) (hc : ringChar (ActualEisensteinCubic.O⧸P)≠2) (u : ActualEisensteinCubic.Oˣ) :
    actualSextic P hg (Ideal.Quotient.mk P u.val) =
      eisEmbedding (u.val^((Nat.card (ActualEisensteinCubic.O⧸P)-1)/6)) := by
  pm_5266
  have hdata : ∃χ : MulChar (ActualEisensteinCubic.O⧸P) ActualEisensteinCubic.O,
      actualSextic P hg=χ.ringHomComp eisEmbedding ∧ χ^6=1 ∧
      ∀v : (ActualEisensteinCubic.O⧸P)ˣ,Ideal.Quotient.mk P (χ v)=v.val^((Nat.card (ActualEisensteinCubic.O⧸P)-1)/6) := by
    refine ⟨_,rfl,(sexticChar_powers P hg).2.2,?_⟩
    exact sexticChar_reduce_unit P hg hc
  obtain ⟨χ,hχ,hχ6,hreduce⟩ := hdata
  let v : (ActualEisensteinCubic.O⧸P)ˣ := Units.map (Ideal.Quotient.mk P).toMonoidHom u
  have hx : χ v.val ^ 6=1 := by
    rw [←MulChar.pow_apply' _ (by decide : (6:ℕ)≠0),hχ6]
    exact MulChar.one_apply v.isUnit
  have hy : (u.val^((Nat.card (ActualEisensteinCubic.O⧸P)-1)/6))^6=1 := by
    rw [←pow_mul,Nat.mul_comm, pow_mul,unit_pow_six,one_pow]
  have he : χ v.val=u.val^((Nat.card (ActualEisensteinCubic.O⧸P)-1)/6) :=
    sixth_roots_reduce_injective P hg hc hx hy (by simpa [v] using hreduce v)
  rw [hχ]
  change eisEmbedding (χ v.val)=_
  exact congrArg eisEmbedding he

end CanonicalUnitEuler

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped Classical Topology ContDiff

section
variable (K : Set KernelQuotient) (hK : MeasurableSet K) (C : ℝ)
include K hK C
lemma kernel_mass_le_weighted_mass_add_core
    (V : KernelQuotient→ℝ) (hV : Continuous V)
    (hlow : ∀q,1-C*(K.indicator (fun _ => (1:ℝ))) q≤V q)
    (f : kernelSmoothTests) :
    ‖kernelSmoothTestsToL2 f‖^2≤
      (∫q,V q*‖f.1 q‖^2∂ integralQuotientVolume globalKubotaKernel)+
        C*‖kernelMassRestrictionCLM K hK (kernelSmoothTestsToL2 f)‖^2 := by
  have hi : Integrable (fun q => ‖f.1 q‖^2) (integralQuotientVolume globalKubotaKernel) :=
    (kernelSmoothTests_memLp f).norm.integrable_sq
  have hki := hi.indicator hK
  have hw := kernelSmoothTest_weighted_mass_integrable V hV f
  have hpoint : ∀q,‖f.1 q‖^2-C*(K.indicator (fun q => ‖f.1 q‖^2)) q≤V q*‖f.1 q‖^2 := by
    intro q
    have hh := mul_le_mul_of_nonneg_right (hlow q) (sq_nonneg ‖f.1 q‖)
    by_cases hq : q∈K
    · simp only [Set.indicator_of_mem hq] at hh ⊢
      nlinarith
    · simp only [Set.indicator_of_notMem hq,mul_zero,sub_zero,one_mul] at hh ⊢
      exact hh
  have hh := integral_mono (hi.sub (hki.const_mul C)) hw hpoint
  simp only [Pi.sub_apply] at hh
  rw [integral_sub hi (hki.const_mul C),integral_const_mul,integral_indicator hK,
    ←kernelSmoothTestsToL2_norm_sq,←kernelMassRestriction_smooth_norm_sq K hK] at hh
  linarith

lemma kernel_compact_coercivity_extend
    (hcore : ∀f : kernelSmoothTests,‖kernelSmoothTestsToL2 f‖^2≤kernelDirichletEnergy f+
      C*‖kernelMassRestrictionCLM K hK (kernelSmoothTestsToL2 f)‖^2)
    (u : KernelEnergyGraph) :
    ‖kernelEnergyMass u‖^2≤‖kernelEnergyGradient u‖^2+C*‖kernelEnergyMassRestriction K hK u‖^2 := by
  exact kernelEnergyGraphCore_dense.induction_on u
    (isClosed_le (by fun_prop) (by fun_prop)) (fun f => by
      change ‖kernelSmoothTestsToL2 f‖^2≤‖kernelGradientToL2 f‖^2+
        C*‖kernelMassRestrictionCLM K hK (kernelSmoothTestsToL2 f)‖^2
      rw [kernelGradientToL2_norm_sq]
      exact hcore f)
end

lemma kernel_barrier_coercivity_of_ground_state
    (hground : ∀f : kernelSmoothTests,
      (∫q,kernelBarrierPotential 2 3 q*‖f.1 q‖^2∂ integralQuotientVolume globalKubotaKernel)≤
        kernelDirichletEnergy f) :
    ∃K : Set KernelQuotient,∃hK : IsCompact K,∃C : ℝ,0≤C ∧
      IsCompactOperator (kernelEnergyMassRestriction K hK.measurableSet) ∧
      ∀u : KernelEnergyGraph,‖kernelEnergyMass u‖^2≤‖kernelEnergyGradient u‖^2+
        C*‖kernelEnergyMassRestriction K hK.measurableSet u‖^2 := by
  obtain ⟨K,hK,C,hC,hlow⟩ := kernelBarrierPotential_lower 2 3 (by norm_num) (by norm_num)
  refine ⟨K,hK,C,hC,kernelEnergyMassRestriction_isCompact K hK,?_⟩
  apply kernel_compact_coercivity_extend
  intro f
  exact (kernel_mass_le_weighted_mass_add_core K hK.measurableSet C
    (kernelBarrierPotential 2 3) (kernelBarrierPotential_continuous 2 3 (by norm_num) (by norm_num))
    hlow f).trans (add_le_add (hground f) le_rfl)

end

open scoped Topology ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section
variable (f : E → ℂ) (u : E → ℝ) (x v : E) (hf : DifferentiableAt ℝ f x) (hu : DifferentiableAt ℝ u x) (hux : u x ≠ 0)
include f u x v hf hu hux
theorem ground_state_test_fderiv :
    fderiv ℝ (fun y => ‖f y‖^2/u y) x v =
      (2*(conj (f x)*fderiv ℝ f x v).re*u x - ‖f x‖^2*fderiv ℝ u x v)/(u x)^2 := by
  have hc : HasDerivAt (fun t : ℝ => x+t•v) v 0 := by
    simpa only [zero_add,one_smul,Pi.add_apply,id_eq] using!
      (hasDerivAt_const (0:ℝ) x).add ((hasDerivAt_id (0:ℝ)).smul_const v)
  have hx : (fun t : ℝ => x+t•v) 0 = x := by simp
  pm_3789 hfc f hf.hasFDerivAt
  pm_3789 huc u hu.hasFDerivAt
  have hzero : (fun t : ℝ => u (x+t•v)) 0 ≠ 0 := by simpa using hux
  have hq := hfc.norm_sq.div huc hzero
  pm_5714 hdiff y f x hf.norm_sq hux
  have hqc : HasDerivAt (fun t : ℝ => ‖f (x+t•v)‖^2/u (x+t•v))
      (fderiv ℝ (fun y => ‖f y‖^2/u y) x v) 0 := by
    have hh : HasFDerivAt (fun y => ‖f y‖^2/u y)
        (fderiv ℝ (fun y => ‖f y‖^2/u y) x) (x+(0:ℝ)•v) := by simpa using hdiff.hasFDerivAt
    simpa only [Function.comp_def] using! hh.comp_hasDerivAt 0 hc
  have he := hqc.unique hq
  simpa only [zero_smul,add_zero,real_inner_eq_re_inner ℂ,RCLike.inner_apply',RCLike.re_to_complex] using he

theorem ground_state_fderiv_inequality :
    fderiv ℝ u x v * fderiv ℝ (fun y => ‖f y‖^2/u y) x v ≤ ‖fderiv ℝ f x v‖^2 := by
  rw [ground_state_test_fderiv f u x v hf hu hux]
  exact ground_state_directional_inequality (u x) (fderiv ℝ u x v) hux (f x) (fderiv ℝ f x v)
end

end CubicEisenstein

open Filter MeasureTheory
open scoped Classical Topology ContDiff Manifold
namespace CubicEisenstein

section

def kernelGroundStateTest (φ : KernelQuotient → ℝ)
    (hφ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ φ)
    (hpos : ∀ q, 0 < φ q) (f : kernelSmoothTests) : kernelSmoothTests := by
  have hn : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ (fun q => ‖f.1 q‖^2) :=
    (contDiff_norm_sq ℂ).contMDiff.comp f.2.1
  have hg := hn.div₀ hφ (fun q => (hpos q).ne')
  refine ⟨fun q => ((‖f.1 q‖^2/φ q : ℝ) : ℂ), Complex.ofRealCLM.contDiff.contMDiff.comp hg, ?_⟩
  apply HasCompactSupport.of_support_subset_isCompact f.2.2
  pm_1300

section
variable (φ : KernelQuotient → ℝ) (hφ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ φ) (hpos : ∀ q, 0 < φ q) (f : kernelSmoothTests)
include φ hφ hpos f
@[simp] theorem kernelGroundStateTest_apply (q : KernelQuotient) :
    (kernelGroundStateTest φ hφ hpos f).1 q = ((‖f.1 q‖^2/φ q : ℝ) : ℂ) := rfl

theorem kernelGroundStateTest_tsupport :
    tsupport (kernelGroundStateTest φ hφ hpos f).1 ⊆ tsupport f.1 := by
  apply closure_minimal _ (isClosed_tsupport f.1)
  pm_1300
end

def kernelTruncatedWeight (χ φ : KernelQuotient → ℝ)
    (hχ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ χ) (hχK : HasCompactSupport χ)
    (hφ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ φ) : kernelSmoothTests := by
  refine ⟨fun q => ((χ q*φ q : ℝ) : ℂ), Complex.ofRealCLM.contDiff.contMDiff.comp (hχ.mul hφ), ?_⟩
  pm_941

theorem kernelRealLift_contDiffAt (φ : KernelQuotient → ℝ)
    (hφ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ φ)
    (p : EuclideanSpatial) (hp : 0 < p 2) :
    ContDiffAt ℝ ∞ (fun p => φ (kernelEuclideanProjection p)) p :=
  (((hφ.comp kernelProjection_contMDiff) (euclideanToHyperbolic p)).comp p
    (euclideanToHyperbolic_contMDiffAt p hp)).contDiffAt

theorem kernelEuclideanProjection_continuousAt (p : EuclideanSpatial) (hp : 0 < p 2) :
    ContinuousAt kernelEuclideanProjection p :=
  (continuous_integralOrbitProjection globalKubotaKernel).continuousAt.comp
    (euclideanToHyperbolic_contMDiffAt p hp).continuousAt

theorem kernelTruncatedWeight_field_eq (χ φ : KernelQuotient → ℝ)
    (hχ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ χ) (hχK : HasCompactSupport χ)
    (hφ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ φ)
    (p : EuclideanSpatial) (hp : 0 < p 2)
    (hχone : χ =ᶠ[𝓝 (kernelEuclideanProjection p)] (fun _ => 1)) :
    kernelTestField (kernelTruncatedWeight χ φ hχ hχK hφ) =ᶠ[𝓝 p]
      (fun q => (φ (kernelEuclideanProjection q) : ℂ)) := by
  have he := hχone.comp_tendsto (kernelEuclideanProjection_continuousAt p hp)
  filter_upwards [he] with q hq
  change χ (kernelEuclideanProjection q) = 1 at hq
  change ((χ (kernelEuclideanProjection q)*φ (kernelEuclideanProjection q) : ℝ) : ℂ) = _
  rw [hq,one_mul]

theorem kernelTruncatedPotential_memLp (χ φ V : KernelQuotient → ℝ)
    (hχ : Continuous χ) (hχK : HasCompactSupport χ) (hφ : Continuous φ) (hV : Continuous V) :
    MemLp (fun q => ((χ q*V q*φ q : ℝ) : ℂ)) 2 (integralQuotientVolume globalKubotaKernel) := by
  have hc : Continuous (fun q => ((χ q*V q*φ q : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((hχ.mul hV).mul hφ)
  apply hc.memLp_of_hasCompactSupport
  pm_941

open Filter MeasureTheory
open scoped Classical Topology ContDiff Manifold ComplexConjugate

theorem ground_state_ofReal_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : E → ℝ) (x v : E) (hu : DifferentiableAt ℝ u x) :
    fderiv ℝ (fun y => (u y : ℂ)) x v = (fderiv ℝ u x v : ℂ) := by
  change fderiv ℝ (Complex.ofRealCLM ∘ u) x v = _
  rw [(Complex.ofRealCLM.hasFDerivAt.comp x hu.hasFDerivAt).fderiv]
  rfl

theorem ground_state_self_product (z : ℂ) : (star z*z).re = ‖z‖^2 := by
  pm_162 Complex.sq_norm Complex.normSq_apply Complex.star_def Complex.mul_re Complex.conj_re Complex.conj_im
  ring

theorem kernelEnergyDensity_euclidean (f : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : 0 < p 2) :
    kernelQuotientEnergyDensity f (kernelEuclideanProjection p) =
      (p 2)^2 * ∑ j : Fin 3, ‖fderiv ℝ (kernelTestField f) p (euclideanCoordinateVector j)‖^2 := by
  have hh := congrArg Complex.re (kernelDirichletPairDensity_euclidean f f p hp)
  rw [kernelDirichletPairDensity_self] at hh
  rw [← Complex.ofReal_pow,Complex.mul_re] at hh
  simpa only [Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,Complex.re_sum,ground_state_self_product] using hh

section
variable (χ φ : KernelQuotient → ℝ) (hχ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ χ) (hχK : HasCompactSupport χ) (hφ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ φ) (hpos : ∀ q, 0 < φ q) (f : kernelSmoothTests)
include χ φ hχ hχK hφ hpos f
theorem kernelGroundState_pair_le_at
    (p : EuclideanSpatial) (hp : 0 < p 2)
    (hχone : χ =ᶠ[𝓝 (kernelEuclideanProjection p)] (fun _ => 1)) :
    (kernelDirichletPairDensity (kernelTruncatedWeight χ φ hχ hχK hφ)
      (kernelGroundStateTest φ hφ hpos f) (kernelEuclideanProjection p)).re ≤
      kernelQuotientEnergyDensity f (kernelEuclideanProjection p) := by
  let u : EuclideanSpatial → ℝ := fun q => φ (kernelEuclideanProjection q)
  let F : EuclideanSpatial → ℂ := kernelTestField f
  have hu : DifferentiableAt ℝ u p := (kernelRealLift_contDiffAt φ hφ p hp).differentiableAt (by simp)
  have hF : DifferentiableAt ℝ F p := (kernelTestField_contDiffAt f p hp).differentiableAt (by simp)
  have hu0 : u p ≠ 0 := (hpos _).ne'
  pm_5714 hG q F p hF.norm_sq hu0
  have hh (j : Fin 3) :
      fderiv ℝ (kernelTestField (kernelTruncatedWeight χ φ hχ hχK hφ)) p (euclideanCoordinateVector j) =
        (fderiv ℝ u p (euclideanCoordinateVector j) : ℂ) := by
    rw [(kernelTruncatedWeight_field_eq χ φ hχ hχK hφ p hp hχone).fderiv_eq]
    exact ground_state_ofReal_fderiv u p _ hu
  have hg (j : Fin 3) :
      fderiv ℝ (kernelTestField (kernelGroundStateTest φ hφ hpos f)) p (euclideanCoordinateVector j) =
        (fderiv ℝ (fun q => ‖F q‖^2/u q) p (euclideanCoordinateVector j) : ℂ) := by
    change fderiv ℝ (fun q => ((‖F q‖^2/u q : ℝ) : ℂ)) p (euclideanCoordinateVector j) = _
    exact ground_state_ofReal_fderiv _ p _ hG
  rw [kernelDirichletPairDensity_euclidean _ _ p hp,kernelEnergyDensity_euclidean f p hp]
  simp only [hh,hg,Complex.star_def,Complex.conj_ofReal,← Complex.ofReal_mul,
    ← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,Complex.re_sum]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro j hj
  exact ground_state_fderiv_inequality F u p (euclideanCoordinateVector j) hF hu hu0

theorem kernelGroundState_pair_le
    (hχone : ∀ q ∈ tsupport f.1, χ =ᶠ[𝓝 q] (fun _ => 1)) (q : KernelQuotient) :
    (kernelDirichletPairDensity (kernelTruncatedWeight χ φ hχ hχK hφ)
      (kernelGroundStateTest φ hφ hpos f) q).re ≤ kernelQuotientEnergyDensity f q := by
  by_cases hq : q ∈ tsupport f.1
  · induction q using Quotient.inductionOn with
    | _ w =>
      have he : kernelEuclideanProjection (hyperbolicEuclideanCoordinates w) =
          integralOrbitProjection globalKubotaKernel w := by
        simp only [kernelEuclideanProjection,Function.comp_apply,euclideanToHyperbolic_coordinates]
      have hh := kernelGroundState_pair_le_at χ φ hχ hχK hφ hpos f
        (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w)
        (by rw [he]; exact hχone _ hq)
      rwa [he] at hh
  · rw [kernelDirichletPairDensity_zero_of_notMem _ _ q
      (fun h => hq (kernelGroundStateTest_tsupport φ hφ hpos f h)),Complex.zero_re]
    exact kernelQuotientEnergyDensity_nonneg f q
end

theorem kernel_ground_state_inequality (φ V : KernelQuotient → ℝ)
    (hφ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ φ)
    (hpos : ∀ q, 0 < φ q) (hV : Continuous V)
    (hPDE : ∀ p : EuclideanSpatial, 0 < p 2 →
      positiveEuclideanLaplacian (fun q => (φ (kernelEuclideanProjection q) : ℂ)) p =
        ((V (kernelEuclideanProjection p)*φ (kernelEuclideanProjection p) : ℝ) : ℂ))
    (f : kernelSmoothTests) :
    (∫ q, V q*‖f.1 q‖^2 ∂ integralQuotientVolume globalKubotaKernel) ≤ kernelDirichletEnergy f := by
  obtain ⟨χ,hχ,hχK,hχone,hχrange⟩ := kernelCompact_smooth_cutoff (tsupport f.1) f.2.2
  let h := kernelTruncatedWeight χ φ hχ hχK hφ
  let g := kernelGroundStateTest φ hφ hpos f
  let A : KernelQuotient → ℂ := fun q => ((χ q*V q*φ q : ℝ) : ℂ)
  have hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel) :=
    kernelTruncatedPotential_memLp χ φ V hχ.continuous hχK hφ.continuous hV
  have hcoord : ∀ p : EuclideanSpatial, 0 < p 2 →
      kernelEuclideanProjection p ∈ tsupport g.1 →
      kernelCoordinateLaplacian h p = A (kernelEuclideanProjection p) := by
    intro p hp hpg
    have hfmem : kernelEuclideanProjection p ∈ tsupport f.1 :=
      kernelGroundStateTest_tsupport φ hφ hpos f hpg
    have hlocal := hχone (kernelEuclideanProjection p) hfmem
    change positiveEuclideanLaplacian (kernelTestField h) p = _
    rw [positiveEuclideanLaplacian_congr _ _ p
      (kernelTruncatedWeight_field_eq χ φ hχ hχK hφ p hp hlocal),hPDE p hp]
    dsimp only [A]
    rw [hlocal.eq_of_nhds,one_mul]
  have hprod (q : KernelQuotient) : star (A q)*g.1 q = ((V q*‖f.1 q‖^2 : ℝ) : ℂ) := by
    change star ((χ q*V q*φ q : ℝ) : ℂ) * ((‖f.1 q‖^2/φ q : ℝ) : ℂ) = _
    by_cases hfzero : f.1 q = 0
    · simp [hfzero]
    · have hq : q ∈ tsupport f.1 := subset_tsupport f.1 hfzero
      have hχq : χ q = 1 := (hχone q hq).eq_of_nhds
      have hφq : φ q ≠ 0 := (hpos q).ne'
      simp only [Complex.star_def,Complex.conj_ofReal,← Complex.ofReal_mul,hχq,one_mul]
      congr 1
      field_simp
  have hgreen : kernelDirichletForm h g =
      ((∫ q, V q*‖f.1 q‖^2 ∂ integralQuotientVolume globalKubotaKernel : ℝ) : ℂ) := by
    rw [kernelDirichletForm_supported_equation h g A hA hcoord]
    simp_rw [hprod]
    exact integral_complex_ofReal
  have hbound : (∫ q, (kernelDirichletPairDensity h g q).re
      ∂ integralQuotientVolume globalKubotaKernel) ≤ kernelDirichletEnergy f := by
    exact integral_mono (kernelDirichletPairDensity_integrable h g).re
      (kernelQuotientEnergyDensity_integrable f)
      (fun q => kernelGroundState_pair_le χ φ hχ hχK hφ hpos f hχone q)
  have hreal : (∫ q, (kernelDirichletPairDensity h g q).re
      ∂ integralQuotientVolume globalKubotaKernel) = (kernelDirichletForm h g).re := by
    simpa only [kernelDirichletForm,RCLike.re_to_complex] using integral_re (kernelDirichletPairDensity_integrable h g)
  rw [hreal,hgreen,Complex.ofReal_re] at hbound
  exact hbound

end

open Filter MeasureTheory
open scoped Classical Topology ContDiff Manifold

theorem kernel_actual_barrier_ground_state (f : kernelSmoothTests) :
    (∫q,kernelBarrierPotential 2 3 q*‖f.1 q‖^2∂ integralQuotientVolume globalKubotaKernel)≤
      kernelDirichletEnergy f :=
  kernel_ground_state_inequality (kernelQuotientBarrier 2 3) (kernelBarrierPotential 2 3)
    (kernelQuotientBarrier_contMDiff 2 3 (by norm_num) (by norm_num))
    (fun q => lt_of_lt_of_le zero_lt_one (kernelQuotientBarrier_one_le 2 3 (by norm_num) (by norm_num) q))
    (kernelBarrierPotential_continuous 2 3 (by norm_num) (by norm_num))
    (kernelBarrierPotential_equation 2 3 (by norm_num) (by norm_num)) f

theorem kernel_global_exterior_coercivity :
    ∃K : Set KernelQuotient,∃hK : IsCompact K,∃C : ℝ,0≤C ∧
      IsCompactOperator (kernelEnergyMassRestriction K hK.measurableSet) ∧
      ∀u : KernelEnergyGraph,‖kernelEnergyMass u‖^2≤‖kernelEnergyGradient u‖^2+
        C*‖kernelEnergyMassRestriction K hK.measurableSet u‖^2 :=
  kernel_barrier_coercivity_of_ground_state kernel_actual_barrier_ground_state

end CubicEisenstein

namespace SecondPassArithmetic

end SecondPassArithmetic

end

end OAI
