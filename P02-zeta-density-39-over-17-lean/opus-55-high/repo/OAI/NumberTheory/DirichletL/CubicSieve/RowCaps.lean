module
public import OAI.NumberTheory.DirichletL.GaussSum.PowerfulParts
public import OAI.NumberTheory.DirichletL.MeanSquare.LogarithmicBins
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
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open EisensteinEmbedding ActualEisensteinCubic
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Ideal NumberField
open Filter Asymptotics Ideal NumberField
open scoped ContDiff FourierTransform SchwartzMap
open scoped Classical
open scoped Classical SchwartzMap ContDiff
open MeasureTheory Set
open ActualEisensteinCubic

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct dilationLabel)
open ConcreteTraceCRT (eisEmbedding)

end SecondPassArithmetic

namespace CompletedGauss
open ActualEisensteinCubic LocalReflectionBrackets

noncomputable abbrev actualSextic := ActualEisensteinCubic.canonicalSextic

def exceptionalPiece (P : Ideal O) [P.IsMaximal] (e : Fin 3) (n b : O) : ℂ :=
  if e=0 then -(rootCard (O ⧸ P) : ℂ)⁻¹
  else if e=1 then (rootCard (O ⧸ P) : ℂ)*(if n∈P then 1 else 0)
  else (rootCard (O ⧸ P) : ℂ)*(if n∉P ∧ b∈P then 1 else 0)

section
variable (P : Ideal O) [P.IsMaximal]
include P
theorem bracket_four_eq_sum_exceptionalPiece
    (hg : lambda∉P) (n b : O) :
    bracket (actualSextic P hg) 4 (Ideal.Quotient.mk P (n*b^3)) =
      ∑e : Fin 3, exceptionalPiece P e n b := by
  rw [canonical_bracket_four_cube_split]
  simp [Fin.sum_univ_succ,exceptionalPiece]
  ring

theorem rootCard_eq_sqrt_absNorm :
    rootCard (O ⧸ P)=Real.sqrt (Ideal.absNorm P:ℝ) := by
  rw [rootCard,←Nat.card_eq_fintype_card]
  rfl

theorem exceptionalPiece_norm_le
    (e : Fin 3) (n b : O) :
    ‖exceptionalPiece P e n b‖≤(if e=0 then (rootCard (O ⧸ P))⁻¹ else rootCard (O ⧸ P)) := by
  have hr : 0≤ rootCard (O ⧸ P) := rootCard_pos.le
  fin_cases e<;> simp only [exceptionalPiece,Fin.isValue,Fin.zero_eta,↓reduceIte]
  · simp [abs_of_nonneg hr]
  · by_cases hn : n∈P <;> simp [hn,abs_of_nonneg hr,hr]
  · by_cases hn : n∉P ∧ b∈P <;> simp [hn,abs_of_nonneg hr,hr]
end

end CompletedGauss

namespace CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss

end CanonicalQuadraticSieve

open Filter MeasureTheory
open scoped Classical Topology MatrixGroups Matrix ContDiff

namespace CubicEisenstein

def spatialHorizontal (p : SpatialCoordinates) : ℂ := (p 0:ℂ)+(p 1:ℂ)*Complex.I

def mobiusSpatialDenominator (g : SL(2,ℂ)) (p : SpatialCoordinates) : ℝ :=
  Complex.normSq (g 1 0*spatialHorizontal p+g 1 1)+Complex.normSq (g 1 0)*(p 2)^2

def mobiusSpatialHorizontal (g : SL(2,ℂ)) (p : SpatialCoordinates) : ℂ :=
  ((g 0 0*spatialHorizontal p+g 0 1)*star (g 1 0*spatialHorizontal p+g 1 1)+
    g 0 0*star (g 1 0)*(p 2:ℂ)^2)/(mobiusSpatialDenominator g p:ℂ)

def mobiusSpatial (g : SL(2,ℂ)) (p : SpatialCoordinates) : SpatialCoordinates :=
  ![(mobiusSpatialHorizontal g p).re,(mobiusSpatialHorizontal g p).im,
    p 2/mobiusSpatialDenominator g p]

section
variable (g : SL(2,ℂ)) (p : SpatialCoordinates) (hp : 0<p 2)
include g p hp
lemma mobiusSpatialDenominator_pos :
    0< mobiusSpatialDenominator g p := by
  simpa only [mobiusSpatialDenominator,Complex.normSq_eq_norm_sq] using
    mobius_denominator_pos g (spatialHorizontal p) (p 2) hp

lemma mobiusSpatial_positive :
    0< mobiusSpatial g p 2 := div_pos hp (mobiusSpatialDenominator_pos g p hp)

lemma mobiusSpatial_coordinates :
    hyperbolicSpatialCoordinates (g • upperPoint (spatialHorizontal p) (p 2) hp)=mobiusSpatial g p := by
  rw [mobius_upperPoint]
  pm_341 hyperbolicSpatialCoordinates hyperbolicHorizontal_upperPoint hyperbolicHeight_upperPoint mobiusSpatial mobiusSpatialHorizontal mobiusSpatialDenominator Complex.normSq_eq_norm_sq
end

lemma spatialHorizontal_contDiff : ContDiff ℝ ∞ spatialHorizontal := by
  unfold spatialHorizontal
  exact (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 0)).add
    ((Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)).mul contDiff_const)

section
variable (g : SL(2,ℂ))
include g
lemma mobiusSpatialDenominator_contDiff : ContDiff ℝ ∞ (mobiusSpatialDenominator g) := by
  unfold mobiusSpatialDenominator
  have hz : ContDiff ℝ ∞ (fun p => g 1 0*spatialHorizontal p+g 1 1) :=
    (contDiff_const.mul spatialHorizontal_contDiff).add contDiff_const
  have hre := Complex.reCLM.contDiff.comp hz
  have him := Complex.imCLM.contDiff.comp hz
  change ContDiff ℝ ∞ (fun p =>
    (g 1 0*spatialHorizontal p+g 1 1).re*(g 1 0*spatialHorizontal p+g 1 1).re+
    (g 1 0*spatialHorizontal p+g 1 1).im*(g 1 0*spatialHorizontal p+g 1 1).im+
    Complex.normSq (g 1 0)*(p 2)^2)
  exact ((hre.mul hre).add (him.mul him)).add (contDiff_const.mul ((contDiff_apply ℝ ℝ 2).pow 2))

lemma mobiusSpatial_contDiffAt (p : SpatialCoordinates) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (mobiusSpatial g) p := by
  have hD := (mobiusSpatialDenominator_contDiff g).contDiffAt (x := p)
  have hDc : ContDiffAt ℝ ∞ (fun p => (mobiusSpatialDenominator g p:ℂ)) p :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp p hD
  have hnum : ContDiffAt ℝ ∞ (fun p : SpatialCoordinates =>
      (g 0 0*spatialHorizontal p+g 0 1)*star (g 1 0*spatialHorizontal p+g 1 1)+
        g 0 0*star (g 1 0)*(p 2:ℂ)^2) p := by
    have hz := spatialHorizontal_contDiff.contDiffAt (x := p)
    have hcz : ContDiffAt ℝ ∞ (fun p => g 1 0*spatialHorizontal p+g 1 1) p :=
      (contDiffAt_const.mul hz).add contDiffAt_const
    have hc := Complex.conjCLE.contDiff.contDiffAt.comp p hcz
    have hv : ContDiffAt ℝ ∞ (fun p : SpatialCoordinates => (p 2:ℂ)) p :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp p (contDiff_apply ℝ ℝ 2).contDiffAt
    exact (((contDiffAt_const.mul hz).add contDiffAt_const).mul hc).add
      (contDiffAt_const.mul (hv.pow 2))
  have hh : ContDiffAt ℝ ∞ (mobiusSpatialHorizontal g) p :=
    by
      unfold mobiusSpatialHorizontal
      simp only [div_eq_mul_inv]
      exact hnum.mul (hDc.inv (Complex.ofReal_ne_zero.mpr (mobiusSpatialDenominator_pos g p hp).ne'))
  apply contDiffAt_pi.mpr
  intro j
  fin_cases j
  · exact Complex.reCLM.contDiff.contDiffAt.comp p hh
  · exact Complex.imCLM.contDiff.contDiffAt.comp p hh
  · exact (by fun_prop : ContDiffAt ℝ ∞ (fun p : SpatialCoordinates => p 2) p).div hD
      (mobiusSpatialDenominator_pos g p hp).ne'
end

abbrev PositiveSpatial := {p : SpatialCoordinates // 0<p 2}

def positiveSpatialToUpper (p : PositiveSpatial) : UpperCoordinates :=
  ⟨(spatialHorizontal p.1,p.1 2),p.2⟩
def upperToPositiveSpatial (p : UpperCoordinates) : PositiveSpatial :=
  ⟨![p.1.1.re,p.1.1.im,p.1.2],p.2⟩

lemma positiveSpatialToUpper_continuous : Continuous positiveSpatialToUpper := by
  apply Continuous.subtype_mk
  exact (spatialHorizontal_contDiff.continuous.comp continuous_subtype_val).prodMk
    ((continuous_apply 2).comp continuous_subtype_val)
lemma upperToPositiveSpatial_continuous : Continuous upperToPositiveSpatial := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  fin_cases j <;> fun_prop

def positiveSpatialUpperHomeomorph : PositiveSpatial ≃ₜ UpperCoordinates where
  toFun := positiveSpatialToUpper
  invFun := upperToPositiveSpatial
  left_inv p := by
    apply Subtype.ext
    funext j
    fin_cases j <;> simp [upperToPositiveSpatial,positiveSpatialToUpper,spatialHorizontal]
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact Complex.re_add_im _
    · rfl
  continuous_toFun := positiveSpatialToUpper_continuous
  continuous_invFun := upperToPositiveSpatial_continuous

def positiveSpatialHomeomorph : PositiveSpatial ≃ₜ HyperbolicSpace :=
  positiveSpatialUpperHomeomorph.trans upperCoordinatesHomeomorph

lemma hyperbolicSpatial_isOpenEmbedding : Topology.IsOpenEmbedding hyperbolicSpatialCoordinates := by
  have ho : IsOpen {p : SpatialCoordinates | 0<p 2} := isOpen_lt continuous_const (by fun_prop)
  have he := ho.isOpenEmbedding_subtypeVal.comp positiveSpatialHomeomorph.symm.isOpenEmbedding
  exact he

end CubicEisenstein

open scoped Classical Topology MatrixGroups Matrix ContDiff Manifold

namespace CubicEisenstein

abbrev KernelQuotient := IntegralOrbitQuotient globalKubotaKernel

def hyperbolicSpatialChart : OpenPartialHomeomorph HyperbolicSpace SpatialCoordinates :=
  hyperbolicSpatial_isOpenEmbedding.toOpenPartialHomeomorph hyperbolicSpatialCoordinates

@[simp] lemma hyperbolicSpatialChart_apply (w : HyperbolicSpace) :
    hyperbolicSpatialChart w=hyperbolicSpatialCoordinates w := rfl

@[simp] lemma hyperbolicSpatialChart_source : hyperbolicSpatialChart.source=Set.univ := rfl

lemma hyperbolicSpatialChart_target_positive {p : SpatialCoordinates}
    (hp : p∈hyperbolicSpatialChart.target) : 0<p 2 := by
  have he := hyperbolicSpatialChart.right_inv hp
  have hh := hyperbolicSpatialCoordinates_positive (hyperbolicSpatialChart.symm p)
  rwa [← hyperbolicSpatialChart_apply,he] at hh

def kernelLocalLift (w : HyperbolicSpace) : OpenPartialHomeomorph KernelQuotient HyperbolicSpace :=
  kernelQuotient_localHomeomorph.localInverseAt w

@[simp] lemma kernelLocalLift_symm (w : HyperbolicSpace) :
    (kernelLocalLift w).symm=integralOrbitProjection globalKubotaKernel :=
  kernelQuotient_localHomeomorph.localInverseAt_symm w

lemma kernelLocalLift_project {w : HyperbolicSpace} {q : KernelQuotient}
    (hq : q∈(kernelLocalLift w).source) :
    integralOrbitProjection globalKubotaKernel (kernelLocalLift w q)=q :=
  kernelQuotient_localHomeomorph.apply_localInverseAt_of_mem hq

section
variable {X : Type*} [TopologicalSpace X] {f g : X→HyperbolicSpace} {x : X} (hf : ContinuousAt f x) (hg : ContinuousAt g x)
include X f g x hf hg
lemma kernel_lifts_eventually_eq
    (hfg : f x=g x)
    (hproj : (fun y => integralOrbitProjection globalKubotaKernel (f y))=ᶠ[𝓝 x]
      (fun y => integralOrbitProjection globalKubotaKernel (g y))) : f=ᶠ[𝓝 x]g := by
  obtain ⟨U,hU,hx,hUinj⟩ := kernelQuotient_localHomeomorph.isLocallyInjective (f x)
  have hfn : ∀ᶠ y in 𝓝 x,f y∈U := hf (hU.mem_nhds hx)
  have hgn : ∀ᶠ y in 𝓝 x,g y∈U := hg (hU.mem_nhds (hfg ▸ hx))
  filter_upwards [hfn,hgn,hproj] with y hyf hyg hye
  exact hUinj hyf hyg hye

lemma kernel_lifts_eventually_deck
    (hproj : (fun y => integralOrbitProjection globalKubotaKernel (f y))=ᶠ[𝓝 x]
      (fun y => integralOrbitProjection globalKubotaKernel (g y))) :
    ∃M : globalKubotaKernel, f=ᶠ[𝓝 x](fun y => integralComplexMatrix M • g y) := by
  have he := (integralOrbitProjection_eq_iff globalKubotaKernel (f x) (g x)).mp
    hproj.self_of_nhds
  obtain ⟨M,hM⟩ := MulAction.mem_orbit_iff.mp he
  refine ⟨M,kernel_lifts_eventually_eq hf
    ((continuous_hyperbolic_action (integralComplexMatrix M)).continuousAt.comp hg) hM.symm ?_⟩
  filter_upwards [hproj] with y hy
  simpa only [integralOrbitProjection_eq] using hy
end

lemma mobiusSpatial_coordinates_global (g : SL(2,ℂ)) (w : HyperbolicSpace) :
    hyperbolicSpatialCoordinates (g•w)=mobiusSpatial g (hyperbolicSpatialCoordinates w) := by
  have hp := hyperbolicSpatialCoordinates_positive w
  have hr := hyperbolicSpatialCoordinates_reconstruct w
  nth_rw 1 [← hr]
  exact mobiusSpatial_coordinates g (hyperbolicSpatialCoordinates w) hp

def kernelCoordinateTransition (w : HyperbolicSpace) (p : SpatialCoordinates) : SpatialCoordinates :=
  hyperbolicSpatialCoordinates (kernelLocalLift w
    (integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm p)))

section
variable (w : HyperbolicSpace) (p : SpatialCoordinates) (hp : p∈hyperbolicSpatialChart.target) (hq : integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm p)∈ (kernelLocalLift w).source)
include w p hp hq
lemma kernelCoordinateTransition_eventually :
    ∃M : globalKubotaKernel,kernelCoordinateTransition w=ᶠ[𝓝 p]
      mobiusSpatial (integralComplexMatrix M) := by
  have hc : ContinuousAt hyperbolicSpatialChart.symm p :=
    hyperbolicSpatialChart.symm.continuousAt hp
  have hπ : ContinuousAt (fun y => integralOrbitProjection globalKubotaKernel
      (hyperbolicSpatialChart.symm y)) p :=
    (continuous_integralOrbitProjection globalKubotaKernel).continuousAt.comp hc
  have hl : ContinuousAt (fun y => kernelLocalLift w (integralOrbitProjection globalKubotaKernel
      (hyperbolicSpatialChart.symm y))) p :=
    ((kernelLocalLift w).continuousAt hq).comp
      (f := fun y : SpatialCoordinates => integralOrbitProjection globalKubotaKernel
        (hyperbolicSpatialChart.symm y)) hπ
  have hqn : ∀ᶠ y in 𝓝 p,integralOrbitProjection globalKubotaKernel
      (hyperbolicSpatialChart.symm y)∈(kernelLocalLift w).source :=
    hπ ((kernelLocalLift w).open_source.mem_nhds hq)
  have hproj : (fun y => integralOrbitProjection globalKubotaKernel (kernelLocalLift w
      (integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm y))))=ᶠ[𝓝 p]
      (fun y => integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm y)) := by
    filter_upwards [hqn] with y hy
    exact kernelLocalLift_project hy
  obtain ⟨M,hM⟩ := kernel_lifts_eventually_deck hl hc hproj
  refine ⟨M,?_⟩
  filter_upwards [hM,hyperbolicSpatialChart.open_target.mem_nhds hp] with y hy hyt
  change hyperbolicSpatialCoordinates _=mobiusSpatial _ y
  rw [hy,mobiusSpatial_coordinates_global]
  exact congrArg _ (hyperbolicSpatialChart.right_inv hyt)

lemma kernelCoordinateTransition_contDiffAt : ContDiffAt ℝ ∞ (kernelCoordinateTransition w) p := by
  obtain ⟨M,hM⟩ := kernelCoordinateTransition_eventually w p hp hq
  exact (mobiusSpatial_contDiffAt _ p (hyperbolicSpatialChart_target_positive hp)).congr_of_eventuallyEq hM
end

def kernelQuotientChart (q : KernelQuotient) : OpenPartialHomeomorph KernelQuotient SpatialCoordinates :=
  (kernelLocalLift q.out).trans hyperbolicSpatialChart

@[simp] lemma kernelQuotientChart_symm (q : KernelQuotient) (p : SpatialCoordinates) :
    (kernelQuotientChart q).symm p=
      integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm p) := by
  change (kernelLocalLift q.out).symm (hyperbolicSpatialChart.symm p)=_
  rw [kernelLocalLift_symm]

lemma kernelQuotientChart_contDiffOn (q r : KernelQuotient) :
    ContDiffOn ℝ ∞ ((kernelQuotientChart q).symm.trans (kernelQuotientChart r))
      ((kernelQuotientChart q).symm.trans (kernelQuotientChart r)).source := by
  intro p hp
  have hp' : p∈hyperbolicSpatialChart.target := hp.1.1
  have hq' : integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm p)∈
      (kernelLocalLift r.out).source := by
    rw [← kernelQuotientChart_symm q p]
    exact hp.2.1
  have he : (fun p => ((kernelQuotientChart q).symm.trans (kernelQuotientChart r)) p)=
      kernelCoordinateTransition r.out := by
    funext y
    change hyperbolicSpatialChart (kernelLocalLift r.out ((kernelQuotientChart q).symm y))=_
    rw [kernelQuotientChart_symm]
    rfl
  change ((kernelQuotientChart q).symm.trans (kernelQuotientChart r) : SpatialCoordinates→SpatialCoordinates)=_ at he
  rw [he]
  exact (kernelCoordinateTransition_contDiffAt r.out p hp' hq').contDiffWithinAt

end CubicEisenstein

end

end OAI
