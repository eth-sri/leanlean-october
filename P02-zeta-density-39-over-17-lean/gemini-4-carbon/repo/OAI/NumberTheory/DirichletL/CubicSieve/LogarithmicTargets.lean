module
public import OAI.NumberTheory.DirichletL.Eisenstein.GreenIdentity

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

end

section
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog primeProductNorm jLabel b0Label)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open JointLogSeparation (frequencyTwist frequencyTwist_apply)

end

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog primeProductNorm b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open RayFourExpansion (RayCharacter)

end SecondPassArithmetic

open Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace CubicEisenstein

@[fun_prop] lemma quadraticHeightDenominator_continuous (A B C D : ℝ) :
    Continuous (fun p : SpatialCoordinates => quadraticHeightDenominator A B C D (p 0) (p 1) (p 2)) := by
  unfold quadraticHeightDenominator
  fun_prop

def smoothFirstCoefficient (s : ℂ) (r : CuspCosets) (j : Fin 3) (p : SpatialCoordinates) : ℂ :=
  smoothSummand s r p*s*(rowLogD (embeddedRow r) p j:ℂ)
def smoothSecondCoefficient (s : ℂ) (r : CuspCosets) (j : Fin 3) (p : SpatialCoordinates) : ℂ :=
  smoothSummand s r p*(s^2*(rowLogD (embeddedRow r) p j:ℂ)^2+s*(rowLogDD (embeddedRow r) p j:ℂ))

lemma smoothFirstCoefficient_eq_deriv (s : ℂ) (r : CuspCosets) (j : Fin 3)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    smoothFirstCoefficient s r j p=deriv (axisSlice (smoothSummand s r) p j) (p j) := by
  unfold axisSlice smoothSummand
  rw [deriv_const_mul_field]
  have hd := (row_axis_hasDerivAt s (embeddedRow r) (embeddedRow_ne_zero r) p hv j).deriv
  unfold axisSlice at hd
  rw [hd]
  unfold smoothFirstCoefficient smoothSummand
  ring

lemma smoothSecondCoefficient_eq_deriv (s : ℂ) (r : CuspCosets) (j : Fin 3)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    smoothSecondCoefficient s r j p=deriv (deriv (axisSlice (smoothSummand s r) p j)) (p j) := by
  unfold axisSlice smoothSummand
  rw [deriv_const_mul_field',deriv_const_mul_field]
  have hd := (row_axis_hasDerivAt_deriv s (embeddedRow r) (embeddedRow_ne_zero r) p hv j).deriv
  unfold axisSlice at hd
  rw [hd]
  unfold smoothSecondCoefficient smoothSummand
  ring

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace CubicEisenstein

lemma spatial_summable_derivative_bounds (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    ∃ U : Set SpatialCoordinates, IsOpen U ∧ p∈U ∧
      ∃ M₀ M₁ M₂ : CuspCosets → ℝ,
      Summable M₀ ∧ Summable M₁ ∧ Summable M₂ ∧
      ∀q∈U, 0<q 2 ∧ ∀r : CuspCosets,
        ‖smoothSummand s r q‖≤M₀ r ∧ ∀j : Fin 3,
        ‖smoothFirstCoefficient s r j q‖≤M₁ r ∧
        ‖smoothSecondCoefficient s r j q‖≤M₂ r := by
  let deltaLoss : ℝ := p 2/2
  have hδ : 0<deltaLoss := by dsimp [deltaLoss]; positivity
  let path := clampedCoordinates deltaLoss hδ
  let C := rowBound (coordinateSection (path p))+1
  have hC : 0<C := by dsimp [C]; linarith [rowBound_pos (coordinateSection (path p))]
  let U : Set SpatialCoordinates := {q | deltaLoss<q 2 ∧ rowBound (coordinateSection (path q))<C}
  have hU : IsOpen U := (isOpen_lt continuous_const (continuous_apply 2)).inter
    (isOpen_lt (continuous_coordinate_rowBound.comp (continuous_clampedCoordinates deltaLoss hδ)) continuous_const)
  have hpU : p∈U := by constructor <;> dsimp [deltaLoss,C] <;> linarith
  obtain ⟨M,hM,hMnonneg,hbound⟩ := coordinate_summable_majorant C s.re s.re hC hs hs
  let c₁ := ‖s‖*(1/deltaLoss)
  let c₂ := ‖s‖^2*(1/deltaLoss)^2 + ‖s‖*(7/deltaLoss^2)
  refine ⟨U,hU,hpU,M,fun r => M r*c₁,fun r => M r*c₂,hM,hM.mul_right _,hM.mul_right _,?_⟩
  intro q hq
  have hpos : 0<q 2 := lt_trans hδ hq.1
  refine ⟨hpos,fun r => ?_⟩
  have hm : ‖smoothSummand s r q‖≤M r := by
    rw [smoothSummand_eq_clamped s r q deltaLoss hδ hq.1.le]
    exact hbound (path q,s) hq.2.le le_rfl le_rfl r
  have hfrac : 1 / q 2 ≤ 1/deltaLoss := one_div_le_one_div_of_le hδ hq.1.le
  have hfrac₂ : 7 / (q 2)^2 ≤ 7/deltaLoss^2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hδ)
    nlinarith [hq.1]
  refine ⟨hm,fun j => ?_⟩
  rw [smoothFirstCoefficient_eq_deriv _ _ _ _ hpos,smoothSecondCoefficient_eq_deriv _ _ _ _ hpos]
  constructor
  · apply (norm_smooth_axis_deriv s r q hpos j).trans
    apply mul_le_mul hm _ (by positivity) (hMnonneg r)
    exact mul_le_mul_of_nonneg_left hfrac (norm_nonneg s)
  · apply (norm_smooth_axis_deriv2 s r q hpos j).trans
    apply mul_le_mul hm _ (by positivity) (hMnonneg r)
    dsimp [c₂]
    gcongr

end CubicEisenstein

end

end OAI
