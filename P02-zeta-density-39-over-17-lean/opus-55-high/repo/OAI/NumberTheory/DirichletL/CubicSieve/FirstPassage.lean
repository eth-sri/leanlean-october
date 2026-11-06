module
public import OAI.NumberTheory.DirichletL.Poisson.QuadraticProfiles
public import OAI.NumberTheory.DirichletL.Poisson.EisensteinLattice
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

namespace FirstPassCubeLabels

section

open scoped Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic
open RayFourExpansion (RayCharacter crossCoeff)

open ConcreteTraceCRT (eisEmbedding)

end

open ActualEisensteinCubic
open ConcretePrimeRowBridge (conjugateIdealRowSum mobiusIdealColumn
  primePool mem_primePool_iff)
open FirstCauchyArithmetic (supportIdealFamily supportIdealFamily_pos supportIdealFamily_good
  recoveredSupport supportRay)
open RayFourExpansion (RayCharacter)
open ConcreteTraceCRT (eisEmbedding)

end FirstPassCubeLabels

namespace SecondPassArithmetic

section
export OAI.EisensteinSchwartzPoisson (O)
open ActualEisensteinCubic
open MixedCrossSeparation (columnCoefficient columnG convertedColumnBlock quadraticCrossPhase
  columnPrimeCoprime columnCoefficient_cancel_false columnCoefficient_cancel_true)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)

section
variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal] (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) (hg : ∀ i, lambda ∉ Ideal.span {p i}) (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
include ι p hp hcop hg hc
theorem columnCoefficient_norm_one (S : Finset ι) :
    ‖columnCoefficient p hp hcop hg S‖ = 1 := by
  rw [FirstPassCubeLabels.columnCoefficient_eq_gaussBlock, norm_mul, norm_star,
    FiniteGaussPhase.norm_angularFactor _
      (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)),
    FirstPassCubeLabels.gaussBlock_norm_one p hp hcop hg hc S (fun _ => 2)
      (fun _ _ => by decide) (fun _ _ => by decide), one_mul]

theorem columnCoefficient_mul_star (S : Finset ι) :
    columnCoefficient p hp hcop hg S * star (columnCoefficient p hp hcop hg S) = 1 := by
  rw [← starRingEnd_apply, Complex.mul_conj', columnCoefficient_norm_one p hp hcop hg hc S]
  norm_num

theorem convertedColumnBlock_restore
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S : Finset ι) :
    convertedColumnBlock p hp hg S false =
      star (columnCoefficient p hp hcop hg S) * columnG p hp hcop hg S ∧
    convertedColumnBlock p hp hg S true =
      columnCoefficient p hp hcop hg S * finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (-1) *
        star (columnG p hp hcop hg S) := by
  have ha := columnCoefficient_mul_star p hp hcop hg hc S
  constructor
  · have h := congrArg (fun z => star (columnCoefficient p hp hcop hg S) * z)
      (columnCoefficient_cancel_false p hp hcop hg hc hpr S)
    calc
      _ = (columnCoefficient p hp hcop hg S * star (columnCoefficient p hp hcop hg S)) *
          convertedColumnBlock p hp hg S false := by rw [ha, one_mul]
      _ = _ := by convert h using 1 ; ring
  · have h := congrArg (fun z => columnCoefficient p hp hcop hg S * z)
      (columnCoefficient_cancel_true p hp hcop hg hc hpr S)
    calc
      _ = (columnCoefficient p hp hcop hg S * star (columnCoefficient p hp hcop hg S)) *
          convertedColumnBlock p hp hg S true := by rw [ha, one_mul]
      _ = _ := by convert h using 1 <;> ring
end

def secondColumnMinus {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (C : Finset ι → ℂ) (e k : O) (S : Finset ι) : ℂ :=
  columnCoefficient p hp hcop hg S * star (columnG p hp hcop hg S) * C S *
    star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S e) *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S k

def secondColumnPlus {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (C : Finset ι → ℂ) (e k : O) (S : Finset ι) : ℂ :=
  columnCoefficient p hp hcop hg S * finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (-1) *
    star (columnG p hp hcop hg S) * C S *
    star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S e) *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S k

theorem mobius_second_gauss_restore {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S T : Finset ι) (hd : Disjoint S T)
    (C₁ C₂ : Finset ι → ℂ) (e k : O) :
    star (supportMobius (fun i => Ideal.span {p i}) S * C₁ S) *
      (supportMobius (fun i => Ideal.span {p i}) T * C₂ T) *
      activeGaussRowFactor p hp hinj hg T S e k =
    quadraticCrossPhase p hg T S * star (secondColumnMinus p hp hcop hg C₁ e k S) *
      secondColumnPlus p hp hcop hg C₂ e k T := by
  pm_3509
  have hmS := FirstCauchyArithmetic.supportMobius_sq _ hprime hinj S
  have hmT := FirstCauchyArithmetic.supportMobius_sq _ hprime hinj T
  have hr (u : O) :
      finiteSexticRow (activePrimes (fun i => Ideal.span {p i}) T S)
        (fun i => hg i.val) (activeExponent T S) u =
      star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T u) *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S u := by
    have hh := finiteSquarefreeRow_pair_activeSupport (fun i => Ideal.span {p i}) hg T S u
    simpa [Finset.disjoint_iff_inter_eq_empty.mp hd.symm, rowCoprimeMask] using hh.symm
  unfold activeGaussRowFactor
  dsimp only
  rw [FirstCauchyArithmetic.active_productGauss_eq_mobius_converted p hp hinj hg hc hpr,
    MixedCrossSeparation.activeConvertedGauss_eq_columnBlocks p hp hg hpr T S,
    Finset.sdiff_eq_self_of_disjoint hd.symm, Finset.sdiff_eq_self_of_disjoint hd,
    (convertedColumnBlock_restore p hp hcop hg hc hpr S).1,
    (convertedColumnBlock_restore p hp hcop hg hc hpr T).2, hr e, hr k]
  pm_188 secondColumnMinus secondColumnPlus star_mul star_star FirstCauchyArithmetic.star_supportMobius
  calc
    _ = (supportMobius (fun i => Ideal.span {p i}) S * supportMobius (fun i => Ideal.span {p i}) S) *
      (supportMobius (fun i => Ideal.span {p i}) T * supportMobius (fun i => Ideal.span {p i}) T) *
      (quadraticCrossPhase p hg T S *
        (star (columnCoefficient p hp hcop hg S) * columnG p hp hcop hg S * star (C₁ S) *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S e *
          star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S k)) *
        (columnCoefficient p hp hcop hg T * finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T (-1) *
          star (columnG p hp hcop hg T) * C₂ T * star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T e) *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T k)) := by ring
    _ = _ := by rw [hmS, hmT]; ring

end
section

open ActualEisensteinCubic
open MixedCrossSeparation (columnCoefficient)
open FirstPassCubeLabels (row_union mask_union mask_mul)

section Masks
variable {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
  (hg : ∀ i, lambda ∉ P i) (S : Finset ι)

theorem mask_star_row (e : O) :
    rowCoprimeMask P S e * star (finiteSquarefreeRow P hg S e) =
      star (finiteSquarefreeRow P hg S e) := by
  pm_1327 h e
  · have hm : rowCoprimeMask P S e = 0 := by simp [rowCoprimeMask, h]
    rw [FirstPassCubeLabels.row_zero_of_mask_zero P hg S e hm]
    simp
  · simp [rowCoprimeMask, h]

theorem second_child_masked (m r c d e k v : O) :
    rowCoprimeMask P S (m * (e * r)) *
      star (finiteSquarefreeRow P hg S e) *
      finiteSquarefreeRow P hg S d * finiteSquarefreeRow P hg S k *
      finiteSquarefreeRow P hg S c ^ 4 * finiteSquarefreeRow P hg S v ^ 4 =
    rowCoprimeMask P S (m * r) *
      finiteSquarefreeRow P hg S (d * e * k) *
      finiteSquarefreeRow P hg S (c * e * v) ^ 4 := by
  have hr := finiteSquarefreeRow_second_child P hg S d e k c 1 v
  simp only [mul_one] at hr
  rw [mask_mul P hg S m (e * r), mask_mul P hg S e r,
    mask_mul P hg S m r]
  calc
    _ = (rowCoprimeMask P S m * rowCoprimeMask P S r) *
      (rowCoprimeMask P S e * star (finiteSquarefreeRow P hg S e)) *
      finiteSquarefreeRow P hg S d * finiteSquarefreeRow P hg S k *
      finiteSquarefreeRow P hg S c ^ 4 * finiteSquarefreeRow P hg S v ^ 4 := by ring
    _ = _ := by
      rw [mask_star_row]
      have hh := congrArg (fun z : ℂ => (rowCoprimeMask P S m * rowCoprimeMask P S r) * z) hr
      convert hh using 1 <;> ring
end Masks

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def secondPreColumn (Ψ : O →* ℂ) (m c d e k : O)
    (H : Finset ι → ℂ) (S : Finset ι) : ℂ :=
  columnCoefficient p hp hcop hg S * Ψ (∏ i ∈ S, p i) *
    rowCoprimeMask (fun i => Ideal.span {p i}) S m *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S c ^ 4 *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S d *
    star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S e) *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S k * H S

def secondChildColumn (Ψ : O →* ℂ) (m f y : O)
    (H : Finset ι → ℂ) (S : Finset ι) : ℂ :=
  columnCoefficient p hp hcop hg S * Ψ (∏ i ∈ S, p i) *
    rowCoprimeMask (fun i => Ideal.span {p i}) S m *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S f ^ 4 *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S y * H S

theorem secondPreColumn_union
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (Ψ : O →* ℂ) (m r c d e k : O) (H : Finset ι → ℂ)
    (V N : Finset ι) (hd : Disjoint V N) :
    secondPreColumn p hp hcop hg Ψ (m * (e * r)) c d e k H (V ∪ N) =
      secondPreColumn p hp hcop hg Ψ (m * (e * r)) c d e k (fun _ => 1) V *
      secondChildColumn p hp hcop hg Ψ (m * r) (c * e * ∏ i ∈ V, p i) (d * e * k)
        (fun U => H (V ∪ U)) N := by
  have hA := FirstPassCubeLabels.columnCoefficient_union_row_four
    p hp hcop hg hpr N V hd.symm
  rw [Finset.union_comm N V] at hA
  have hrow := second_child_masked (fun i => Ideal.span {p i}) hg N m r c d e k (∏ i ∈ V, p i)
  simp only [secondPreColumn, secondChildColumn, hA, Finset.prod_union hd,
    map_mul, row_union _ hg V N hd, mask_union _ hg V N hd,
    mul_pow, star_mul, mul_one]
  calc
    _ = (columnCoefficient p hp hcop hg V * Ψ (∏ i ∈ V, p i) *
      rowCoprimeMask (fun i => Ideal.span {p i}) V (m * (e * r)) *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V c ^ 4 *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V d *
      star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V e) *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V k) *
      (columnCoefficient p hp hcop hg N * Ψ (∏ i ∈ N, p i) *
        (rowCoprimeMask (fun i => Ideal.span {p i}) N (m * (e * r)) *
          star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N e) *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N d *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N k *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N c ^ 4 *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N (∏ i ∈ V, p i) ^ 4) *
        H (V ∪ N)) := by ring
    _ = _ := by rw [hrow]; ring

end

open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def secondCommonWeight (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k₁ k₂ : O) (V : Finset ι) : ℂ :=
  supportMobius (fun i => Ideal.span {p i}) V *
    star (secondPreColumn p hp hcop hg Ψ₁ (m * (e * r)) c d e k₁ (fun _ => 1) V) *
      secondPreColumn p hp hcop hg Ψ₂ (m * (e * r)) c d e k₂ (fun _ => 1) V

def secondChildSum (F V : Finset ι) (Ψ : O →* ℂ)
    (m r c d e k : O) (H : Finset ι → ℂ) : ℂ :=
  ∑ N ∈ (F \ V).powerset,
    secondChildColumn p hp hcop hg Ψ (m * r) (c * e * ∏ i ∈ V, p i) (d * e * k)
      (fun U => H (V ∪ U)) N

end SecondPassArithmetic

end

end OAI
