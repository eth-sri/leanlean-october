module
public import OAI.NumberTheory.DirichletL.QuadraticSieve.IdealQuotients

@[expose] public section

namespace OAI

noncomputable section

namespace FirstPassCubeLabels

open scoped BigOperators Topology FourierTransform SchwartzMap Classical LSeries.notation ArithmeticFunction.Moebius ContDiff
open MulChar AddChar Filter Asymptotics MeasureTheory Real Finset Complex ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount EisensteinEmbedding ConcreteTraceCRT Ideal NumberField RingOfIntegers UniqueFactorizationMonoid Set

section


section
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)

def actualFirstKernel {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ lengthScale : ℝ) (d h : O) : ℂ :=
  ∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
    (V₁ (columnLog p X₁ N) * V₂ (columnLog p X₂ P)) *
    ((lengthScale : ℂ) / (‖eisEmbedding (∏ i ∈ (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂, p i)‖ : ℂ)) *
    paperRadialFourier W (lengthScale * ‖eisEmbedding h‖ ^ 2 /
      (‖eisEmbedding d‖ ^ 2 * primeProductNorm p ((N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂))) *
    threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h else 0

end

section
open FirstCauchyArithmetic (supportMobius supportRay supportConjugateSum)
open RayFourExpansion (RayCharacter)

section Local
variable {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
  (hg : ∀ i, lambda ∉ P i)

theorem row_union (S T : Finset ι) (hd : Disjoint S T) (a : O) :
    finiteSquarefreeRow P hg (S ∪ T) a =
      finiteSquarefreeRow P hg S a * finiteSquarefreeRow P hg T a := by
  exact Finset.prod_union hd

include hg in
theorem mask_union (S T : Finset ι) (hd : Disjoint S T) (a : O) :
    rowCoprimeMask P (S ∪ T) a = rowCoprimeMask P S a * rowCoprimeMask P T a := by
  simp only [← row_sixth P hg, row_union P hg S T hd, mul_pow]

omit [DecidableEq ι] in
theorem row_four_star (S : Finset ι) (f h : O) :
    finiteSquarefreeRow P hg S f ^ 4 * star (finiteSquarefreeRow P hg S h) =
      star (finiteSquarefreeRow P hg S (h * f ^ 2)) := by
  have hf : star (finiteSquarefreeRow P hg S (f ^ 2)) =
      finiteSquarefreeRow P hg S f ^ 4 := by
    rw [row_pow, star_pow, finiteSquarefreeRow_conj_as_row_label]
    calc
      _ = finiteSquarefreeRow P hg S f ^ 4 * finiteSquarefreeRow P hg S f ^ 6 := by ring
      _ = _ := by
        rw [row_sixth]
        simpa only [pow_one] using row_power_mul_mask_power P hg S f 4 1 (by decide)
  rw [finiteSquarefreeRow_mul, star_mul, hf]

def beforeDilationLabel {κ : Type*} (p : κ → O) (B : Finset κ)
    (v : κ → ℕ) (ε₁ ε₂ : κ → Bool) (side : Bool) (c d f : O) (S : Finset ι) : ℂ :=
  finiteSquarefreeRow P hg S c ^ 4 * finiteSquarefreeRow P hg S d *
    (rowCoprimeMask P S (cubeRadical p B) *
      finiteSquarefreeRow P hg S (aLabel p B (if side then ε₂ else ε₁)) ^ 4 *
      finiteSquarefreeRow P hg S (crtLabel p B v ε₁ ε₂ side)) *
    finiteSquarefreeRow P hg S f ^ 4

def afterDilationLabel {κ : Type*} (p : κ → O) (B : Finset κ)
    (v : κ → ℕ) (ε₁ ε₂ : κ → Bool) (c d : O) (S : Finset ι) : ℂ :=
  finiteSquarefreeRow P hg S (c * jLabel p B v ε₁ ε₂) ^ 4 *
    finiteSquarefreeRow P hg S d * rowCoprimeMask P S (b0Label p B v ε₁ ε₂)

theorem beforeDilationLabel_union {κ : Type*} (p : κ → O) (B : Finset κ)
    (v : κ → ℕ) (ε₁ ε₂ : κ → Bool) (side : Bool) (c d f : O)
    (S T : Finset ι) (hd : Disjoint S T) :
    beforeDilationLabel P hg p B v ε₁ ε₂ side c d f (S ∪ T) =
      beforeDilationLabel P hg p B v ε₁ ε₂ side c d f S *
      beforeDilationLabel P hg p B v ε₁ ε₂ side c d f T := by
  simp only [beforeDilationLabel, row_union P hg S T hd, mask_union P hg S T hd, mul_pow]
  ring

omit [DecidableEq ι] in
theorem beforeDilationLabel_norm_le_one {κ : Type*} (p : κ → O) (B : Finset κ)
    (v : κ → ℕ) (ε₁ ε₂ : κ → Bool) (side : Bool) (c d f : O) (S : Finset ι) :
    ‖beforeDilationLabel P hg p B v ε₁ ε₂ side c d f S‖ ≤ 1 := by
  have hm : ‖rowCoprimeMask P S (cubeRadical p B)‖ ≤ 1 := by
    unfold rowCoprimeMask
    split_ifs <;> simp
  simp only [beforeDilationLabel, norm_mul, norm_pow]
  calc
    _ ≤ (1:ℝ)^4 * 1 * (1 * 1^4 * 1) * 1^4 := by
      gcongr <;> first | exact hm | exact finiteSquarefreeRow_norm_le_one P hg S _
    _ = 1 := by norm_num

omit [DecidableEq ι] in
theorem beforeDilationLabel_star_row {κ : Type*} (p : κ → O) (B : Finset κ)
    (v : κ → ℕ) (ε₁ ε₂ : κ → Bool) (hv : ∀ j ∈ B, 0 < v j)
    (side : Bool) (c d f h : O) (S : Finset ι) :
    beforeDilationLabel P hg p B v ε₁ ε₂ side c d f S *
      star (finiteSquarefreeRow P hg S h) =
    afterDilationLabel P hg p B v ε₁ ε₂ c d S *
      star (finiteSquarefreeRow P hg S (h * f^2 * dilationLabel p B v ε₁ ε₂)) := by
  unfold beforeDilationLabel afterDilationLabel
  calc
    _ = (finiteSquarefreeRow P hg S c ^ 4 * finiteSquarefreeRow P hg S d) *
      ((rowCoprimeMask P S (cubeRadical p B) *
        finiteSquarefreeRow P hg S (aLabel p B (if side then ε₂ else ε₁)) ^ 4 *
        finiteSquarefreeRow P hg S (crtLabel p B v ε₁ ε₂ side)) *
        (finiteSquarefreeRow P hg S f ^ 4 * star (finiteSquarefreeRow P hg S h))) := by ring
    _ = _ := by
      rw [row_four_star, first_pass_after_dual_dilation P hg S p B v ε₁ ε₂ hv side]
      simp only [finiteSquarefreeRow_mul, mul_pow]
      ring
end Local

theorem rayIdealRow_eq_supportRow {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D : Finset ι)
    (C : Finset ι → ℂ) (negative : Bool) (χ : RayCharacter) (h : O) :
    rayIdealRow p hg F C negative χ D h =
    supportConjugateSum (fun i => Ideal.span {p i}) hg (F \ D)
      (fun U => (if negative then star (supportRay p χ U) else supportRay p χ U) * C (D ∪ U)) h := by
  symm
  exact FirstCauchyArithmetic.supportConjugateSum_eq_conjugateIdealRowSum
    (fun i => Ideal.span {p i}) hinj hg (F \ D) _ h

def dilatedRayColumn {ι κ : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F D : Finset ι) (C : Finset ι → ℂ) (negative : Bool) (χ : RayCharacter)
    (q : κ → O) (B : Finset κ) (v : κ → ℕ) (ε₁ ε₂ : κ → Bool) (c d y : O) : ℂ :=
  supportConjugateSum (fun i => Ideal.span {p i}) hg (F \ D)
    (fun U => (if negative then star (supportRay p χ U) else supportRay p χ U) *
      C (D ∪ U) * afterDilationLabel (fun i => Ideal.span {p i}) hg q B v ε₁ ε₂ c d U) y

theorem rayIdealRow_beforeDilation {ι κ : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D : Finset ι)
    (C : Finset ι → ℂ) (negative : Bool) (χ : RayCharacter)
    (q : κ → O) (B : Finset κ) (v : κ → ℕ) (ε₁ ε₂ : κ → Bool)
    (hv : ∀ j ∈ B, 0 < v j) (side : Bool) (c d f h : O) :
    rayIdealRow p hg F
      (fun S => C S * beforeDilationLabel (fun i => Ideal.span {p i}) hg q B v ε₁ ε₂ side c d f S)
      negative χ D h =
    beforeDilationLabel (fun i => Ideal.span {p i}) hg q B v ε₁ ε₂ side c d f D *
      dilatedRayColumn p hg F D C negative χ q B v ε₁ ε₂ c d
        (h * f ^ 2 * dilationLabel q B v ε₁ ε₂) := by
  rw [rayIdealRow_eq_supportRow p hinj]
  unfold dilatedRayColumn supportConjugateSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  have hd : Disjoint D U := by
    exact Finset.disjoint_left.mpr (fun i hiD hiU =>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hU) hiU)).2 hiD)
  dsimp only
  rw [beforeDilationLabel_union _ hg q B v ε₁ ε₂ side c d f D U hd]
  calc
    _ = beforeDilationLabel (fun i => Ideal.span {p i}) hg q B v ε₁ ε₂ side c d f D *
      supportMobius (fun i => Ideal.span {p i}) U *
      ((if negative then star (supportRay p χ U) else supportRay p χ U) * C (D ∪ U)) *
      (beforeDilationLabel (fun i => Ideal.span {p i}) hg q B v ε₁ ε₂ side c d f U *
        star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U h)) := by ring
    _ = _ := by
      rw [beforeDilationLabel_star_row _ hg q B v ε₁ ε₂ hv side c d f h U]
      ring

def originalLabelColumn {ι : Type*} (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (B : Finset ι) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (c f : O) (S : Finset ι) : ℂ :=
  C S * rowCoprimeMask (fun i => Ideal.span {p i}) S (cubeRadical p B) *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S
      (aLabel p B (if negative then ε₂ else ε₁) * c) ^ 4 *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S f ^ 4

def cubeCoreCoefficient {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (t : ℝ) (S : Finset ι) : ℂ :=
  if negative then
    star (fixedRayExpansion p (cubeOddSupport B v ε₁ ε₂) S) *
      star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (-1)) *
      MixedCrossSeparation.columnG p hp hcop hg S * C S *
      star (V (y S) * FourierBridge.logPhase t (-(y S)))
  else
    fixedRayExpansion p (cubeOddSupport B v ε₁ ε₂) S *
      MixedCrossSeparation.columnG p hp hcop hg S * C S *
      (V (y S) * FourierBridge.logPhase t (-(y S)))

theorem cubeLogCoefficient_originalLabel {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (t : ℝ) (c d f : O) (S : Finset ι) :
    cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ negative
      (originalLabelColumn p hg B ε₁ ε₂ negative C c f) V y t d S =
    cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t S *
      beforeDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ negative c d f S := by
  cases negative <;>
    simp only [cubeLogCoefficient, cubeCoreCoefficient, cubeMinusCoefficient,
      cubePlusCoefficient, FirstCauchyArithmetic.firstPassColumnMinus,
      FirstCauchyArithmetic.firstPassColumnPlus, logTwistMinus, logTwistPlus,
      originalLabelColumn, beforeDilationLabel, Bool.false_eq_true, ite_false, ite_true,
      finiteSquarefreeRow_mul, mul_pow] <;> ring

theorem rayIdealRow_cube_labels {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ j ∈ B, 0 < v j)
    (negative : Bool) (χ : RayCharacter) (C : Finset ι → ℂ) (V : ℝ → ℂ)
    (y : Finset ι → ℝ) (t : ℝ) (c d f h : O) :
    rayIdealRow p hg F
      (cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ negative
        (originalLabelColumn p hg B ε₁ ε₂ negative C c f) V y t d) negative χ D h =
    beforeDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ negative c d f D *
      dilatedRayColumn p hg F D (cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t)
        negative χ p B v ε₁ ε₂ c d (h * f ^ 2 * dilationLabel p B v ε₁ ε₂) := by
  have he : cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ negative
      (originalLabelColumn p hg B ε₁ ε₂ negative C c f) V y t d =
    fun S => cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t S *
      beforeDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ negative c d f S := by
    funext S
    exact cubeLogCoefficient_originalLabel p hp hcop hg B v ε₁ ε₂ negative C V y t c d f S
  rw [he]
  exact rayIdealRow_beforeDilation p hinj hg F D _ negative χ p B v ε₁ ε₂ hv negative c d f h

end

open ConcreteTraceCRT (eisEmbedding)

end

section
open RayFourExpansion (RayCharacter crossCoeff)

theorem blockRow_norm_le_one {ι : Type*} (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (S : Finset ι) (e : ι → ℕ) (a : O) : ‖blockRow p hg S e a‖ ≤ 1 := by
  rw [blockRow_eq_product, norm_prod]
  calc
    _ ≤ ∏ i ∈ S, (1 : ℝ) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro i hi
      let : Fintype (O ⧸ Ideal.span {p i}) := Fintype.ofFinite _
      exact FiniteRayExpansion.norm_char_le_one _ _
    _ = 1 := by simp

theorem cubeBaseFactor_norm_le_one {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (d h : O) :
    ‖cubeBaseFactor p hp hg B v ε₁ ε₂ d h‖ ≤ 1 := by
  have he : ∀ i ∈ cubeActiveSupport B v ε₁ ε₂,
      (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val ≠ 0 := by
    intro i hi
    exact (ZMod.val_eq_zero _).not.mpr (Finset.mem_filter.mp hi).2
  simp only [cubeBaseFactor, norm_mul, norm_star,
    gaussBlock_norm_one p hp hcop hg hc _ _ he (fun _ _ => ZMod.val_lt _), one_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (blockRow_norm_le_one p hg _ _ _)).trans (blockRow_norm_le_one p hg _ _ _)

end
