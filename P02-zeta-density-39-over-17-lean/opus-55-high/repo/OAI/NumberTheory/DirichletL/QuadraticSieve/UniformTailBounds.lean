module
public import OAI.NumberTheory.DirichletL.QuadraticSieve.ProductColumns
import WeylPort.Analytic.RealLaplace

public section

namespace OAI


open MulChar
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic
open ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Ideal NumberField
open Filter Asymptotics Ideal NumberField
open scoped ContDiff FourierTransform SchwartzMap
open scoped Classical
open scoped Classical SchwartzMap ContDiff
open MeasureTheory Set
open ActualEisensteinCubic

namespace CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum

end CanonicalQuadraticSieve

open scoped Classical SchwartzMap
namespace SecondPassArithmetic
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open FirstPassCubeLabels (columnLog primeProductNorm)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)
open JointLogSeparation (frequencyTwist frequencyTwist_apply)

theorem full_uniform_secondPairRadialMode_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2),
    ∀ (S T : Finset ι) (e : O), e ≠ 0 → ∀ (W : 𝓢(ℝ, ℂ)) (Y H : ℝ),
      0 < Y → 0 ≤ H →
      let n := ∏ i : activeSupport T S, p i.val
      let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
      (∑' k : {k : O // H ≤ scale * ‖eisEmbedding k‖^2},
        ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖) ≤
      (Y / ‖eisEmbedding n‖) *
        ((C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 scale)^2 * (1+H)^A)) := by
  pm_3085 s C hC hbound EisensteinSchwartzPoisson.paperRadialFourier_lattice_tail A
  intro ι _ p hp _ hg hinj hc
    S T e he W Y H hY hH
  dsimp only
  pm_3028
  pm_3046
  pm_8880 hnorm hn
  have hscale : 0 < scale := div_pos hY
    (mul_pos (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero he))) (sq_pos_of_pos hnorm))
  pm_6623 tailSet
  let c := Y / ‖eisEmbedding n‖
  have hc0 : 0 ≤ c := (div_pos hY hnorm).le
  have hpnt (k : tailSet) : ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖ ≤
      c * ‖EisensteinSchwartzPoisson.paperRadialFourier W (scale * ‖eisEmbedding k.val‖^2)‖ := by
    pm_3029 k.val
    change ‖(Y : ℂ) / (‖eisEmbedding n‖ : ℂ)‖ * _ * _ ≤ _
    rw [ha, norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hY, abs_of_pos hnorm]
    pm_7122 k.val
  have hmajor : Summable (fun k : tailSet =>
      c * ‖EisensteinSchwartzPoisson.paperRadialFourier W (scale * ‖eisEmbedding k.val‖^2)‖) :=
    ((EisensteinSchwartzPoisson.paperRadialFourier_lattice_summable_norm W scale hscale).subtype tailSet).mul_left c
  have hsmall : Summable (fun k : tailSet => ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpnt hmajor
  calc
    _ ≤ ∑' k : tailSet, c * ‖EisensteinSchwartzPoisson.paperRadialFourier W
          (scale * ‖eisEmbedding k.val‖^2)‖ := hsmall.tsum_le_tsum hpnt hmajor
    _ = c * ∑' k : tailSet, ‖EisensteinSchwartzPoisson.paperRadialFourier W
          (scale * ‖eisEmbedding k.val‖^2)‖ := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (hbound W scale H hscale hH) hc0

section
variable (A : ℕ)
include A
theorem full_uniform_secondPairRadialMode_remainder :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2),
    ∀ (S T : Finset ι) (e : O), e ≠ 0 → ∀ (W : 𝓢(ℝ, ℂ)) (Y H : ℝ),
      0 < Y → 0 ≤ H → ∀ K : Finset O,
      let n := ∏ i : activeSupport T S, p i.val
      let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
      (∀ k : O, k ∉ K → H ≤ scale * ‖eisEmbedding k‖^2) →
      ‖∑' k : {k : O // k ∉ K}, secondPairRadialMode p hp hg hinj S T e k.val W Y‖ ≤
        (Y/‖eisEmbedding n‖) *
          ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/((min 1 scale)^2*(1+H)^A)) := by
  pm_3008 s C hC hb full_uniform_secondPairRadialMode_tail A
  pm_3001
  intro S T e he W Y H hY hH K
  dsimp only
  intro hK
  pm_3028
  let small : Set O := {k | k ∉ K}
  pm_6623 large
  let f : small → large := fun k => ⟨k.val,hK k.val k.property⟩
  have hi : Function.Injective f := by
    intro a b heq
    exact Subtype.ext (congrArg (fun z : large => z.val) heq)
  have hs := secondPairRadialMode_summable_norm p hp hg hinj hc S T e he W Y hY
  calc
    _ ≤ ∑' k : small, ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖ :=
      norm_tsum_le_tsum_norm (hs.subtype small)
    _ ≤ ∑' k : large, ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖ :=
      (hs.subtype small).tsum_le_tsum_of_inj f hi (fun _ _ => norm_nonneg _) (fun _ => le_rfl)
        (hs.subtype large)
    _ ≤ _ := hb S T e he W Y H hY hH

theorem full_uniform_residualSecondMode_tail_bound :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2),
    ∀ (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O) (H₁ H₂ : Finset ι → ℂ)
      (e : O), e ≠ 0 → ∀ (W : 𝓢(ℝ, ℂ)) (Y H : ℝ), 0 < Y → 0 ≤ H → ∀ K : Finset O,
      (∀ S ∈ (F\G).powerset, ∀ T ∈ (F\G).powerset, Disjoint S T →
        residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T ≠ 0 →
        ∀ k : O, k ∉ K →
          H ≤ (Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2)) *
            ‖eisEmbedding k‖^2) →
      ‖∑' k : {k : O // k ∉ K}, residualSecondMode p hp hg hinj F G Ψ₁ Ψ₂ m c d H₁ H₂ e k.val W Y‖ ≤
      residualTailCost p hg F G Ψ₁ Ψ₂ m c d H₁ H₂ e Y H A (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) := by
  pm_3008 s C hC hb full_uniform_secondPairRadialMode_remainder A
  pm_3001
  intro F G Ψ₁ Ψ₂ m c d H₁ H₂ e he W Y H hY hH K hK
  rw [residualSecondMode_tail_eq p hp hg hinj F G Ψ₁ Ψ₂ m c d H₁ H₂ e he W Y hY K]
  unfold residualTailCost
  pm_3719 S hS
  pm_3719 T hT
  by_cases hd : Disjoint S T
  · simp only [ite_eq_left hd, norm_mul]
    by_cases hw : residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T = 0
    pm_2997 hw norm_zero zero_mul le_refl
    · exact mul_le_mul_of_nonneg_left (hb S T e he W Y H hY hH K (hK S hS T hT hd hw)) (norm_nonneg _)
  · simp [hd]

theorem full_uniform_secondSourceTail_bound :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2),
    ∀ (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (Hcol : Finset ι → ℂ)
      (W : 𝓢(ℝ, ℂ)) (Y H : ℝ), 0 < Y → 0 ≤ H →
      ∀ K : Finset ι → Finset ι → Finset O,
      (∀ G ∈ F.powerset, ∀ E : G.powerset,
        ∀ S ∈ (F\G).powerset, ∀ T ∈ (F\G).powerset, Disjoint S T →
        residualPairWeight p hg Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U)) S T ≠ 0 →
        ∀ k : O, k ∉ K G E.val →
          H ≤ (Y / (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val)‖^2 *
            ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2)) * ‖eisEmbedding k‖^2) →
      ‖secondSourceTail p hp hg hinj F Ψ m c d Hcol W Y K‖ ≤
      ∑ G ∈ F.powerset, ∑ E : G.powerset, ‖secondSourceCommonCoefficient p hg Ψ m c d G E.val‖ *
        residualTailCost p hg F G Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U))
          (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) Y H A
          (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) := by
  pm_3008 s C hC hb full_uniform_residualSecondMode_tail_bound A
  pm_3001
  intro F Ψ m c d Hcol W Y H hY hH K hK
  unfold secondSourceTail
  pm_3719 G hG
  pm_3719 E hE
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simp_rw [← residualSecondMode_eq_frequencyKernel p hp hg hinj F G E.val
    (Finset.mem_powerset.mp E.property) Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U))]
  exact hb F G Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U))
    (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) (primeSubsetGenerator_ne_zero _ _)
    W Y H hY hH (K G E.val) (hK G hG E)
end

end SecondPassArithmetic

namespace InitialMeanSquare
open IdealMobiusDivisorSum

end InitialMeanSquare

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open EisensteinSchwartzPoisson (paperRadialFourier)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

end

end SecondPassArithmetic


end OAI
