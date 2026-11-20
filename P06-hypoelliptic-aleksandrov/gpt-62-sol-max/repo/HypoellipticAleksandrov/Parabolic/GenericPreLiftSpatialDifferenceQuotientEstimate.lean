module

public import HypoellipticAleksandrov.Parabolic.GenericPreLiftDifferentiatedWeakEquation
public import HypoellipticAleksandrov.Parabolic.ProperCommutatorSquaredAggregation
public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyL2Norm
public import HypoellipticAleksandrov.Parabolic.GenericPreLiftSpatialDifferenceQuotientFixedCore
public import HypoellipticAleksandrov.Analysis.BoundedMultiplierLp
public import HypoellipticAleksandrov.Analysis.FiniteSumL2Norm

/-!
# Generic pre-lift spatial difference-quotient estimate

This module assembles the differentiated pre-lift equation into the fixed
divergence-form difference-quotient estimate.  The private residual API below
keeps the literal proper commutator, coefficient-gradient, drift-gradient,
and zeroth-order terms in one finite `L²` sum.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set
open HypoellipticAleksandrov.Analysis
open scoped BigOperators ENNReal MatrixOrder

/-- Quantitative coefficient regularity used in a single pre-lift step. -/
structure PreliftCoefficientBounds {d M : ℕ} (U : Set (TimeVelocity d)) (lam Lam : ℝ)
    (Ba : Fin d → Fin d → ParabolicDerivativeIndex d (M + 1) → ℝ)
    (Bb : Fin d → ParabolicDerivativeIndex d M → ℝ)
    (Bc : ParabolicDerivativeIndex d M → ℝ)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ) : Prop where
  elliptic : ∀ z ∈ U, lam • (1 : PDE.Mat d) ≤ a z.1 z.2 ∧ a z.1 z.2 ≤ Lam • (1 : PDE.Mat d)
  diffusion_smooth : ∀ i j, ContDiffOn ℝ (M + 1) (fun z => a z.1 z.2 i j) U
  drift_smooth : ∀ j, ContDiffOn ℝ M (fun z => b z.1 z.2 j) U
  potential_smooth : ContDiffOn ℝ M (fun z => c z.1 z.2) U
  diffusion_bound : ∀ i j α z, z ∈ U →
    |TimeVelocityMultiIndex.coordinateIteratedFDeriv α.1 (fun x => a x.1 x.2 i j) z| ≤ Ba i j α
  drift_bound : ∀ j α z, z ∈ U →
    |TimeVelocityMultiIndex.coordinateIteratedFDeriv α.1 (fun x => b x.1 x.2 j) z| ≤ Bb j α
  potential_bound : ∀ α z, z ∈ U →
    |TimeVelocityMultiIndex.coordinateIteratedFDeriv α.1 (fun x => c x.1 x.2) z| ≤ Bc α

/-- Restrict the coefficient control to a smaller set and a lower derivative order. -/
theorem PreliftCoefficientBounds.restrict {d m n : ℕ} {U V : Set (TimeVelocity d)} {lam Lam : ℝ}
    {Ba : Fin d → Fin d → ParabolicDerivativeIndex d (n + 1) → ℝ}
    {Bb : Fin d → ParabolicDerivativeIndex d n → ℝ} {Bc : ParabolicDerivativeIndex d n → ℝ}
    {a : CoefficientField d} {b : ℝ → PDE.Vec d → PDE.Vec d} {c : ℝ → PDE.Vec d → ℝ}
    (h : PreliftCoefficientBounds U lam Lam Ba Bb Bc a b c) (hVU : V ⊆ U) (hm : m ≤ n) :
    PreliftCoefficientBounds V lam Lam
      (fun i j α => Ba i j (ParabolicDerivativeIndex.castLE (Nat.succ_le_succ hm) α))
      (fun j α => Bb j (ParabolicDerivativeIndex.castLE hm α))
      (fun α => Bc (ParabolicDerivativeIndex.castLE hm α)) a b c := by
  refine ⟨fun z hz => h.elliptic z (hVU hz), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i j => ((h.diffusion_smooth i j).of_le (by exact_mod_cast Nat.succ_le_succ hm)).mono hVU
  · exact fun j => ((h.drift_smooth j).of_le (by exact_mod_cast hm)).mono hVU
  · exact (h.potential_smooth.of_le (by exact_mod_cast hm)).mono hVU
  · exact fun i j α z hz => h.diffusion_bound i j (ParabolicDerivativeIndex.castLE (Nat.succ_le_succ hm) α) z (hVU hz)
  · exact fun j α z hz => h.drift_bound j (ParabolicDerivativeIndex.castLE hm α) z (hVU hz)
  · exact fun α z hz => h.potential_bound (ParabolicDerivativeIndex.castLE hm α) z (hVU hz)

section
variable {d M : ℕ}

private def preliftDiffusionDerivative (hM : 1 ≤ M)
    (a : CoefficientField d) (k i j : Fin d) (z : TimeVelocity d) : ℝ :=
  TimeVelocityMultiIndex.coordinateIteratedFDeriv (singletonCoefficientIndex hM k).1
    (fun x : TimeVelocity d => a x.1 x.2 i j) z

private def diffusionGradientMajorant (hM : 1 ≤ M)
    (Ba : Fin d → Fin d → ParabolicDerivativeIndex d (M + 1) → ℝ) : ℝ :=
  ∑ k, ∑ i, ∑ j, Ba i j (singletonCoefficientIndex hM k)

private def driftValueMajorant (Bb : Fin d → ParabolicDerivativeIndex d M → ℝ) : ℝ :=
  ∑ j, Bb j (ParabolicDerivativeIndex.zero d M)

private def potentialValueMajorant (Bc : ParabolicDerivativeIndex d M → ℝ) : ℝ :=
  Bc (ParabolicDerivativeIndex.zero d M)

end

section
variable {d M : ℕ}

private theorem diffusionGradientMajorant_nonneg (hM : 1 ≤ M)
    (Ba : Fin d → Fin d → ParabolicDerivativeIndex d (M + 1) → ℝ)
    (hBa : ∀ i j alpha, 0 ≤ Ba i j alpha) :
    0 ≤ diffusionGradientMajorant hM Ba := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun k _ => hBa j k (singletonCoefficientIndex hM i)

private theorem driftValueMajorant_nonneg (Bb : Fin d → ParabolicDerivativeIndex d M → ℝ)
    (hBb : ∀ j alpha, 0 ≤ Bb j alpha) :
    0 ≤ driftValueMajorant Bb := Finset.sum_nonneg fun j _ => hBb j (ParabolicDerivativeIndex.zero d M)

private theorem potentialValueMajorant_nonneg (Bc : ParabolicDerivativeIndex d M → ℝ)
    (hBc : ∀ alpha, 0 ≤ Bc alpha) :
    0 ≤ potentialValueMajorant Bc :=
  hBc (ParabolicDerivativeIndex.zero d M)

section
variable {U : Set (TimeVelocity d)}

private theorem diffusionGradient_abs_le_majorant (hM : 1 ≤ M)
    (a : CoefficientField d)
    (Ba : Fin d → Fin d → ParabolicDerivativeIndex d (M + 1) → ℝ)
    (hBa : ∀ i j alpha, 0 ≤ Ba i j alpha)
    (haBound : ∀ i j alpha z, z ∈ U →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d => a x.1 x.2 i j) z| ≤ Ba i j alpha) :
    ∀ i j k z, z ∈ U →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (singletonCoefficientIndex hM k).1
        (fun x : TimeVelocity d => a x.1 x.2 i j) z| ≤
        diffusionGradientMajorant hM Ba := by
  intro i j k z hz
  have hij : Ba i j (singletonCoefficientIndex hM k) ≤
      ∑ l, Ba i l (singletonCoefficientIndex hM k) :=
    Finset.single_le_sum (fun l _ => hBa i l _) (Finset.mem_univ j)
  have hi : (∑ l, Ba i l (singletonCoefficientIndex hM k)) ≤
      ∑ r, ∑ l, Ba r l (singletonCoefficientIndex hM k) := by
    exact Finset.single_le_sum
      (fun r _ => Finset.sum_nonneg fun l _ => hBa r l _) (Finset.mem_univ i)
  have hk : (∑ r, ∑ l, Ba r l (singletonCoefficientIndex hM k)) ≤
      diffusionGradientMajorant hM Ba := by
    unfold diffusionGradientMajorant
    exact Finset.single_le_sum
      (fun s _ => Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun l _ =>
        hBa r l (singletonCoefficientIndex hM s)) (Finset.mem_univ k)
  exact (haBound i j (singletonCoefficientIndex hM k) z hz).trans
    (hij.trans (hi.trans hk))

private theorem spatialPartial_coefficient_eq_singletonDerivative (hU : IsOpen U) (hM : 1 ≤ M)
    (a : CoefficientField d)
    (ha : ∀ i j, ContDiffOn ℝ (M + 1)
      (fun z : TimeVelocity d => a z.1 z.2 i j) U) :
    ∀ k i j z, z ∈ U →
      spatialPartial k (fun y => a z.1 y i j) z.2 =
        TimeVelocityMultiIndex.coordinateIteratedFDeriv
          (singletonCoefficientIndex hM k).1
          (fun x : TimeVelocity d => a x.1 x.2 i j) z := by
  intro k i j z hz
  rw [singletonCoefficientIndex_coe,
    TimeVelocityMultiIndex.coordinateIteratedFDeriv_single_at (velocityCoord k)
      (((ha i j).contDiffAt (hU.mem_nhds hz)).of_le (by simp))]
  unfold spatialPartial
  have hdiff := ((ha i j).contDiffAt (hU.mem_nhds hz)).differentiableAt
    (by norm_num)
  have hslice : HasFDerivAt (fun y : PDE.Vec d => a z.1 y i j)
      ((fderiv ℝ (fun x : TimeVelocity d => a x.1 x.2 i j) z).comp
        (ContinuousLinearMap.inr ℝ ℝ (PDE.Vec d))) z.2 := by
    simpa only [Function.comp_def] using! hdiff.hasFDerivAt.comp z.2
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2)
  rw [hslice.fderiv]
  rfl

end

end

section
variable {d M : ℕ} {U : Set (TimeVelocity d)}

private theorem spatialPartial_coefficient_abs_le_majorant (hU : IsOpen U) (hM : 1 ≤ M)
    (a : CoefficientField d)
    (Ba : Fin d → Fin d → ParabolicDerivativeIndex d (M + 1) → ℝ)
    (hBa : ∀ i j alpha, 0 ≤ Ba i j alpha)
    (ha : ∀ i j, ContDiffOn ℝ (M + 1)
      (fun z : TimeVelocity d => a z.1 z.2 i j) U)
    (haBound : ∀ i j alpha z, z ∈ U →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d => a x.1 x.2 i j) z| ≤ Ba i j alpha) :
    ∀ i j k z, z ∈ U →
      |spatialPartial k (fun y => a z.1 y i j) z.2| ≤
        diffusionGradientMajorant hM Ba := by
  intro i j k z hz
  rw [spatialPartial_coefficient_eq_singletonDerivative hU hM a ha k i j z hz]
  exact diffusionGradient_abs_le_majorant hM a Ba hBa haBound i j k z hz

private theorem driftValue_abs_le_majorant
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (Bb : Fin d → ParabolicDerivativeIndex d M → ℝ)
    (hBb : ∀ j alpha, 0 ≤ Bb j alpha)
    (hbBound : ∀ j alpha z, z ∈ U →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d => b x.1 x.2 j) z| ≤ Bb j alpha) :
    ∀ j z, z ∈ U → |b z.1 z.2 j| ≤ driftValueMajorant Bb := by
  intro j z hz
  have hj : Bb j (ParabolicDerivativeIndex.zero d M) ≤
      driftValueMajorant Bb := by
    exact Finset.single_le_sum
      (fun k _ => hBb k (ParabolicDerivativeIndex.zero d M))
      (Finset.mem_univ j)
  have hv : |b z.1 z.2 j| ≤ Bb j (ParabolicDerivativeIndex.zero d M) := by
    simpa using hbBound j (ParabolicDerivativeIndex.zero d M) z hz
  exact hv.trans hj

private theorem potentialValue_abs_le_majorant
    (c : ℝ → PDE.Vec d → ℝ)
    (Bc : ParabolicDerivativeIndex d M → ℝ)
    (hcBound : ∀ alpha z, z ∈ U →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d => c x.1 x.2) z| ≤ Bc alpha) :
    ∀ z, z ∈ U → |c z.1 z.2| ≤ potentialValueMajorant Bc := by
  intro z hz
  simpa [potentialValueMajorant] using
    hcBound (ParabolicDerivativeIndex.zero d M) z hz

private theorem singletonCoefficientDerivative_continuousOn (hU : IsOpen U) (hM : 1 ≤ M)
    (q : TimeVelocity d → ℝ) (hq : ContDiffOn ℝ (M + 1) q U)
    (i : Fin d) :
    ContinuousOn (TimeVelocityMultiIndex.coordinateIteratedFDeriv
      (singletonCoefficientIndex hM i).1 q) U := by
  rw [singletonCoefficientIndex_coe]
  exact (TimeVelocityMultiIndex.coordinateIteratedFDeriv_contDiffOn (Pi.single (velocityCoord i) 1)
    (m := 0) hU hq (by simp)).continuousOn

end

section
variable {d M : ℕ} {U : Set (TimeVelocity d)} (hU : IsOpen U)
include hU

private theorem diffusionGradient_aestronglyMeasurable (hM : 1 ≤ M)
    (a : CoefficientField d)
    (ha : ∀ i j, ContDiffOn ℝ (M + 1)
      (fun z : TimeVelocity d => a z.1 z.2 i j) U) (i j : Fin d) :
    AEStronglyMeasurable
      (TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (singletonCoefficientIndex hM i).1
        (fun z : TimeVelocity d => a z.1 z.2 i j))
      (timeVelocityVolumeOn U) := by
  exact (singletonCoefficientDerivative_continuousOn hU hM _ (ha i j) i)
    |>.aestronglyMeasurable hU.measurableSet

private theorem driftValue_aestronglyMeasurable
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (hb : ∀ j, ContDiffOn ℝ M
      (fun z : TimeVelocity d => b z.1 z.2 j) U) (j : Fin d) :
    AEStronglyMeasurable (fun z : TimeVelocity d => b z.1 z.2 j)
      (timeVelocityVolumeOn U) :=
  (hb j).continuousOn.aestronglyMeasurable hU.measurableSet

end

section
variable {d M : ℕ} (Ba : Fin d → Fin d → ParabolicDerivativeIndex d M → ℝ)
  (Bb : Fin d → ParabolicDerivativeIndex d M → ℝ) (Bc : ParabolicDerivativeIndex d M → ℝ)
include d M Ba Bb Bc

private noncomputable def properResidualCoarseConstant : ℝ :=
  ∑ beta : ParabolicDerivativeIndex d M,
    ((1 + (d ^ 2 + d + 1) * properSplitCard beta : ℕ) : ℝ) *
      (1 +
        (∑ i, ∑ j, ∑ gamma :
            {gamma : TimeVelocityMultiIndex.Split beta.1 // gamma.left ≠ 0},
          ((beta.1.choose gamma.1.left : ℝ) *
            Ba i j (ParabolicDerivativeIndex.splitLeft beta gamma.1)) ^ 2) +
        (∑ j, ∑ gamma :
            {gamma : TimeVelocityMultiIndex.Split beta.1 // gamma.left ≠ 0},
          ((beta.1.choose gamma.1.left : ℝ) *
            Bb j (ParabolicDerivativeIndex.splitLeft beta gamma.1)) ^ 2) +
        (∑ gamma :
            {gamma : TimeVelocityMultiIndex.Split beta.1 // gamma.left ≠ 0},
          ((beta.1.choose gamma.1.left : ℝ) *
            Bc (ParabolicDerivativeIndex.splitLeft beta gamma.1)) ^ 2))

private theorem properResidualCoarseConstant_nonneg :
    0 ≤ properResidualCoarseConstant Ba Bb Bc := Finset.sum_nonneg fun beta _ => mul_nonneg (by positivity) (by positivity)

end

section
variable {d M : ℕ}

private theorem properResidual_memLp_and_sum_sq_le_coarse (U : Set (TimeVelocity d)) (hU : IsOpen U)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ) (u : TimeVelocity d → ℝ)
    (F : ℝ → PDE.Vec d → ℝ)
    (D : ParabolicWeakDerivativeFamily d (M + 1) U u)
    (E : ParabolicWeakDerivativeFamily d M U
      (fun z : TimeVelocity d => F z.1 z.2))
    (Ba : Fin d → Fin d → ParabolicDerivativeIndex d M → ℝ)
    (Bb : Fin d → ParabolicDerivativeIndex d M → ℝ)
    (Bc : ParabolicDerivativeIndex d M → ℝ)
    (hBa : ∀ i j alpha, 0 ≤ Ba i j alpha)
    (hBb : ∀ j alpha, 0 ≤ Bb j alpha)
    (hBc : ∀ alpha, 0 ≤ Bc alpha)
    (ha : ∀ i j, ContDiffOn ℝ M (fun z : TimeVelocity d => a z.1 z.2 i j) U)
    (hb : ∀ j, ContDiffOn ℝ M (fun z : TimeVelocity d => b z.1 z.2 j) U)
    (hc : ContDiffOn ℝ M (fun z : TimeVelocity d => c z.1 z.2) U)
    (haBound : ∀ i j alpha z, z ∈ U →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d => a x.1 x.2 i j) z| ≤ Ba i j alpha)
    (hbBound : ∀ j alpha z, z ∈ U →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d => b x.1 x.2 j) z| ≤ Bb j alpha)
    (hcBound : ∀ alpha z, z ∈ U →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d => c x.1 x.2) z| ≤ Bc alpha) :
    (∀ beta : ParabolicDerivativeIndex d M, ParabolicMemLpOn U 2
      (properDifferentiatedScalarCommutatorResidual a b c D E beta)) ∧
    (∑ beta : ParabolicDerivativeIndex d M,
      squaredL2Seminorm (timeVelocityVolumeOn U) (properDifferentiatedScalarCommutatorResidual a b c D E beta)) ≤
      properResidualCoarseConstant Ba Bb Bc *
        (ParabolicWeakDerivativeFamily.squaredL2Norm D +
          ParabolicWeakDerivativeFamily.squaredL2Norm E) := by
  classical
  obtain ⟨hmem, hsum⟩ :=
    properDifferentiatedScalarCommutatorResidual_memLp_and_sum_sq_le
      U hU a b c u F D E Ba Bb Bc hBa hBb hBc ha hb hc
        haBound hbBound hcBound
  refine ⟨hmem, hsum.trans ?_⟩
  unfold properResidualCoarseConstant
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro beta hbeta
  have hD := ParabolicWeakDerivativeFamily.squaredL2Norm_nonneg D
  have hE := ParabolicWeakDerivativeFamily.squaredL2Norm_nonneg E
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simp only [add_mul, one_mul]
  simp_rw [Finset.sum_mul]
  gcongr <;> first
  | exact (ParabolicWeakDerivativeFamily.component_sq_le_squaredL2Norm E beta).trans
      (le_add_of_nonneg_left hD)
  | rw [mul_pow]
    exact mul_le_mul_of_nonneg_left
      ((ParabolicWeakDerivativeFamily.component_sq_le_squaredL2Norm D _).trans
        (le_add_of_nonneg_right hE)) (sq_nonneg _)

private def preliftValueIndex
    (beta : ParabolicDerivativeIndex d M) : ParabolicDerivativeIndex d (M + 1) :=
  ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta

private def preliftGradientIndex
    (beta : ParabolicDerivativeIndex d M) (j : Fin d) :
    ParabolicDerivativeIndex d (M + 1) :=
  ParabolicDerivativeIndex.velocitySucc (preliftValueIndex beta) j (by
    change beta.1.parabolicWeight + 1 ≤ M + 1
    omega)

end

private theorem component_sum_sq_le_card
    {ι : Type*} [Fintype ι] {d M : ℕ} {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d M U u) (f : ι → ParabolicDerivativeIndex d M) :
    (∑ i, squaredL2Seminorm (timeVelocityVolumeOn U) (D.representative (f i))) ≤
      (Fintype.card ι : ℝ) * D.squaredL2Norm := by
  simpa only [Finset.card_univ, nsmul_eq_mul] using
    Finset.sum_le_card_nsmul Finset.univ _ D.squaredL2Norm
      (fun i _ => ParabolicWeakDerivativeFamily.component_sq_le_squaredL2Norm D (f i))

private def genericPreliftFullResidual
    {d : ℕ} (Rproper : TimeVelocity d → ℝ)
    (da : Fin d → Fin d → TimeVelocity d → ℝ)
    (b : Fin d → TimeVelocity d → ℝ) (c q : TimeVelocity d → ℝ)
    (G : Fin d → TimeVelocity d → ℝ) (z : TimeVelocity d) : ℝ :=
  Rproper z + (∑ i, ∑ j, da i j z * G j z) -
    (∑ j, b j z * G j z) - c z * q z

private theorem genericPreliftFullResidual_memLp_and_sq_le
    {d : ℕ} {U : Set (TimeVelocity d)}
    (Rproper : TimeVelocity d → ℝ)
    (da : Fin d → Fin d → TimeVelocity d → ℝ)
    (b : Fin d → TimeVelocity d → ℝ) (c q : TimeVelocity d → ℝ)
    (G : Fin d → TimeVelocity d → ℝ)
    (hR : ParabolicMemLpOn U 2 Rproper)
    (Ada Ab Ac : ℝ)
    (hda : ∀ i j, ParabolicMemLpOn U 2 (fun z => da i j z * G j z) ∧
      squaredL2Seminorm (timeVelocityVolumeOn U) (fun z => da i j z * G j z) ≤
        Ada ^ 2 * squaredL2Seminorm (timeVelocityVolumeOn U) (G j))
    (hb : ∀ j, ParabolicMemLpOn U 2 (fun z => b j z * G j z) ∧
      squaredL2Seminorm (timeVelocityVolumeOn U) (fun z => b j z * G j z) ≤
        Ab ^ 2 * squaredL2Seminorm (timeVelocityVolumeOn U) (G j))
    (hc : ParabolicMemLpOn U 2 (fun z => c z * q z) ∧
      squaredL2Seminorm (timeVelocityVolumeOn U) (fun z => c z * q z) ≤
        Ac ^ 2 * squaredL2Seminorm (timeVelocityVolumeOn U) q) :
    ParabolicMemLpOn U 2
        (genericPreliftFullResidual Rproper da b c q G) ∧
      squaredL2Seminorm (timeVelocityVolumeOn U) (genericPreliftFullResidual Rproper da b c q G) ≤
        ((d : ℝ) ^ 2 + (d : ℝ) + 2) *
          (squaredL2Seminorm (timeVelocityVolumeOn U) Rproper +
          Ada ^ 2 * ∑ _i : Fin d, ∑ j : Fin d,
            squaredL2Seminorm (timeVelocityVolumeOn U) (G j) +
          Ab ^ 2 * ∑ j : Fin d,
            squaredL2Seminorm (timeVelocityVolumeOn U) (G j) +
          Ac ^ 2 * squaredL2Seminorm (timeVelocityVolumeOn U) q) := by
  let μ := timeVelocityVolumeOn U
  obtain ⟨hm, hs⟩ := memLp_and_squaredL2Seminorm_add_terms (μ := μ) Rproper
    (fun i j z => da i j z * G j z) (fun j => -(fun z => b j z * G j z)) (-(fun z => c z * q z))
    hR (fun i j => (hda i j).1) (fun j => (hb j).1.neg) hc.1.neg
  simp only [Pi.neg_apply, Finset.sum_neg_distrib, ← sub_eq_add_neg] at hm hs
  refine ⟨hm, hs.trans ?_⟩
  simp only [Fintype.card_fin, squaredL2Seminorm_neg]
  simp_rw [Finset.mul_sum]
  gcongr
  · exact (hda _ _).2
  · exact (hb _).2
  · exact hc.2

section
variable {d M : ℕ} (hM : 1 ≤ M) (Ba : Fin d → Fin d → ParabolicDerivativeIndex d (M + 1) → ℝ)
  (Bb : Fin d → ParabolicDerivativeIndex d M → ℝ) (Bc : ParabolicDerivativeIndex d M → ℝ)
include d M hM Ba Bb Bc

private noncomputable def fullResidualCoarseConstant : ℝ :=
  ((d : ℝ) ^ 2 + (d : ℝ) + 2) *
    (properResidualCoarseConstant
        (fun i j alpha => Ba i j (ParabolicDerivativeIndex.castLE
          (Nat.le_succ M) alpha)) Bb Bc +
      (Fintype.card (ParabolicDerivativeIndex d M) : ℝ) *
        (diffusionGradientMajorant hM Ba ^ 2 * (d : ℝ) ^ 2 +
          driftValueMajorant Bb ^ 2 * (d : ℝ) +
          potentialValueMajorant Bc ^ 2))

private theorem fullResidualCoarseConstant_nonneg :
    0 ≤ fullResidualCoarseConstant hM Ba Bb Bc := by
  unfold fullResidualCoarseConstant
  have hproper := properResidualCoarseConstant_nonneg
    (fun i j alpha => Ba i j (ParabolicDerivativeIndex.castLE
      (Nat.le_succ M) alpha)) Bb Bc
  positivity

end

private theorem sum_le_coarse_product_of_pointwise_four_term
    {ι : Type*} [Fintype ι]
    (r p doubleG singleG q : ι → ℝ)
    (N Cp K Ada Ab Ac d Dnorm Enorm : ℝ)
    (hN : 0 ≤ N) (hK : 0 ≤ K)
    (hd : 0 ≤ d) (hE : 0 ≤ Enorm)
    (hpoint : ∀ beta,
      r beta ≤ N * (p beta + Ada ^ 2 * doubleG beta +
        Ab ^ 2 * singleG beta + Ac ^ 2 * q beta))
    (hp : (∑ beta, p beta) ≤ Cp * (Dnorm + Enorm))
    (hdoubleG : (∑ beta, doubleG beta) ≤ K * d ^ 2 * Dnorm)
    (hsingleG : (∑ beta, singleG beta) ≤ K * d * Dnorm)
    (hq : (∑ beta, q beta) ≤ K * Dnorm) :
    (∑ beta, r beta) ≤
      N * (Cp + K * (Ada ^ 2 * d ^ 2 + Ab ^ 2 * d + Ac ^ 2)) *
        (Dnorm + Enorm) := by
  have step {g : ι → ℝ} {m : ℝ} (a : ℝ) (hm : 0 ≤ m) (h : (∑ j, g j) ≤ m * Dnorm) :
      (∑ j, a ^ 2 * g j) ≤ (a ^ 2 * m) * (Dnorm + Enorm) := by
    rw [← Finset.mul_sum, mul_assoc]
    gcongr
    exact h.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hE) hm)
  convert sum_le_mul_four_term_bound hN hpoint hp
    (step Ada (by positivity) hdoubleG) (step Ab (by positivity) hsingleG) (step Ac hK hq) using 1
  ring

private def sourceSpecificFullResidual
    {d M : ℕ} (hM : 1 ≤ M)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ) {U : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ} {F : ℝ → PDE.Vec d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) U u)
    (E : ParabolicWeakDerivativeFamily d M U
      (fun z : TimeVelocity d => F z.1 z.2))
    (beta : ParabolicDerivativeIndex d M) : TimeVelocity d → ℝ :=
  genericPreliftFullResidual
    (properDifferentiatedScalarCommutatorResidual a b c D E beta)
    (fun i j => preliftDiffusionDerivative hM a i i j)
    (fun j z => b z.1 z.2 j) (fun z => c z.1 z.2)
    (D.representative (preliftValueIndex beta))
    (fun j => D.representative (preliftGradientIndex beta j))

private theorem integral_genericPreliftFullResidual_mul
    {d : ℕ} {U : Set (TimeVelocity d)} (R q φ : TimeVelocity d → ℝ)
    (da : Fin d → Fin d → TimeVelocity d → ℝ) (b G : Fin d → TimeVelocity d → ℝ)
    (c : TimeVelocity d → ℝ)
    (hφ : ParabolicMemLpOn U 2 φ) (hR : ParabolicMemLpOn U 2 R)
    (hda : ∀ i j, ParabolicMemLpOn U 2 (fun z => da i j z * G j z))
    (hb : ∀ j, ParabolicMemLpOn U 2 (fun z => b j z * G j z))
    (hc : ParabolicMemLpOn U 2 (fun z => c z * q z)) :
    (∫ z in U, genericPreliftFullResidual R da b c q G z * φ z) =
      (∫ z in U, R z * φ z) + (∑ i, ∑ j, ∫ z in U, da i j z * G j z * φ z) -
        (∑ j, ∫ z in U, b j z * G j z * φ z) - ∫ z in U, c z * q z * φ z := by
  let r := fun z => R z * φ z
  let a := fun z => ∑ i, ∑ j, da i j z * G j z * φ z
  let b' := fun z => ∑ j, b j z * G j z * φ z
  let c' := fun z => c z * q z * φ z
  let μ := timeVelocityVolumeOn U
  have hr : Integrable r μ := hR.integrable_mul hφ
  have ha (i j : Fin d) : Integrable (fun z => da i j z * G j z * φ z) μ :=
    (hda i j).integrable_mul hφ
  have hA : Integrable a μ := integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ha i j
  have hb' (j : Fin d) : Integrable (fun z => b j z * G j z * φ z) μ :=
    (hb j).integrable_mul hφ
  have hB : Integrable b' μ := integrable_finsetSum _ fun j _ => hb' j
  have hC : Integrable c' μ := hc.integrable_mul hφ
  calc
    _ = ∫ z, (r + a - b' - c') z ∂μ := by
      exact integral_congr_ae (ae_of_all _ fun z => by
        simp only [genericPreliftFullResidual, r, a, b', c', Pi.add_apply, Pi.sub_apply,
          add_mul, sub_mul, Finset.sum_mul])
    _ = _ := by
      rw [integral_sub' ((hr.add hA).sub hB) hC, integral_sub' (hr.add hA) hB, integral_add' hr hA]
      dsimp only [a, b']
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => ha i j),
        integral_finsetSum _ (fun j _ => hb' j)]
      simp_rw [integral_finsetSum Finset.univ (fun j _ => ha _ j)]
      rfl

private theorem sourceSpecific_testedEquation
    {d M : ℕ} (hM : 1 ≤ M) (U : Set (TimeVelocity d)) (hU : IsOpen U)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ) (u : TimeVelocity d → ℝ)
    (D : ParabolicWeakDerivativeFamily d (M + 1) U u)
    (E : ParabolicWeakDerivativeFamily d M U
      (fun z : TimeVelocity d => F z.1 z.2))
    (ha : ∀ i j, ContDiffOn ℝ (M + 1)
      (fun z : TimeVelocity d => a z.1 z.2 i j) U)
    (hb : ∀ j, ContDiffOn ℝ M (fun z : TimeVelocity d => b z.1 z.2 j) U)
    (hc : ContDiffOn ℝ M (fun z : TimeVelocity d => c z.1 z.2) U)
    (hEq :
      D.backwardOperator (by omega) a b c =ᵐ[timeVelocityVolumeOn U]
        (fun z => F z.1 z.2))
    (beta : ParabolicDerivativeIndex d M)
    (hproper : ParabolicMemLpOn U 2
      (properDifferentiatedScalarCommutatorResidual a b c D E beta))
    (hda : ∀ i j, ParabolicMemLpOn U 2 (fun z =>
      preliftDiffusionDerivative hM a i i j z * D.representative (preliftGradientIndex beta j) z))
    (hB : ∀ j, ParabolicMemLpOn U 2 (fun z => b z.1 z.2 j * D.representative (preliftGradientIndex beta j) z))
    (hC : ParabolicMemLpOn U 2 (fun z => c z.1 z.2 * D.representative (preliftValueIndex beta) z)) :
    ∀ φ : TimeVelocity d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ U →
      -(∫ z in U, D.representative (preliftValueIndex beta) z *
          timeDerivative φ z) -
        (∑ i, ∑ j, ∫ z in U, a z.1 z.2 i j *
          D.representative (preliftGradientIndex beta j) z *
          velocityGradient φ z i) =
        ∫ z in U, sourceSpecificFullResidual hM a b c D E beta z * φ z := by
  intro φ hφ hφc hφU
  have hraw := integral_genericPreliftDifferentiatedScalarEquation hM U hU
    a b c F u D E ha hb hc hEq beta φ hφ hφc hφU
  have hφLp : ParabolicMemLpOn U 2 φ := (hφ.continuous.memLp_of_hasCompactSupport hφc).restrict U
  unfold sourceSpecificFullResidual
  rw [integral_genericPreliftFullResidual_mul _ _ _ _ _ _ _ hφLp hproper hda hB hC]
  simp only [preliftValueIndex, preliftGradientIndex, preliftDiffusionDerivative, singletonCoefficientIndex_coe] at ⊢
  linear_combination hraw

/-- Uniform interior spatial-difference-quotient control of every selected
gradient in the generic tested pre-lift equation. -/
theorem exists_genericPrelift_gradient_spatialDifferenceQuotient_estimate
    (d M : ℕ) (hM : 1 ≤ M)
    (t₀ t₁ t₂ t₃ : ℝ)
    (ht₀₁ : t₀ < t₁) (ht₁₂ : t₁ < t₂) (ht₂₃ : t₂ < t₃)
    (O₀ O₁ : Set (PDE.Vec d))
    (hO₀ : IsOpen O₀) (hO₁ : IsOpen O₁)
    (hO₁compact : IsCompact (closure O₁))
    (hO₁O₀ : closure O₁ ⊆ O₀)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (Ba : Fin d → Fin d → ParabolicDerivativeIndex d (M + 1) → ℝ)
    (Bb : Fin d → ParabolicDerivativeIndex d M → ℝ)
    (Bc : ParabolicDerivativeIndex d M → ℝ)
    (hBa : ∀ i j alpha, 0 ≤ Ba i j alpha)
    (hBb : ∀ j alpha, 0 ≤ Bb j alpha)
    (hBc : ∀ alpha, 0 ≤ Bc alpha) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ (a : CoefficientField d)
        (b : ℝ → PDE.Vec d → PDE.Vec d)
        (c F : ℝ → PDE.Vec d → ℝ)
        (u : TimeVelocity d → ℝ)
        (D : ParabolicWeakDerivativeFamily d (M + 1)
          (Set.Ioo t₀ t₃ ×ˢ O₀) u)
        (E : ParabolicWeakDerivativeFamily d M
          (Set.Ioo t₀ t₃ ×ˢ O₀)
          (fun z : TimeVelocity d => F z.1 z.2)),
        PreliftCoefficientBounds (Ioo t₀ t₃ ×ˢ O₀) lam Lam Ba Bb Bc a b c →
        (D.backwardOperator (by omega) a b c
          =ᵐ[timeVelocityVolumeOn (Set.Ioo t₀ t₃ ×ˢ O₀)]
            fun z => F z.1 z.2) →
        ∀ h : ℝ, 0 < h → h < δ →
          (∀ (beta : ParabolicDerivativeIndex d M) (j i : Fin d),
            ParabolicMemLpOn (Set.Ioo t₁ t₂ ×ˢ O₁) 2
              (spatialDifferenceQuotient i h
                (D.representative
                  (ParabolicDerivativeIndex.velocitySucc
                    (ParabolicDerivativeIndex.castLE
                      (Nat.le_succ M) beta) j
                    (by
                      change beta.1.parabolicWeight + 1 ≤ M + 1
                      omega))))) ∧
          (∑ beta : ParabolicDerivativeIndex d M,
            ∑ j : Fin d, ∑ i : Fin d,
              (ENNReal.toReal (eLpNorm
                (spatialDifferenceQuotient i h
                  (D.representative
                    (ParabolicDerivativeIndex.velocitySucc
                      (ParabolicDerivativeIndex.castLE
                        (Nat.le_succ M) beta) j
                      (by
                        change beta.1.parabolicWeight + 1 ≤ M + 1
                        omega))))
                2 (timeVelocityVolumeOn
                  (Set.Ioo t₁ t₂ ×ˢ O₁)))) ^ 2) ≤
            C *
              (ParabolicWeakDerivativeFamily.squaredL2Norm D +
                ParabolicWeakDerivativeFamily.squaredL2Norm E) := by
  classical
  let Ma := diffusionGradientMajorant hM Ba
  obtain ⟨Ccore, δ, hCcore, hδ, hcore⟩ :=
    exists_gradient_spatialDifferenceQuotient_estimate_of_testedEquation
      d t₀ t₁ t₂ t₃ ht₀₁ ht₁₂ ht₂₃ O₀ O₁ hO₀ hO₁
      hO₁compact hO₁O₀ lam Lam Ma hlam hlamLam
      (diffusionGradientMajorant_nonneg hM Ba hBa)
  let K := (Fintype.card (ParabolicDerivativeIndex d M) : ℝ) * (1 + (d : ℝ)) +
    fullResidualCoarseConstant hM Ba Bb Bc
  refine ⟨Ccore * K, δ, mul_nonneg hCcore ?_, hδ, ?_⟩
  · dsimp only [K]
    exact add_nonneg
      (mul_nonneg (by positivity) (by positivity))
      (fullResidualCoarseConstant_nonneg hM Ba Bb Bc)
  · rintro a b c F u D E ⟨hEll, ha, hb, hc, haBound, hbBound, hcBound⟩ hEq
    let U : Set (TimeVelocity d) := Set.Ioo t₀ t₃ ×ˢ O₀
    have hU : IsOpen U := isOpen_Ioo.prod hO₀
    let BaM : Fin d → Fin d → ParabolicDerivativeIndex d M → ℝ :=
      fun i j alpha => Ba i j
        (ParabolicDerivativeIndex.castLE (Nat.le_succ M) alpha)
    have hproper := properResidual_memLp_and_sum_sq_le_coarse U hU
      a b c u F D E BaM Bb Bc
      (fun i j alpha => hBa i j
        (ParabolicDerivativeIndex.castLE (Nat.le_succ M) alpha))
      hBb hBc (fun i j => (ha i j).of_le (by
        exact_mod_cast Nat.le_succ M)) hb hc
      (fun i j alpha z hz => haBound i j
        (ParabolicDerivativeIndex.castLE (Nat.le_succ M) alpha) z hz)
      hbBound hcBound
    let q (beta : ParabolicDerivativeIndex d M) := D.representative (preliftValueIndex beta)
    let G (beta : ParabolicDerivativeIndex d M) (j : Fin d) := D.representative (preliftGradientIndex beta j)
    let μ := timeVelocityVolumeOn U
    let sq : (TimeVelocity d → ℝ) → ℝ := squaredL2Seminorm μ
    have hmem := ae_restrict_mem (μ := (volume : Measure (TimeVelocity d))) hU.measurableSet
    have hda beta i j := memLp_mul_squaredL2Seminorm_le
      (diffusionGradientMajorant_nonneg hM Ba hBa)
      (diffusionGradient_aestronglyMeasurable hU hM a ha i j)
      (D.memLp (preliftGradientIndex beta j))
      (hmem.mono fun z hz => diffusionGradient_abs_le_majorant hM a Ba hBa haBound i j i z hz)
    have hB beta j := memLp_mul_squaredL2Seminorm_le
      (driftValueMajorant_nonneg Bb hBb) (driftValue_aestronglyMeasurable hU b hb j)
      (D.memLp (preliftGradientIndex beta j))
      (hmem.mono fun z hz => driftValue_abs_le_majorant b Bb hBb hbBound j z hz)
    have hC beta := memLp_mul_squaredL2Seminorm_le
      (potentialValueMajorant_nonneg Bc hBc) ((hc.continuousOn.aestronglyMeasurable hU.measurableSet))
      (D.memLp (preliftValueIndex beta))
      (hmem.mono fun z hz => potentialValue_abs_le_majorant c Bc hcBound z hz)
    have hres beta := genericPreliftFullResidual_memLp_and_sq_le
      (properDifferentiatedScalarCommutatorResidual a b c D E beta)
      (fun i j => preliftDiffusionDerivative hM a i i j) (fun j z => b z.1 z.2 j)
      (fun z => c z.1 z.2) (q beta) (G beta) (hproper.1 beta)
      Ma (driftValueMajorant Bb) (potentialValueMajorant Bc) (hda beta) (hB beta) (hC beta)
    have hqSum := component_sum_sq_le_card D preliftValueIndex
    have hGSum : (∑ beta, ∑ j, sq (G beta j)) ≤
        (Fintype.card (ParabolicDerivativeIndex d M) : ℝ) * (d : ℝ) * D.squaredL2Norm := by
      simpa only [Fintype.sum_prod_type, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, sq, G] using
        component_sum_sq_le_card D (fun p : ParabolicDerivativeIndex d M × Fin d => preliftGradientIndex p.1 p.2)
    have hGSum₂ : (∑ beta, ∑ _i : Fin d, ∑ j, sq (G beta j)) ≤
        (Fintype.card (ParabolicDerivativeIndex d M) : ℝ) * (d : ℝ) ^ 2 * D.squaredL2Norm := by
      simpa only [Fintype.sum_prod_type, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two, sq, G] using
        component_sum_sq_le_card D (fun p : ParabolicDerivativeIndex d M × Fin d × Fin d =>
          preliftGradientIndex p.1 p.2.2)
    have hresSum : (∑ beta, sq (sourceSpecificFullResidual hM a b c D E beta)) ≤
        fullResidualCoarseConstant hM Ba Bb Bc * (D.squaredL2Norm + E.squaredL2Norm) :=
      sum_le_coarse_product_of_pointwise_four_term (fun beta => sq (sourceSpecificFullResidual hM a b c D E beta))
        (fun beta => sq (properDifferentiatedScalarCommutatorResidual a b c D E beta))
        (fun beta => ∑ _i : Fin d, ∑ j, sq (G beta j)) (fun beta => ∑ j, sq (G beta j))
        (fun beta => sq (q beta)) _ _ _ _ _ _ _ _ _ (by positivity) (by positivity) (by positivity)
        (ParabolicWeakDerivativeFamily.squaredL2Norm_nonneg E) (fun beta => (hres beta).2)
        hproper.2 hGSum₂ hGSum hqSum
    have hbeta (beta : ParabolicDerivativeIndex d M) :=
      hcore (fun z => a z.1 z.2)
        (D.representative (preliftValueIndex beta))
        (fun j => D.representative (preliftGradientIndex beta j))
        (sourceSpecificFullResidual hM a b c D E beta)
        ⟨hEll,
        (fun i j => (ha i j).of_le (by
          exact_mod_cast (show 1 ≤ M + 1 by omega))),
        (fun i j k z hz =>
          spatialPartial_coefficient_abs_le_majorant hU hM a Ba hBa ha haBound
            i j k z hz),
        D.memLp (preliftValueIndex beta),
        (fun j => D.memLp (preliftGradientIndex beta j)),
        (hres beta).1,
        (fun j => D.hasWeakVelocitySucc (preliftValueIndex beta) j (by
          change beta.1.parabolicWeight + 1 ≤ M + 1
          omega)),
        sourceSpecific_testedEquation hM U hU a b c F u D E ha hb hc hEq beta (hproper.1 beta)
          (fun i j => (hda beta i j).1) (fun j => (hB beta j).1) (hC beta).1⟩
    intro h hh hhd
    have hbetaH (beta : ParabolicDerivativeIndex d M) := hbeta beta h hh hhd
    constructor
    · intro beta j i
      exact (hbetaH beta).1 j i
    · have hsum := Finset.sum_le_sum fun beta (_ : beta ∈ Finset.univ) => (hbetaH beta).2
      simp only [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
      refine hsum.trans ?_
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hCcore
      have hE := ParabolicWeakDerivativeFamily.squaredL2Norm_nonneg E
      have hDtot : D.squaredL2Norm ≤ D.squaredL2Norm + E.squaredL2Norm := le_add_of_nonneg_right hE
      have hk : 0 ≤ (Fintype.card (ParabolicDerivativeIndex d M) : ℝ) := by positivity
      have hd : 0 ≤ (d : ℝ) := by positivity
      have hx := add_le_add (add_le_add hqSum hGSum) hresSum
      refine hx.trans ?_
      dsimp only [K]
      nlinarith only [mul_le_mul_of_nonneg_left hDtot hk,
        mul_le_mul_of_nonneg_left hDtot (mul_nonneg hk hd)]

end HypoellipticAleksandrov.Parabolic
