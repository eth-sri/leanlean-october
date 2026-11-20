module

public import HypoellipticAleksandrov.Parabolic.GenericPreLiftHessianRecovery
public import HypoellipticAleksandrov.Parabolic.MeasurableSpatialC1WeakLeibniz
public import HypoellipticAleksandrov.Parabolic.ProperCommutatorSquaredAggregation
public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyL2Norm
public import HypoellipticAleksandrov.Analysis.FiniteSumL2Norm
import HypoellipticAleksandrov.Analysis.L2Pairing

/-! # Generic pre-lift time-successor recovery -/

@[expose] public section

noncomputable section
namespace HypoellipticAleksandrov.Parabolic
open MeasureTheory Set
open HypoellipticAleksandrov.Analysis
open scoped BigOperators ENNReal MatrixOrder

private theorem timeSuccessorResidual_memLp_and_sq_le
    {d : ℕ} {V : Set (TimeVelocity d)}
    (R : TimeVelocity d → ℝ)
    (AH : Fin d → Fin d → TimeVelocity d → ℝ)
    (BG : Fin d → TimeVelocity d → ℝ)
    (CQ : TimeVelocity d → ℝ)
    (hR : ParabolicMemLpOn V 2 R)
    (hAH : ∀ i j, ParabolicMemLpOn V 2 (AH i j))
    (hBG : ∀ j, ParabolicMemLpOn V 2 (BG j))
    (hCQ : ParabolicMemLpOn V 2 CQ) :
    ParabolicMemLpOn V 2 (fun z =>
      R z - (∑ i, ∑ j, AH i j z) - (∑ j, BG j z) - CQ z) ∧
    squaredL2Seminorm (timeVelocityVolumeOn V) (fun z =>
      R z - (∑ i, ∑ j, AH i j z) - (∑ j, BG j z) - CQ z) ≤
      ((d : ℝ) ^ 2 + (d : ℝ) + 2) *
        (squaredL2Seminorm (timeVelocityVolumeOn V) R +
          (∑ i, ∑ j, squaredL2Seminorm (timeVelocityVolumeOn V) (AH i j)) +
          (∑ j, squaredL2Seminorm (timeVelocityVolumeOn V) (BG j)) +
          squaredL2Seminorm (timeVelocityVolumeOn V) CQ) := by
  simpa only [Pi.neg_apply, squaredL2Seminorm_neg, Finset.sum_neg_distrib, sub_eq_add_neg,
    Fintype.card_fin] using memLp_and_squaredL2Seminorm_add_terms R
    (fun i j => -AH i j) (fun j => -BG j) (-CQ)
    hR (fun i j => (hAH i j).neg) (fun j => (hBG j).neg) hCQ.neg

private noncomputable def timeSuccessorProperCoefficientEnergy
    {d M : ℕ}
    (Ba : Fin d → Fin d → ParabolicDerivativeIndex d M → ℝ)
    (Bb : Fin d → ParabolicDerivativeIndex d M → ℝ)
    (Bc : ParabolicDerivativeIndex d M → ℝ)
    (beta : ParabolicDerivativeIndex d M) : ℝ :=
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
      Bc (ParabolicDerivativeIndex.splitLeft beta gamma.1)) ^ 2)

section
variable {d M : ℕ} (Ba : Fin d → Fin d → ParabolicDerivativeIndex d M → ℝ)
  (Bb : Fin d → ParabolicDerivativeIndex d M → ℝ) (Bc : ParabolicDerivativeIndex d M → ℝ)
include d M Ba Bb Bc

private noncomputable def timeSuccessorProperResidualCoarseConstant : ℝ :=
  ∑ beta : ParabolicDerivativeIndex d M,
    ((1 + (d ^ 2 + d + 1) * properSplitCard beta : ℕ) : ℝ) *
      (1 + timeSuccessorProperCoefficientEnergy Ba Bb Bc beta)

private theorem timeSuccessorProperCoefficientEnergy_nonneg
    (beta : ParabolicDerivativeIndex d M) :
    0 ≤ timeSuccessorProperCoefficientEnergy Ba Bb Bc beta := by
  unfold timeSuccessorProperCoefficientEnergy
  positivity

end

section
variable {d M : ℕ}

private theorem timeSuccessorProperResidualCoarseConstant_nonneg
    (Ba : Fin d → Fin d → ParabolicDerivativeIndex d M → ℝ)
    (Bb : Fin d → ParabolicDerivativeIndex d M → ℝ)
    (Bc : ParabolicDerivativeIndex d M → ℝ) :
    0 ≤ timeSuccessorProperResidualCoarseConstant Ba Bb Bc := by
  exact Finset.sum_nonneg fun beta _ => mul_nonneg (by positivity)
    (add_nonneg zero_le_one
      (timeSuccessorProperCoefficientEnergy_nonneg Ba Bb Bc beta))

private def timeSuccessorValueIndex
    (beta : ParabolicDerivativeIndex d M) :
    ParabolicDerivativeIndex d (M + 1) :=
  ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta

private def timeSuccessorGradientIndex
    (beta : ParabolicDerivativeIndex d M) (j : Fin d) :
    ParabolicDerivativeIndex d (M + 1) :=
  ParabolicDerivativeIndex.velocitySucc (timeSuccessorValueIndex beta) j (by
    change beta.1.parabolicWeight + 1 ≤ M + 1
    omega)

private theorem velocityGradient_coefficient_eq_singletonDerivative {U : Set (TimeVelocity d)} (hU : IsOpen U)
    (hM : 1 ≤ M) (a : CoefficientField d)
    (ha : ∀ i j, ContDiffOn ℝ (M + 1)
      (fun z : TimeVelocity d => a z.1 z.2 i j) U)
    (k i j : Fin d) (z : TimeVelocity d) (hz : z ∈ U) :
    velocityGradient (fun x : TimeVelocity d => a x.1 x.2 i j) z k =
      TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (singletonCoefficientIndex hM k).1
        (fun x : TimeVelocity d => a x.1 x.2 i j) z := by
  rw [singletonCoefficientIndex_coe]
  exact TimeVelocityMultiIndex.velocityGradient_eq_coordinateIteratedFDeriv k
    (((ha i j).contDiffAt (hU.mem_nhds hz)).of_le (by simp))

end

private theorem hasWeakTimeDerivOn_of_testedEquation_cancellation
    {d n : ℕ} {V : Set (TimeVelocity d)}
    (q R W : TimeVelocity d → ℝ)
    (P DA AH : Fin d → Fin n → TimeVelocity d → ℝ)
    (BG : Fin n → TimeVelocity d → ℝ)
    (CQ : TimeVelocity d → ℝ)
    (hPweak : ∀ i j, HasWeakVelocityPartialDerivOn V
      i (P i j) (fun z ↦ DA i j z + AH i j z))
    (hR : ParabolicMemLpOn V 2 R)
    (hDA : ∀ i j, ParabolicMemLpOn V 2 (DA i j))
    (hAH : ∀ i j, ParabolicMemLpOn V 2 (AH i j))
    (hBG : ∀ j, ParabolicMemLpOn V 2 (BG j))
    (hCQ : ParabolicMemLpOn V 2 CQ)
    (hW : ∀ z, W z = R z - (∑ i, ∑ j, AH i j z) -
      (∑ j, BG j z) - CQ z)
    (htested : ∀ φ : TimeVelocity d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ V →
      -(∫ z in V, q z * timeDerivative φ z ∂(volume : Measure (TimeVelocity d))) -
          (∑ i, ∑ j, ∫ z in V, P i j z *
            velocityGradient φ z i ∂(volume : Measure (TimeVelocity d))) -
          (∑ i, ∑ j, ∫ z in V, DA i j z * φ z
            ∂(volume : Measure (TimeVelocity d))) +
          (∑ j, ∫ z in V, BG j z * φ z
            ∂(volume : Measure (TimeVelocity d))) +
          (∫ z in V, CQ z * φ z ∂(volume : Measure (TimeVelocity d))) =
        ∫ z in V, R z * φ z ∂(volume : Measure (TimeVelocity d))) :
    HasWeakTimeDerivOn V q W := by
  intro φ hφ hφc hφV
  have hφ₂ : ParabolicMemLpOn V 2 φ := hφ.continuous.memLp_of_hasCompactSupport hφc
  have hraw := htested φ hφ hφc hφV
  have hweak i j := hPweak i j φ hφ hφc hφV
  have hadd i j := integral_add_mul_L2 (hDA i j) (hAH i j) hφ₂
  simp only [timeVelocityVolumeOn] at hadd
  simp only [hweak, hadd, Finset.sum_add_distrib, Finset.sum_neg_distrib] at hraw
  let A : TimeVelocity d → ℝ := fun z => ∑ i, ∑ j, AH i j z
  let B : TimeVelocity d → ℝ := fun z => ∑ j, BG j z
  have hrow i : ParabolicMemLpOn V 2 (fun z => ∑ j, AH i j z) :=
    memLp_finsetSum _ fun j _ => hAH i j
  have hA : ParabolicMemLpOn V 2 A := memLp_finsetSum _ fun i _ => hrow i
  have hB : ParabolicMemLpOn V 2 B := memLp_finsetSum _ fun j _ => hBG j
  have hrowInt i := integral_sum_mul_L2 (hAH i) hφ₂
  have hAInt := integral_sum_mul_L2 hrow hφ₂
  simp_rw [hrowInt] at hAInt
  change (∫ z, q z * timeDerivative φ z ∂timeVelocityVolumeOn V) =
    -∫ z, W z * φ z ∂timeVelocityVolumeOn V
  have h₁ := integral_sub_mul_L2 hR hA hφ₂
  have h₂ := integral_sub_mul_L2 (hR.sub hA) hB hφ₂
  have h₃ := integral_sub_mul_L2 ((hR.sub hA).sub hB) hCQ hφ₂
  simp only [Pi.sub_apply] at h₂ h₃
  rw [show W = fun z => ((R z - A z) - B z) - CQ z from funext hW, h₃, h₂, h₁]
  change (∫ z, A z * φ z ∂timeVelocityVolumeOn V) = _ at hAInt
  rw [hAInt]
  have hBInt := integral_sum_mul_L2 hBG hφ₂
  change (∫ z, B z * φ z ∂timeVelocityVolumeOn V) = _ at hBInt
  rw [hBInt]
  linarith only [hraw]

/-- Canonical weak time-successor candidate obtained after recovering every
spatial derivative of the selected generic pre-lift gradients. -/
def genericPreliftTimeSuccessorResidual
    {d M : ℕ} (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    {F : ℝ → PDE.Vec d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) U u)
    (E : ParabolicWeakDerivativeFamily d M U
      (fun z : TimeVelocity d => F z.1 z.2))
    (H : TimeVelocity d → ParabolicDerivativeIndex d M →
      Fin d → Fin d → ℝ)
    (beta : ParabolicDerivativeIndex d M) (z : TimeVelocity d) : ℝ :=
  properDifferentiatedScalarCommutatorResidual a b c D E beta z -
    (∑ i : Fin d, ∑ j : Fin d, a z.1 z.2 i j * H z beta j i) -
    (∑ j : Fin d, b z.1 z.2 j *
      D.representative
        (ParabolicDerivativeIndex.velocitySucc
          (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
          (by
            change beta.1.parabolicWeight + 1 ≤ M + 1
            omega)) z) -
    c z.1 z.2 *
      D.representative
        (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) z

/-- Exact joint weak spatial-and-time conclusion of generic pre-lift
time-successor recovery. -/
def GenericPreliftTimeSuccessorConclusion
    {d M : ℕ} (V : Set (TimeVelocity d))
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    {F : ℝ → PDE.Vec d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) U u)
    (E : ParabolicWeakDerivativeFamily d M U
      (fun z : TimeVelocity d => F z.1 z.2))
    (C_HW : ℝ) : Prop :=
  ∃ H : TimeVelocity d → ParabolicDerivativeIndex d M →
      Fin d → Fin d → ℝ,
    (∀ beta j i, ParabolicMemLpOn V 2
      (fun z => H z beta j i)) ∧
    (∀ beta j i, HasWeakVelocityPartialDerivOn V i
      (fun z =>
        D.representative
          (ParabolicDerivativeIndex.velocitySucc
            (ParabolicDerivativeIndex.castLE
              (Nat.le_succ M) beta) j
            (by
              change beta.1.parabolicWeight + 1 ≤ M + 1
              omega)) z)
      (fun z => H z beta j i)) ∧
    (∀ beta, ParabolicMemLpOn V 2
      (genericPreliftTimeSuccessorResidual a b c D E H beta)) ∧
    (∀ beta, HasWeakTimeDerivOn V
      (fun z =>
        D.representative
          (ParabolicDerivativeIndex.castLE
            (Nat.le_succ M) beta) z)
      (genericPreliftTimeSuccessorResidual a b c D E H beta)) ∧
    ((∑ beta : ParabolicDerivativeIndex d M,
        ∑ j : Fin d, ∑ i : Fin d,
          squaredL2Seminorm (timeVelocityVolumeOn V) (fun z => H z beta j i)) +
      ∑ beta : ParabolicDerivativeIndex d M,
        squaredL2Seminorm (timeVelocityVolumeOn V) (genericPreliftTimeSuccessorResidual a b c D E H beta)) ≤
      C_HW *
        (ParabolicWeakDerivativeFamily.squaredL2Norm D +
          ParabolicWeakDerivativeFamily.squaredL2Norm E)

/-- The generic pre-lift Hessian determines all selected weak time successors
on the interior cylinder, with a joint spatial-and-time `L²` estimate. -/
theorem exists_genericPrelift_hessian_timeSuccessor_family_estimate
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
    ∃ C_HW : ℝ, 0 ≤ C_HW ∧
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
        GenericPreliftTimeSuccessorConclusion
          (Set.Ioo t₁ t₂ ×ˢ O₁) a b c D E C_HW := by
  classical
  obtain ⟨C_H, hC_H, hHessian⟩ :=
    exists_genericPrelift_gradient_velocityPartialDeriv_family_estimate
      d M hM t₀ t₁ t₂ t₃ ht₀₁ ht₁₂ ht₂₃ O₀ O₁ hO₀ hO₁
        hO₁compact hO₁O₀ lam Lam hlam hlamLam Ba Bb Bc hBa hBb hBc
  let BaM : Fin d → Fin d → ParabolicDerivativeIndex d M → ℝ :=
    fun i j alpha => Ba i j
      (ParabolicDerivativeIndex.castLE (Nat.le_succ M) alpha)
  let C_R := timeSuccessorProperResidualCoarseConstant BaM Bb Bc
  let B_b : ℝ := ∑ j : Fin d, (Bb j (ParabolicDerivativeIndex.zero d M)) ^ 2
  let B_c : ℝ := (Bc (ParabolicDerivativeIndex.zero d M)) ^ 2
  let N : ℝ := (d : ℝ) ^ 2 + (d : ℝ) + 2
  let K : ℝ := (Fintype.card (ParabolicDerivativeIndex d M) : ℝ)
  let C_W : ℝ := N * (C_R + Lam ^ 2 * C_H + B_b * K + B_c * K)
  let C_HW : ℝ := C_H + C_W
  have hLam : 0 ≤ Lam := le_trans (le_of_lt hlam) hlamLam
  have hBaM : ∀ i j alpha, 0 ≤ BaM i j alpha := fun i j alpha => hBa _ _ _
  have hCR : 0 ≤ C_R := timeSuccessorProperResidualCoarseConstant_nonneg BaM Bb Bc
  have hBbEnergy : 0 ≤ B_b := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hBcEnergy : 0 ≤ B_c := sq_nonneg _
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hCW : 0 ≤ C_W := by
    dsimp [C_W]
    positivity
  refine ⟨C_HW, add_nonneg hC_H hCW, ?_⟩
  intro a b c F u D E hcoeff hEq
  obtain ⟨H, hHmem, hHweak, hHsq⟩ :=
    hHessian a b c F u D E hcoeff hEq
  rcases hcoeff with ⟨hEll, ha, hb, hc, haBound, hbBound, hcBound⟩
  let U := Set.Ioo t₀ t₃ ×ˢ O₀
  let V := Set.Ioo t₁ t₂ ×ˢ O₁
  have hVopen : IsOpen V := isOpen_Ioo.prod hO₁
  have hVU : V ⊆ U := Set.prod_mono
    (Set.Ioo_subset_Ioo ht₀₁.le ht₂₃.le) (subset_closure.trans hO₁O₀)
  have haV : ∀ i j, ContDiffOn ℝ (M + 1)
      (fun z : TimeVelocity d => a z.1 z.2 i j) V := fun i j => (ha i j).mono hVU
  have hbV : ∀ j, ContDiffOn ℝ M
      (fun z : TimeVelocity d => b z.1 z.2 j) V := fun j => (hb j).mono hVU
  have hcV : ContDiffOn ℝ M (fun z : TimeVelocity d => c z.1 z.2) V := hc.mono hVU
  have hDlocal (alpha : ParabolicDerivativeIndex d (M + 1)) :
      ParabolicMemLpOn V 2 (D.representative alpha) :=
    (D.memLp alpha).mono_measure (Measure.restrict_mono_set volume hVU)
  have hR := properDifferentiatedScalarCommutatorResidual_memLp_and_sum_sq_le
    V hVopen a b c u F (D.restrict hVU) (E.restrict hVU) BaM Bb Bc
      hBaM hBb hBc (fun i j => (haV i j).of_le (by
        exact_mod_cast Nat.le_succ M)) hbV hcV
      (fun i j alpha z hz => by
        simpa only [BaM, ParabolicWeakDerivativeFamily.restrict_representative,
          ParabolicDerivativeIndex.coe_castLE] using
          haBound i j (ParabolicDerivativeIndex.castLE (Nat.le_succ M) alpha) z (hVU hz))
      (fun j alpha z hz => hbBound j alpha z (hVU hz))
      (fun alpha z hz => hcBound alpha z (hVU hz))
  simp only [ParabolicWeakDerivativeFamily.restrict_representative] at hR
  let AH (β : ParabolicDerivativeIndex d M) (i j : Fin d) (z : TimeVelocity d) :=
    a z.1 z.2 i j * H z β j i
  let BG (β : ParabolicDerivativeIndex d M) (j : Fin d) (z : TimeVelocity d) :=
    b z.1 z.2 j * D.representative (timeSuccessorGradientIndex β j) z
  let CQ (β : ParabolicDerivativeIndex d M) (z : TimeVelocity d) :=
    c z.1 z.2 * D.representative (timeSuccessorValueIndex β) z
  have hAbsA (i j : Fin d) (z : TimeVelocity d) (hz : z ∈ V) : |a z.1 z.2 i j| ≤ Lam :=
    HypoellipticAleksandrov.abs_apply_le_of_loewner hlam
      (hEll z (hVU hz)).1 (hEll z (hVU hz)).2 i j
  have weighted {w f : TimeVelocity d → ℝ} {C : ℝ} (hC : 0 ≤ C)
      (hw : ContinuousOn w V) (hf : ParabolicMemLpOn V 2 f) (hwC : ∀ z ∈ V, |w z| ≤ C) :=
    memLp_mul_squaredL2Seminorm_le hC (hw.aestronglyMeasurable hVopen.measurableSet)
      hf (MeasureTheory.ae_restrict_of_forall_mem hVopen.measurableSet hwC)
  have hAH β i j := weighted hLam (haV i j).continuousOn (hHmem β j i) (hAbsA i j)
  have hBG β j := weighted (hBb j (ParabolicDerivativeIndex.zero d M)) (hbV j).continuousOn
    (hDlocal (timeSuccessorGradientIndex β j)) (fun z hz => by
      simpa [ParabolicDerivativeIndex.zero] using hbBound j (ParabolicDerivativeIndex.zero d M) z (hVU hz))
  have hCQ β := weighted (hBc (ParabolicDerivativeIndex.zero d M)) hcV.continuousOn
    (hDlocal (timeSuccessorValueIndex β)) (fun z hz => by
      simpa [ParabolicDerivativeIndex.zero] using hcBound (ParabolicDerivativeIndex.zero d M) z (hVU hz))
  have hW (β : ParabolicDerivativeIndex d M) := timeSuccessorResidual_memLp_and_sq_le
    (properDifferentiatedScalarCommutatorResidual a b c D E β) (AH β) (BG β) (CQ β)
    (hR.1 β) (fun i j => (hAH β i j).1) (fun j => (hBG β j).1) (hCQ β).1
  refine ⟨H, hHmem, hHweak, fun β => (hW β).1, ?_, ?_⟩
  · intro beta
    let P : Fin d → Fin d → TimeVelocity d → ℝ := fun i j z =>
      a z.1 z.2 i j * D.representative (timeSuccessorGradientIndex beta j) z
    let DA : Fin d → Fin d → TimeVelocity d → ℝ := fun i j z =>
      velocityGradient (fun x : TimeVelocity d => a x.1 x.2 i j) z i *
        D.representative (timeSuccessorGradientIndex beta j) z
    have hprod (i j : Fin d) :=
      velocityC1_mul_hasWeakVelocityPartialDerivOn_memLp_eLpNorm_le hVopen i
        Lam (Ba i j (singletonCoefficientIndex hM i)) hLam (hBa _ _ _)
        (fun z : TimeVelocity d => a z.1 z.2 i j)
        ((haV i j).of_le (by norm_num))
        (hAbsA i j)
        (fun z hz => by
          rw [velocityGradient_coefficient_eq_singletonDerivative
            hVopen hM a haV i i j z hz]
          exact haBound i j (singletonCoefficientIndex hM i) z (hVU hz))
        (fun z => D.representative (timeSuccessorGradientIndex beta j) z)
        (fun z => H z beta j i) (hDlocal _) (hHmem beta j i) (hHweak beta j i)
    have hPweak : ∀ i j, HasWeakVelocityPartialDerivOn V i (P i j)
        (fun z => DA i j z + AH beta i j z) := by
      intro i j
      simpa only [P, DA, AH, timeSuccessorGradientIndex, add_comm]
        using (hprod i j).2.2.2.1
    have hDA (i j : Fin d) : ParabolicMemLpOn V 2 (DA i j) := by
      convert (hprod i j).2.2.1.sub (hAH beta i j).1 using 1
      funext z
      dsimp only [DA, AH, Pi.sub_apply]
      ring
    apply hasWeakTimeDerivOn_of_testedEquation_cancellation _
      (properDifferentiatedScalarCommutatorResidual a b c D E beta) _ P DA (AH beta) (BG beta) (CQ beta)
      hPweak (hR.1 beta) hDA (fun i j => (hAH beta i j).1) (fun j => (hBG beta j).1) (hCQ beta).1
    · intro z; rfl
    · intro φ hφ hφc hφV
      have hout := integral_genericPreliftDifferentiatedScalarEquation hM U
        (isOpen_Ioo.prod hO₀) a b c F u D E ha hb hc hEq beta φ hφ hφc
          (hφV.trans hVU)
      have localize {ψ : TimeVelocity d → ℝ} (hs : tsupport ψ ⊆ V) (f : TimeVelocity d → ℝ) :=
        setIntegral_mul_eq_of_tsupport_subset (isOpen_Ioo.prod hO₀).measurableSet hVU f ψ hs
      have hv (i : Fin d) := localize ((velocityGradient_tsupport (i := i) φ).trans hφV)
      dsimp only [U] at hout
      simp only [localize ((timeDerivative_tsupport φ).trans hφV), hv, localize hφV] at hout
      have hDAint (i j : Fin d) :
          (∫ z in V, TimeVelocityMultiIndex.coordinateIteratedFDeriv
              (Pi.single (velocityCoord i) 1)
              (fun x : TimeVelocity d => a x.1 x.2 i j) z *
                D.representative (timeSuccessorGradientIndex beta j) z * φ z) =
            ∫ z in V, velocityGradient
              (fun x : TimeVelocity d => a x.1 x.2 i j) z i *
                D.representative (timeSuccessorGradientIndex beta j) z * φ z := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hVopen.measurableSet] with z hz
        rw [velocityGradient_coefficient_eq_singletonDerivative
          hVopen hM a haV i i j z hz, singletonCoefficientIndex_coe]
      dsimp only [timeSuccessorGradientIndex, timeSuccessorValueIndex] at hDAint
      simp_rw [hDAint] at hout
      simpa only [P, DA, BG, CQ, timeSuccessorGradientIndex,
        timeSuccessorValueIndex] using hout
  · let Etotal := ParabolicWeakDerivativeFamily.squaredL2Norm D +
        ParabolicWeakDerivativeFamily.squaredL2Norm E
    have hDnorm := ParabolicWeakDerivativeFamily.squaredL2Norm_nonneg D
    have hEnorm := ParabolicWeakDerivativeFamily.squaredL2Norm_nonneg E
    have hEtotal : 0 ≤ Etotal := add_nonneg hDnorm hEnorm
    have component_le {L : ℕ} {q : TimeVelocity d → ℝ} (G : ParabolicWeakDerivativeFamily d L U q)
        (α : ParabolicDerivativeIndex d L) :
        squaredL2Seminorm (timeVelocityVolumeOn V) (G.representative α) ≤ G.squaredL2Norm :=
      ((G.restrict hVU).component_sq_le_squaredL2Norm α).trans (G.squaredL2Norm_restrict_le hVU)
    have hRcoarse :
        (∑ beta : ParabolicDerivativeIndex d M,
          squaredL2Seminorm (timeVelocityVolumeOn V) (properDifferentiatedScalarCommutatorResidual a b c D E beta)) ≤ C_R * Etotal := by
      refine hR.2.trans ?_
      dsimp only [C_R, timeSuccessorProperResidualCoarseConstant]
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro beta hbeta
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      unfold timeSuccessorProperCoefficientEnergy
      simp only [add_mul, Finset.sum_mul, one_mul, add_assoc, mul_pow]
      gcongr
      · exact (component_le E beta).trans (le_add_of_nonneg_left hDnorm)
      all_goals exact (component_le D _).trans (le_add_of_nonneg_right hEnorm)
    have hWsum : (∑ beta : ParabolicDerivativeIndex d M,
        squaredL2Seminorm (timeVelocityVolumeOn V) (genericPreliftTimeSuccessorResidual a b c D E H beta)) ≤ C_W * Etotal := by
      refine (sum_le_mul_four_term_bound (CR := C_R) (CA := Lam ^ 2 * C_H)
        (CB := B_b * K) (CC := B_c * K) (E := Etotal)
        hN (fun β => (hW β).2) hRcoarse ?_ ?_ ?_).trans_eq rfl
      · calc
          _ ≤ ∑ beta, ∑ i, ∑ j, Lam ^ 2 *
              squaredL2Seminorm (timeVelocityVolumeOn V) (fun z => H z beta j i) := by
                gcongr
                exact (hAH _ _ _).2
          _ = Lam ^ 2 * (∑ beta, ∑ j, ∑ i,
              squaredL2Seminorm (timeVelocityVolumeOn V) (fun z => H z beta j i)) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro beta hbeta
                rw [Finset.mul_sum]
                rw [Finset.sum_comm]
                simp_rw [Finset.mul_sum]
          _ ≤ Lam ^ 2 * C_H * Etotal := by
                rw [mul_assoc]
                exact mul_le_mul_of_nonneg_left hHsq (sq_nonneg _)
      · calc
          _ ≤ ∑ beta, ∑ j, (Bb j (ParabolicDerivativeIndex.zero d M)) ^ 2 *
              ParabolicWeakDerivativeFamily.squaredL2Norm D := by gcongr; exact (hBG _ _).2.trans (mul_le_mul_of_nonneg_left (component_le D _) (sq_nonneg _))
          _ = K * B_b * ParabolicWeakDerivativeFamily.squaredL2Norm D := by
            simp only [Finset.sum_const, nsmul_eq_mul, K, B_b,
              Finset.card_univ]
            rw [← Finset.sum_mul]
            ac_rfl
          _ ≤ K * B_b * Etotal :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hEnorm)
              (mul_nonneg hK hBbEnergy)
          _ = B_b * K * Etotal := by ring
      · calc
          _ ≤ ∑ _beta : ParabolicDerivativeIndex d M,
              B_c * ParabolicWeakDerivativeFamily.squaredL2Norm D := by
                gcongr; exact (hCQ _).2.trans (mul_le_mul_of_nonneg_left (component_le D _) (sq_nonneg _))
          _ = K * B_c * ParabolicWeakDerivativeFamily.squaredL2Norm D := by
            simp only [Finset.sum_const, nsmul_eq_mul, K, Finset.card_univ]
            ring
          _ ≤ K * B_c * Etotal :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hEnorm)
              (mul_nonneg hK hBcEnergy)
          _ = B_c * K * Etotal := by ring
    calc
      _ ≤ C_H * Etotal + C_W * Etotal := add_le_add hHsq hWsum
      _ = C_HW * Etotal := by dsimp only [C_HW]; ring

end HypoellipticAleksandrov.Parabolic
