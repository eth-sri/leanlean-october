module

public import HypoellipticAleksandrov.Parabolic.GenericPreLiftDifferentiatedWeakEquationSupport
public import HypoellipticAleksandrov.Parabolic.GenericProperCommutatorResidual
public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyPairing

/-!
# Generic pre-lift differentiated weak equation

This module exposes the source-facing differentiated scalar equation before
the next spatial lift.
-/

@[expose] public section


namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped BigOperators ENNReal Topology

theorem coordinateIteratedFDeriv_tsupport_subset
    {d : ℕ} (gamma : TimeVelocityMultiIndex d) (f : TimeVelocity d → ℝ) :
    tsupport (TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma f) ⊆ tsupport f := by
  apply closure_minimal _ isClosed_closure
  intro z hz
  apply support_iteratedFDeriv_subset (f := f) (𝕜 := ℝ) gamma.coordinateList.length
  intro hzero
  exact hz (by
    unfold TimeVelocityMultiIndex.coordinateIteratedFDeriv
    simp_all)

theorem setIntegral_mul_eq_of_tsupport_subset
    {d : ℕ} {V U : Set (TimeVelocity d)} (hU : MeasurableSet U)
    (hVU : V ⊆ U) (f g : TimeVelocity d → ℝ) (hgV : tsupport g ⊆ V) :
    (∫ z in U, f z * g z ∂(volume : Measure (TimeVelocity d))) =
      ∫ z in V, f z * g z ∂(volume : Measure (TimeVelocity d)) := by
  apply setIntegral_eq_of_subset_of_forall_diff_eq_zero hU hVU
  intro z hz
  have hgz : g z = 0 := by
    by_contra hn
    exact hz.2 (hgV (subset_closure hn))
  grind

theorem timeDerivative_tsupport_subset
    {d : ℕ} (f : TimeVelocity d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    tsupport (timeDerivative f) ⊆ tsupport f := by
  have heq : timeDerivative f =
      TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (Pi.single (timeCoord d) 1) f := by
    funext z
    have h := TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at
      (0) (timeCoord d) f z
        (by
          simpa [TimeVelocityMultiIndex.order, VelocityMultiIndex.order,
            TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity, Pi.zero_apply] using
            hf.contDiffAt.of_le
              (show (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) by simp))
    rw [show TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (0 : TimeVelocityMultiIndex d) f = f by
      aesop] at h
    aesop
  rw [heq]
  exact coordinateIteratedFDeriv_tsupport_subset _ f

theorem velocityGradient_tsupport_subset
    {d : ℕ} (f : TimeVelocity d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (i : Fin d) :
    tsupport (fun z ↦ velocityGradient f z i) ⊆ tsupport f := by
  have heq : (fun z ↦ velocityGradient f z i) =
      TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (Pi.single (velocityCoord i) 1) f := by
    funext z
    have h := TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at
      (0) (velocityCoord i) f z
        (by
          simpa [TimeVelocityMultiIndex.order, VelocityMultiIndex.order,
            TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity, Pi.zero_apply] using
            hf.contDiffAt.of_le
              (show (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) by simp))
    rw [show TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (0 : TimeVelocityMultiIndex d) f = f by
      aesop] at h
    aesop
  rw [heq]
  exact coordinateIteratedFDeriv_tsupport_subset _ f

theorem bounded_mul_memLp
    {d : ℕ} {V : Set (TimeVelocity d)} (hV : IsOpen V)
    (q f : TimeVelocity d → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hq : ContinuousOn q V) (hqBound : ∀ z ∈ V, |q z| ≤ C)
    (hf : ParabolicMemLpOn V 2 f) :
    ParabolicMemLpOn V 2 (fun z ↦ q z * f z) := by
  have hqMeas : AEStronglyMeasurable q (timeVelocityVolumeOn V) :=
    hq.aestronglyMeasurable hV.measurableSet
  have hqBoundAE : ∀ᵐ z ∂timeVelocityVolumeOn V, |q z| ≤ C := by
    filter_upwards [ae_restrict_mem hV.measurableSet] with z hz
    simp_all
  have hprodMeas : AEStronglyMeasurable (fun z ↦ q z * f z)
      _ := hqMeas.mul hf.aestronglyMeasurable
  apply MemLp.of_le_mul hf hprodMeas
  filter_upwards [hqBoundAE] with z hz
  simpa using
    mul_le_mul hz le_rfl (abs_nonneg (f z)) hC



variable {d M : ℕ} {V : Set (TimeVelocity d)}


private theorem properAtom_memLp
    {d M N : ℕ} {V : Set (TimeVelocity d)} (hV : IsOpen V)
    (q : TimeVelocity d → ℝ) (hq : ContDiffOn ℝ N q V)
    (B : ParabolicDerivativeIndex d N → ℝ) (hB : ∀ alpha, 0 ≤ B alpha)
    (hqBound : ∀ alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 q z| ≤ B alpha)
    (hMN : M ≤ N) (beta : ParabolicDerivativeIndex d M)
    (gamma : TimeVelocityMultiIndex.Split beta.1)
    (f : gamma.left ≠ 0 → TimeVelocity d → ℝ)
    (hf : ∀ hproper, ParabolicMemLpOn V 2 (f hproper)) :
    ParabolicMemLpOn V 2 (fun z ↦
      if hproper : gamma.left ≠ 0 then
        (beta.1.choose gamma.left : ℝ) *
          TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q z *
          f hproper z
      else 0) := by
  classical
  by_cases hproper : gamma.left ≠ 0
  · simp only [dif_pos hproper]
    let alpha : ParabolicDerivativeIndex d N :=
      ParabolicDerivativeIndex.castLE hMN
        (ParabolicDerivativeIndex.splitLeft beta gamma)
    apply bounded_mul_memLp hV _ _
      ((beta.1.choose gamma.left : ℝ) * B alpha)
      (mul_nonneg (Nat.cast_nonneg _) (hB alpha))
    · exact continuousOn_const.mul
        (coordinateIteratedFDeriv_continuousOn hV q hq gamma.left
          ((splitLeft_order_le beta gamma).trans hMN))
    · intro z hz
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      aesop
    simp_all
  simp_all

private theorem properCommutatorComponents_memLp
     (hV : IsOpen V)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (Ba : Fin d → Fin d → ParabolicDerivativeIndex d (M + 1) → ℝ)
    (Bb : Fin d → ParabolicDerivativeIndex d M → ℝ)
    (Bc : ParabolicDerivativeIndex d M → ℝ)
    (hBa : ∀ i j alpha, 0 ≤ Ba i j alpha)
    (hBb : ∀ j alpha, 0 ≤ Bb j alpha)
    (hBc : ∀ alpha, 0 ≤ Bc alpha)
    (ha : ∀ i j, ContDiffOn ℝ (M + 1)
      (fun z : TimeVelocity d ↦ a z.1 z.2 i j) V)
    (hb : ∀ j, ContDiffOn ℝ M
      (fun z : TimeVelocity d ↦ b z.1 z.2 j) V)
    (hc : ContDiffOn ℝ M (fun z : TimeVelocity d ↦ c z.1 z.2) V)
    (haBound : ∀ i j alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d ↦ a x.1 x.2 i j) z| ≤ Ba i j alpha)
    (hbBound : ∀ j alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d ↦ b x.1 x.2 j) z| ≤ Bb j alpha)
    (hcBound : ∀ alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d ↦ c x.1 x.2) z| ≤ Bc alpha)
    (beta : ParabolicDerivativeIndex d M) :
    ParabolicMemLpOn V 2 (fun z ↦
      ∑ i, ∑ j, ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
        if hproper : gamma.left ≠ 0 then
          (beta.1.choose gamma.left : ℝ) *
            TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
              (fun x : TimeVelocity d ↦ a x.1 x.2 i j) z *
            D.representative
              (ParabolicDerivativeIndex.properSplitRightVelocityTwo
                beta gamma hproper j i) z
        else 0) ∧
    ParabolicMemLpOn V 2 (fun z ↦
      ∑ j, ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
        if hproper : gamma.left ≠ 0 then
          (beta.1.choose gamma.left : ℝ) *
            TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
              (fun x : TimeVelocity d ↦ b x.1 x.2 j) z *
            D.representative
              (ParabolicDerivativeIndex.properSplitRightVelocity
                beta gamma hproper j) z
        else 0) ∧
    ParabolicMemLpOn V 2 (fun z ↦
      ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
        if hproper : gamma.left ≠ 0 then
          (beta.1.choose gamma.left : ℝ) *
            TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
              (fun x : TimeVelocity d ↦ c x.1 x.2) z *
            D.representative
              (ParabolicDerivativeIndex.properSplitRightValue
                beta gamma hproper) z
        else 0) := by
  classical
  have hAatom (i j : Fin d) (gamma : TimeVelocityMultiIndex.Split beta.1) :=
    properAtom_memLp hV _ (ha i j)
      _ (hBa i j) (haBound i j) (Nat.le_succ M) beta gamma
      (fun hproper ↦ D.representative
        (ParabolicDerivativeIndex.properSplitRightVelocityTwo
          beta gamma hproper j i))
      (fun hproper ↦ D.memLp _)
  have hBatom (j : Fin d) (gamma : TimeVelocityMultiIndex.Split beta.1) :=
    properAtom_memLp hV _ (hb j)
      _ (hBb j) (hbBound j) (le_refl M) beta gamma
      (fun hproper ↦ D.representative
        (ParabolicDerivativeIndex.properSplitRightVelocity beta gamma hproper j))
      (fun hproper ↦ D.memLp _)
  have hCatom (gamma : TimeVelocityMultiIndex.Split beta.1) :=
    properAtom_memLp hV _ hc
      Bc hBc hcBound (le_refl M) beta gamma
      (fun hproper ↦ D.representative
        (ParabolicDerivativeIndex.properSplitRightValue beta gamma hproper))
      (fun hproper ↦ D.memLp _)
  refine ⟨?_, ?_, ?_⟩
  · exact memLp_finset_sum Finset.univ fun i _ ↦
      memLp_finset_sum Finset.univ fun j _ ↦
        memLp_finset_sum Finset.univ fun gamma _ ↦ hAatom i j gamma
  · exact memLp_finset_sum Finset.univ fun j _ ↦
      memLp_finset_sum Finset.univ fun gamma _ ↦ hBatom j gamma
  · exact memLp_finset_sum Finset.univ fun gamma _ ↦ hCatom gamma

private theorem originalEquation_integral
     (hM : 1 ≤ M)
    {V : Set (TimeVelocity d)} (hV : IsOpen V)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (E : ParabolicWeakDerivativeFamily d M V
      (fun z : TimeVelocity d ↦ F z.1 z.2))
    (Ba : Fin d → Fin d → ParabolicDerivativeIndex d (M + 1) → ℝ)
    (Bb : Fin d → ParabolicDerivativeIndex d M → ℝ)
    (Bc : ParabolicDerivativeIndex d M → ℝ)
    (hBa : ∀ i j alpha, 0 ≤ Ba i j alpha)
    (hBb : ∀ j alpha, 0 ≤ Bb j alpha)
    (hBc : ∀ alpha, 0 ≤ Bc alpha)
    (ha : ∀ i j, ContDiffOn ℝ (M + 1)
      (fun z : TimeVelocity d ↦ a z.1 z.2 i j) V)
    (hb : ∀ j, ContDiffOn ℝ M
      (fun z : TimeVelocity d ↦ b z.1 z.2 j) V)
    (hc : ContDiffOn ℝ M (fun z : TimeVelocity d ↦ c z.1 z.2) V)
    (haBound : ∀ i j alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d ↦ a x.1 x.2 i j) z| ≤ Ba i j alpha)
    (hbBound : ∀ j alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d ↦ b x.1 x.2 j) z| ≤ Bb j alpha)
    (hcBound : ∀ alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d ↦ c x.1 x.2) z| ≤ Bc alpha)
    (hEq :
      (fun z ↦
        D.representative
            (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
              (ParabolicDerivativeIndex.timeOne d)) z +
          (∑ i, ∑ j, a z.1 z.2 i j *
            D.representative
              (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
                (ParabolicDerivativeIndex.velocityTwo j i)) z) +
          (∑ j, b z.1 z.2 j *
            D.representative
              (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
                (ParabolicDerivativeIndex.velocityOne j)) z) +
          c z.1 z.2 * D.representative
            (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
              (ParabolicDerivativeIndex.zeroTwo d)) z)
        =ᵐ[timeVelocityVolumeOn V] fun z ↦ F z.1 z.2)
    (beta : ParabolicDerivativeIndex d M)
    (φ : TimeVelocity d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφCompact : HasCompactSupport φ) :
    (∫ z in V, D.representative
          (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
            (ParabolicDerivativeIndex.timeOne d)) z *
        TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z ∂volume) +
      (∑ i, ∑ j, ∫ z in V, (a z.1 z.2 i j *
          D.representative
            (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
              (ParabolicDerivativeIndex.velocityTwo j i)) z) *
        TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z ∂volume) +
      (∑ j, ∫ z in V, (b z.1 z.2 j *
          D.representative
            (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
              (ParabolicDerivativeIndex.velocityOne j)) z) *
        TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z ∂volume) +
      (∫ z in V, (c z.1 z.2 * D.representative
          (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
            (ParabolicDerivativeIndex.zeroTwo d)) z) *
        TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z ∂volume) =
      ∫ z in V, F z.1 z.2 *
        TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z ∂volume := by
  classical
  let θ := TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ
  have hθSmooth := coordinateIteratedFDeriv_contDiff beta.1 φ hφ
  have hθCompact : HasCompactSupport θ :=
    hφCompact.of_isClosed_subset isClosed_closure
      (coordinateIteratedFDeriv_tsupport_subset beta.1 φ)
  have hθLp : ParabolicMemLpOn V 2 θ :=
    (hθSmooth.continuous.memLp_of_hasCompactSupport hθCompact).restrict V
  let zeroM1  :=
    ParabolicDerivativeIndex.zero d (M + 1)
  let zeroM  := ParabolicDerivativeIndex.zero d M
  have haLp (i j : Fin d) : ParabolicMemLpOn V 2 (fun z ↦
      a z.1 z.2 i j * D.representative
        (ParabolicDerivativeIndex.castLE (by omega)
          (ParabolicDerivativeIndex.velocityTwo j i)) z) := by
    apply bounded_mul_memLp hV _ _ _ (hBa i j zeroM1)
    · exact (ha i j).continuousOn
    · intro z hz
      simpa [zeroM1, TimeVelocityMultiIndex.coordinateIteratedFDeriv_zero] using
        haBound i j zeroM1 z hz
    · exact D.memLp _
  have hbLp (j : Fin d) : ParabolicMemLpOn V 2 (fun z ↦
      b z.1 z.2 j * D.representative
        (ParabolicDerivativeIndex.castLE (by omega)
          (ParabolicDerivativeIndex.velocityOne j)) z) := by
    apply bounded_mul_memLp hV _ _ _ (hBb j zeroM)
    · exact (hb j).continuousOn
    · intro z hz
      simpa [zeroM, TimeVelocityMultiIndex.coordinateIteratedFDeriv_zero] using
        hbBound j zeroM z hz
    · exact D.memLp _
  have hcLp : ParabolicMemLpOn V 2 (fun z ↦
      c z.1 z.2 * D.representative
        (ParabolicDerivativeIndex.castLE (by omega)
          (ParabolicDerivativeIndex.zeroTwo d)) z) := by
    apply bounded_mul_memLp hV _ _ _ (hBc zeroM)
    · exact hc.continuousOn
    · intro z hz
      simpa [zeroM, TimeVelocityMultiIndex.coordinateIteratedFDeriv_zero] using
        hcBound zeroM z hz
    · exact D.memLp _
  have htInt : Integrable (fun z ↦ D.representative
      (ParabolicDerivativeIndex.castLE (by omega)
        (ParabolicDerivativeIndex.timeOne d)) z * θ z)
      (timeVelocityVolumeOn V) := by
    simpa only [Pi.mul_def] using
      (D.memLp _).integrable_mul hθLp
  have haInt (i j : Fin d) := (haLp i j).integrable_mul hθLp
  have hbInt (j : Fin d) := (hbLp j).integrable_mul hθLp
  have haInt' (i j : Fin d) : Integrable (fun z ↦
      a z.1 z.2 i j * D.representative
        (ParabolicDerivativeIndex.castLE (by omega)
          (ParabolicDerivativeIndex.velocityTwo j i)) z * θ z)
      (timeVelocityVolumeOn V) := by
    simpa only [Pi.mul_def] using haInt i j
  have hbInt' (j : Fin d) : Integrable (fun z ↦
      b z.1 z.2 j * D.representative
        (ParabolicDerivativeIndex.castLE (by omega)
          (ParabolicDerivativeIndex.velocityOne j)) z * θ z)
      (timeVelocityVolumeOn V) := by
    simpa only [Pi.mul_def] using hbInt j
  have hcInt : Integrable (fun z ↦
      (c z.1 z.2 * D.representative
        (ParabolicDerivativeIndex.castLE (by omega)
          (ParabolicDerivativeIndex.zeroTwo d)) z) * θ z)
      (timeVelocityVolumeOn V) := by
    simpa only [Pi.mul_def] using hcLp.integrable_mul hθLp
  have haSumInt : Integrable (fun z ↦
      (∑ i, ∑ j, a z.1 z.2 i j * D.representative
        (ParabolicDerivativeIndex.castLE (by omega)
          (ParabolicDerivativeIndex.velocityTwo j i)) z) * θ z)
      (timeVelocityVolumeOn V) := by
    simpa only [Finset.sum_mul] using
      integrable_finset_sum Finset.univ (fun i _ ↦
        integrable_finset_sum Finset.univ (fun j _ ↦ haInt' i j))
  have hbSumInt : Integrable (fun z ↦
      (∑ j, b z.1 z.2 j * D.representative
        (ParabolicDerivativeIndex.castLE (by omega)
          (ParabolicDerivativeIndex.velocityOne j)) z) * θ z)
      (timeVelocityVolumeOn V) := by
    simpa only [Finset.sum_mul] using
      integrable_finset_sum Finset.univ (fun j _ ↦ hbInt' j)
  have hEqMul : (fun z ↦
      (D.representative
            (ParabolicDerivativeIndex.castLE (by omega)
              (ParabolicDerivativeIndex.timeOne d)) z +
        (∑ i, ∑ j, a z.1 z.2 i j * D.representative
          (ParabolicDerivativeIndex.castLE (by omega)
            (ParabolicDerivativeIndex.velocityTwo j i)) z) +
        (∑ j, b z.1 z.2 j * D.representative
          (ParabolicDerivativeIndex.castLE (by omega)
            (ParabolicDerivativeIndex.velocityOne j)) z) +
        c z.1 z.2 * D.representative
          (ParabolicDerivativeIndex.castLE (by omega)
            (ParabolicDerivativeIndex.zeroTwo d)) z) * θ z) =ᵐ[
      timeVelocityVolumeOn V] fun z ↦ F z.1 z.2 * θ z := by
    filter_upwards [hEq] with z hz
    rw [hz]
  have hraw := integral_congr_ae hEqMul
  simp only [add_mul] at hraw
  rw [integral_add, integral_add, integral_add] at hraw
  · simp only [Finset.sum_mul] at hraw
    rw [integral_finset_sum Finset.univ (fun i _ ↦
      integrable_finset_sum Finset.univ (fun j _ ↦ haInt' i j))] at hraw
    simp_rw [integral_finset_sum Finset.univ (fun j _ ↦ haInt' _ j)] at hraw
    rw [integral_finset_sum Finset.univ (fun j _ ↦ hbInt' j)] at hraw
    omega
  · exact htInt
  · exact haSumInt
  · exact htInt.add haSumInt
  · exact hbSumInt
  · exact (htInt.add haSumInt).add hbSumInt
  omega


private theorem principalComponent_pairing_explicit
     (hV : IsOpen V)
    (q : TimeVelocity d → ℝ) (hq : ContDiffOn ℝ (M + 1) q V)
    (Bq : ParabolicDerivativeIndex d (M + 1) → ℝ)
    (hBq : ∀ alpha, 0 ≤ Bq alpha)
    (hqBound : ∀ alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 q z| ≤ Bq alpha)
    {u : TimeVelocity d → ℝ}
    (hM : 1 ≤ M) (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (beta : ParabolicDerivativeIndex d M) (j i : Fin d)
    (φ : TimeVelocity d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφCompact : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    -(∫ z in V,
        q z *
            D.representative
              (ParabolicDerivativeIndex.velocitySucc
                (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
                (by
                  aesop)) z *
          velocityGradient φ z i
        ∂(volume : Measure (TimeVelocity d))) -
      ∫ z in V,
        TimeVelocityMultiIndex.coordinateIteratedFDeriv
              (Pi.single (velocityCoord i) 1) q z *
            D.representative
              (ParabolicDerivativeIndex.velocitySucc
                (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
                (by
                  aesop)) z *
          φ z
        ∂(volume : Measure (TimeVelocity d)) =
      ((-1 : ℝ) ^ beta.1.order) *
        ∫ z in V,
          (q z *
            D.representative
              (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
                (ParabolicDerivativeIndex.velocityTwo j i)) z) *
            TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z
          ∂(volume : Measure (TimeVelocity d)) -
      ∫ z in V,
        (∑ gamma : TimeVelocityMultiIndex.Split beta.1,
          if hproper : gamma.left ≠ 0 then
            (beta.1.choose gamma.left : ℝ) *
              TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q z *
              D.representative
                (ParabolicDerivativeIndex.properSplitRightVelocityTwo
                  beta gamma hproper j i) z
          else 0) * φ z
        ∂(volume : Measure (TimeVelocity d)) := GenericPreLiftDifferentiatedWeakEquationSupport.principalComponent_pairing
    hV q hq Bq hBq hqBound hM D beta j i φ hφ hφCompact hφV

private theorem principalComponents_pairing_explicit
     (hV : IsOpen V)
    (a : CoefficientField d)
    (ha : ∀ i j, ContDiffOn ℝ (M + 1)
      (fun z : TimeVelocity d ↦ a z.1 z.2 i j) V)
    (Ba : Fin d → Fin d → ParabolicDerivativeIndex d (M + 1) → ℝ)
    (hBa : ∀ i j alpha, 0 ≤ Ba i j alpha)
    (haBound : ∀ i j alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d ↦ a x.1 x.2 i j) z| ≤ Ba i j alpha)
    {u : TimeVelocity d → ℝ}
    (hM : 1 ≤ M) (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (beta : ParabolicDerivativeIndex d M)
    (φ : TimeVelocity d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφCompact : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    (∑ i, ∑ j,
        (-(∫ z in V,
            a z.1 z.2 i j *
                D.representative
                  (ParabolicDerivativeIndex.velocitySucc
                    (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
                    (by
                      aesop)) z *
              velocityGradient φ z i
            ∂(volume : Measure (TimeVelocity d))) -
          ∫ z in V,
            TimeVelocityMultiIndex.coordinateIteratedFDeriv
                  (Pi.single (velocityCoord i) 1)
                  (fun x : TimeVelocity d ↦ a x.1 x.2 i j) z *
                D.representative
                  (ParabolicDerivativeIndex.velocitySucc
                    (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
                    (by
                      aesop)) z *
              φ z
            ∂(volume : Measure (TimeVelocity d)))) =
      ((-1 : ℝ) ^ beta.1.order) *
        (∑ i, ∑ j, ∫ z in V,
          (a z.1 z.2 i j *
            D.representative
              (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
                (ParabolicDerivativeIndex.velocityTwo j i)) z) *
            TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z
          ∂(volume : Measure (TimeVelocity d))) -
      (∑ i, ∑ j, ∫ z in V,
        (∑ gamma : TimeVelocityMultiIndex.Split beta.1,
          if hproper : gamma.left ≠ 0 then
            (beta.1.choose gamma.left : ℝ) *
              TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
                (fun x : TimeVelocity d ↦ a x.1 x.2 i j) z *
              D.representative
                (ParabolicDerivativeIndex.properSplitRightVelocityTwo
                  beta gamma hproper j i) z
          else 0) * φ z
        ∂(volume : Measure (TimeVelocity d))) := by
  classical
  have hcomponent (i j : Fin d) := principalComponent_pairing_explicit hV
    _ (ha i j) _
    (hBa i j) (haBound i j) hM D beta j i φ hφ hφCompact hφV
  calc
    _ = ∑ i, ∑ j,
        (((-1) ^ beta.1.order) *
            ∫ z in V,
              (a z.1 z.2 i j *
                D.representative
                  (ParabolicDerivativeIndex.castLE (by omega)
                    (ParabolicDerivativeIndex.velocityTwo j i)) z) *
                TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z
              ∂volume -
          ∫ z in V,
            (∑ gamma : TimeVelocityMultiIndex.Split beta.1,
              if hproper : gamma.left ≠ 0 then
                (beta.1.choose gamma.left) *
                  TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
                    (fun x : TimeVelocity d ↦ a x.1 x.2 i j) z *
                  D.representative
                    (ParabolicDerivativeIndex.properSplitRightVelocityTwo
                      beta gamma hproper j i) z
              else 0) * φ z
            ∂volume) := by
      simp_all
    _ = _ := by
      simp only [Finset.sum_sub_distrib, Finset.mul_sum]

private theorem integral_genericPreliftDifferentiatedScalarEquationOn
     (hM : 1 ≤ M)
    {V : Set (TimeVelocity d)} (hV : IsOpen V)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (E : ParabolicWeakDerivativeFamily d M V
      (fun z : TimeVelocity d ↦ F z.1 z.2))
    (Ba : Fin d → Fin d → ParabolicDerivativeIndex d (M + 1) → ℝ)
    (Bb : Fin d → ParabolicDerivativeIndex d M → ℝ)
    (Bc : ParabolicDerivativeIndex d M → ℝ)
    (hBa : ∀ i j alpha, 0 ≤ Ba i j alpha)
    (hBb : ∀ j alpha, 0 ≤ Bb j alpha)
    (hBc : ∀ alpha, 0 ≤ Bc alpha)
    (ha : ∀ i j, ContDiffOn ℝ (M + 1)
      (fun z : TimeVelocity d ↦ a z.1 z.2 i j) V)
    (hb : ∀ j, ContDiffOn ℝ M
      (fun z : TimeVelocity d ↦ b z.1 z.2 j) V)
    (hc : ContDiffOn ℝ M (fun z : TimeVelocity d ↦ c z.1 z.2) V)
    (haBound : ∀ i j alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d ↦ a x.1 x.2 i j) z| ≤ Ba i j alpha)
    (hbBound : ∀ j alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d ↦ b x.1 x.2 j) z| ≤ Bb j alpha)
    (hcBound : ∀ alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d ↦ c x.1 x.2) z| ≤ Bc alpha)
    (hEq :
      (fun z ↦
        D.representative
            (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
              (ParabolicDerivativeIndex.timeOne d)) z +
          (∑ i, ∑ j, a z.1 z.2 i j *
            D.representative
              (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
                (ParabolicDerivativeIndex.velocityTwo j i)) z) +
          (∑ j, b z.1 z.2 j *
            D.representative
              (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
                (ParabolicDerivativeIndex.velocityOne j)) z) +
          c z.1 z.2 * D.representative
            (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
              (ParabolicDerivativeIndex.zeroTwo d)) z)
        =ᵐ[timeVelocityVolumeOn V] fun z ↦ F z.1 z.2)
    (beta : ParabolicDerivativeIndex d M)
    (φ : TimeVelocity d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφCompact : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    -(∫ z in V,
        D.representative
            (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) z *
          timeDerivative φ z ∂(volume : Measure (TimeVelocity d))) -
      (∑ i, ∑ j, ∫ z in V,
        a z.1 z.2 i j *
            D.representative
              (ParabolicDerivativeIndex.velocitySucc
                (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
                (by
                  change beta.1.parabolicWeight + 1 ≤ M + 1
                  omega)) z *
          velocityGradient φ z i ∂(volume : Measure (TimeVelocity d))) -
      (∑ i, ∑ j, ∫ z in V,
        TimeVelocityMultiIndex.coordinateIteratedFDeriv
              (Pi.single (velocityCoord i) 1)
              (fun x : TimeVelocity d ↦ a x.1 x.2 i j) z *
            D.representative
              (ParabolicDerivativeIndex.velocitySucc
                (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
                (by
                  change beta.1.parabolicWeight + 1 ≤ M + 1
                  omega)) z *
          φ z ∂(volume : Measure (TimeVelocity d))) +
      (∑ j, ∫ z in V,
        b z.1 z.2 j *
            D.representative
              (ParabolicDerivativeIndex.velocitySucc
                (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
                (by
                  change beta.1.parabolicWeight + 1 ≤ M + 1
                  omega)) z *
          φ z ∂(volume : Measure (TimeVelocity d))) +
      (∫ z in V, c z.1 z.2 *
          D.representative
            (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) z *
          φ z ∂(volume : Measure (TimeVelocity d))) =
      ∫ z in V,
        properDifferentiatedScalarCommutatorResidual a b c D E beta z * φ z
        ∂(volume : Measure (TimeVelocity d)) := by
  classical
  let s  := (-1 : ℝ) ^ beta.1.order
  let A  := fun z ↦
    ∑ i, ∑ j, ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
      if hproper : gamma.left ≠ 0 then
        (beta.1.choose gamma.left : ℝ) *
          TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
            (fun x : TimeVelocity d ↦ a x.1 x.2 i j) z *
          D.representative
            (ParabolicDerivativeIndex.properSplitRightVelocityTwo
              beta gamma hproper j i) z
      else 0
  let B  := fun z ↦
    ∑ j, ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
      if hproper : gamma.left ≠ 0 then
        (beta.1.choose gamma.left : ℝ) *
          TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
            (fun x : TimeVelocity d ↦ b x.1 x.2 j) z *
          D.representative
            (ParabolicDerivativeIndex.properSplitRightVelocity
              beta gamma hproper j) z
      else 0
  let C  := fun z ↦
    ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
      if hproper : gamma.left ≠ 0 then
        (beta.1.choose gamma.left : ℝ) *
          TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
            (fun x : TimeVelocity d ↦ c x.1 x.2) z *
          D.representative
            (ParabolicDerivativeIndex.properSplitRightValue
              beta gamma hproper) z
      else 0
  have hproperLp := properCommutatorComponents_memLp hV a b c D Ba Bb Bc
    hBa hBb hBc ha hb hc haBound hbBound hcBound beta
  have hφLp : ParabolicMemLpOn V 2 φ :=
    (hφ.continuous.memLp_of_hasCompactSupport hφCompact).restrict V
  have hAInt : Integrable (fun z ↦ A z * φ z) (timeVelocityVolumeOn V) := by
    simpa only [A, Pi.mul_def] using hproperLp.1.integrable_mul hφLp
  have hBInt : Integrable (fun z ↦ B z * φ z) (timeVelocityVolumeOn V) := by
    simpa only [B, Pi.mul_def] using hproperLp.2.1.integrable_mul hφLp
  have hCInt : Integrable (fun z ↦ C z * φ z) (timeVelocityVolumeOn V) := by
    simpa only [C, Pi.mul_def] using hproperLp.2.2.integrable_mul hφLp
  have hEInt : Integrable (fun z ↦ E.representative beta z * φ z)
      (timeVelocityVolumeOn V) := by
    simpa only [Pi.mul_def] using (E.memLp beta).integrable_mul hφLp
  have horiginal := originalEquation_integral hM hV a b c F D E Ba Bb Bc
    hBa hBb hBc ha hb hc haBound hbBound hcBound hEq beta φ hφ hφCompact
  have htime := GenericPreLiftDifferentiatedWeakEquationSupport.timeComponent_pairing
    D (by omega : 2 ≤ M + 1) beta φ hφ hφCompact hφV
  have hprincipal := principalComponents_pairing_explicit hV a ha Ba hBa haBound
    hM D beta φ hφ hφCompact hφV
  have hsource := GenericPreLiftDifferentiatedWeakEquationSupport.sourceComponent_pairing
    E beta φ hφ hφCompact hφV
  have hdrift (j : Fin d) :=
    GenericPreLiftDifferentiatedWeakEquationSupport.driftComponent_pairing
      hV b hb Bb hBb hbBound hM D beta j φ hφ hφCompact hφV
  have hzero :=
    GenericPreLiftDifferentiatedWeakEquationSupport.zerothOrderComponent_pairing
      hV c hc Bc hBc hcBound D beta φ hφ hφCompact hφV
  have hsquare : s * s = 1 := by
    rw [← pow_two, ← pow_mul]
    simp
  have hAijLp (i j : Fin d) : ParabolicMemLpOn V 2 (fun z ↦
      ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
        if hproper : gamma.left ≠ 0 then
          (beta.1.choose gamma.left : ℝ) *
            TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
              (fun x : TimeVelocity d ↦ a x.1 x.2 i j) z *
            D.representative
              (ParabolicDerivativeIndex.properSplitRightVelocityTwo
                beta gamma hproper j i) z
        else 0) := memLp_finset_sum Finset.univ fun gamma _ ↦
      properAtom_memLp hV _ (ha i j)
        _ (hBa i j) (haBound i j) (Nat.le_succ M) beta gamma
        _ (fun hproper ↦ D.memLp _)
  have hBjLp (j : Fin d) : ParabolicMemLpOn V 2 (fun z ↦
      ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
        if hproper : gamma.left ≠ 0 then
          (beta.1.choose gamma.left : ℝ) *
            TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
              (fun x : TimeVelocity d ↦ b x.1 x.2 j) z *
            D.representative
              (ParabolicDerivativeIndex.properSplitRightVelocity
                beta gamma hproper j) z
        else 0) := memLp_finset_sum Finset.univ fun gamma _ ↦
      properAtom_memLp hV _ (hb j)
        _ (hBb j) (hbBound j) (le_refl M) beta gamma
        _ (fun hproper ↦ D.memLp _)
  let zeroM  := ParabolicDerivativeIndex.zero d M
  have hbRootLp (j : Fin d) : ParabolicMemLpOn V 2 (fun z ↦
      b z.1 z.2 j * D.representative
        (ParabolicDerivativeIndex.velocitySucc
          (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
          (by
            change beta.1.parabolicWeight + 1 ≤ M + 1
            omega)) z) := by
    apply bounded_mul_memLp hV _ _ _ (hBb j zeroM)
    · exact (hb j).continuousOn
    · intro z hz
      simpa [zeroM, TimeVelocityMultiIndex.coordinateIteratedFDeriv_zero] using
        hbBound j zeroM z hz
    · exact D.memLp _
  have hcRootLp : ParabolicMemLpOn V 2 (fun z ↦
      c z.1 z.2 * D.representative
        (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) z) := by
    apply bounded_mul_memLp hV _ _ _ (hBc zeroM)
    · exact hc.continuousOn
    · intro z hz
      simpa [zeroM, TimeVelocityMultiIndex.coordinateIteratedFDeriv_zero] using
        hcBound zeroM z hz
    · exact D.memLp _
  have hdrift' (j : Fin d) :
      (∫ z in V, b z.1 z.2 j *
          D.representative
            (ParabolicDerivativeIndex.velocitySucc
              (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
              (by
                change beta.1.parabolicWeight + 1 ≤ M + 1
                omega)) z * φ z ∂volume) +
        (∫ z in V,
          (∑ gamma : TimeVelocityMultiIndex.Split beta.1,
            if hproper : gamma.left ≠ 0 then
              (beta.1.choose gamma.left : ℝ) *
                TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
                  (fun x : TimeVelocity d ↦ b x.1 x.2 j) z *
                D.representative
                  (ParabolicDerivativeIndex.properSplitRightVelocity
                    beta gamma hproper j) z
            else 0) * φ z ∂volume) =
        ((-1 : ℝ) ^ beta.1.order) *
          ∫ z in V, (b z.1 z.2 j * D.representative
            (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
              (ParabolicDerivativeIndex.velocityOne j)) z) *
            TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z ∂volume := by
    have h := hdrift j
    simp only [add_mul] at h
    rw [integral_add] at h
    · exact h
    · simpa only [Pi.mul_def] using (hbRootLp j).integrable_mul hφLp
    · simpa only [Pi.mul_def] using (hBjLp j).integrable_mul hφLp
  have hdriftSum :
      (∑ j, ((∫ z in V, b z.1 z.2 j *
          D.representative
            (ParabolicDerivativeIndex.velocitySucc
              (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
              (by
                change beta.1.parabolicWeight + 1 ≤ M + 1
                omega)) z * φ z ∂volume) +
        ∫ z in V,
          (∑ gamma : TimeVelocityMultiIndex.Split beta.1,
            if hproper : gamma.left ≠ 0 then
              (beta.1.choose gamma.left : ℝ) *
                TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
                  (fun x : TimeVelocity d ↦ b x.1 x.2 j) z *
                D.representative
                  (ParabolicDerivativeIndex.properSplitRightVelocity
                    beta gamma hproper j) z
            else 0) * φ z ∂volume)) =
        ∑ j, ((-1 : ℝ) ^ beta.1.order) *
          ∫ z in V, (b z.1 z.2 j * D.representative
            (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
              (ParabolicDerivativeIndex.velocityOne j)) z) *
            TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z ∂volume := Finset.sum_congr rfl fun j _ ↦ hdrift' j
  have hzero' := hzero
  simp only [add_mul] at hzero'
  have hcRootInt : Integrable (fun z ↦
      (c z.1 z.2 * D.representative
        (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) z) * φ z)
      (timeVelocityVolumeOn V) := by
    simpa only [Pi.mul_def] using hcRootLp.integrable_mul hφLp
  have hcProperInt  := hCInt
  rw [integral_add hcRootInt (by simpa only [C] using hcProperInt)] at hzero'
  have hAExpand : (∫ z in V, A z * φ z ∂volume) =
      ∑ i, ∑ j, ∫ z in V,
        (∑ gamma : TimeVelocityMultiIndex.Split beta.1,
          if hproper : gamma.left ≠ 0 then
            (beta.1.choose gamma.left : ℝ) *
              TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
                (fun x : TimeVelocity d ↦ a x.1 x.2 i j) z *
              D.representative
                (ParabolicDerivativeIndex.properSplitRightVelocityTwo
                  beta gamma hproper j i) z
          else 0) * φ z ∂volume := by
    calc
      _ = ∫ z in V, ∑ i, ∑ j,
          (∑ gamma : TimeVelocityMultiIndex.Split beta.1,
            if hproper : gamma.left ≠ 0 then
              (beta.1.choose gamma.left : ℝ) *
                TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
                  _ z *
                D.representative
                  _ z
            else 0) * φ z ∂volume := by
          apply integral_congr_ae
          filter_upwards [] with z
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_mul]
      _ = _ := by
        rw [integral_finset_sum Finset.univ (fun i _ ↦
          integrable_finset_sum Finset.univ fun j _ ↦ by
            simpa only [Pi.mul_def] using (hAijLp i j).integrable_mul hφLp)]
        apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finset_sum Finset.univ (fun j _ ↦ by
          simpa only [Pi.mul_def] using (hAijLp i j).integrable_mul hφLp)]
  have hBExpand : (∫ z in V, B z * φ z ∂volume) =
      ∑ j, ∫ z in V,
        (∑ gamma : TimeVelocityMultiIndex.Split beta.1,
          if hproper : gamma.left ≠ 0 then
            (beta.1.choose gamma.left : ℝ) *
              TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
                (fun x : TimeVelocity d ↦ b x.1 x.2 j) z *
              D.representative
                (ParabolicDerivativeIndex.properSplitRightVelocity
                  beta gamma hproper j) z
          else 0) * φ z ∂volume := by
    calc
      _ = ∫ z in V, ∑ j,
          (∑ gamma : TimeVelocityMultiIndex.Split beta.1,
            if hproper : gamma.left ≠ 0 then
              (beta.1.choose gamma.left : ℝ) *
                TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
                  _ z *
                D.representative
                  _ z
            else 0) * φ z ∂volume := by
          apply integral_congr_ae
          filter_upwards [] with z
          rw [Finset.sum_mul]
      _ = _ := by
        rw [integral_finset_sum Finset.univ (fun j _ ↦ by
          simpa only [Pi.mul_def] using (hBjLp j).integrable_mul hφLp)]
  have hresidual :
      (∫ z in V,
        properDifferentiatedScalarCommutatorResidual a b c D E beta z * φ z
        ∂volume) =
      (∫ z in V, E.representative beta z * φ z ∂volume) -
        (∫ z in V, A z * φ z ∂volume) -
        (∫ z in V, B z * φ z ∂volume) -
        (∫ z in V, C z * φ z ∂volume) := by
    unfold properDifferentiatedScalarCommutatorResidual
    simp only [sub_mul]
    change (∫ z, ((((fun z ↦ E.representative beta z * φ z) -
      (fun z ↦ A z * φ z)) - (fun z ↦ B z * φ z)) -
      (fun z ↦ C z * φ z)) z ∂(timeVelocityVolumeOn V)) = _
    simp only [Pi.sub_apply]
    rw [integral_sub, integral_sub, integral_sub] <;>
      first | exact hEInt | exact hAInt | exact hBInt | exact hCInt |
        exact hEInt.sub hAInt | exact (hEInt.sub hAInt).sub hBInt
  have hzeroRootEq :
      (∫ z in V, (c z.1 z.2 * u z) *
        TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z ∂volume) =
      ∫ z in V, (c z.1 z.2 * D.representative
        (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
          (ParabolicDerivativeIndex.zeroTwo d)) z) *
        TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z ∂volume := by
    apply integral_congr_ae
    filter_upwards [D.zero_ae] with z hz
    have hindex : ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
        (ParabolicDerivativeIndex.zeroTwo d) =
        ParabolicDerivativeIndex.zero d _ := by
      apply Subtype.ext
      simp [ParabolicDerivativeIndex.zeroTwo, ParabolicDerivativeIndex.zero]
    rw [hindex, hz]
  rw [hresidual, hAExpand, hBExpand]
  rw [hzeroRootEq] at hzero'
  simp only [Finset.sum_add_distrib] at hdriftSum
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hprincipal
  rw [← Finset.mul_sum] at hdriftSum
  have htime' := congrArg (fun x : ℝ ↦ s * x) htime
  rw [← mul_assoc, hsquare, one_mul] at htime'
  linear_combination
    ((-1 : ℝ) ^ beta.1.order) * horiginal - htime' + hprincipal +
      hdriftSum + hzero' - hsource

/-- The differentiated scalar equation tested before the next spatial lift.
The principal second-order term is integrated once in its first velocity
coordinate, retaining both the coefficient and coefficient-derivative terms. -/
theorem integral_genericPreliftDifferentiatedScalarEquation
    
    (hM : 1 ≤ M)
    (U : Set (TimeVelocity d)) (hU : IsOpen U)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (u : TimeVelocity d → ℝ)
    (D : ParabolicWeakDerivativeFamily d (M + 1) U u)
    (E : ParabolicWeakDerivativeFamily d M U
      (fun z : TimeVelocity d => F z.1 z.2))
    (ha : ∀ i j, ContDiffOn ℝ (M + 1)
      (fun z : TimeVelocity d => a z.1 z.2 i j) U)
    (hb : ∀ j, ContDiffOn ℝ M
      (fun z : TimeVelocity d => b z.1 z.2 j) U)
    (hc : ContDiffOn ℝ M
      (fun z : TimeVelocity d => c z.1 z.2) U)
    (hEq :
      (fun z =>
        D.representative
            (ParabolicDerivativeIndex.castLE
              (by omega : 2 ≤ M + 1)
              (ParabolicDerivativeIndex.timeOne d)) z +
          (∑ i, ∑ j,
            a z.1 z.2 i j *
              D.representative
                (ParabolicDerivativeIndex.castLE
                  (by omega : 2 ≤ M + 1)
                  (ParabolicDerivativeIndex.velocityTwo j i)) z) +
          (∑ j,
            b z.1 z.2 j *
              D.representative
                (ParabolicDerivativeIndex.castLE
                  (by omega : 2 ≤ M + 1)
                  (ParabolicDerivativeIndex.velocityOne j)) z) +
          c z.1 z.2 *
            D.representative
              (ParabolicDerivativeIndex.castLE
                (by omega : 2 ≤ M + 1)
                (ParabolicDerivativeIndex.zeroTwo d)) z)
        =ᵐ[timeVelocityVolumeOn U]
      (fun z => F z.1 z.2))
    (beta : ParabolicDerivativeIndex d M)
    (φ : TimeVelocity d → ℝ)
    (hφSmooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφCompact : HasCompactSupport φ)
    (hφSupport : tsupport φ ⊆ U) :
    -(∫ z in U,
        D.representative
            (ParabolicDerivativeIndex.castLE
              (Nat.le_succ M) beta) z *
          timeDerivative φ z
        ∂(volume : Measure (TimeVelocity d))) -
      (∑ i, ∑ j,
        ∫ z in U,
          a z.1 z.2 i j *
              D.representative
                (ParabolicDerivativeIndex.velocitySucc
                  (ParabolicDerivativeIndex.castLE
                    (Nat.le_succ M) beta) j
                  (by
                    aesop)) z *
            velocityGradient φ z i
          ∂(volume : Measure (TimeVelocity d))) -
      (∑ i, ∑ j,
        ∫ z in U,
          TimeVelocityMultiIndex.coordinateIteratedFDeriv
                (Pi.single (velocityCoord i) 1)
                (fun x : TimeVelocity d => a x.1 x.2 i j) z *
              D.representative
                (ParabolicDerivativeIndex.velocitySucc
                  (ParabolicDerivativeIndex.castLE
                    (Nat.le_succ M) beta) j
                  (by
                    aesop)) z *
            φ z
          ∂(volume : Measure (TimeVelocity d))) +
      (∑ j,
        ∫ z in U,
          b z.1 z.2 j *
              D.representative
                (ParabolicDerivativeIndex.velocitySucc
                  (ParabolicDerivativeIndex.castLE
                    (Nat.le_succ M) beta) j
                  (by
                    aesop)) z *
            φ z
          ∂(volume : Measure (TimeVelocity d))) +
      (∫ z in U,
        c z.1 z.2 *
            D.representative
              (ParabolicDerivativeIndex.castLE
                (Nat.le_succ M) beta) z *
          φ z
        ∂(volume : Measure (TimeVelocity d))) =
      ∫ z in U,
        properDifferentiatedScalarCommutatorResidual a b c D E beta z *
          φ z
        ∂(volume : Measure (TimeVelocity d)) := by
  classical
  obtain ⟨V, Ba, Bb, Bc, hV, hφV, hclosureVU, _hVCompact,
      hBa, hBb, hBc, haBoundClosure, hbBoundClosure, hcBoundClosure⟩ :=
    GenericPreLiftDifferentiatedWeakEquationSupport.exists_precompactOpen_coefficient_majorants
      hU hφCompact hφSupport a b c ha hb hc
  have hVU : V ⊆ U := subset_closure.trans hclosureVU
  let DV := D.restrict hVU
  let EV := E.restrict hVU
  have haV  :=
    fun i j ↦ (ha i j).mono hVU
  have hbV  :=
    fun j ↦ (hb j).mono hVU
  have hcV  := hc.mono hVU
  have haBound  :=
    fun i j alpha z hz ↦ haBoundClosure i j alpha z (subset_closure hz)
  have hbBound  :=
    fun j alpha z hz ↦ hbBoundClosure j alpha z (subset_closure hz)
  have hcBound  :=
    fun alpha z hz ↦ hcBoundClosure alpha z (subset_closure hz)
  have hEqV := ae_restrict_of_ae_restrict_of_subset hVU hEq
  have hlocal := integral_genericPreliftDifferentiatedScalarEquationOn hM hV
    a b c F DV EV Ba Bb Bc hBa hBb hBc haV hbV hcV haBound hbBound hcBound
    (by
      aesop)
    beta φ hφSmooth hφCompact hφV
  have htimeSupport : tsupport _ ⊆ V :=
    (timeDerivative_tsupport_subset φ hφSmooth).trans hφV
  have htime :
      (∫ z in U, D.representative
          _ z *
          timeDerivative φ z ∂volume) =
        ∫ z in V, D.representative
          (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) z *
          timeDerivative φ z ∂volume :=
    setIntegral_mul_eq_of_tsupport_subset hU.measurableSet hVU _ _ htimeSupport
  have hprincipal (i j : Fin d) :
      (∫ z in U, (a z.1 z.2 i j * D.representative
          _ z) *
          velocityGradient φ z i ∂volume) =
        ∫ z in V, (a z.1 z.2 i j * D.representative
          (ParabolicDerivativeIndex.velocitySucc
            (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
            (by aesop)) z) *
          velocityGradient φ z i ∂volume :=
    setIntegral_mul_eq_of_tsupport_subset hU.measurableSet hVU _ _
      ((velocityGradient_tsupport_subset φ hφSmooth i).trans hφV)
  have hphiMul (f : TimeVelocity d → ℝ)  :=
    setIntegral_mul_eq_of_tsupport_subset hU.measurableSet hVU f φ hφV
  aesop

end HypoellipticAleksandrov.Parabolic
