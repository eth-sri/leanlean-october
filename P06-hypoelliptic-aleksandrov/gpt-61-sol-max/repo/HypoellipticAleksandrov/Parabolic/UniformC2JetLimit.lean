module

public import HypoellipticAleksandrov.Parabolic.CoordinateFrechetAssembly
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# Uniform limits of mollified coordinate jets

The private lemmas in this file select the scalar limits of uniformly Cauchy
coordinate jets and package the order-one and order-two indices used in the
Fréchet assembly.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open Filter


noncomputable section

variable (d : ℕ)

private def oneCoordinateIndex  (c : TimeVelocityCoord d) :
    TimeVelocityDerivativeIndex d 2 :=
  ⟨Pi.single c 1, by simp⟩

private def twoCoordinateIndex  (c e : TimeVelocityCoord d) :
    TimeVelocityDerivativeIndex d 2 :=
  ⟨Pi.single c 1 + Pi.single e 1, by simp⟩

variable {X F : Type*}

private theorem exists_uniformLimit_of_uniformCauchySeqOn_univ
     [UniformSpace F] [CompleteSpace F]
    (u : ℕ → X → F) (hu : UniformCauchySeqOn u atTop Set.univ) :
    ∃ v : X → F, TendstoUniformly u v atTop := by
  have hex : ∀ x : X, ∃ y : F, Tendsto (fun n => u n x) atTop (nhds y) := by
    intro x
    exact cauchySeq_tendsto_of_complete (hu.cauchy_map (Set.mem_univ x))
  choose v hv using hex
  refine ⟨v, ?_⟩
  rw [← tendstoUniformlyOn_univ]
  exact hu.tendstoUniformlyOn_of_tendsto (fun x _ => hv x)

private theorem tendstoUniformly_pi
     {ι : Type*} [Fintype ι]
    [PseudoMetricSpace F]
    (u : ℕ → X → ι → F) (v : X → ι → F)
    (h : ∀ i, TendstoUniformly (fun n x => u n x i) (fun x => v x i) atTop) :
    TendstoUniformly u v atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε


  filter_upwards [(show ∀ᶠ n in atTop, ∀ i, ∀ x,
      dist (v x i) (u n x i) < ε by
      simpa using
        ((Finset.univ : Finset ι).eventually_all.2 (fun i _ => (show ∀ i, ∀ᶠ n in atTop, ∀ x,
      dist (v x i) (u n x i) < ε by
            intro i
            exact Metric.tendstoUniformly_iff.mp (h i) ε hε) i)))] with n hn
  intro x
  rw [dist_pi_lt_iff hε]
  intro i
  exact hn i x

variable {d : ℕ}

variable {F : Type*}

private def coordinateAssemblerLinearMap

    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    (TimeVelocityCoord d → F) →ₗ[ℝ] (TimeVelocity d →L[ℝ] F) where
  toFun := coordinateContinuousLinearMap
  map_add' a b := by
    apply ContinuousLinearMap.ext
    intro z
    simp [coordinateContinuousLinearMap, smul_add, Finset.sum_add_distrib]
    abel
  map_smul' r a := by
    apply ContinuousLinearMap.ext
    intro z
    simp [coordinateContinuousLinearMap, Finset.smul_sum, smul_smul, mul_comm]

private def coordinateAssembler

    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] :
    (TimeVelocityCoord d → F) →L[ℝ] (TimeVelocity d →L[ℝ] F) :=
  { toLinearMap := coordinateAssemblerLinearMap
    cont := (coordinateAssemblerLinearMap (d := d) (F := F)).continuous_of_finiteDimensional }

private theorem tendstoUniformly_coordinateContinuousLinearMap
     {X F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (u : ℕ → X → TimeVelocityCoord d → F)
    (v : X → TimeVelocityCoord d → F)
    (h : ∀ c, TendstoUniformly (fun n x => u n x c) (fun x => v x c) atTop) :
    TendstoUniformly
      (fun n x => coordinateContinuousLinearMap (u n x))
      (fun x => coordinateContinuousLinearMap (v x)) atTop := by

  have hc :=
    (coordinateAssembler (d := d) (F := F)).uniformContinuous.comp_tendstoUniformly (tendstoUniformly_pi u v h)
  assumption

private theorem tendstoUniformly_coordinateBilinearOperator
     {X : Type*}
    (u : ℕ → X → TimeVelocityCoord d → TimeVelocityCoord d → ℝ)
    (v : X → TimeVelocityCoord d → TimeVelocityCoord d → ℝ)
    (h : ∀ c e, TendstoUniformly (fun n x => u n x c e)
      (fun x => v x c e) atTop) :
    TendstoUniformly
      (fun n x => coordinateBilinearOperator (u n x))
      (fun x => coordinateBilinearOperator (v x)) atTop := by
  apply tendstoUniformly_coordinateContinuousLinearMap
  intro c
  apply tendstoUniformly_coordinateContinuousLinearMap
  exact h c

variable {root : HypoellipticAleksandrov.Parabolic.ScalarField d} (G : ParabolicWeakDerivativeFamily d (2 * (d + 4)) Set.univ root) (rho : ℝ) (hrho : 0 < rho) (K : HypoellipticAleksandrov.Parabolic.Region d) (hK : IsCompact K) (hsupp : ∀ ε, 0 < ε → ε < rho → ∀ beta : TimeVelocityDerivativeIndex d (d + 4), tsupport (SpacetimeMollifier.spacetimeMollification ε (G.ordinaryRepresentative beta)) ⊆ K)

include hrho hK hsupp
private theorem exists_uniformLimit_coordinateJet

    (alpha : TimeVelocityDerivativeIndex d 2) :
    ∃ v : HypoellipticAleksandrov.Parabolic.ScalarField d,
      TendstoUniformly
        (fun n ↦ TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
          (SpacetimeMollifier.spacetimeMollification (shrinkingRadius rho n)
            (G.ordinaryRepresentative
              (TimeVelocityDerivativeIndex.zero d (d + 4)))))
        v atTop := by
  apply exists_uniformLimit_of_uniformCauchySeqOn_univ
  exact uniformCauchySeqOn_coordinateJet_spacetimeMollification_shrinkingRadius
    G rho hrho K hK hsupp alpha

/-- Uniform limits of the localized mollified coordinate jets through order two
assemble into one ambient `C²` function. -/
theorem exists_contDiff_two_uniformLimit_coordinateJet_spacetimeMollification_shrinkingRadius
      :
    ∃ v : HypoellipticAleksandrov.Parabolic.ScalarField d,
      ContDiff ℝ 2 v ∧
      ∀ alpha : TimeVelocityDerivativeIndex d 2,
        TendstoUniformly
          (fun n ↦ TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
            (SpacetimeMollifier.spacetimeMollification (shrinkingRadius rho n)
              (G.ordinaryRepresentative
                (TimeVelocityDerivativeIndex.zero d (d + 4)))))
          (TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 v) atTop := by
  let u  := fun n =>
    SpacetimeMollifier.spacetimeMollification (shrinkingRadius rho n)
      (G.ordinaryRepresentative (TimeVelocityDerivativeIndex.zero d (d + 4)))
  have hex : ∀ alpha : TimeVelocityDerivativeIndex d 2,
      ∃ w : HypoellipticAleksandrov.Parabolic.ScalarField d,
        TendstoUniformly
          (fun n => TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 (u n))
          w atTop := by
    intro alpha
    exact exists_uniformLimit_coordinateJet G rho hrho K hK hsupp alpha
  choose J hJ using hex
  let zero  := TimeVelocityDerivativeIndex.zero d 2
  let v  := J zero
  let A  := fun z =>
    coordinateContinuousLinearMap (fun c => J (oneCoordinateIndex d c) z)
  let B  := fun z =>
    coordinateBilinearOperator (fun c e => J (twoCoordinateIndex d c e) z)
  have hu_smooth (n : ℕ)  :=
    G.contDiff_spacetimeMollification_ordinaryRepresentative_zero
      _ (shrinkingRadius_pos rho hrho n)
  have hzero : TendstoUniformly u v atTop := by
    convert hJ zero using 1
    funext n z
    exact (TimeVelocityMultiIndex.coordinateIteratedFDeriv_zero (u n) z).symm
  have hA : TendstoUniformly (fun n z => fderiv ℝ (u n) z) A atTop := by
    have hcoord := tendstoUniformly_coordinateContinuousLinearMap
      (fun n z c => TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (Pi.single c 1) (u n) z)
      (fun z c => J (oneCoordinateIndex d c) z)
      (fun c => by exact hJ (oneCoordinateIndex d c))
    convert hcoord using 1
    funext n z
    exact (coordinateContinuousLinearMap_coordinateIteratedFDeriv_one_eq_fderiv
      (u n) z ((contDiff_infty.mp (hu_smooth n) 1).contDiffAt)).symm
  have hB : TendstoUniformly
      (fun n z => fderiv ℝ ((fderiv ℝ (u n))) z) B atTop := by
    have hcoord := tendstoUniformly_coordinateBilinearOperator
      (fun n z c e => TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (Pi.single c 1 + Pi.single e 1) (u n) z)
      (fun z c e => J (twoCoordinateIndex d c e) z)
      (fun c e => by exact hJ (twoCoordinateIndex d c e))
    convert hcoord using 1
    funext n z
    exact (coordinateBilinearOperator_coordinateIteratedFDeriv_two_eq
      (u n) z (hu_smooth n)).symm
  have hvA : ∀ z, HasFDerivAt v (A z) z := by
    intro z
    apply hasFDerivAt_of_tendstoUniformly hA
    · intro n x
      exact ((contDiff_infty.mp (hu_smooth n) 1).differentiable (by norm_num) x).hasFDerivAt
    · intro x
      exact hzero.tendsto_at x
  have hAB : ∀ z, HasFDerivAt A (B z) z := by
    intro z
    apply hasFDerivAt_of_tendstoUniformly hB
    · intro n x
      have hderiv : ContDiff ℝ 1 (fderiv ℝ (u n)) :=
        (contDiff_infty_iff_fderiv.mp (hu_smooth n)).2.of_le (by simp)
      exact (hderiv.differentiable (by norm_num) x).hasFDerivAt
    · intro x
      exact hA.tendsto_at x

  have hAone : ContDiff ℝ 1 A :=
    contDiff_one_iff_hasFDerivAt.mpr ⟨B, (by
        apply hB.continuous
        exact Frequently.of_forall fun n =>
          (contDiff_infty_iff_fderiv.mp
            (contDiff_infty_iff_fderiv.mp (hu_smooth n)).2).2.continuous), hAB⟩

  have hvf : fderiv ℝ v = A := by
    funext z
    exact (hvA z).fderiv
  have hAf : fderiv ℝ A = B := by
    funext z
    exact (hAB z).fderiv
  refine ⟨v, (by
      convert contDiff_succ_iff_hasFDerivAt.mpr ⟨A, hAone, hvA⟩ using 1 <;> norm_num), ?_⟩
  intro alpha
  have hord : alpha.1.order = 0 ∨ alpha.1.order = 1 ∨ alpha.1.order = 2 := by
    omega
  rcases hord with h0 | h1 | h2
  · convert hzero using 1
    · funext n z
      have hlen : alpha.1.coordinateList.length = 0 := by simpa
      have hl  := List.eq_nil_iff_length_eq_zero.mpr hlen
      rw [TimeVelocityMultiIndex.coordinateIteratedFDeriv, hl]
      simp only [List.length_nil, iteratedFDeriv_zero_apply]
      rfl
    · funext z
      have hlen : alpha.1.coordinateList.length = 0 := by simpa
      have hl  := List.eq_nil_iff_length_eq_zero.mpr hlen
      rw [TimeVelocityMultiIndex.coordinateIteratedFDeriv, hl]
      rfl
  ·
    obtain ⟨c, hc⟩ := List.length_eq_one_iff.mp (show alpha.1.coordinateList.length = 1 by simpa)
    let q  := timeVelocityBasis c
    have heval := (ContinuousLinearMap.apply ℝ ℝ q).uniformContinuous
      |>.comp_tendstoUniformly hA
    convert heval using 1
    · funext n z
      unfold TimeVelocityMultiIndex.coordinateIteratedFDeriv
      rw [hc]
      simp only [List.length_cons, List.length_nil]
      simp [q, u, Function.comp_apply]
    · funext z
      unfold TimeVelocityMultiIndex.coordinateIteratedFDeriv
      rw [hc]
      simp only [List.length_cons, List.length_nil]
      rw [iteratedFDeriv_succ_apply_right]
      simp only [iteratedFDeriv_zero_apply]
      rw [hvf]
      simp [q, Function.comp_apply]
  ·
    obtain ⟨c, e, hc⟩ := List.length_eq_two.mp (show alpha.1.coordinateList.length = 2 by simpa)
    let q₀  := timeVelocityBasis c
    let q₁  := timeVelocityBasis e
    have hout := (ContinuousLinearMap.apply ℝ (TimeVelocity d →L[ℝ] ℝ)
      q₀).uniformContinuous.comp_tendstoUniformly hB
    have heval := (ContinuousLinearMap.apply ℝ ℝ q₁).uniformContinuous
      |>.comp_tendstoUniformly hout
    convert heval using 1
    · funext n z
      unfold TimeVelocityMultiIndex.coordinateIteratedFDeriv
      rw [hc]
      simp only [List.length_cons, List.length_nil]
      rw [iteratedFDeriv_two_apply]
      simp [q₀, q₁, u, Function.comp_apply]
    · funext z
      unfold TimeVelocityMultiIndex.coordinateIteratedFDeriv
      rw [hc]
      simp only [List.length_cons, List.length_nil]
      rw [iteratedFDeriv_two_apply]
      rw [hvf, hAf]
      simp [q₀, q₁, Function.comp_apply]

end

end HypoellipticAleksandrov.Parabolic
