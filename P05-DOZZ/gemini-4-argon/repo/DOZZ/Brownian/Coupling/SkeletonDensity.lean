/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Coupling.VectorMarkov

/-!
# Exact finite radial skeleton densities

Factor the literal positive finite-dimensional density at its final observation. Lebesgue measure
is transported by the explicit last-coordinate split, so every induction step retains all state and
time operands of the transition density.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Topology Classical

namespace DOZZ.Proofs

/-- Split a finite real vector into its initial block and final coordinate. -/
noncomputable def radialSkeletonLastSplit (n : ℕ) :
    (Fin (n + 1) → ℝ) ≃ᵐ ((Fin n → ℝ) × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).trans
    (MeasurableEquiv.prodComm : ℝ × (Fin n → ℝ) ≃ᵐ ((Fin n → ℝ) × ℝ))


/-- Its initial block is the actual `Fin.init`, without reordering observations. -/
theorem radialSkeletonLastSplit_fst n x :
    (radialSkeletonLastSplit n x).1 = Fin.init x := by
  funext i
  simp [radialSkeletonLastSplit]
  rfl

/-- Its final coordinate is the actual last observation. -/
theorem radialSkeletonLastSplit_snd n x :
    (radialSkeletonLastSplit n x).2 = x (Fin.last n) := rfl

/-- The literal finite-dimensional density measure in positive coordinates. -/
noncomputable def radialSkeletonDensityMeasure (a : ℝ) {n : ℕ} (times : Fin n → ℝ) : Measure (Fin n → ℝ) :=
  volume.withDensity (conditionedPositiveFDDVectorDensity a times)

/-- Last-coordinate factorization of the positive density before applying `ofReal`. -/
theorem conditionedPositiveFDDDensity_last_split a n
    times x :
    conditionedPositiveFDDDensity a (List.ofFn times) (List.ofFn x) =
      conditionedPositiveFDDDensity a (List.ofFn (Fin.init times)) (List.ofFn (Fin.init x)) *
        conditionedPositiveTransitionDensity a (times (Fin.last (n + 1)) - times ((Fin.last n).castSucc))
          (x ((Fin.last n).castSucc)) (x (Fin.last (n + 1))) := by
  rw [List.ofFn_succ' times, List.ofFn_succ' x]
  simp only [List.concat_eq_append]
  change conditionedPositiveFDDDensity a ((List.ofFn (Fin.init times)) ++ [times (Fin.last (n + 1))])
    ((List.ofFn (Fin.init x)) ++ [x (Fin.last (n + 1))]) = _
  rw [List.ofFn_succ (f := Fin.init times), List.ofFn_succ (f := Fin.init x), List.cons_append, List.cons_append, conditionedPositiveFDDDensity_append_split a _ _ _ _ _ _ (by simp), conditionedPositiveLastTime_ofFn_tail, conditionedPositiveLastState_ofFn_tail]
  simp only [conditionedPositiveTimeChainDensity, mul_one]
  rfl


/-- Nonnegative transition-density kernel, with zero fibers at nonpositive starts. -/
noncomputable def radialSkeletonTransitionDensityKernel (a dt : ℝ) : Kernel ℝ ℝ :=
  (Kernel.const ℝ (volume : Measure ℝ)).withDensity
    (fun x y => ENNReal.ofReal (conditionedPositiveTransitionDensity a dt x y))

instance isSFiniteKernel_radialSkeletonTransitionDensityKernel (a dt : ℝ) :
    IsSFiniteKernel (radialSkeletonTransitionDensityKernel a dt) := by
  apply Kernel.IsSFiniteKernel.withDensity
  intro x y
  exact ENNReal.ofReal_ne_top

/-- Every density-kernel fiber is the literal Doob transition-density measure. -/
theorem radialSkeletonTransitionDensityKernel_apply a dt x :
    radialSkeletonTransitionDensityKernel a dt x = conditionedPositiveTransitionMeasure a dt x := by
  rw [radialSkeletonTransitionDensityKernel, Kernel.withDensity_apply _
    (measurable_conditionedPositiveTransitionDensity_pair a dt).ennreal_ofReal, Kernel.const_apply]
  rfl



/-- The final FDD factor is an actual composition-product with the literal transition-density kernel. -/
theorem radialSkeletonDensityMeasure_last_compProd a (ha : 0 ≤ a) n
    times :
    (radialSkeletonDensityMeasure a times).map (radialSkeletonLastSplit (n + 1)) =
      (radialSkeletonDensityMeasure a (Fin.init times)) ⊗ₘ
        (radialSkeletonTransitionDensityKernel a
          (times (Fin.last (n + 1)) - times ((Fin.last n).castSucc))).comap
            (fun x : Fin (n + 1) → ℝ => x (Fin.last n)) (measurable_pi_apply _) := by
  have radialSkeletonDensityMeasure_last_split : (radialSkeletonDensityMeasure a times).map (radialSkeletonLastSplit (n + 1)) = (volume : Measure ((Fin (n + 1) → ℝ) × ℝ)).withDensity (fun p => conditionedPositiveFDDVectorDensity a (Fin.init times) p.1 * ENNReal.ofReal (conditionedPositiveTransitionDensity a (times (Fin.last (n + 1)) - times ((Fin.last n).castSucc)) (p.1 (Fin.last n)) p.2)) := by
    have conditionedPositiveFDDVectorDensity_last_split (times : Fin (n + 2) → ℝ) x : conditionedPositiveFDDVectorDensity a times x = conditionedPositiveFDDVectorDensity a (Fin.init times) (Fin.init x) * ENNReal.ofReal (conditionedPositiveTransitionDensity a (times (Fin.last (n + 1)) - times ((Fin.last n).castSucc)) (x ((Fin.last n).castSucc)) (x (Fin.last (n + 1)))) := by
      have hpast := conditionedPositiveFDDDensity_nonneg ha
        (List.ofFn (Fin.init times)) (List.ofFn (Fin.init x)) (by simp)
      rw [conditionedPositiveFDDVectorDensity, max_eq_right (conditionedPositiveFDDDensity_nonneg ha (List.ofFn times) (List.ofFn x) (by simp)),
        conditionedPositiveFDDDensity_last_split a n times x,
        ENNReal.ofReal_mul hpast]
      rw [conditionedPositiveFDDVectorDensity, max_eq_right hpast]
    have radialSkeletonLastSplit_measurePreserving n : MeasurePreserving (radialSkeletonLastSplit n) := by
      exact (show MeasurePreserving (Prod.swap : ℝ × (Fin n → ℝ) → (Fin n → ℝ) × ℝ) by simpa only [Measure.volume_eq_prod] using (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Fin n → ℝ))))).comp (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n))
    rw [radialSkeletonDensityMeasure, map_withDensity_of_measurePreserving_equiv
      (radialSkeletonLastSplit (n + 1)) volume volume (radialSkeletonLastSplit_measurePreserving _)
        _ (measurable_conditionedPositiveFDDVectorDensity a times)]
    apply withDensity_congr_ae
    filter_upwards [] with p
    rw [Function.comp_apply, conditionedPositiveFDDVectorDensity_last_split]
    have hf := radialSkeletonLastSplit_fst (n + 1) ((radialSkeletonLastSplit (n + 1)).symm p)
    have hs := radialSkeletonLastSplit_snd (n + 1) ((radialSkeletonLastSplit (n + 1)).symm p)
    rw [MeasurableEquiv.apply_symm_apply] at hf hs
    have hv := congrFun hf (Fin.last n)
    change p.1 (Fin.last n) = (radialSkeletonLastSplit (n + 1)).symm p ((Fin.last n).castSucc) at hv
    rw [← hf, ← hs, ← hv]
  rw [radialSkeletonDensityMeasure_last_split]
  let dt := times (Fin.last (n + 1)) - times ((Fin.last n).castSucc)
  have hm : Measurable (Function.uncurry (fun (x : Fin (n + 1) → ℝ) y =>
      ENNReal.ofReal (conditionedPositiveTransitionDensity a dt (x (Fin.last n)) y))) := by
    change Measurable (fun p : (Fin (n + 1) → ℝ) × ℝ =>
      ENNReal.ofReal (conditionedPositiveTransitionDensity a dt (p.1 (Fin.last n)) p.2))
    exact ((measurable_conditionedPositiveTransitionDensity_pair a dt).comp (((measurable_pi_apply (Fin.last n)).comp measurable_fst).prodMk measurable_snd : Measurable (fun p : (Fin (n + 1) → ℝ) × ℝ => (p.1 (Fin.last n), p.2)))).ennreal_ofReal
  have hk : (radialSkeletonTransitionDensityKernel a dt).comap
      (fun x : Fin (n + 1) → ℝ => x (Fin.last n)) (measurable_pi_apply _) =
      (Kernel.const (Fin (n + 1) → ℝ) (volume : Measure ℝ)).withDensity
        (fun x y => ENNReal.ofReal (conditionedPositiveTransitionDensity a dt (x (Fin.last n)) y)) := by
    ext x S hS
    rw [Kernel.comap_apply, radialSkeletonTransitionDensityKernel_apply, Kernel.withDensity_apply _ hm,
      Kernel.const_apply]
    rfl
  change _ = (radialSkeletonDensityMeasure a (Fin.init times)) ⊗ₘ
    (radialSkeletonTransitionDensityKernel a dt).comap _ _
  rw [hk, radialSkeletonDensityMeasure]
  have hf : IsSFiniteKernel ((Kernel.const (Fin (n + 1) → ℝ) (volume : Measure ℝ)).withDensity
      (fun x y => ENNReal.ofReal (conditionedPositiveTransitionDensity a dt (x (Fin.last n)) y))) := by
    apply Kernel.IsSFiniteKernel.withDensity
    intro x y
    exact ENNReal.ofReal_ne_top
  let _ := hf
  rw [Measure.withDensity_compProd_withDensity
    (measurable_conditionedPositiveFDDVectorDensity a (Fin.init times)) hm,
    Measure.compProd_const, ← Measure.volume_eq_prod]


/-- A one-coordinate FDD is exactly the literal entrance measure. -/
theorem radialSkeletonDensityMeasure_one_map a (ha : 0 ≤ a) (times : Fin 1 → ℝ)
    (ht : 0 < times 0) :
    (radialSkeletonDensityMeasure a times).map (MeasurableEquiv.funUnique (Fin 1) ℝ) =
      conditionedPositiveEntranceMeasure a (times 0) := by
  rw [radialSkeletonDensityMeasure, map_withDensity_of_measurePreserving_equiv
    (MeasurableEquiv.funUnique (Fin 1) ℝ) volume volume (volume_preserving_funUnique (Fin 1) ℝ)
      _ (measurable_conditionedPositiveFDDVectorDensity a times), conditionedPositiveEntranceMeasure]
  apply withDensity_congr_ae
  filter_upwards [] with y
  change ENNReal.ofReal (max 0 (conditionedPositiveFDDDensity a (List.ofFn times)
    (List.ofFn ((MeasurableEquiv.funUnique (Fin 1) ℝ).symm y)))) = _
  simp only [List.ofFn_succ, List.ofFn_zero, conditionedPositiveFDDDensity,
    conditionedPositiveTimeChainDensity, mul_one]
  change ENNReal.ofReal (max 0 (conditionedPositiveEntranceDensity a (times 0) y)) = _
  rw [max_eq_right (conditionedPositiveEntranceDensity_nonneg ha ht y)]


/-- Reflection of the literal positive FDD measure is the literal negative FDD measure. -/
theorem radialSkeletonDensityMeasure_map_neg a {n} times :
    (radialSkeletonDensityMeasure a times).map (conditionedCoordinateNegEquiv (Fin n)) =
      (volume : Measure (Fin n → ℝ)).withDensity (fun x => ENNReal.ofReal (max 0
        (negativeConditionedFDDDensity a (List.ofFn times) (List.ofFn x)))) := by
  let e := conditionedCoordinateNegEquiv (Fin n)
  rw [radialSkeletonDensityMeasure, map_withDensity_of_measurePreserving_equiv e volume volume ⟨e.measurable, map_conditionedCoordinateNegEquiv_volume (Fin n)⟩
    _ (measurable_conditionedPositiveFDDVectorDensity a times)]
  apply withDensity_congr_ae
  filter_upwards [] with x
  change ENNReal.ofReal (max 0 (conditionedPositiveFDDDensity a (List.ofFn times)
    (List.ofFn fun i => -x i))) = _
  have h := negativeConditionedFDDDensity_reflect a (List.ofFn times) (List.ofFn fun i => -x i)
  simp only [List.map_ofFn, Function.comp_def, neg_neg] at h
  rw [← h]

/-- Actual nonnegative tests of every zero-drift Wiener radial skeleton use the density
`conditionedPositiveFDDVectorDensity`. -/
theorem lintegral_wienerRadialSamples_zeroDrift n
    (times : Fin (n + 1) → ℝ≥0) (hpos : ∀ i, 0 < times i) (hmono : StrictMono times)
    (F : (Fin (n + 1) → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ V, F (wienerRadialSamples times V) ∂wienerTripleMeasure) =
      ∫⁻ x, conditionedPositiveFDDVectorDensity 0 (fun i => (times i : ℝ)) x * F x := by
  have wienerRadialSamples_zeroDrift_fdd : ∀ (n : ℕ) (times : Fin (n + 1) → ℝ≥0), (∀ i, 0 < times i) → StrictMono times → wienerTripleMeasure.map (wienerRadialSamples times) = radialSkeletonDensityMeasure 0 (fun i => (times i : ℝ)) := by
    have wienerRadial_samples_next_density_joint_map {n} (times : Fin (n + 1) → ℝ≥0) (s : ℝ≥0) (hs : 0 < s) (htimes : ∀ i, times i ≤ s) (hlast : times (Fin.last n) = s) (dt : ℝ≥0) (ht : 0 < dt) : wienerTripleMeasure.map (fun V => (wienerRadialSamples times V, ‖wienerVectorEval (s + dt) V‖)) = (wienerTripleMeasure.map (wienerRadialSamples times)) ⊗ₘ (radialSkeletonTransitionDensityKernel 0 dt).comap (fun x : Fin (n + 1) → ℝ => x (Fin.last n)) (measurable_pi_apply _) := by
      have radialSkeletonTransitionDensityKernel_lintegral a dt x (F : ℝ → ℝ≥0∞) (hF : Measurable F) : (∫⁻ y, F y ∂radialSkeletonTransitionDensityKernel a dt x) = ∫⁻ y, F y * ENNReal.ofReal (conditionedPositiveTransitionDensity a dt x y) := by
        rw [radialSkeletonTransitionDensityKernel_apply, conditionedPositiveTransitionMeasure,
          lintegral_withDensity_eq_lintegral_mul volume
            (show Measurable (fun y => ENNReal.ofReal (conditionedPositiveTransitionDensity a dt x y)) from
              ((measurable_conditionedPositiveTransitionDensity_pair a dt).comp
                (measurable_const.prodMk measurable_id)).ennreal_ofReal) hF]
        apply lintegral_congr
        intro y
        exact mul_comm _ _
      apply Measure.ext_of_lintegral
      intro F hF
      rw [lintegral_map hF ((measurable_wienerRadialSamples times).prodMk (measurable_wienerVectorEval (s + dt)).norm),
        wienerRadial_samples_markov_lintegral times s hs htimes dt ht F hF,
        Measure.lintegral_compProd hF]
      rw [lintegral_map hF.lintegral_kernel_prod_right' (measurable_wienerRadialSamples times)]
      apply lintegral_congr
      intro V
      rw [Kernel.comap_apply, radialSkeletonTransitionDensityKernel_lintegral _ _ _ _
        (show Measurable (fun y => F (wienerRadialSamples times V, y)) from
          hF.comp (measurable_const.prodMk measurable_id))]
      simp only [wienerRadialSamples, hlast]
    intro n
    induction n with
    | zero =>
      intro times hpos hmono
      let e := MeasurableEquiv.funUnique (Fin 1) ℝ
      apply e.measurableEmbedding.map_injective
      rw [Measure.map_map e.measurable (measurable_wienerRadialSamples times),
        radialSkeletonDensityMeasure_one_map 0 (le_refl 0) _ (hpos 0)]
      exact wienerRadialEval_map (times 0) (hpos 0)
    | succ n ih =>
      intro times hpos hmono
      let past := Fin.init times
      let s := times ((Fin.last n).castSucc)
      let dt := times (Fin.last (n + 1)) - s
      have hlastlt : s < times (Fin.last (n + 1)) := hmono (Fin.castSucc_lt_last _)
      let e := radialSkeletonLastSplit (n + 1)
      apply e.measurableEmbedding.map_injective
      rw [Measure.map_map e.measurable (measurable_wienerRadialSamples times)]
      have heval : (fun V => e (wienerRadialSamples times V)) =
          (fun V => (wienerRadialSamples past V, ‖wienerVectorEval (s + dt) V‖)) := by
        funext V
        apply Prod.ext
        · rw [radialSkeletonLastSplit_fst]
          rfl
        · rw [radialSkeletonLastSplit_snd, (add_tsub_cancel_of_le hlastlt.le)]
          rfl
      change wienerTripleMeasure.map (fun V => e (wienerRadialSamples times V)) = _
      rw [heval, wienerRadial_samples_next_density_joint_map past s (hpos _) (fun i => hmono.monotone (Fin.strictMono_castSucc.monotone (Fin.le_last i))) rfl dt (tsub_pos_iff_lt.mpr hlastlt), (ih past (fun i => hpos i.castSucc) (hmono.comp Fin.strictMono_castSucc)),
        radialSkeletonDensityMeasure_last_compProd 0 (le_refl 0) n]
      rw [(NNReal.coe_sub hlastlt.le)]
      rfl
  rw [← lintegral_map hF (measurable_wienerRadialSamples times),
    wienerRadialSamples_zeroDrift_fdd n times hpos hmono, radialSkeletonDensityMeasure,
    lintegral_withDensity_eq_lintegral_mul volume
      (measurable_conditionedPositiveFDDVectorDensity 0 _) hF]
  rfl

end DOZZ.Proofs
