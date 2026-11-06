module

public import OAI.NumberTheory.PrimeGaps.LaplaceTransform
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace OAI

namespace LargePrimeGaps

open Filter

open Set MeasureTheory





open scoped Classical



open scoped Convolution Pointwise

noncomputable def cumulativeExtension {ι : Type*} [Fintype ι]
    (T : ℝ) (f : EuclideanSpace ℝ ι → ℝ) : EuclideanSpace ℝ ι → ℝ :=
  cubeIndicator T ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] f

noncomputable def cumulativeTail {ι : Type*} [Fintype ι]
    (f : EuclideanSpace ℝ ι → ℝ) (v : EuclideanSpace ℝ ι) : ℝ :=
  ∫ y in {y | ∀ i, v i≤y i}, f y

theorem cumulativeExtension_tail {ι : Type*} [Fintype ι]
    (T : ℝ) (f : EuclideanSpace ℝ ι → ℝ)
    (hf : ∀ y, f y≠0 → ∀ i, y i≤T)
    (v : EuclideanSpace ℝ ι) (hv : ∀ i, 0≤v i) :
    cumulativeExtension T f v = cumulativeTail f v := by
  have hs : MeasurableSet {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i} := by
    rw [Set.ofPred_forall]
    exact (isClosed_iInter fun i => isClosed_le (continuous_const (y := v i)) (PiLp.continuous_apply 2 (fun _ : ι => ℝ) i)).measurableSet
  unfold cumulativeExtension cumulativeTail
  rw [convolution_def]
  change (∫ t, cubeIndicator T t * f (v-t)) = _
  rw [← integral_sub_left_eq_self (fun t => cubeIndicator T t * f (v-t)) volume v]
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [sub_sub_cancel]
  by_cases hfy : f y=0
  · simp [Set.indicator,hfy]
  · by_cases hy : ∀ i, v i≤y i
    · rw [Set.indicator_of_mem (s := {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i}) hy]
      have hcube : v-y∈negativeCube T := by
        intro i
        change -T≤v i-y i ∧ v i-y i≤0
        constructor <;> linarith [hf y hfy i,hv i,hy i]
      simp [cubeIndicator,Set.indicator_of_mem hcube]
    · rw [Set.indicator_of_notMem (s := {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i}) hy]
      have hcube : v-y∉negativeCube T := by
        intro h
        apply hy
        intro i
        have := (h i).2
        change v i-y i≤0 at this
        linarith
      simp [cubeIndicator,Set.indicator_of_notMem hcube]

section GeneralDirections

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

end GeneralDirections

noncomputable def finTailEmbed (n : ℕ) : (Fin n → ℝ) →L[ℝ] (Fin (n+1) → ℝ) :=
  let A : (Fin n → ℝ) →ₗ[ℝ] (Fin (n+1) → ℝ) :=
    { toFun := fun x => Fin.cons 0 x
      map_add' := by intros; ext i; cases i using Fin.cases <;> simp
      map_smul' := by intros; ext i; cases i using Fin.cases <;> simp }
  A.toContinuousLinearMap

@[simp] theorem finTailEmbed_apply (n : ℕ) (x : Fin n → ℝ) :
    finTailEmbed n x = Fin.cons 0 x := rfl

noncomputable def finDirections (n : ℕ) : List (Fin n → ℝ) :=
  (List.finRange n).map (fun i => Pi.single i 1)

noncomputable def piTailMeasure {n : ℕ} (v : Fin n → ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun i => volume.restrict (Ioi (v i)))

instance {n : ℕ} (v : Fin n → ℝ) : SigmaFinite (piTailMeasure v) := by
  unfold piTailMeasure
  infer_instance

instance {n : ℕ} (v : Fin n → ℝ) : IsFiniteMeasureOnCompacts (piTailMeasure v) := by
  unfold piTailMeasure
  infer_instance

noncomputable def euclideanFinDirections (n : ℕ) : List (EuclideanSpace ℝ (Fin n)) :=
  (finDirections n).map (EuclideanSpace.equiv (Fin n) ℝ).symm

@[simp] theorem euclideanFinDirections_multiplier (n : ℕ) (u : EuclideanSpace ℝ (Fin n)) :
    ((euclideanFinDirections n).map
      (fun m => laplaceFrequency (fourierCoordinateSum (Fin n)) m u)).prod =
      ∏ i, frequencyW (u i) := by
  simp only [euclideanFinDirections,finDirections,List.map_map]
  change ((List.finRange n).map (fun i =>
    laplaceFrequency (fourierCoordinateSum (Fin n)) (EuclideanSpace.single i (1:ℝ)) u)).prod = _
  rw [← Fin.prod_univ_def]
  apply Finset.prod_congr rfl
  intro i _
  convert laplaceFrequency_coordinate i u using 1
  congr 2
  grind

noncomputable def cumulativeProfile {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → ℝ :=
  fun v => cumulativeExtension tau (fun y => f y.ofLp) (WithLp.toLp 2 v)

theorem profile_coordinate_upper {n : ℕ} {tau : ℝ} {f : (Fin n → ℝ) → ℝ}
    (hf : tsupport f ⊆ positiveSimplex n tau) (y : Fin n → ℝ) (hy : y∈tsupport f)
    (i : Fin n) : y i≤tau := by
  have hh := hf hy
  exact (Finset.single_le_sum (fun j _ => (hh.1 j).le) (Finset.mem_univ i)).trans hh.2.le

theorem cumulativeProfile_tail {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : tsupport f ⊆ positiveSimplex n tau) (v : Fin n → ℝ) (hv : ∀ i, 0≤v i) :
    cumulativeProfile tau f v = ∫ y in Ici v, f y := by
  unfold cumulativeProfile
  rw [cumulativeExtension_tail tau _ _ _ hv]
  · unfold cumulativeTail
    have hm := (PiLp.volume_preserving_ofLp (Fin n)).setIntegral_preimage_emb
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurableEmbedding f (Ici v)
    exact hm
  · intro y hy i
    exact profile_coordinate_upper hf y.ofLp (subset_tsupport f hy) i

end LargePrimeGaps

end OAI
