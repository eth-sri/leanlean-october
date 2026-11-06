module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Infra.Lambda
public import PottsDiscontinuity.PottsThm.ColoringPushforward
public import PottsDiscontinuity.PottsThm.CriticalLimits
public import PottsDiscontinuity.PottsThm.Distinctness
public import PottsDiscontinuity.PottsThm.MixtureSeparation
public import PottsDiscontinuity.PottsThm.PottsColoringErgodicity
public import PottsDiscontinuity.PottsThm.RateTransfer

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsDiscontinuity.PottsThm

open PottsDiscontinuity
open PottsDiscontinuity.FK
open PottsDiscontinuity.Potts
open PottsDiscontinuity.Duality
open PottsDiscontinuity.RCInfinite

private theorem probabilityMeasure_eq_of_spinCylinder_real (q : ℕ) (hq : 2 ≤ q)
    (μ ν : ProbabilityMeasure (SpinSpace q))
    (h : ∀ A ξ, μ.toMeasure.real (spinCylinder q A ξ) =
      ν.toMeasure.real (spinCylinder q A ξ)) : μ = ν :=
  spinCylinderCoordinates_injective q hq <| funext fun i => NNReal.coe_injective <| by
    simpa only [spinCylinderCoordinates, ProbabilityMeasure.measureReal_eq_coe_coeFn] using h i.1 i.2

theorem potts_theorem_1_1_of_rc_rate (q : ℕ) (hq : 4 < q)
    (hRCrate : ∀ lam : ℝ, 0 < lam → Real.cosh lam = Real.sqrt q / 2 →
      ∀ φ₀ : Measure LatticeConfiguration,
        IsRCInfiniteVolumeLimit
          (rcCriticalParameter ⟨(q : ℝ), by
            change (1 : ℝ) ≤ (q : ℝ)
            exact_mod_cast (show 1 ≤ q by omega)⟩)
          ⟨(q : ℝ), by
            change (0 : ℝ) < (q : ℝ)
            exact_mod_cast (show 0 < q by omega)⟩ 0 φ₀ →
        ∃ S : ℝ,
          Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
            (-1 : ℝ) ^ k / k * Real.tanh (k * lam)) atTop (𝓝 S) ∧
          Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log
            (φ₀.real {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)}))
            atTop (𝓝 (lam + 2 * S)) ∧ 0 < lam + 2 * S) :
    ∃ μ : Fin (q + 1) → Measure (ℤ × ℤ → Set.Icc 1 q),
      (∀ i, IsPottsInfiniteVolumeLimit q (pottsCriticalBeta q) i (μ i)) ∧
      ((∀ i j, i ≠ j → μ i ≠ μ j) ∧ (∀ i, IsTranslationErgodic (μ i)) ∧
        μ 0 ≠ (q : ℝ≥0∞)⁻¹ • ∑ i : Fin q, μ i.succ) ∧
      (∀ i : Fin q, (1 : ℝ) / q < (μ i.succ).real
        {σ | ((σ (0, 0) : ℕ)) = (i.succ : ℕ)}) ∧
      (∀ lam : ℝ, 0 < lam → Real.cosh lam = Real.sqrt q / 2 →
        ∃ S : ℝ,
          Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
            (-1 : ℝ) ^ k / k * Real.tanh (k * lam)) atTop (𝓝 S) ∧
          Tendsto (fun n : ℕ => -(1 / (n : ℝ)) *
              Real.log ((μ 0).real {σ | σ (0, 0) = σ (diagonalSite n)} - 1 / q))
            atTop (𝓝 (lam + 2 * S)) ∧
          0 < lam + 2 * S) := by
  classical
  have hq2 : 2 ≤ q := by omega
  have hqReal : (4 : ℝ) < q := by exact_mod_cast hq
  have hβ : 0 < pottsCriticalBeta q := pottsCriticalBeta_pos q hq
  let qI : Set.Ici (1 : ℝ) := ⟨(q : ℝ), by
    change (1 : ℝ) ≤ (q : ℝ); exact_mod_cast (show 1 ≤ q by omega)⟩
  let qO : Set.Ioi (0 : ℝ) := ⟨(q : ℝ), by
    change (0 : ℝ) < (q : ℝ); exact_mod_cast (show 0 < q by omega)⟩
  have : Nonempty (Set.Icc 1 q) := ⟨⟨1, le_rfl, by omega⟩⟩
  have hbridge := fkCritical_toP_toQ q hq
  have hcriticalParams :
      (criticalFKParameters q hq).toP = rcCriticalParameter qI ∧
        (criticalFKParameters q hq).toQ = qO :=
    ⟨by rw [hbridge.1]; rfl, by rw [hbridge.2]; exact Subtype.ext rfl⟩
  obtain ⟨μP, φ₀, φp, hRC₀, hμ₀, hES₀, hrest⟩ := exists_critical_coloured_limits q hq
  have hRCp : ∀ k : Fin q, IsRCInfiniteVolumeLimit (criticalFKParameters q hq).toP
      (criticalFKParameters q hq).toQ 1 (φp k).toMeasure := fun k => (hrest k).1
  have hμp : ∀ k : Fin q, IsPottsInfiniteVolumeLimit q (pottsCriticalBeta q) k.succ
      (μP k.succ).toMeasure := fun k => (hrest k).2.1
  have hESp : ∀ k : Fin q, IsWiredEdwardsSokalColouring q (φp k).toMeasure k.succ
      (by simp only [Fin.val_succ]; omega) (μP k.succ).toMeasure := fun k => (hrest k).2.2
  have hRC₀external : IsRCInfiniteVolumeLimit (rcCriticalParameter qI) qO 0 φ₀.toMeasure := by
    rwa [← hcriticalParams.1, ← hcriticalParams.2]
  obtain ⟨S₀, _, hrate₀, hpositive₀⟩ := hRCrate (Real.arcosh (Real.sqrt q / 2))
    (arcosh_pos_of_gt4 (q : ℝ) hqReal).1 (arcosh_pos_of_gt4 (q : ℝ) hqReal).2
    φ₀.toMeasure hRC₀external
  have hdisc (k : Fin q) := rc_discontinuity_of_positive_rate q hq φ₀ (φp k)
    hRC₀ (hRCp k) (_ + 2 * S₀) hpositive₀ hrate₀
  have hno : φ₀.toMeasure Duality.existsInfiniteCluster = 0 :=
    free_no_infinite_clusters (criticalFKParameters q hq) φ₀.toMeasure hRC₀
      (hdisc ⟨0, by omega⟩).1
  have hφ₀weak : Tendsto (fun n => boxProbabilityMeasure
      (fkParameters q hq2 (pottsCriticalBeta q) hβ) (0, 0) n) atTop (𝓝 φ₀) := by
    have ht := boxMeasure_tendsto (criticalFKParameters q hq) 0 φ₀.toMeasure hRC₀
    rw [show (⟨φ₀.toMeasure, hRC₀.1⟩ : ProbabilityMeasure LatticeConfiguration) = φ₀ by ext; rfl] at ht
    simpa [boxMeasure_free, criticalFKParameters, fkParameters] using ht
  have hφpweak (k : Fin q) : Tendsto (fun n => wiredBoxProbabilityMeasure
      (fkParameters q hq2 (pottsCriticalBeta q) hβ) (0, 0) n) atTop (𝓝 (φp k)) := by
    have ht := boxMeasure_tendsto (criticalFKParameters q hq) 1 (φp k).toMeasure (hRCp k)
    rw [show (⟨(φp k).toMeasure, (hRCp k).1⟩ : ProbabilityMeasure LatticeConfiguration) = φp k by
      ext; rfl] at ht
    simpa [boxMeasure_wired, criticalFKParameters, fkParameters] using ht
  let μ : Fin (q + 1) → Measure (SpinSpace q) := fun i => (μP i).toMeasure
  have herg (i : Fin (q + 1)) : IsTranslationErgodic (μ i) := by
    cases i using Fin.cases with
    | zero =>
      have hsampler := freeColoringMap_isFreeESC q hq φ₀ hno
      let sm : ProbabilityMeasure (SpinSpace q) := ⟨_, hsampler.1⟩
      have hPM := probabilityMeasure_eq_of_spinCylinder_real q hq2 sm (μP 0) fun A ξ =>
        (hsampler.2 A ξ).trans (hES₀.2 A ξ).symm
      rw [show μ 0 = sm.toMeasure from congrArg ProbabilityMeasure.toMeasure hPM.symm]
      exact clusterColoring_map_ergodic_of_RCmixing (criticalFKParameters q hq) 0
        φ₀.toMeasure hRC₀ (⟨1, le_rfl, by omega⟩ : Set.Icc 1 q)
    | succ k =>
      have hi : 1 ≤ (k.succ : ℕ) := by simp
      have hsampler := wiredColoringMap_isWiredESC q hq (φp k) k.succ hi
      let sm : ProbabilityMeasure (SpinSpace q) := ⟨_, hsampler.1⟩
      have hPM := probabilityMeasure_eq_of_spinCylinder_real q hq2 sm (μP k.succ) fun A ξ =>
        (hsampler.2 A ξ).trans ((hESp k).2 A ξ).symm
      rw [show μ k.succ = sm.toMeasure from congrArg ProbabilityMeasure.toMeasure hPM.symm]
      exact clusterColoring_map_ergodic_of_RCmixing (criticalFKParameters q hq) 1
        (φp k).toMeasure (hRCp k) (boundaryColor q k.succ hi)
  refine ⟨μ, fun i => Fin.cases hμ₀ hμp i,
    ⟨critical_potts_limits_pairwise_distinct q hq μP φ₀ φp hRC₀ hμ₀ hRCp hμp _ hpositive₀ hrate₀,
     herg,
     critical_potts_free_measure_ne_wired_average q hq μP φ₀ φp hRC₀ hμ₀ hRCp hμp _ hpositive₀ hrate₀⟩,
    fun k => wired_pinned_one_site_probability_gt q hq2 (pottsCriticalBeta q) hβ k.succ (by simp)
      (φp k) (hφpweak k) (μP k.succ) (hμp k)
      (ENNReal.toReal_pos (hdisc k).2.ne' (measure_ne_top _ _)),
    fun lam hlam hcosh => ?_⟩
  obtain ⟨S, hseries, hrate, hpositive⟩ := hRCrate lam hlam hcosh φ₀.toMeasure hRC₀external
  exact ⟨S, hseries, free_spin_rate_of_rc_rate q hq2 (pottsCriticalBeta q) hβ
    φ₀ hφ₀weak hRC₀ (μP 0) hμ₀ (lam + 2 * S) hrate, hpositive⟩

end PottsDiscontinuity.PottsThm
