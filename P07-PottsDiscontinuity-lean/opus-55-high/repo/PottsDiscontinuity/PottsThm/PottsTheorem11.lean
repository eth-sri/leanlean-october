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

public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsDiscontinuity.PottsThm

open PottsDiscontinuity
open PottsDiscontinuity.FK
open PottsDiscontinuity.Potts
open PottsDiscontinuity.Duality
open PottsDiscontinuity.RCInfinite

section
variable (q : ℕ)
theorem ergodic_of_cyl (hq : 2 ≤ q) (θ : FK.Parameters) (i : Fin 2) (φ : Measure LatticeConfiguration)
    (hφ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i φ) (c₀ : Set.Icc 1 q) (μ : ProbabilityMeasure (SpinSpace q))
    (h : IsProbabilityMeasure ((φ.prod (iidFieldMeasure (ProbabilityTheory.uniformOn Set.univ))).map
      (clusterColoring c₀)) ∧ ∀ A ξ, ((φ.prod (iidFieldMeasure (ProbabilityTheory.uniformOn Set.univ))).map
        (clusterColoring c₀)).real (spinCylinder q A ξ) = μ.toMeasure.real (spinCylinder q A ξ)) :
    IsTranslationErgodic μ.toMeasure := by
  have := h.1
  have : Nonempty (Set.Icc 1 q) := ⟨c₀⟩
  rw [← spinCylinderCoordinates_injective q hq (a₁ := ⟨_, h.1⟩) (funext fun i => NNReal.coe_injective (h.2 i.1 i.2))]
  exact clusterColoring_map_ergodic_of_RCmixing θ i φ hφ c₀

/-- Theorem 1.1 follows from the stated random-cluster rate input at every
positive solution of `cosh λ = √q / 2`. -/
theorem potts_theorem_1_1_of_rc_rate (hq : 4 < q)
    (hRCrate : ∀ lam : ℝ, 0 < lam → Real.cosh lam = Real.sqrt q / 2 →
      ∀ φ₀ : Measure LatticeConfiguration,
        IsRCInfiniteVolumeLimit
          (rcCriticalParameter ⟨(q : ℝ), by
            change (1 : ℝ) ≤ (q : ℝ)
            exact_mod_cast (show 1 ≤ q by omega)⟩)
          ⟨(q : ℝ), by
            change (0 : ℝ) < (q : ℝ)
            positivity⟩ 0 φ₀ →
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
  have hq2 : 2 ≤ q := by omega
  obtain ⟨μP, φ₀, φp, hRC₀, hμ₀, hES₀, hrest⟩ := exists_critical_coloured_limits q hq
  have hc : (criticalFKParameters q hq).toP = rcCriticalParameter ⟨q, by grind⟩ ∧
      (criticalFKParameters q hq).toQ = ⟨q, by grind⟩ := by
    have := fkCritical_toP_toQ q hq
    tauto
  have hR (lam hlam hcosh) := hRCrate lam hlam hcosh φ₀.toMeasure (hc.1 ▸ hc.2 ▸ hRC₀)
  obtain ⟨S₀, -, hrate₀, hpositive₀⟩ := hR _ (arcosh_pos_of_gt4 q (by exact_mod_cast hq)).1
    (arcosh_pos_of_gt4 q (by exact_mod_cast hq)).2
  have hdisc (k : Fin q) := rc_discontinuity_of_positive_rate q hq φ₀ (φp k) hRC₀ (hrest k).1 _ hpositive₀ hrate₀
  refine ⟨fun i => (μP i).toMeasure, Fin.cases hμ₀ fun k => (hrest k).2.1, ⟨critical_potts_limits_pairwise_distinct
    q hq μP φ₀ φp hRC₀ hμ₀ (fun k => (hrest k).1) (fun k => (hrest k).2.1) _ hpositive₀ hrate₀, Fin.cases ?e0 ?e1,
    critical_potts_free_measure_ne_wired_average q hq μP φ₀ φp hRC₀ hμ₀ (fun k => (hrest k).1) (fun k => (hrest k).2.1) _
      hpositive₀ hrate₀⟩, ?o, fun lam hlam hcosh => ?r⟩
  case e0 =>
    have hs := freeColoringMap_isFreeESC q hq φ₀ (free_no_infinite_clusters (criticalFKParameters q hq) φ₀.toMeasure
      hRC₀ (hdisc ⟨0, by omega⟩).1)
    exact ergodic_of_cyl q hq2 _ 0 _ hRC₀ _ (μP 0) ⟨hs.1, fun A ξ => (hs.2 A ξ).trans (hES₀.2 A ξ).symm⟩
  case e1 =>
    intro k
    have hs := wiredColoringMap_isWiredESC q hq (φp k) k.succ (by simp)
    exact ergodic_of_cyl q hq2 _ 1 _ (hrest k).1 _ (μP k.succ) ⟨hs.1, fun A ξ => (hs.2 A ξ).trans ((hrest k).2.2.2 A ξ).symm⟩
  case o =>
    intro k
    exact wired_pinned_one_site_probability_gt q hq2 _ (pottsCriticalBeta_pos q hq) k.succ (by simp) (φp k)
      (criticalWiredBoxLimit q hq _ (hrest k).1) (μP k.succ) (hrest k).2.1 (ENNReal.toReal_pos (hdisc k).2.ne' (measure_ne_top _ _))
  case r =>
    obtain ⟨S, hseries, hrate, hpositive⟩ := hR lam hlam hcosh
    exact ⟨S, hseries, free_spin_rate_of_rc_rate q hq2 _ (pottsCriticalBeta_pos q hq) φ₀
      (criticalFreeBoxLimit q hq φ₀ hRC₀) hRC₀ (μP 0) hμ₀ _ hrate, hpositive⟩
end

end PottsDiscontinuity.PottsThm
