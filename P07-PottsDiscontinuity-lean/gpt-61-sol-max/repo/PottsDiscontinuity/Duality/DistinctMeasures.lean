module
public import Mathlib

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.DiagonalComparison
public import PottsDiscontinuity.Duality.InfiniteDuality
public import PottsDiscontinuity.Duality.LongConnectionBound

/-! Exponential free decay distinguishes the critical free and wired measures.
This route uses the planar crossing alternative directly, without assuming
positive wired percolation or a surrounding-circuit theorem. -/

@[expose] public section

namespace PottsDiscontinuity.Duality

open FK FK.Medial MeasureTheory Filter Topology
noncomputable section

/-- A free limit with exponential two-point decay cannot be invariant under
the actual whole-plane dual transform. -/
theorem free_not_dual_invariant_of_exponential_decay (θ : Parameters)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hdecay : ∀ x : LatticeVertex, twoPoint μ x ≤
      C * Real.exp (-c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|))) :
    μ.map wholePlaneDualConfigurationHomeomorph ≠ μ := by
  have := hμ.1
  intro hmap
  
  obtain ⟨n, hn⟩ := ((tendsto_square_longConnection_bound C c hc).eventually
                       (eventually_lt_nhds (show  0  < 1 / 2 by norm_num))).exists
  let S := latticeRectangle (0, 0) n n
  let T := rectangleDualExpanded (0, 0) n n
  let B  := ( n  + 2) ^ 4 * (C * Real.exp (-c *  n ))
  have hb (U : Finset LatticeVertex)
      (hcard :  U.card  ≤ ((n : ℝ) + 2) ^ 2) :
      μ.real (longConnectionEvent U n) ≤ B := by
    calc
      μ.real (longConnectionEvent U n) ≤
           U.card  ^ 2 * (C * Real.exp (-c *  n )) :=
        free_longConnectionEvent_bound θ μ hμ C c hC hc hdecay U n
      _ ≤ (( n  + 2) ^ 2) ^ 2 * (C * Real.exp (-c *  n )) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2)
          (mul_nonneg hC (Real.exp_nonneg _))
      _ = B := by  ring
  
  
  
  
  have hu := measureReal_union_le (μ := μ) (longConnectionEvent S n)
    (wholePlaneDualConfigurationHomeomorph ⁻¹' longConnectionEvent T n)
  rw [(by
                                                                                             solve_by_elim [_root_.Iff.mpr, _root_.Set.eq_univ_iff_forall, _root_.PottsDiscontinuity.Duality.planar_long_connection_alternative] : longConnectionEvent S n ∪
      wholePlaneDualConfigurationHomeomorph ⁻¹' longConnectionEvent T n = Set.univ), (by
                 have hm := congrArg (fun ν  => ν (longConnectionEvent T n)) hmap
                 rw [Measure.map_apply wholePlaneDualConfigurationHomeomorph_measurable
                   (longConnectionEvent_measurableSet T n)] at hm
                 exact congrArg ENNReal.toReal hm : μ.real (wholePlaneDualConfigurationHomeomorph ⁻¹' longConnectionEvent T n) =
      μ.real (longConnectionEvent T n))] at hu
  simp only [measureReal_def, measure_univ] at hu
  change 1 ≤ μ.real (longConnectionEvent S n) + μ.real (longConnectionEvent T n) at hu
  
  linarith only [hu,  hb S (by
                        
                        rw [card_latticeRectangle]
                        grind) ,  hb T (by
                            
                            rw [rectangleDualExpanded_card]
                            push_cast
                            ring_nf
                            exact le_rfl) , hn]

/-- Exponential free decay at the exact frozen critical parameter implies
that the actual free and wired infinite-volume measures are different. -/
theorem free_ne_wired_at_critical_of_exponential_decay (q : Set.Ici (1 : ℝ))
    (μ₀ μ₁ : Measure LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit (criticalParameters q).toP (criticalParameters q).toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit (criticalParameters q).toP (criticalParameters q).toQ 1 μ₁)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hdecay : ∀ x : LatticeVertex, twoPoint μ₀ x ≤
      C * Real.exp (-c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|))) : μ₀ ≠ μ₁ := by
  intro heq
  apply free_not_dual_invariant_of_exponential_decay (criticalParameters q) μ₀ hμ₀
    C c hC hc hdecay
  exact (free_map_dual_eq_wired_at_critical q μ₀ μ₁ hμ₀ hμ₁).trans heq.symm

end
end PottsDiscontinuity.Duality
