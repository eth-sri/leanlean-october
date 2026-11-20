module

public import Erdos821.S2.EdgeTasks
public import Erdos821.P3Edge.RowBound
public import Erdos821.P3Edge.ColumnBound

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

open Erdos821.Blueprint.Graph Erdos821.S2Core

theorem memoryEdgeAbsoluteTask_holds (F : FixedData) (r : MemoryParameters F) :
    MemoryEdgeAbsoluteTask F r := by
  intro m C₁
  obtain ⟨Ca_row, hrow⟩ := row_tsum_le F r m C₁
  obtain ⟨Ca_col, hcol⟩ := col_tsum_le F r m C₁
  let Ca : ℝ := max Ca_row Ca_col
  refine ⟨Ca, fun J => ?_⟩
  obtain ⟨x₀_row, hrow_J⟩ := hrow J
  obtain ⟨x₀_col, hcol_J⟩ := hcol J
  let x₀ := max (edgeLogThreshold F) (max x₀_row x₀_col)
  refine ⟨x₀, fun x hx P hP A hA theta i => ?_⟩
  obtain ⟨hL1, hL10⟩ := edge_log_gates ((le_max_left _ _).trans hx)
  have hx_rc : max x₀_row x₀_col ≤ x := le_trans (le_max_right _ _) hx
  have hx_row : x ≥ x₀_row := le_trans (le_max_left _ _) hx_rc
  have hx_col : x ≥ x₀_col := le_trans (le_max_right _ _) hx_rc
  have hCa_row : (L x) ^ Ca_row ≤ (L x) ^ Ca :=
    Real.rpow_le_rpow_of_exponent_le hL1.le (le_max_left _ _)
  have hCa_col : (L x) ^ Ca_col ≤ (L x) ^ Ca :=
    Real.rpow_le_rpow_of_exponent_le hL1.le (le_max_right _ _)
  have hVpos : ∀ g : P.Group, 0 < P.V g := fun g => V_pos_of_adm hP g
  have htilted_nn := (edge_tilted_bounds hP hL1 hL10).1
  refine ⟨fun s => ⟨row_summable F r A (N x) theta i s, ?_⟩,
    fun t => ⟨col_summable F r A (N x) theta i t, ?_⟩⟩
  · calc ∑' t, ‖((absoluteMemoryEdgeKernel A (N x) r.rho theta i .all s t : ℝ) : ℂ)‖ *
          P.memoryWeight r.v t
        ≤ (L x) ^ Ca_row * P.memoryWeight r.v s := hrow_J x hx_row P hP A hA theta i s
      _ ≤ (L x) ^ Ca * P.memoryWeight r.v s :=
          mul_le_mul_of_nonneg_right hCa_row (memoryWeight_nonneg r s)
  · have hmass_nn : 0 ≤ P.memoryMass F J (N x) t :=
      memoryMass_nonneg F J (N x) hVpos htilted_nn t
    have hw_nn : 0 ≤ P.memoryWeight r.v t := memoryWeight_nonneg r t
    calc ∑' s, P.memoryMass F J (N x) s *
          ‖((absoluteMemoryEdgeKernel A (N x) r.rho theta i .all s t : ℝ) : ℂ)‖ *
          P.memoryWeight r.v s
        ≤ (L x) ^ Ca_col * P.memoryMass F J (N x) t * P.memoryWeight r.v t :=
          hcol_J x hx_col P hP A hA theta i t
      _ ≤ (L x) ^ Ca * P.memoryMass F J (N x) t * P.memoryWeight r.v t :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCa_col hmass_nn) hw_nn

end Erdos821.P3Edge

open Erdos821.Blueprint.Graph Erdos821.S2Core Erdos821.P3Edge in
theorem Erdos821.S2Core.MemoryEdgeAbsoluteTask_proof (F : FixedData) (r : MemoryParameters F) :
    Erdos821.S2Core.MemoryEdgeAbsoluteTask F r :=
  memoryEdgeAbsoluteTask_holds F r

