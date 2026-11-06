module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTime
import Batteries.Tactic.Alias
import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialBounds
public import PDEFoundation.Calculus.RegularityOrder




/-!
# Reverse-time smoothness infrastructure

This module records smoothness preservation under the reverse-time map and
the coordinate-level smoothness facts used by the reverse-time Dirichlet
construction.
-/

 public section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open scoped BigOperators Matrix.Norms.Elementwise

/-- The reverse-time map is smooth. -/
theorem contDiff_reverseTimeMap {d : ℕ} (r₁ : ℝ) :
    ContDiff ℝ ⊤ (reverseTimeMap r₁ : TimeVelocity d → TimeVelocity d) := (contDiff_const.sub contDiff_fst).prodMk contDiff_snd

/-- A function smooth on a neighborhood of a set is differentiable at each
point of the set. -/
theorem IsSmoothOnNeighborhood.differentiableAt
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {K : Set E}
    (hf : IsSmoothOnNeighborhood f K) {x : E} (hx : x ∈ K) :
    DifferentiableAt ℝ f x := by
  rcases hf with ⟨V, hVopen, hKV, hV⟩
  exact (hV.contDiffAt (hVopen.mem_nhds (hKV hx))).differentiableAt (by simp)

variable {d : ℕ}

/-- Reverse-time pullback preserves smoothness on corresponding neighborhoods. -/
theorem IsSmoothOnNeighborhood.reverseTime
     {S K : HypoellipticAleksandrov.Parabolic.Region d} (r₁ : ℝ)
    {f : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hSK : reverseTimeMap r₁ '' S ⊆ K)
    (hf : IsSmoothOnNeighborhood f K) :
    IsSmoothOnNeighborhood (f ∘ reverseTimeMap r₁) S := by
  rcases hf with ⟨V, hVopen, hKV, hV⟩
  refine ⟨reverseTimeMap r₁ ⁻¹' V,
    (contDiff_reverseTimeMap r₁).continuous.isOpen_preimage V hVopen, ?_, ?_⟩
  · intro z hz
    exact hKV (hSK ⟨z, hz, rfl⟩)
  · exact hV.comp
      ((contDiff_reverseTimeMap r₁).of_le (by exact_mod_cast le_top)).contDiffOn
      fun _ hz => hz

/-- Matrix-valued coefficient smoothness gives smoothness of each entry. -/
theorem IsSmoothOnNeighborhood.coefficientEntry
     {K : HypoellipticAleksandrov.Parabolic.Region d} (a : CoefficientField d)
    (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2) K)
    (i j : Fin d) :
    IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2 i j) K := by
  rcases ha with ⟨V, hVopen, hKV, hV⟩
  refine ⟨V, hVopen, hKV, ?_⟩

  exact (contDiffOn_apply ℝ ℝ j Set.univ).comp ((contDiffOn_apply ℝ (Fin d → ℝ) i Set.univ).comp hV fun _ _ => Set.mem_univ _) fun _ _ => Set.mem_univ _

/-- The spatial slice derivative is the full derivative applied to a purely
spatial tangent vector. -/
alias fderiv_spatialSlice_apply := _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.fderiv_scalarSpatialSlice_apply


/-- Smooth matrix and drift fields give a smooth divergence-form drift entry. -/
theorem IsSmoothOnNeighborhood.divergenceDriftEntry
     {K : HypoellipticAleksandrov.Parabolic.Region d}
    (a : CoefficientField d) (b : PDE.TimeVectorField d)
    (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2) K)
    (hb : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2) K)
    (j : Fin d) :
    IsSmoothOnNeighborhood
      (fun z  => scalarSpatialCoefficientDivergence a z j - b z.1 z.2 j) K := by
  rcases ha with ⟨Va, hVaopen, hKVa, hVa⟩
  rcases hb with ⟨Vb, hVbopen, hKVb, hVb⟩
  refine ⟨Va ∩ Vb, hVaopen.inter hVbopen, fun z hz => ⟨hKVa hz, hKVb hz⟩, ?_⟩
  have hentry (i : Fin d) : ContDiffOn ℝ PDE.smoothOrder
      (fun z : TimeVelocity d => a z.1 z.2 i j) Va := by
    exact (contDiffOn_apply ℝ ℝ j Set.univ).comp
      ((contDiffOn_apply ℝ (Fin d → ℝ) i Set.univ).comp hVa fun _ _ => Set.mem_univ _)
      fun _ _ => Set.mem_univ _
  have hdiv : ContDiffOn ℝ PDE.smoothOrder (fun z  =>
      scalarSpatialCoefficientDivergence a z j) Va := by

    refine (show ContDiffOn ℝ PDE.smoothOrder (fun z  =>
        ∑ i : Fin d,
          (fderiv ℝ (fun w : TimeVelocity d => a w.1 w.2 i j) z)
            (0, PDE.basisVec i)) Va by
        apply ContDiffOn.sum
        intro i _
        exact ((hentry i).fderiv_of_isOpen hVaopen (m := PDE.smoothOrder) (by simp)).clm_apply
          contDiffOn_const).congr ?_
    intro z hz
    rcases z with ⟨r, y⟩
    simp only [scalarSpatialCoefficientDivergence]
    apply Finset.sum_congr rfl
    intro i _
    exact fderiv_spatialSlice_apply a r y (PDE.basisVec i) i j
      (((hentry i).contDiffAt (hVaopen.mem_nhds hz)).differentiableAt (by simp))
  have hbentry  := (contDiffOn_apply ℝ ℝ j Set.univ).comp hVb fun _ _ => Set.mem_univ _
  exact (hdiv.mono Set.inter_subset_left).sub (hbentry.mono Set.inter_subset_right)

end HypoellipticAleksandrov.Parabolic.Dirichlet
