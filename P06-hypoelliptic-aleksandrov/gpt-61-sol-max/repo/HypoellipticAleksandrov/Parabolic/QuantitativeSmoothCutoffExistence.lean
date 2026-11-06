module

public import PDEFoundation.Sobolev.Cutoff.Basic
public import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Tactic.Bound



/-!
# Quantitative smooth cutoffs on open velocity sets

This module turns the smooth plateau construction into the project-specific
quantitative cutoff data required for velocity localization.
-/

 public section

namespace HypoellipticAleksandrov.Parabolic

open scoped Manifold

/-- A compact subset of an open velocity set admits a quantitative smooth
cutoff with topological support in that open set. -/
theorem exists_quantitativeSmoothCutoff_tsupport_subset
    {d : ℕ} {E Ω : PDE.VelocityRegion d}
    (hE : IsCompact E) (hΩ : IsOpen Ω) (hEΩ : E ⊆ Ω) :
    ∃ K : ℝ, Nonempty (PDE.QuantitativeSmoothCutoff E Ω K) := by
  obtain ⟨V, hVopen, hEV, hclosureVΩ, hclosureVcompact⟩ :=
    exists_open_between_and_isCompact_closure hE hΩ hEΩ
  obtain ⟨f, hfSmooth, hfRange, hfSupport, hfOne⟩ :=
    exists_contMDiff_support_eq_eq_one_iff (n := ⊤) (𝓘(ℝ, PDE.Vec d)) hVopen hE.isClosed hEV
  have hfCompact : HasCompactSupport f := by
    change IsCompact (closure (Function.support f))
    rw [hfSupport]
    exact hclosureVcompact


  obtain ⟨C, hC⟩ :=
    (PDE.ContDiff.continuous_classicalGradient (hfSmooth.contDiff.of_le (by simp))).bounded_above_of_compact_support (by
        change HasCompactSupport
          (fun x i => (fderiv ℝ f x) (PDE.basisVec i))
        exact
          (hfCompact.fderiv (𝕜 := ℝ)).comp_left
            (g := fun L : PDE.Vec d →L[ℝ] ℝ => fun i => L (PDE.basisVec i)) (rfl))
  refine ⟨Real.sqrt d * C, ⟨?_⟩⟩
  refine
    { toFun := f
      smooth := hfSmooth.contDiff
      hasCompactSupport := hfCompact
      tsupport_subset := ?_
      nonneg := ?_
      le_one := ?_
      eq_one_on_inner := ?_
      gradient_bound := ?_ }
  · bound
  · intro x
    exact (hfRange ⟨x, rfl⟩).1
  · intro x
    exact (hfRange ⟨x, rfl⟩).2
  · intro x hx
    exact (hfOne x).mp hx
  · intro x
    calc
      PDE.vecEuclideanNorm (PDE.classicalGradient f x) ≤
          Real.sqrt d * ‖PDE.classicalGradient f x‖ :=
        PDE.vecEuclideanNorm_le_sqrt_natCast_mul_norm _
      _ ≤ Real.sqrt d * C :=
        mul_le_mul_of_nonneg_left (hC x) (Real.sqrt_nonneg _)

end HypoellipticAleksandrov.Parabolic
