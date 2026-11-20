module

public import PDEFoundation.Geometry.Affine
public import PDEFoundation.Geometry.Domain
public import PDEFoundation.Geometry.EuclideanBall
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Bounded open convex domains

The shared domain class for mean-zero Poincaré and Sobolev--Poincaré
estimates. It contains explicit round balls and axis-aligned cubes.
-/

@[expose] public section

open scoped Pointwise

namespace PDE

section
variable {d : ℕ} {U : Set (Vec d)}

theorem Bornology.IsBounded.isBoundedDomain (hU : Bornology.IsBounded U) :
    IsBoundedDomain U := by
  classical
  by_cases hd : d = 0
  · refine ⟨1, zero_lt_one, ?_⟩
    subst hd
    intro x hx i
    exact Fin.elim0 i
  · have : NeZero d := ⟨hd⟩
    have hcoordBound :
        ∀ i : Fin d, ∃ R : ℝ, 0 < R ∧
          ∀ y ∈ Function.eval i '' U, ‖y‖ ≤ R := by
      intro i
      rcases isBounded_iff_forall_norm_le.1 ((fun i => hU.image_eval i) i) with
        ⟨R, hR⟩
      refine
        ⟨max R 1, zero_lt_one.trans_le (le_max_right _ _), ?_⟩
      grind
    choose R hRpos hR using hcoordBound
    let Rmax : ℝ := Finset.univ.sup' Finset.univ_nonempty R
    have hRmaxPos : 0 < Rmax := by
      let i₀ : Fin d := 0
      have hi₀ : i₀ ∈ Finset.univ := by
        simp
      exact lt_of_lt_of_le (hRpos i₀) (Finset.le_sup' (s := Finset.univ) (f := R) hi₀)
    refine ⟨Rmax, hRmaxPos, ?_⟩
    intro x hx i
    simpa [Real.norm_eq_abs] using! (hR i (x i) ⟨x, hx, rfl⟩).trans (Finset.le_sup' (s := Finset.univ) (f := R) (Finset.mem_univ i))

theorem IsBoundedDomain.isBounded (hU : IsBoundedDomain U) :
    Bornology.IsBounded U := by
  rcases hU with ⟨R, hRpos, hR⟩
  refine isBounded_iff_forall_norm_le.2 ⟨R, ?_⟩
  intro x hx
  refine (pi_norm_le_iff_of_nonneg hRpos.le).2 ?_
  intro i
  exact hR x hx i

end

end PDE
