module

public import PDEFoundation.Geometry.ConvexDomain

/-!
# Axis-aligned cubes

Open coordinate cubes as instances of the bounded open convex domain API.
-/

@[expose] public section

namespace PDE

/-- The open axis cube `z + (0,L)^d`, parametrized by a corner and side. -/
def axisCube {d : ℕ} (z : Vec d) (L : ℝ) : Set (Vec d) :=
  Set.pi Set.univ fun i => Set.Ioo (z i) (z i + L)

/-- The coordinate center of an axis cube. -/
noncomputable def axisCubeCenter {d : ℕ} (z : Vec d) (L : ℝ) : Vec d :=
  fun i => z i + L / 2

variable {d : ℕ} (z : Vec d) (L : ℝ)

@[simp]
theorem axisCubeCenter_apply  (i : Fin d) :
    axisCubeCenter z L i = z i + L / 2 :=
  rfl

theorem axisCube_nonempty  {L : ℝ}
    (hL : 0 < L) :
    (axisCube z L).Nonempty := by
  refine ⟨axisCubeCenter z L, ?_⟩
  intro i _hi
  simp_all

theorem isOpen_axisCube  :
    IsOpen (axisCube z L) := isOpen_set_pi Set.finite_univ fun _i _hi => isOpen_Ioo

theorem isBoundedDomain_axisCube  :
    IsBoundedDomain (axisCube z L) := Bornology.IsBounded.isBoundedDomain <|
    Bornology.IsBounded.pi fun _i => Metric.isBounded_Ioo _ _

theorem convex_axisCube  :
    Convex ℝ (axisCube z L) := by
  refine convex_pi ?_
  intro _i _hi
  exact convex_Ioo _ _

theorem isOpenBoundedConvexDomain_axisCube  :
    IsOpenBoundedConvexDomain (axisCube z L) :=
  ⟨isOpen_axisCube z L, isBoundedDomain_axisCube z L,
    convex_axisCube z L⟩

theorem hasEuclideanDiameterLE_axisCube  {L : ℝ} (hL : 0 ≤ L) :
    HasEuclideanDiameterLE (axisCube z L)
      (Real.sqrt d * L) := by
  intro x hx y hy
  have hsup : ‖x - y‖ ≤ L := by
    rw [pi_norm_le_iff_of_nonneg hL]
    intro i
    have hxi := hx i (Set.mem_univ i)
    have hyi := hy i (Set.mem_univ i)
    simpa [Real.norm_eq_abs] using
      (abs_le.2 ⟨by grind,
        by grind⟩)
  exact
    (vecEuclideanNorm_le_sqrt_natCast_mul_norm _).trans
      (mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg d))

end PDE
