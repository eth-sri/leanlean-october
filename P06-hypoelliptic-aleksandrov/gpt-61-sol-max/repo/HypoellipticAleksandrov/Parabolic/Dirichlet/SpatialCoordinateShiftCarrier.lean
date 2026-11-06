module

public import PDEFoundation.Ambient.Basis
public import PDEFoundation.Measure.AffineVolume

/-!
# Spatial coordinate-shift carriers

This module defines the finite union of signed coordinate shifts of a compact
spatial carrier and records its elementary membership and compactness API.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open Set

variable {d : ℕ}

/-- The finite coordinate-shift carrier of `K` at signed radius `ρ`. -/
def spatialCoordinateShiftCarrier
    (K : PDE.VelocityRegion d) (ρ : ℝ) : PDE.VelocityRegion d :=
  ⋃ k : Fin d,
    (fun ys : PDE.Vec d × ℝ => ys.1 + ys.2 • PDE.basisVec k) ''
      (K ×ˢ Set.Icc (-ρ) ρ)

variable {K : PDE.VelocityRegion d}

/-- Membership in the coordinate-shift carrier is witnessed by one coordinate
and one signed shift of the original carrier. -/
theorem mem_spatialCoordinateShiftCarrier_iff
      {ρ : ℝ} {x : PDE.Vec d} :
    x ∈ spatialCoordinateShiftCarrier K ρ ↔
      ∃ (y : PDE.Vec d) (k : Fin d) (s : ℝ),
        y ∈ K ∧ |s| ≤ ρ ∧ x = y + s • PDE.basisVec k := by
  unfold spatialCoordinateShiftCarrier
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨k, hx⟩
    rcases hx with ⟨ys, hys, hxy⟩
    rcases hys with ⟨hy, hs⟩
    exact ⟨ys.1, k, ys.2, hy, abs_le.mpr hs, hxy.symm⟩
  · rintro ⟨y, k, s, hy, hs, rfl⟩
    apply Set.mem_iUnion.mpr
    refine ⟨k, (y, s), ⟨hy, abs_le.mp hs⟩, rfl⟩

/-- A point of `K` shifted by an admissible signed amount in one coordinate
belongs to its coordinate-shift carrier. -/
theorem mem_spatialCoordinateShiftCarrier_of_mem_of_abs_le
      {ρ s : ℝ}
    {y : PDE.Vec d} {k : Fin d}
    (hy : y ∈ K) (hs : |s| ≤ ρ) :
    y + s • PDE.basisVec k ∈ spatialCoordinateShiftCarrier K ρ :=
  mem_spatialCoordinateShiftCarrier_iff.mpr ⟨y, k, s, hy, hs, rfl⟩

/-- A coordinate-shift carrier of a compact spatial set is compact. -/
theorem IsCompact.spatialCoordinateShiftCarrier

    (hK : IsCompact K) (ρ : ℝ) :
    IsCompact (spatialCoordinateShiftCarrier K ρ) := (id
  (isCompact_iUnion fun k =>
    IsCompact.image (IsCompact.prod hK isCompact_Icc)
      (Continuous.add continuous_fst (Continuous.smul continuous_snd continuous_const))))

end HypoellipticAleksandrov.Parabolic.Dirichlet
