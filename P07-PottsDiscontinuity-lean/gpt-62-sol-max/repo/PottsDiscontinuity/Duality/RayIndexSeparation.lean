module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.RayIndex
public import PottsDiscontinuity.FK.BoxExhaustion

/-! Finiteness of the nonzero-index region and the jump across a simple circuit. -/

@[expose] public section

namespace PottsDiscontinuity.Duality
open FK FK.Medial Filter
noncomputable section

section

variable
  (v : LatticeVertex) {u w : LatticeVertex}
    (p : squareLattice.Walk u w)

/-- If all vertical edges have the same ray mask, the intersection sum telescopes. -/
lemma rayIndex_eq_scaled_heightDiff (k : ℤ)
    (hmask : ∀ d : squareLattice.Dart, d ∈ p.darts → ¬ (d.fst.2 < v.2 ↔ d.snd.2 < v.2) →
      (if v.1 ≤ d.fst.1 then (1 : ℤ) else 0) = k) :
    rayIndex v p = ((if u.2 < v.2 then 1 else 0) - (if w.2 < v.2 then 1 else 0)) * k := by
  induction p with
  | nil => aesop
  | @cons u z w hz p ih =>
    have hh : rayStep v u z = ((if u.2 < v.2 then 1 else 0) - (if z.2 < v.2 then 1 else 0)) * k := by
      by_cases he : u.2 < v.2 ↔ z.2 < v.2
      · simp [rayStep, he]
      · have := hmask ⟨⟨u,z⟩,hz⟩ (by simp) he
        simp [rayStep, this]
    rw [rayIndex, hh, ih (by intro d hd; exact hmask d (by simp [hd]))]
    ring

end

end
end PottsDiscontinuity.Duality
