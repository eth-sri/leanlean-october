/- Native unital generation endpoint.
The preceding coordinate stages supply generation directly.
No classification, stronger real-slot normal form, or conclusion axiom. -/
module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.NormNum
public import Aesop
public import Glennie.NativeGenerationHiddenCompletionR01
public import Glennie.UnitShifts

@[expose] public section
namespace Glennie.NativeGenerationEndpointR01
section
open Glennie.NativeGenerationComplexSectorR01
open Glennie.NativeGenerationHiddenCompletionR01

variable (K : Submodule ℝ Albert) (h1 : (1 : Albert) ∈ K)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (x y z : Albert) (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K)

include K h1 hJ x y z hx hy hz in
/-- Definition-free full unital generation: every native product-closed real
submodule containing the unit and a nonzero-Phi triple is the entire Albert space. -/
theorem eq_top_of_phi_ne_zero

    (hphi : phi x y z ≠ 0) : K = ⊤ := by
  obtain ⟨g, hxd, hyc⟩ := universal_pair_reduction x y
  let L : Submodule ℝ Albert := K.map g.equiv.toLinearMap
  have hL1 : (1 : Albert) ∈ L := ⟨1, h1, g.map_unit⟩
  have hLJ : ∀ p ∈ L, ∀ q ∈ L, jordan p q ∈ L := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    exact ⟨jordan p q, hJ p hp q hq, g.map_jordan p q⟩
  have hn : phi (g.equiv x) (g.equiv y) (g.equiv z) ≠ 0 := by
    rwa [g.phi_map]
  rw [phi_of_diagonal_complex _ _ _ hxd hyc] at hn
  simp only [ne_eq, mul_eq_zero, not_or] at hn
  have hC := complexSector_le_of_regular_triangle L hL1 hLJ
    _ _ _ _ _ _ _ _ _
    (by rw [diagonalAlbert_eq (g.equiv x) hxd]; exact ⟨x, hx, rfl⟩)
    (by rw [complexAlbert_eq (g.equiv y) hyc]; exact ⟨y, hy, rfl⟩)
    hn.1.1.1.1.2 hn.1.1.1.2 hn.1.1.2 hn.1.2
  have hL := eq_top_of_complexSector_le_hidden_det L hLJ hC (g.equiv z)
    ⟨z, hz, rfl⟩ (fun h => hn.2 (by simp [h]))
  all_goals aesop

end
end Glennie.NativeGenerationEndpointR01
