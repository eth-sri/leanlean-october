/- Consequences of native unital generation.
No generation/span premise. -/
module
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.GRewrite
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr
public import Aesop
public import Glennie.NativeGenerationEndpointR01
public import Glennie.Compact.InnerDerivation
public import Glennie.Compact.LocalReconstruction

@[expose] public section
namespace Glennie.NativeGenerationStabilizersR01
noncomputable section
open Glennie.NativeGenerationEndpointR01
open Glennie.Compact
open Glennie.Compact.Affine20
open Glennie.Compact.Sections

/-- Actual native automorphisms are determined by their linear equivalence. -/
theorem automorphism_ext {g h : CompactAutomorphism} (he : g.equiv = h.equiv) : g = h := by
  cases g
  cases h
  cases he
  rfl

def fixedSubmodule (g : CompactAutomorphism) : Submodule ℝ Albert where
  carrier := {t | g.equiv t = t}
  zero_mem' := by simp
  add_mem' := by simp_all
  smul_mem' := by
    intro r p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    rw [map_smul, hp]

theorem automorphism_fixes_all_of_phi_ne_zero
    (g : CompactAutomorphism) (x y z : Albert)
    (hphi : phi x y z ≠ 0)
    (hx : g.equiv x = x) (hy : g.equiv y = y) (hz : g.equiv z = z) :
    ∀ t : Albert, g.equiv t = t := by
  have hK                        := eq_top_of_phi_ne_zero (fixedSubmodule g)
    g.map_unit
    (by
      intro p hp q hq
      change g.equiv p = p at hp
      change g.equiv q = q at hq
      change g.equiv (jordan p q) = jordan p q
      rw [g.map_jordan, hp, hq])
    x y z hx hy hz hphi
  intro t
  have ht : t ∈ fixedSubmodule g := by rw [hK]; trivial
  exact ht

theorem automorphism_eq_refl_of_phi_ne_zero
    (g : CompactAutomorphism) (x y z : Albert)
    (hphi : phi x y z ≠ 0)
    (hx : g.equiv x = x) (hy : g.equiv y = y) (hz : g.equiv z = z) :
    g = CompactAutomorphism.refl := by
  apply automorphism_ext
  apply LinearEquiv.ext
  exact automorphism_fixes_all_of_phi_ne_zero g x y z hphi hx hy hz

/-- No trace-free condition is needed for this derivation consequence. -/
theorem derivation_eq_zero_of_phi_ne_zero
    (D : Albert →ₗ[ℝ] Albert) (hD : IsJordanDerivation D)
    (x y z : Albert) (hphi : phi x y z ≠ 0)
    (hx : D x = 0) (hy : D y = 0) (hz : D z = 0) : D = 0 := by
  have hK                       := eq_top_of_phi_ne_zero (LinearMap.ker D)
    hD.map_one
    (by
      intro p hp q hq
      change D p = 0 at hp
      change D q = 0 at hq
      change D (jordan p q) = 0
      rw [hD p q, hp, hq]
      simp)
    x y z hx hy hz hphi
  apply LinearMap.ext
  intro t
  have ht : t ∈ LinearMap.ker D := by rw [hK]; trivial
  exact ht

end
end Glennie.NativeGenerationStabilizersR01
