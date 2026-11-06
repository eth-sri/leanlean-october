module

public import GaloisCohomology.Topology.TotallyDisconnectedQuotients
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Tactic.Measurability

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/







set_option autoImplicit false

/-!
# Connected-component quotients under topological group equivalences

A topological group equivalence carries the connected component of one
onto the connected component of one. It therefore induces an equivalence
of the corresponding quotient topological groups.
-/

noncomputable section

namespace ClassFieldTheory

universe u v

variable {G : Type u} {H : Type v}
  [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]

/-- A topological group equivalence maps the identity component exactly
onto the identity component. -/
theorem connectedComponentOfOne_map_equiv (e : G ≃ₜ* H) :
    (Subgroup.connectedComponentOfOne G).map e.toMulEquiv.toMonoidHom =
      Subgroup.connectedComponentOfOne H := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change e x ∈ connectedComponent (1 : H)
    have h := e.continuous.mapsTo_connectedComponent (1 : G) hx
    measurability
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    change e.symm y ∈ connectedComponent (1 : G)
    have h := e.symm.continuous.mapsTo_connectedComponent (1 : H) hy
    measurability

/-- An equivalence of topological groups descends to a
topological group equivalence modulo the identity components. -/
noncomputable def connectedComponentQuotientCongr (e : G ≃ₜ* H) :
    (G ⧸ Subgroup.connectedComponentOfOne G) ≃ₜ*
      (H ⧸ Subgroup.connectedComponentOfOne H) := by
  let G₀ := Subgroup.connectedComponentOfOne G
  let H₀ := Subgroup.connectedComponentOfOne H
  have he : G₀.map e.toMulEquiv.toMonoidHom = H₀ :=
    connectedComponentOfOne_map_equiv e
  let eQ : G ⧸ G₀ ≃* H ⧸ H₀ :=
    QuotientGroup.congr G₀ H₀ e.toMulEquiv he
  have hcont : Continuous eQ := by
    apply (QuotientGroup.isQuotientMap_mk G₀).continuous_iff.mpr
    have hcomp : Continuous (fun g : G => QuotientGroup.mk' H₀ (e g)) :=
      QuotientGroup.continuous_mk.comp e.continuous
    measurability
  have hinv : Continuous eQ.symm := by
    apply (QuotientGroup.isQuotientMap_mk H₀).continuous_iff.mpr
    have hcomp : Continuous (fun h : H => QuotientGroup.mk' G₀ (e.symm h)) :=
      QuotientGroup.continuous_mk.comp e.symm.continuous
    measurability
  exact
    { toMulEquiv := eQ
      continuous_toFun := hcont
      continuous_invFun := hinv }

/-- On representatives, the quotient equivalence applies the original map. -/
@[simp]
theorem connectedComponentQuotientCongr_mk
    (e : G ≃ₜ* H) (g : G) :
    connectedComponentQuotientCongr e
        (QuotientGroup.mk' (Subgroup.connectedComponentOfOne G) g) =
      QuotientGroup.mk' (Subgroup.connectedComponentOfOne H) (e g) :=
  QuotientGroup.congr_mk' _ _ _ (connectedComponentOfOne_map_equiv e) g

end ClassFieldTheory

end
