module

public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Mathlib.Topology.Algebra.Group.Quotient

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Totally disconnected quotient groups

This file proves that a closed normal quotient of a compact Hausdorff totally
disconnected topological group is totally disconnected.
-/

namespace QuotientGroup

/-- A closed normal quotient of a compact Hausdorff totally disconnected
topological group is totally disconnected. -/
theorem totallyDisconnectedSpace_of_isClosed
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  let q := QuotientGroup.mk' N
  have hsep : Pairwise (fun a b : G ⧸ N =>
      ∃ U : Set (G ⧸ N), IsClopen U ∧ a ∈ U ∧ b ∈ Uᶜ) := by
    intro a b hab
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N b
    let g := x⁻¹ * y
    have hgN : g ∉ N := by
      intro hgN
      apply hab
      apply inv_mul_eq_one.mp
      exact (QuotientGroup.eq_one_iff g).2 hgN
    let W := {u | g * u⁻¹ ∉ N}
    have hWopen : IsOpen W := by
      exact hN.isOpen_compl.preimage (continuous_const.mul continuous_inv)
    have hWone : (1 : G) ∈ W := by
      simpa only [W, Set.mem_ofPred_eq, inv_one, mul_one] using hgN
    obtain ⟨V, hVW⟩ :=
      ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
        (G := G) hWopen hWone
    let K := N ⊔ V
    have hKopen :=
      Subgroup.isOpen_of_openSubgroup K
        (show V ≤ K from le_sup_right)
    have hNK : N ≤ K := le_sup_left
    have hgK : g ∉ K := by
      intro hgK
      rcases (Subgroup.mem_sup_of_normal_right
           ).1 hgK with
        ⟨n, hnN, v, hvV, hnv⟩
      have hgn : g * v⁻¹ = n := by
        calc
          _ = (n * v) * v⁻¹ := by rw [hnv]
          _ = n := by simp
      apply hVW hvV
      simpa only [hgn] using hnN
    let Kbar : Subgroup (G ⧸ N) := K.map q
    have hKbarOpen : IsOpen (Kbar : Set (G ⧸ N)) := by
      change IsOpen (((↑) : G → G ⧸ N) '' K)
      exact QuotientGroup.isOpenMap_coe (K : Set G) hKopen
    have hqgKbar : q g ∉ Kbar := by
      intro hqgKbar
      have hgComap : g ∈ Kbar.comap q := hqgKbar
      have hker : q.ker ≤ K := by
        simpa only [q, QuotientGroup.ker_mk'] using hNK
      have hcomap : Kbar.comap q = K := by
        simpa only [Kbar] using Subgroup.comap_map_eq_self hker
      rw [hcomap] at hgComap
      exact hgK hgComap
    let U := {z | (q x)⁻¹ * z ∈ Kbar}
    have hUclopen : IsClopen U := by
      have hcont :=
        (continuous_const :
          Continuous (fun _ : G ⧸ N => (q x)⁻¹)).mul continuous_id
      exact
        ⟨(Subgroup.isClosed_of_isOpen Kbar hKbarOpen).preimage hcont,
          hKbarOpen.preimage hcont⟩
    refine ⟨U, hUclopen, ?_, ?_⟩
    · change (q x)⁻¹ * q x ∈ Kbar
      simp
    · assumption
  let :=
    totallySeparatedSpace_iff_exists_isClopen.2 hsep
  infer_instance

end QuotientGroup

namespace QuotientGroup

/-- The identity component of a topological group is a normal subgroup. -/
instance Subgroup.Normal.connectedComponentOfOne
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    (Subgroup.connectedComponentOfOne G).Normal where
  conj_mem x hx g := by
    change g * x * g⁻¹ ∈ connectedComponent (1 : G)
    simpa only [mul_one, mul_inv_cancel] using
      (IsTopologicalGroup.continuous_conj g).mapsTo_connectedComponent
        (1 : G) hx

/-- Quotienting a topological group by its identity component produces a
totally disconnected topological group. -/
theorem totallyDisconnectedSpace_quotient_connectedComponentOfOne
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    TotallyDisconnectedSpace
      (G ⧸ Subgroup.connectedComponentOfOne G) := by
  let N := Subgroup.connectedComponentOfOne G
  let q := QuotientGroup.mk' N
  have hfibers : ∀ y : G ⧸ N, IsConnected (q ⁻¹' {y}) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
    have hfiber :
        q ⁻¹' {q g} =
          (fun x : G ↦ x * g) '' connectedComponent (1 : G) := by
      ext x
      constructor
      · intro hx
        exact ⟨x / g, (QuotientGroup.eq_iff_div_mem.mp hx), div_mul_cancel x g⟩
      · rintro ⟨n, hn, rfl⟩
        change q (n * g) = q g
        rw [map_mul]
        have hqn : q n = 1 := by
          exact (QuotientGroup.eq_one_iff n).2 hn
        rw [hqn, one_mul]
    rw [hfiber]
    exact
      isConnected_connectedComponent.image _
        (continuous_id.mul continuous_const).continuousOn
  apply totallyDisconnectedSpace_iff_connectedComponent_one.mpr
  apply (QuotientGroup.mk'_surjective N).preimage_injective
  calc
    _ =
        connectedComponent (1 : G) := by
      exact Topology.IsCoinducing.preimage_connectedComponent (isQuotientMap_mk N).isCoinducing hfibers 1
    _ = N := rfl
    _ = QuotientGroup.mk ⁻¹' {1} := by
      ext x
      exact (QuotientGroup.eq_one_iff x).symm

end QuotientGroup

namespace ContinuousMonoidHom

/-- A continuous homomorphism from a topological group to a totally disconnected
topological group vanishes on the identity component. -/
theorem connectedComponentOfOne_le_ker
    {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TotallyDisconnectedSpace H]
    (f : G →ₜ* H) :
    Subgroup.connectedComponentOfOne G ≤ f.ker := by
  intro g hg
  have hfg : f g ∈ connectedComponent (1 : H) := by
    simpa using (f.continuous_toFun.mapsTo_connectedComponent (1 : G) hg)
  simpa using hfg

end ContinuousMonoidHom
