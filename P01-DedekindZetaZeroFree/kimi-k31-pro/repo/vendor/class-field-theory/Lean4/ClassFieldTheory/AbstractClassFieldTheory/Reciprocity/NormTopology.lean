module

public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Topology.Algebra.FilterBasis
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension
public import GaloisCohomology.Cyclic.IntegralRepUniverse
public import ValuedFieldTheory.Valuation.Topology.Models

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/








set_option autoImplicit false

/-!
# Abstract reciprocity: the norm topology

The neighbourhood basis at zero consists literally of the norm subgroups
`N_{L/K} A_L` as `L / K` ranges over finite Galois extensions.  Composita
make this family downward directed.
-/

noncomputable section

namespace ClassFormation

open CyclicCohomology KummerTheory

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- The actual norm subgroup belonging to a packaged finite Galois
extension. -/
def normSubgroup (A : Rep ℤ G) (L : FiniteGaloisSubextension K) :
    AddSubgroup (ambientFixedAddSubgroup A K) := by
  letI := L.finite
  exact finiteNormSubgroup A K L.field L.below

/-- Proves the bound `normSubgroup A (L₁.compositum L₂) ≤ normSubgroup A L₁`. -/
theorem normSubgroup_compositum_le_left
    (A : Rep ℤ G) (L₁ L₂ : FiniteGaloisSubextension K) :
    normSubgroup A (L₁.compositum L₂) ≤ normSubgroup A L₁ := by
  simpa [normSubgroup] using
    ClassFormation.FiniteGaloisSubextension.finiteNormSubgroup_compositum_le_left A L₁ L₂

/-- Proves the bound `normSubgroup A (L₁.compositum L₂) ≤ normSubgroup A L₂`. -/
theorem normSubgroup_compositum_le_right
    (A : Rep ℤ G) (L₁ L₂ : FiniteGaloisSubextension K) :
    normSubgroup A (L₁.compositum L₂) ≤ normSubgroup A L₂ := by
  simpa [normSubgroup] using
    ClassFormation.FiniteGaloisSubextension.finiteNormSubgroup_compositum_le_right A L₁ L₂

end FiniteGaloisSubextension

open FiniteGaloisSubextension

/-- The additive-group filter basis formed by all finite Galois norm
subgroups. -/
@[implicit_reducible]
def normFilterBasis (A : Rep ℤ G) (K : ClosedSubgroup G) :
    AddGroupFilterBasis (ambientFixedAddSubgroup A K) :=
  addGroupFilterBasisOfComm
    {U | ∃ L : FiniteGaloisSubextension K,
      U = (normSubgroup A L : Set (ambientFixedAddSubgroup A K))}
    (by
      refine ⟨(normSubgroup A (FiniteGaloisSubextension.refl K) :
        Set (ambientFixedAddSubgroup A K)), ?_⟩
      exact ⟨FiniteGaloisSubextension.refl K, rfl⟩)
    (by
      rintro U V ⟨L₁, rfl⟩ ⟨L₂, rfl⟩
      refine ⟨(normSubgroup A (L₁.compositum L₂) :
        Set (ambientFixedAddSubgroup A K)),
        ⟨L₁.compositum L₂, rfl⟩, ?_⟩
      intro x hx
      exact ⟨normSubgroup_compositum_le_left A L₁ L₂ hx,
        normSubgroup_compositum_le_right A L₁ L₂ hx⟩)
    (by
      rintro _ ⟨L, rfl⟩
      exact (normSubgroup A L).zero_mem)
    (by
      rintro _ ⟨L, rfl⟩
      refine ⟨(normSubgroup A L : Set (ambientFixedAddSubgroup A K)),
        ⟨L, rfl⟩, ?_⟩
      rintro x ⟨a, ha, b, hb, rfl⟩
      exact (normSubgroup A L).add_mem ha hb)
    (by
      rintro _ ⟨L, rfl⟩
      refine ⟨(normSubgroup A L : Set (ambientFixedAddSubgroup A K)),
        ⟨L, rfl⟩, ?_⟩
      intro x hx
      exact (normSubgroup A L).neg_mem hx)

/-- The norm topology: norm subgroups form a basis at zero. -/
@[implicit_reducible]
def normTopology (A : Rep ℤ G) (K : ClosedSubgroup G) :
    TopologicalSpace (ambientFixedAddSubgroup A K) :=
  (normFilterBasis A K).topology

/-- The fixed subgroup with its norm topology recorded in the type.  This is
the public carrier model for norm-topological statements; choosing the norm
topology no longer mutates the topology instance of the underlying group. -/
def WithNormTopology (A : Rep ℤ G) (K : ClosedSubgroup G) : Type _ :=
  WithTopology
    (ambientFixedAddSubgroup A K) (normTopology A K)

/-- Installs the norm topology on the `WithNormTopology` carrier. -/
instance withNormTopology.instTopologicalSpace
    (A : Rep ℤ G) (K : ClosedSubgroup G) :
    TopologicalSpace (WithNormTopology A K) := by
  unfold WithNormTopology
  infer_instance

/--
Transports the additive commutative group structure to the `WithNormTopology` carrier.
-/
instance withNormTopology.instAddCommGroup
    (A : Rep ℤ G) (K : ClosedSubgroup G) :
    AddCommGroup (WithNormTopology A K) := by
  unfold WithNormTopology
  exact
    (WithTopology.equiv
      (ambientFixedAddSubgroup A K) (normTopology A K)).addCommGroup



/-- Openness in the norm topology, expressed through the type-level norm
topology model. -/
def IsNormOpen (A : Rep ℤ G) (K : ClosedSubgroup G)
    (s : Set (ambientFixedAddSubgroup A K)) : Prop :=
  @IsOpen (ambientFixedAddSubgroup A K) (normTopology A K) s









private theorem isNormOpen_iff_raw
    (A : Rep ℤ G) (K : ClosedSubgroup G)
    (s : Set (ambientFixedAddSubgroup A K)) :
    IsNormOpen A K s ↔
      @IsOpen (ambientFixedAddSubgroup A K) (normTopology A K) s := by
  rfl



 

/-- A set belongs to the defining filter basis exactly when it is one of
the finite Galois norm subgroups. -/
@[simp]
theorem mem_normFilterBasis_iff
    (A : Rep ℤ G) (K : ClosedSubgroup G)
    (U : Set (ambientFixedAddSubgroup A K)) :
    U ∈ normFilterBasis A K ↔
      ∃ L : FiniteGaloisSubextension K,
        U = (normSubgroup A L : Set (ambientFixedAddSubgroup A K)) :=
  Iff.rfl

/-- A subgroup is open in the norm topology exactly when it contains one
finite Galois norm subgroup. -/
theorem normTopology_addSubgroup_isOpen_iff
    (A : Rep ℤ G) (K : ClosedSubgroup G)
    (H : AddSubgroup (ambientFixedAddSubgroup A K)) :
    IsNormOpen A K H ↔
      ∃ L : FiniteGaloisSubextension K, normSubgroup A L ≤ H := by
  rw [isNormOpen_iff_raw]
  let : TopologicalSpace (ambientFixedAddSubgroup A K) := normTopology A K
  let : IsTopologicalAddGroup (ambientFixedAddSubgroup A K) :=
    (normFilterBasis A K).isTopologicalAddGroup
  constructor
  · intro hH
    have hnh : (H : Set (ambientFixedAddSubgroup A K)) ∈ nhds 0 :=
      hH.mem_nhds H.zero_mem
    rcases (normFilterBasis A K).nhds_zero_hasBasis.mem_iff.mp hnh with
      ⟨U, hU, hUH⟩
    rcases hU with ⟨L, rfl⟩
    exact ⟨L, hUH⟩
  · rintro ⟨L, hLH⟩
    apply H.isOpen_of_mem_nhds
    exact Filter.mem_of_superset
      ((normFilterBasis A K).mem_nhds_zero ⟨L, rfl⟩) hLH

/-- Every defining norm subgroup is open. -/
theorem normSubgroup_isOpen
    (A : Rep ℤ G) (K : ClosedSubgroup G)
    (L : FiniteGaloisSubextension K) :
    IsNormOpen A K (normSubgroup A L) := by
  rw [normTopology_addSubgroup_isOpen_iff]
  exact ⟨L, le_rfl⟩

/-- The subgroup of universal norms used in Hausdorffness of the norm topology. -/
def universalNormSubgroup (A : Rep ℤ G) (K : ClosedSubgroup G) :
    AddSubgroup (ambientFixedAddSubgroup A K) :=
  ⨅ L : FiniteGaloisSubextension K, normSubgroup A L

/--
Characterizes `a ∈ universalNormSubgroup A K` by the equivalent condition `∀ L :
FiniteGaloisSubextension K, a ∈ normSubgroup A L`.
-/
@[simp]
theorem mem_universalNormSubgroup_iff
    (A : Rep ℤ G) (K : ClosedSubgroup G)
    (a : ambientFixedAddSubgroup A K) :
    a ∈ universalNormSubgroup A K ↔
      ∀ L : FiniteGaloisSubextension K, a ∈ normSubgroup A L := by
  simp [universalNormSubgroup]







end ClassFormation

end
