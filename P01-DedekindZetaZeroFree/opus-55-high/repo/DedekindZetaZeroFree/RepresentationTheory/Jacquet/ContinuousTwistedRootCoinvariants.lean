module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.ContinuousWhittakerFunctionals

@[expose] public section

noncomputable section

open Topology

namespace DedekindZetaZeroFree

section Algebraic

variable {G N V W X E : Type*} [Group G] [Group N]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X] [AddCommGroup E] [Module ℂ E]

def rootTwistedRepresentation (ρ : Representation ℂ G V) (n : N →* G)
    (ψ : N →* ℂˣ) : Representation ℂ N V where
  toFun t := (↑(ψ t)⁻¹ : ℂ) • ρ (n t)
  map_one' := by simp
  map_mul' t u := by ext v; simp [map_mul, mul_smul]

@[simp] theorem rootTwistedRepresentation_apply (ρ : Representation ℂ G V)
    (n : N →* G) (ψ : N →* ℂˣ) (t : N) (v : V) :
    rootTwistedRepresentation ρ n ψ t v = (↑(ψ t)⁻¹ : ℂ) • ρ (n t) v := rfl

abbrev RootCoinvariants (ρ : Representation ℂ G V) (n : N →* G)
    (ψ : N →* ℂˣ) := Representation.Coinvariants (rootTwistedRepresentation ρ n ψ)

def rootRelationSpan (ρ : Representation ℂ G V) (n : N →* G) (ψ : N →* ℂˣ) :
    Submodule ℂ V :=
  Submodule.span ℂ (Set.range fun tv : N × V =>
    ρ (n tv.1) tv.2 - (ψ tv.1 : ℂ) • tv.2)

theorem rootTwistedRepresentation_ker (ρ : Representation ℂ G V)
    (n : N →* G) (ψ : N →* ℂˣ) :
    Representation.Coinvariants.ker (rootTwistedRepresentation ρ n ψ) =
      rootRelationSpan ρ n ψ := by
  rw [Representation.Coinvariants.ker, rootRelationSpan]
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro x ⟨tv, rfl⟩
    show (↑(ψ tv.1)⁻¹ : ℂ) • ρ (n tv.1) tv.2 - tv.2 ∈
      Submodule.span ℂ (Set.range fun tv : N × V =>
        ρ (n tv.1) tv.2 - (ψ tv.1 : ℂ) • tv.2)
    have h1 : (↑(ψ tv.1)⁻¹ : ℂ) * (ψ tv.1 : ℂ) = 1 := by
      simp
    rw [show (↑(ψ tv.1)⁻¹ : ℂ) • ρ (n tv.1) tv.2 - tv.2 =
        (↑(ψ tv.1)⁻¹ : ℂ) • (ρ (n tv.1) tv.2 - (ψ tv.1 : ℂ) • tv.2) from by
      rw [smul_sub, smul_smul, h1, one_smul]]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨tv, rfl⟩)
  · rintro x ⟨tv, rfl⟩
    show ρ (n tv.1) tv.2 - (ψ tv.1 : ℂ) • tv.2 ∈
      Submodule.span ℂ (Set.range fun gv : N × V =>
        (↑(ψ gv.1)⁻¹ : ℂ) • ρ (n gv.1) gv.2 - gv.2)
    have h1 : (ψ tv.1 : ℂ) * (↑(ψ tv.1)⁻¹ : ℂ) = 1 := by
      simp
    rw [show ρ (n tv.1) tv.2 - (ψ tv.1 : ℂ) • tv.2 =
        (ψ tv.1 : ℂ) • ((↑(ψ tv.1)⁻¹ : ℂ) • ρ (n tv.1) tv.2 - tv.2) from by
      rw [smul_sub, smul_smul, h1, one_smul]]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨tv, rfl⟩)

def rootCoinvariantsMk (ρ : Representation ℂ G V) (n : N →* G) (ψ : N →* ℂˣ) :
    V →ₗ[ℂ] RootCoinvariants ρ n ψ :=
  Representation.Coinvariants.mk (rootTwistedRepresentation ρ n ψ)

theorem rootCoinvariantsMk_equivariant (ρ : Representation ℂ G V)
    (n : N →* G) (ψ : N →* ℂˣ) (t : N) (v : V) :
    rootCoinvariantsMk ρ n ψ (ρ (n t) v) =
      (ψ t : ℂ) • rootCoinvariantsMk ρ n ψ v := by
  have h1 : (ψ t : ℂ) * (↑(ψ t)⁻¹ : ℂ) = 1 := by
    simp
  have h : ρ (n t) v = (ψ t : ℂ) • rootTwistedRepresentation ρ n ψ t v := by
    simp
  rw [rootCoinvariantsMk, h, map_smul, Representation.Coinvariants.mk_self_apply]

theorem rootCoinvariantsMk_surjective (ρ : Representation ℂ G V)
    (n : N →* G) (ψ : N →* ℂˣ) : Function.Surjective (rootCoinvariantsMk ρ n ψ) :=
  Representation.Coinvariants.mk_surjective _

theorem rootCoinvariantsMk_ker (ρ : Representation ℂ G V)
    (n : N →* G) (ψ : N →* ℂˣ) :
    LinearMap.ker (rootCoinvariantsMk ρ n ψ) = rootRelationSpan ρ n ψ := by
  ext v
  rw [LinearMap.mem_ker, rootCoinvariantsMk, Representation.Coinvariants.mk_eq_zero,
    rootTwistedRepresentation_ker]

def RootEquivariantMaps (ρ : Representation ℂ G V) (n : N →* G) (ψ : N →* ℂˣ)
    (E : Type*) [AddCommGroup E] [Module ℂ E] : Submodule ℂ (V →ₗ[ℂ] E) where
  carrier := {L | ∀ t v, L (ρ (n t) v) = (ψ t : ℂ) • L v}
  zero_mem' := by simp
  add_mem' := by
    simp_all
  smul_mem' := by
    intro c L hL t v
    simp only [LinearMap.smul_apply, hL t v, smul_comm c (ψ t : ℂ)]

theorem rootRelationSpan_le_ker (ρ : Representation ℂ G V)
    (n : N →* G) (ψ : N →* ℂˣ) (L : RootEquivariantMaps ρ n ψ E) :
    rootRelationSpan ρ n ψ ≤ LinearMap.ker L.val := by
  rw [rootRelationSpan]
  apply Submodule.span_le.mpr
  rintro x ⟨tv, rfl⟩
  show L.val (ρ (n tv.1) tv.2 - (ψ tv.1 : ℂ) • tv.2) = 0
  rw [map_sub, map_smul, L.property tv.1 tv.2, sub_self]

def rootCoinvariantsLift (ρ : Representation ℂ G V) (n : N →* G) (ψ : N →* ℂˣ)
    (L : RootEquivariantMaps ρ n ψ E) : RootCoinvariants ρ n ψ →ₗ[ℂ] E :=
  (Representation.Coinvariants.ker (rootTwistedRepresentation ρ n ψ)).liftQ L.val
    (by rw [rootTwistedRepresentation_ker]; exact rootRelationSpan_le_ker ρ n ψ L)

@[simp] theorem rootCoinvariantsLift_mk (ρ : Representation ℂ G V)
    (n : N →* G) (ψ : N →* ℂˣ) (L : RootEquivariantMaps ρ n ψ E) (v : V) :
    rootCoinvariantsLift ρ n ψ L (rootCoinvariantsMk ρ n ψ v) = L.val v := rfl

def rootCoinvariantsUniversalEquiv (ρ : Representation ℂ G V) (n : N →* G)
    (ψ : N →* ℂˣ) (E : Type*) [AddCommGroup E] [Module ℂ E] :
    (RootCoinvariants ρ n ψ →ₗ[ℂ] E) ≃ₗ[ℂ] RootEquivariantMaps ρ n ψ E where
  toFun F := ⟨F.comp (rootCoinvariantsMk ρ n ψ), by
    intro t v
    simp only [LinearMap.comp_apply, rootCoinvariantsMk_equivariant, map_smul]⟩
  invFun := rootCoinvariantsLift ρ n ψ
  left_inv := by
    intro F
    apply Representation.Coinvariants.hom_ext
    rfl
  right_inv := by
    intro L
    rfl
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp] theorem rootCoinvariantsUniversalEquiv_apply (ρ : Representation ℂ G V)
    (n : N →* G) (ψ : N →* ℂˣ) (F : RootCoinvariants ρ n ψ →ₗ[ℂ] E) :
    (rootCoinvariantsUniversalEquiv ρ n ψ E F).val =
      F.comp (rootCoinvariantsMk ρ n ψ) := rfl

def rootTwistedIntertwiner (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (n : N →* G) (ψ : N →* ℂˣ) (f : ρ.IntertwiningMap σ) :
    (rootTwistedRepresentation ρ n ψ).IntertwiningMap (rootTwistedRepresentation σ n ψ) where
  toLinearMap := f.toLinearMap
  isIntertwining' t := by
    ext v
    simp [rootTwistedRepresentation, f.isIntertwining]

def rootCoinvariantsMap (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (n : N →* G) (ψ : N →* ℂˣ) (f : ρ.IntertwiningMap σ) :
    RootCoinvariants ρ n ψ →ₗ[ℂ] RootCoinvariants σ n ψ :=
  Representation.Coinvariants.map _ _ (rootTwistedIntertwiner ρ σ n ψ f)

@[simp] theorem rootCoinvariantsMap_comp_mk (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) (n : N →* G) (ψ : N →* ℂˣ)
    (f : ρ.IntertwiningMap σ) :
    (rootCoinvariantsMap ρ σ n ψ f).comp (rootCoinvariantsMk ρ n ψ) =
      (rootCoinvariantsMk σ n ψ).comp f.toLinearMap := rfl

@[simp] theorem rootTwistedRepresentation_trivial (ρ : Representation ℂ G V) (n : N →* G) :
    rootTwistedRepresentation ρ n 1 = ρ.comp n := by
  ext t v
  simp [rootTwistedRepresentation]

theorem rootCoinvariants_trivial (ρ : Representation ℂ G V) (n : N →* G) :
    RootCoinvariants ρ n 1 = Representation.Coinvariants (ρ.comp n) := by
  rw [RootCoinvariants, rootTwistedRepresentation_trivial]

end Algebraic

section Topological

variable {G N V E : Type*} [Group G] [Group N]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
  [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [ContinuousAdd E] [ContinuousSMul ℂ E]

instance rootCoinvariantsTopology (ρ : Representation ℂ G V) (n : N →* G)
    (ψ : N →* ℂˣ) : TopologicalSpace (RootCoinvariants ρ n ψ) :=
  inferInstanceAs (TopologicalSpace
    (V ⧸ Representation.Coinvariants.ker (rootTwistedRepresentation ρ n ψ)))
