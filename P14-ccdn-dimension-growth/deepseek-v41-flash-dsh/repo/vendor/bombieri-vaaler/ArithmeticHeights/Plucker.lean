/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# The Plücker point of a subspace

A `k`-dimensional subspace `V` of `ι → K` determines a point of the projective space on
`Set.powersetCard ι k → K`, the tuple of its **Plücker coordinates**: wedge a basis of `V` together
inside `⋀[K]^k (ι → K)` and read the result in the basis that the standard basis of `ι → K`
induces there. A change of basis of `V` multiplies the wedge by a determinant, hence by a unit, so
the point of projective space depends on `V` alone.

This file builds that point and proves it is an embedding of the `k`-dimensional subspaces into
projective space. Layer 3.2 defines the height of a subspace as the height of this point, and
everything the height inherits — Northcott for subspaces above all — rests on the injectivity
proved here.

## Main definitions

* `exteriorPower.plucker k v` for `v : Fin k → (ι → K)`: the coordinate tuple of the wedge
  `v 0 ∧ ⋯ ∧ v (k-1)`, indexed by the `k`-element subsets of `ι`.
* `Submodule.pluckerPoint V hV` for `hV : Module.finrank K V = k`: the induced point of
  `Projectivization K (Set.powersetCard ι k → K)`.

## Main results

* `exteriorPower.plucker_apply`: the Plücker coordinate at `s` is the maximal minor on the columns
  `s` of the matrix whose rows are the `v i`. `exteriorPower.plucker_fin_eq_det` is the top-rank
  case, where the single coordinate is the determinant, and
  `exteriorPower.plucker_one_ofSingleton` the rank-one case, where the coordinates are the
  coordinates of the vector.
* `exteriorPower.plucker_eq_zero_iff`: the coordinate tuple vanishes exactly when the family is
  linearly dependent, so a basis of `V` produces a nonzero tuple.
* `Submodule.pluckerPoint_eq_mk` and `Submodule.pluckerPoint_span_range`: the value of the Plücker
  point on *any* basis of `V`, and on any linearly independent family spanning it. This is the
  basis-independence, stated in the form that is actually used.
  `Submodule.pluckerPoint_span_singleton` is the rank-one case: the Plücker point of a line is the
  point itself.
* `Submodule.pluckerPoint_injective`: distinct subspaces of the same rank have distinct Plücker
  points.

Two lemmas are stated here because Mathlib lacks them and the proofs need them:
`exteriorPower.ιMulti_eq_zero_iff`, that over a field a wedge vanishes exactly on linearly
dependent families, and `linearIndependent_fin1`, the `Fin 1` companion of Mathlib's
`linearIndependent_fin2`.

## Implementation notes

The index type is Mathlib's `Set.powersetCard ι k`, the type of `k`-element finsets of `ι`, because
that is what `Module.Basis.exteriorPower` is indexed by; using it verbatim is what lets
`exteriorPower.plucker_apply` come out of Mathlib's `exteriorPower.ιMultiDual_apply_ιMulti` with no
index bookkeeping of our own. It is also why `[LinearOrder ι]` is a standing hypothesis: an order
on `ι` is needed to say *which* wedge of basis vectors a `k`-element subset names. A different
order changes each coordinate by a sign only, so nothing downstream depends on the choice.

The Plücker point is *not* built by `Projectivization.lift`. There is no projective space to lift
from: the data that varies is a basis of `V`, and bases do not form a projectivization. What takes
its place is `Submodule.pluckerPoint_eq_mk`, which says the value on an arbitrary basis is the
value on the chosen one, and which is the only thing a proof ever needs from well-definedness.
The definition itself picks `Module.finBasisOfFinrankEq`.

Injectivity is proved through the wedge criterion `exteriorPower.ιMulti_snoc_eq_zero_iff`: a vector
lies in the span of a linearly independent family exactly when wedging it on gives `0`. Since the
wedge of a basis of `V` is recovered from the Plücker point up to a nonzero scalar, and scaling
does not change what the criterion detects, the point determines the subspace. The criterion itself
is proved in `ExteriorAlgebra K (ι → K)`, where wedging on is multiplication.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§2.8.4.

M. Hindry and J. H. Silverman, *Diophantine Geometry: An Introduction*, Springer GTM 201 (2000),
Exercise A.1.11(a)–(b).

This is Layer 3.1 of the `ArithmeticHeights` roadmap.
-/

public section

open Module

section LinearIndependent

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

end LinearIndependent

namespace exteriorPower

/-- `Fin k` has exactly one subset of `k` elements, and its increasing enumeration is the
identity. -/
lemma ofFinEmbEquiv_symm_fin {k : ℕ} (s : Set.powersetCard (Fin k) k) :
    ⇑(Set.powersetCard.ofFinEmbEquiv.symm s) = (id : Fin k → Fin k) := by
  have hs : (s : Finset (Fin k)) = Finset.univ := Finset.eq_univ_of_card _ (by simp)
  rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
  exact (Finset.orderEmbOfFin_unique _ (fun x ↦ hs ▸ Finset.mem_univ x) strictMono_id).symm

section Field

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] {k : ℕ}

/-- Over a field, the wedge of a linearly independent family is nonzero. -/
theorem ιMulti_ne_zero {v : Fin k → E} (hv : LinearIndependent K v) : ιMulti K k v ≠ 0 := by
  have h := (ιMulti_family_linearIndependent_field k hv).ne_zero
    (⟨Finset.univ, by simp⟩ : Set.powersetCard (Fin k) k)
  rwa [ιMulti_family, ofFinEmbEquiv_symm_fin, Function.comp_id] at h

/-- Over a field, a wedge of `k` vectors vanishes exactly when they are linearly dependent. -/
theorem ιMulti_eq_zero_iff (v : Fin k → E) : ιMulti K k v = 0 ↔ ¬ LinearIndependent K v :=
  ⟨fun h hv ↦ ιMulti_ne_zero hv h, AlternatingMap.map_linearDependent _ v⟩

end Field

section Snoc

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {k : ℕ}

end Snoc

section Plucker

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The **Plücker coordinates** of a family `v : Fin k → (ι → R)`: the coordinate tuple of the
wedge `v 0 ∧ ⋯ ∧ v (k-1)` in the basis of `⋀[R]^k (ι → R)` induced by the standard basis of
`ι → R`, indexed by the `k`-element subsets of `ι`. -/
@[expose] noncomputable def plucker (k : ℕ) (v : Fin k → (ι → R)) : Set.powersetCard ι k → R :=
  ((Pi.basisFun R ι).exteriorPower k).equivFun (ιMulti R k v)

/-- **The Plücker coordinates are the maximal minors.** The coordinate at a `k`-element subset `s`
of `ι` is the determinant of the `k × k` matrix cut out of the rows `v` by the columns `s`, the
columns taken in the order of `ι`. -/
theorem plucker_apply (k : ℕ) (v : Fin k → (ι → R)) (s : Set.powersetCard ι k) :
    plucker k v s = (Matrix.of fun i j ↦ v i (Set.powersetCard.ofFinEmbEquiv.symm s j)).det := by
  rw [plucker, Basis.equivFun_apply, basis_repr_apply, ιMultiDual_apply_ιMulti]
  simp

/-- In top rank there is one Plücker coordinate and it is the determinant. -/
theorem plucker_fin_eq_det {n : ℕ} (v : Fin n → (Fin n → R)) (s : Set.powersetCard (Fin n) n) :
    plucker n v s = (Matrix.of v).det := by
  rw [plucker_apply, ofFinEmbEquiv_symm_fin]
  rfl

/-- The Plücker coordinates determine the wedge: proportionality of the coordinate tuples is
proportionality of the wedges. -/
theorem plucker_eq_smul_iff (k : ℕ) (c : R) (v w : Fin k → (ι → R)) :
    plucker k v = c • plucker k w ↔ ιMulti R k v = c • ιMulti R k w := by
  rw [plucker, plucker, ← map_smul]
  exact (LinearEquiv.injective _).eq_iff

variable {K : Type*} [Field K] {k : ℕ} {v : Fin k → (ι → K)}

/-- Over a field, the Plücker coordinates of a family vanish exactly when it is linearly
dependent. -/
theorem plucker_eq_zero_iff (k : ℕ) (v : Fin k → (ι → K)) :
    plucker k v = 0 ↔ ¬ LinearIndependent K v := by
  rw [← ιMulti_eq_zero_iff (K := K) v, plucker,
    map_eq_zero_iff _ (LinearEquiv.injective _)]

/-- Over a field, the Plücker coordinates of a linearly independent family are not all zero. -/
theorem plucker_ne_zero (hv : LinearIndependent K v) : plucker k v ≠ 0 :=
  fun h ↦ (plucker_eq_zero_iff k v).1 h hv

end Plucker

end exteriorPower

namespace Submodule

open exteriorPower

section Basis

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {κ : Type*}
  {V : Submodule R M}

/-- The family of vectors of `M` underlying a basis of a submodule is linearly independent. -/
theorem linearIndependent_coe_basis (b : Basis κ R V) : LinearIndependent R fun i ↦ ((b i : M)) :=
  b.linearIndependent.map' V.subtype V.ker_subtype

end Basis

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [LinearOrder ι] {k : ℕ}
  {V : Submodule K (ι → K)}

/-- Two bases of the same `k`-dimensional subspace have proportional Plücker coordinates: the
scalar is the determinant of the change-of-basis matrix, and in particular a unit. -/
lemma exists_plucker_eq_smul (hV : finrank K V = k) (b b' : Basis (Fin k) K V) :
    ∃ c : K, plucker k (fun i ↦ ((b' i : ι → K))) = c • plucker k fun i ↦ ((b i : ι → K)) := by
  have h1 : finrank K (⋀[K]^k V) = 1 := by rw [exteriorPower.finrank_eq, hV, Nat.choose_self]
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (ιMulti K k ⇑b)
    (ιMulti_ne_zero b.linearIndependent)).1 h1 (ιMulti K k ⇑b')
  refine ⟨c, (plucker_eq_smul_iff ..).2 ?_⟩
  have := congrArg (exteriorPower.map k V.subtype) hc
  rwa [map_smul, map_apply_ιMulti, map_apply_ιMulti, eq_comm] at this

/-- **The Plücker point of a `k`-dimensional subspace of `ι → K`** (Bombieri–Gubler 2.8.4;
Hindry–Silverman, Exercise A.1.11(a)–(b)): the point of projective space on the `k`-element subsets
of `ι` given by the Plücker coordinates of any basis of `V`. It does not depend on the basis; see
`Submodule.pluckerPoint_eq_mk`. -/
@[expose] noncomputable def pluckerPoint (V : Submodule K (ι → K)) (hV : finrank K V = k) :
    Projectivization K (Set.powersetCard ι k → K) :=
  Projectivization.mk K (plucker k fun i ↦ (((finBasisOfFinrankEq K V hV) i : ι → K)))
    (plucker_ne_zero (linearIndependent_coe_basis _))

/-- **The Plücker point is computed by every basis, not only by the chosen one.** -/
theorem pluckerPoint_eq_mk (hV : finrank K V = k) (b : Basis (Fin k) K V)
    (hb : plucker k (fun i ↦ ((b i : ι → K))) ≠ 0) :
    pluckerPoint V hV = Projectivization.mk K (plucker k fun i ↦ ((b i : ι → K))) hb := by
  obtain ⟨c, hc⟩ := exists_plucker_eq_smul hV b (finBasisOfFinrankEq K V hV)
  refine ((Projectivization.mk_eq_mk_iff' K _ _ _ hb).2 ⟨c, hc.symm⟩)

/-- **The Plücker point of a span.** For a linearly independent family, the Plücker point of the
subspace it spans is the point defined by its Plücker coordinates. -/
theorem pluckerPoint_span_range {v : Fin k → (ι → K)} (hv : LinearIndependent K v)
    (hV : finrank K (Submodule.span K (Set.range v)) = k) :
    pluckerPoint (Submodule.span K (Set.range v)) hV =
      Projectivization.mk K (plucker k v) (plucker_ne_zero hv) := by
  have hfun : (fun i ↦ ((Basis.span hv i : ι → K))) = v :=
    funext fun i ↦ congrArg Subtype.val (Basis.span_apply hv i)
  rw [pluckerPoint_eq_mk hV (Basis.span hv) (by rw [hfun]; exact plucker_ne_zero hv)]
  simp only [hfun]

end Submodule

section Examples

open Submodule exteriorPower

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [LinearOrder ι]

end Examples
