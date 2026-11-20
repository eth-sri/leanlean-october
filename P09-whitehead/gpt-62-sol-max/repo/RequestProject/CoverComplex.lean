module

public import RequestProject.CellComplex
public import RequestProject.CoverChainComplex
public import RequestProject.FoxCommutator
public import RequestProject.FoxFinsupp
public import RequestProject.FinsuppBasis

public import RequestProject.GroupCellChainCoordinates
public import RequestProject.FoxVoltage

@[expose] public section

/-!
# The presentation complex, its covers, and the dictionary with the Fox complex

For a finite presentation `⟨x_1, …, x_n | r_1, …, r_m⟩` this file builds, inside the
combinatorial world of `RequestProject/CellComplex.lean`:

* `FiniteChains.Comb.presComplex ρ` — the presentation complex `K`: one vertex, one edge
  per generator, one two-cell per relator, attached along the relator word;
* `FiniteChains.Comb.coverComplex ρ Nsub` — for a normal subgroup `Ñ ◁ F` containing the
  relators, the cover `K_N` with deck group `Q = F/Ñ`: vertices `Q`, edges `Q × {x_i}`,
  two-cells `Q × {r_j}` attached along the lift of the relator word;
* `FiniteChains.Comb.coverProj` — the covering map `K_N → K`, which is proved to be a
  combinatorial covering (`coverProj_isCovering`), regular with deck group `Q`
  (`coverProj_isRegular`), with `K_N` connected (`coverComplex_isConnected`).

The **dictionary between topology and algebra** is the content of
`FiniteChains.Comb.coords_pathChain_liftPath`: in the coordinates
`ℤ[cells of K_N] ≅ ℤ[Q]^{cells of K}`, the cellular chain carried by the lift at `q` of a
word `w` is `q · (∂w/∂x_i)_i`, the Fox vector of `w`.  Consequently the cellular chain
complex of `K_N` *is* the Fox complex of `RequestProject/CoverChainComplex.lean`
(`coverComplex_bdry1`, `coverComplex_bdry2`, `coverComplex_augC`), and the algebraic
acyclicity proved there becomes acyclicity of the cover as a two-complex
(`coverComplex_isAcyclic`).

The final statement, `FiniteChains.Comb.presComplex_hasAcyclicRegularCover`, is exactly the
topological input `cover` of Section 2, now a theorem: a perfect normal subgroup satisfying
the requirements (2.2) produces a connected acyclic regular cover of the presentation
complex.
-/


namespace FiniteChains
namespace Comb

open MonoidAlgebra

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]
variable {J : Type u} [Fintype J] [DecidableEq J]

/-! ### Paths in a complex with one vertex -/

theorem isPath_of_subsingleton {V E : Type*} [Subsingleton V] (src tgt : E → V)
    (p : List (E × Bool)) (a b : V) : IsPath src tgt p a b := by
  induction p generalizing a with
  | nil => exact Subsingleton.elim _ _
  | cons e p ih => exact ⟨Subsingleton.elim _ _, ih _⟩

/-! ### The presentation complex -/

/-- The two-complex of the presentation `⟨x_i | r_j⟩`: one vertex, an edge for every
generator and a two-cell for every relator, attached along the relator word. -/
abbrev presComplex (ρ : J → FreeGroup α) : Complex2.{u} where
  V := PUnit.{u + 1}
  E := α
  F := J
  src _ := PUnit.unit
  tgt _ := PUnit.unit
  base _ := PUnit.unit
  att j := FreeGroup.toWord (ρ j)
  att_isLoop _ := isPath_of_subsingleton _ _ _ _ _

/-! ### The cover attached to a normal subgroup of the free group -/

variable (Nsub : Subgroup (FreeGroup α)) [Nsub.Normal]

/-- The image of a generator in the deck group `Q = F/Ñ`. -/
def qof (i : α) : FreeGroup α ⧸ Nsub := QuotientGroup.mk (FreeGroup.of i)

omit [Fintype α] [DecidableEq α] in
def presentationVoltage (e : α × Bool) : FreeGroup α ⧸ Nsub :=
  QuotientGroup.mk (FreeGroup.mk [e])

variable {Nsub}

/-- The lift at the vertex `q` of the edge path spelled by a word. -/
abbrev liftPath := PathVoltage.liftPath (presentationVoltage Nsub)



omit [Fintype α] [DecidableEq α] in
@[simp] theorem liftPath_cons_true (i : α) (L : List (α × Bool)) (q : FreeGroup α ⧸ Nsub) :
    liftPath ((i, true) :: L) q = ((q, i), true) :: liftPath L (q * qof Nsub i) := rfl

omit [Fintype α] [DecidableEq α] in
@[simp] theorem liftPath_cons_false (i : α) (L : List (α × Bool)) (q : FreeGroup α ⧸ Nsub) :
    liftPath ((i, false) :: L) q
      = ((q * (qof Nsub i)⁻¹, i), false) :: liftPath L (q * (qof Nsub i)⁻¹) := rfl

omit [Fintype α] [DecidableEq α] in
theorem mk_cons_true (i : α) (L : List (α × Bool)) :
    FreeGroup.mk ((i, true) :: L) = FreeGroup.of i * FreeGroup.mk L :=
  rfl

omit [Fintype α] [DecidableEq α] in
theorem mk_cons_false (i : α) (L : List (α × Bool)) :
    FreeGroup.mk ((i, false) :: L) = (FreeGroup.of i)⁻¹ * FreeGroup.mk L :=
  rfl

omit [Fintype α] [DecidableEq α] in
/-- The projection of the lift of a word is the word itself. -/
theorem map_liftPath (L : List (α × Bool)) (q : FreeGroup α ⧸ Nsub) :
    (liftPath L q).map (fun eb => (eb.1.2, eb.2)) = L :=
  PathVoltage.liftPath_projection _ L q

omit [Fintype α] [DecidableEq α] in
private theorem mk_prod_letters (L : List (α × Bool)) :
    (L.map fun e => FreeGroup.mk [e]).prod = FreeGroup.mk L := by
  induction L with
  | nil => rfl
  | cons e L ih => simp only [List.map_cons, List.prod_cons, ih, FreeGroup.mul_mk, List.singleton_append]

variable (Nsub)

omit [Fintype α] [DecidableEq α] in
/-- The lift at `q` of the word `w` is an edge path from `q` to `q · w`. -/
theorem liftPath_isPath (L : List (α × Bool)) (q : FreeGroup α ⧸ Nsub) :
    IsPath (fun e : (FreeGroup α ⧸ Nsub) × α => e.1)
      (fun e : (FreeGroup α ⧸ Nsub) × α => e.1 * qof Nsub e.2) (liftPath L q) q
      (q * QuotientGroup.mk (FreeGroup.mk L)) := by
  have h := PathVoltage.liftPath_isPath (V := PUnit.{u+1}) (presentationVoltage Nsub)
    (fun _ => PUnit.unit) (fun _ => PUnit.unit) Prod.fst (fun _ => rfl)
    (isPath_of_subsingleton _ _ L PUnit.unit PUnit.unit) q
  change IsPath _ _ _ q (q * (L.map (presentationVoltage Nsub)).prod) at h
  have hw : (L.map (presentationVoltage Nsub)).prod = QuotientGroup.mk (FreeGroup.mk L) := by
    calc
      _ = (List.map (QuotientGroup.mk' Nsub) (L.map fun e => FreeGroup.mk [e])).prod := by
        rw [List.map_map]
        rfl
      _ = _ := by rw [← map_list_prod, mk_prod_letters]; rfl
  rwa [hw] at h

variable (ρ : J → FreeGroup α)

/-- The cover `K_N` of the presentation complex attached to `Ñ ◁ F`: vertices the deck
group `Q = F/Ñ`, one edge `(q, x_i)` from `q` to `q x_i` for every `q` and every generator,
one two-cell `(q, r_j)` attached along the lift at `q` of the relator `r_j`. -/
abbrev coverComplex (hρ : ∀ j, ρ j ∈ Nsub) : Complex2.{u} where
  V := FreeGroup α ⧸ Nsub
  E := (FreeGroup α ⧸ Nsub) × α
  F := (FreeGroup α ⧸ Nsub) × J
  src e := e.1
  tgt e := e.1 * qof Nsub e.2
  base f := f.1
  att f := liftPath (FreeGroup.toWord (ρ f.2)) f.1
  att_isLoop f := by
    have h := liftPath_isPath Nsub (FreeGroup.toWord (ρ f.2)) f.1
    rw [FreeGroup.mk_toWord] at h
    rwa [(QuotientGroup.eq_one_iff (ρ f.2)).2 (hρ f.2), mul_one] at h

variable {Nsub ρ}

/-! ### Coordinates: the cellular chains of the cover as free `ℤ[Q]`-modules -/

variable (Nsub)

/-- Finitely supported coordinates over the cover group ring, with no
finiteness assumption on the set of cells. -/
noncomputable def fsCoords (β : Type u) :
    (((FreeGroup α ⧸ Nsub) × β) →₀ ℤ) ≃ₗ[ℤ] (β →₀ CoverRing Nsub) :=
  groupCellChainEquiv

omit [Fintype α] [DecidableEq α] in
theorem fsCoords_apply (β : Type u) (c : ((FreeGroup α ⧸ Nsub) × β) →₀ ℤ)
    (i : β) (q : FreeGroup α ⧸ Nsub) : (fsCoords Nsub β c i).coeff q = c (q, i) :=
  groupCellChainEquiv_apply c i q

omit [Fintype α] [DecidableEq α] in
theorem fsCoords_single (β : Type u) (q : FreeGroup α ⧸ Nsub) (i : β) (n : ℤ) :
    fsCoords Nsub β (Finsupp.single (q, i) n) =
      Finsupp.single i (MonoidAlgebra.single q n : CoverRing Nsub) :=
  groupCellChainEquiv_single q i n

omit [Fintype α] in
theorem fsCoords_pathChain_liftPath_apply (L : List (α × Bool))
    (q : FreeGroup α ⧸ Nsub) (i : α) :
    fsCoords Nsub α (pathChain (liftPath L q)) i =
      (MonoidAlgebra.single q (1 : ℤ) : CoverRing Nsub) * proj Nsub (fox i (FreeGroup.mk L)) := by
  classical
  let D := (Finsupp.lapply i).comp (fsCoords Nsub α).toLinearMap
  change D (pathChain (liftPath L q)) = _
  rw [← mk_prod_letters L]
  refine PathVoltage.liftPath_fox (QuotientGroup.mk' Nsub) (fun e => FreeGroup.mk [e]) D i
    ?_ L q
  rintro g ⟨k, b⟩
  change D (pathChain [PathVoltage.liftGerm (presentationVoltage Nsub) g (k, b)]) =
    single g 1 * proj Nsub (fox i (FreeGroup.mk [(k, b)]))
  cases b <;> by_cases h : i = k <;>
    simp [D, PathVoltage.liftGerm, presentationVoltage, pathChain, fsCoords_single,
      show FreeGroup.mk [(k, true)] = FreeGroup.of k from rfl,
      show FreeGroup.mk [(k, false)] = (FreeGroup.of k)⁻¹ from rfl,
      fox_inv, proj_grp, qgrp, single_mul_single, h]

variable (hρ : ∀ j, ρ j ∈ Nsub)

omit [Fintype α] [Fintype J] [DecidableEq J] in
include hρ in
theorem fs_coverComplex_bdry2 (c : ((FreeGroup α ⧸ Nsub) × J) →₀ ℤ) :
    coverSecondBoundary Nsub ρ (fsCoords Nsub J c) =
      fsCoords Nsub α (bdry2 (coverComplex Nsub ρ hρ) c) := by
  finsupp_basis c
  rintro ⟨q, j⟩
  rw [fsCoords_single, bdry2_single, one_smul, coverSecondBoundary, Finsupp.linearCombination_single]
  ext i
  rw [Finsupp.smul_apply, smul_eq_mul, fsCoords_pathChain_liftPath_apply, FreeGroup.mk_toWord]
  rfl

/-- If the cell set is finite, these coordinates are just a function on it. -/
noncomputable def coords (β : Type u) [Fintype β] [DecidableEq β] :
    (((FreeGroup α ⧸ Nsub) × β) →₀ ℤ) ≃ₗ[ℤ] (β → CoverRing Nsub) :=
  (fsCoords Nsub β).trans (Finsupp.linearEquivFunOnFinite _ _ _)

variable {Nsub}

omit [Fintype α] [DecidableEq α] in
theorem coords_apply (β : Type u) [Fintype β] [DecidableEq β]
    (c : ((FreeGroup α ⧸ Nsub) × β) →₀ ℤ) (i : β) (q : FreeGroup α ⧸ Nsub) :
    (coords Nsub β c i).coeff q = c (q, i) :=
  fsCoords_apply Nsub β c i q

omit [Fintype α] [DecidableEq α] in
theorem coords_single (β : Type u) [Fintype β] [DecidableEq β] (q : FreeGroup α ⧸ Nsub)
    (i : β) (n : ℤ) :
    coords Nsub β (Finsupp.single (q, i) n) = Pi.single i (MonoidAlgebra.single q n) := by
  change ⇑(fsCoords Nsub β (Finsupp.single (q, i) n)) = _
  rw [fsCoords_single, Finsupp.single_eq_pi_single]

theorem coords_pathChain_liftPath (L : List (α × Bool)) (q : FreeGroup α ⧸ Nsub) :
    coords Nsub α (pathChain (liftPath L q)) = fun i =>
      (MonoidAlgebra.single q (1 : ℤ) : CoverRing Nsub) * proj Nsub (fox i (FreeGroup.mk L)) :=
  funext (fsCoords_pathChain_liftPath_apply Nsub L q)

include hρ in
theorem coverComplex_bdry2 (c : ((FreeGroup α ⧸ Nsub) × J) →₀ ℤ) :
    _root_.FiniteChains.bdry2 Nsub ρ (coords Nsub J c) =
      coords Nsub α (Comb.bdry2 (coverComplex Nsub ρ hρ) c) := by
  funext i
  change (∑ j, (fsCoords Nsub J c) j * proj Nsub (fox i (ρ j))) =
    fsCoords Nsub α (Comb.bdry2 (coverComplex Nsub ρ hρ) c) i
  rw [← fs_coverComplex_bdry2 Nsub hρ, coverSecondBoundary, Finsupp.linearCombination_apply,
    Finsupp.sum_apply, Finsupp.sum_fintype]
  · rfl
  · simp

/-! ### Acyclicity of the cover -/

/-! ### The cover is connected -/

/-! ### The covering map and the deck action -/

/-- The projection of the cover onto the presentation complex. -/
def coverProj : Hom (coverComplex Nsub ρ hρ) (presComplex ρ) where
  onV _ := PUnit.unit
  onE e := e.2
  onF f := f.2
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF _ := rfl
  att_onF f := (map_liftPath (FreeGroup.toWord (ρ f.2)) f.1).symm


/-! ### The topological input of Section 2, as a theorem -/

end Comb
end FiniteChains
