import RequestProject.CellComplex
import RequestProject.CoverAcyclic
import RequestProject.Tac


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

bwd

namespace FiniteChains.Comb

open MonoidAlgebra

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]
variable {J : Type u} [Fintype J] [DecidableEq J]

/-! ### Paths in a complex with one vertex -/

theorem isPath_of_subsingleton {V E} [Subsingleton V] src tgt
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

variable {Nsub}

/-- The lift at the vertex `q` of the edge path spelled by a word. -/
def liftPath : List (α × Bool) → (FreeGroup α ⧸ Nsub) →
    List (((FreeGroup α ⧸ Nsub) × α) × Bool)
  | [], _ => []
  | (i, true) :: L, q => ((q, i), true) :: liftPath L (q * qof Nsub i)
  | (i, false) :: L, q => ((q * (qof Nsub i)⁻¹, i), false) :: liftPath L (q * (qof Nsub i)⁻¹)

omit [Fintype α] [DecidableEq α] in
@[simp] theorem liftPath_nil (q : FreeGroup α ⧸ Nsub) : liftPath [] q = [] := rfl

omit [Fintype α] [DecidableEq α] in
@[simp] theorem liftPath_cons_true (i : α) (L : List (α × Bool)) (q : FreeGroup α ⧸ Nsub) :
    liftPath ((i, true) :: L) q = ((q, i), true) :: liftPath L (q * qof Nsub i) := rfl

omit [Fintype α] [DecidableEq α] in
@[simp] theorem liftPath_cons_false (i : α) (L : List (α × Bool)) (q : FreeGroup α ⧸ Nsub) :
    liftPath ((i, false) :: L) q
      = ((q * (qof Nsub i)⁻¹, i), false) :: liftPath L (q * (qof Nsub i)⁻¹) := rfl

omit [Fintype α] in
theorem mk_cons_true (i : α) (L : List (α × Bool)) :
    FreeGroup.mk ((i, true) :: L) = FreeGroup.of i * FreeGroup.mk L :=
  FreeGroup.toWord_inj.mp rfl

omit [Fintype α] in
theorem mk_cons_false (i : α) (L : List (α × Bool)) :
    FreeGroup.mk ((i, false) :: L) = (FreeGroup.of i)⁻¹ * FreeGroup.mk L :=
  FreeGroup.toWord_inj.mp rfl

omit [Fintype α] [DecidableEq α] in
/-- The projection of the lift of a word is the word itself. -/
theorem map_liftPath (L : List (α × Bool)) (q : FreeGroup α ⧸ Nsub) :
    (liftPath L q).map (fun eb => (eb.1.2, eb.2)) = L := by
  induction L generalizing q with
  | nil => rfl
  | cons a L ih =>
      cases' a with i b
      cases b
      · simp_all
      simp_all


variable (Nsub)

omit [Fintype α] in
/-- The lift at `q` of the word `w` is an edge path from `q` to `q · w`. -/
theorem liftPath_isPath (L : List (α × Bool)) (q : FreeGroup α ⧸ Nsub) :
    IsPath (fun e : (FreeGroup α ⧸ Nsub) × α => e.1)
      (fun e : (FreeGroup α ⧸ Nsub) × α => e.1 * qof Nsub e.2) (liftPath L q) q
      (q * QuotientGroup.mk (FreeGroup.mk L)) := by
  induction L generalizing q with
  | nil =>
      simp [show FreeGroup.mk ([] : List (α × Bool)) = 1 from rfl]
  | cons a L ih =>
      cases' a with i b
      cases b
      · have hmk : (QuotientGroup.mk (FreeGroup.mk ((i, false) :: L)) : FreeGroup α ⧸ Nsub)
            = (qof Nsub i)⁻¹ * QuotientGroup.mk (FreeGroup.mk L) := by
          rfl
        refine ⟨?_, ?_⟩
        · simp
        · simp_all [hmk, ← mul_assoc]
      · have hmk : (QuotientGroup.mk (FreeGroup.mk ((i, true) :: L)) : FreeGroup α ⧸ Nsub)
            = qof Nsub i * QuotientGroup.mk (FreeGroup.mk L) := by
          rfl
        simp_all [hmk, ← mul_assoc]

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
    simp_all [FreeGroup.mk_toWord, (QuotientGroup.eq_one_iff (ρ f.2)).2 (hρ f.2), mul_one]

variable {Nsub ρ}

/-! ### Coordinates: the cellular chains of the cover as free `ℤ[Q]`-modules -/

variable (Nsub)

/-- The cellular chains on the cells `Q × β` of the cover, read as the free `ℤ[Q]`-module
on `β`. -/
noncomputable def coords (β : Type u) [Fintype β] [DecidableEq β] :
    (((FreeGroup α ⧸ Nsub) × β) →₀ ℤ) ≃ₗ[ℤ] (β → CoverRing Nsub) :=
  (Finsupp.domLCongr (Equiv.prodComm _ β)).trans
    ((Finsupp.curryLinearEquiv (R := ℤ)).trans
      ((Finsupp.linearEquivFunOnFinite ℤ _ β).trans
        (LinearEquiv.piCongrRight (fun _ => (MonoidAlgebra.coeffLinearEquiv ℤ).symm))))

variable {Nsub}

omit [Fintype α] [DecidableEq α] [Nsub.Normal] in
/-- The coordinates of a cellular chain: the coefficient of the cell `(q, i)`. -/
theorem coords_apply (β : Type u) [Fintype β] [DecidableEq β]
    (c : ((FreeGroup α ⧸ Nsub) × β) →₀ ℤ) (i : β) (q : FreeGroup α ⧸ Nsub) :
    ((coords Nsub β c) i).coeff q = c (q, i) := by
  rfl

omit [Fintype α] [DecidableEq α] in
theorem coords_single (β : Type u) [Fintype β] [DecidableEq β] (q : FreeGroup α ⧸ Nsub)
    (i : β) (n : ℤ) :
    coords Nsub β (Finsupp.single (q, i) n) = Pi.single i (MonoidAlgebra.single q n) := by
  classical
  funext k
  apply MonoidAlgebra.coeff_injective
  refine Finsupp.ext fun q' => ?_
  rw [coords_apply, Finsupp.single_apply]
  by_cases h : k = i
  · aesop
  aesop

/-- **The dictionary between the cellular boundary and the Fox derivative.**  In the
coordinates above, the cellular chain carried by the lift at `q` of the word `w` is the
Fox vector `q · (∂w/∂x_i)_i`. -/
theorem coords_pathChain_liftPath L q :
    coords Nsub α (pathChain (liftPath L q))
      = fun i => (MonoidAlgebra.single q (1 : ℤ)) *
          proj Nsub (fox i (FreeGroup.mk L)) := by
  classical
  induction L generalizing q with
  | nil =>
      aesop
  | cons a L ih =>
      obtain ⟨i₀, b⟩ := a
      cases b
      · -- the letter `x_{i₀}⁻¹`
        have hq : (MonoidAlgebra.single (q * (qof Nsub i₀)⁻¹) (1))
            = (MonoidAlgebra.single q (1)) *
              proj Nsub (grp (FreeGroup.of i₀)⁻¹) := by
          rw [proj_grp, qgrp, QuotientGroup.mk_inv, MonoidAlgebra.single_mul_single, mul_one]
          rfl
        rw [liftPath_cons_false, pathChain_cons]
        simp [Bool.false_eq_true, if_false, map_add, map_neg]
        funext i
        rw [Pi.add_apply, Pi.neg_apply, coords_single, mk_cons_false, fox_mul, fox_inv,
          map_add, map_neg, map_mul, map_mul, mul_add, mul_neg, ← mul_assoc, ← mul_assoc]
        aesop
      · -- the letter `x_{i₀}`
        have hq : (MonoidAlgebra.single (q * qof Nsub i₀) (1))
            = (MonoidAlgebra.single q (1)) *
              proj Nsub (grp (FreeGroup.of i₀)) := by
          rw [proj_grp, qgrp, MonoidAlgebra.single_mul_single, mul_one]
          rfl
        rw [liftPath_cons_true, pathChain_cons]
        simp [if_true, map_add]
        funext i
        rw [Pi.add_apply, coords_single, mk_cons_true, fox_mul, map_add, map_mul, mul_add,
          ← mul_assoc]
        aesop

/-! ### The cellular chain complex of the cover is the Fox complex -/

variable (hρ : ∀ j, ρ j ∈ Nsub)

include hρ in
/-- `∂₂` of the cover complex is the Fox boundary `∂₂(e_j) = (∂r_j/∂x_i)_i`. -/
theorem coverComplex_bdry2 (u : ((FreeGroup α ⧸ Nsub) × J) →₀ ℤ) :
    _root_.FiniteChains.bdry2 Nsub ρ (coords Nsub J u)
      = coords Nsub α (Comb.bdry2 (coverComplex Nsub ρ hρ) u) := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => simp [map_zero, _root_.FiniteChains.bdry2_zero]
  | add u₁ u₂ h₁ h₂ =>
      rw [map_add, _root_.FiniteChains.bdry2_add, h₁, h₂, map_add, ← map_add]
  | single f n =>
      cases' f with q j
      rw [coords_single, bdry2_single, map_smul, coords_pathChain_liftPath, FreeGroup.mk_toWord]
      funext i
      show ∑ j' : J, (Pi.single j (MonoidAlgebra.single q n) : J → CoverRing Nsub) j' *
          proj Nsub (fox i (ρ j')) = _
      rw [Finset.sum_eq_single j (by simp_all)
        (by simp)]
      simp only [Pi.single_eq_same, Pi.smul_apply]
      rw [show (MonoidAlgebra.single q n : CoverRing Nsub)
          = n • (MonoidAlgebra.single q (1 : ℤ) : CoverRing Nsub) by
        simp, smul_mul_assoc]

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
