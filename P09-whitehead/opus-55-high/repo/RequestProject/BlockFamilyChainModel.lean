module

public import RequestProject.BlockFamilySubst
public import RequestProject.BlockRelativeQuotient

@[expose] public section

/-!
# The chain model of the double mapping cylinder of a whole family of blocks

`RequestProject/BlockFamilySubst.lean` builds the structural map of the article's
simultaneous substitution (3.4): a family `(s : Sx)` of labelled relator entries of

  `ρ : Jr ⊕ Sx → FreeGroup α`

is replaced at the same time, the entry `s` by its own block with its own internal generators
`Zt s` and its own relator entries `Mt s`.

This file instantiates the (B2) route of `RequestProject/BlockRelativeQuotient.lean` — the one
that goes through the *relative* complex of the pair `(W̃, U)` and the article's homological
input `H₂(W̃, U) = 0` — **at that concrete substitution**.  All the data that the general
statement `FiniteChains.BlockFox.generates_of_quotient_relative` takes as parameters are
*constructed* here from the substitution itself, and all its structural hypotheses are
*proved* here:

* `FiniteChains.BlockFamily.oneChainIncl` (`f₁`) — the one-chains of the preimage of `X` are
  the one-chains on the old generators, included into the one-chains on all generators by
  extension by zero.  Its injectivity is `oneChainIncl_injective`;
* `FiniteChains.BlockFamily.polyBdry` (`bq`) — the module `Sx → ℤ[G']` of the two-chains
  carried by the replaced polygons, with the boundary of the polygon at `s` equal to the
  base-changed Fox row of the replaced relator `ρ (Sum.inr s)`;
* `FiniteChains.BlockFamily.cylChain` (`a₃`) and the negation isomorphism (`b₃`) — the
  three-cells of the double mapping cylinder, one per replaced entry: the boundary of the
  three-cell at `s` is the filling chain `c s` of the block at `s` minus the replaced polygon.
  This is the cancelling pair of cells of the article ("in the double mapping cylinder of
  `a_s` the polygon-cylinder three-cell cancels that old two-cell; for distinct `s` these
  cancelling pairs are disjoint");
* `FiniteChains.BlockFamily.chainMap_incl` (`hchainF₂`) — the inclusion of the preimage of
  `X` is a chain map, i.e. the boundary of the cover restricts to the base-changed Fox
  boundary of `ρ`;
* `FiniteChains.BlockFamily.bdry_bdry_eq_zero` (`hdd`) — the boundary of the boundary of a
  three-cell vanishes.

The outcome is

  `FiniteChains.BlockFamily.generates_familySubst_of_relative_vanishing`,

property (B2) — equation (3.3) — for the article's simultaneous substitution, with exactly
two remaining inputs, both of them the geometric ones of the article's proof:

* `hinj`: the substitution is injective on fundamental groups (Step 1 of the article's
  "Generation in the pushout of a family", the radial retraction in the CAT(0) universal
  cover).  By `FiniteChains.BlockSubst.baseHom_not_injective` this cannot be replaced by any
  argument using presentations alone;
* `hrel`: `H₂(W̃, U) = 0` for this concrete relative complex (Steps 2 and 3, the collapsed
  space `V` and its cube structure).

No further dictionary, no cell-by-cell identification with a cube complex and no hypothesis
about `H₂(W̃)` (which is false for a nonaspherical `X`, see
`RequestProject/BlockSphereRegression.lean`) is used.

As everywhere in the project's Fox calculus, the presentations are finite, so the family `Sx`
of simultaneously replaced entries is a finite (but otherwise arbitrary) set of labelled
entries.
-/

namespace FiniteChains

namespace BlockFamily

open MonoidAlgebra

universe u

variable {α Jr Sx : Type u} {Zt Mt : Sx → Type u}
  [Fintype α] [DecidableEq α] [Fintype Jr] [DecidableEq Jr]
  [Fintype Sx] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype (Mt s)]
  {ρ : Jr ⊕ Sx → FreeGroup α} {bsub : ∀ s : Sx, Mt s → FreeGroup (α ⊕ Zt s)}
  {hfill : FilledF ρ bsub}
  {c : ∀ s : Sx, Mt s → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub))}

/-! ### The one-chains of the preimage of `X` -/

/-- The inclusion of the one-chains of the preimage of `X` into the one-chains of the cover of
the double mapping cylinder: extension by zero from the old generators to all generators. -/
noncomputable def oneChainIncl (ρ : Jr ⊕ Sx → FreeGroup α)
    (bsub : ∀ s : Sx, Mt s → FreeGroup (α ⊕ Zt s)) :
    (α → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub)))
      →ₗ[MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub))]
      ((α ⊕ (Σ s : Sx, Zt s)) → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub))) where
  toFun v := Sum.elim v 0
  map_add' v w := by
    funext i
    cases i <;> simp
  map_smul' x v := by
    funext i
    cases i <;> simp

omit [Fintype α] [DecidableEq α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype (Mt s)] in
@[simp] theorem oneChainIncl_inl
    (v : α → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub))) (i : α) :
    oneChainIncl ρ bsub v (Sum.inl i) = v i := rfl

omit [Fintype α] [DecidableEq α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype (Mt s)] in
@[simp] theorem oneChainIncl_inr
    (v : α → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub))) (w : Σ s : Sx, Zt s) :
    oneChainIncl ρ bsub v (Sum.inr w) = 0 := rfl

/-! ### The replaced polygons and the cancelling three-cells -/

/-- The boundary of the replaced two-cells: the polygon of the entry `s` is attached along the
replaced relator, so its boundary is the base change of the Fox row of that relator. -/
noncomputable def polyBdry (ρ : Jr ⊕ Sx → FreeGroup α)
    (bsub : ∀ s : Sx, Mt s → FreeGroup (α ⊕ Zt s)) (hfill : FilledF ρ bsub) :
    (Sx → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub)))
      →ₗ[MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub))]
      ((α ⊕ (Σ s : Sx, Zt s)) → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub))) where
  toFun q := Sum.elim
    (fun i => ∑ s : Sx, q s * coeffF ρ bsub hfill (foxMatrixPres ρ i (Sum.inr s))) 0
  map_add' q q' := by
    funext i
    cases i with
    | inl i => simp [Finset.sum_add_distrib, add_mul]
    | inr w => simp
  map_smul' x q := by
    funext i
    cases i with
    | inl i => simp [Finset.mul_sum, mul_assoc]
    | inr w => simp

omit [Fintype α] [Fintype Jr] [DecidableEq Jr] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype (Mt s)] in
@[simp] theorem polyBdry_inl (q : Sx → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub)))
    (i : α) :
    polyBdry ρ bsub hfill q (Sum.inl i)
      = ∑ s : Sx, q s * coeffF ρ bsub hfill (foxMatrixPres ρ i (Sum.inr s)) := rfl

omit [Fintype α] [Fintype Jr] [DecidableEq Jr] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype (Mt s)] in
@[simp] theorem polyBdry_inr (q : Sx → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub)))
    (w : Σ s : Sx, Zt s) : polyBdry ρ bsub hfill q (Sum.inr w) = 0 := rfl

/-- The part of the boundary of the three-cells which lies on the two-cells of the substituted
presentation: the three-cell at `s` is the cylinder over the polygon of `s`, so this part is
the filling chain `c s` of the block substituted at `s`. -/
noncomputable def cylChain (ρ : Jr ⊕ Sx → FreeGroup α)
    (bsub : ∀ s : Sx, Mt s → FreeGroup (α ⊕ Zt s))
    (c : ∀ s : Sx, Mt s → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub))) :
    (Sx → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub)))
      →ₗ[MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub))]
      ((Jr ⊕ (Σ s : Sx, Mt s)) → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub))) where
  toFun y := Sum.elim 0 (fun p => y p.1 * c p.1 p.2)
  map_add' y y' := by
    funext k
    cases k with
    | inl j => simp
    | inr p => simp [add_mul]
  map_smul' x y := by
    funext k
    cases k with
    | inl j => simp
    | inr p => simp [mul_assoc]

omit [Fintype α] [DecidableEq α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype (Mt s)] in
@[simp] theorem cylChain_inl (y : Sx → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub)))
    (j : Jr) : cylChain ρ bsub c y (Sum.inl j) = 0 := rfl

omit [Fintype α] [DecidableEq α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype (Mt s)] in
@[simp] theorem cylChain_inr (y : Sx → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub)))
    (p : Σ s : Sx, Mt s) : cylChain ρ bsub c y (Sum.inr p) = y p.1 * c p.1 p.2 := rfl

/-- The identification of the three-cells with the replaced two-cells they cancel: the
three-cell at `s` has the polygon at `s` in its boundary with the coefficient `-1`. -/
noncomputable def cylCancel (ρ : Jr ⊕ Sx → FreeGroup α)
    (bsub : ∀ s : Sx, Mt s → FreeGroup (α ⊕ Zt s)) :
    (Sx → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub)))
      ≃ₗ[MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub))]
      (Sx → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub))) :=
  LinearEquiv.neg _

omit [Fintype α] [DecidableEq α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype (Mt s)] in
@[simp] theorem cylCancel_apply (y : Sx → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub))) :
    cylCancel ρ bsub y = -y := rfl

/-! ### The two sums over the cells of the blocks -/

variable (hc : IsFillingF ρ bsub hfill c)

include hc

/-! ### The inclusion of the preimage of `X`, in the coordinates of the model -/

/-! ### Property (B2) for the article's simultaneous substitution -/

end BlockFamily

end FiniteChains
