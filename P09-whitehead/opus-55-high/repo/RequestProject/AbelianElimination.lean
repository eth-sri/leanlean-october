import RequestProject.ExponentCorrection
import RequestProject.Tac
noncomputable section


/-!
# Words in commuting elements, and the elimination step of Lemma 3.1

If the images `u i` of the generators of a free group pairwise commute, then the image of a
word depends only on its vector of exponent sums.  Consequently, if a family of words `r j`
maps to `1` and the exponent vectors of the `r j` span the whole lattice `ℤ^{(I)}`, then
every `u i` is trivial (`FiniteChains.eq_one_of_expCol_surjective`).

This is the elimination used twice in Section 3 of the paper: in Lemma 3.1 it turns the
relators `r_j(U) = ∏_i U_i^{M_{ij}}` of the reduced presentation of `Y_D`, together with
surjectivity of the exponent-sum matrix `M` of the acyclic core, into `U_i = [a_i, b_i] = 1`.
`RequestProject/InitialPair.lean` records the same step in the shape in which the paper
states it; the version proved here is the one used to compute the fundamental group of the
complex `Y_D` built in `RequestProject/InitialComplex.lean`.
-/

bwd

namespace FiniteChains

universe u v

variable {I : Type u} {H : Type v} [Group H]

/-- The vector of exponent sums of a word, as a homomorphism to the free abelian group on
the generators.  Its underlying function is `FiniteChains.expVec`. -/
def expVecHom : FreeGroup I →* Multiplicative (I →₀ ℤ) :=
  FreeGroup.lift fun i => Multiplicative.ofAdd (Finsupp.single i (1 : ℤ))

@[simp] theorem expVecHom_of (i : I) :
    Multiplicative.toAdd (expVecHom (FreeGroup.of i)) = Finsupp.single i 1 := by
  simp [expVecHom, FreeGroup.lift_apply_of]

/-- The column of the exponent-sum matrix belonging to the relator `r j`. -/
def expCol {J : Type*} (r : J → FreeGroup I) (j : J) :=
  Multiplicative.toAdd (expVecHom (r j))

/-- The two descriptions of the exponent vector of a word agree. -/
theorem expCol_eq_expVec [DecidableEq I] {J} (r : J → FreeGroup I) j :
    expCol r j = expVec (r j) := by
  rfl

section Commuting

variable (u : I → H) (hu : ∀ i k, Commute (u i) (u k))


end Commuting

/-- **The elimination step.**  Let the elements `u i` of a group commute pairwise, let each
word `r j` map to `1`, and let the exponent vectors of the `r j` span `ℤ^{(I)}`.  Then every
`u i` is trivial. -/
theorem eq_one_of_expCol_surjective (u : I → H) (hu : ∀ i k, Commute (u i) (u k))
    (r : J → FreeGroup I) (hrel : ∀ j, FreeGroup.lift u (r j) = 1)
    (hsurj : Function.Surjective (Finsupp.linearCombination ℤ (expCol r))) :
    ∀ i, u i = 1 := by
  classical
  set S : Set H := Set.range u with hS
  letI : CommGroup (Subgroup.closure S) :=
    Subgroup.closureCommGroupOfComm (k := S) (fun a ha b hb _ => by grind)
  set U : I → Subgroup.closure S := fun i => ⟨u i, Subgroup.subset_closure ⟨i, rfl⟩⟩ with hU
  -- the additive homomorphism `ℤ^{(I)} → A` sending `e_i` to `U i`
  set g : (I →₀ ℤ) →+ Additive (Subgroup.closure S) :=
    Finsupp.liftAddHom fun i =>
      zmultiplesHom _ (Additive.ofMul (U i)) with hg
  have hg_single : ∀ i n,
      Additive.toMul (g (Finsupp.single i n)) = U i ^ n := by
    simp_all
  -- the same map, read multiplicatively
  set Gm : Multiplicative (I →₀ ℤ) →* Subgroup.closure S :=
    { toFun := fun m => Additive.toMul (g m.toAdd)
      map_one' := by simp
      map_mul' := by simp } with hGm
  -- a word in pairwise commuting elements only depends on its exponent vector
  have key : Gm.comp expVecHom = FreeGroup.lift U := by
    aesop
  have hsub : ∀ w, (FreeGroup.lift U w)
      = FreeGroup.lift u w := by
    intro w
    have : ((Subgroup.closure S).subtype).comp (FreeGroup.lift U) = FreeGroup.lift u := by
      aesop
    exact congrArg (· w) this
  -- hence `g` kills every exponent vector of a relator
  have hcol : ∀ j, g (expCol r j) = 0 := by
    intro j
    have h1 : FreeGroup.lift U (r j) = 1 := by
      aesop
    have h2 : Gm (expVecHom (r j)) = 1 := by
      rw [← MonoidHom.comp_apply, key, h1]
    tauto
  -- and therefore the whole image of the exponent matrix
  have hzero : ∀ c, g (Finsupp.linearCombination ℤ (expCol r) c) = 0 := by
    intro c
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [AddMonoidHom.map_zsmul, hcol j, smul_zero]
  intro i
  cases' hsurj (Finsupp.single i 1) with c hc
  have h0 : g (Finsupp.single i (1)) = 0 := by grind
  simp_all
