module

public import QPBT.Games.CondLinear

/-!
# Reindexing of conditionally linear functions

A conditionally linear function of one register space transports along an
injective map of index types.  The transported function restricts a coefficient
vector to the registers named by that map, applies the original function, and
extends the result by zero outside the image; it is conditionally linear at the
same level on the full register.  In the one-level case the predicate holds of
every linear map of the ambient coefficient space, which is the converse
direction of the remark following `def:cl-func`.

## References

The source definition is `def:cl-func` in
`blueprint/src/chapter/ch12_qpbt_games.tex`, with paper origin
`references/qpbt-paper/05_conditionally_linear_functions.tex:35-57`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

/-- Transport a linear map of coefficient vectors along a reindexing `f` of
registers: restrict a vector to the registers named by `f`, apply the map, and
extend the result by zero outside the image of `f`.  This is the composition of
restriction along `f` with `Function.ExtendByZero.linearMap`, named here for the
reindexing of `def:cl-func`. -/
noncomputable def reindexLinearMap {K κ ι : Type*} [Field K] (f : κ → ι)
    (L : (κ → K) →ₗ[K] (κ → K)) : (ι → K) →ₗ[K] (ι → K) :=
  (Function.ExtendByZero.linearMap K f).comp (L.comp (LinearMap.funLeft K K f))

@[simp]
theorem reindexLinearMap_apply {K κ ι : Type*} [Field K] (f : κ → ι)
    (L : (κ → K) →ₗ[K] (κ → K)) (x : ι → K) :
    reindexLinearMap f L x = Function.extend f (L fun k => x (f k)) 0 :=
  rfl

/-- The reindexing of a linear map supported on a register vanishes off the
image of that register, so it satisfies the support condition of the successor
constructor of a representation of a conditionally linear function. -/
theorem reindexLinearMap_apply_eq_zero {K κ ι : Type*} [Field K] [DecidableEq ι]
    {f : κ → ι} (hf : Function.Injective f) {S₁ : Finset κ}
    {L₁ : (κ → K) →ₗ[K] (κ → K)} (hL : ∀ x i, i ∉ S₁ → L₁ x i = 0)
    (x : ι → K) (i : ι) (hi : i ∉ S₁.image f) :
    reindexLinearMap f L₁ x i = 0 := by
  rw [reindexLinearMap_apply]
  by_cases hex : ∃ k, f k = i
  · obtain ⟨k, rfl⟩ := hex
    have hk : k ∉ S₁ := fun hk => hi (Finset.mem_image_of_mem f hk)
    rw [hf.extend_apply]
    exact hL _ k hk
  · rw [Function.extend_apply' _ _ _ hex]
    rfl

/-- Transport a representation of a conditionally linear function along an
injective reindexing of registers; the linear contribution of each level is
reindexed by `reindexLinearMap` and its register is carried along by the image
under `f`. -/
noncomputable def CondLinearTerm.reindex {K κ ι : Type*} [Field K]
    [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] {f : κ → ι} (hf : Function.Injective f) :
    {ell : ℕ} → CondLinearTerm K (ι := κ) ell → CondLinearTerm K (ι := ι) ell
  | _, .zero => .zero
  | _, .succ S₁ L₁ hL rest =>
      .succ (S₁.image f) (reindexLinearMap f L₁)
        (fun x i hi => reindexLinearMap_apply_eq_zero hf hL x i hi)
        (fun y => CondLinearTerm.reindex hf (rest fun k => y (f k)))

end MIPStarRE.QPBT
