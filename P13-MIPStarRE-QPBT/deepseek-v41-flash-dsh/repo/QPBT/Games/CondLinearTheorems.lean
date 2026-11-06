module

public import QPBT.Games.CondLinear
public import QPBT.Games.CondLinearTheorems.DirectSumSupport
public import QPBT.Games.CondLinearTheorems.Reindex

/-! # Structure and direct sums of conditionally linear functions

A conditionally linear map admits a prefix decomposition. Equal-level
representations on pairwise disjoint registers combine coordinatewise, and the
corresponding shared-seed distributions factor as products. A representation
may first be raised to a larger level by adjoining zero linear contributions.

## References

The source results are blueprint `lem:cl-kth`, `lem:cl-func-prod`, and
`lem:cl-dist-prod`, with paper origin
`references/qpbt-paper/05_conditionally_linear_functions.tex:150-379`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
variable {K ι : Type*}
variable [Field K] [Fintype ι] [DecidableEq ι]



/-- Raise a representation of a conditionally linear function by one level,
whose linear contribution is zero. -/
private def CondLinearTerm.raiseLevel  {ell : ℕ}
    (t : CondLinearTerm K (ι := ι) ell) : CondLinearTerm K (ι := ι) (ell + 1) :=
  .succ ∅ 0 (by simp) (fun _ => t)

@[simp]
private theorem CondLinearTerm.eval_raiseLevel {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {ell : ℕ}
    (t : CondLinearTerm K (ι := ι) ell) (x : ι → K) :
    CondLinearTerm.eval t.raiseLevel x = CondLinearTerm.eval t x := by
  simp [CondLinearTerm.raiseLevel, CondLinearTerm.eval]

/-- Raise a representation of a conditionally linear function by a specified
number of levels, each with zero linear contribution. -/
private def CondLinearTerm.raiseBy  :
    (d : ℕ) → {ell : ℕ} → CondLinearTerm K (ι := ι) ell →
      CondLinearTerm K (ι := ι) (ell + d)
  | 0, _, t => t
  | d + 1, _, t => (raiseBy d t).raiseLevel

@[simp]
private theorem CondLinearTerm.eval_raiseBy {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] (d : ℕ) {ell : ℕ}
    (t : CondLinearTerm K (ι := ι) ell) (x : ι → K) :
    CondLinearTerm.eval (CondLinearTerm.raiseBy d t) x = CondLinearTerm.eval t x := by
  induction d with
  | zero => rfl
  | succ d ih => simp [CondLinearTerm.raiseBy, ih]

/-- Prepend a first-level linear contribution, supported on one register, to a
family of residual conditionally linear maps indexed by its value. -/
private theorem IsCondLinearOn.cons {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {S S₁ : Finset ι} {ell : ℕ}
    (L₁ : (ι → K) →ₗ[K] (ι → K))
    (hS₁ : S₁ ⊆ S) (hSupport : ∀ x a, a ∉ S₁ → L₁ x a = 0)
    (R : (ι → K) → (ι → K) → (ι → K))
    (hR : ∀ y, IsCondLinearOn K (S \ S₁) ell (R y)) :
    IsCondLinearOn K S (ell + 1) (fun x =>
      L₁ (coordinateRestriction S₁ x) +
        R (L₁ (coordinateRestriction S₁ x)) x) := by
  classical
  choose t ht ht_eval using hR
  refine ⟨.succ S₁ L₁ hSupport t, ⟨hS₁, ht⟩, ?_⟩
  funext x
  change L₁ (coordinateRestriction S₁ x) +
      CondLinearTerm.eval (t (L₁ (coordinateRestriction S₁ x))) x = _
  rw [congrFun (ht_eval _) x]

private theorem coordinateRestriction_eq_self {K ι : Type*} [Field K]
    [DecidableEq ι] {S : Finset ι} {x : ι → K}
    (hx : ∀ a, a ∉ S → x a = 0) : coordinateRestriction S x = x := by
  ext a
  by_cases ha : a ∈ S
  · simp [coordinateRestriction, ha]
  · simp [coordinateRestriction, ha, hx a ha]

private theorem coordinateRestriction_add {K ι : Type*} [Field K]
    [DecidableEq ι] (S : Finset ι) (x y : ι → K) :
    coordinateRestriction S (x + y) =
      coordinateRestriction S x + coordinateRestriction S y := by
  ext a
  by_cases ha : a ∈ S <;> simp [coordinateRestriction, ha]

private theorem coordinateRestriction_eq_zero_of_disjoint {K ι : Type*} [Field K]
    [DecidableEq ι] {S T : Finset ι} (hST : Disjoint S T)
    {x : ι → K} (hx : ∀ a, a ∉ T → x a = 0) :
    coordinateRestriction S x = 0 := by
  ext a
  by_cases ha : a ∈ S
  · have haT := fun h => Finset.disjoint_left.mp hST ha h
    simp [coordinateRestriction, ha, hx a haT]
  · simp [coordinateRestriction, ha]

/-- Coordinate restriction as a linear endomorphism. -/
private def coordinateRestrictionLinear  (S : Finset ι) :
    (ι → K) →ₗ[K] (ι → K) where
  toFun := coordinateRestriction S
  map_add' := coordinateRestriction_add S
  map_smul' c x := by
    ext a
    by_cases ha : a ∈ S <;> simp [coordinateRestriction, ha]

/-- The value of the strict-prefix marginal preceding `k`. This is a
formalization-only auxiliary for blueprint
`lem:cl-kth`, paper
`references/qpbt-paper/05_conditionally_linear_functions.tex:150-178`. -/
def clPrefix  [Zero K] {ell : ℕ}
    (marginal : Fin ell → (ι → K) → (ι → K)) (k : Fin ell)
    (x : ι → K) : ι → K :=
  if _hk : k.val = 0 then 0
  else marginal ⟨k.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩ x

/-- Prefix-indexed decomposition data from `lem:cl-kth`. Factor spaces are
represented by their coordinate sets, matching the register-subspace encoding
used by `IsCondLinearOn`. Blueprint `lem:cl-kth`, paper
`references/qpbt-paper/05_conditionally_linear_functions.tex:150-178`. -/
structure CLData (K ι : Type*) [Field K] [Fintype ι] [DecidableEq ι]
    (ell : ℕ) (L : (ι → K) → (ι → K)) where
  /-- The marginal `L_{≤k}`. -/
  marginal : Fin ell → (ι → K) → (ι → K)
  /-- The factor register selected by a prefix value. -/
  factor : Fin ell → (ι → K) → Finset ι
  /-- The linear map selected by a prefix value. -/
  linear : Fin ell → (ι → K) → ((ι → K) →ₗ[K] (ι → K))
  /-- Each marginal has the corresponding conditionally linear level. -/
  marginal_cl : ∀ k, IsCondLinearOn K Finset.univ (k.val + 1) (marginal k)
  /-- The selected factor registers are pairwise disjoint. -/
  factor_disjoint : ∀ x i j, i ≠ j →
    Disjoint (factor i (clPrefix marginal i x)) (factor j (clPrefix marginal j x))
  /-- The selected factor registers cover all coordinates. -/
  factor_cover : ∀ x a, ∃ i, a ∈ factor i (clPrefix marginal i x)
  /-- Each selected linear map is supported on its factor register. -/
  linear_supported : ∀ k u x a, a ∉ factor k u → linear k u x a = 0
  /-- Each marginal is the sum of the preceding selected linear pieces. -/
  sum_formula : ∀ k x, marginal k x =
    ∑ i : Fin ell, if i.val ≤ k.val then
      linear i (clPrefix marginal i x)
        (coordinateRestriction (factor i (clPrefix marginal i x)) x) else 0
  /-- The final marginal is the original function. -/
  top : ∀ h : 0 < ell,
    marginal ⟨ell - 1, Nat.sub_lt h (by decide)⟩ = L

/-- Prefix decomposition data on a register `S`, refining the decomposition
in `lem:cl-kth`. -/
private structure CLDataOn (K ι : Type*) [Field K] [Fintype ι]
    [DecidableEq ι] (S : Finset ι) (ell : ℕ)
    (L : (ι → K) → (ι → K)) where
  marginal : Fin ell → (ι → K) → (ι → K)
  factor : Fin ell → (ι → K) → Finset ι
  linear : Fin ell → (ι → K) → ((ι → K) →ₗ[K] (ι → K))
  marginal_cl : ∀ k, IsCondLinearOn K S (k.val + 1) (marginal k)
  factor_subset : ∀ k u, factor k u ⊆ S
  factor_disjoint : ∀ x i j, i ≠ j →
    Disjoint (factor i (clPrefix marginal i x))
      (factor j (clPrefix marginal j x))
  factor_cover : ∀ x a, a ∈ S → ∃ i, a ∈ factor i (clPrefix marginal i x)
  linear_supported : ∀ k u x a, a ∉ factor k u → linear k u x a = 0
  sum_formula : ∀ k x, marginal k x =
    ∑ i : Fin ell, if i.val ≤ k.val then
      linear i (clPrefix marginal i x)
        (coordinateRestriction (factor i (clPrefix marginal i x)) x) else 0
  top : ∀ h : 0 < ell,
    marginal ⟨ell - 1, Nat.sub_lt h (by decide)⟩ = L

/-- Every marginal in support-relative decomposition data is supported on the
active register. -/
private theorem CLDataOn.marginal_eq_zero_of_not_mem {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {S : Finset ι} {ell : ℕ}
    {L : (ι → K) → (ι → K)} (d : CLDataOn K ι S ell L)
    (k : Fin ell) (x : ι → K) {a : ι} (ha : a ∉ S) :
    d.marginal k x a = 0 := by
  rw [d.sum_formula, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  split_ifs
  · exact d.linear_supported i _ _ a (fun hai => ha (d.factor_subset i _ hai))
  · rfl

/-- Every strict-prefix marginal in support-relative decomposition data is
supported on the active register. -/
private theorem CLDataOn.prefix_eq_zero_of_not_mem {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {S : Finset ι} {ell : ℕ}
    {L : (ι → K) → (ι → K)} (d : CLDataOn K ι S ell L)
    (k : Fin ell) (x : ι → K) {a : ι} (ha : a ∉ S) :
    clPrefix d.marginal k x a = 0 := by
  unfold clPrefix
  split_ifs
  · rfl
  · exact d.marginal_eq_zero_of_not_mem _ x ha

private theorem CondLinearTerm.eval_zero {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι]
    (t : CondLinearTerm K (ι := ι) 0) (x : ι → K) :
    CondLinearTerm.eval t x = 0 := by
  cases t
  rfl

/-- A one-level representation of a conditionally linear function has
support-relative prefix decomposition data. -/
private theorem CondLinearTerm.nonempty_clDataOn_one {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] (t : CondLinearTerm K (ι := ι) 1)
    {S : Finset ι} (ht : CondLinearTerm.supportedOn t S) :
    Nonempty (CLDataOn K ι S 1 (CondLinearTerm.eval t)) := by
  cases t with
  | @succ ell S₁ L₁ hSupport rest =>
      refine ⟨{
        marginal := fun _ => CondLinearTerm.eval (.succ S₁ L₁ hSupport rest)
        factor := fun _ _ => S
        linear := fun _ _ => L₁.comp (coordinateRestrictionLinear S₁)
        marginal_cl := ?_
        factor_subset := ?_
        factor_disjoint := ?_
        factor_cover := ?_
        linear_supported := ?_
        sum_formula := ?_
        top := ?_
      }⟩
      · intro k
        have hk : k = 0 := Subsingleton.elim _ _
        subst k
        exact ⟨.succ S₁ L₁ hSupport rest, ht, rfl⟩
      · intro k u
        exact Finset.Subset.rfl
      · intro x i j hij
        exact (hij (Subsingleton.elim i j)).elim
      · intro x a ha
        exact ⟨0, ha⟩
      · intro k u x a ha
        exact hSupport _ _ (fun haS₁ => ha (ht.1 haS₁))
      · intro k x
        have hk : k = 0 := Subsingleton.elim _ _
        simp [Fin.sum_univ_one, Fin.isValue, le_refl, ↓reduceIte]
        change CondLinearTerm.eval (.succ S₁ L₁ hSupport rest) x =
          L₁ (coordinateRestriction S₁ (coordinateRestriction S x))
        rw [coordinateRestriction_coordinateRestriction ht.1]
        change L₁ (coordinateRestriction S₁ x) +
            CondLinearTerm.eval
              (rest (L₁ (coordinateRestriction S₁ x))) x = _
        rw [CondLinearTerm.eval_zero]
        exact add_zero _
      · intro h
        rfl

/-- The first linear contribution in the inductive prefix decomposition. -/
private def clDataFirst 
    (S₁ : Finset ι) (L₁ : (ι → K) →ₗ[K] (ι → K))
    (x : ι → K) : ι → K :=
  L₁ (coordinateRestriction S₁ x)

/-- Add the first contribution to each marginal of residual decomposition
data. -/
private def clDataConsMarginal  {T : Finset ι} {ell : ℕ}
    {R : (ι → K) → (ι → K) → (ι → K)}
    (S₁ : Finset ι) (L₁ : (ι → K) →ₗ[K] (ι → K))
    (d : ∀ y, CLDataOn K ι T ell (R y)) :
    Fin (ell + 1) → (ι → K) → (ι → K) :=
  Fin.cases (clDataFirst S₁ L₁) fun k x =>
    clDataFirst S₁ L₁ x + (d (clDataFirst S₁ L₁ x)).marginal k x

/-- Select the first or residual factor register from a combined prefix. -/
private def clDataConsFactor  {T : Finset ι} {ell : ℕ}
    {R : (ι → K) → (ι → K) → (ι → K)}
    (S₁ : Finset ι) (d : ∀ y, CLDataOn K ι T ell (R y)) :
    Fin (ell + 1) → (ι → K) → Finset ι :=
  Fin.cases (fun _ => S₁) fun k u =>
    (d (coordinateRestriction S₁ u)).factor k (coordinateRestriction T u)

/-- Select the first or residual linear map from a combined prefix. -/
private def clDataConsLinear  {T : Finset ι} {ell : ℕ}
    {R : (ι → K) → (ι → K) → (ι → K)}
    (S₁ : Finset ι) (L₁ : (ι → K) →ₗ[K] (ι → K))
    (d : ∀ y, CLDataOn K ι T ell (R y)) :
    Fin (ell + 1) → (ι → K) → ((ι → K) →ₗ[K] (ι → K)) :=
  Fin.cases (fun _ => L₁.comp (coordinateRestrictionLinear S₁)) fun k u =>
    (d (coordinateRestriction S₁ u)).linear k (coordinateRestriction T u)

@[simp]
private theorem clDataConsMarginal_zero {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {T : Finset ι} {ell : ℕ}
    {R : (ι → K) → (ι → K) → (ι → K)}
    (S₁ : Finset ι) (L₁ : (ι → K) →ₗ[K] (ι → K))
    (d : ∀ y, CLDataOn K ι T ell (R y)) (x : ι → K) :
    clDataConsMarginal S₁ L₁ d 0 x = clDataFirst S₁ L₁ x := rfl

@[simp]
private theorem clDataConsMarginal_succ {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {T : Finset ι} {ell : ℕ}
    {R : (ι → K) → (ι → K) → (ι → K)}
    (S₁ : Finset ι) (L₁ : (ι → K) →ₗ[K] (ι → K))
    (d : ∀ y, CLDataOn K ι T ell (R y)) (k : Fin ell) (x : ι → K) :
    clDataConsMarginal S₁ L₁ d k.succ x =
      clDataFirst S₁ L₁ x +
        (d (clDataFirst S₁ L₁ x)).marginal k x := rfl

private theorem clPrefix_cons_succ {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {T : Finset ι} {ell : ℕ}
    {R : (ι → K) → (ι → K) → (ι → K)}
    (S₁ : Finset ι) (L₁ : (ι → K) →ₗ[K] (ι → K))
    (d : ∀ y, CLDataOn K ι T (ell + 1) (R y)) (k : Fin (ell + 1))
    (x : ι → K) :
    clPrefix (clDataConsMarginal S₁ L₁ d) k.succ x =
      clDataFirst S₁ L₁ x +
        clPrefix (d (clDataFirst S₁ L₁ x)).marginal k x := by
  cases k using Fin.cases with
  | zero => simp [clPrefix]
  | succ k =>
      change clDataConsMarginal S₁ L₁ d (Fin.castSucc k).succ x =
        clDataFirst S₁ L₁ x +
          (d (clDataFirst S₁ L₁ x)).marginal (Fin.castSucc k) x
      rfl

@[simp]
private theorem clDataConsFactor_zero {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {T : Finset ι} {ell : ℕ}
    {R : (ι → K) → (ι → K) → (ι → K)}
    (S₁ : Finset ι) (d : ∀ y, CLDataOn K ι T ell (R y)) (u : ι → K) :
    clDataConsFactor S₁ d 0 u = S₁ := rfl

@[simp]
private theorem clDataConsFactor_succ {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {T : Finset ι} {ell : ℕ}
    {R : (ι → K) → (ι → K) → (ι → K)}
    (S₁ : Finset ι) (d : ∀ y, CLDataOn K ι T ell (R y))
    (k : Fin ell) (u : ι → K) :
    clDataConsFactor S₁ d k.succ u =
      (d (coordinateRestriction S₁ u)).factor k (coordinateRestriction T u) := rfl

@[simp]
private theorem clDataConsLinear_zero {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {T : Finset ι} {ell : ℕ}
    {R : (ι → K) → (ι → K) → (ι → K)}
    (S₁ : Finset ι) (L₁ : (ι → K) →ₗ[K] (ι → K))
    (d : ∀ y, CLDataOn K ι T ell (R y)) (u : ι → K) :
    clDataConsLinear S₁ L₁ d 0 u =
      L₁.comp (coordinateRestrictionLinear S₁) := rfl

@[simp]
private theorem clDataConsLinear_succ {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {T : Finset ι} {ell : ℕ}
    {R : (ι → K) → (ι → K) → (ι → K)}
    (S₁ : Finset ι) (L₁ : (ι → K) →ₗ[K] (ι → K))
    (d : ∀ y, CLDataOn K ι T ell (R y)) (k : Fin ell) (u : ι → K) :
    clDataConsLinear S₁ L₁ d k.succ u =
      (d (coordinateRestriction S₁ u)).linear k (coordinateRestriction T u) := rfl

private theorem coordinateRestriction_clPrefix_cons_succ_left
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    {T : Finset ι} {ell : ℕ}
    {R : (ι → K) → (ι → K) → (ι → K)}
    (S₁ : Finset ι) (L₁ : (ι → K) →ₗ[K] (ι → K))
    (hSupport : ∀ x a, a ∉ S₁ → L₁ x a = 0)
    (d : ∀ y, CLDataOn K ι T (ell + 1) (R y))
    (hDisjoint : Disjoint S₁ T) (k : Fin (ell + 1)) (x : ι → K) :
    coordinateRestriction S₁
        (clPrefix (clDataConsMarginal S₁ L₁ d) k.succ x) =
      clDataFirst S₁ L₁ x := by
  rw [clPrefix_cons_succ, coordinateRestriction_add]
  have hfirst :=
    coordinateRestriction_eq_self (x := clDataFirst S₁ L₁ x) (hSupport _)
  have htail : coordinateRestriction S₁
      (clPrefix (d (clDataFirst S₁ L₁ x)).marginal k x) = 0 :=
    coordinateRestriction_eq_zero_of_disjoint hDisjoint
      (fun a ha =>
        (d (clDataFirst S₁ L₁ x)).prefix_eq_zero_of_not_mem k x ha)
  rw [hfirst, htail]
  exact add_zero _

private theorem coordinateRestriction_clPrefix_cons_succ_right
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    {T : Finset ι} {ell : ℕ}
    {R : (ι → K) → (ι → K) → (ι → K)}
    (S₁ : Finset ι) (L₁ : (ι → K) →ₗ[K] (ι → K))
    (hSupport : ∀ x a, a ∉ S₁ → L₁ x a = 0)
    (d : ∀ y, CLDataOn K ι T (ell + 1) (R y))
    (hDisjoint : Disjoint S₁ T) (k : Fin (ell + 1)) (x : ι → K) :
    coordinateRestriction T
        (clPrefix (clDataConsMarginal S₁ L₁ d) k.succ x) =
      clPrefix (d (clDataFirst S₁ L₁ x)).marginal k x := by
  rw [clPrefix_cons_succ, coordinateRestriction_add]
  have hfirst : coordinateRestriction T (clDataFirst S₁ L₁ x) = 0 :=
    coordinateRestriction_eq_zero_of_disjoint hDisjoint.symm (hSupport _)
  have htail :=
    coordinateRestriction_eq_self
      (fun a ha =>
        (d (clDataFirst S₁ L₁ x)).prefix_eq_zero_of_not_mem k x ha)
  rw [hfirst, htail]
  exact zero_add _

private theorem clDataConsFactor_prefix_succ
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    {T : Finset ι} {ell : ℕ}
    {R : (ι → K) → (ι → K) → (ι → K)}
    (S₁ : Finset ι) (L₁ : (ι → K) →ₗ[K] (ι → K))
    (hSupport : ∀ x a, a ∉ S₁ → L₁ x a = 0)
    (d : ∀ y, CLDataOn K ι T (ell + 1) (R y))
    (hDisjoint : Disjoint S₁ T) (k : Fin (ell + 1)) (x : ι → K) :
    clDataConsFactor S₁ d k.succ
        (clPrefix (clDataConsMarginal S₁ L₁ d) k.succ x) =
      (d (clDataFirst S₁ L₁ x)).factor k
        (clPrefix (d (clDataFirst S₁ L₁ x)).marginal k x) := by
  rw [clDataConsFactor_succ, coordinateRestriction_clPrefix_cons_succ_left S₁ L₁ hSupport d
    hDisjoint, coordinateRestriction_clPrefix_cons_succ_right S₁ L₁ hSupport d
    hDisjoint]
private theorem clDataConsLinear_prefix_succ
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    {T : Finset ι} {ell : ℕ}
    {R : (ι → K) → (ι → K) → (ι → K)}
    (S₁ : Finset ι) (L₁ : (ι → K) →ₗ[K] (ι → K))
    (hSupport : ∀ x a, a ∉ S₁ → L₁ x a = 0)
    (d : ∀ y, CLDataOn K ι T (ell + 1) (R y))
    (hDisjoint : Disjoint S₁ T) (k : Fin (ell + 1)) (x : ι → K) :
    clDataConsLinear S₁ L₁ d k.succ
        (clPrefix (clDataConsMarginal S₁ L₁ d) k.succ x) =
      (d (clDataFirst S₁ L₁ x)).linear k
        (clPrefix (d (clDataFirst S₁ L₁ x)).marginal k x) := by
  rw [clDataConsLinear_succ, coordinateRestriction_clPrefix_cons_succ_left S₁ L₁ hSupport d
    hDisjoint, coordinateRestriction_clPrefix_cons_succ_right S₁ L₁ hSupport d
    hDisjoint]
private theorem CondLinearTerm.nonempty_clDataOn_succ
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] {ell : ℕ}
    (S₁ : Finset ι) (L₁ : (ι → K) →ₗ[K] (ι → K))
    (hSupport : ∀ x a, a ∉ S₁ → L₁ x a = 0)
    (rest : (ι → K) → CondLinearTerm K (ι := ι) (ell + 1))
    {S : Finset ι}
    (ht : CondLinearTerm.supportedOn (.succ S₁ L₁ hSupport rest) S)
    (hd : ∀ y, Nonempty (CLDataOn K ι (S \ S₁) (ell + 1)
      (fun x => CondLinearTerm.eval (rest y) x))) :
    Nonempty (CLDataOn K ι S ((ell + 1) + 1)
      (CondLinearTerm.eval (.succ S₁ L₁ hSupport rest))) := by
  classical
  let d := fun y => Classical.choice (hd y)
  have hDisjoint : Disjoint S₁ (S \ S₁) := Finset.disjoint_sdiff
  refine ⟨{
    marginal := clDataConsMarginal S₁ L₁ d
    factor := clDataConsFactor S₁ d
    linear := clDataConsLinear S₁ L₁ d
    marginal_cl := ?_
    factor_subset := ?_
    factor_disjoint := ?_
    factor_cover := ?_
    linear_supported := ?_
    sum_formula := ?_
    top := ?_
  }⟩
  · intro k
    refine Fin.cases ?_ (fun i => ?_) k
    · refine ⟨.succ S₁ L₁ hSupport (fun _ => .zero), ⟨ht.1, fun _ => trivial⟩, ?_⟩
      funext x
      simp [CondLinearTerm.eval, clDataFirst]
    · rw [show clDataConsMarginal S₁ L₁ d i.succ =
          (fun x => clDataFirst S₁ L₁ x +
            (d (clDataFirst S₁ L₁ x)).marginal i x) by
          funext x
          rfl]
      simpa only [clDataFirst, Fin.val_succ, Nat.add_assoc] using
        (IsCondLinearOn.cons L₁ ht.1 hSupport
          (fun y x => (d y).marginal i x) (fun y => (d y).marginal_cl i))
  · intro k u
    refine Fin.cases ?_ (fun i => ?_) k
    · exact ht.1
    · exact ((d (coordinateRestriction S₁ u)).factor_subset i _).trans
          Finset.sdiff_subset
  · intro x i j hij
    cases i using Fin.cases with
    | zero =>
        cases j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j =>
            rw [clDataConsFactor_zero, clDataConsFactor_prefix_succ S₁ L₁ hSupport d hDisjoint]
            exact hDisjoint.mono_right
              ((d (clDataFirst S₁ L₁ x)).factor_subset j _)
    | succ i =>
        cases j using Fin.cases with
        | zero =>
            rw [clDataConsFactor_zero, clDataConsFactor_prefix_succ S₁ L₁ hSupport d hDisjoint]
            exact (hDisjoint.mono_right
              ((d (clDataFirst S₁ L₁ x)).factor_subset i _)).symm
        | succ j =>
            have hij' : i ≠ j := by
              intro h
              subst j
              exact hij rfl
            rw [clDataConsFactor_prefix_succ S₁ L₁ hSupport d hDisjoint, clDataConsFactor_prefix_succ S₁ L₁ hSupport d hDisjoint]
            exact (d (clDataFirst S₁ L₁ x)).factor_disjoint x i j hij'
  · intro x a ha
    by_cases haS₁ : a ∈ S₁
    · exact ⟨0, by simpa using haS₁⟩
    · have haTail := Finset.mem_sdiff.mpr ⟨ha, haS₁⟩
      obtain ⟨i, hai⟩ :=
        (d (clDataFirst S₁ L₁ x)).factor_cover x a haTail
      refine ⟨i.succ, ?_⟩
      rw [clDataConsFactor_prefix_succ S₁ L₁ hSupport d hDisjoint]
      exact hai
  · intro k u x a ha
    revert ha
    refine Fin.cases ?_ (fun i => ?_) k
    · intro ha
      exact hSupport _ _ ha
    · intro ha
      exact (d (coordinateRestriction S₁ u)).linear_supported i
          (coordinateRestriction (S \ S₁) u) x a ha
  · intro k x
    have hhead :
        clDataConsLinear S₁ L₁ d 0
            (clPrefix (clDataConsMarginal S₁ L₁ d) 0 x)
            (coordinateRestriction
              (clDataConsFactor S₁ d 0
                (clPrefix (clDataConsMarginal S₁ L₁ d) 0 x)) x) =
          clDataFirst S₁ L₁ x := by
      change L₁ (coordinateRestriction S₁ (coordinateRestriction S₁ x)) =
        L₁ (coordinateRestriction S₁ x)
      rw [coordinateRestriction_coordinateRestriction Finset.Subset.rfl]
    refine Fin.cases ?_ (fun j => ?_) k
    · rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, le_refl, ↓reduceIte, hhead]
      simp
    · rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Nat.zero_le, ↓reduceIte, hhead]
      rw [clDataConsMarginal_succ]
      congr 1
      rw [(d (clDataFirst S₁ L₁ x)).sum_formula j x]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hij : i.val ≤ j.val
      · have hsucc : i.succ.val ≤ j.succ.val := by
          simpa only [Fin.val_succ, Nat.succ_le_succ_iff] using hij
        rw [if_pos hsucc, if_pos hij, clDataConsLinear_prefix_succ S₁ L₁ hSupport d hDisjoint, clDataConsFactor_prefix_succ S₁ L₁ hSupport d hDisjoint]
      · have hsucc : ¬ i.succ.val ≤ j.succ.val := by
          simpa only [Fin.val_succ, Nat.succ_le_succ_iff] using hij
        rw [if_neg hsucc, if_neg hij]
  · intro h
    have hTail : 0 < ell + 1 := by omega
    let last : Fin (ell + 1) :=
      ⟨(ell + 1) - 1, Nat.sub_lt hTail (by decide)⟩
    have hlast :
        (⟨((ell + 1) + 1) - 1, Nat.sub_lt h (by decide)⟩ : Fin ((ell + 1) + 1)) =
          last.succ := by
      simp [last]
    funext x
    rw [hlast, clDataConsMarginal_succ, congrFun ((d (clDataFirst S₁ L₁ x)).top hTail) x]
    rfl

/-- Every positive-level supported representation of a conditionally linear
function admits support-relative prefix decomposition data. -/
private theorem CondLinearTerm.nonempty_clDataOn {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {ell : ℕ} (hEll : 1 ≤ ell)
    (t : CondLinearTerm K (ι := ι) ell) {S : Finset ι}
    (ht : CondLinearTerm.supportedOn t S) :
    Nonempty (CLDataOn K ι S ell (CondLinearTerm.eval t)) := by
  induction ell using Nat.strong_induction_on generalizing S with
  | h ell ih =>
      cases ell with
      | zero => omega
      | succ n =>
          cases n with
          | zero => exact CondLinearTerm.nonempty_clDataOn_one t ht
          | succ n =>
              cases t with
              | @succ ell S₁ L₁ hSupport rest =>
                  apply CondLinearTerm.nonempty_clDataOn_succ S₁ L₁ hSupport rest ht
                  intro y
                  exact ih (n + 1) (by omega) (by omega) (rest y) (ht.2 y)

/-- A map is `ell`-level conditionally linear exactly when it admits the
prefix decomposition of blueprint `lem:cl-kth`,
paper `references/qpbt-paper/05_conditionally_linear_functions.tex:150-262`. -/
theorem isCondLinear_iff_nonempty_clData {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {ell : ℕ} (hEll : 1 ≤ ell)
    (L : (ι → K) → (ι → K)) :
    IsCondLinear ell L ↔ Nonempty (CLData K ι ell L) := by
  constructor
  · rintro ⟨t, ht, ht_eval⟩
    rw [← ht_eval]
    obtain ⟨d⟩ := CondLinearTerm.nonempty_clDataOn hEll t ht
    exact ⟨{
      marginal := d.marginal
      factor := d.factor
      linear := d.linear
      marginal_cl := d.marginal_cl
      factor_disjoint := d.factor_disjoint
      factor_cover := fun x a => d.factor_cover x a (Finset.mem_univ a)
      linear_supported := d.linear_supported
      sum_formula := d.sum_formula
      top := d.top
    }⟩
  · rintro ⟨d⟩
    have hPos : 0 < ell := by omega
    let last : Fin ell := ⟨ell - 1, Nat.sub_lt hPos (by decide)⟩
    have hLast := d.marginal_cl last
    rw [d.top hPos] at hLast
    simpa only [IsCondLinear, last, Nat.sub_add_cancel hEll] using hLast

end MIPStarRE.QPBT
