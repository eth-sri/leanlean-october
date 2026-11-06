module

public import ADR11.Computation.Lists
public import ADR11.MSC.Basic
/-!
# A verified computation of gene tree distributions

For a species tree whose shape is given by a `PTree` (a cluster code and the list of its
children), `PTree.rootedL` and `PTree.unrootedL` compute, by a program that the kernel can run,
the rooted and the unrooted gene tree distributions as lists of terms `CTerm`: a rational
coefficient, a monomial in the `e^{-len A}` (one factor per non-root cluster `A`, as a pair
(code of `A`, exponent)), and a family of clusters (a rooted gene tree, or the sides of the
splits of an unrooted one). `PTree.out_spec` and `PTree.unrootedL_spec` prove that the
computation is the multispecies coalescent model, whenever the tree shape is well formed for
the clusters of the species tree (`PTree.wfB`, decidable) and the computation succeeds.

## Main steps

* `kingmanTransition_eq_sum_range`: over a time `t`, Kingman's coalescent from a forest with
  `k ≥ 1` roots is `∑_{j < k} g_{k,k-j}(t) J^j`; `spectrum`: a computable spectral expansion as polynomials in `e^{-t}`.
* `kernelL_spec`: finite-time evolution and root absorption through a single population kernel.
* `forestDist_eq_iterSum`: unfolding `forestDist` at a cluster with any list of children.
* `PTree.out_spec`, `PTree.prodL_spec`: the recursion over the species tree.
-/

@[expose] public section

namespace ADR11.Computation

open Finset

abbrev Key := List (ℕ × ℕ)
abbrev Poly := Multiset (ℚ × Key)

/-! ### Kingman's coalescent over a finite time, along the jump chain -/

theorem kingmanTransition_eq_sum_range {L : Type*} [Fintype L] [DecidableEq L]
    {F : Family L} (hF : IsForest F) (hk : 1 ≤ #(roots F)) (t : ℝ)
    (G : Family L) :
    kingmanTransition t F G =
      ∑ j ∈ range #(roots F), spectrumValue #(roots F) (#(roots F) - j) t * (jumpMatrix ^ j) F G := by
  rw [kingmanTransition_apply hF]
  have hsupp {j : ℕ} (h : (jumpMatrix ^ j) F G ≠ 0) := (jumpMatrix_pow_support hF h).2.2.2
  rw [Finset.sum_eq_single (#(roots F) - #(roots G))]
  · by_cases hz : (jumpMatrix ^ (#(roots F) - #(roots G))) F G = 0
    · simp [hz]
    · have := hsupp hz
      congr 2 <;> split_ifs at this <;> omega
  · intro j hj hne
    have hz : (jumpMatrix ^ j) F G = 0 := by grind
    simp [hz]
  · intro h
    have hz : (jumpMatrix ^ (#(roots F) - #(roots G))) F G = 0 := by grind
    simp [hz]

/-! ### Weighted terms -/

/-- A term of a distribution: a rational coefficient, a monomial `∏ (e^{-len A})^e` given by the
list of pairs (code of `A`, `e`), and a family of clusters given by codes. -/
structure CTerm (m : ℕ) where
  coef : ℚ
  key : Key
  forest : Family (Fin m)

variable {m n a : ℕ} (len : Finset (Fin n) → ℝ)

noncomputable def weight (k : Key) : ℝ :=
  (k.map fun (c, e) => (e : ℝ) * len (decC n c)).sum

/-- The value of a monomial. -/
noncomputable def monoVal (k : Key) : ℝ := Real.exp (-weight len k)

/-- The weight of a term. -/
noncomputable def CTerm.val (τ : CTerm m) : ℝ :=
  τ.coef * monoVal len τ.key

@[simp] theorem monoVal_nil : monoVal len [] = 1 := by simp [monoVal, weight]

@[simp] theorem monoVal_cons (ae : ℕ × ℕ)
    (k : Key) :
    monoVal len (ae :: k) = Real.exp (-len (decC n ae.1)) ^ ae.2 * monoVal len k := by
  simp [monoVal, weight, Real.exp_add, ← Real.exp_nat_mul, mul_neg, mul_comm]

theorem monoVal_append (k₁ k₂ : Key) :
    monoVal len (k₁ ++ k₂) = monoVal len k₁ * monoVal len k₂ := by
  simp [monoVal, weight, List.sum_append, Real.exp_add, mul_comm]

/-! ### The population above a non-root cluster -/

/-- The terms produced from `τ` by a population of code `a`, when `τ.forest` has `k ≥ 2` roots. -/
def kernelL (m n a : ℕ) (τ : CTerm m) : Option (Multiset (CTerm m)) :=
  let k := #(roots τ.forest)
  if IsForest τ.forest then some (
    if decC n a = univ then
      (Lists.jumpL (k - 1) τ.forest).map fun q => ⟨τ.coef * q.1, τ.key, q.2⟩
    else if k ≤ 1 then {τ} else
      (Multiset.range k).bind fun j => (Multiset.ofList (spectrum k (k - j))).bind fun ce =>
        (Lists.jumpL j τ.forest).map fun q =>
          ⟨τ.coef * ce.1 * q.1, τ.key ++ (if ce.2 = 0 then [] else [(a, ce.2)]), q.2⟩)
  else none

theorem kernelL_spec {τ : CTerm m} {K : Multiset (CTerm m)}
    (h : kernelL m n a τ = some K) (G : Family (Fin m)) :
    τ.val len * populationKernel len (decC n a) τ.forest G =
      (K.map fun τ' => if τ'.forest = G then τ'.val len else 0).sum := by
  dsimp only [kernelL] at h
  split_ifs at h with hF hr h1
  · cases h
    simp only [populationKernel, hr, ite_true]
    rw [kingmanAbsorption_eq_jump hF,
      Lists.jump_spec _ _ hF, ← Multiset.sum_map_mul_left, Multiset.map_map]
    congr! 2
    simp only [Function.comp_apply, CTerm.val]
    split_ifs <;> push_cast <;> ring
  · cases h
    rw [populationKernel, ite_eq_right hr, kingmanTransition_of_card_roots_le_one hF h1]
    simp [mul_ite, eq_comm]
  · cases h
    rw [populationKernel, ite_eq_right hr, kingmanTransition_eq_sum_range hF (by omega)]
    simp only [Multiset.map_bind, Multiset.sum_bind, Multiset.map_map,
      Multiset.map_coe, Multiset.sum_coe, Function.comp_def]
    change τ.val len * ((Multiset.range #(roots τ.forest)).map fun j => _).sum = _
    rw [← Multiset.sum_map_mul_left]
    congr 2
    funext j
    rw [spectrumValue, Lists.jump_spec j _ hF G,
      ← List.sum_map_mul_right, ← List.sum_map_mul_left]
    congr! 2
    simp_rw [← Multiset.sum_map_mul_left]
    congr! 2
    simp only [CTerm.val, monoVal_append]
    split_ifs <;> simp_all <;> ring

/-! ### Unfolding the multispecies coalescent at a cluster with a list of children -/

theorem sum_collapse {β γ : Type*} [Fintype γ] [DecidableEq γ] (M : Multiset β) (key : β → γ)
    (v : β → ℝ) (ψ : γ → ℝ) :
    ∑ x, (M.map fun b => if key b = x then v b else 0).sum * ψ x =
      (M.map fun b => v b * ψ (key b)).sum := by
  induction M using Multiset.induction with
  | empty => simp
  | cons b M ih => simp [add_mul, sum_add_distrib, ih]

/-! ### The species tree recursion -/

/-- A rooted tree shape driving the recursion: the code of a cluster and the list of its
children. -/
inductive PTree where
  | node (a : ℕ) (cs : List PTree)

namespace PTree

/-- The code of the top cluster. -/
def code : PTree → ℕ
  | node a _ => a

end PTree

variable (m n : ℕ) (s : Fin m → Fin n)

mutual
/-- The terms of the distribution of the forest leaving the population above the top cluster of a
tree shape (lineages coded on `m` bits, taxa on `n` bits, sampling map `s`). -/
def PTree.out : PTree → Option (Multiset (CTerm m))
  | .node a cs => do
      flatMapO (kernelL m n a) (← PTree.prodL cs (sampledForest s (decC n a)))
/-- The terms of the joint distribution of the forests leaving the populations of the trees `cs`,
joined to the family of codes `S`. -/
def PTree.prodL : List PTree → Family (Fin m) → Option (Multiset (CTerm m))
  | [], S => some {⟨1, [], S⟩}
  | c :: cs, S => do
      flatMapO (fun τ => (PTree.prodL cs (τ.forest ∪ S)).map
        (Multiset.map fun τ' => ⟨τ.coef * τ'.coef, τ.key ++ τ'.key, τ'.forest⟩)) (← PTree.out c)
end

mutual
/-- A tree shape is well formed for the clusters `H` (taxa coded on `n` bits) if at every node the
children in `H` of the cluster are exactly the clusters of the children, without repetition, and
the children are proper clusters. -/
def PTree.wfB (H : Family (Fin n)) : PTree → Bool
  | .node a cs =>
    decide (childClusters H (decC n a) = (cs.map fun c => decC n c.code).toFinset) &&
      decide (cs.map fun c => decC n c.code).Nodup &&
      PTree.wfListB H cs
/-- `PTree.wfB` for a list of trees. -/
def PTree.wfListB (H : Family (Fin n)) : List PTree → Bool
  | [] => true
  | c :: cs => PTree.wfB H c && PTree.wfListB H cs
end

variable {m n s} (H : Family (Fin n)) (len : Finset (Fin n) → ℝ)

mutual
theorem PTree.out_spec : ∀ (T : PTree), T.wfB n H = true → ∀ M, T.out m n s = some M → ∀ G,
    forestDist H len s (decC n T.code) G =
      (M.map fun τ => if τ.forest = G then τ.val len else 0).sum
  | .node a cs, hwf, M, hM, G => by
    simp only [PTree.wfB, Bool.and_eq_true, decide_eq_true_eq] at hwf
    obtain ⟨⟨hC, hnd⟩, hwfl⟩ := hwf
    simp only [PTree.code]
    simp only [PTree.out] at hM
    obtain ⟨E, hE, hM⟩ := Option.bind_eq_some_iff.1 hM
    rw [forestDist, hC, PTree.prodL_spec cs hwfl hnd _ E hE (fun F => populationKernel len (decC n a) F G)]
    exact (sum_flatMapO hM _ _ fun τ _ K hK => (kernelL_spec len hK G).symm).symm
theorem PTree.prodL_spec : ∀ (cs : List PTree), PTree.wfListB n H cs = true →
    (cs.map fun c => decC n c.code).Nodup →
    ∀ S M, PTree.prodL m n s cs S = some M →
    ∀ φ : Family (Fin m) → ℝ, (∑ f : (cs.map fun c => decC n c.code).toFinset → Family (Fin m),
      (∏ B : (cs.map fun c => decC n c.code).toFinset, forestDist H len s B (f B)) * φ (univ.sup f ∪ S)) =
      (M.map fun τ => τ.val len * φ τ.forest).sum
  | [], _, _, S, M, hM, φ => by
    simp only [PTree.prodL, Option.some.injEq] at hM
    subst hM
    erw [List.toFinset_nil, Fintype.sum_unique]
    simp [CTerm.val]
  | c :: cs, hwf, hnd, S, M, hM, φ => by
    simp only [PTree.wfListB, Bool.and_eq_true] at hwf
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [PTree.prodL] at hM
    obtain ⟨Mc, hMc, hM⟩ := Option.bind_eq_some_iff.1 hM
    let l := cs.map fun c => decC n c.code
    have hB : decC n c.code ∉ l.toFinset := by simpa [l] using hnd.1
    let e := ((subtypeInsertEquivOption hB).arrowCongr (Equiv.refl (Family (Fin m)))).trans
      Equiv.piOptionEquivProd
    erw [List.toFinset_cons, Fintype.sum_equiv e _
      (fun p => forestDist H len s (decC n c.code) p.1 *
        ((∏ i : l.toFinset, forestDist H len s i (p.2 i)) * φ (univ.sup p.2 ∪ (p.1 ∪ S))))]
    · rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum, PTree.out_spec c hwf.1 Mc hMc]
      rw [sum_collapse]
      symm
      apply sum_flatMapO hM
      intro τ _ x hx
      obtain ⟨Mτ, hMτ, rfl⟩ := Option.map_eq_some_iff.1 hx
      rw [PTree.prodL_spec cs hwf.2 hnd.2 _ Mτ hMτ φ, Multiset.map_map,
        ← Multiset.sum_map_mul_left]
      congr! 2
      simp only [Function.comp_apply, CTerm.val, monoVal_append]
      push_cast
      ring
    · intro f
      conv_lhs =>
        arg 2; arg 1; arg 1
        rw [Finset.univ_eq_attach, Finset.attach_insert, Finset.sup_insert,
          Finset.sup_image, ← Finset.univ_eq_attach]
      rw [← (subtypeInsertEquivOption hB).symm.prod_comp]
      simp [Function.comp_def, Fintype.prod_option, e, Equiv.arrowCongr_apply, Equiv.piOptionEquivProd_apply,
        subtypeInsertEquivOption, mul_assoc, union_assoc, union_left_comm, l]

end

noncomputable def evalPoly {n : ℕ} (len : Finset (Fin n) → ℝ) (P : Poly) :
    ℝ :=
  (P.map fun p => (p.1 : ℝ) * monoVal len p.2).sum

/-- The terms contributing to the gene tree whose clusters have codes `u`. -/
def collect {m : ℕ} (M : Multiset (CTerm m)) (u : Family (Fin m)) : Poly :=
  M.bind fun τ => if unroot τ.forest = u then {(τ.coef, τ.key)} else 0

end ADR11.Computation
