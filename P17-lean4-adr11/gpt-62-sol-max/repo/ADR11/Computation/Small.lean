module
public import ADR11.Trees.Hierarchy
public import ADR11.MSC.Independent
public meta import Mathlib.Data.Multiset.Sort

@[expose] public section
namespace ADR11.Computation
open Finset Independent MonoidAlgebra
open scoped Independent

theorem sum_prod_sections {α β : Type*} [CommMonoid α] [CommSemiring β]
    (f : α →* β) (s : Multiset (Multiset α)) :
    ((Multiset.Sections s).map (fun a => f a.prod)).sum = (s.map fun a => (a.map f).sum).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp [Multiset.map_bind, Multiset.sum_bind, Multiset.map_map, ih,
      Multiset.sum_map_mul_left, Multiset.sum_map_mul_right]

variable {n : ℕ}
abbrev TreeOn (n : ℕ) := SpeciesTree (Fin n)

abbrev Cl (n : ℕ) := Finset (Fin n)
abbrev For (n : ℕ) := ClusterFamily (Fin n)

def decC (n c : ℕ) : Cl n := univ.filter fun i => c.testBit i

/-- Bit mask for a finite set of encoded objects. -/
def encoded {α : Type*} (f : α ↪ ℕ) : Finset α ↪ ℕ :=
  (mapEmbedding f).toEmbedding.trans equivBitIndices.symm.toEmbedding

def clusterCode (n : ℕ) : Cl n ↪ ℕ := encoded ⟨Fin.val, Fin.val_injective⟩

@[simp] private theorem decC_encC (A : Cl n) : decC n (clusterCode n A) = A := by
  ext i
  simp only [decC, mem_filter, mem_univ, true_and, ← Nat.mem_bitIndices, ← List.mem_toFinset]
  change i.val ∈ equivBitIndices (equivBitIndices.symm (A.map _)) ↔ _
  rw [Equiv.apply_symm_apply]
  exact mem_map' ⟨Fin.val, Fin.val_injective⟩

def codedHierarchy (n : ℕ) (cs : List ℕ) : For n :=
  hierarchyOf (cs.map (decC n)).toFinset

abbrev Expo := ℕ × ℕ
abbrev Monomial := Multiset Expo
scoped instance : CommMonoid Monomial := inferInstanceAs (CommMonoid (Multiplicative (Multiset Expo)))
abbrev Term (α : Type*) := ℚ × Monomial × α
abbrev Terms (α : Type*) := Multiset (Term α)

noncomputable def monoVal (len : Cl n → ℝ) (M : Monomial) :=
  (M.map fun p => Real.exp (-len (decC n p.1)) ^ p.2).prod

noncomputable def monoHom (len : Cl n → ℝ) : Monomial →* ℝ where
  toFun k := monoVal len k
  map_one' := rfl
  map_mul' a b := by simp [monoVal, show a * b = a + b from rfl]

noncomputable def termValue (len : Cl n → ℝ) {α : Type*} (t : Term α) : ℝ := t.1 * monoHom len t.2.1

private noncomputable def representation (len : Cl n → ℝ) {α : Type*} [CommMonoid α] : Term α →* MonoidAlgebra ℝ α where
  toFun t := single t.2.2 (termValue len t)
  map_one' := by simp [termValue, MonoidAlgebra.one_def]
  map_mul' s t := by simp [termValue, single_mul_single, mul_assoc, mul_left_comm, mul_comm]

noncomputable def prob {α : Type*} [DecidableEq α] (len : Cl n → ℝ) (M : Terms α) (b : α) : ℝ :=
  (M.map fun t => if t.2.2 = b then termValue len t else 0).sum

private theorem law_prob {α : Type*} [Finite α] [DecidableEq α] [CommMonoid α] (len : Cl n → ℝ) (M : Terms α) :
    law (prob len M) = (M.map (representation len)).sum := by
  ext G
  change _ = Finsupp.applyAddHom G (MonoidAlgebra.coeffAddEquiv ((M.map (representation len)).sum))
  simp [law, map_multiset_sum, representation, prob, Multiset.map_map, Function.comp_def, Finsupp.single_apply]

private theorem sum_prob {α : Type*} [Fintype α] [DecidableEq α] (len : Cl n → ℝ) (M : Terms α) (w : α → ℝ) :
    ∑ a, prob len M a * w a = (M.map fun t => termValue len t * w t.2.2).sum := by
  simp_rw [prob, ← Multiset.sum_map_mul_right, ← Multiset.sum_map_sum, ite_mul, zero_mul]
  simp

/-- Compose weighted histories, recording each path and the product of its weights. -/
def bindT {α β : Type*} (M : Terms α) (f : α → Terms β) : Terms β :=
  M.bind fun t => (f t.2.2).map fun u => (t.1 * u.1, t.2.1 * u.2.1, u.2.2)

private theorem prob_bind {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (len : Cl n → ℝ) (M : Terms α) (f : α → Terms β) (b : β) :
    prob len (bindT M f) b = ∑ a, prob len M a * prob len (f a) b := by
  rw [sum_prob]
  simp [prob, bindT, Multiset.map_bind, Multiset.sum_bind, ← Multiset.sum_map_mul_left,
    termValue, mul_ite, mul_assoc, mul_left_comm]

private theorem prob_map {α : Type*} [DecidableEq α] (len : Cl n → ℝ) (M : Multiset α)
    (c : ℚ) (m : Monomial) (b : α) :
    prob len (M.map fun a => (c, m, a)) b = (c : ℝ) * monoHom len m * M.count b := by
  induction M using Multiset.induction_on with
  | empty => simp [prob]
  | cons a M ih =>
    by_cases h : a = b <;> simp_all [prob, termValue, eq_comm (a := b), mul_add, add_comm]

def mono (A : Cl n) (e : ℕ) : Monomial :=
  if e = 0 then 1 else {(clusterCode n A, e)}

@[simp] private theorem monoHom_mono (len : Cl n → ℝ) (A : Cl n) (e : ℕ) :
    monoHom len (mono A e) = Real.exp (-len A) ^ e := by
  by_cases h : e = 0 <;> simp [mono, monoHom, monoVal, h, show (1 : Monomial) = 0 from rfl]

/-- Histories for a finite branch or the absorbing root population. -/
def populationTerms (A : Cl n) (F : For n) : Terms (For n) :=
  let k := deathRank F
  if A = univ then (mergeHistories (k - 1) F).map fun G => (tavareRat k 1 1, 1, G) else
    (Icc 1 k).val.bind fun j => (Icc j k).val.bind fun i =>
      (mergeHistories (k - j) F).map fun G => (tavareRat k j i, mono A (i.choose 2), G)

private theorem prob_pop (len : Cl n → ℝ) (A : Cl n) {F : For n} (hF : IsForest F) (G : For n) :
    prob len (populationTerms A F) G = populationKernel len A F G := by
  by_cases h : A = univ
  · simp [populationTerms, populationKernel, h, prob_map, kingmanAbsorption_apply hF, mergeCount]
  rw [populationTerms, populationKernel, ite_eq_right h, ite_eq_right h, kingmanTransition_eq_sum_Icc hF]
  simp only [prob, Multiset.map_bind, Multiset.sum_bind, pathWeight, spectralMix, sum_eq_multiset_sum,
    ← Multiset.sum_map_mul_right]
  simp only [← prob.eq_1, prob_map, monoHom_mono, mergeCount, tavareRat_cast,
    ← Real.exp_nat_mul, rate, neg_mul, mul_comm]

/-- The species-tree recursion, enumerating only the possible histories rather than all states. -/
def distTerms (H : For n) : ℕ → Cl n → Terms (For n)
  | 0, _ => 0
  | k + 1, A =>
    let S : Term (For n) := (1, 1, sampledForest id A)
    let C := maximalClusters (H.filter (· ⊂ A))
    bindT ((Multiset.Sections (C.val.map (distTerms H k))).map fun m => S * m.prod)
      (populationTerms A)

private theorem prob_dist {H : For n} (hH : IsHierarchy H) (len : Cl n → ℝ) (k : ℕ) (A : Cl n)
    (hk : #A < k) (G : For n) : prob len (distTerms H k A) G = forestDist H len id A G := by
  induction k generalizing A G with
  | zero => omega
  | succ k ih =>
    let C := childClusters H A
    let S : Term (For n) := (1, 1, sampledForest id A)
    let E := (Multiset.Sections (C.val.map (distTerms H k))).map fun m => S * m.prod
    have hE : law (prob len E) = law (enteringDist H len id A) := by
      rw [law_prob, law_entering]
      simp only [E, Multiset.map_map, Function.comp_def, map_mul, Multiset.sum_map_mul_left,
        sum_prod_sections, ← prod_eq_multiset_prod]
      rw [show representation len S = single (sampledForest id A) 1 by simp [S, representation, termValue]]
      congr 1
      refine prod_congr rfl fun B hB => ?_
      rw [← law_prob]
      exact congrArg law (funext (ih B (by have := card_lt_card (child_lt hB); omega)))
    rw [distTerms, maximalClusters_eq, ← children_as_roots, prob_bind]
    change (∑ F, prob len E F * _) = _
    rw [law_injective hE, forestDist_eq]
    exact sum_mul_congr fun F _ hF => prob_pop len A (enteringDist_support hH len id hF).1 G

def smallTerms (n : ℕ) (cs : List ℕ) := distTerms (codedHierarchy n cs) (n + 1) univ

def smallTable (n : ℕ) (cs : List ℕ) : Terms ℕ :=
  (smallTerms n cs).map fun t => (t.1, t.2.1, encoded (clusterCode n) (unroot t.2.2))

theorem dist_small_poly {n : ℕ} (σ : TreeOn n) {cs : List ℕ}
    (hσ : σ.clusters = codedHierarchy n cs) (U : For n) :
    σ.unrootedDist id U = prob σ.length (smallTable n cs) (encoded (clusterCode n) U) := by
  unfold smallTable prob
  rw [Multiset.map_map]
  simp only [Function.comp_def, (encoded (clusterCode n)).injective.eq_iff]
  have h := sum_prob σ.length (smallTerms n cs) (fun F => if unroot F = U then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at h
  erw [← h]
  simp [smallTerms, SpeciesTree.unrootedDist, SpeciesTree.rootedDist, hσ,
    prob_dist (hσ ▸ σ.isHierarchy) σ.length (n + 1) univ (by simp)]

end ADR11.Computation
public meta section

open Lean Elab Tactic in
/-- Compute a closed polynomial in the evaluator, then check the equality in the kernel. -/
elab "compute_table" : conv => withMainContext do
  let l ← instantiateMVars (← Conv.getLhs)
  let stx ← runTermElab (Term.exprToSyntax l)
  let r ← elabTerm (← `(term| eval% $stx)) none
  let h ← elabTermEnsuringType (← `(term| by decide +kernel)) (some (← Meta.mkEq l r))
  Conv.updateLhs r h


open Lean.Parser.Tactic ADR11.Computation in
/-- Evaluate the common finite table, then prove each requested reading by polynomial arithmetic. -/
macro "verify_readings " h:ident i:ident " [" extra:simpLemma,* "]" : tactic => do
  let h ← `(term| $h:ident)
  let i ← `(term| $i:ident)
  `(tactic| fin_cases $h:term <;> (conv_lhs => arg 2; compute_table) <;> fin_cases $i:term <;>
    simp (config := {decide := true}) only [Multiset.insert_eq_cons, ← Multiset.cons_zero,
      prob, termValue, monoHom, MonoidHom.coe_mk, OneHom.coe_mk, monoVal,
      Multiset.map_cons, Multiset.map_zero, Multiset.sum_cons, Multiset.sum_zero, Multiset.prod_cons,
      Multiset.prod_zero, Prod.fst, Prod.snd, ite_true, ite_false, neg_zero, Real.exp_zero,
      Nat.reduceSub, Nat.reducePow, Fin.val_mk, $extra,*] <;> push_cast <;> ring)
