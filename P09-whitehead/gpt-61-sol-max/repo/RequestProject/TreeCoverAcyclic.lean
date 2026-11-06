import Mathlib.Tactic

import RequestProject.CoverComplexFinsupp
import RequestProject.TreeCover

/-!
# The cover of `K` is acyclic when the cover of the collapsed presentation complex is

`RequestProject/TreeCover.lean` constructs, for a spanning tree `T` of a two-complex `K` and a
normal subgroup `N ◁ F(E ∖ T)` containing the relators, a connected regular covering
`treeCover T N hN → K` with deck group `Q = F(E ∖ T)/N`.  Collapsing the tree identifies its
cellular chain complex with that of the cover `coverComplex N (treeRel T) hN` of the
presentation complex, up to the tree edges, which carry no homology: this file proves that the
cover of `K` is acyclic as soon as the cover of the presentation complex is
(`treeCover_isAcyclic`).

The comparison is given by the chain maps

* `piV`, which forgets the vertex of `K` (the vertices of `treeCover` are `Q × V`, those of the
  presentation cover are `Q`);
* `piE`, which deletes the tree edges;
* the identity on two-cells, the two covers having the same two-cells `Q × F`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.SpanningTree




variable {K : Complex2.{u}} (T : SpanningTree K)
variable (N : Subgroup (FreeGroup (NonTree T))) [N.Normal]

/-! ### The letters of a path outside the tree -/

open Classical in
/-- The word in the non-tree edges spelled by an edge path, as a list of letters. -/
noncomputable def letters : List (K.E × Bool) → List (NonTree T × Bool)
  | [] => []
  | g :: L => if h : T.isTree g.1 then letters L else (⟨g.1, h⟩, g.2) :: letters L

variable {T}

@[simp] theorem letters_nil : letters T [] = [] := rfl

variable {g : K.E × Bool}
theorem letters_cons_tree  (h : T.isTree g.1) (L : List (K.E × Bool)) :
    letters T (g :: L) = letters T L := by
  simp [letters, h]

theorem letters_cons_nontree  (h : ¬ T.isTree g.1) (L : List (K.E × Bool)) :
    letters T (g :: L) = (⟨g.1, h⟩, g.2) :: letters T L := by
  simp [letters, h]

variable (L : List (K.E × Bool))
/-- The list of non-tree letters spells the word of the path. -/
theorem mk_letters  :
    FreeGroup.mk (letters T L) = pathWord T L := by
  classical
  induction L with
  | nil => rfl
  | cons g L ih =>
      classical aesop (add simp [letters_cons_tree, pathWord_cons, germWord_of_isTree, letters_cons_nontree, mk_cons_false, germWord, NonTree, mk_cons_true])

/-! ### The comparison maps on chains -/

theorem germQ_eq_one_of_isTree  (h : T.isTree g.1) : germQ T N g = 1 := by
  show QuotientGroup.mk (germWord T g) = 1
  rw [germWord_of_isTree T h]
  rfl

variable {e : K.E}
omit [N.Normal] in
theorem germQ_true_eq_qof  (h : ¬ T.isTree e) :
    germQ T N (e, true) = qof N (⟨e, h⟩ : NonTree T) := by
  show QuotientGroup.mk (germWord T (e, true)) = _
  rw [show germWord T (e, true) = FreeGroup.of (⟨e, h⟩ : NonTree T) by simp [germWord, h]]
  rfl

theorem germQ_false_eq_qof_inv  (h : ¬ T.isTree e) :
    germQ T N (e, false) = (qof N (⟨e, h⟩ : NonTree T))⁻¹ := by
  classical simp_all [FiniteChains.Comb.SpanningTree.germQ_false_eq_inv, FiniteChains.Comb.SpanningTree.germQ_true_eq_qof]

variable (T)

open Classical in
/-- Deleting the tree edges: the comparison map on one-chains. -/
noncomputable def piE  :=
  Finsupp.linearCombination ℤ (fun x : CovQ T N × K.E =>
    if h : T.isTree x.2 then 0 else Finsupp.single (x.1, (⟨x.2, h⟩ : NonTree T)) (1 : ℤ))

/-- Forgetting the vertex of `K`: the comparison map on zero-chains. -/
noncomputable def piV : ((CovQ T N × K.V) →₀ ℤ) →ₗ[ℤ] ((CovQ T N) →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ Prod.fst

/-- Putting a vertex of the presentation cover at the root of its tree. -/
noncomputable def iotaV : ((CovQ T N) →₀ ℤ) →ₗ[ℤ] ((CovQ T N × K.V) →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun q => (q, T.root))

variable {T}

section
omit [N.Normal]
variable {x : CovQ T N × K.E}
theorem piE_single_tree  (h : T.isTree x.2) (n : ℤ) :
    piE T N (Finsupp.single x n) = 0 := by simp_all [piE]

theorem piE_single_nontree  (h : ¬ T.isTree x.2) (n : ℤ) :
    piE T N (Finsupp.single x n) = Finsupp.single (x.1, (⟨x.2, h⟩ : NonTree T)) n := by simp_all [piE]

@[simp] theorem piV_single (x : CovQ T N × K.V) (n : ℤ) :
    piV T N (Finsupp.single x n) = Finsupp.single x.1 n := by
  rw [piV]
  simp 

@[simp] theorem iotaV_single (q : CovQ T N) (n : ℤ) :
    iotaV T N (Finsupp.single q n) = Finsupp.single (q, T.root) n := by simp_all [iotaV]
end

/-- **Deleting the tree edges from a lifted path** gives the lift of the word it spells. -/
theorem piE_pathChain_liftK  (q : CovQ T N) :
    piE T N (pathChain (liftK T N L q)) = pathChain (liftPath (letters T L) q) := by
  classical
  induction L generalizing q with
  | nil => simp [pathChain]
  | cons g L ih =>
      obtain ⟨e, b⟩ := g
      by_cases h : T.isTree e
      · have hq : q * germQ T N (e, b) = q := by
          simp_all [germQ_eq_one_of_isTree]
        have hsnd : (liftGerm T N q (e, b)).2 = b := by cases b <;> rfl
        have hfst : (liftGerm T N q (e, b)).1.2 = e := by cases b <;> rfl
        have hz  :=
          piE_single_tree (N := N) (x := (liftGerm T N q (e, b)).1) (by rw [hfst]; exact h) 1
        rw [liftK_cons, pathChain_cons, map_add, letters_cons_tree (g := (e, b)) h, hq, ih q,
          hsnd]
        cases b
        · simp [hz]
        · simp [hz]
      · rw [liftK_cons, pathChain_cons, map_add, letters_cons_nontree (g := (e, b)) h]
        cases b
        · have hlift : liftGerm T N q (e, false) =
              ((q * germQ T N (e, false), e), false) := rfl
          rw [hlift]
          simp only [Bool.false_eq_true, if_false, map_neg]
          aesop (add simp [FiniteChains.Comb.SpanningTree.piE_single_nontree, FiniteChains.Comb.SpanningTree.germQ_false_eq_qof_inv])
        aesop (add simp [liftGerm, piE_single_nontree, germQ_true_eq_qof])

/-! ### The comparison maps are chain maps -/

variable [Fintype (NonTree T)] [DecidableEq (NonTree T)]

omit [Fintype (NonTree T)] in
/-- The chain of a lifted word depends only on the free-group element it spells. -/
theorem pathChain_liftPath_congr {L L' : List (NonTree T × Bool)}
    (h : FreeGroup.mk L = FreeGroup.mk L') (q : CovQ T N) :
    pathChain (liftPath (Nsub := N) L q) = pathChain (liftPath (Nsub := N) L' q) := by
  apply (fsCoords N (NonTree T)).injective
  ext <;> simp_all [fsCoords_pathChain_liftPath_apply]

variable (hN : ∀ f, treeRel T f ∈ N)

section
omit [Fintype (NonTree T)]
/-- **The comparison map is a chain map in degree two**: the two covers have the same
two-cells, and deleting the tree edges from the attaching path of a two-cell of the cover of
`K` gives the attaching path of the corresponding two-cell of the cover of the presentation
complex. -/
theorem piE_bdry2 (u : (CovQ T N × K.F) →₀ ℤ) :
    piE T N (bdry2 (treeCover T N hN) u) = bdry2 (coverComplex N (treeRel T) hN) u := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u₁ u₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]
  | single x n =>
      obtain ⟨q, f⟩ := x
      rw [bdry2_single, bdry2_single, map_smul]
      show n • piE T N (pathChain (liftK T N (K.att f) q)) = _
      rw [piE_pathChain_liftK]
      congr 1
      refine pathChain_liftPath_congr (N := N) ?_ q
      rw [mk_letters, FreeGroup.mk_toWord]
      rfl

/-- **The comparison map is a chain map in degree one.** -/
theorem piV_bdry1 (c : (CovQ T N × K.E) →₀ ℤ) :
    piV T N (bdry1 (treeCover T N hN) c) = bdry1 (coverComplex N (treeRel T) hN) (piE T N c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => simp_all
  | single x n =>
      obtain ⟨q, e⟩ := x
      rw [bdry1_single]
      by_cases h : T.isTree e
      · rw [piE_single_tree (N := N) (x := (q, e)) h n, map_zero]
        have hg  := germQ_eq_one_of_isTree (N := N) (g := (e, true)) h
        show piV T N (n • (Finsupp.single (covTgt T N (q, e)) (1 : ℤ)
          - Finsupp.single (covSrc T N (q, e)) (1 : ℤ))) = 0
        rw [map_smul, map_sub, piV_single, piV_single]
        show n • (Finsupp.single (covTgt T N (q, e)).1 (1 : ℤ)
          - Finsupp.single (covSrc T N (q, e)).1 (1 : ℤ)) = 0
        show n • (Finsupp.single (q * germQ T N (e, true)) (1 : ℤ)
          - Finsupp.single q (1 : ℤ)) = 0
        rw [hg, mul_one, sub_self, smul_zero]
      · rw [piE_single_nontree (N := N) (x := (q, e)) h n, bdry1_single]
        show piV T N (n • (Finsupp.single (covTgt T N (q, e)) (1 : ℤ)
          - Finsupp.single (covSrc T N (q, e)) (1 : ℤ))) = _
        rw [map_smul, map_sub, piV_single, piV_single]
        show n • (Finsupp.single (covTgt T N (q, e)).1 (1 : ℤ)
          - Finsupp.single (covSrc T N (q, e)).1 (1 : ℤ)) = _
        show n • (Finsupp.single (q * germQ T N (e, true)) (1 : ℤ)
          - Finsupp.single q (1 : ℤ)) = _
        rw [germQ_true_eq_qof (N := N) h]

/-- The augmentations agree. -/
theorem augC_piV (c : (CovQ T N × K.V) →₀ ℤ) :
    augC (coverComplex N (treeRel T) hN) (piV T N c) = augC (treeCover T N hN) c := by
  induction c using Finsupp.induction_linear <;> simp_all [augC]
end

/-! ### Contracting the tree and lifting the generators -/

variable (T)

/-- The loop of `K` at the root carried by a non-tree edge. -/
noncomputable def loopPath (ε : NonTree T)  :=
  conjPath T [((ε : K.E), true)] (K.src (ε : K.E)) (K.tgt (ε : K.E))

/-- Lifting the loops of the generators: a section of the comparison map on one-chains. -/
noncomputable def sectionE  :=
  Finsupp.linearCombination ℤ (fun x : CovQ T N × NonTree T =>
    pathChain (liftK T N (loopPath T x.2) x.1))

variable {T}

section
omit [Fintype (NonTree T)] [DecidableEq (NonTree T)]
theorem isPath_loopPath (ε : NonTree T) :
    IsPath K.src K.tgt (loopPath T ε) T.root T.root :=
  conjPath_isLoop T (isPath_single _)

theorem pathWord_loopPath (ε : NonTree T) : pathWord T (loopPath T ε) = FreeGroup.of ε := by
  rw [loopPath, conjPath, pathWord_append, pathWord_append, pathWord_treePath,
    pathWord_revPath, pathWord_treePath]
  simp [pathWord, germWord, dif_neg ε.2]
end

omit [N.Normal] [Fintype (NonTree T)] [DecidableEq (NonTree T)] in
theorem wordQ_loopPath (ε : NonTree T) : wordQ T N (loopPath T ε) = qof N ε := by
  show QuotientGroup.mk (pathWord T (loopPath T ε)) = _
  rw [pathWord_loopPath]
  rfl

variable (hN : ∀ f, treeRel T f ∈ N)

omit [Fintype (NonTree T)] in
/-- **Lifting the generators**: the section is a chain homotopy inverse in degree one. -/
theorem bdry1_sectionE (u : (CovQ T N × NonTree T) →₀ ℤ) :
    bdry1 (treeCover T N hN) (sectionE T N u)
      = iotaV T N (bdry1 (coverComplex N (treeRel T) hN) u) := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u₁ u₂ h₁ h₂ => simp_all
  | single x n =>
      obtain ⟨q, ε⟩ := x
      have hpath := liftK_isPath (T := T) (N := N) (isPath_loopPath (T := T) ε) q
      rw [wordQ_loopPath (N := N)] at hpath
      rw [sectionE, Finsupp.linearCombination_single, map_smul, bdry1_single]
      have hb  :=
        bdry1_pathChain_of_isPath (X := treeCover T N hN) hpath
      rw [hb, map_smul, map_sub, iotaV_single, iotaV_single]

/-! ### One-cycles supported on the tree vanish -/

/-- The coefficient of a boundary at a vertex. -/
theorem bdry1_apply (X : Complex2.{u}) (z : X.E →₀ ℤ) (w : X.V) :
    bdry1 X z w = ∑ x ∈ z.support, z x *
      ((Finsupp.single (X.tgt x) (1 : ℤ)) w - (Finsupp.single (X.src x) (1 : ℤ)) w) := by
  classical
  rw [bdry1, Finsupp.linearCombination_apply, Finsupp.sum]
  simp_all

variable (he : T.isTree e)
include he in
/-- The non-root vertex whose tree edge is the given tree edge. -/
noncomputable def treeTop    :=
  ((T.isTree_iff e).1 he).choose

include he in
omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] in
abbrev treeTop_ne_root    :=
  ((T.isTree_iff e).1 he).choose_spec.choose

include he in
omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] in
abbrev up_treeTop    :=
  ((T.isTree_iff e).1 he).choose_spec.choose_spec

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] in
/-- The vertex of a tree edge farther from the root is unique. -/
theorem up_edge_unique {a b : K.V} (ha : a ≠ T.root) (hb : b ≠ T.root)
    (h : (T.up a ha).1 = (T.up b hb).1) : a = b := by
  by_cases hs : (T.up a ha).2 = (T.up b hb).2
  · have huv  := Prod.ext h hs
    have h1  := T.up_src a ha
    have h2  := T.up_src b hb
    rw [huv, h2] at h1
    exact h1.symm
  · exfalso
    have huv : T.up b hb = revGerm (T.up a ha) := by
      refine Prod.ext h.symm ?_
      show (T.up b hb).2 = !(T.up a ha).2
      cases hx : (T.up a ha).2 <;> cases hy : (T.up b hb).2 <;> simp_all
    have hb' : b = T.parent a ha := by
      have h2  := T.up_src b hb
      aesop
    have ha' : T.parent b hb = a := by
      show germTgt K.src K.tgt (T.up b hb) = a
      rw [huv]
      simpa using T.up_src a ha
    have h1  := T.ht_parent ha
    have h2  := T.ht_parent hb
    rw [← hb'] at h1
    rw [ha'] at h2
    omega

include he in
omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] in
abbrev treeTop_eq   {a : K.V} (ha : a ≠ T.root)
    (h : (T.up a ha).1 = e)  :=
  up_edge_unique (treeTop_ne_root he) ha ((up_treeTop he).trans h.symm)

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] in
/-- The endpoints of a tree edge are the vertex it belongs to and its parent. -/
theorem tree_edge_endpoints  {a : K.V} (ha : a ≠ T.root) (hup : (T.up a ha).1 = e) :
    (K.src e = a ∧ K.tgt e = T.parent a ha) ∨ (K.src e = T.parent a ha ∧ K.tgt e = a) := by
  have hsrc  := T.up_src a ha
  have htgt : germTgt K.src K.tgt (T.up a ha) = T.parent a ha := rfl
  cases hb : (T.up a ha).2
  · classical grind [Prod.ext, FiniteChains.Comb.germSrc_false, FiniteChains.Comb.germTgt_false]
  · classical grind [Prod.ext, FiniteChains.Comb.germSrc_true, FiniteChains.Comb.germTgt_true]

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] in
theorem parent_ne_self {a : K.V} (ha : a ≠ T.root) : T.parent a ha ≠ a := by
  intro h
  have := T.ht_parent ha
  rw [h] at this
  omega

include he in
omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] in
theorem covTgt_of_isTree   (q : CovQ T N) :
    covTgt T N (q, e) = (q, K.tgt e) := by
  show (q * germQ T N (e, true), K.tgt e) = (q, K.tgt e)
  rw [germQ_eq_one_of_isTree (N := N) (g := (e, true)) he, mul_one]

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] in
/-- The maximal-height argument for tree chains, independent of the sheet type
and of the off-tree endpoints. Only the boundary away from the root is needed. -/
theorem treeChain_eq_zero_of_endpoints (T : SpanningTree K) {G : Type u}
    (s t : G × K.E → G × K.V)
    (hs : ∀ x, s x = (x.1, K.src x.2))
    (ht : ∀ x, T.isTree x.2 → t x = (x.1, K.tgt x.2))
    {z : (G × K.E) →₀ ℤ} (hsupp : ∀ x ∈ z.support, T.isTree x.2)
    (hz : ∀ g v, v ≠ T.root →
      ∑ x ∈ z.support, z x *
        ((Finsupp.single (t x) (1 : ℤ)) (g,v) - (Finsupp.single (s x) (1 : ℤ)) (g,v)) = 0) : z = 0 := by
  classical
  by_contra hne
  obtain ⟨x₀, hx₀, hmax⟩ := z.support.exists_max_image
    (fun x => if h : T.isTree x.2 then T.ht (treeTop h) else 0)
    (Finsupp.support_nonempty_iff.mpr hne)
  have he₀ := hsupp x₀ hx₀
  let a₀ := treeTop he₀
  have hn₀ : a₀ ≠ T.root := treeTop_ne_root he₀
  have hup₀ : (T.up a₀ hn₀).1 = x₀.2 := up_treeTop he₀
  have hterm : ∀ x ∈ z.support, x ≠ x₀ →
      z x * ((Finsupp.single (t x) (1 : ℤ)) (x₀.1,a₀)
        - (Finsupp.single (s x) (1 : ℤ)) (x₀.1,a₀)) = 0 := by
    intro x hx hne
    have he := hsupp x hx
    let a := treeTop he
    have hn : a ≠ T.root := treeTop_ne_root he
    have hup : (T.up a hn).1 = x.2 := up_treeTop he
    have hle : T.ht a ≤ T.ht a₀ := by simpa [he, he₀] using hmax x hx
    have hp : T.parent a hn ≠ a₀ := by
      intro heq
      have hheight := T.ht_parent hn
      rw [heq] at hheight
      omega
    have key : ∀ v, (v = K.src x.2 ∨ v = K.tgt x.2) → (x.1,v) ≠ (x₀.1,a₀) := by
      have ha : (x.1,a) ≠ (x₀.1,a₀) := by
        intro hh
        have hq := congrArg Prod.fst hh
        have hv : a = a₀ := congrArg Prod.snd hh
        have hupeq : (T.up a₀ hn₀).1 = x.2 := by simpa only [hv] using hup
        have heq := hupeq.symm.trans hup₀
        exact hne (Prod.ext hq heq)
      have hend := tree_edge_endpoints hn hup
      grind
    simp [hs, ht x he, Finsupp.single_eq_of_ne (Ne.symm (key _ (Or.inr rfl))),
      Finsupp.single_eq_of_ne (Ne.symm (key _ (Or.inl rfl)))]
  have hzero := hz x₀.1 a₀ hn₀
  rw [Finset.sum_eq_single_of_mem x₀ hx₀ hterm] at hzero
  have hp := parent_ne_self hn₀
  have hcoeff := Finsupp.mem_support_iff.mp hx₀
  rcases tree_edge_endpoints hn₀ hup₀ with ⟨hsrc, htgt⟩ | ⟨hsrc, htgt⟩ <;>
    simp [hs, ht x₀ he₀, hsrc, htgt, Finsupp.single_apply, hp, Ne.symm hp] at hzero <;>
    contradiction

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] in
/-- **A one-cycle of the cover supported on the tree edges vanishes**: the tree edges of each
sheet form a tree, so they carry no cycle. -/
theorem treeChain_eq_zero {z : (CovQ T N × K.E) →₀ ℤ}
    (hsupp : ∀ x ∈ z.support, T.isTree x.2)
    (hz : bdry1 (treeCover T N hN) z = 0) : z = 0 := by
  refine treeChain_eq_zero_of_endpoints T (treeCover T N hN).src
    (treeCover T N hN).tgt (fun _ => rfl) ?_ hsupp ?_
  · intro x hx
    exact covTgt_of_isTree (N := N) hx x.1
  · intro g v _
    exact (bdry1_apply (treeCover T N hN) z (g,v)).symm.trans
      (congrArg (fun c => c (g,v)) hz)

/-! ### Acyclicity -/

section
omit [Fintype (NonTree T)] [N.Normal]
/-- The coefficient of the comparison map at a non-tree edge. -/
theorem piE_apply (z : (CovQ T N × K.E) →₀ ℤ) (q : CovQ T N) (ε : NonTree T) :
    piE T N z (q, ε) = z (q, (ε : K.E)) := by
  classical
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z₁ z₂ h₁ h₂ => simp_all
  | single x n =>
      by_cases h : T.isTree x.2
      · grind [piE_single_tree]
      grind [piE_single_nontree]

theorem support_isTree_of_piE_eq_zero {z : (CovQ T N × K.E) →₀ ℤ} (h : piE T N z = 0) :
    ∀ x ∈ z.support, T.isTree x.2 := by
  intro x hx
  by_contra hnt
  have hval := piE_apply (N := N) z x.1 ⟨x.2, hnt⟩
  rw [h] at hval
  exact (Finsupp.mem_support_iff.1 hx) (by simpa using hval.symm)
end

end FiniteChains.Comb.SpanningTree


