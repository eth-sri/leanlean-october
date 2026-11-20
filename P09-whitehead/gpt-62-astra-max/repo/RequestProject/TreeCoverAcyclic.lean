module

public import RequestProject.CoverComplexFinsupp
public import RequestProject.TreeCover

@[expose] public section

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

noncomputable section

namespace FiniteChains
namespace Comb
namespace SpanningTree

universe u

variable {K : Complex2.{u}} (T : SpanningTree K)
variable (N : Subgroup (FreeGroup (NonTree T))) [N.Normal]

/-! ### The letters of a path outside the tree -/

open Classical in
/-- The word in the non-tree edges spelled by an edge path, as a list of letters. -/
def letters : List (K.E × Bool) → List (NonTree T × Bool)
  | [] => []
  | g :: L => if h : T.isTree g.1 then letters L else (⟨g.1, h⟩, g.2) :: letters L

variable {T}

@[simp] theorem letters_nil : letters T [] = [] := rfl

variable {g : K.E × Bool}

theorem letters_cons_tree (h : T.isTree g.1) (L : List _) :
    letters T (g :: L) = letters T L := by
  simp [letters, h]

theorem letters_cons_nontree (h : ¬ T.isTree g.1) (L : List _) :
    letters T (g :: L) = (⟨g.1, h⟩, g.2) :: letters T L := by
  simp [letters, h]

/-- The list of non-tree letters spells the word of the path. -/
theorem mk_letters (L : List _) :
    FreeGroup.mk (letters T L) = pathWord T L := by
  classical
  induction L with
  | nil => rfl
  | cons g L ih =>
      by_cases h : T.isTree g.1
      · simp_all [letters_cons_tree, pathWord_cons, germWord_of_isTree]
      · rw [letters_cons_nontree h, pathWord_cons]
        obtain ⟨e, b⟩ := g
        cases b
        · rw [mk_cons_false, ih, show germWord T _
            = (FreeGroup.of (⟨e, h⟩))⁻¹ by simp [germWord, h]]
        · rw [mk_cons_true, ih, show germWord T _
            = FreeGroup.of (⟨e, h⟩) by simp [germWord, h]]

/-! ### The comparison maps on chains -/

theorem germQ_eq_one_of_isTree {g : K.E × Bool} (h : T.isTree g.1) : germQ T N g = 1 := by
  show QuotientGroup.mk (germWord T g) = 1
  simp_all [germWord_of_isTree]

variable {e : K.E} (h : ¬ T.isTree e)

omit [N.Normal] in
theorem germQ_true_eq_qof :
    germQ T N (e, true) = qof N (⟨e, h⟩) := by
  classical
  show QuotientGroup.mk (germWord T _) = _
  rw [show germWord T _ = FreeGroup.of (⟨e, h⟩) by simp [germWord, h]] <;> rfl

theorem germQ_false_eq_qof_inv :
    germQ T N (e, false) = (qof N (⟨e, h⟩))⁻¹ := by
  simp_all [germQ_false_eq_inv, germQ_true_eq_qof]

variable (T)

open Classical in
/-- Deleting the tree edges: the comparison map on one-chains. -/
def piE :=
  Finsupp.linearCombination ℤ (fun x : CovQ T N × K.E =>
    if h : T.isTree x.2 then 0 else Finsupp.single (x.1, (⟨x.2, h⟩ : NonTree T)) (1 : ℤ))

/-- Forgetting the vertex of `K`: the comparison map on zero-chains. -/
def piV : ((CovQ T N × K.V) →₀ ℤ) →ₗ[ℤ] ((CovQ T N) →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ Prod.fst

/-- Putting a vertex of the presentation cover at the root of its tree. -/
def iotaV : ((CovQ T N) →₀ ℤ) →ₗ[ℤ] ((CovQ T N × K.V) →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun q => (q, T.root))

variable {T}

variable {x : CovQ T N × K.E}

omit [N.Normal] in
theorem piE_single_tree (h : T.isTree x.2) (n : ℤ) :
    piE T N (Finsupp.single x n) = 0 := by
  simp [piE, h]

omit [N.Normal] in
theorem piE_single_nontree (h : ¬ T.isTree x.2) (n : ℤ) :
    piE T N (Finsupp.single x n) = Finsupp.single (x.1, (⟨x.2, h⟩)) n := by
  simp [piE, h]

omit [N.Normal] in
@[simp] theorem piV_single (x : CovQ T N × K.V) (n : ℤ) :
    piV T N (Finsupp.single x n) = Finsupp.single x.1 n := by
  rw [piV]
  simp

omit [N.Normal] in
@[simp] theorem iotaV_single (q : CovQ T N) (n : ℤ) :
    iotaV T N (Finsupp.single q n) = Finsupp.single (q, T.root) n := by
  rw [iotaV]
  simp

/-- **Deleting the tree edges from a lifted path** gives the lift of the word it spells. -/
theorem piE_pathChain_liftK (L : List _) (q : CovQ T N) :
    piE T N (pathChain (liftK T N L q)) = pathChain (liftPath (letters T L) q) := by
  classical
  induction L generalizing q with
  | nil => rfl
  | cons g L ih =>
      obtain ⟨e, b⟩ := g
      by_cases h : T.isTree e
      · have hq : q * germQ T N (e, b) = q := by
          simp_all [germQ_eq_one_of_isTree]
        have hsnd : (liftGerm T N q (e, b)).2 = b := by cases b <;> rfl
        have hfst : (liftGerm T N q (e, b)).1.2 = e := by cases b <;> rfl
        have hz :=
          piE_single_tree (N := N) (x := (liftGerm T N q (e, b)).1) (by simp_all) 1
        rw [liftK_cons, pathChain_cons, map_add, letters_cons_tree (g := (e, b)) h, hq, ih q,
          hsnd] <;> aesop
      · rw [liftK_cons, pathChain_cons, map_add, letters_cons_nontree (g := (e, b)) h]
        cases b
        · have hlift : liftGerm T N q (e, false) =
              ((q * germQ T N _, e), false) := rfl
          simp_all [piE_single_nontree, germQ_false_eq_qof_inv, pathChain_cons]
        · have hlift : liftGerm T N q (e, true) = ((q, e), true) := rfl
          simp_all [piE_single_nontree, germQ_true_eq_qof, pathChain_cons]

/-! ### The comparison maps are chain maps -/

variable [Fintype (NonTree T)] [DecidableEq (NonTree T)]

omit [Fintype _] in
/-- The chain of a lifted word depends only on the free-group element it spells. -/
theorem pathChain_liftPath_congr {L L' : List _}
    (h : FreeGroup.mk L = FreeGroup.mk L') (q : CovQ T N) :
    pathChain (liftPath (Nsub := N) L q) = pathChain (liftPath (Nsub := N) L' q) := by
  apply (fsCoords N _).injective
  ext <;> simp_all [fsCoords_pathChain_liftPath_apply]

variable (hN : ∀ f, treeRel T f ∈ N)

omit [Fintype _] in
/-- **The comparison map is a chain map in degree two**: the two covers have the same
two-cells, and deleting the tree edges from the attaching path of a two-cell of the cover of
`K` gives the attaching path of the corresponding two-cell of the cover of the presentation
complex. -/
theorem piE_bdry2 (u : (CovQ T N × K.F) →₀ ℤ) :
    piE T N (bdry2 (treeCover T N hN) u) = bdry2 (coverComplex N _ hN) u := by
  classical
  induction u using Finsupp.induction_linear with
  | single x n =>
      obtain ⟨q, f⟩ := x
      rw [bdry2_single, bdry2_single, map_smul]
      show n • piE T N (pathChain (liftK T N (K.att f) q)) = _
      rw [piE_pathChain_liftK]
      congr 1
      refine pathChain_liftPath_congr (N := N) ?_ q
      rw [mk_letters, FreeGroup.mk_toWord]
      rfl
  | _ => simp_all

omit [Fintype _] in
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
        rw [map_smul, map_sub, piV_single, piV_single]; show n • (Finsupp.single (q * germQ T N _) 1
          - Finsupp.single q 1) = 0; simp [(germQ_eq_one_of_isTree (N := N) (g := (e, true)) h)]
      · rw [piE_single_nontree (N := N) (x := (q, e)) h n, bdry1_single]
        rw [map_smul, map_sub, piV_single, piV_single]; show n • (Finsupp.single (q * germQ T N _) 1
          - Finsupp.single q 1) = _; rw [germQ_true_eq_qof (N := N) h]

omit [Fintype _] in
/-- The augmentations agree. -/
theorem augC_piV (c : (CovQ T N × K.V) →₀ ℤ) :
    augC (coverComplex N (treeRel T) hN) (piV T N c) = augC (treeCover T N hN) c := by
  classical
  induction c using Finsupp.induction_linear with
  | single x n =>
      rw [piV_single]; rw [augC_single, augC_single]
  | _ => simp_all

/-! ### Contracting the tree and lifting the generators -/

variable (T)

/-- The loop of `K` at the root carried by a non-tree edge. -/
def loopPath (ε : NonTree T) :=
  conjPath T [(ε, true)] (K.src ε) (K.tgt ε)

/-- Lifting the loops of the generators: a section of the comparison map on one-chains. -/
def sectionE :=
  Finsupp.linearCombination ℤ (fun x : CovQ T N × NonTree T =>
    pathChain (liftK T N (loopPath T x.2) x.1))

variable {T}

variable (ε : NonTree T)

omit [Fintype _] [DecidableEq _] in
theorem isPath_loopPath :
    IsPath K.src K.tgt (loopPath T ε) T.root T.root :=
  by solve_by_elim [conjPath_isLoop]

omit [Fintype _] [DecidableEq _] in
theorem pathWord_loopPath : pathWord T (loopPath T ε) = FreeGroup.of ε := by
  classical
  rw [loopPath, conjPath, pathWord_append, pathWord_append, pathWord_treePath,
    pathWord_revPath, pathWord_treePath]
  simp [pathWord, germWord, dif_neg ε.2]

omit [N.Normal] [Fintype _] [DecidableEq _] in
theorem wordQ_loopPath : wordQ T N (loopPath T ε) = qof N ε := by
  show QuotientGroup.mk (pathWord T _) = _
  solve_by_elim [pathWord_loopPath]

variable (hN : ∀ f, treeRel T f ∈ N)

omit [Fintype _] in
/-- **Lifting the generators**: the section is a chain homotopy inverse in degree one. -/
theorem bdry1_sectionE (u : (CovQ T N × NonTree T) →₀ ℤ) :
    bdry1 (treeCover T N hN) (sectionE T N u)
      = iotaV T N (bdry1 (coverComplex N (treeRel T) hN) u) := by
  classical
  induction u using Finsupp.induction_linear with
  | single x n =>
      obtain ⟨q, ε⟩ := x
      have hpath := liftK_isPath (isPath_loopPath (T := T) ε) q
      rw [wordQ_loopPath (N := N)] at hpath
      rw [sectionE, Finsupp.linearCombination_single, map_smul, bdry1_single]
      have hb :=
        bdry1_pathChain_of_isPath (X := treeCover T N hN) hpath
      simp_all
  | _ => simp_all

/-! ### One-cycles supported on the tree vanish -/

/-- The coefficient of a boundary at a vertex. -/
theorem bdry1_apply (X : Complex2.{u}) (z : X.E →₀ ℤ) (w : X.V) :
    bdry1 X z w = ∑ x ∈ z.support, z x *
      ((Finsupp.single (X.tgt x) 1) w - (Finsupp.single (X.src x) 1) w) := by
  simp [bdry1, Finsupp.linearCombination_apply, Finsupp.sum]

/-- The non-root vertex whose tree edge is the given tree edge. -/
def treeTop {e : K.E} (he : T.isTree e) :=
  ((T.isTree_iff e).1 he).choose

omit [Fintype _] [DecidableEq _] in
theorem treeTop_ne_root {e : K.E} (he : T.isTree e) : treeTop he ≠ T.root :=
  ((T.isTree_iff e).1 he).choose_spec.choose

omit [Fintype _] [DecidableEq _] in
theorem up_treeTop {e : K.E} (he : T.isTree e) :
    (T.up _ (treeTop_ne_root he)).1 = e :=
  ((T.isTree_iff e).1 he).choose_spec.choose_spec

omit [Fintype _] [DecidableEq _] in
/-- The vertex of a tree edge farther from the root is unique. -/
theorem up_edge_unique {a b : K.V} (ha : a ≠ T.root) (hb : b ≠ T.root)
    (h : (T.up a ha).1 = (T.up b hb).1) : a = b := by
  by_cases hs : (T.up a ha).2 = (T.up b hb).2
  · have huv := Prod.ext h hs
    have h1 := T.up_src a ha
    have h2 := T.up_src b hb
    simp_all
  · exfalso
    have huv : T.up b hb = revGerm (T.up a ha) := by
      refine Prod.ext h.symm ?_
      show (T.up b hb).2 = !(T.up a ha).2
      grind
    have hb' : b = T.parent a ha := by
      have h2 := T.up_src b hb
      aesop
    have ha' : T.parent b hb = a := by
      show germTgt K.src K.tgt _ = a
      rw [huv]
      simpa using T.up_src a ha
    have h1 := T.ht_parent ha
    have h2 := T.ht_parent hb
    grind

variable {e : K.E}

omit [Fintype _] [DecidableEq _] in
theorem treeTop_eq (he : T.isTree e) {a : K.V} (ha : a ≠ T.root)
    (h : (T.up a ha).1 = e) : treeTop he = a :=
  up_edge_unique _ ha ((up_treeTop he).trans h.symm)

omit [Fintype _] [DecidableEq _] in
/-- The endpoints of a tree edge are the vertex it belongs to and its parent. -/
theorem tree_edge_endpoints {a : K.V} (ha : a ≠ T.root) (hup : (T.up a ha).1 = e) :
    (K.src e = a ∧ K.tgt e = T.parent a ha) ∨ (K.src e = T.parent a ha ∧ K.tgt e = a) := by
  have hsrc := T.up_src a ha
  have htgt : germTgt K.src K.tgt _ = T.parent a ha := rfl
  cases hb : (T.up a ha).2 <;> grind [germSrc_false, germTgt_false, germSrc_true, germTgt_true]

omit [Fintype _] [DecidableEq _] in
theorem parent_ne_self {a : K.V} (ha : a ≠ T.root) : T.parent a ha ≠ a := by
  intro h
  have := T.ht_parent ha
  simp_all

omit [Fintype _] [DecidableEq _] in
theorem covTgt_of_isTree {e : K.E} (he : T.isTree e) (q : CovQ T N) :
    covTgt T N (q, e) = (q, K.tgt e) := by
  show (q * germQ T N _, K.tgt e) = (q, K.tgt e)
  simp_all [germQ_eq_one_of_isTree]

omit [Fintype _] [DecidableEq _] in
/-- A leaf of maximal height detects every nonzero finite chain on a sheeted tree.
Only the boundary off the root matters; non-tree edges and the group on the sheets are irrelevant. -/
theorem treeChain_eq_zero_of_offRoot {S : Type u} {z : (S × K.E) →₀ ℤ}
    (tgt : S × K.E → S × K.V) (ht : ∀ x, T.isTree x.2 → tgt x = (x.1, K.tgt x.2))
    (hsupp : ∀ x ∈ z.support, T.isTree x.2)
    (hz : ∀ g v, v ≠ T.root → ∑ x ∈ z.support, z x *
      ((Finsupp.single (tgt x) 1) (g, v) - (Finsupp.single (x.1, K.src x.2) 1) (g, v)) = 0) :
    z = 0 := by
  classical
  by_contra hzne
  obtain ⟨x₀, hx₀mem, hx₀max⟩ := z.support.exists_max_image
    (fun x => if h : T.isTree x.2 then T.ht (treeTop h) else 0) (Finsupp.support_nonempty_iff.2 hzne)
  obtain ⟨a₀, ha₀ne, ha₀up⟩ := (T.isTree_iff x₀.2).1 (hsupp x₀ hx₀mem)
  have hg : ∀ x ∈ z.support, ∀ (a : K.V) (ha : a ≠ T.root), (T.up a ha).1 = x.2 →
      (if h : T.isTree x.2 then T.ht (treeTop h) else 0) = T.ht a := by
    grind [treeTop_eq]
  have hg₀ :=
    hg x₀ hx₀mem a₀ ha₀ne ha₀up
  -- all terms but the one of `x₀` vanish at the vertex `(x₀.1, a₀)`
  have hterm : ∀ x ∈ z.support, x ≠ x₀ →
      z x * ((Finsupp.single (tgt x) 1) (x₀.1, a₀)
        - (Finsupp.single ((x.1, K.src x.2)) 1) (x₀.1, a₀)) = 0 := by
    intro x hx hxne
    obtain ⟨a, hane, haup⟩ := (T.isTree_iff x.2).1 (hsupp x hx)
    have key : ∀ v : K.V, (v = K.src x.2 ∨ v = K.tgt x.2) → (x.1, v) ≠ (x₀.1, a₀) := by
      intro v hv hc
      rw [Prod.mk.injEq] at hc
      obtain ⟨hq, hva⟩ := hc
      have hparent : T.parent a hane = a₀ → False := by
        intro hp
        have hht := T.ht_parent hane
        grind
      grind [tree_edge_endpoints]
    grind
  -- evaluate the boundary at the vertex `(x₀.1, a₀)`
  have hzero : 0 = z x₀ *
      ((Finsupp.single (tgt x₀) 1) (x₀.1, a₀)
        - (Finsupp.single ((x₀.1, K.src x₀.2)) 1) (x₀.1, a₀)) := (hz x₀.1 a₀ ha₀ne).symm.trans (Finset.sum_eq_single_of_mem x₀ hx₀mem hterm)
  have hpne := parent_ne_self ha₀ne
  grind [tree_edge_endpoints]

omit [Fintype _] [DecidableEq _] in
/-- **A one-cycle of the cover supported on the tree edges vanishes**: the tree edges of each
sheet form a tree, so they carry no cycle. -/
theorem treeChain_eq_zero {z : (CovQ T N × K.E) →₀ ℤ}
    (hsupp : ∀ x ∈ z.support, T.isTree x.2)
    (hz : bdry1 (treeCover T N hN) z = 0) : z = 0 := by
  apply treeChain_eq_zero_of_offRoot _ (fun x h => covTgt_of_isTree (N := N) h x.1) hsupp
  · intro g v _
    exact (bdry1_apply (treeCover T N hN) z _).symm.trans (DFunLike.congr_fun hz (g, v))

/-! ### Acyclicity -/

omit [Fintype _] [N.Normal] in
/-- The coefficient of the comparison map at a non-tree edge. -/
theorem piE_apply (z : (CovQ T N × K.E) →₀ ℤ) (q : CovQ T N) (ε : NonTree T) :
    piE T N z (q, ε) = z (q, ε) := by
  classical
  induction z using Finsupp.induction_linear with
  | single x n =>
      by_cases h : T.isTree x.2
      · grind [piE_single_tree]
      · grind [piE_single_nontree]
  | _ => simp_all

omit [Fintype _] [N.Normal] in
theorem support_isTree_of_piE_eq_zero {z : (CovQ T N × K.E) →₀ ℤ} (h : piE T N z = 0) :
    ∀ x ∈ z.support, T.isTree x.2 := by
  intro x hx
  by_contra hnt
  have hval := piE_apply (N := N) z x.1 ⟨x.2, hnt⟩
  simp_all

end SpanningTree
end Comb
end FiniteChains
