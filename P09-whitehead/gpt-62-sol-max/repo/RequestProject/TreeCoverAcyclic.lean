module

public import RequestProject.CoverComplex
public import RequestProject.FinsuppBasis
public import RequestProject.CrowellFinsupp
public import RequestProject.PresentationNecessityFinsupp
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

namespace FiniteChains
namespace Comb
namespace SpanningTree

universe u

variable {K : Complex2.{u}} (T : SpanningTree K)
variable (N : Subgroup (FreeGroup (NonTree T))) [N.Normal]

/-! ### The letters of a path outside the tree -/

open Classical in
/-- The word in the non-tree edges spelled by an edge path, as a list of letters. -/
noncomputable def letters : List (K.E × Bool) → List (NonTree T × Bool)
  | [] => []
  | g :: L => if h : T.isTree g.1 then letters L else (⟨g.1, h⟩, g.2) :: letters L

variable {T}


theorem letters_cons_tree {g : K.E × Bool} (h : T.isTree g.1) (L : List (K.E × Bool)) :
    letters T (g :: L) = letters T L := by
  classical
  simp [letters, h]

theorem letters_cons_nontree {g : K.E × Bool} (h : ¬ T.isTree g.1) (L : List (K.E × Bool)) :
    letters T (g :: L) = (⟨g.1, h⟩, g.2) :: letters T L := by
  classical
  simp [letters, h]

/-- The list of non-tree letters spells the word of the path. -/
theorem mk_letters (L : List (K.E × Bool)) :
    FreeGroup.mk (letters T L) = pathWord T L := by
  classical
  induction L with
  | nil => rfl
  | cons g L ih =>
      by_cases h : T.isTree g.1
      · rw [letters_cons_tree h, ih, pathWord_cons, germWord_of_isTree T h, one_mul]
      · rw [letters_cons_nontree h, pathWord_cons]
        obtain ⟨e, b⟩ := g
        cases b
        · rw [mk_cons_false, ih, show germWord T (e, false)
            = (FreeGroup.of ⟨e, h⟩)⁻¹ by simp [germWord, h]]
        · rw [mk_cons_true, ih, show germWord T (e, true)
            = FreeGroup.of ⟨e, h⟩ by simp [germWord, h]]

/-! ### The comparison maps on chains -/

theorem germQ_eq_one_of_isTree {g : K.E × Bool} (h : T.isTree g.1) : germQ T N g = 1 := by
  show QuotientGroup.mk (germWord T g) = 1
  rw [germWord_of_isTree T h]
  rfl

omit [N.Normal] in
theorem germQ_true_eq_qof {e : K.E} (h : ¬ T.isTree e) :
    germQ T N (e, true) = qof N (⟨e, h⟩ : NonTree T) := by
  classical
  show QuotientGroup.mk (germWord T (e, true)) = _
  rw [show germWord T (e, true) = FreeGroup.of ⟨e, h⟩ by simp [germWord, h]]
  rfl

theorem germQ_false_eq_qof_inv {e : K.E} (h : ¬ T.isTree e) :
    germQ T N (e, false) = (qof N (⟨e, h⟩ : NonTree T))⁻¹ := by
  rw [germQ_false_eq_inv, germQ_true_eq_qof (N := N) h]

variable (T)

open Classical in
/-- Deleting the tree edges: the comparison map on one-chains. -/
noncomputable def piE : ((CovQ T N × K.E) →₀ ℤ) →ₗ[ℤ] ((CovQ T N × NonTree T) →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x  =>
    if h : T.isTree x.2 then 0 else Finsupp.single (x.1, ⟨x.2, h⟩) 1)

/-- Forgetting the vertex of `K`: the comparison map on zero-chains. -/
noncomputable def piV : ((CovQ T N × K.V) →₀ ℤ) →ₗ[ℤ] ((CovQ T N) →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ Prod.fst

/-- Putting a vertex of the presentation cover at the root of its tree. -/
noncomputable def iotaV : ((CovQ T N) →₀ ℤ) →ₗ[ℤ] ((CovQ T N × K.V) →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun q => (q, T.root))

variable {T}

omit [N.Normal] in
theorem piE_single_tree {x : CovQ T N × K.E} (h : T.isTree x.2) (n : ℤ) :
    piE T N (Finsupp.single x n) = 0 := by
  classical
  rw [piE, Finsupp.linearCombination_single]
  simp [h]

omit [N.Normal] in
theorem piE_single_nontree {x : CovQ T N × K.E} (h : ¬ T.isTree x.2) (n : ℤ) :
    piE T N (Finsupp.single x n) = Finsupp.single (x.1, (⟨x.2, h⟩ : NonTree T)) n := by
  classical
  rw [piE, Finsupp.linearCombination_single]
  simp [h, Finsupp.smul_single]

omit [N.Normal] in
@[simp] theorem piV_single (x : CovQ T N × K.V) (n : ℤ) :
    piV T N (Finsupp.single x n) = Finsupp.single x.1 n := by
  rw [piV]
  simp [Finsupp.lmapDomain_apply]

omit [N.Normal] in
@[simp] theorem iotaV_single (q : CovQ T N) (n : ℤ) :
    iotaV T N (Finsupp.single q n) = Finsupp.single (q, T.root) n := by
  rw [iotaV]
  simp [Finsupp.lmapDomain_apply]

/-- **Deleting the tree edges from a lifted path** gives the lift of the word it spells. -/
theorem piE_pathChain_liftK (L : List (K.E × Bool)) (q : CovQ T N) :
    piE T N (pathChain (liftK T N L q)) = pathChain (liftPath (letters T L) q) := by
  classical
  induction L generalizing q with
  | nil => change piE T N 0 = 0; simp
  | cons g L ih =>
      obtain ⟨e, b⟩ := g
      by_cases h : T.isTree e
      · have hq : q * germQ T N (e, b) = q := by
          rw [germQ_eq_one_of_isTree (N := N) (g := (e, b)) h, mul_one]
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
          rw [piE_single_nontree (N := N) (x := (q * germQ T N (e, false), e)) h 1,
            ih (q * germQ T N (e, false)), germQ_false_eq_qof_inv (N := N) h,
            liftPath_cons_false, pathChain_cons]
          simp
        · have hlift : liftGerm T N q (e, true) = ((q, e), true) := rfl
          rw [hlift]
          simp only [if_true]
          rw [piE_single_nontree (N := N) (x := (q, e)) h 1,
            germQ_true_eq_qof (N := N) h, ih (q * qof N ⟨e, h⟩)]
          rw [liftPath_cons_true, pathChain_cons]
          simp

/-! ### The comparison maps are chain maps -/

section Comparison
variable [DecidableEq (NonTree T)]

/-- The chain of a lifted word depends only on the free-group element it spells. -/
theorem pathChain_liftPath_congr {L L' : List (NonTree T × Bool)}
    (h : FreeGroup.mk L = FreeGroup.mk L') (q : CovQ T N) :
    pathChain (liftPath (Nsub := N) L q) = pathChain (liftPath (Nsub := N) L' q) := by
  apply (fsCoords N (NonTree T)).injective
  apply Finsupp.ext
  intro i
  rw [fsCoords_pathChain_liftPath_apply, fsCoords_pathChain_liftPath_apply, h]

variable (hN : ∀ f, treeRel T f ∈ N)

/-- **The comparison map is a chain map in degree two**: the two covers have the same
two-cells, and deleting the tree edges from the attaching path of a two-cell of the cover of
`K` gives the attaching path of the corresponding two-cell of the cover of the presentation
complex. -/
theorem piE_bdry2 (u : (CovQ T N × K.F) →₀ ℤ) :
    piE T N (bdry2 (treeCover T N hN) u) = bdry2 (coverComplex N (treeRel T) hN) u := by
  classical
  finsupp_basis u
  rintro ⟨q, f⟩
  rw [bdry2_single, bdry2_single, one_smul, one_smul]
  change piE T N (pathChain (liftK T N (K.att f) q)) = _
  rw [piE_pathChain_liftK]
  apply pathChain_liftPath_congr
  rw [mk_letters, FreeGroup.mk_toWord]
  rfl

/-- **The comparison map is a chain map in degree one.** -/
theorem piV_bdry1 (c : (CovQ T N × K.E) →₀ ℤ) :
    piV T N (bdry1 (treeCover T N hN) c) = bdry1 (coverComplex N (treeRel T) hN) (piE T N c) := by
  classical
  finsupp_basis c
  rintro ⟨q, e⟩
  rw [bdry1_single, one_smul, map_sub, piV_single, piV_single]
  change Finsupp.single (q * germQ T N (e, true)) 1 - Finsupp.single q 1 = _
  by_cases h : T.isTree e
  · rw [piE_single_tree (N := N) (x := (q, e)) h 1, map_zero,
      germQ_eq_one_of_isTree (N := N) (g := (e, true)) h, mul_one, sub_self]
  · rw [piE_single_nontree (N := N) (x := (q, e)) h 1, bdry1_single, one_smul,
      germQ_true_eq_qof (N := N) h]

/-- The augmentations agree. -/
theorem augC_piV (c : (CovQ T N × K.V) →₀ ℤ) :
    augC (coverComplex N (treeRel T) hN) (piV T N c) = augC (treeCover T N hN) c := by
  classical
  finsupp_basis c
  intro x
  obtain ⟨q, a⟩ := x
  rw [piV_single]
  show augC (coverComplex N (treeRel T) hN) (Finsupp.single q 1) = _
  rw [augC_single, augC_single]

end Comparison

/-! ### Contracting the tree and lifting the generators -/

variable (hN : ∀ f, treeRel T f ∈ N)

variable (T)

/-- The loop of `K` at the root carried by a non-tree edge. -/
noncomputable def loopPath (ε : NonTree T) : List (K.E × Bool) :=
  conjPath T [(ε, true)] (K.src ε) (K.tgt ε)

/-- Lifting the loops of the generators: a section of the comparison map on one-chains. -/
noncomputable def sectionE :
    ((CovQ T N × NonTree T) →₀ ℤ) →ₗ[ℤ] ((CovQ T N × K.E) →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x  =>
    pathChain (liftK T N (loopPath T x.2) x.1))

variable {T}

theorem isPath_loopPath (ε : NonTree T) :
    IsPath K.src K.tgt (loopPath T ε) T.root T.root :=
  conjPath_isLoop T (isPath_single _)

theorem pathWord_loopPath (ε : NonTree T) : pathWord T (loopPath T ε) = FreeGroup.of ε := by
  classical
  rw [loopPath, conjPath, pathWord_append, pathWord_append, pathWord_treePath,
    pathWord_revPath, pathWord_treePath]
  simp [pathWord, germWord, dif_neg ε.2]

omit [N.Normal] in
theorem wordQ_loopPath (ε : NonTree T) : wordQ T N (loopPath T ε) = qof N ε := by
  show QuotientGroup.mk (pathWord T (loopPath T ε)) = _
  rw [pathWord_loopPath]
  rfl

variable (hN : ∀ f, treeRel T f ∈ N)

/-- **Lifting the generators**: the section is a chain homotopy inverse in degree one. -/
theorem bdry1_sectionE [DecidableEq (NonTree T)] (u : (CovQ T N × NonTree T) →₀ ℤ) :
    bdry1 (treeCover T N hN) (sectionE T N u)
      = iotaV T N (bdry1 (coverComplex N (treeRel T) hN) u) := by
  classical
  finsupp_basis u
  intro x
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
  rw [Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finsupp.smul_apply, Finsupp.sub_apply, smul_eq_mul]

/-- The non-root vertex whose tree edge is the given tree edge. -/
noncomputable def treeTop {e : K.E} (he : T.isTree e) : K.V :=
  ((T.isTree_iff e).1 he).choose

theorem treeTop_ne_root {e : K.E} (he : T.isTree e) : treeTop he ≠ T.root :=
  ((T.isTree_iff e).1 he).choose_spec.choose

theorem up_treeTop {e : K.E} (he : T.isTree e) :
    (T.up (treeTop he) (treeTop_ne_root he)).1 = e :=
  ((T.isTree_iff e).1 he).choose_spec.choose_spec



/-- The endpoints of a tree edge are the vertex it belongs to and its parent. -/
theorem tree_edge_endpoints {e : K.E} {a : K.V} (ha : a ≠ T.root) (hup : (T.up a ha).1 = e) :
    (K.src e = a ∧ K.tgt e = T.parent a ha) ∨ (K.src e = T.parent a ha ∧ K.tgt e = a) := by
  have hsrc  := T.up_src a ha
  have htgt : germTgt K.src K.tgt (T.up a ha) = T.parent a ha := rfl
  cases hb : (T.up a ha).2
  · right
    have hg : T.up a ha = (e, false) := Prod.ext hup hb
    rw [hg] at hsrc htgt
    simp only [germSrc_false, germTgt_false] at hsrc htgt
    exact ⟨htgt, hsrc⟩
  · left
    have hg : T.up a ha = (e, true) := Prod.ext hup hb
    rw [hg] at hsrc htgt
    simp only [germSrc_true, germTgt_true] at hsrc htgt
    exact ⟨hsrc, htgt⟩

theorem parent_ne_self {a : K.V} (ha : a ≠ T.root) : T.parent a ha ≠ a := by
  intro h
  have := T.ht_parent ha
  rw [h] at this
  omega

theorem covTgt_of_isTree {e : K.E} (he : T.isTree e) (q : CovQ T N) :
    covTgt T N (q, e) = (q, K.tgt e) := by
  show (q * germQ T N (e, true), K.tgt e) = (q, K.tgt e)
  rw [germQ_eq_one_of_isTree (N := N) (g := (e, true)) he, mul_one]

/-- In any disjoint union of copies of the tree, a finite edge chain with no
boundary away from the roots is zero. -/
theorem treeSupport_eq_zero {G : Type*} {z : (G × K.E) →₀ ℤ}
    (hsupp : ∀ x ∈ z.support, T.isTree x.2)
    (hz : ∀ g v, v ≠ T.root →
      ∑ x ∈ z.support, z x * ((Finsupp.single (x.1, K.tgt x.2) (1 : ℤ)) (g, v) -
        (Finsupp.single (x.1, K.src x.2) (1 : ℤ)) (g, v)) = 0) : z = 0 := by
  classical
  by_contra hne
  let height (e : G × K.E) := if h : T.isTree e.2 then T.ht (treeTop h) else 0
  obtain ⟨e, he, hmax⟩ := z.support.exists_max_image height (Finsupp.support_nonempty_iff.mpr hne)
  let v := treeTop (hsupp e he)
  have hv : v ≠ T.root := treeTop_ne_root _
  have hev : (T.up v hv).1 = e.2 := up_treeTop _
  let coeff (x : G × K.E) := z x * ((Finsupp.single (x.1, K.tgt x.2) 1) (e.1, v) -
    (Finsupp.single (x.1, K.src x.2) 1) (e.1, v))
  have hz'  := hz e.1 v hv
  rw [Finset.sum_eq_single_of_mem e he] at hz'
  · have hzₑ := Finsupp.mem_support_iff.mp he
    have hp := parent_ne_self hv
    rcases tree_edge_endpoints hv hev with ⟨hs, ht⟩ | ⟨hs, ht⟩ <;>
      simp [hs, ht, hp] at hz' <;> contradiction
  · intro x hx hxe
    let w := treeTop (hsupp x hx)
    have hw : w ≠ T.root := treeTop_ne_root _
    have hxw : (T.up w hw).1 = x.2 := up_treeTop _
    have hle : T.ht w ≤ T.ht v := by simpa [height, hsupp x hx, hsupp e he] using hmax x hx
    have hpar : T.parent w hw ≠ v := by
      intro h
      have ht := T.ht_parent hw
      rw [h] at ht
      omega
    have hn : (e.1, v) ≠ (x.1, w) := by
      intro h
      obtain ⟨hg, hvw⟩ := Prod.mk.inj h
      exact hxe (Prod.ext hg.symm (hxw.symm.trans (by simpa only [hvw] using hev)))
    rcases tree_edge_endpoints hw hxw with ⟨hs, ht⟩ | ⟨hs, ht⟩ <;>
      simp [hs, ht, show ¬ (x.1 = e.1 ∧ w = v) from by simpa using Ne.symm hn, hpar]

/-- **A one-cycle of the cover supported on the tree edges vanishes**: the tree edges of each
sheet form a tree, so they carry no cycle. -/
theorem treeChain_eq_zero {z : (CovQ T N × K.E) →₀ ℤ}
    (hsupp : ∀ x ∈ z.support, T.isTree x.2)
    (hz : bdry1 (treeCover T N hN) z = 0) : z = 0 := by
  classical
  apply treeSupport_eq_zero hsupp
  intro q v _
  have h : bdry1 (treeCover T N hN) z (q, v) = 0 := by simp [hz]
  rw [bdry1_apply] at h
  refine (Finset.sum_congr rfl fun x hx => ?_).trans h
  rcases x with ⟨g, e⟩
  rw [treeCover_src, treeCover_tgt, covTgt_of_isTree (N := N) (hsupp _ hx)]
  rfl


/-! ### Acyclicity -/

omit [N.Normal] in
/-- The coefficient of the comparison map at a non-tree edge. -/
theorem piE_apply (z : (CovQ T N × K.E) →₀ ℤ) (q : CovQ T N) (ε : NonTree T) :
    piE T N z (q, ε) = z (q, (ε : K.E)) := by
  classical
  finsupp_basis z
  intro x
  by_cases h : T.isTree x.2
  · rw [piE_single_tree (N := N) h 1]
    have hne : x ≠ (q, (ε : K.E)) := by
      intro hc
      exact ε.2 (by rw [hc] at h; exact h)
    simp [hne]
  · rw [piE_single_nontree (N := N) h 1, Finsupp.single_apply, Finsupp.single_apply]
    congr 1
    simp only [Prod.ext_iff, Subtype.ext_iff]

omit [N.Normal] in
theorem support_isTree_of_piE_eq_zero {z : (CovQ T N × K.E) →₀ ℤ} (h : piE T N z = 0) :
    ∀ x ∈ z.support, T.isTree x.2 := by
  intro x hx
  by_contra hnt
  have hval := piE_apply (N := N) z x.1 ⟨x.2, hnt⟩
  rw [h] at hval
  exact (Finsupp.mem_support_iff.1 hx) (by simpa using hval.symm)

end SpanningTree
end Comb
end FiniteChains
