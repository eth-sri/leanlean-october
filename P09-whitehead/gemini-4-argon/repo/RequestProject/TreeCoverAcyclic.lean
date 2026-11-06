module

public import RequestProject.CoverComplexFinsupp
public import RequestProject.TreeCover

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FiniteChains.Comb.SpanningTree

universe u

variable {K : Complex2.{u}} (T : SpanningTree K) (N : Subgroup (FreeGroup (NonTree T)))

open Classical in
def letters : List (K.E × Bool) → List (NonTree T × Bool)
  | [] => []
  | g :: L => if h : T.isTree g.1 then letters L else (⟨g.1, h⟩, g.2) :: letters L

open Classical in
def piE : ((CovQ T N × K.E) →₀ ℤ) →ₗ[ℤ] ((CovQ T N × NonTree T) →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x : CovQ T N × K.E =>
    if h : T.isTree x.2 then 0 else Finsupp.single (x.1, (⟨x.2, h⟩ : NonTree T)) (1 : ℤ))

def piV : ((CovQ T N × K.V) →₀ ℤ) →ₗ[ℤ] ((CovQ T N) →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ Prod.fst

def iotaV : ((CovQ T N) →₀ ℤ) →ₗ[ℤ] ((CovQ T N × K.V) →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun q => (q, T.root))

def loopPath (ε : NonTree T) : List (K.E × Bool) :=
  conjPath T [((ε : K.E), true)] (K.src (ε : K.E)) (K.tgt (ε : K.E))

variable {T}

theorem letters_cons_tree {g : K.E × Bool} (h : T.isTree g.1) (L : List (K.E × Bool)) :
    letters T (g :: L) = letters T L := by classical simp [letters, h]

theorem letters_cons_nontree {g : K.E × Bool} (h : ¬ T.isTree g.1) (L : List (K.E × Bool)) :
    letters T (g :: L) = (⟨g.1, h⟩, g.2) :: letters T L := by classical simp [letters, h]

theorem mk_letters : ∀ L : List (K.E × Bool), FreeGroup.mk (letters T L) = pathWord T L
  | [] => rfl
  | ⟨e, b⟩ :: L => by
      classical
      by_cases h : T.isTree e
      · rw [letters_cons_tree h, mk_letters L, pathWord_cons, germWord_of_isTree T h, one_mul]
      · rw [letters_cons_nontree h, pathWord_cons]
        cases b
        · rw [mk_cons_false, mk_letters L,
            show germWord T (e, false) = (FreeGroup.of (⟨e, h⟩ : NonTree T))⁻¹ by simp [germWord, h]]
        · rw [mk_cons_true, mk_letters L,
            show germWord T (e, true) = FreeGroup.of (⟨e, h⟩ : NonTree T) by simp [germWord, h]]

theorem germQ_true_eq_qof {e : K.E} (h : ¬ T.isTree e) :
    germQ T N (e, true) = qof N (⟨e, h⟩ : NonTree T) := by
  classical
  show QuotientGroup.mk (germWord T (e, true)) = _
  rw [show germWord T (e, true) = FreeGroup.of (⟨e, h⟩ : NonTree T) by simp [germWord, h]]; rfl

theorem piE_single_tree {x : CovQ T N × K.E} (h : T.isTree x.2) (n : ℤ) :
    piE T N (Finsupp.single x n) = 0 := by classical simp [piE, h]

theorem piE_single_nontree {x : CovQ T N × K.E} (h : ¬ T.isTree x.2) (n : ℤ) :
    piE T N (Finsupp.single x n) = Finsupp.single (x.1, (⟨x.2, h⟩ : NonTree T)) n := by
  classical simp [piE, h, Finsupp.smul_single]

@[simp] theorem piV_single (x : CovQ T N × K.V) (n : ℤ) :
    piV T N (Finsupp.single x n) = Finsupp.single x.1 n := by simp [piV, Finsupp.lmapDomain_apply]

@[simp] theorem iotaV_single (q : CovQ T N) (n : ℤ) :
    iotaV T N (Finsupp.single q n) = Finsupp.single (q, T.root) n := by simp [iotaV, Finsupp.lmapDomain_apply]

theorem pathWord_loopPath (ε : NonTree T) : pathWord T (loopPath T ε) = FreeGroup.of ε := by
  classical
  rw [loopPath, conjPath, pathWord_append, pathWord_append, pathWord_treePath,
    pathWord_revPath, pathWord_treePath]
  simp [pathWord, germWord, dif_neg ε.2]

theorem bdry1_apply (X : Complex2.{u}) (z : X.E →₀ ℤ) (w : X.V) :
    bdry1 X z w = ∑ x ∈ z.support, z x *
      ((Finsupp.single (X.tgt x) (1 : ℤ)) w - (Finsupp.single (X.src x) (1 : ℤ)) w) := by
  classical
  rw [bdry1, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.finset_sum_apply]
  exact Finset.sum_congr rfl fun _ _ => by rw [Finsupp.smul_apply, Finsupp.sub_apply, smul_eq_mul]

def treeTop {e : K.E} (he : T.isTree e) : K.V := ((T.isTree_iff e).1 he).choose

theorem treeTop_eq {e : K.E} (he : T.isTree e) {a : K.V} (ha : a ≠ T.root)
    (h : (T.up a ha).1 = e) : treeTop he = a := by
  have hunique {x y : K.V} (hx : x ≠ T.root) (hy : y ≠ T.root)
      (hxy : (T.up x hx).1 = (T.up y hy).1) : x = y := by
    have h1 := T.up_src x hx; have h2 := T.up_src y hy
    by_cases hs : (T.up x hx).2 = (T.up y hy).2
    · rw [Prod.ext hxy hs, h2] at h1; exact h1.symm
    · have huv : T.up y hy = revGerm (T.up x hx) :=
        Prod.ext hxy.symm (by show (T.up y hy).2 = !(T.up x hx).2; cases hux : (T.up x hx).2 <;> cases huy : (T.up y hy).2 <;> simp_all)
      have hb' : y = T.parent x hx := by rw [← h2, huv]; simp [parent]
      have ha' : T.parent y hy = x := by show germTgt K.src K.tgt (T.up y hy) = x; rw [huv]; simpa using h1
      have h3 := T.ht_parent hx; have h4 := T.ht_parent hy
      rw [← hb'] at h3; rw [ha'] at h4; omega
  exact hunique ((T.isTree_iff e).1 he).choose_spec.choose ha
    (((T.isTree_iff e).1 he).choose_spec.choose_spec.trans h.symm)

theorem tree_edge_endpoints {e : K.E} {a : K.V} (ha : a ≠ T.root) (hup : (T.up a ha).1 = e) :
    (K.src e = a ∧ K.tgt e = T.parent a ha) ∨ (K.src e = T.parent a ha ∧ K.tgt e = a) := by
  have hsrc := T.up_src a ha
  have htgt : germTgt K.src K.tgt (T.up a ha) = T.parent a ha := rfl
  cases hb : (T.up a ha).2
  · rw [show T.up a ha = (e, false) from Prod.ext hup hb] at hsrc htgt; exact .inr ⟨htgt, hsrc⟩
  · rw [show T.up a ha = (e, true) from Prod.ext hup hb] at hsrc htgt; exact .inl ⟨hsrc, htgt⟩

theorem parent_ne_self {a : K.V} (ha : a ≠ T.root) : T.parent a ha ≠ a := by
  intro h; have h1 := T.ht_parent ha; rw [h] at h1; omega

section
variable [DecidableEq (NonTree T)]

theorem support_isTree_of_piE_eq_zero {z : (CovQ T N × K.E) →₀ ℤ} (h : piE T N z = 0) :
    ∀ x ∈ z.support, T.isTree x.2 := by
  have happly (w : (CovQ T N × K.E) →₀ ℤ) (q : CovQ T N) (ε : NonTree T) :
      piE T N w (q, ε) = w (q, (ε : K.E)) := by
    classical
    induction w using Finsupp.induction_linear with
    | zero => simp
    | add z₁ z₂ h₁ h₂ => rw [map_add, Finsupp.add_apply, Finsupp.add_apply, h₁, h₂]
    | single x n =>
        by_cases ht : T.isTree x.2
        · rw [piE_single_tree (N := N) ht n]
          have hne : x ≠ (q, (ε : K.E)) := fun hc => ε.2 (by rw [hc] at ht; exact ht)
          simp [hne]
        · rw [piE_single_nontree (N := N) ht n, Finsupp.single_apply, Finsupp.single_apply]
          congr 1; simp only [Prod.ext_iff, Subtype.ext_iff]
  intro x hx; by_contra hnt
  have hval := happly z x.1 ⟨x.2, hnt⟩
  rw [h] at hval
  exact (Finsupp.mem_support_iff.1 hx) (by simpa using hval.symm)

end

variable [N.Normal]

theorem germQ_eq_one_of_isTree {g : K.E × Bool} (h : T.isTree g.1) : germQ T N g = 1 := by
  show QuotientGroup.mk (germWord T g) = 1; rw [germWord_of_isTree T h]; rfl

theorem piE_pathChain_liftK (L : List (K.E × Bool)) (q : CovQ T N) :
    piE T N (pathChain (liftK T N L q)) = pathChain (liftPath (letters T L) q) := by
  classical
  induction L generalizing q with
  | nil => simp [pathChain, letters]
  | cons g L ih =>
      obtain ⟨e, b⟩ := g
      by_cases h : T.isTree e
      · have hq : q * germQ T N (e, b) = q := by
          rw [germQ_eq_one_of_isTree (N := N) (g := (e, b)) h, mul_one]
        have hsnd : (liftGerm T N q (e, b)).2 = b := by cases b <;> rfl
        have hz : piE T N (Finsupp.single (liftGerm T N q (e, b)).1 (1 : ℤ)) = 0 :=
          piE_single_tree (N := N) (by cases b <;> exact h) 1
        rw [liftK_cons, pathChain_cons, map_add, letters_cons_tree (g := (e, b)) h, hq, ih q, hsnd]
        cases b <;> simp [hz]
      · rw [liftK_cons, pathChain_cons, map_add, letters_cons_nontree (g := (e, b)) h]
        cases b
        · change piE T N (-Finsupp.single (q * germQ T N (e, false), e) 1) + _ = _
          rw [map_neg, piE_single_nontree (N := N) h 1, ih (q * germQ T N (e, false)),
            germQ_false_eq_inv, germQ_true_eq_qof (N := N) h, liftPath_cons_false, pathChain_cons]
          simp
        · change piE T N (Finsupp.single (q, e) 1) + _ = _
          rw [piE_single_nontree (N := N) h 1, germQ_true_eq_qof (N := N) h,
            ih (q * qof N ⟨e, h⟩), liftPath_cons_true, pathChain_cons]
          simp

variable (T) in
def sectionE : ((CovQ T N × NonTree T) →₀ ℤ) →ₗ[ℤ] ((CovQ T N × K.E) →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x : CovQ T N × NonTree T =>
    pathChain (liftK T N (loopPath T x.2) x.1))

theorem covTgt_of_isTree {e : K.E} (he : T.isTree e) (q : CovQ T N) :
    covTgt T N (q, e) = (q, K.tgt e) := by
  show (q * germQ T N (e, true), K.tgt e) = (q, K.tgt e)
  rw [germQ_eq_one_of_isTree (N := N) (g := (e, true)) he, mul_one]

variable (hN : ∀ f, treeRel T f ∈ N)

theorem treeChain_eq_zero {z : (CovQ T N × K.E) →₀ ℤ}
    (hsupp : ∀ x ∈ z.support, T.isTree x.2)
    (hz : bdry1 (treeCover T N hN) z = 0) : z = 0 := by
  classical
  by_contra hzne
  obtain ⟨x₀, hx₀mem, hx₀max⟩ := z.support.exists_max_image
    (fun x => if h : T.isTree x.2 then T.ht (treeTop h) else 0)
    (Finsupp.support_nonempty_iff.2 hzne)
  have he₀ : T.isTree x₀.2 := hsupp x₀ hx₀mem
  obtain ⟨a₀, ha₀ne, ha₀up⟩ := (T.isTree_iff x₀.2).1 he₀
  have hg (x) (hx : x ∈ z.support) (a : K.V) (ha : a ≠ T.root) (hup : (T.up a ha).1 = x.2) :
      (if h : T.isTree x.2 then T.ht (treeTop h) else 0) = T.ht a := by
    rw [dif_pos (hsupp x hx), treeTop_eq (hsupp x hx) ha hup]
  have hterm : ∀ x ∈ z.support, x ≠ x₀ →
      z x * ((Finsupp.single ((treeCover T N hN).tgt x) (1 : ℤ)) (x₀.1, a₀)
        - (Finsupp.single ((treeCover T N hN).src x) (1 : ℤ)) (x₀.1, a₀)) = 0 := by
    intro x hx hxne
    have hex : T.isTree x.2 := hsupp x hx
    obtain ⟨a, hane, haup⟩ := (T.isTree_iff x.2).1 hex
    have hle : T.ht a ≤ T.ht a₀ := by
      simpa [hg x hx a hane haup, hg x₀ hx₀mem a₀ ha₀ne ha₀up] using hx₀max x hx
    have key (v : K.V) (hv : v = K.src x.2 ∨ v = K.tgt x.2) : (x.1, v) ≠ (x₀.1, a₀) := by
      intro hc
      obtain ⟨hq, rfl⟩ := Prod.mk.inj hc
      have hvertex (haa : a = v) : False := hxne (Prod.ext hq (haup.symm.trans (haa ▸ ha₀up)))
      have hparent (hp : T.parent a hane = v) : False := by
        have hht := T.ht_parent hane; rw [hp] at hht; omega
      rcases tree_edge_endpoints hane haup with ⟨hs, ht⟩ | ⟨hs, ht⟩ <;>
        rcases hv with rfl | rfl <;>
        first | exact hvertex hs.symm | exact hvertex ht.symm | exact hparent hs.symm | exact hparent ht.symm
    have h1 : (treeCover T N hN).tgt x ≠ (x₀.1, a₀) := by
      rw [treeCover_tgt, show x = (x.1, x.2) from rfl, covTgt_of_isTree (N := N) hex]
      exact key (K.tgt x.2) (Or.inr rfl)
    have h2 : (treeCover T N hN).src x ≠ (x₀.1, a₀) := key (K.src x.2) (Or.inl rfl)
    rw [Finsupp.single_eq_of_ne h1.symm, Finsupp.single_eq_of_ne h2.symm, sub_self, mul_zero]
  have hzero : (0 : ℤ) = z x₀ *
      ((Finsupp.single ((treeCover T N hN).tgt x₀) (1 : ℤ)) (x₀.1, a₀)
        - (Finsupp.single ((treeCover T N hN).src x₀) (1 : ℤ)) (x₀.1, a₀)) := by
    have h := bdry1_apply (treeCover T N hN) z (x₀.1, a₀)
    rw [hz] at h
    exact h.trans (Finset.sum_eq_single_of_mem x₀ hx₀mem hterm)
  have hzx₀ : z x₀ ≠ 0 := Finsupp.mem_support_iff.1 hx₀mem
  have hsrc : (treeCover T N hN).src x₀ = (x₀.1, K.src x₀.2) := rfl
  have htgt : (treeCover T N hN).tgt x₀ = (x₀.1, K.tgt x₀.2) := by
    rw [treeCover_tgt, show x₀ = (x₀.1, x₀.2) from rfl, covTgt_of_isTree (N := N) he₀]
  have hpne : T.parent a₀ ha₀ne ≠ a₀ := parent_ne_self (T := T) ha₀ne
  rcases tree_edge_endpoints ha₀ne ha₀up with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · have h1 : (treeCover T N hN).tgt x₀ ≠ (x₀.1, a₀) := by rw [htgt, ht]; exact fun hc => hpne (Prod.mk.inj hc).2
    have h2 : (treeCover T N hN).src x₀ = (x₀.1, a₀) := by rw [hsrc, hs]
    rw [Finsupp.single_eq_of_ne h1.symm, h2, Finsupp.single_eq_same] at hzero
    simp at hzero; omega
  · have h1 : (treeCover T N hN).tgt x₀ = (x₀.1, a₀) := by rw [htgt, ht]
    have h2 : (treeCover T N hN).src x₀ ≠ (x₀.1, a₀) := by rw [hsrc, hs]; exact fun hc => hpne (Prod.mk.inj hc).2
    rw [Finsupp.single_eq_of_ne h2.symm, h1, Finsupp.single_eq_same] at hzero
    simp at hzero; omega

variable [DecidableEq (NonTree T)]

omit hN in
theorem pathChain_liftPath_congr {L L' : List (NonTree T × Bool)}
    (h : FreeGroup.mk L = FreeGroup.mk L') (q : CovQ T N) :
    pathChain (liftPath (Nsub := N) L q) = pathChain (liftPath (Nsub := N) L' q) := by
  apply (fsCoords N (NonTree T)).injective
  ext i
  rw [fsCoords_pathChain_liftPath_apply, fsCoords_pathChain_liftPath_apply, h]

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
      exact congrArg (n • ·) (pathChain_liftPath_congr (N := N) (by rw [mk_letters, FreeGroup.mk_toWord]; rfl) q)

theorem piV_bdry1 (c : (CovQ T N × K.E) →₀ ℤ) :
    piV T N (bdry1 (treeCover T N hN) c) = bdry1 (coverComplex N (treeRel T) hN) (piE T N c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => rw [map_add, map_add, map_add, map_add, h₁, h₂]
  | single x n =>
      obtain ⟨q, e⟩ := x
      rw [bdry1_single]
      by_cases h : T.isTree e
      · rw [piE_single_tree (N := N) (x := (q, e)) h n, map_zero]
        show piV T N (n • (Finsupp.single (covTgt T N (q, e)) 1 - Finsupp.single (covSrc T N (q, e)) 1)) = 0
        rw [map_smul, map_sub, piV_single, piV_single]
        show n • (Finsupp.single (q * germQ T N (e, true)) 1 - Finsupp.single q 1) = 0
        rw [germQ_eq_one_of_isTree (N := N) (g := (e, true)) h, mul_one, sub_self, smul_zero]
      · rw [piE_single_nontree (N := N) (x := (q, e)) h n, bdry1_single]
        show piV T N (n • (Finsupp.single (covTgt T N (q, e)) 1 - Finsupp.single (covSrc T N (q, e)) 1)) = _
        rw [map_smul, map_sub, piV_single, piV_single]
        show n • (Finsupp.single (q * germQ T N (e, true)) 1 - Finsupp.single q 1) = _
        rw [germQ_true_eq_qof (N := N) h]

theorem augC_piV (c : (CovQ T N × K.V) →₀ ℤ) :
    augC (coverComplex N (treeRel T) hN) (piV T N c) = augC (treeCover T N hN) c := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]
  | single x n =>
      obtain ⟨q, a⟩ := x
      rw [piV_single]
      show augC (coverComplex N (treeRel T) hN) (Finsupp.single q n) = _
      rw [augC_single, augC_single]

theorem bdry1_sectionE (u : (CovQ T N × NonTree T) →₀ ℤ) :
    bdry1 (treeCover T N hN) (sectionE T N u)
      = iotaV T N (bdry1 (coverComplex N (treeRel T) hN) u) := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u₁ u₂ h₁ h₂ => rw [map_add, map_add, map_add, map_add, h₁, h₂]
  | single x n =>
      obtain ⟨q, ε⟩ := x
      have hpath := liftK_isPath (T := T) (N := N) (L := loopPath T ε)
        (conjPath_isLoop T (isPath_single _)) q
      rw [show wordQ T N (loopPath T ε) = qof N ε by
        show QuotientGroup.mk (pathWord T (loopPath T ε)) = _; rw [pathWord_loopPath]; rfl] at hpath
      rw [sectionE, Finsupp.linearCombination_single, map_smul, bdry1_single,
        bdry1_pathChain_of_isPath (X := treeCover T N hN) hpath, map_smul, map_sub,
        iotaV_single, iotaV_single]
