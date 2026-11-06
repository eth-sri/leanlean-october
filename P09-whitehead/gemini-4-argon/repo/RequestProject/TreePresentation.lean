module

public import RequestProject.SpanningTree
public import RequestProject.PresentationDictionary

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FiniteChains.Comb.SpanningTree

universe u

variable {K : Complex2.{u}} (T : SpanningTree K)

abbrev NonTree (T : SpanningTree K) : Type u := {e : K.E // ¬ T.isTree e}

open Classical in
def germWord (g : K.E × Bool) : FreeGroup (NonTree T) :=
  if h : T.isTree g.1 then 1 else
    if g.2 then FreeGroup.of (⟨g.1, h⟩ : NonTree T) else (FreeGroup.of (⟨g.1, h⟩ : NonTree T))⁻¹

def pathWord (l : List (K.E × Bool)) : FreeGroup (NonTree T) := (l.map (germWord T)).prod

def treeRel (f : K.F) : FreeGroup (NonTree T) := pathWord T (K.att f)

@[simp] theorem pathWord_nil : pathWord T [] = 1 := rfl

theorem pathWord_cons (g : K.E × Bool) (l : List (K.E × Bool)) :
    pathWord T (g :: l) = germWord T g * pathWord T l := by simp [pathWord]

theorem pathWord_append (l l' : List (K.E × Bool)) :
    pathWord T (l ++ l') = pathWord T l * pathWord T l' := by simp [pathWord, List.prod_append]

theorem germWord_revGerm (g : K.E × Bool) :
    germWord T (revGerm g) = (germWord T g)⁻¹ := by
  classical
  rcases g with ⟨e, false | true⟩ <;> by_cases h : T.isTree e <;> simp [germWord, revGerm, h]

theorem pathWord_revPath : ∀ l : List (K.E × Bool),
    pathWord T (revPath l) = (pathWord T l)⁻¹
  | [] => by simp [revPath]
  | g :: l => by
      rw [revPath_cons, pathWord_append, pathWord_revPath l, pathWord_cons, germWord_revGerm]
      simp [pathWord]

theorem germWord_of_isTree {g : K.E × Bool} (h : T.isTree g.1) : germWord T g = 1 := by
  classical simp [germWord, h]

theorem pathWord_eq_one_of_tree : ∀ {l : List (K.E × Bool)}, (∀ g ∈ l, T.isTree g.1) →
    pathWord T l = 1
  | [], _ => rfl
  | g :: l, hl => by
      rw [pathWord_cons, germWord_of_isTree T (hl g (by simp)), one_mul]
      exact pathWord_eq_one_of_tree fun g' hg' => hl g' (by simp [hg'])

@[simp] theorem pathWord_treePath (a : K.V) : pathWord T (T.treePath a) = 1 :=
  pathWord_eq_one_of_tree T fun _ hg => T.isTree_of_mem_treePath a hg

def wordClass (l : List (K.E × Bool)) : PresGroup (treeRel T) :=
  QuotientGroup.mk (pathWord T l)

theorem wordClass_append (l l' : List (K.E × Bool)) :
    wordClass T (l ++ l') = wordClass T l * wordClass T l' := by
  unfold wordClass; rw [pathWord_append, QuotientGroup.mk_mul]

theorem wordClass_cancels {l l' : List (K.E × Bool)} (h : Cancels K l l') :
    wordClass T l = wordClass T l' := by
  rcases h with ⟨p, q, g, rfl, rfl⟩ | ⟨p, q, f, rfl, rfl⟩
  · rw [wordClass_append, wordClass_append]; congr 1
    show QuotientGroup.mk (pathWord T (g :: revGerm g :: q)) = QuotientGroup.mk (pathWord T q)
    rw [pathWord_cons, pathWord_cons, germWord_revGerm]; group
  · rw [wordClass_append, wordClass_append, wordClass_append,
      show wordClass T (K.att f) = 1 by
        rw [show wordClass T (K.att f) = QuotientGroup.mk (treeRel T f) from rfl, QuotientGroup.eq_one_iff]
        exact Subgroup.subset_normalClosure ⟨f, rfl⟩, mul_one]

theorem wordClass_htpy {a b : K.V} {l l' : List (K.E × Bool)} (h : Htpy K a b l l') :
    wordClass T l = wordClass T l' := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      exact ih.trans (hstep.elim (fun hs => wordClass_cancels T hs.2.2)
        fun hs => (wordClass_cancels T hs.2.2).symm)

def pi1ToPres : Pi1 K T.root →* PresGroup (treeRel T) where
  toFun := Quotient.lift (fun p => wordClass T p.1) (fun _ _ h => wordClass_htpy T h)
  map_one' := rfl
  map_mul' := by rintro ⟨p⟩ ⟨q⟩; exact wordClass_append T p.1 q.1

def conjPath (l : List (K.E × Bool)) (a b : K.V) : List (K.E × Bool) :=
  T.treePath a ++ l ++ revPath (T.treePath b)

theorem conjPath_isLoop {l : List (K.E × Bool)} {a b : K.V}
    (hl : IsPath K.src K.tgt l a b) :
    IsPath K.src K.tgt (conjPath T l a b) T.root T.root :=
  isPath_append_iff.mpr ⟨b, isPath_append_iff.mpr ⟨a, T.treePath_isPath a, hl⟩,
    isPath_revPath (T.treePath_isPath b)⟩

def loopOf {l : List (K.E × Bool)} {a b : K.V}
    (hl : IsPath K.src K.tgt l a b) : Pi1 K T.root :=
  Pi1.mk ⟨conjPath T l a b, conjPath_isLoop T hl⟩

@[simp] theorem loopOf_nil (a : K.V) :
    loopOf T (l := []) (a := a) (b := a) rfl = 1 :=
  Quotient.sound (by show Htpy K T.root T.root (conjPath T [] a a) []; simpa [conjPath] using htpy_append_revPath (T.treePath_isPath a))

theorem loopOf_mul {p q : List (K.E × Bool)} {a m b : K.V}
    (hp : IsPath K.src K.tgt p a m) (hq : IsPath K.src K.tgt q m b) :
    loopOf T hp * loopOf T hq = loopOf T (hp.append hq) := by
  refine Quotient.sound ?_
  show Htpy K T.root T.root (conjPath T p a m ++ conjPath T q m b) (conjPath T (p ++ q) a b)
  simpa [conjPath, List.append_assoc] using
    (htpy_revPath_append (T.treePath_isPath m)).congr_append
      (isPath_append_iff.mpr ⟨a, T.treePath_isPath a, hp⟩)
      (isPath_append_iff.mpr ⟨b, hq, isPath_revPath (T.treePath_isPath b)⟩)

theorem loopOf_rev {l : List (K.E × Bool)} {a b : K.V} (hl : IsPath K.src K.tgt l a b) :
    loopOf T (isPath_revPath hl) = (loopOf T hl)⁻¹ := by
  refine Quotient.sound ?_
  show Htpy K T.root T.root (conjPath T (revPath l) b a) (revPath (conjPath T l a b))
  rw [show revPath (conjPath T l a b) = conjPath T (revPath l) b a by
    simp [conjPath, revPath_append, List.append_assoc, revPath_revPath]]

theorem loopOf_eq {l l' : List (K.E × Bool)} {a b a' b' : K.V}
    (hl : IsPath K.src K.tgt l a b) (hl' : IsPath K.src K.tgt l' a' b')
    (hll : l = l') (ha : a = a') (hb : b = b') : loopOf T hl = loopOf T hl' := by
  subst hll ha hb; rfl

def genLoop (e : NonTree T) : Pi1 K T.root :=
  loopOf T (isPath_single ((e : K.E), true))

def freeToPi1 : FreeGroup (NonTree T) →* Pi1 K T.root := FreeGroup.lift (genLoop T)

@[simp] theorem freeToPi1_of (e : NonTree T) :
    freeToPi1 T (FreeGroup.of e) = genLoop T e := by simp [freeToPi1]

theorem loopOf_up {a : K.V} (ha : a ≠ T.root) :
    loopOf T (isPath_single (T.up a ha)) = 1 := by
  set u := T.up a ha with hu
  set m := T.parent a ha with hm
  have hpar : T.treePath a = T.treePath m ++ [revGerm u] := T.treePath_of_ne ha
  refine Quotient.sound ?_
  show Htpy K T.root T.root (conjPath T [u] (germSrc K.src K.tgt u) (germTgt K.src K.tgt u)) []
  rw [show conjPath T [u] (germSrc K.src K.tgt u) (germTgt K.src K.tgt u) =
      (T.treePath m ++ [revGerm u, u]) ++ revPath (T.treePath m) by
    rw [conjPath, T.up_src a ha, show germTgt K.src K.tgt u = m from rfl, hpar]; simp]
  have hstep : Htpy K m m [revGerm u, u] [] :=
    Htpy.of_step ⟨⟨by simp [hm, parent, hu], by simp, rfl⟩, rfl, Or.inl ⟨[], [], revGerm u, by simp, rfl⟩⟩
  exact (hstep.congr_append (T.treePath_isPath m) (isPath_revPath (T.treePath_isPath m))).trans
    (by simpa using htpy_append_revPath (T.treePath_isPath m))

theorem freeToPi1_germWord (g : K.E × Bool) :
    freeToPi1 T (germWord T g) = loopOf T (isPath_single g) := by
  classical
  by_cases h : T.isTree g.1
  · rw [germWord_of_isTree T h, map_one]
    obtain ⟨a, ha, hae⟩ := (T.isTree_iff g.1).1 h
    by_cases hb : g.2 = (T.up a ha).2
    · obtain rfl : g = T.up a ha := Prod.ext hae.symm hb
      exact (loopOf_up T ha).symm
    · obtain rfl : g = revGerm (T.up a ha) := Prod.ext hae.symm
        (by show g.2 = !(T.up a ha).2; cases hg2 : g.2 <;> cases hu2 : (T.up a ha).2 <;> simp_all)
      have hrev := loopOf_rev T (isPath_single (T.up a ha))
      rw [loopOf_up T ha, inv_one] at hrev
      rw [loopOf_eq T (isPath_single (revGerm (T.up a ha)))
        (isPath_revPath (isPath_single (T.up a ha))) (by simp [revPath]) (by simp) (by simp)]
      exact hrev.symm
  · rcases g with ⟨e, false | true⟩
    · rw [show germWord T (e, false) = (FreeGroup.of (⟨e, h⟩ : NonTree T))⁻¹ by simp [germWord, h],
        map_inv, freeToPi1_of, genLoop, ← loopOf_rev T (isPath_single ((e, true) : K.E × Bool))]
    · rw [show germWord T (e, true) = FreeGroup.of (⟨e, h⟩ : NonTree T) by simp [germWord, h],
        freeToPi1_of, genLoop]

theorem freeToPi1_pathWord : ∀ {l : List (K.E × Bool)} {a b : K.V}
    (hl : IsPath K.src K.tgt l a b), freeToPi1 T (pathWord T l) = loopOf T hl
  | [], _, _, rfl => by simp [pathWord]
  | g :: l, _, _, ⟨rfl, hrest⟩ => by
      rw [pathWord_cons, map_mul, freeToPi1_germWord T g, freeToPi1_pathWord hrest,
        loopOf_mul T (isPath_single g) hrest]

theorem freeToPi1_treeRel (f : K.F) : freeToPi1 T (treeRel T f) = 1 := by
  have hf := K.att_isLoop f
  rw [show treeRel T f = pathWord T (K.att f) from rfl, freeToPi1_pathWord T hf]
  refine Quotient.sound ?_
  show Htpy K T.root T.root (conjPath T (K.att f) (K.base f) (K.base f)) []
  have hstep : Htpy K (K.base f) (K.base f) (K.att f) [] :=
    Htpy.of_step ⟨hf, rfl, Or.inr ⟨[], [], f, by simp, rfl⟩⟩
  exact (hstep.congr_append (T.treePath_isPath (K.base f))
    (isPath_revPath (T.treePath_isPath (K.base f)))).trans
    (by simpa using htpy_append_revPath (T.treePath_isPath (K.base f)))

theorem relSub_le_ker_freeToPi1 : relSub (treeRel T) ≤ (freeToPi1 T).ker :=
  Subgroup.normalClosure_le_normal (by rintro _ ⟨f, rfl⟩; exact freeToPi1_treeRel T f)

def presToPi1 : PresGroup (treeRel T) →* Pi1 K T.root :=
  QuotientGroup.lift (relSub (treeRel T)) (freeToPi1 T) fun _ hx => relSub_le_ker_freeToPi1 T hx

@[simp] theorem presToPi1_mk (w : FreeGroup (NonTree T)) :
    presToPi1 T (QuotientGroup.mk w) = freeToPi1 T w := rfl

theorem presToPi1_pi1ToPres (x : Pi1 K T.root) : presToPi1 T (pi1ToPres T x) = x := by
  induction x using Quotient.inductionOn with | h p =>
  obtain ⟨l, hl⟩ := p
  show presToPi1 T (wordClass T l) = Pi1.mk ⟨l, hl⟩
  rw [show wordClass T l = QuotientGroup.mk (pathWord T l) from rfl, presToPi1_mk,
    freeToPi1_pathWord T hl]
  exact Quotient.sound (by show Htpy K T.root T.root (conjPath T l T.root T.root) l; simpa [conjPath] using Htpy.refl l)

theorem pi1ToPres_presToPi1 (g : PresGroup (treeRel T)) :
    pi1ToPres T (presToPi1 T g) = g := by
  induction g using QuotientGroup.induction_on with | H w =>
  rw [presToPi1_mk]
  induction w using FreeGroup.induction_on with
  | one => simp
  | of e =>
      rw [freeToPi1_of, genLoop]
      show wordClass T (conjPath T [((e : K.E), true)] _ _) = _
      rw [conjPath, wordClass_append, wordClass_append,
        show wordClass T (T.treePath _) = 1 by simp [wordClass],
        show wordClass T (revPath (T.treePath _)) = 1 by simp [wordClass, pathWord_revPath],
        one_mul, mul_one]
      show QuotientGroup.mk (pathWord T [((e : K.E), true)]) = _
      classical simp [pathWord, germWord, dif_neg e.2]
  | inv_of _ ih => rw [map_inv, map_inv, ih, QuotientGroup.mk_inv]
  | mul _ _ hx hy => rw [map_mul, map_mul, hx, hy, ← QuotientGroup.mk_mul]

def pi1EquivPres : Pi1 K T.root ≃* PresGroup (treeRel T) where
  toFun := pi1ToPres T
  invFun := presToPi1 T
  left_inv := presToPi1_pi1ToPres T
  right_inv := pi1ToPres_presToPi1 T
  map_mul' := (pi1ToPres T).map_mul
