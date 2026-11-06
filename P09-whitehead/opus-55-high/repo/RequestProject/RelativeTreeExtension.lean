import RequestProject.TreePi2Reflection
import RequestProject.CombPushout
import RequestProject.Tac


/-! Undo a spanning-tree collapse relative to the original complex.
New generators are actual loops at the original tree root. An old
non-tree generator is read as its edge prefixed and suffixed by tree
paths. Original vertices, edges and two-cells are retained literally.
 -/

noncomputable section
open scoped Classical
bwd

namespace FiniteChains.Comb.RelativeTreeExtension
open SpanningTree

variable {D : Complex2} (T : SpanningTree D) {Z S : Type}

def source : D.E ⊕ Z → D.V := Sum.elim D.src (fun _ => T.root)
def target : D.E ⊕ Z → D.V := Sum.elim D.tgt (fun _ => T.root)

def loopGraph : Complex2 where
  V := D.V
  E := D.E ⊕ Z
  F := PEmpty
  src := source T
  tgt := target T
  base := PEmpty.elim
  att := PEmpty.elim
  att_isLoop f := PEmpty.elim f

def oldPath (l : List (D.E × Bool)) : List ((D.E ⊕ Z) × Bool) :=
  l.map (fun e => (Sum.inl e.1, e.2))

theorem oldPath_isPath
    (hl : IsPathX D l a b) :
    IsPath (source T) (target T) (oldPath (Z := Z) l) a b :=
  FiniteChains.Comb.isPath_map (src := D.src) (tgt := D.tgt)
    (src' := source T) (tgt' := target T) (·)
    _ (by aesop) (by aesop) hl

def generatorLoop : NonTree T ⊕ Z → List ((D.E ⊕ Z) × Bool)
  | Sum.inl e => oldPath (conjPath T [(e.val, true)] (D.src e.val) (D.tgt e.val))
  | Sum.inr z => [(Sum.inr z, true)]

theorem generatorLoop_isPath (a : NonTree T ⊕ Z) :
    IsPath (source T) (target T) (generatorLoop T a) T.root T.root := by
  cases a with
  | inl e => exact oldPath_isPath T (conjPath_isLoop T (by simp))
  | inr z => tauto

def signedLoop (e : (NonTree T ⊕ Z) × Bool) :=
  if e.2 then generatorLoop T e.1 else revPath (X := loopGraph (Z := Z) T) (generatorLoop T e.1)

theorem signedLoop_isPath (e : (NonTree T ⊕ Z) × Bool) :
    IsPath (source T) (target T) (signedLoop T e) T.root T.root := by
  cases' e with a b
  cases b
  · exact isPath_revPath (X := loopGraph (Z := Z) T) (generatorLoop_isPath T a)
  · exact generatorLoop_isPath T a

def readWord (l : List ((NonTree T ⊕ Z) × Bool)) :=
  l.flatMap (signedLoop T)

theorem readWord_isPath (l : List ((NonTree T ⊕ Z) × Bool)) :
    IsPath (source T) (target T) (readWord T l) T.root T.root := by
  induction l with
  | nil => rfl
  | cons a l ih => exact (signedLoop_isPath T a).append ih

variable (extra : S → FreeGroup (NonTree T ⊕ Z))

def complex : Complex2 where
  V := D.V
  E := D.E ⊕ Z
  F := D.F ⊕ S
  src := source T
  tgt := target T
  base := Sum.elim D.base (fun _ => T.root)
  att := Sum.elim (fun f => oldPath (D.att f)) (fun s => readWord T (extra s).toWord)
  att_isLoop := by
    intro f
    cases f with
    | inl f => exact oldPath_isPath T (D.att_isLoop f)
    | inr s => exact readWord_isPath T (extra s).toWord

def oldInclusion : Hom D (complex T extra) where
  onV := id
  onE := Sum.inl
  onF := Sum.inl
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF _ := rfl
  att_onF _ := rfl

def tree : SpanningTree (complex T extra) where
  root := T.root
  ht := T.ht
  isTree := Sum.elim T.isTree (fun _ => False)
  up a ha := (Sum.inl (T.up a ha).1, (T.up a ha).2)
  ht_root := T.ht_root
  ht_eq_zero := T.ht_eq_zero
  up_src := by
    intro a ha
    cases hb : (T.up a ha).2 <;>
      simpa only [germSrc, hb, Bool.false_eq_true, if_false, if_true, source, target, complex, Sum.elim_inl] using T.up_src a ha
  up_ht := by
    intro a ha
    cases hb : (T.up a ha).2 <;>
      simpa only [germTgt, hb, Bool.false_eq_true, if_false, if_true, target, source, complex, Sum.elim_inl] using T.up_ht a ha
  isTree_iff := by
    intro e
    cases e with
    | inl e =>
        change T.isTree e ↔ ∃ a ha, Sum.inl (T.up a ha).1 = Sum.inl e
        simpa [Sum.inl.injEq] using T.isTree_iff e
    | inr z =>
        simp

theorem tree_old e :
    (tree T extra).isTree ((oldInclusion T extra).onE e) ↔ T.isTree e := Iff.rfl

def generatorEquiv : NonTree (tree T extra) ≃ NonTree T ⊕ Z where
  toFun e := match e with
    | ⟨Sum.inl e, he⟩ => Sum.inl ⟨e, he⟩
    | ⟨Sum.inr z, _⟩ => Sum.inr z
  invFun a := match a with
    | Sum.inl e => ⟨Sum.inl e.val, e.property⟩
    | Sum.inr z => ⟨Sum.inr z, not_false⟩
  left_inv e := by grind
  right_inv a := by grind

theorem oldPath_collapsed l :
    FreeGroup.map (generatorEquiv T extra)
      (pathWord (tree T extra) (oldPath (Z := Z) l)) =
        FreeGroup.map Sum.inl (pathWord T l) := by
  change FreeGroup.map (generatorEquiv T extra)
    (pathWord _ (mapPath (oldInclusion T extra) l)) = _
  rw [pathWord_mapPath (tree_old T extra), FreeGroup.map.comp]
  rfl

theorem generatorLoop_collapsed a :
    FreeGroup.map (generatorEquiv T extra)
      (pathWord (tree T extra) (generatorLoop T a)) = FreeGroup.of a := by
  cases a with
  | inl e =>
      rw [generatorLoop, oldPath_collapsed]
      simp [conjPath, pathWord_append, pathWord_revPath, pathWord_cons,
        germWord, e.property]
  | inr z =>
      change FreeGroup.map (generatorEquiv T extra)
        (pathWord _ [(Sum.inr z, true)]) = _
      rw [pathWord_cons, pathWord_nil, mul_one]
      simp [germWord, tree, generatorEquiv]

theorem readWord_collapsed l :
    FreeGroup.map (generatorEquiv T extra)
      (pathWord (tree T extra) (readWord T l)) = FreeGroup.mk l := by
  induction l with
  | nil => rfl
  | cons e l ih =>
      cases' e with a b
      cases b
      · have happ := pathWord_append (tree T extra)
          (revPath (X := complex T extra) (generatorLoop T a)) (readWord T l)
        have hrev := pathWord_revPath (tree T extra) (generatorLoop T a)
        have hpw : pathWord _ (readWord T ((a, false) :: l)) =
            (pathWord _ (generatorLoop T a))⁻¹ *
              pathWord (tree T extra) (readWord T l) :=
          by aesop
        rw [hpw, map_mul, map_inv,
          generatorLoop_collapsed, ih, mk_cons_false]
      · change FreeGroup.map (generatorEquiv T extra)
          (pathWord _ (generatorLoop T a ++ readWord T l)) = _
        rw [pathWord_append, map_mul, generatorLoop_collapsed, ih, mk_cons_true]

/-- Collapsing the retained tree recovers exactly the prescribed relative
presentation; no homotopy classification assumption occurs here. -/
theorem treeRel_equation (f : D.F ⊕ S) :
    FreeGroup.map (generatorEquiv T extra) (treeRel (tree T extra) f) =
      Sum.elim (fun d => FreeGroup.map Sum.inl (treeRel T d)) extra f := by
  cases f with
  | inl f => exact oldPath_collapsed T extra _
  | inr s =>
      change FreeGroup.map (generatorEquiv T extra)
        (pathWord _ (readWord T (extra s).toWord)) = extra s
      rw [readWord_collapsed, FreeGroup.mk_toWord]

theorem connected : IsConnected (complex T extra) := by
  intro a b
  exact ⟨oldPath (revPath (T.treePath a) ++ T.treePath b),
    oldPath_isPath T ((isPath_revPath (T.treePath_isPath a)).append (T.treePath_isPath b))⟩
