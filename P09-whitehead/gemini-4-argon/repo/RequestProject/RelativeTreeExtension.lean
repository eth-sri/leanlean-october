module

public import RequestProject.TreePi2Reflection
public import RequestProject.CombPushout

@[expose] public section

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false

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

theorem oldPath_isPath {l : List (D.E × Bool)} {a b : D.V}
    (hl : IsPath D.src D.tgt l a b) :
    IsPath (source T) (target T) (oldPath (Z := Z) l) a b :=
  FiniteChains.Comb.isPath_map (src := D.src) (tgt := D.tgt)
    (src' := source T) (tgt' := target T) (fun x : D.V => x)
    (Sum.inl : D.E → D.E ⊕ Z) (fun _ => rfl) (fun _ => rfl) hl

def generatorLoop : NonTree T ⊕ Z → List ((D.E ⊕ Z) × Bool)
  | Sum.inl e => oldPath (conjPath T [(e.val, true)] (D.src e.val) (D.tgt e.val))
  | Sum.inr z => [(Sum.inr z, true)]

def signedLoop (e : (NonTree T ⊕ Z) × Bool) : List ((D.E ⊕ Z) × Bool) :=
  if e.2 then generatorLoop T e.1 else revPath (X := loopGraph (Z := Z) T) (generatorLoop T e.1)

def readWord (l : List ((NonTree T ⊕ Z) × Bool)) : List ((D.E ⊕ Z) × Bool) :=
  l.flatMap (signedLoop T)

theorem readWord_isPath (l : List ((NonTree T ⊕ Z) × Bool)) :
    IsPath (source T) (target T) (readWord T l) T.root T.root := by
  have hgen : ∀ a : NonTree T ⊕ Z, IsPath (source T) (target T) (generatorLoop T a) T.root T.root
    | .inl e => oldPath_isPath T (conjPath_isLoop T (isPath_single (e.val, true)))
    | .inr _ => ⟨rfl, rfl⟩
  induction l with
  | nil => rfl
  | cons a l ih =>
      refine IsPath.append ?_ ih
      rcases a with ⟨a, _ | _⟩
      exacts [isPath_revPath (X := loopGraph (Z := Z) T) (hgen a), hgen a]

variable (extra : S → FreeGroup (NonTree T ⊕ Z))

def complex : Complex2 where
  V := D.V
  E := D.E ⊕ Z
  F := D.F ⊕ S
  src := source T
  tgt := target T
  base := Sum.elim D.base (fun _ => T.root)
  att := Sum.elim (fun f => oldPath (D.att f)) (fun s => readWord T (extra s).toWord)
  att_isLoop | .inl f => oldPath_isPath T (D.att_isLoop f) | .inr s => readWord_isPath T (extra s).toWord

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
  up_src a ha := by
    cases hb : (T.up a ha).2 <;>
      simpa only [germSrc, hb, Bool.false_eq_true, if_false, if_true, source, target, complex, Sum.elim_inl] using T.up_src a ha
  up_ht a ha := by
    cases hb : (T.up a ha).2 <;>
      simpa only [germTgt, hb, Bool.false_eq_true, if_false, if_true, target, source, complex, Sum.elim_inl] using T.up_ht a ha
  isTree_iff
    | .inl e => by
        change T.isTree e ↔ ∃ a ha, Sum.inl (T.up a ha).1 = Sum.inl e
        simpa only [Sum.inl.injEq] using T.isTree_iff e
    | .inr z => by
        change False ↔ ∃ a ha, Sum.inl (T.up a ha).1 = Sum.inr z
        simp

def generatorEquiv : NonTree (tree T extra) ≃ NonTree T ⊕ Z where
  toFun | ⟨Sum.inl e, he⟩ => Sum.inl ⟨e, he⟩ | ⟨Sum.inr z, _⟩ => Sum.inr z
  invFun | Sum.inl e => ⟨Sum.inl e.val, e.property⟩ | Sum.inr z => ⟨Sum.inr z, not_false⟩
  left_inv := by rintro ⟨_ | _, _⟩ <;> rfl
  right_inv := by rintro (_ | _) <;> rfl

theorem oldPath_collapsed (l : List (D.E × Bool)) :
    FreeGroup.map (generatorEquiv T extra)
      (pathWord (tree T extra) (oldPath (Z := Z) l)) =
        FreeGroup.map Sum.inl (pathWord T l) := by
  change FreeGroup.map (generatorEquiv T extra)
    (pathWord (tree T extra) (mapPath (oldInclusion T extra) l)) = _
  rw [pathWord_mapPath (fun _ => Iff.rfl), FreeGroup.map.comp]; rfl

theorem treeRel_equation (f : D.F ⊕ S) :
    FreeGroup.map (generatorEquiv T extra) (treeRel (tree T extra) f) =
      Sum.elim (fun d => FreeGroup.map Sum.inl (treeRel T d)) extra f := by
  have hgen (a : NonTree T ⊕ Z) :
      FreeGroup.map (generatorEquiv T extra) (pathWord (tree T extra) (generatorLoop T a)) =
        FreeGroup.of a := by
    cases a with
    | inl e =>
        rw [generatorLoop, oldPath_collapsed]
        simp [conjPath, pathWord_append, pathWord_revPath, pathWord_cons, germWord, e.property]
    | inr z =>
        change FreeGroup.map (generatorEquiv T extra) (pathWord (tree T extra) [(Sum.inr z, true)]) = _
        rw [pathWord_cons, pathWord_nil, mul_one]
        simp [germWord, tree, generatorEquiv]
  cases f with
  | inl f => exact oldPath_collapsed T extra (D.att f)
  | inr s =>
      have hread : ∀ l : List ((NonTree T ⊕ Z) × Bool),
          FreeGroup.map (generatorEquiv T extra) (pathWord (tree T extra) (readWord T l)) =
            FreeGroup.mk l := by
        intro l; induction l with
        | nil =>
            change FreeGroup.map _ (pathWord (tree T extra) []) = FreeGroup.mk []
            rw [pathWord_nil, map_one]; rfl
        | cons e l ih =>
            rcases e with ⟨a, _ | _⟩
            · have hpw : pathWord (tree T extra) (readWord T ((a, false) :: l)) =
                  (pathWord (tree T extra) (generatorLoop T a))⁻¹ *
                    pathWord (tree T extra) (readWord T l) :=
                (pathWord_append (tree T extra)
                  (revPath (X := complex T extra) (generatorLoop T a)) (readWord T l)).trans
                  (congrArg (· * pathWord (tree T extra) (readWord T l))
                    (pathWord_revPath (tree T extra) (generatorLoop T a)))
              rw [hpw, map_mul, map_inv, hgen, ih, mk_cons_false]
            · change FreeGroup.map (generatorEquiv T extra)
                (pathWord (tree T extra) (generatorLoop T a ++ readWord T l)) = _
              rw [pathWord_append, map_mul, hgen, ih, mk_cons_true]
      change FreeGroup.map (generatorEquiv T extra)
        (pathWord (tree T extra) (readWord T (extra s).toWord)) = extra s
      rw [hread, FreeGroup.mk_toWord]

theorem connected : IsConnected (complex T extra) :=
  fun a b => ⟨oldPath (revPath (T.treePath a) ++ T.treePath b),
    oldPath_isPath T ((isPath_revPath (T.treePath_isPath a)).append (T.treePath_isPath b))⟩

end FiniteChains.Comb.RelativeTreeExtension
