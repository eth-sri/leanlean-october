module

public import Chazelle.Core.ClusterSep

/-!
# WP-I, part 15: the centroid split of a piece

For a planar map with a spanning tree `T`, a rooted cotree `C`, a choice `δ v` of a dart at every
vertex and a piece `P` of vertices:

* `cnt P x` counts the vertices of `P` whose chosen face lies in the subtree of the face `x`;
  `Good P x` means more than half of `P`;
* `centroid_half`: if `f` is good but none of its children is, every side of the fundamental
  cycle of a non-tree dart of `f` holds at most half of `P`;
* `split_classes`: with an enumeration `x 0, x 1, x 2` of the darts of `f`, the classes
  `cls t = {v ∈ P off sepSet f : x t is a non-tree dart and v's face is beyond x t}` partition
  `P \ sepSet f`, have at most half of `P` each, and no edge off `sepSet f` joins two classes.
-/

namespace Chazelle.Core.Cluster

open Chazelle.Separator Chazelle.Separator.CombMap Equiv Relation

@[expose] public section

variable {V F D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D] [Fintype F]
  [DecidableEq F] {M : CombMap V F D} {T : SpanTree M} (C : CoTree T) (δ : V → D)

/-- The vertices of `P` whose chosen face lies in the subtree of `x`. -/
noncomputable def cnt (P : Finset V) (x : F) : ℕ :=
  haveI := Classical.decPred (fun v => C.IsDesc (M.face (δ v)) x)
  (P.filter (fun v => C.IsDesc (M.face (δ v)) x)).card

/-- More than half of the piece lies in the subtree of `x`. -/
def Good (P : Finset V) (x : F) : Prop := P.card < 2 * cnt C δ P x

variable {C δ}

/-- **The centroid**: if `f` is good and none of its children is, every side entered through a
non-tree dart of `f` holds at most half of the piece. -/
theorem centroid_half (hM : M.Planar) {P : Finset V} {f : F} (hf : Good C δ P f)
    (hch : ∀ g, g ≠ C.r0 → C.parent g = f → ¬ Good C δ P g) {d : D} (hd : d ∈ T.coDarts)
    (hdf : M.face d = f) :
    2 * (P.filter (fun v => M.face (δ v) ∈ T.cross d)).card ≤ P.card := by
  classical
  obtain ⟨g, hg, rfl | rfl⟩ := (C.mem_coDarts_iff hM).mp hd
  · -- `g` is a child of `f`
    have hpar : C.parent g = f := by rw [C.parent_of_ne hg]; exact hdf
    have hng := hch g hg hpar
    unfold Good cnt at hng
    push Not at hng
    have : P.filter (fun v => M.face (δ v) ∈ T.cross (C.fpar g)) =
        P.filter (fun v => C.IsDesc (M.face (δ v)) g) := by
      ext v; simp only [Finset.mem_filter, C.cross_fpar hM hg]
    rw [this]
    convert hng using 3
  · -- the parent side of `f`
    have hgf : g = f := (C.head g hg).symm.trans hdf
    subst hgf
    unfold Good cnt at hf
    have hsplit := Finset.card_filter_add_card_filter_not (s := P)
      (fun v => C.IsDesc (M.face (δ v)) g)
    have : P.filter (fun v => M.face (δ v) ∈ T.cross (M.opp (C.fpar g))) =
        P.filter (fun v => ¬ C.IsDesc (M.face (δ v)) g) := by
      ext v; simp only [Finset.mem_filter, C.cross_opp_fpar hM hg]
    rw [this]
    have e : (P.filter (fun v => C.IsDesc (M.face (δ v)) g)).card =
        (haveI := Classical.decPred (fun v => C.IsDesc (M.face (δ v)) g);
          (P.filter (fun v => C.IsDesc (M.face (δ v)) g)).card) := by
      congr 1
    omega

/-- The class of the dart `x t` of the face `f`: the vertices of `P` off `sepSet f` whose face lies
beyond the non-tree dart `x t`. -/
noncomputable def cls (T : SpanTree M) (δ : V → D) (P : Finset V) (f : F) (x : ℕ → D) (t : ℕ) :
    Finset V :=
  haveI := Classical.decPred
    (fun v => v ∉ T.sepSet f ∧ x t ∈ T.coDarts ∧ M.face (δ v) ∈ T.cross (x t))
  P.filter (fun v => v ∉ T.sepSet f ∧ x t ∈ T.coDarts ∧ M.face (δ v) ∈ T.cross (x t))

omit [DecidableEq F] in
theorem mem_cls {P : Finset V} {f : F} {x : ℕ → D} {t : ℕ} {v : V} :
    v ∈ cls T δ P f x t ↔
      v ∈ P ∧ v ∉ T.sepSet f ∧ x t ∈ T.coDarts ∧ M.face (δ v) ∈ T.cross (x t) := by
  unfold cls
  exact @Finset.mem_filter _ _ (Classical.decPred _) _ _

omit [DecidableEq F] in
/-- **The classes of a split.**  With the darts of `f` enumerated as `x 0, x 1, x 2`: every vertex
of `P` off `sepSet f` is in a class, classes are disjoint, and no edge off `sepSet f` joins two
classes. -/
theorem split_classes (hM : M.Planar) (hδ : ∀ v, M.vert (δ v) = v) {P : Finset V} {f : F}
    {x : ℕ → D} (hx : ∀ e, M.face e = f ↔ ∃ t, t < 3 ∧ x t = e)
    (hxinj : ∀ t t', t < 3 → t' < 3 → x t = x t' → t = t') :
    (∀ v ∈ P, v ∉ T.sepSet f → ∃ t, t < 3 ∧ v ∈ cls T δ P f x t) ∧
    (∀ t t', t < 3 → t' < 3 → ∀ v, v ∈ cls T δ P f x t → v ∈ cls T δ P f x t' → t = t') ∧
    (∀ e t t', t < 3 → t' < 3 → M.vert e ∈ cls T δ P f x t → M.head e ∈ cls T δ P f x t' →
      t = t') := by
  refine ⟨fun v hv hs => ?_, fun t t' ht ht' v h1 h2 => ?_, fun e t t' ht ht' h1 h2 => ?_⟩
  · obtain ⟨d, hd, hdf, hdc⟩ := exists_label' T hM δ hδ hs
    obtain ⟨t, ht, rfl⟩ := (hx d).mp hdf
    exact ⟨t, ht, mem_cls.mpr ⟨hv, hs, hd, hdc⟩⟩
  · obtain ⟨-, -, a1, a2⟩ := mem_cls.mp h1
    obtain ⟨-, -, b1, b2⟩ := mem_cls.mp h2
    have hf1 := (hx (x t)).mpr ⟨t, ht, rfl⟩
    have hf2 := (hx (x t')).mpr ⟨t', ht', rfl⟩
    exact hxinj t t' ht ht' (label_unique' T hM a1 b1 (hf2.trans hf1.symm) a2 b2)
  · obtain ⟨-, s1, a1, a2⟩ := mem_cls.mp h1
    obtain ⟨-, s2, b1, b2⟩ := mem_cls.mp h2
    have hf1 := (hx (x t)).mpr ⟨t, ht, rfl⟩
    have hf2 := (hx (x t')).mpr ⟨t', ht', rfl⟩
    have a3 := (label_adj' T δ hδ e s1 s2 a1 hf1).mp a2
    exact hxinj t t' ht ht' (label_unique' T hM a1 b1 (hf2.trans hf1.symm) a3 b2)

/-- **Each class of a centroid split holds at most half of the piece.** -/
theorem cls_half (hM : M.Planar) {P : Finset V} {f : F} (hf : Good C δ P f)
    (hch : ∀ g, g ≠ C.r0 → C.parent g = f → ¬ Good C δ P g) {x : ℕ → D}
    (hx : ∀ e, M.face e = f ↔ ∃ t, t < 3 ∧ x t = e) {t : ℕ} (ht : t < 3) :
    2 * (cls T δ P f x t).card ≤ P.card := by
  classical
  by_cases hco : x t ∈ T.coDarts
  · refine le_trans (Nat.mul_le_mul_left 2 (Finset.card_le_card (fun v hv => ?_)))
      (centroid_half hM hf hch hco ((hx (x t)).mpr ⟨t, ht, rfl⟩))
    obtain ⟨a, -, -, b⟩ := mem_cls.mp hv
    exact Finset.mem_filter.mpr ⟨a, b⟩
  · have : cls T δ P f x t = ∅ := by
      ext v; simp only [mem_cls, Finset.notMem_empty, iff_false]; tauto
    rw [this]; simp

end

end Chazelle.Core.Cluster
