module

public import Chazelle.Separator.Clusters

/-!
# WP-I, part 7: the face separator with a rooted cotree

The algorithmic form of `CombMap.SpanTree.exists_face_separator` (`CycleSeparator.lean`).

* **Labels for an arbitrary choice of vertex faces** (`label_adj'`, `exists_label'`): every
  vertex `v` sends its weight to the face of a dart `δ v` at `v` (the library uses the fixed
  choice `vdart`; the RAM uses its own).
* **Rooted cotree** (`CoTree`): a root face and, for every other face `g`, a non-tree dart
  `fpar g` entering `g` from a face one level higher up (what a breadth-first search of the
  dual map through the non-tree darts produces).  In a planar map, every non-tree dart is such a
  parent dart or the opposite of one (`CoTree.mem_coDarts_iff`, by counting: both sets have
  `2 (F - 1)` elements), and the side of the fundamental cycle entered through a parent dart is
  the subtree below it (`CoTree.cross_fpar`), through the opposite dart its complement
  (`CoTree.cross_opp_fpar`).
-/

namespace Chazelle.Core.Cluster

open Chazelle.Separator Chazelle.Separator.CombMap Equiv Relation

@[expose] public section

variable {V F D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D] [Fintype F]
  [DecidableEq F] {M : CombMap V F D} (T : SpanTree M)

/-! ## Labels for an arbitrary choice of vertex faces -/

omit [DecidableEq F] in
/-- **Jordan property with arbitrary darts**: the endpoints of an edge off `sepSet f` have
their chosen faces on the same side of every non-tree dart of `f`. -/
theorem label_adj' (δ : V → D) (hδ : ∀ v, M.vert (δ v) = v) {f : F} (e : D)
    (h1 : M.vert e ∉ T.sepSet f) (h2 : M.head e ∉ T.sepSet f) {d : D} (hd : d ∈ T.coDarts)
    (hdf : M.face d = f) :
    M.face (δ (M.vert e)) ∈ T.cross d ↔ M.face (δ (M.head e)) ∈ T.cross d := by
  have key := T.eqvGen_face_of_dart hd e
    (T.not_isAnc_of_notMem_sepSet h1 hdf) (T.not_isAnc_head_of_notMem_sepSet h1 hdf)
    (T.not_isAnc_of_notMem_sepSet h2 hdf) (T.not_isAnc_head_of_notMem_sepSet h2 hdf)
    (hδ _) (hδ _)
  rw [T.mem_cross, T.mem_cross]
  exact ⟨fun h => EqvGen.trans _ _ _ h key, fun h => EqvGen.trans _ _ _ h (EqvGen.symm _ _ key)⟩

omit [DecidableEq F] in
/-- **Every vertex off `sepSet f` has a label**: its chosen face lies beyond some non-tree dart
of `f`. -/
theorem exists_label' (hM : M.Planar) (δ : V → D) (hδ : ∀ v, M.vert (δ v) = v) {f : F} {v : V}
    (hv : v ∉ T.sepSet f) :
    ∃ d ∈ T.coDarts, M.face d = f ∧ M.face (δ v) ∈ T.cross d := by
  have hfv : M.face (δ v) ≠ f := by
    intro h
    exact T.not_isAnc_of_notMem_sepSet hv h (by rw [hδ]; exact T.isAnc_refl v)
  set U : Set F := {g | g = f ∨ ∃ d ∈ T.coDarts, M.face d = f ∧ g ∈ T.cross d}
  have hstep : ∀ x y, M.faceRel T.coDarts x y → x ∈ U → y ∈ U := by
    rintro x y ⟨e, he, rfl, rfl⟩ hx
    rcases hx with hx | ⟨d, hd, hdf, hxd⟩
    · exact Or.inr ⟨e, he, hx, T.face_opp_mem_cross e⟩
    · by_cases h1 : e = d
      · subst h1; exact absurd hxd (T.face_notMem_cross hM hd)
      · by_cases h2 : e = M.opp d
        · subst h2; left; rwa [M.opp_opp]
        · exact Or.inr ⟨d, hd, hdf, T.cross_closed (T.mem_Sd.mpr ⟨he, h1, h2⟩) hxd⟩
  have hmem : M.face (δ v) ∈ U :=
    mem_of_eqvGen (M.faceRel T.coDarts) U hstep
      (fun x y hxy hy => hstep y x (faceRel_opp T.coDarts_oppClosed hxy) hy)
      (T.eqvGen_faceRel_coDarts hM.1 f (M.face (δ v))) (Or.inl rfl)
  rcases hmem with h | h
  · exact absurd h hfv
  · exact h

omit [DecidableEq F] in
/-- The label of a vertex is unique. -/
theorem label_unique' (hM : M.Planar) {d d' : D} (hd : d ∈ T.coDarts) (hd' : d' ∈ T.coDarts)
    (hf : M.face d' = M.face d) {g : F} (hg : g ∈ T.cross d) (hg' : g ∈ T.cross d') : d = d' :=
  T.label_unique hM hd hd' hf hg hg'

/-! ## Rooted cotrees -/

/-- **A rooted cotree**: a root face `r0` and, for every other face `g`, a non-tree dart
`fpar g` from its parent face into `g`, the parent being one level higher up. -/
structure CoTree where
  /-- the root face -/
  r0 : F
  /-- the dart entering a face from its parent -/
  fpar : F → D
  /-- the depth of a face -/
  flev : F → ℕ
  lev_root : flev r0 = 0
  mem : ∀ g, g ≠ r0 → fpar g ∈ T.coDarts
  head : ∀ g, g ≠ r0 → M.face (M.opp (fpar g)) = g
  lev : ∀ g, g ≠ r0 → flev (M.face (fpar g)) + 1 = flev g

namespace CoTree

variable {T} (C : CoTree T)

/-- The parent face (the root is its own parent). -/
def parent (g : F) : F := if g = C.r0 then C.r0 else M.face (C.fpar g)

/-- `IsDesc h g`: `g` lies on the path from `h` to the root. -/
def IsDesc (h g : F) : Prop := ∃ n : ℕ, C.parent^[n] h = g

omit [Fintype F] in
theorem parent_of_ne {g : F} (hg : g ≠ C.r0) : C.parent g = M.face (C.fpar g) := by
  simp [parent, hg]

omit [Fintype F] in
theorem isDesc_refl (g : F) : C.IsDesc g g := ⟨0, rfl⟩

omit [Fintype F] in
/-- Descendance steps up through the parent. -/
theorem isDesc_parent_iff {h g : F} (hh : h ≠ g) : C.IsDesc h g ↔ C.IsDesc (C.parent h) g := by
  constructor
  · rintro ⟨n, hn⟩
    rcases n with _ | n
    · exact absurd hn hh
    · exact ⟨n, by rwa [Function.iterate_succ_apply] at hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, by rwa [Function.iterate_succ_apply]⟩

/-- The parent darts and their opposites. -/
noncomputable def treeDarts : Finset D :=
  ((Finset.univ.erase C.r0).image C.fpar) ∪ ((Finset.univ.erase C.r0).image (fun g => M.opp (C.fpar g)))

/-- **Every non-tree dart is a parent dart or the opposite of one** (planar maps). -/
theorem coDarts_eq (hM : M.Planar) : T.coDarts = C.treeDarts := by
  classical
  have hsub : C.treeDarts ⊆ T.coDarts := by
    intro e he
    rcases Finset.mem_union.mp he with h | h
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp h
      exact C.mem g (Finset.ne_of_mem_erase hg)
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp h
      exact T.opp_mem_coDarts (C.mem g (Finset.ne_of_mem_erase hg))
  have hinj1 : Set.InjOn C.fpar (Finset.univ.erase C.r0 : Finset F) := by
    intro g hg g' hg' h
    have e1 := C.head g (Finset.ne_of_mem_erase hg)
    have e2 := C.head g' (Finset.ne_of_mem_erase hg')
    rw [← e1, ← e2, h]
  have hinj2 : Set.InjOn (fun g => M.opp (C.fpar g)) (Finset.univ.erase C.r0 : Finset F) := by
    intro g hg g' hg' h
    exact hinj1 hg hg' (M.opp_injective h)
  have hdisj : Disjoint ((Finset.univ.erase C.r0).image C.fpar)
      ((Finset.univ.erase C.r0).image (fun g => M.opp (C.fpar g))) := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨g', hg', heq⟩ := Finset.mem_image.mp h2
    have hg0 := Finset.ne_of_mem_erase hg
    have hg0' := Finset.ne_of_mem_erase hg'
    -- `g'` is the parent of `g` and `g` the parent of `g'`
    have a1 : M.face (C.fpar g') = g := by
      have := C.head g hg0; rwa [← heq, M.opp_opp] at this
    have a2 : M.face (C.fpar g) = g' := by
      have := C.head g' hg0'; rwa [heq] at this
    have l1 := C.lev g hg0
    have l2 := C.lev g' hg0'
    rw [a2] at l1; rw [a1] at l2
    omega
  have hcard : C.treeDarts.card = 2 * (Fintype.card F - 1) := by
    unfold treeDarts
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj1,
      Finset.card_image_of_injOn hinj2, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ]
    omega
  have hco := T.card_coDarts hM
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

theorem mem_coDarts_iff (hM : M.Planar) {e : D} :
    e ∈ T.coDarts ↔ ∃ g, g ≠ C.r0 ∧ (e = C.fpar g ∨ e = M.opp (C.fpar g)) := by
  rw [C.coDarts_eq hM]
  unfold treeDarts
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · rintro (⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩)
    · exact ⟨g, hg, Or.inl rfl⟩
    · exact ⟨g, hg, Or.inr rfl⟩
  · rintro ⟨g, hg, rfl | rfl⟩
    · exact Or.inl ⟨g, hg, rfl⟩
    · exact Or.inr ⟨g, hg, rfl⟩

/-- **The side entered through a parent dart is the subtree below it.** -/
theorem cross_fpar (hM : M.Planar) {g : F} (hg : g ≠ C.r0) (h : F) :
    h ∈ T.cross (C.fpar g) ↔ C.IsDesc h g := by
  classical
  rw [T.mem_cross, C.head g hg]
  constructor
  · -- the subtree is closed under the remaining non-tree edges
    intro hr
    refine mem_of_eqvGen _ {x | C.IsDesc x g} ?_ ?_ hr (C.isDesc_refl g)
    · rintro x y ⟨e, he, rfl, rfl⟩ hx
      obtain ⟨he1, hne1, hne2⟩ := T.mem_Sd.mp he
      obtain ⟨x', hx'0, rfl | rfl⟩ := (C.mem_coDarts_iff hM).mp he1
      · -- crossing down the parent dart of `x'`
        have hx'g : x' ≠ g := fun h => hne1 (by rw [h])
        show C.IsDesc _ g
        rwa [C.head x' hx'0, C.isDesc_parent_iff hx'g, C.parent_of_ne hx'0]
      · -- crossing up to the parent
        have hx'g : x' ≠ g := fun h => hne2 (by rw [h])
        show C.IsDesc _ g
        simp only [Set.mem_ofPred_eq] at hx
        rw [C.head x' hx'0, C.isDesc_parent_iff hx'g, C.parent_of_ne hx'0] at hx
        rwa [M.opp_opp]
    · rintro x y ⟨e, he, rfl, rfl⟩ hy
      obtain ⟨he1, hne1, hne2⟩ := T.mem_Sd.mp he
      obtain ⟨x', hx'0, rfl | rfl⟩ := (C.mem_coDarts_iff hM).mp he1
      · have hx'g : x' ≠ g := fun h => hne1 (by rw [h])
        show C.IsDesc _ g
        simp only [Set.mem_ofPred_eq] at hy
        rwa [C.head x' hx'0, C.isDesc_parent_iff hx'g, C.parent_of_ne hx'0] at hy
      · have hx'g : x' ≠ g := fun h => hne2 (by rw [h])
        show C.IsDesc _ g
        simp only [Set.mem_ofPred_eq] at hy
        rw [M.opp_opp] at hy
        rwa [C.head x' hx'0, C.isDesc_parent_iff hx'g, C.parent_of_ne hx'0]
  · -- every descendant reaches `g` along parent darts other than `fpar g`
    rintro ⟨n, hn⟩
    induction n generalizing h with
    | zero => rw [← hn]; exact EqvGen.refl _
    | succ n ih =>
      rw [Function.iterate_succ_apply] at hn
      have hpar := ih (C.parent h) hn
      by_cases hhg : h = g
      · rw [hhg]; exact EqvGen.refl _
      have hh0 : h ≠ C.r0 := by
        intro h0
        rw [h0, show C.parent C.r0 = C.r0 by simp [parent],
          Function.iterate_fixed (show C.parent C.r0 = C.r0 by simp [parent])] at hn
        exact hg hn.symm
      refine EqvGen.trans _ _ _ hpar (EqvGen.rel _ _ ⟨C.fpar h, ?_, ?_, C.head h hh0⟩)
      · refine T.mem_Sd.mpr ⟨C.mem h hh0, fun heq => hhg ?_, fun heq => ?_⟩
        · rw [← C.head h hh0, ← C.head g hg, heq]
        · -- `h` would be the parent of `g` and `g` the parent of `h`
          have a1 : h = M.face (C.fpar g) := by
            rw [← C.head h hh0, heq, M.opp_opp]
          have a2 : M.face (C.fpar h) = g := by
            rw [heq]; exact C.head g hg
          have l1 := C.lev g hg
          have l2 := C.lev h hh0
          rw [← a1] at l1; rw [a2] at l2
          omega
      · exact (C.parent_of_ne hh0).symm

/-- **The side entered through the opposite of a parent dart is the complement of the subtree.** -/
theorem cross_opp_fpar (hM : M.Planar) {g : F} (hg : g ≠ C.r0) (h : F) :
    h ∈ T.cross (M.opp (C.fpar g)) ↔ ¬ C.IsDesc h g := by
  have hd := C.mem g hg
  constructor
  · intro h1 h2
    exact T.notMem_cross_opp hM hd ((C.cross_fpar hM hg h).mpr h2) h1
  · intro h1
    exact (T.mem_cross_or hM hd h).resolve_left (fun h2 => h1 ((C.cross_fpar hM hg h).mp h2))

end CoTree

end

end Chazelle.Core.Cluster
