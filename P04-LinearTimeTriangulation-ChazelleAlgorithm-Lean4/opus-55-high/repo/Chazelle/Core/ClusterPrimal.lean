module

public import Chazelle.MacT
public import Chazelle.Programs.Tactics
public import Chazelle.Core.NFDecompBfs
public import Mathlib.Data.Nat.Size
public import Chazelle.Core.ClusterEulerRam

namespace Chazelle.Core.Cluster
open Chazelle.Separator
@[expose] public section
def MapArrays (m : ℕ → ℕ) (bO bR bV μ N : ℕ) {F : Type} (M : CombMap ztemr F ztjiv) : Prop :=
  ∀ d : Fin N, m ztbtt = M.opp d ∧ m zttgi = M.rot d ∧ m zthdv = M.vert d
section arrays
variable {m : ℕ → ℕ} {bO bR bV μ N : ℕ} {F : Type} {M : CombMap (Fin μ) F (Fin N)}
theorem MapArrays.opp (h : MapArrays m bO bR bV μ N M) {d : ℕ} (hd : d < N) :
    m ztbtt = M.opp ztpw := (h ztpw).1
theorem MapArrays.rot (h : MapArrays m bO bR bV μ N M) {d : ℕ} (hd : d < N) :
    m zttgi = M.rot ztpw := (h ztpw).2.1
theorem MapArrays.vert (h : MapArrays m bO bR bV μ N M) {d : ℕ} (hd : d < N) :
    m zthdv = M.vert ztpw := (h ztpw).2.2

/-- Iterating the stored rotation is iterating the rotation. -/
theorem MapArrays.iterate_rot (h : MapArrays m bO bR bV μ N M) (n : ℕ) (d : Fin N) :
    (fun x => view m bR N x)^[n] d = ((M.rot ^ n) d : ℕ) := by
  induction n generalizing d with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, pow_succ, Equiv.Perm.mul_apply]
    have : view m bR N (d : ℕ) = ((M.rot d : Fin N) : ℕ) := by
      zuinc
    rw [this, ih]
end arrays

/-- The input of `ClusterSpec` holds a planar map in its arrays. -/
theorem PlanarMapAt.exists_arrays {m : ℕ → ℕ} {B μ E : ℕ} (h : PlanarMapAt m B μ E) :
    ∃ (F : Type) (_ : Fintype F) (_ : DecidableEq F) (M : CombMap ztemr F ztzbw),
      M.Planar ∧ MapArrays m ztqtg ztbaif ztbaic μ ztdsj M := by
  tauto

/-- **The rotation system of the input map** with a `first` array and flag arrays. -/
def primalEnv (m : ℕ → ℕ) (bO bR bV bF bDB bVB μ N : ℕ) : Env :=
  ⟨view m bO N, view m bR N, view m bV N, view m bF μ, view m bDB N, view m bVB μ, μ, N⟩
section env
variable {m : ℕ → ℕ} {bO bR bV bF bDB bVB μ N : ℕ} {F : Type} {M : CombMap (Fin μ) F (Fin N)}

/-- **The input map is a well-formed rotation system** once `first` names a dart at every
vertex. -/
theorem primalEnv_ok [Fintype F] (h : MapArrays m bO bR bV μ N M)
    (hF : ∀ u, u < μ → m ztdts < N ∧ m ztzko = u) :
    (primalEnv m bO bR bV bF bDB bVB μ N).OK := by
  refine ⟨fun d hd => ?_, fun d hd => ?_, fun d hd => ?_, fun d hd e he hde => ?_,
    fun d hd => ?_, fun d hd e he hde => ?_, fun u hu => ?_, fun u hu => ?_⟩
  all_goals simp only [primalEnv] at *
  · rw [view_lt hd, h.opp hd]; omega
  · rw [view_lt hd, h.rot hd]; omega
  · rw [view_lt hd, h.vert hd]; omega
  · rw [view_lt hd, view_lt he, h.rot hd, h.rot he] at hde
    have := M.rot.injective ztuyk
    simp_all
  · rw [view_lt hd, h.rot hd, view_lt (M.rot ztpw).2, h.vert (M.rot ztpw).2,
      view_lt hd, h.vert hd]
    zumpl
  · rw [view_lt hd, view_lt he, h.vert hd, h.vert he] at hde
    have hsc := M.sameCycle_of_vert ztpw ztugi ztuyk
    zuicz
    refine ⟨n, ?_⟩
    have := h.iterate_rot n ztpw
    simp_all
  · rw [view_lt hu]; simp_all
  · rw [view_lt hu, view_lt (hF u hu).1]; simp_all

/-- The input map is symmetric for symmetric dart flags. -/
theorem primalEnv_sym (h : MapArrays m bO bR bV μ N M)
    (hdb : ∀ d, d < N → m (bDB + m ztbtt) = m zttfy) :
    (primalEnv m bO bR bV bF bDB bVB μ N).Sym := by
  zuip
  change d < N at hd
  have ho : ztyyx := by rw [h.opp hd]; omega
  show view m bO N ztqyh = d ∧ view m bDB N ztqyh = view m bDB N d
  rw [view_lt hd, view_lt ho, view_lt ho, view_lt hd]
  refine ⟨?_, hdb d hd⟩
  rw [h.opp hd, h.opp (M.opp ztpw).2]
  zunrk

/-- **Walks of the stored graph avoiding the flagged vertices are reachabilities** (for dart
flags never equal to `1`). -/
theorem reach_of_walk (h : MapArrays m bO bR bV μ N M) (hdb : ∀ d, d < N → m zttfy ≠ 1)
    {B E : ℕ} (hB : m B = bO) (hB2 : m zthb = bV) (hN : N = 2 * E) {u v : Fin μ}
    (w : (memGraph m B μ E).Walk u v) (hw : ∀ x ∈ w.support, m (bVB + x) ≠ 1) :
    (primalEnv m bO bR bV bF bDB bVB μ N).Reach u v := by
  induction w with
  | nil => exact Relation.ReflTransGen.refl
  | @cons a b c hadj w ih =>
    have ha : m (bVB + a) ≠ 1 := hw a by_simp
    have hb : m (bVB + b) ≠ 1 := hw b by_simp
    have hrest := ih (fun x hx => hw x by_simp_all)
    have hstep : (primalEnv m bO bR bV bF bDB bVB μ N).Step a b := by
      obtain ⟨-, hd⟩ := hadj
      rcases hd with ⟨d, hd, h1, h2⟩ | ⟨d, hd, h1, h2⟩
      · zubeo

        refine ⟨d, hd, ?_, ?_, ?_, ?_, ?_⟩
        · zunxr; simp_all
        · zunxr; exact h1
        · simp only [Env.head, primalEnv, view_lt hd, view_lt ho]; exact h2
        · zughx
        · zughy
      · -- the opposite dart goes from `a` to `b`
        zubeo

        have hoo : m (bO + m ztbtt) = d := by
          rw [h.opp ho]; simp only [h.opp hd, Fin.eta, M.opp_opp]
        refine ⟨m ztbtt, ho, ?_, ?_, ?_, ?_, ?_⟩
        · zunxs; simp_all
        · zunxs; exact h2
        · show view m bV N (view m bO N (m ztbtt)) = _
          rw [view_lt ho, hoo, view_lt hd]
          zubvv
        · zughx
        · zughy
    exact Relation.ReflTransGen.head hstep hrest
end env
open Chazelle.Separator.CombMap Equiv Relation
variable {V F D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D] [Fintype F]
  [DecidableEq F] {M : CombMap V F D} (T : SpanTree M)

/-! ## Labels for an arbitrary choice of vertex faces -/
omit [DecidableEq F] in
/-- **Jordan property with arbitrary darts**: the endpoints of an edge off `sepSet f` have
their chosen faces on the same side of every non-tree dart of `f`. -/
theorem label_adj' (δ : V → D) (hδ : ∀ v, M.vert ztbuz = v) {f : F} (e : D)
    (h1 : M.vert e ∉ T.sepSet f) (h2 : M.head e ∉ T.sepSet f) {d : D} (hd : d ∈ T.coDarts)
    (hdf : M.face d = f) :
    M.face (δ ztenh) ∈ T.cross d ↔ M.face (δ ztjjv) ∈ T.cross d := by
  have key := T.eqvGen_face_of_dart hd e
    (T.not_isAnc_of_notMem_sepSet h1 hdf) (T.not_isAnc_head_of_notMem_sepSet h1 hdf)
    (T.not_isAnc_of_notMem_sepSet h2 hdf) (T.not_isAnc_head_of_notMem_sepSet h2 hdf)
    ztvwu ztvwu
  rw [T.mem_cross, T.mem_cross]
  exact ⟨fun h => EqvGen.trans _ _ _ h key, fun h => EqvGen.trans _ _ _ h (EqvGen.symm _ _ key)⟩
omit [DecidableEq F] in
/-- **Every vertex off `sepSet f` has a label**: its chosen face lies beyond some non-tree dart
of `f`. -/
theorem exists_label' (hM : M.Planar) (δ : V → D) (hδ : ∀ v, M.vert ztbuz = v) {f : F} {v : V}
    (hv : v ∉ T.sepSet f) :
    ∃ d ∈ T.coDarts, M.face d = f ∧ M.face ztbuz ∈ T.cross d := by
  have hfv : M.face ztbuz ≠ f := by
    zuq
    exact T.not_isAnc_of_notMem_sepSet hv h by_tauto
  set U : Set F := {g | g = f ∨ ∃ d ∈ T.coDarts, M.face d = f ∧ g ∈ T.cross d}
  have hstep : ∀ x y, M.faceRel T.coDarts x y → x ∈ U → y ∈ U := by
    zuewi
    rcases hx with hx | ⟨d, hd, hdf, hxd⟩
    · exact Or.inr ⟨e, he, hx, T.face_opp_mem_cross e⟩
    · by_cases h1 : e = d
      · subst h1; exact absurd hxd (T.face_notMem_cross hM hd)
      · by_cases h2 : e = M.opp d
        · subst h2; left; rw [M.opp_opp]; omega
        · exact Or.inr ⟨d, hd, hdf, T.cross_closed (T.mem_Sd.mpr ⟨he, h1, h2⟩) hxd⟩
  have hmem : M.face ztbuz ∈ U :=
    mem_of_eqvGen ztpzy U hstep
      (fun x y hxy hy => hstep y x (faceRel_opp T.coDarts_oppClosed hxy) hy)
      (T.eqvGen_faceRel_coDarts hM.1 f ztxmw) ztp
  grind
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
  head : ∀ g, g ≠ r0 → M.face (M.opp ztvqo) = g
  lev : ∀ g, g ≠ r0 → flev (M.face ztvqo) + 1 = flev g
namespace CoTree
variable {T} (C : CoTree T)

/-- The parent face (the root is its own parent). -/
def parent (g : F) : F := if g = C.r0 then C.r0 else M.face ztcch

/-- `IsDesc h g`: `g` lies on the path from `h` to the root. -/
def IsDesc (h g : F) : Prop := ∃ n : ℕ, C.parent^[n] h = g
omit [Fintype F] in
theorem parent_of_ne {g : F} (hg : g ≠ C.r0) : C.parent g = M.face ztcch := by
  simp [parent, hg]
omit [Fintype F] in
theorem isDesc_refl (g : F) : C.IsDesc g g := ztkil
omit [Fintype F] in
/-- Descendance steps up through the parent. -/
theorem isDesc_parent_iff {h g : F} (hh : h ≠ g) : C.IsDesc h g ↔ C.IsDesc ztuxf g := by
  constructor
  · zurf
    zugai
    · simp_all
    tauto
  · zurf
    exact ⟨n + 1, by_simp_all⟩

/-- The parent darts and their opposites. -/
noncomputable def treeDarts : Finset D :=
  ztosb ∪ ztxru

/-- **Every non-tree dart is a parent dart or the opposite of one** (planar maps). -/
theorem coDarts_eq (hM : M.Planar) : T.coDarts = C.treeDarts := by
  classical
  have hsub : C.treeDarts ⊆ T.coDarts := by
    zubre
    rcases Finset.mem_union.mp he with h | h
    · zufxw
      exact C.mem g ztpyx
    · zufxw
      exact T.opp_mem_coDarts (C.mem g ztpyx)
  have hinj1 : Set.InjOn C.fpar (Finset.univ.erase C.r0 : Finset F) := by
    zukjg
    have e1 := C.head g ztpyx
    have e2 := C.head g' (Finset.ne_of_mem_erase hg')
    simp_all
  have hinj2 : Set.InjOn (fun g => M.opp ztcch) (Finset.univ.erase C.r0 : Finset F) := by
    zukjg
    exact hinj1 hg hg' ztqaa
  have hdisj : Disjoint ztosb
      ztxru := by
    zuzt
    intro e h1 h2
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨g', hg', heq⟩ := Finset.mem_image.mp h2
    have hg0 := Finset.ne_of_mem_erase hg
    have hg0' := Finset.ne_of_mem_erase hg'
    -- `g'` is the parent of `g` and `g` the parent of `g'`
    have a1 : M.face (C.fpar g') = g := by
      have := C.head g hg0; rw [← heq, M.opp_opp] at this; omega
    have a2 : M.face ztcch = g' := by
      have := C.head g' hg0'; simp_all
    have l1 := C.lev g hg0
    have l2 := C.lev g' hg0'
    grind
  have hcard : C.treeDarts.card = 2 * (Fintype.card F - 1) := by
    unfold treeDarts
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj1,
      Finset.card_image_of_injOn hinj2, Finset.card_erase_of_mem ztuyq,
      Finset.card_univ]
    omega
  have hco := T.card_coDarts hM
  have hF : 0 < Fintype.card F := Fintype.card_pos_iff.mpr ⟨C.r0⟩
  exact (Finset.eq_of_subset_of_card_le hsub by_omega).symm
theorem mem_coDarts_iff (hM : M.Planar) {e : D} :
    e ∈ T.coDarts ↔ ∃ g, g ≠ C.r0 ∧ (e = C.fpar g ∨ e = M.opp ztcch) := by
  rw [C.coDarts_eq hM]
  unfold treeDarts
  grind

/-- **The side entered through a parent dart is the subtree below it.** -/
theorem cross_fpar (hM : M.Planar) {g : F} (hg : g ≠ C.r0) (h : F) :
    h ∈ T.cross ztcch ↔ C.IsDesc h g := by
  classical
  rw [T.mem_cross, C.head g hg]
  constructor
  · -- the subtree is closed under the remaining non-tree edges
    zuibu
    refine mem_of_eqvGen _ {x | C.IsDesc x g} ?_ ?_ hr (C.isDesc_refl g)
    · zuewi
      zubpc

      · -- crossing down the parent dart of `x'`
        zugni
        show C.IsDesc _ g
        zufmj
        zufsg
      · -- crossing up to the parent
        zugnj
        show C.IsDesc _ g
        simp only [Set.mem_ofPred_eq] at hx
        rw [C.head x' hx'0, C.isDesc_parent_iff hx'g, C.parent_of_ne hx'0] at hx
        zumlq
        zufsg
    · rintro x y ⟨e, he, rfl, rfl⟩ hy
      zubpc

      · zugni
        show C.IsDesc _ g
        zujnz
        rw [C.head x' hx'0, C.isDesc_parent_iff hx'g, C.parent_of_ne hx'0] at hy
        zulfn
      · zugnj
        show C.IsDesc _ g
        zujnz
        rw [M.opp_opp] at hy
        zufmj
        zulfn
  · -- every descendant reaches `g` along parent darts other than `fpar g`
    zurf
    induction n generalizing h with
    | zero => zvocr; exact EqvGen.refl _
    | succ n ih =>
      rw [Function.iterate_succ_apply] at hn
      have hpar := ih ztuxf hn
      by_cases hhg : h = g
      · rw [hhg]; exact EqvGen.refl _
      have hh0 : h ≠ C.r0 := by
        zubww
        rw [h0, show C.parent C.r0 = C.r0 by zuocs,
          Function.iterate_fixed (show C.parent C.r0 = C.r0 by zuocs)] at hn
        simp_all
      refine EqvGen.trans _ _ _ hpar (EqvGen.rel _ _ ⟨C.fpar h, ?_, ?_, C.head h hh0⟩)
      · refine T.mem_Sd.mpr ⟨C.mem h hh0, fun heq => hhg ?_, fun heq => ?_⟩
        · rw [← C.head h hh0, ← C.head g hg, heq]
        · -- `h` would be the parent of `g` and `g` the parent of `h`
          have a1 : h = M.face ztcch := by
            rw [← C.head h hh0, heq, M.opp_opp]
          have a2 : M.face (C.fpar h) = g := by
            zvnbk; exact C.head g hg
          have l1 := C.lev g hg
          have l2 := C.lev h hh0
          grind
      · exact (C.parent_of_ne hh0).symm

/-- **The side entered through the opposite of a parent dart is the complement of the subtree.** -/
theorem cross_opp_fpar (hM : M.Planar) {g : F} (hg : g ≠ C.r0) (h : F) :
    h ∈ T.cross ztbaei ↔ ¬ C.IsDesc h g := by
  have hd := C.mem g hg
  constructor
  · zujay
    exact T.notMem_cross_opp hM hd ((C.cross_fpar hM hg h).mpr h2) h1
  · zudqd
    exact (T.mem_cross_or hM hd h).resolve_left (fun h2 => h1 ((C.cross_fpar hM hg h).mp h2))
end CoTree
end
open Chazelle.Separator.CombMap Equiv Relation
@[expose] public section
variable {V F D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D] [Fintype F]
  [DecidableEq F] {M : CombMap V F D} {T : SpanTree M} (C : CoTree T) (δ : V → D)

/-- The vertices of `P` whose chosen face lies in the subtree of `x`. -/
noncomputable def cnt (P : Finset V) (x : F) : ℕ :=
  haveI := Classical.decPred ztbaou
  (P.filter ztbaou).card

/-- More than half of the piece lies in the subtree of `x`. -/
def Good (P : Finset V) (x : F) : Prop := P.card < 2 * cnt C δ P x
variable {C δ}

/-- **The centroid**: if `f` is good and none of its children is, every side entered through a
non-tree dart of `f` holds at most half of the piece. -/
theorem centroid_half (hM : M.Planar) {P : Finset V} {f : F} (hf : Good C δ P f)
    (hch : ∀ g, g ≠ C.r0 → C.parent g = f → ¬ Good C δ P g) {d : D} (hd : d ∈ T.coDarts)
    (hdf : M.face d = f) :
    2 * (P.filter (fun v => M.face ztbuz ∈ T.cross d)).card ≤ P.card := by
  classical
  obtain ⟨g, hg, rfl | rfl⟩ := (C.mem_coDarts_iff hM).mp hd
  · -- `g` is a child of `f`
    have hpar : C.parent g = f := by rw [C.parent_of_ne hg]; omega
    have hng := hch g hg hpar
    unfold Good cnt at hng
    push Not at hng
    have : P.filter (fun v => M.face ztbuz ∈ T.cross ztcch) =
        P.filter ztbaot := by
      ext v; simp only [Finset.mem_filter, C.cross_fpar hM hg]
    simp_all
  · -- the parent side of `f`
    have hgf : g = f := (C.head g hg).symm.trans hdf
    subst hgf
    unfold Good cnt at hf
    have hsplit := Finset.card_filter_add_card_filter_not (s := P)
      ztbaot
    have : P.filter (fun v => M.face ztbuz ∈ T.cross ztbaei) =
        P.filter (fun v => ¬ C.IsDesc ztxmw g) := by
      ext v; simp only [Finset.mem_filter, C.cross_opp_fpar hM hg]
    grind

/-- The class of the dart `x t` of the face `f`: the vertices of `P` off `sepSet f` whose face lies
beyond the non-tree dart `x t`. -/
noncomputable def cls (T : SpanTree M) (δ : V → D) (P : Finset V) (f : F) (x : ℕ → D) (t : ℕ) :
    Finset V :=
  haveI := Classical.decPred
    ztxew
  P.filter ztxew
omit [DecidableEq F] in
theorem mem_cls {P : Finset V} {f : F} {x : ℕ → D} {t : ℕ} {v : V} :
    v ∈ cls T δ P f x t ↔
      v ∈ P ∧ v ∉ T.sepSet f ∧ x t ∈ T.coDarts ∧ M.face ztbuz ∈ T.cross ztibr := by
  unfold cls
  simp
omit [DecidableEq F] in
/-- **The classes of a split.**  With the darts of `f` enumerated as `x 0, x 1, x 2`: every vertex
of `P` off `sepSet f` is in a class, classes are disjoint, and no edge off `sepSet f` joins two
classes. -/
theorem split_classes (hM : M.Planar) (hδ : ∀ v, M.vert ztbuz = v) {P : Finset V} {f : F}
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
    zuddb

    exact hxinj t t' ht ht' (label_unique' T hM a1 b1 ztvva a2 b2)
  · obtain ⟨-, s1, a1, a2⟩ := mem_cls.mp h1
    obtain ⟨-, s2, b1, b2⟩ := mem_cls.mp h2
    zuddb

    have a3 := (label_adj' T δ hδ e s1 s2 a1 hf1).mp a2
    exact hxinj t t' ht ht' (label_unique' T hM a1 b1 ztvva a3 b2)

/-- **Each class of a centroid split holds at most half of the piece.** -/
theorem cls_half (hM : M.Planar) {P : Finset V} {f : F} (hf : Good C δ P f)
    (hch : ∀ g, g ≠ C.r0 → C.parent g = f → ¬ Good C δ P g) {x : ℕ → D}
    (hx : ∀ e, M.face e = f ↔ ∃ t, t < 3 ∧ x t = e) {t : ℕ} (ht : t < 3) :
    2 * (cls T δ P f x t).card ≤ P.card := by
  classical
  by_cases hco : x t ∈ T.coDarts
  · refine le_trans (Nat.mul_le_mul_left 2 (Finset.card_le_card ztest))
      (centroid_half hM hf hch hco ((hx ztibr).mpr ztbik))
    obtain ⟨a, -, -, b⟩ := mem_cls.mp hv
    simp_all
  · have : cls T δ P f x t = ∅ := by
      ext v; simp only [mem_cls, Finset.notMem_empty, iff_false]; tauto
    simp_all
end
@[expose] public section
open Finset

/-- The items of the segment `p`. -/
def items (act : ℕ → ℕ) (p : ℕ × ℕ) : Finset ℕ := (Finset.Ico p.1 p.2).image act

/-- The length of a segment. -/
def len (p : ℕ × ℕ) : ℕ := p.2 - p.1
variable {act : ℕ → ℕ} {p : ℕ × ℕ}
theorem items_card (h : Set.InjOn act ztsxm) :
    (items act p).card = len p := by
  unfold items len
  rw [Finset.card_image_of_injOn h, Nat.card_Ico]
theorem mem_items {v : ℕ} :
    v ∈ items act p ↔ ∃ i, p.1 ≤ i ∧ i < p.2 ∧ act i = v := by
  unfold items
  grind

/-- Items only depend on the array inside the segment. -/
theorem items_congr {act act' : ℕ → ℕ} {p : ℕ × ℕ}
    (h : ∀ i, p.1 ≤ i → i < p.2 → act' i = act i) : items act' p = items act p := by
  zuepb
  simp only [mem_items]
  grind
section stack
variable (μ k s : ℕ) (H : Finset ℕ) (slab : ℕ → ℕ) (Adj : ℕ → ℕ → Prop)

/-- A live segment: on the stack or finished. -/
def Lv (stk : List ztw) (fin : Finset ztw) (p : ℕ × ℕ) : Prop := p ∈ stk ∨ p ∈ fin

/-- Disjoint position ranges (empty ranges are disjoint from everything). -/
def RDisj (p q : ℕ × ℕ) : Prop := p.2 ≤ q.1 ∨ q.2 ≤ p.1 ∨ p.2 ≤ p.1 ∨ q.2 ≤ q.1

/-- **The invariant of the work stack.** -/
structure SInv (act : ℕ → ℕ) (stk : List ztw) (fin : Finset ztw) (D : Finset ℕ)
    (nsp : ℕ) : Prop where
  wf : ∀ p, Lv stk fin p → p.1 ≤ p.2
  inj : ∀ p, Lv stk fin p → Set.InjOn act ztsxm
  lt : ∀ p, Lv stk fin p → ∀ v ∈ items act p, v < μ
  nodup : stk.Nodup
  sf : ∀ p ∈ stk, p ∉ fin
  rdisj : ∀ p q, Lv stk fin p → Lv stk fin q → p ≠ q → RDisj p q
  disj : ∀ p q, Lv stk fin p → Lv stk fin q → p ≠ q → Disjoint (items act p) (items act q)
  big : ∀ p ∈ stk, s < len p
  small : ∀ p ∈ fin, len p ≤ s
  cover : ∀ v, v < μ → v ∉ H → v ∉ D → ∃ p, Lv stk fin p ∧ v ∈ items act p
  off : ∀ p, Lv stk fin p → ∀ v ∈ items act p, v ∉ D ∧ v ∉ H
  inslab : ∀ p, Lv stk fin p → ∀ v ∈ items act p, ∀ w ∈ items act p, slab v = slab w
  edge : ∀ x y, Adj x y → x ∉ H → x ∉ D → y ∉ H → y ∉ D →
    ∃ p, Lv stk fin p ∧ x ∈ items act p ∧ y ∈ items act p
  hD : Disjoint D H
  pot : s * D.card + ∑ p ∈ stk.toFinset, 3 * k * ztcyr ≤ 6 * k * μ
  pot2 : nsp * s + ∑ p ∈ stk.toFinset, ztcyr ≤ 2 * μ
variable {μ k s H slab Adj}

/-- **A valid split** of the segment `p = (lo, hi)` in place: the array changes only inside
`[lo, hi)`; the classes are the consecutive segments `(e t, e (t + 1))`, `t < 3`, inside
`[lo, hi)`, the new array is injective on their union, they hold exactly the items of `p` off
the separator `sep ⊆ items p`, at most half of them each, and no edge joins two classes;
`|sep| ≤ 3k`. -/
structure SplitOK (act act' : ℕ → ℕ) (p : ℕ × ℕ) (e : ℕ → ℕ) (sep : Finset ℕ) : Prop where
  out : ∀ i, (i < p.1 ∨ p.2 ≤ i) → i < μ → act' i = act i
  e0 : p.1 ≤ e 0
  mono : ∀ t, t < 3 → e t ≤ e ztbx
  e3 : e 3 ≤ p.2
  inj : Set.InjOn act' (Finset.Ico (e 0) (e 3))
  sub : sep ⊆ items act p
  parts : ∀ v, v ∈ items act p → v ∉ sep → ∃ t, t < 3 ∧ v ∈ items act' ztwzt
  inparts : ∀ t, t < 3 → ∀ v ∈ items act' ztwzt, v ∈ items act p ∧ v ∉ sep
  half : ∀ t, t < 3 → 2 * len ztwzt ≤ len p
  noedge : ∀ x y, Adj x y → ∀ t t', t < 3 → t' < 3 → x ∈ items act' ztwzt →
    y ∈ items act' (e t', e (t' + 1)) → t = t'
  card : sep.card ≤ 3 * k

/-- The class `t` of a split. -/
def scls (e : ℕ → ℕ) (t : ℕ) : ℕ × ℕ := ztwzt
variable {act act' : ℕ → ℕ} {p : ℕ × ℕ} {e : ℕ → ℕ} {sep : Finset ℕ}
theorem SplitOK.e_mono
    (hS : SplitOK (μ := μ) (k := k) (Adj := Adj) act act' p e sep) {t t' : ℕ} (htt : t ≤ t')
    (ht' : t' ≤ 3) : e t ≤ e t' := by
  induction t' with
  | zero => rw [show t = 0 by omega]
  | succ n ih =>
    rcases Nat.lt_or_ge t ztkk with h | h
    · exact le_trans by_omega (hS.mono n by_omega)
    · grind
theorem SplitOK.scls_in
    (hS : SplitOK (μ := μ) (k := k) (Adj := Adj) act act' p e sep) {t : ℕ} (ht : t < 3) :
    p.1 ≤ e t ∧ e t ≤ e ztbx ∧ e ztbx ≤ p.2 := by
  refine ⟨le_trans hS.e0 (hS.e_mono ztbg by_omega), hS.mono t ht,
    le_trans (hS.e_mono by_omega le_rfl) hS.e3⟩
theorem SplitOK.scls_inj
    (hS : SplitOK (μ := μ) (k := k) (Adj := Adj) act act' p e sep) {t : ℕ} (ht : t < 3) :
    Set.InjOn act' (Finset.Ico (e t) (e ztbx)) := by
  have a := hS.e_mono ztvaj by_omega
  have b := hS.e_mono ztmog le_rfl
  zuvc
  zugzc
  exact hS.inj by_grind
    by_grind hxy

/-- Distinct classes are disjoint. -/
theorem SplitOK.scls_disj
    (hS : SplitOK (μ := μ) (k := k) (Adj := Adj) act act' p e sep) {t t' : ℕ} (ht : t < 3) (ht' : t' < 3)
    (hne : t ≠ t') : Disjoint (items act' ztbug) (items act' (scls e t')) := by
  zuzt
  zugon
  obtain ⟨i, a, b, c⟩ := mem_items.mp hv
  obtain ⟨i', a', b', c'⟩ := mem_items.mp hv'
  simp only [scls] at a b a' b'
  have h0 := hS.e_mono ztvaj by_omega
  have h0' := hS.e_mono (Nat.zero_le t') by_omega
  have h3 := hS.e_mono ztmog le_rfl
  have h3' := hS.e_mono (show t' + 1 ≤ 3 by omega) le_rfl
  have := hS.inj by_grind
    by_grind (c.trans c'.symm)
  zumo
  zubxx
  · have := hS.e_mono ztgmb by_omega; omega
  · have := hS.e_mono (show t' + 1 ≤ t by omega) by_omega; omega

/-- **Split the top segment.**  The large classes are pushed (`news`), the small nonempty ones
finished. -/
theorem SInv.split {rest news : List ztw}
    {fin : Finset ztw} {D sep : Finset ℕ} {nsp : ℕ} {e : ℕ → ℕ}
    (hI : SInv μ k s H slab Adj act (p :: rest) fin D nsp)
    (hS : SplitOK (μ := μ) (k := k) (Adj := Adj) act act' p e sep)
    (hnews : ∀ q, q ∈ news ↔ ∃ t, t < 3 ∧ q = scls e t ∧ s < len q) (hnd : news.Nodup)
    (hrng : ∀ q, Lv (p :: rest) fin q → q.2 ≤ μ) :
    SInv μ k s H slab Adj act' ztcny
      (fin ∪ ((Finset.range 3).image (scls e)).filter ztiss)
      (D ∪ sep) ztodu := by
  classical
  set fin' := fin ∪ ((Finset.range 3).image _).filter ztiss
  have hLp : Lv (p :: rest) fin p := Or.inl (List.mem_cons_self)
  have hbig := hI.big p List.mem_cons_self
  have hpwf := hI.wf p hLp
  have hoffp := hI.off p hLp
  -- the old live segments other than `p` are untouched
  have hold : ∀ q, Lv (p :: rest) fin q → q ≠ p → items act' q = items act q := by
    zumhg
    refine items_congr (fun i a b => hS.out i ?_ by_grind)
    zuebr
    · omega
    · omega
    · omega
    grind
  -- classification of the new live segments
  have hlive : ∀ q, Lv ztcny fin' q →
      (Lv (p :: rest) fin q ∧ q ≠ p) ∨ (∃ t, t < 3 ∧ q = scls e t ∧ 0 < len q) := by
    zuco
    zubht
    · zucyk
      · grind
      · refine Or.inl ⟨Or.inl by_simp_all, fun h => ?_⟩
        zubst
        exact (List.nodup_cons.mp hI.nodup).1 hq
    · zujci
      · refine Or.inl ztomf
        subst h; exact hI.sf q List.mem_cons_self hq
      grind
  have hcls_live : ∀ t, t < 3 → 0 < len ztbug → Lv ztcny fin' ztbug := by
    intro t ht hpos
    by_cases hb : s < len ztbug
    · zulef
    · refine Or.inr by_grind
  have hold_live : ∀ q, Lv (p :: rest) fin q → q ≠ p → Lv ztcny fin' q := by
    zumhg
    zubht
    · rcases List.mem_cons.mp hq with h | h
      · simp_all
      · zudxj
    · zufsb
  have hclsp : ∀ t, t < 3 → scls e t ≠ p ∧ len ztbug < len p := by
    zucj
    have := hS.half t ht
    have hl : len ztbug < len p := by unfold len at *; simp only [scls] at *; omega
    grind
  have hnew_items : ∀ t, t < 3 → ∀ v ∈ items act' ztbug, v ∈ items act p ∧ v ∉ sep :=
    hS.inparts
  have hsep_off : ∀ v ∈ sep, v ∉ D ∧ v ∉ H := fun v hv => hoffp v (hS.sub hv)
  -- range disjointness of a class and an old segment
  have hrd_cls_old : ∀ t, t < 3 → ∀ q, Lv (p :: rest) fin q → q ≠ p → RDisj ztbug q := by
    intro t ht q hq hqp
    zufxt
    zuebr
    · right; left; simp only [scls]; omega
    · left; simp only [scls]; omega
    · tauto
    · unfold len at hbig; omega
  refine ⟨fun q hq => ?_, fun q hq => ?_, fun q hq v hv => ?_, ?_, fun q hq hqf => ?_,
    fun q q' hq hq' hne => ?_, fun q q' hq hq' hne => ?_, fun q hq => ?_, fun q hq => ?_,
    fun v hv h1 h2 => ?_, fun q hq v hv => ?_, fun q hq v hv w hw => ?_,
    fun x y hxy a b c d => ?_, ?_, ?_, ?_⟩
  · -- well formed
    rcases hlive q hq with ⟨h1, _⟩ | ⟨t, ht, rfl, _⟩
    · exact hI.wf q h1
    · exact hS.mono t ht
  · -- injective
    zukc
    · zubgs
      simp only [Finset.coe_Ico, Set.mem_Ico] at hi hj
      have ho : ∀ i, q.1 ≤ i → i < q.2 → act' i = act i := by
        zujbd
        refine hS.out i ?_ by_grind
        rcases hI.rdisj q p h1 hLp h2 with h | h | h | h
        · omega
        · omega
        · omega
        grind
      rw [ho i hi.1 hi.2, ho j hj.1 hj.2] at hij
      exact hI.inj q h1 by_grind by_grind hij
    · exact hS.scls_inj ht
  · -- vertices
    zukc
    · rw [hold q h1 h2] at hv; exact hI.lt q h1 v hv
    · exact hI.lt p hLp v by_grind
  · -- nodup
    refine List.Nodup.append hnd (List.nodup_cons.mp hI.nodup).2 ?_
    zubol

    have hne := (hclsp t ht).1
    have hrd := hI.rdisj _ p hq2' hLp hne
    zugi

  · -- stack and finished disjoint
    zucyk
    · obtain ⟨t, ht, rfl, hb⟩ := (hnews q).mp hq
      zujcj
      · -- an old finished segment equal to a large class: ranges overlap
        have hL' : ztdrj := Or.inr h
        zuhfn
        zugi

      grind
    · zujcj
      · exact hI.sf q by_grind h
      · obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp h
        zufzd
        have hL' : ztdrj := Or.inl ztnmm
        zuhfn
        obtain ⟨a, b, c⟩ := hS.scls_in ztffj
        have := hq2.1
        unfold len at this hbig
        simp only [scls] at hrd this
        rcases hrd with h | h | h | h <;> omega
  · -- range disjointness
    rcases hlive q hq with ⟨h1, h2⟩ | ⟨t, ht, rfl, _⟩ <;>
      zucth
    · exact hI.rdisj q q' h1 h1' hne
    · have := hrd_cls_old t' ht' q h1 h2
      unfold RDisj at this ⊢; omega
    · grind
    · have htt : t ≠ t' := by_grind
      simp only [RDisj, scls]
      rcases Nat.lt_or_gt_of_ne htt with h | h
      · left; exact hS.e_mono by_grind by_omega
      · right; left; exact hS.e_mono by_grind by_omega
  · -- item disjointness
    rcases hlive q hq with ⟨h1, h2⟩ | ⟨t, ht, rfl, _⟩ <;>
      zucth
    · rw [hold q h1 h2, hold q' h1' h2']; exact hI.disj q q' h1 h1' hne
    · rw [hold q h1 h2, Finset.disjoint_left]
      zugon
      exact Finset.disjoint_left.mp ztpce hv by_grind
    · rw [hold q' h1' h2', Finset.disjoint_left]
      zugon
      exact Finset.disjoint_left.mp (hI.disj q' p h1' hLp h2') hv' by_grind
    · exact hS.scls_disj ht ht' by_grind
  · -- large on the stack
    zucyk
    · grind
    · exact hI.big q by_grind
  · -- small finished
    rcases Finset.mem_union.mp hq with h | h
    · exact hI.small q h
    grind
  · -- cover
    rw [Finset.mem_union, not_or] at h2
    obtain ⟨q, hq, hvq⟩ := hI.cover v hv h1 h2.1
    zudme
    · subst hqp
      obtain ⟨t, ht, hvt⟩ := hS.parts v hvq h2.2
      have hpos : ztbabr := by
        obtain ⟨i, a, b, _⟩ := mem_items.mp hvt
        zuluo
      exact ⟨scls e t, by_grind, hvt⟩
    grind
  · -- off
    zukc
    · rw [hold q h1 h2] at hv
      obtain ⟨a, b⟩ := hI.off q h1 v hv
      refine ⟨?_, b⟩
      rw [Finset.mem_union, not_or]
      refine ⟨a, fun hs => ?_⟩
      exact Finset.disjoint_left.mp ztpce hv (hS.sub hs)
    grind
  · -- slabs
    zukc
    · rw [hold q h1 h2] at hv hw; exact hI.inslab q h1 v hv w hw
    · exact hI.inslab p hLp v by_grind w by_grind
  · -- edges
    rw [Finset.mem_union, not_or] at b d
    obtain ⟨q, hq, hxq, hyq⟩ := hI.edge x y hxy a b.1 c d.1
    zudme
    · subst hqp
      obtain ⟨t, ht, hxt⟩ := hS.parts x hxq b.2
      obtain ⟨t', ht', hyt⟩ := hS.parts y hyq d.2
      have := hS.noedge x y hxy t t' ht ht' hxt hyt
      zumo
      have hpos : ztbabr := by
        obtain ⟨i, a, b, _⟩ := mem_items.mp hxt
        zuluo
      exact ⟨scls e t, by_grind, hxt, hyt⟩
    grind
  · -- `D ∪ sep` stays off `H`
    rw [Finset.disjoint_union_left]
    exact ⟨hI.hD, Finset.disjoint_left.mpr by_grind⟩
  · -- the potential
    have hdisjDs : Disjoint D sep := Finset.disjoint_right.mpr by_grind
    rw [Finset.card_union_of_disjoint hdisjDs]
    have hpot := hI.pot
    zucml

    have hdn : Disjoint news.toFinset rest.toFinset := by
      zuzt
      zumhf
      exact List.disjoint_of_nodup_append (List.Nodup.append hnd (List.nodup_cons.mp hI.nodup).2
        (by
          zubol

          zuhfo
          zufxt
          unfold len at hb hbig
          simp only [scls] at hrd hb
          rcases hrd with h | h | h | h <;> omega)) (List.mem_toFinset.mp h1)
          ztuzr
    zulpc
    -- the new terms
    have hsub : ztlbb := by
      zuco
      zudew

    have hnewsum : ∑ q ∈ news.toFinset, 3 * k * ztowh ≤
        ∑ t ∈ Finset.range 3, 3 * k * ztigs :=
      le_trans ztsxo
        ztuys
    -- the recursion bound
    have hsizes : ztydc := by
      have hcard : ztxmo :=
        fun t ht => items_card ztvtx
      rw [← Finset.sum_congr rfl ztyqw,
        ← Finset.card_biUnion (fun t ht t' ht' htt' => hS.scls_disj ztffj
          ztuyo htt')]
      zugxy

    have hb := Chazelle.Separator.sum_split_bound _ ztqoe
      _ s hsizes ztyqv hbig
    have hb3 : 3 * k * (s + ∑ t ∈ Finset.range 3, ztigs) ≤
        3 * k * ztcyr := Nat.mul_le_mul_left _ hb
    rw [Nat.mul_add, Finset.mul_sum] at hb3
    have hsc : s * sep.card ≤ s * (3 * k) := Nat.mul_le_mul_left _ hS.card
    grind
  · -- the split counter
    have hpot := hI.pot2
    zucml

    have hdn : Disjoint news.toFinset rest.toFinset := by
      zuzt
      zumhf
      obtain ⟨t, ht, rfl, hb⟩ := (hnews q).mp (List.mem_toFinset.mp h1)
      have hq2' : ztdrj :=
        Or.inl (List.mem_cons_of_mem _ ztuzr)
      zuhfo
      zugi

    zulpc
    have hsub : ztlbb := by
      zuco
      zudew

    have hnewsum : ∑ q ∈ news.toFinset, ztowh ≤
        ∑ t ∈ Finset.range 3, ztigs :=
      le_trans ztsxo
        ztuys
    have hsizes : ztydc := by
      have hcard : ztxmo :=
        fun t ht => items_card ztvtx
      rw [← Finset.sum_congr rfl ztyqw,
        ← Finset.card_biUnion (fun t ht t' ht' htt' => hS.scls_disj ztffj
          ztuyo htt')]
      zugxy

    have hb := Chazelle.Separator.sum_split_bound _ ztqoe
      _ s hsizes ztyqv hbig
    grind

/-- **The size potential of a split**: `Σ_{classes} |C| · size |C| + |P| ≤ |P| · size |P|`
when the classes have at most half of `|P|` items each and at most `|P|` in total. -/
theorem split_size_pot (m : ℕ → ℕ) (M : ℕ) (hsum : ∑ t ∈ Finset.range 3, m t ≤ M)
    (hhalf : ∀ t, t < 3 → 2 * m t ≤ M) :
    ∑ t ∈ Finset.range 3, m t * Nat.size ztmmi + M ≤ M * Nat.size M := by
  have hsz : ∀ t, t < 3 → m t * Nat.size ztmmi + m t ≤ m t * Nat.size M := by
    zucj
    rcases Nat.eq_zero_or_pos ztmmi with h0 | hpos
    · simp_all
    · have h2 : Nat.size _ ≤ Nat.size M := Nat.size_le_size (hhalf t ht)
      have h3 : Nat.size (2 * m t) = Nat.size ztmmi + 1 := by
        rw [show 2 * m t = m t <<< 1 by rw [Nat.shiftLeft_eq_mul_pow]; ring]
        exact Nat.size_shiftLeft by_omega 1
      calc m t * Nat.size _ + m t = m t * (Nat.size _ + 1) := by_ring
        _ ≤ m t * Nat.size M := by_simp_all
  have h1 : ∑ t ∈ Finset.range 3, (m t * Nat.size _ + m t) ≤
      ∑ t ∈ Finset.range 3, m t * Nat.size M :=
    Finset.sum_le_sum (fun t ht => hsz t ztffj)
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at h1
  have h2 : ztmpv * Nat.size M ≤ M * Nat.size M :=
    Nat.mul_le_mul_right _ hsum
  -- `M ≤ |P| size |P| - Σ |C| size |C|` needs `M ≤ (M - Σ) size M + Σ`: fine when `size M ≥ 1`
  rcases Nat.eq_zero_or_pos M with hM | hM
  · omega
  · have hs1 := Nat.size_pos.mpr hM
    have h3 : ztfbc ≤ ztfbc * Nat.size M :=
      Nat.le_mul_of_pos_right _ hs1
    have h4 : ztfbc * Nat.size M + ztmpv *
        Nat.size M = M * Nat.size M := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hsum]
    omega
end stack
variable {V F D : Type*} (M : CombMap V F D)

/-- The rotation of the star map. -/
def starRot : Perm ztjhv where
  toFun x := match x with
    | .inl d => .inr (.inr (M.rot d))
    | .inr (.inl d) => .inr ztzal
    | .inr (.inr d) => .inl d
  invFun x := match x with
    | .inl d => .inr ztprz
    | .inr (.inl d) => .inr (.inl ztjju)
    | .inr (.inr d) => .inl (M.rot⁻¹ d)
  left_inv x := by rcases x with d | d | d <;> simp
  right_inv x := by rcases x with d | d | d <;> simp

/-- The opposite darts of the star map. -/
def starOpp : Perm ztjhv where
  toFun x := match x with
    | .inl d => .inl ztxa
    | .inr (.inl d) => .inr ztprz
    | .inr (.inr d) => .inr ztbrs
  invFun x := match x with
    | .inl d => .inl ztxa
    | .inr (.inl d) => .inr ztprz
    | .inr (.inr d) => .inr ztbrs
  left_inv x := by rcases x with d | d | d <;> zunrk
  right_inv x := by rcases x with d | d | d <;> zunrk
variable (d : D)
@[simp] theorem starRot_inl : starRot M (.inl d) = .inr (.inr (M.rot d)) := rfl
@[simp] theorem starRot_inl_inr : starRot M (.inr (.inl d)) = .inr (.inl (M.fperm⁻¹ d)) :=
  rfl
@[simp] theorem starRot_inr_inr : starRot M (.inr (.inr d)) = .inl d := rfl
@[simp] theorem starOpp_inl : starOpp M (.inl d) = .inl (M.opp d) := rfl
@[simp] theorem starOpp_inl_inr : starOpp M (.inr (.inl d)) = .inr (.inr d) := rfl
@[simp] theorem starOpp_inr_inr : starOpp M (.inr (.inr d)) = .inr (.inl d) := rfl

/-- The tail vertex in the star map. -/
def starVert : D ⊕ D ⊕ D → V ⊕ F
  | .inl d => .inl ztbmc
  | .inr (.inl d) => .inr ztcci
  | .inr (.inr d) => .inl ztbmc

/-- The face in the star map. -/
def starFace : D ⊕ D ⊕ D → D
  | .inl d => d
  | .inr (.inl d) => d
  | .inr (.inr d) => M.fperm⁻¹ d
@[simp] theorem starVert_inl : starVert M (.inl d) = .inl (M.vert d) := rfl
@[simp] theorem starVert_inl_inr : starVert M (.inr (.inl d)) = .inr (M.face d) := rfl
@[simp] theorem starVert_inr_inr : starVert M (.inr (.inr d)) = .inl (M.vert d) := rfl
@[simp] theorem starFace_inl : starFace M (.inl d) = d := rfl
@[simp] theorem starFace_inl_inr : starFace M (.inr (.inl d)) = d := rfl
@[simp] theorem starFace_inr_inr : starFace M (.inr (.inr d)) = M.fperm⁻¹ d := rfl

/-- The face permutation of the star map, explicitly. -/
theorem starFperm_inl : ztgmh ztbrs = .inr ztbadk := by
  rfl
theorem starFperm_inr_inr :
    ztgmh ztcsa = .inr ztzal := by
  simp
theorem starFperm_inl_inr : ztgmh ztxfu = .inl d := by
  simp
variable [Finite D]

/-- **The star map** of a combinatorial map. -/
def star : CombMap (V ⊕ F) D ztjhv where
  rot := starRot M
  opp := starOpp M
  vert := starVert M
  face := starFace M
  opp_opp x := by rcases x with d | d | d <;> zunrk
  opp_ne x := by
    rcases x with d | d | d <;> simp [M.opp_ne]
  vert_rot x := by
    zuim
    · zumpl
    · simp only [starRot_inl_inr, starVert_inl_inr, Sum.inr.injEq]
      have := M.face_fperm_apply ztfnz
      simp_all
    · simp
  sameCycle_of_vert x y hxy := by
    -- real vertices: old darts along `rot`, reverse spokes one step before their old dart
    have hold : ∀ d e : D, M.vert d = M.vert e →
        (starRot M).SameCycle ztbrs ztuvh := by
      zumgn
      refine sameCycle_of_step M.rot ztmop Sum.inl (fun z => ?_) (M.sameCycle_of_vert d e hde)
      exact ⟨2, by_rfl⟩
    have hspoke : ∀ d : D, (starRot M).SameCycle ztcsa ztbrs := fun d => ztufp
    have hctr : ∀ d e : D, M.face d = M.face e →
        (starRot M).SameCycle ztxfu (.inr ztuvh) := by
      zumgn
      have h1 : M.fperm⁻¹.SameCycle d e := (M.sameCycle_of_face d e hde).inv
      exact sameCycle_of_step M.fperm⁻¹ ztmop (fun z => Sum.inr (Sum.inl z))
        (fun z => ztufp) h1
    rcases x with d | d | d <;> rcases y with e | e | e <;>
      simp only [starVert_inl, starVert_inl_inr, starVert_inr_inr, Sum.inl.injEq, Sum.inr.injEq,
        reduceCtorEq] at hxy
    · simp_all
    · exact (hold d e hxy).trans (hspoke e).symm
    · simp_all
    · exact (hspoke d).trans (hold d e hxy)
    · exact (hspoke d).trans ((hold d e hxy).trans (hspoke e).symm)
  face_fperm x := by
    zuim
    · show starFace M (ztgmh ztbrs) = _
      zukyq
    · simp
    simp
  sameCycle_of_face x y hxy := by
    -- every dart is in the face cycle of its old dart
    have key : ∀ z : D ⊕ D ⊕ D, (starRot M * starOpp M).SameCycle (.inl (starFace M z)) z := by
      intro z
      rcases z with d | d | d
      · rfl
      · refine ztolp
        simp only [starFace_inl_inr, zpow_ofNat, pow_two, Perm.mul_apply]
        rw [show (starOpp M) (Sum.inl d) = Sum.inl ztxa from rfl]
        simp only [starRot_inl, starOpp_inr_inr, starRot_inl_inr, Sum.inr.injEq, Sum.inl.injEq]
        rw [← M.fperm_apply]; simp
      · refine ztfvv
        simp only [starFace_inr_inr, zpow_one]
        zukyq
    have h1 := key x
    have h2 := key y
    rw [show starFace M x = starFace M y from hxy] at h1
    exact h1.symm.trans h2
  vert_surj v := by
    rcases v with v | g
    · obtain ⟨d, rfl⟩ := M.vert_surj v; simp
    · obtain ⟨d, rfl⟩ := M.face_surj g; simp
  face_surj d := ⟨.inl d, rfl⟩

/-! ## The star map: basic facts -/
@[simp] theorem star_rot : (star M).rot = starRot M := rfl
@[simp] theorem star_opp : (star M).opp = starOpp M := rfl
@[simp] theorem star_vert : (star M).vert = starVert M := rfl
@[simp] theorem star_face : (star M).face = starFace M := rfl
theorem star_fperm_inl : (star M).fperm ztbrs = .inr ztbadk :=
  starFperm_inl M d
theorem star_fperm_inr_inr : (star M).fperm ztcsa = .inr ztzal :=
  starFperm_inr_inr M d
theorem star_fperm_inl_inr : (star M).fperm ztxfu = .inl d :=
  starFperm_inl_inr M d

/-- **Every face of the star map is a triangle.** -/
theorem star_faceDeg [Fintype D] [DecidableEq D] (g : D) : (star M).faceDeg g = 3 := by
  classical
  unfold CombMap.faceDeg
  have : Finset.univ.filter (fun x => (star M).face x = g) =
      {.inl g, .inr (.inl g), .inr (.inr (M.fperm g))} := by
    zumx
    zuim
    · zumpm
    · zumpm
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      show M.fperm⁻¹ d = g ↔ _
      rw [Perm.inv_eq_iff_eq]
      simp
  zubk
  rw [Finset.card_insert_of_notMem by_simp, Finset.card_insert_of_notMem by_simp,
    Finset.card_singleton]

/-- **Connectivity is preserved.** -/
theorem star_connected (hM : M.Connected) : (star M).Connected := by
  intro S hrot hopp x hx y
  -- the old darts in `S` form a nonempty rotation- and opposite-closed set
  have hinv : ∀ z ∈ S, ztmop⁻¹ z ∈ S := fun z hz => mem_of_inv_mem ztmop S hrot hz
  set S0 : Set D := {d | Sum.inl d ∈ S}
  have h0rot : ∀ d ∈ S0, M.rot d ∈ S0 := by
    zuip
    exact hrot _ (hrot _ hd)
  have h0opp : ∀ d ∈ S0, M.opp d ∈ S0 := fun d hd => hopp _ hd
  have hS0 : ∃ d, d ∈ S0 := by
    zuim
    · tauto
    · exact ⟨d, hrot _ (hopp _ hx)⟩
    · exact ⟨d, hrot _ hx⟩
  obtain ⟨d0, hd0⟩ := hS0
  have hall : ∀ d, Sum.inl d ∈ S := fun d => hM S0 h0rot h0opp d0 hd0 d
  rcases y with d | d | d
  · grind
  · exact hopp _ (hinv _ ztvun)
  · exact hinv _ ztvun

/-- **The Euler characteristic is preserved.** -/
theorem star_euler [Fintype V] [Fintype F] [Fintype D] [DecidableEq D] :
    (star M).euler = M.euler := by
  have h1 := (star M).two_mul_euler
  zumbf
  simp only [Fintype.card_sum] at h1
  omega

/-- **The star map of a planar map is planar.** -/
theorem star_planar [Fintype V] [Fintype F] [Fintype D] [DecidableEq D] (hM : M.Planar) :
    (star M).Planar :=
  ⟨star_connected M hM.1, by rw [star_euler]; exact hM.2⟩

/-! ## The spanning tree of the star map -/

/-- **The spanning tree of the star map**: the tree `T` of `M` on the real vertices, and the
centre of `g` hanging at the corner `vert (a g)` by the spoke `inr (inl (a g))`. -/
def starTree {M : CombMap V F D} (T : CombMap.SpanTree M) (a : F → D)
    (ha : ∀ g, M.face ztbkl = g) : CombMap.SpanTree (star M) where
  root := .inl T.root
  level x := match x with
    | .inl v => T.level v
    | .inr g => T.level ztzcd + 1
  par x := match x with
    | .inl v => .inl zteoj
    | .inr g => .inr ztbadj
  level_root := T.level_root
  vert_par x hx := by
    zugaj
    · zuhdl
      simp [T.vert_par v this]
    simp_all
  level_head_par x hx := by
    zugaj
    · zuhdl
      show T.level ztbaeh + 1 = T.level v
      exact T.level_head_par v this
    · rfl
@[simp] theorem starTree_level_inl {M : CombMap V F D} (T : CombMap.SpanTree M) (a : F → D)
    (ha : ∀ g, M.face ztbkl = g) (v : V) : (starTree T a ha).level ztgbq = T.level v := rfl
@[simp] theorem starTree_root {M : CombMap V F D} (T : CombMap.SpanTree M) (a : F → D)
    (ha : ∀ g, M.face ztbkl = g) : (starTree T a ha).root = .inl T.root := rfl
end
@[expose] public section
variable {V F D : Type*} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F] [Fintype D]
  [DecidableEq D] {M : CombMap V F D} (T : SpanTree M) (a : F → D) (ha : ∀ g, M.face ztbkl = g)
omit [Fintype V] [Fintype F] [DecidableEq D] in
theorem starTree_parent_inl (v : V) :
    (starTree T a ha).parent ztgbq = .inl ztqda := by
  unfold SpanTree.parent
  zufro
  · simp_all
  · have : (Sum.inl v : V ⊕ F) ≠ (starTree T a ha).root := by_simp_all
    rw [ite_eq_right this, ite_eq_right hv]
    rfl
omit [Fintype V] [Fintype F] [DecidableEq D] in
theorem starTree_parent_inr (g : F) :
    (starTree T a ha).parent ztuvj = .inl ztzcd := by
  rfl
omit [Fintype V] [Fintype F] [DecidableEq D] in
theorem starTree_iterate_inl (n : ℕ) (v : V) :
    (starTree T a ha).parent^[n] ztgbq = .inl (T.parent^[n] v) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, starTree_parent_inl, ih, Function.iterate_succ_apply]
omit [Fintype V] [Fintype F] [DecidableEq D] in
/-- Ancestry between real vertices is ancestry in `T`. -/
theorem starTree_isAnc_inl (v u : V) :
    (starTree T a ha).IsAnc ztgbq (.inl u) ↔ T.IsAnc v u := by
  constructor
  · zurf
    rw [starTree_iterate_inl] at hn
    exact ztryx
  · zurf
    exact ⟨n, by rw [starTree_iterate_inl, hn]⟩
omit [Fintype V] [Fintype F] [DecidableEq D] in
/-- A real vertex is an ancestor of a centre iff it is an ancestor of its corner. -/
theorem starTree_isAnc_inr (v : V) (g : F) :
    (starTree T a ha).IsAnc ztgbq ztuvj ↔ T.IsAnc v ztzcd := by
  constructor
  · zurf
    zugai
    · simp_all
    · rw [Function.iterate_succ_apply, starTree_parent_inr, starTree_iterate_inl] at hn
      exact ztryx
  · zurf
    exact ⟨n + 1, by rw [Function.iterate_succ_apply, starTree_parent_inr,
      starTree_iterate_inl, hn]⟩

/-- The three darts of the star face `f`. -/
def starDarts (f : D) : ℕ → D ⊕ D ⊕ D
  | 0 => .inl f
  | 1 => .inr ztpry
  | _ => .inr ztuvi
omit [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F] [DecidableEq D] in
/-- The darts of the star face `f` are the three `starDarts f t`. -/
theorem star_face_iff (f : D) (e : D ⊕ D ⊕ D) :
    (star M).face e = f ↔ ∃ t, t < 3 ∧ starDarts (M := M) f t = e := by
  constructor
  · zuq
    rcases e with d | d | d
    · exact ⟨0, by_omega, by simp only [star_face, starFace_inl] at h; subst h; rfl⟩
    · exact ⟨2, by_omega, by simp only [star_face, starFace_inl_inr] at h; subst h; rfl⟩
    · refine ztqzv
      simp only [star_face, starFace_inr_inr] at h
      zubst
      zuouh
  · zuifv
    rcases ztxp with rfl | rfl | rfl <;> zuouh
omit [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F] [Fintype D] [DecidableEq D] in
theorem starDarts_inj (f : D) {t t' : ℕ} (ht : t < 3) (ht' : t' < 3)
    (h : starDarts (M := M) f t = starDarts (M := M) f t') : t = t' := by
  rcases ztxp with rfl | rfl | rfl <;>
    rcases (show t' = 0 ∨ t' = 1 ∨ t' = 2 by omega) with rfl | rfl | rfl <;>
    simp_all [starDarts]
omit [DecidableEq D] in
/-- **The separator of a star face**, restricted to real vertices. -/
theorem star_mem_sepSet_inl (f : D) (v : V) :
    (Sum.inl v : V ⊕ F) ∈ (starTree T a ha).sepSet f ↔
      T.IsAnc v ztjka ∨ T.IsAnc v ztjjw ∨ T.IsAnc v ztdyr := by
  rw [SpanTree.mem_sepSet]
  constructor
  · rintro ⟨e, he, hanc⟩
    obtain ⟨t, ht, rfl⟩ := (star_face_iff f e).mp he
    zublm
    · left; simpa [starDarts, starTree_isAnc_inl] using hanc
    · zuhl
      simp only [starDarts, star_vert, starVert_inr_inr] at hanc
      rw [starTree_isAnc_inl, M.vert_fperm] at hanc
      omega
    · zulw
      simp only [starDarts, star_vert, starVert_inl_inr] at hanc
      exact (starTree_isAnc_inr T a ha v _).mp hanc
  · zuciz
    · exact ⟨.inl f, rfl, by simpa [starTree_isAnc_inl] using h⟩
    · refine ⟨.inr ztpry, ?_, ?_⟩
      · simp
      · simp only [star_vert, starVert_inr_inr]
        rw [starTree_isAnc_inl, M.vert_fperm]; exact h
    · exact ⟨.inr ztuvi, rfl, (starTree_isAnc_inr T a ha v _).mpr h⟩

/-- **The separator in a slab**: at most `3 k` real vertices whose levels (shifted by `c`) lie in
a window of `k` levels. -/
theorem star_sep_card (f : D) (c j k : ℕ) (S : Finset V)
    (hS : ∀ v ∈ S, j * k ≤ T.level v + c ∧ T.level v + c < j * k + k) :
    (S.filter (fun v => (Sum.inl v : V ⊕ F) ∈ (starTree T a ha).sepSet f)).card ≤ 3 * k := by
  classical
  have h := (starTree T a ha).card_sepSet_filter_shift_le f c (Finset.Ico (j * k) (j * k + k))
  rw [star_faceDeg, Nat.card_Ico, show j * k + k - j * k = k by omega] at h
  refine le_trans ?_ h
  rw [← Finset.card_map Function.Embedding.inl]
  refine Finset.card_le_card ztjwp
  obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hx
  rw [Finset.mem_filter] at hv ⊢
  refine ⟨hv.2, ?_⟩
  rw [Finset.mem_Ico]
  exact hS v hv.1
end
@[expose] public section
def enc (N : ℕ) : Fin N ⊕ Fin N ⊕ Fin N → ℕ
  | .inl d => d
  | .inr (.inl d) => N + d
  | .inr (.inr d) => 2 * N + d
theorem enc_lt {N : ℕ} (x : Fin N ⊕ Fin N ⊕ Fin N) : enc N x < 3 * N := by
  rcases x with d | d | d <;> simp only [enc] <;> omega
theorem enc_inj {N : ℕ} {x y : Fin N ⊕ Fin N ⊕ Fin N} (h : enc N x = enc N y) : x = y := by
  rcases x with d | d | d <;> rcases y with e | e | e <;> simp only [enc] at h <;>
    first | (congr 1; exact by_omega) | (congr 2; exact by_grind) |
      (exfalso; omega)

/-- The class test of the RAM for the star dart `X` of the face `f`, at the key `κ`. -/
def inClass (sopp sface fparN pre sz : ℕ → ℕ) (r0 X f κ : ℕ) : Prop :=
  if sface (sopp X) ≠ r0 ∧ fparN ztglv = X then
    pre ztglv ≤ κ ∧ κ < pre ztglv + sz ztglv
  else if f ≠ r0 ∧ sopp ztvqp = X then ¬ (pre f ≤ κ ∧ κ < pre f + sz f) else False
variable {μ N : ℕ} {F : Type} [Fintype F] [DecidableEq F] {M : CombMap (Fin μ) F (Fin N)}
  {T : SpanTree M} {a : F → Fin N} {ha : ∀ g, M.face ztbkl = g}
  {C : CoTree ztqc} {R : BTree}

/-- Descendants in the cotree are descendants in the preorder tree. -/
theorem isDesc_iff_anc (hup : ∀ g : Fin N, R.up g = (C.parent g : ℕ)) (h g : Fin N) :
    C.IsDesc h g ↔ R.Anc g h := by
  have hit : ∀ n (x : Fin N), R.up^[n] x = ((C.parent^[n] x : Fin N) : ℕ) := by
    zugok
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      zugop
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← ih, hup]
  constructor
  · zurf
    exact ⟨n, by_simp_all⟩
  · zurf
    exact ⟨n, by_grind⟩

/-- **The class test is the side of the fundamental cycle.** -/
theorem inClass_iff (hM : M.Planar) {sopp sface fparN pre sz : ℕ → ℕ} {r0 : ℕ}
    (hsopp : ∀ x, sopp zterv = enc N ztfeh)
    (hsface : ∀ x, sface zterv = ((star M).face x : ℕ))
    (hr0 : r0 = (C.r0 : ℕ))
    (hfpar : ∀ g : Fin N, g ≠ C.r0 → fparN g = enc N ztcch)
    (hint : ∀ g h : Fin N, C.IsDesc h g ↔ pre g ≤ pre h ∧ pre h < pre g + sz g)
    {f : Fin N} {x : Fin N ⊕ Fin N ⊕ Fin N} (hx : (star M).face x = f) (h : Fin N) :
    inClass sopp sface fparN pre sz r0 zterv f (pre h) ↔
      x ∈ (starTree T a ha).coDarts ∧ h ∈ (starTree T a ha).cross x := by
  zukaj
  set gF : Fin N := (star M).face ztfeh with hgF
  have hg : sface (sopp zterv) = (gF : ℕ) := by_grind
  have hne : ∀ g : Fin N, (g : ℕ) ≠ r0 ↔ g ≠ C.r0 := by
    omega
  unfold inClass
  zuguv
  by_cases hd : (gF : ℕ) ≠ r0 ∧ fparN gF = enc N x
  · rw [ite_eq_left hd]
    have hg0 : gF ≠ C.r0 := by_omega
    have hfx : C.fpar gF = x := enc_inj by_grind
    rw [← hfx, C.cross_fpar hSM hg0, hint]
    exact ⟨fun h => ⟨C.mem gF hg0, h⟩, by_omega⟩
  · zuhmn
    by_cases hu : (f : ℕ) ≠ r0 ∧ sopp ztvqp = enc N x
    · rw [ite_eq_left hu]
      have hf0 : f ≠ C.r0 := by_omega
      have hfx : (star M).opp (C.fpar f) = x := by
        apply enc_inj
        grind
      rw [← hfx, C.cross_opp_fpar hSM hf0, hint]
      exact ⟨fun h => ⟨(starTree T a ha).opp_mem_coDarts (C.mem f hf0), h⟩, by_omega⟩
    · rw [ite_eq_right hu]
      simp only [false_iff, not_and]
      intro hco _
      obtain ⟨g', hg', rfl | rfl⟩ := (C.mem_coDarts_iff hSM).mp hco
      · -- a parent dart: the down test holds
        apply hd
        have  := C.head g' hg'
        grind
      · -- the opposite of a parent dart: the up test holds
        apply hu
        have hfg : f = g' := by rw [← hx]; exact C.head g' hg'
        grind

/-- The vertex choice of the star map: the old dart `first v` at a real vertex, the spoke of
`a g` at a centre. -/
def delta (first : Fin μ → Fin N) (a : F → Fin N) : Fin μ ⊕ F → Fin N ⊕ Fin N ⊕ Fin N
  | .inl v => .inl zthws
  | .inr g => .inr ztbadj
omit [Fintype F] [DecidableEq F] in
theorem delta_vert {first : Fin μ → Fin N} (hfirst : ∀ v, M.vert zthws = v)
    (ha' : ∀ g, M.face ztbkl = g) (x : Fin μ ⊕ F) :
    (star M).vert ztrop = x := by
  zugaj
  · simp [delta, hfirst]
  · simp [delta, ha']

/-- A set of real vertices as a set of star vertices. -/
noncomputable def liftP (P : Finset ℕ) : Finset (Fin μ ⊕ F) :=
  haveI := Classical.decPred (fun v : Fin μ => (v : ℕ) ∈ P)
  (Finset.univ.filter (fun v : Fin μ => (v : ℕ) ∈ P)).map Function.Embedding.inl
omit [Fintype F] [DecidableEq F] in
theorem mem_liftP {P : Finset ℕ} {x : Fin μ ⊕ F} :
    x ∈ liftP (μ := μ) (F := F) P ↔ ∃ v : Fin μ, x = .inl v ∧ (v : ℕ) ∈ P := by
  unfold liftP
  rw [Finset.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    simp_all
  simp_all
omit [Fintype F] [DecidableEq F] in
theorem card_liftP {P : Finset ℕ} (hP : ∀ v ∈ P, v < μ) : (liftP (μ := μ)
    (F := F) P).card = P.card := by
  classical
  unfold liftP
  zumle
  have : P = (@Finset.filter _ (fun v : Fin μ => (v : ℕ) ∈ P) (Classical.decPred _)
      Finset.univ).map Fin.valEmbedding := by
    zuepb
    simp only [Finset.mem_map, Fin.valEmbedding_apply]
    constructor
    · intro hv
      exact ⟨ztopr, by_simp_all, rfl⟩
    grind
  conv_rhs => rw [this]
  zumle
omit [Fintype F] [DecidableEq F] in
/-- Counting a predicate of lifted vertices. -/
theorem card_filter_liftP {P : Finset ℕ} (hP : ∀ v ∈ P, v < μ) (Q : Fin μ ⊕ F → Prop)
    [DecidablePred Q] (Q' : ℕ → Prop) [DecidablePred Q']
    (hQ : ∀ v : Fin μ, (v : ℕ) ∈ P → (Q ztgbq ↔ Q' v)) :
    ((liftP (μ := μ) (F := F) P).filter Q).card = (P.filter Q').card := by
  have hP' : ∀ v ∈ P.filter Q', v < μ := by_simp_all
  rw [← card_liftP (F := F) hP']
  zucr
  zumx
  rw [Finset.mem_filter, mem_liftP, mem_liftP]
  grind

/-- Positions of a segment and its items. -/
theorem card_items_filter {act : ℕ → ℕ} {lo hi : ℕ}
    (hinj : Set.InjOn act ztjiw) (Q : ℕ → Prop) [DecidablePred Q] :
    ((items act ztdz).filter Q).card = ((Finset.Ico lo hi).filter (fun i => Q ztjoa)).card := by
  unfold items
  zubi
  rw [Finset.filter_image, Finset.card_image_of_injOn]
  zuvc
  exact hinj by_simp_all
    by_simp_all hxy

/-- **The good test is `Good`.** -/
theorem good_iff {first : Fin μ → Fin N} {firstN : ℕ → ℕ}
    (hfN : ∀ v : Fin μ, firstN v = first v) {pre sz : ℕ → ℕ}
    (hint : ∀ g h : Fin N, C.IsDesc h g ↔ pre g ≤ pre h ∧ pre h < pre g + sz g)
    {act : ℕ → ℕ} {lo hi : ℕ} (hinj : Set.InjOn act ztjiw)
    (hlt : ∀ v ∈ items act ztdz, v < μ) (z : Fin N) :
    Good C ztdhe (liftP (μ := μ) (F := F) ztxac) z ↔
      BTree.GdN pre sz ztbmw lo hi z := by
  classical
  unfold Good cnt BTree.GdN cntIn
  rw [card_liftP hlt, items_card hinj]
  have hc : ((liftP ztxac).filter
      (fun x => C.IsDesc ((star M).face ztrop) z)).card =
      ((Finset.Ico lo hi).filter (fun i => pre z ≤ pre ztzes ∧
        pre ztzes < pre z + sz z)).card := by
    rw [card_filter_liftP hlt _ (fun v => pre z ≤ pre ztvqn ∧ pre ztvqn < pre z + sz z)
      (fun v hv => by
        simp only [delta, star_face, starFace_inl]
        simp_all)]
    exact card_items_filter hinj _
  unfold len
  zubi
  zulqz

/-- The marked vertices of the split at `f`: the `T`-ancestors of the three corners of the star
face `f`. -/
def markN (T : SpanTree M) (a : F → Fin N) (f : Fin N) (v : ℕ) : Prop :=
  ∃ h : v < μ, T.IsAnc ztops ztjka ∨ T.IsAnc ztops ztjjw ∨
    T.IsAnc ztops ztdyr
theorem markN_iff (f : Fin N) (v : Fin μ) :
    markN T a f v ↔ (Sum.inl v : Fin μ ⊕ F) ∈ (starTree T a ha).sepSet f := by
  rw [star_mem_sepSet_inl]
  unfold markN
  simp
open Classical in
/-- **The split, in the terms of the RAM.**  With the centroid `f` (good, no good child) of the
piece `P = items act (lo, hi)`, the classes `inClass (enc (starDarts f t))` of the unmarked items
cover them, are disjoint, have at most half of the items each and are not joined by an edge;
the marks in a window of `k` levels are at most `3k`. -/
theorem split_math (hM : M.Planar) {first : Fin μ → Fin N} (hfirst : ∀ v, M.vert zthws = v)
    {firstN : ℕ → ℕ} (hfN : ∀ v : Fin μ, firstN v = first v)
    {sopp sface fparN pre sz : ℕ → ℕ} {r0 : ℕ}
    (hsopp : ∀ x, sopp zterv = enc N ztfeh)
    (hsface : ∀ x, sface zterv = ((star M).face x : ℕ))
    (hr0 : r0 = (C.r0 : ℕ))
    (hfpar : ∀ g : Fin N, g ≠ C.r0 → fparN g = enc N ztcch)
    (hint : ∀ g h : Fin N, C.IsDesc h g ↔ pre g ≤ pre h ∧ pre h < pre g + sz g)
    {act : ℕ → ℕ} {lo hi : ℕ} (hinj : Set.InjOn act ztjiw)
    (hlt : ∀ v ∈ items act ztdz, v < μ) {f : Fin N}
    (hgood : Good C ztdhe (liftP (μ := μ) (F := F) ztxac) f)
    (hch : ∀ g, g ≠ C.r0 → C.parent g = f →
      ¬ Good C ztdhe (liftP (μ := μ) (F := F) ztxac) g) :
    (∀ v ∈ items act ztdz, ¬ markN T a f v → ∃ t, t < 3 ∧
      inClass sopp sface fparN pre sz r0 (enc N (starDarts (M := M) f t)) f ztcwg) ∧
    (∀ v ∈ items act ztdz, ¬ markN T a f v → ∀ t t', t < 3 → t' < 3 →
      inClass sopp sface fparN pre sz r0 (enc N (starDarts (M := M) f t)) f ztcwg →
      inClass sopp sface fparN pre sz r0 (enc N (starDarts (M := M) f t')) f ztcwg →
      t = t') ∧
    (∀ t, t < 3 → 2 * ((items act ztdz).filter (fun v => ¬ markN T a f v ∧
      inClass sopp sface fparN pre sz r0 (enc N (starDarts (M := M) f t)) f
        ztcwg)).card ≤ hi - lo) ∧
    (∀ (d : Fin N) t t', t < 3 → t' < 3 →
      ((M.vert d : ℕ) ∈ items act ztdz ∧ ¬ markN T a f ztbmc ∧
        inClass sopp sface fparN pre sz r0 (enc N (starDarts (M := M) f t)) f
          (pre (firstN ztbmc))) →
      ((M.head d : ℕ) ∈ items act ztdz ∧ ¬ markN T a f ztbyq ∧
        inClass sopp sface fparN pre sz r0 (enc N (starDarts (M := M) f t')) f
          (pre (firstN ztbyq))) → t = t') := by
  set δ := delta (F := F) first a
  set P' := liftP (μ := μ) (F := F) ztxac
  zukaj
  have hδ := delta_vert hfirst ha
  have hx : ∀ e, (star M).face e = f ↔ ∃ t, t < 3 ∧ starDarts f t = e :=
    (star_face_iff f)
  have hxinj : ∀ t t', t < 3 → t' < 3 → starDarts f t = starDarts (M := M) f t' →
      t = t' := fun t t' ht ht' h => starDarts_inj f ht ht' h
  obtain ⟨hcov, huniq, hedge⟩ := split_classes (T := starTree T a ha) hSM hδ (P := P') hx hxinj
  -- the class test at a real vertex
  have hic : ∀ (v : Fin μ) t, t < 3 →
      (inClass sopp sface fparN pre sz r0 (enc N (starDarts (M := M) f t)) f ztcwg ↔
        starDarts (M := M) f t ∈ (starTree T a ha).coDarts ∧ (star M).face (δ ztgbq) ∈ (starTree T a ha).cross
          (starDarts (M := M) f t)) := by
    zumho
    have hft : (star M).face _ = f := (hx _).mpr ztbik
    rw [hfN]
    exact inClass_iff hM hsopp hsface hr0 hfpar hint hft _
  have hmemcls : ∀ (v : Fin μ) t, t < 3 →
      ((.inl v : Fin μ ⊕ F) ∈ cls ztqc δ P' f (starDarts (M := M) f) t ↔
        (v : ℕ) ∈ items act ztdz ∧ ¬ markN T a f v ∧
          inClass sopp sface fparN pre sz r0 (enc N (starDarts (M := M) f t)) f
            ztcwg) := by
    zumho
    rw [mem_cls, hic v t ht, markN_iff (ha := ha)]
    constructor
    · zuei
      obtain ⟨w, hw, hwv⟩ := mem_liftP.mp h1
      grind
    · zuei
      exact ⟨mem_liftP.mpr by_grind, h2, h3⟩
  refine ⟨fun v hv hm => ?_, fun v hv hm t t' ht ht' h1 h2 => ?_, fun t ht => ?_,
    fun d t t' ht ht' ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ => ?_⟩
  · zukgo
    have hm' := hm
    obtain ⟨t, ht, hvt⟩ := hcov (.inl ztujp) (mem_liftP.mpr ⟨_, rfl, hv⟩)
      (by rw [← markN_iff (ha := ha)]; omega)
    grind
  · zukgo
    exact huniq t t' ht ht' _ by_grind
      ((hmemcls ztujp t' ht').mpr by_grind)
  · have hh := cls_half hSM hgood hch hx ht
    rw [card_liftP hlt] at hh
    rw [items_card hinj] at hh
    have hc : (cls ztqc δ P' f (starDarts (M := M) f) t).card =
        ((items act ztdz).filter (fun v => ¬ markN T a f v ∧
          inClass sopp sface fparN pre sz r0 (enc N (starDarts (M := M) f t)) f
            ztcwg)).card := by
      have e1 : cls ztqc δ P' f (starDarts (M := M) f) t = P'.filter
          (fun x => x ∈ cls ztqc δ P' f (starDarts (M := M) f) t) := by
        zumx
        constructor
        · intro hx'
          exact Finset.mem_filter.mpr ⟨(mem_cls.mp hx').1, hx'⟩
        simp
      zukd
      exact card_filter_liftP hlt _ _ (fun v hv => by
        rw [hmemcls v t ht]; exact ztsr)
    zulqz
    tauto
  · have hs := hedge ztbrs t t' ht ht'
      ((hmemcls _ t ht).mpr by_omega)
      ((hmemcls _ t' ht').mpr ztraj)
    zujux
open Classical in
include ha in
/-- **At most `3k` marks in a window of `k` levels.** -/
theorem card_mark_le (f : Fin N) (S : Finset ℕ) (hSμ : ∀ v ∈ S, v < μ) (c j k : ℕ)
    (hS : ∀ v (hv : v ∈ S), j * k ≤ T.level ztopr + c ∧
      T.level ztopr + c < j * k + k) :
    (S.filter ztmjy).card ≤ 3 * k := by
  classical
  set S' : Finset _ := Finset.univ.filter (fun v : Fin μ => (v : ℕ) ∈ S)
  have h := star_sep_card T a ha f c j k S' (fun v hv => by
    grind)
  refine le_trans ztkad h
  zugfo
  zucr
  zuepb
  simp only [Finset.mem_filter, Finset.mem_map, Fin.valEmbedding_apply, Finset.mem_univ,
    true_and, S']
  constructor
  · rintro ⟨hv, hm⟩
    refine ⟨⟨v, hSμ v hv⟩, zthnd, rfl⟩
    rw [← markN_iff]; exact hm
  · rintro ⟨w, ⟨hw, hm⟩, rfl⟩
    exact ⟨hw, (markN_iff f w).mpr hm⟩
end
open Machine Machine.Stmt Programs
@[expose] public section
def ClassTest (mode a b κ : ℕ) : Prop :=
  (mode = 1 ∧ a ≤ κ ∧ κ < b) ∨ (2 ≤ mode ∧ ¬ (a ≤ κ ∧ κ < b))

/-- `if x = y then S`. -/
def eqThen (x y : ℕ) (S : Stmt) : Stmt := .ifLtN x y .skip (.ifLtN y x .skip S)

/-- The parameters of the down test. -/
def setDown : Stmt := block [.addN 130641 130635 130640, .loadN 130638 130641,
  .addN 130641 130636 130640, .loadN 130642 130641, .addN 130639 130638 130642,
  .constN 130637 1]

/-- The parameters of the up test. -/
def setUp : Stmt := block [.addN 130641 130635 130631, .loadN 130638 130641,
  .addN 130641 130636 130631, .loadN 130642 130641, .addN 130639 130638 130642,
  .constN 130637 2]

/-- The down test: the face `g` across `X` is not the root and `FPAR[g] = X`. -/
def downS : Stmt := .ifLtN 130009 130640
  (.seq ztjos (eqThen 130641 130630 setDown))
  .skip

/-- The up test (only if the down test failed): `f` is not the root and `SOPP[FPAR[f]] = X`. -/
def upS : Stmt := .ifLtN 130009 130637 .skip (.ifLtN 130009 130631
  (.seq (block [.addN 130641 130634 130631, .loadN 130641 130641, .addN 130641 130632 130641,
    .loadN 130641 130641]) (eqThen 130641 130630 setUp)) .skip)

/-- **The class parameters of the star dart `X` of `f`.** -/
def cpStmt : Stmt := .seq (block [.addN 130641 130632 130630, .loadN 130641 130641,
    .addN 130641 130633 130641, .loadN 130640 130641, .constN 130637 0])
  (.seq downS upS)

/-- The registers written by `cpStmt`. -/
def CpRG (r : ℕ) : Prop := ztneh

/-- The static memory of the class test. -/
structure CpMem (m : ℕ → ℕ) (W bSO bSF bFP bPR bSZ N : ℕ) : Prop where
  wSO : bSO + 3 * N ≤ W
  wSF : bSF + 3 * N ≤ W
  wFP : bFP + N ≤ W
  wPR : bPR + N ≤ W
  wSZ : bSZ + N ≤ W
  so_lt : ∀ x, x < 3 * N → m zttgk < 3 * N
  sf_lt : ∀ x, x < 3 * N → m zttgj < N
  fp_lt : ∀ g, g < N → m (bFP + g) < 3 * N
  prsz : ∀ g, g < N → m (bPR + g) + m (bSZ + g) ≤ W
section proofs
variable {P : Polygon} {W : ℕ}

/-- The equality test. -/
theorem eqThen_exec {S : Stmt} {c : Config} (hw : WordsBounded W c) (x y : ℕ)
    {R : Config → Prop} {K : ℕ}
    (hS : c.nreg x = c.nreg y → ∃ c' k, Exec P W S c c' k ∧ k ≤ K ∧ R c')
    (hne : c.nreg x ≠ c.nreg y → R c) :
    ∃ c' k, Exec P W (eqThen x y S) c c' k ∧ k ≤ K + 4 ∧ R c' := by
  unfold eqThen
  by_cases h1 : c.nreg x < c.nreg y
  · exact ⟨c, 0 + 1, .ifLtN_true h1 ztjd, by_omega, by_grind⟩
  · by_cases h2 : c.nreg y < c.nreg x
    · exact ⟨c, 0 + 1 + 2, .ifLtN_false h1 ztxdj, by_omega, by_grind⟩
    · obtain ⟨c', k, e, hk, hr⟩ := hS by_omega
      exact ⟨c', k + 2 + 2, .ifLtN_false h1 ztjdj, by_omega, hr⟩

/-- **The class parameters.** -/
theorem cpStmt_exec {c : Config} (hw : WordsBounded W c) (hzero : c.nreg 130009 = 0)
    {X f bSO bSF bFP bPR bSZ N : ℕ} (hX : c.nreg 130630 = X) (hf : c.nreg 130631 = f)
    (hSO : c.nreg 130632 = bSO) (hSF : c.nreg 130633 = bSF) (hFP : c.nreg 130634 = bFP)
    (hPR : c.nreg 130635 = bPR) (hSZ : c.nreg 130636 = bSZ)
    (hM : CpMem c.nmem W bSO bSF bFP bPR bSZ N) (hXN : X < 3 * N) (hfN : f < N) :
    ∃ c' k, Exec P W cpStmt c c' k ∧ k ≤ 45 ∧ WordsBounded W c' ∧ c'.nmem = c.nmem ∧
      (∀ r, ¬ CpRG r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output ∧
      ∀ κ, ClassTest (c'.nreg 130637) (c'.nreg 130638) (c'.nreg 130639) κ ↔
        inClass (fun x => c.nmem zttgk) (fun x => c.nmem zttgj)
          (fun x => c.nmem (bFP + x)) (fun x => c.nmem (bPR + x)) (fun x => c.nmem (bSZ + x))
          0 X f κ := by
  set sO : ℕ → ℕ := fun x => c.nmem _
  set sF : ℕ → ℕ := fun x => c.nmem _
  set fp : ℕ → ℕ := fun x => c.nmem _
  set pr : ℕ → ℕ := fun x => c.nmem _
  set sz : ℕ → ℕ := fun x => c.nmem _
  have hsoX := hM.so_lt X hXN
  set g := sF ztqvz
  have hgN : g < N := hM.sf_lt _ hsoX
  have := hM.wSO; have := hM.wSF; have := hM.wFP; have := hM.wPR; have := hM.wSZ
  -- common frame facts
  have fr : ∀ c1 : Config, ztivn →
      c1.nreg 130009 = 0 ∧ c1.nreg 130630 = X ∧ c1.nreg 130631 = f ∧ c1.nreg 130632 = bSO ∧
      c1.nreg 130633 = bSF ∧ c1.nreg 130634 = bFP ∧ c1.nreg 130635 = bPR ∧
      c1.nreg 130636 = bSZ := fun c1 h => by
    refine ztdiu <;> (rw [h _ zteqi]; assumption)
  -- the face across `X`
  obtain ⟨c1, k1, e1, hk1, hw1, h1g, h1m, h1r, hrr1, hrm1, ho1, hm1⟩ : ∃ c1 k1, Exec P W
      (block [.addN 130641 130632 130630, .loadN 130641 130641, .addN 130641 130633 130641,
        .loadN 130640 130641, .constN 130637 0]) c c1 k1 ∧ k1 = 5 ∧ WordsBounded W c1 ∧
      c1.nreg 130640 = g ∧ c1.nreg 130637 = 0 ∧ ztivn ∧
      c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output ∧ c1.nmem = c.nmem := by
    exec_block
    all_goals first | omega | (config_simp; simp only [hSO, hSF, hX]; omega) | skip
    refine ⟨rfl, by_omega, by config_simp; grind, by config_simp,
      fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    zumwj; unfold CpRG at hr; grind
  obtain ⟨z1, x1, f1, so1, sf1, fp1, pr1, sz1⟩ := fr c1 h1r
  -- the down test
  obtain ⟨c2, k2, e2, hk2, hw2, h2r, h2m, hdown, hndown, hrr2, hrm2, ho2⟩ : ∃ c2 k2,
      Exec P W downS c1 c2 k2 ∧ k2 ≤ 16 ∧ WordsBounded W c2 ∧
      (∀ r, ¬ CpRG r → c2.nreg r = c.nreg r) ∧ c2.nmem = c.nmem ∧
      (ztgjt → c2.nreg 130637 = 1 ∧ c2.nreg 130638 = pr g ∧
        c2.nreg 130639 = pr g + sz g) ∧
      (¬ ztgjt → c2.nreg 130637 = 0) ∧
      c2.rreg = c.rreg ∧ c2.rmem = c.rmem ∧ c2.output = c.output := by
    unfold downS
    by_cases hg0 : c1.nreg 130009 < c1.nreg 130640
    · zuinf
      obtain ⟨c3, k3, e3, hk3, hw3, h3p, h3r, hrr3, hrm3, ho3, hm3⟩ : ∃ c3 k3, Exec P W
          ztjos c1 c3 k3 ∧ k3 = 2 ∧
          WordsBounded W c3 ∧ c3.nreg 130641 = fp g ∧ (∀ r, r ≠ 130641 → c3.nreg r = c1.nreg r) ∧
          c3.rreg = c1.rreg ∧ c3.rmem = c1.rmem ∧ c3.output = c1.output ∧ c3.nmem = c1.nmem := by
        exec_block
        · omega
        · refine ⟨rfl, by_omega, by config_simp; grind, fun r hr => ?_, rfl, rfl, rfl,
            rfl⟩
          simp_all
      zujyt
      have h3g : c3.nreg 130640 = g := by_grind
      obtain ⟨c4, k4, e4, hk4, hR4⟩ := eqThen_exec (P := P) (S := setDown) hw3 130641 130630
        (R := fun c4 => WordsBounded W c4 ∧ ztivo ∧
          c4.nmem = c.nmem ∧ (ztgjt → c4.nreg 130637 = 1 ∧ c4.nreg 130638 = pr g ∧
            c4.nreg 130639 = pr g + sz g) ∧ (¬ (g ≠ 0 ∧ fp g = X) → c4.nreg 130637 = 0) ∧
          c4.rreg = c.rreg ∧ c4.rmem = c.rmem ∧ c4.output = c.output)
        (fun heq => by
          rw [h3p, h3x] at heq
          zuffu

          have hpg := hM.prsz g hgN
          unfold setDown
          exec_block
          all_goals first | omega | (config_simp; simp only [h3pr, h3sz, h3g, hm3, hm1]; omega) |
            skip
          refine ⟨le_refl _, by_omega, fun r hr => ?_, by_grind, fun _ => ⟨by config_simp,
            by config_simp; grind, by
              config_simp; grind⟩,
            by omega, by_grind, by_grind,
            by grind⟩
          zudi
          zumqq
          rw [ite_eq_right by_omega, ite_eq_right by_omega, ite_eq_right by_omega, ite_eq_right by_omega,
            ite_eq_right by_omega, ite_eq_right by_omega, h3r r by_omega]
          exact h1r r zteqi)
        (fun hne => by
          rw [h3p, h3x] at hne
          refine ⟨hw3, fun r hr => ?_, by_grind, by_omega, by_grind, by_grind, by_grind,
            by grind⟩
          zuohw; grind)
      obtain ⟨hw4, h4r, h4m, hd4, hnd4, hrr4, hrm4, ho4⟩ := hR4
      refine ⟨c4, k3 + k4 + 1, .ifLtN_true by_omega ztspy, by_omega,
        hw4, h4r, h4m, hd4, hnd4, hrr4, hrm4, ho4⟩
    · zuinf
      refine ⟨c1, 0 + 2, .ifLtN_false by_omega ztdbq, by_omega, hw1,
        h1r, hm1, by_omega, by_omega, hrr1, hrm1, ho1⟩
  obtain ⟨z2, x2, f2, so2, sf2, fp2, pr2, sz2⟩ := fr c2 h2r
  -- the up test
  obtain ⟨c5, k5, e5, hk5, hw5, h5r, h5m, h5test, hrr5, hrm5, ho5⟩ : ∃ c5 k5,
      Exec P W upS c2 c5 k5 ∧ k5 ≤ 20 ∧ WordsBounded W c5 ∧
      (∀ r, ¬ CpRG r → c5.nreg r = c.nreg r) ∧ c5.nmem = c.nmem ∧
      (∀ κ, ClassTest (c5.nreg 130637) (c5.nreg 130638) (c5.nreg 130639) κ ↔
        inClass sO sF fp pr sz 0 X f κ) ∧
      c5.rreg = c.rreg ∧ c5.rmem = c.rmem ∧ c5.output = c.output := by
    unfold upS
    by_cases hd : g ≠ 0 ∧ fp g = X
    · -- the down test succeeded
      obtain ⟨m1, ma, mb⟩ := hdown hd
      refine ⟨c2, 0 + 1, .ifLtN_true by_omega ztgbs, by_omega, hw2, h2r, h2m,
        fun κ => ?_, hrr2, hrm2, ho2⟩
      unfold inClass ClassTest
      grind
    · have m0 := hndown hd
      have hni : ∀ κ, inClass sO sF fp pr sz 0 X f κ ↔
          (f ≠ 0 ∧ sO ztmje = X) ∧ ¬ (pr f ≤ κ ∧ κ < pr f + sz f) := by
        intro κ
        unfold inClass
        grind
      by_cases hf0 : c2.nreg 130009 < c2.nreg 130631
      · zuing
        have hfpf := hM.fp_lt f hfN
        obtain ⟨c3, k3, e3, hk3, hw3, h3q, h3r, hrr3, hrm3, ho3, hm3⟩ : ∃ c3 k3, Exec P W
            (block [.addN 130641 130634 130631, .loadN 130641 130641, .addN 130641 130632 130641,
              .loadN 130641 130641]) c2 c3 k3 ∧ k3 = 4 ∧ WordsBounded W c3 ∧
            c3.nreg 130641 = sO ztmje ∧ (∀ r, r ≠ 130641 → c3.nreg r = c2.nreg r) ∧
            c3.rreg = c2.rreg ∧ c3.rmem = c2.rmem ∧ c3.output = c2.output ∧
            c3.nmem = c2.nmem := by
          exec_block
          all_goals first | omega | (config_simp; simp only [fp2, so2, f2, h2m]; omega) | skip
          refine ⟨rfl, by_omega, by config_simp; grind, fun r hr => ?_,
            rfl, rfl, rfl, rfl⟩
          zuhpk
        zujyt
        obtain ⟨c4, k4, e4, hk4, hR4⟩ := eqThen_exec (P := P) (S := setUp) hw3 130641 130630
          (R := fun c4 => WordsBounded W c4 ∧ ztivo ∧
            c4.nmem = c.nmem ∧ (∀ κ, ClassTest (c4.nreg 130637) (c4.nreg 130638)
              (c4.nreg 130639) κ ↔ inClass sO sF fp pr sz 0 X f κ) ∧
            c4.rreg = c.rreg ∧ c4.rmem = c.rmem ∧ c4.output = c.output)
          (fun heq => by
            rw [h3q, h3x] at heq
            zuffu

            have h3f : c3.nreg 130631 = f := by_grind
            have hpf := hM.prsz f hfN
            unfold setUp
            exec_block
            all_goals first | omega | (config_simp; zunjk; omega) |
              skip
            refine ⟨le_refl _, by_omega, fun r hr => ?_, by_grind, fun κ => ?_,
              by grind, by_grind, by_grind⟩
            · zudi
              zumqq
              rw [ite_eq_right by_omega, ite_eq_right by_omega, ite_eq_right by_omega, ite_eq_right by_omega,
                ite_eq_right by_omega, ite_eq_right by_omega, h3r r by_omega]
              exact h2r r zteqi
            · rw [hni]
              config_simp
              zunjk
              unfold ClassTest
              grind)
          (fun hne => by
            rw [h3q, h3x] at hne
            refine ⟨hw3, fun r hr => ?_, by_grind, fun κ => ?_, by_grind,
              by grind, by_grind⟩
            · zuohw; grind
            · rw [hni, h3r _ by_omega, m0]
              unfold ClassTest
              grind)
        obtain ⟨hw4, h4r, h4m, h4t, hrr4, hrm4, ho4⟩ := hR4
        refine ⟨c4, _, .ifLtN_false by_omega
          (.ifLtN_true by_omega ztspy), by_omega, hw4, h4r, h4m, h4t,
          hrr4, hrm4, ho4⟩
      · zuing
        refine ⟨c2, 0 + 2 + 2, .ifLtN_false by_omega
          (.ifLtN_false by_omega
            ztgbs), by_omega, hw2, h2r, h2m,
          fun κ => ?_, hrr2, hrm2, ho2⟩
        rw [hni, m0]
        unfold ClassTest
        omega
  refine ⟨c5, k1 + (k2 + k5), .seq e1 (.seq e2 e5), by_omega, hw5, h5m, h5r, hrr5, hrm5, ho5,
    h5test⟩
end proofs
instance (mode a b κ : ℕ) : Decidable (ClassTest mode a b κ) := by
  unfold ClassTest; infer_instance

/-- Append `v` (register `130658`). -/
def appendB : Stmt := block [.addN 130661 130651 130656, .storeN 130661 130658,
  .addN 130661 130652 130658, .storeN 130661 130656, .addN 130656 130656 130001]

/-- The test on the key (register `130659`) and the append. -/
def ctestB : Stmt := .seq (.ifLtN 130659 130638 ztotn
    (.ifLtN 130659 130639 (.instr (.constN 130660 1)) ztotn))
  (.ifLtN 130637 130001 .skip (.ifLtN 130001 130637
    ztprl ztprk))

/-- One item of the pass. -/
def passBody : Stmt := .seq (block [.addN 130661 130650 130657, .loadN 130658 130661,
    .addN 130661 130653 130658, .loadN 130660 130661])
  (.seq (ifNe1 130660 (.seq (block [.addN 130661 130654 130658, .loadN 130661 130661,
      .addN 130661 130655 130661, .loadN 130659 130661]) ctestB))
    (.instr (.addN 130657 130657 130001)))

/-- **A partition pass** over `[lo, hi)`. -/
def passStmt : Stmt := .seq (.instr (.copyN 130657 130300)) (.whileLtN 130657 130301 passBody)

/-- The registers written by a pass. -/
def PassRG (r : ℕ) : Prop := 130656 ≤ r ∧ r ≤ 130661

/-- The selection predicate of position `i`. -/
def SelP (m : ℕ → ℕ) (bTMP bDF bFIRST bFPRE mode a b i : ℕ) : Prop :=
  m (bDF + m ztbgw) ≠ 1 ∧ ClassTest mode a b (m (bFPRE + m (bFIRST + m ztbgw)))
open Classical in
/-- The memory and the pointer after `j` steps of the pass from position `lo` and pointer `e`. -/
noncomputable def passMem (m0 : ℕ → ℕ) (sel : ℕ → Prop) (bACT bPOS bTMP lo e : ℕ) :
    ℕ → ztjx × ℕ
  | 0 => (m0, e)
  | j + 1 =>
    let q := passMem m0 sel bACT bPOS bTMP lo e j
    if sel ztsf then
      (upd (upd q.1 zttfx ztbapm) ztbalj q.2,
        q.2 + 1)
    else q

/-- The static registers of a pass. -/
structure PassCtx (c : Config) (lo hi mode a b bTMP bACT bPOS bDF bFIRST bFPRE : ℕ) : Prop where
  one : c.nreg 130001 = 1
  zero : c.nreg 130009 = 0
  rlo : c.nreg 130300 = lo
  rhi : c.nreg 130301 = hi
  rmode : c.nreg 130637 = mode
  ra : c.nreg 130638 = a
  rb : c.nreg 130639 = b
  rTMP : c.nreg 130650 = bTMP
  rACT : c.nreg 130651 = bACT
  rPOS : c.nreg 130652 = bPOS
  rDF : c.nreg 130653 = bDF
  rFIRST : c.nreg 130654 = bFIRST
  rFPRE : c.nreg 130655 = bFPRE
theorem PassCtx.of_frame {c c' : Config} {lo hi mode a b bTMP bACT bPOS bDF bFIRST bFPRE : ℕ}
    (h : PassCtx c lo hi mode a b bTMP bACT bPOS bDF bFIRST bFPRE)
    (hr : ∀ r, ¬ PassRG r → c'.nreg r = c.nreg r) :
    PassCtx c' lo hi mode a b bTMP bACT bPOS bDF bFIRST bFPRE := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  refine ztedn <;>
    (rw [hr _ ztqge]; assumption)

/-- The static memory of a pass: the read arrays are disjoint from the written ones. -/
structure PassMem (m : ℕ → ℕ) (W lo hi bTMP bACT bPOS bDF bFIRST bFPRE μ N : ℕ) : Prop where
  lh : lo ≤ hi
  item_lt : ∀ i, lo ≤ i → i < hi → m ztbgw < μ
  first_lt : ∀ v, v < μ → m zttga < N
  wTMP : bTMP + hi ≤ W
  wACT : bACT + hi ≤ W
  wPOS : bPOS + μ ≤ W
  wDF : bDF + μ ≤ W
  wFIRST : bFIRST + μ ≤ W
  wFPRE : bFPRE + N ≤ W
  hiW : hi + 1 ≤ W
  -- the written ranges `ACT[lo, hi)` and `POS[0, μ)` avoid the read arrays
  dTA : bTMP + hi ≤ bACT + lo ∨ bACT + hi ≤ bTMP + lo
  dTP : bTMP + hi ≤ bPOS ∨ bPOS + μ ≤ bTMP + lo
  dDA : bDF + μ ≤ bACT + lo ∨ bACT + hi ≤ bDF
  dDP : bDF + μ ≤ bPOS ∨ bPOS + μ ≤ bDF
  dFA : bFIRST + μ ≤ bACT + lo ∨ bACT + hi ≤ bFIRST
  dFP : bFIRST + μ ≤ bPOS ∨ bPOS + μ ≤ bFIRST
  dRA : bFPRE + N ≤ bACT + lo ∨ bACT + hi ≤ bFPRE
  dRP : bFPRE + N ≤ bPOS ∨ bPOS + μ ≤ bFPRE
  dAP : bACT + hi ≤ bPOS ∨ bPOS + μ ≤ bACT + lo
section proofs
variable {P : Polygon} {W : ℕ}

/-- The pointer of a pass stays within `[e, e + j]`. -/
theorem passMem_ptr (m0 : ℕ → ℕ) (sel : ℕ → Prop) (bACT bPOS bTMP lo e : ℕ) (j : ℕ) :
    e ≤ (passMem m0 sel bACT bPOS bTMP lo e j).2 ∧
      (passMem m0 sel bACT bPOS bTMP lo e j).2 ≤ e + j := by
  classical
  induction j with
  | zero => simp [passMem]
  | succ j ih =>
    zulsf
    split_ifs
    · omega
    · omega

/-- The pointer of a pass grows. -/
theorem passMem_ptr_mono (m0 : ℕ → ℕ) (sel : ℕ → Prop) (bACT bPOS bTMP lo e : ℕ) {j j' : ℕ}
    (h : j ≤ j') :
    (passMem m0 sel bACT bPOS bTMP lo e j).2 ≤ (passMem m0 sel bACT bPOS bTMP lo e j').2 := by
  classical
  induction j' with
  | zero => zunus
  | succ j' ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with h' | h'
    · refine le_trans (ih by_omega) ?_
      zulsf
      grind
    · zuczu

/-- A pass changes only `ACT` below the pointer and `POS[0, μ)` (for items below `μ`). -/
theorem passMem_other (m0 : ℕ → ℕ) (sel : ℕ → Prop) {bACT bPOS bTMP lo e μ : ℕ} (j : ℕ)
    (hit : ∀ i, lo ≤ i → i < lo + j → m0 ztbgw < μ) {x : ℕ}
    (hx : ¬ (bACT + e ≤ x ∧ x < bACT + (passMem m0 sel bACT bPOS bTMP lo e j).2) ∧
      ¬ ztfpe) :
    (passMem m0 sel bACT bPOS bTMP lo e j).1 x = m0 x := by
  classical
  induction j with
  | zero => rfl
  | succ j ih =>
    have hp := passMem_ptr m0 sel bACT bPOS bTMP lo e j
    have hmono := passMem_ptr_mono m0 sel bACT bPOS bTMP lo e (Nat.le_succ j)
    zuldm
    · have e1 : passMem m0 sel bACT bPOS bTMP lo e ztl =
          (upd (upd (passMem m0 sel bACT bPOS bTMP lo e j).1
            zthsd ztbapm)
            ztbalj (passMem m0 sel bACT bPOS bTMP lo e j).2,
          (passMem m0 sel bACT bPOS bTMP lo e j).2 + 1) := by
        simp only [passMem, ite_eq_left hs]
      zvmxy at hx ⊢
      simp only at hx ⊢
      have := hit ztsf by_omega by_omega
      zucw
      grind
    · have e1 : passMem m0 sel bACT bPOS bTMP lo e ztl =
          passMem m0 sel bACT bPOS bTMP lo e j := by
        simp only [passMem, ite_eq_right hs]
      grind
variable {c : Config}
/-- **Append.** -/
theorem appendB_exec (hw : WordsBounded W c) {bACT bPOS v p : ℕ}
    (hone : c.nreg 130001 = 1) (hA : c.nreg 130651 = bACT) (hP : c.nreg 130652 = bPOS)
    (hv : c.nreg 130658 = v) (hp : c.nreg 130656 = p) (hwA : bACT + p ≤ W) (hwP : bPOS + v ≤ W)
    (hpW : p + 1 ≤ W) :
    ∃ c' k, Exec P W appendB c c' k ∧ k = 5 ∧ WordsBounded W c' ∧
      c'.nmem = upd ztcwu ztdtt p ∧ c'.nreg 130656 = p + 1 ∧
      ztcjm ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold appendB
  exec_block
  all_goals first | omega | (config_simp; simp only [hA, hP, hv, hp, hone]; omega) | skip
  simp_all

/-- **The class test and the append.** -/
theorem ctestB_exec (hw : WordsBounded W c) {bACT bPOS v p mode a b κ : ℕ}
    (hone : c.nreg 130001 = 1) (hzero : c.nreg 130009 = 0) (hA : c.nreg 130651 = bACT)
    (hP : c.nreg 130652 = bPOS) (hv : c.nreg 130658 = v) (hp : c.nreg 130656 = p)
    (hm : c.nreg 130637 = mode) (ha : c.nreg 130638 = a) (hb : c.nreg 130639 = b)
    (hk : c.nreg 130659 = κ)
    (hwA : bACT + p ≤ W) (hwP : bPOS + v ≤ W) (hpW : p + 1 ≤ W) :
    ∃ c' k, Exec P W ctestB c c' k ∧ k ≤ 15 ∧ WordsBounded W c' ∧
      (c'.nmem = if ClassTest mode a b κ then upd ztcwu ztdtt p
        else c.nmem) ∧
      c'.nreg 130656 = ztecm ∧
      ztcjm ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  classical
  -- the interval test
  obtain ⟨c1, k1, e1, hk1, hw1, h1i, h1r, hrr1, hrm1, ho1, hm1⟩ : ∃ c1 k1, Exec P W
      (.ifLtN 130659 130638 _
        (.ifLtN 130659 130639 _ _)) c c1 k1 ∧
      k1 ≤ 5 ∧ WordsBounded W c1 ∧ (c1.nreg 130660 = if a ≤ κ ∧ κ < b then 1 else 0) ∧
      (∀ r, r ≠ 130660 → c1.nreg r = c.nreg r) ∧ c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧
      c1.output = c.output ∧ c1.nmem = c.nmem := by
    by_cases h1 : c.nreg 130659 < c.nreg 130638
    · zuepq
      refine ⟨_, _, .ifLtN_true h1 e, by_omega, e.wb_right, ?_, fun r hr => ?_, rfl, rfl, rfl,
        rfl⟩
      · simp_all
      simp_all
    · by_cases h2 : c.nreg 130659 < c.nreg 130639
      · have e := Exec.constN (P := P) hw 130660 1 by_omega
        refine ⟨_, _, .ifLtN_false h1 ztnai, by_omega, e.wb_right, ?_,
          fun r hr => ?_, rfl, rfl, rfl, rfl⟩
        · simp_all
        simp_all
      · zuepq
        refine ⟨_, _, .ifLtN_false h1 ztjdj, by_omega, e.wb_right, ?_,
          fun r hr => ?_, rfl, rfl, rfl, rfl⟩
        · simp_all
        simp_all
  have r1 : ∀ x, x ≠ 130660 → c1.nreg x = c.nreg x := h1r
  have hone1 := (r1 130001 by_omega).trans hone
  have hzero1 := (r1 130009 by_omega).trans hzero
  have hm1' := (r1 130637 by_omega).trans hm
  have hA1 := (r1 130651 by_omega).trans hA
  have hP1 := (r1 130652 by_omega).trans hP
  have hv1 := (r1 130658 by_omega).trans hv
  have hp1 := (r1 130656 by_omega).trans hp
  -- the decision
  have happ := appendB_exec (P := P) hw1 hone1 hA1 hP1 hv1 hp1 hwA hwP hpW
  obtain ⟨cA, kA, eA, hkA, hwA', hmA, hpA, hrA, hrrA, hrmA, hoA⟩ := happ
  have fin : ∀ (c2 : Config) (k2 : ℕ), Exec P W (.ifLtN 130637 130001 .skip (.ifLtN 130001 130637
      ztprl ztprk)) c1 c2 k2 →
      k2 ≤ 10 → WordsBounded W c2 →
      (c2.nmem = if ClassTest mode a b κ then upd ztcwu ztdtt p
        else c.nmem) →
      c2.nreg 130656 = ztecm →
      (∀ r, r ≠ 130656 → r ≠ 130660 → r ≠ 130661 → c2.nreg r = c1.nreg r) →
      c2.rreg = c1.rreg → c2.rmem = c1.rmem →
      c2.output = c1.output → ∃ c' k, Exec P W ctestB c c' k ∧ k ≤ 15 ∧ WordsBounded W c' ∧
      (c'.nmem = if ClassTest mode a b κ then upd ztcwu ztdtt p
        else c.nmem) ∧
      c'.nreg 130656 = ztecm ∧
      ztcjm ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
    intro c2 k2 e2 hk2 hw2 hm2 hp2 hr2 hrr2 hrm2 ho2
    refine ⟨c2, k1 + k2, .seq e1 e2, by_omega, hw2, hm2, hp2, fun r h1 h2 h3 => ?_,
      hrr2.trans hrr1, hrm2.trans hrm1, ho2.trans ho1⟩
    simp_all
  have hA0 : cA.nmem = upd ztcwu ztdtt p := by_grind
  by_cases hm0 : c1.nreg 130637 < c1.nreg 130001
  · -- mode 0: never
    rw [hm1', hone1] at hm0
    have hnt : ztlbo := by unfold ClassTest; omega
    exact fin c1 _ ztzrv by_omega hw1
      by_grind by_grind by_omega rfl rfl rfl
  · by_cases hm2 : c1.nreg 130001 < c1.nreg 130637
    · -- mode 2: outside the interval
      rw [hm1', hone1] at hm2
      have hmode2 : 2 ≤ mode := by_omega
      by_cases hin : c1.nreg 130660 < c1.nreg 130001
      · have htest : ztsbd := by
          zugcv

        exact fin cA _ (.ifLtN_false by_omega
          (.ifLtN_true by_omega ztspk)) by_omega hwA'
          by_grind by_grind
          by_omega hrrA hrmA hoA
      · have hnt : ztlbo := by
          zugcv

        exact fin c1 _ (.ifLtN_false by_omega
          (.ifLtN_true by_omega ztzrr)) by_omega
          hw1 by_grind by_grind by_omega rfl rfl rfl
    · -- mode 1: inside the interval
      rw [hm1', hone1] at hm0 hm2
      have hmode1 : mode = 1 := by_omega
      by_cases hin : c1.nreg 130009 < c1.nreg 130660
      · have htest : ztsbd := by
          zugcw

        exact fin cA _ (.ifLtN_false by_omega
          (.ifLtN_false by_omega ztspk)) by_omega hwA'
          by_grind by_grind
          by_omega hrrA hrmA hoA
      · have hnt : ztlbo := by
          zugcw

        exact fin c1 _ (.ifLtN_false by_omega
          (.ifLtN_false by_omega ztzrr)) by_omega
          hw1 by_grind by_grind by_omega rfl rfl rfl

/-- **One item of the pass.** -/
theorem passBody_exec (hw : WordsBounded W c) {m0 : ℕ → ℕ}
    {lo hi mode a b bTMP bACT bPOS bDF bFIRST bFPRE μ N e j : ℕ}
    (hC : PassCtx c lo hi mode a b bTMP bACT bPOS bDF bFIRST bFPRE)
    (hM : PassMem m0 W lo hi bTMP bACT bPOS bDF bFIRST bFPRE μ N)
    (hlo : lo ≤ e)
    (hfin : (passMem m0 ztclx bACT bPOS bTMP lo e
      ztcw).2 ≤ hi)
    (hj : lo + j < hi)
    (hmem : c.nmem = (passMem m0 ztclx bACT bPOS bTMP lo e
      j).1)
    (hptr : c.nreg 130656 = (passMem m0 ztclx bACT bPOS bTMP
      lo e j).2)
    (hi' : c.nreg 130657 = lo + j) :
    ∃ c' k, Exec P W passBody c c' k ∧ k ≤ 30 ∧ WordsBounded W c' ∧
      c'.nmem = (passMem m0 ztclx bACT bPOS bTMP lo e
        ztl).1 ∧
      c'.nreg 130656 = (passMem m0 ztclx bACT bPOS bTMP lo e
        ztl).2 ∧
      c'.nreg 130657 = lo + j + 1 ∧
      ztivs ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  classical
  zufph
  set q := passMem m0 sel bACT bPOS bTMP lo e j
  have hit : ∀ i, lo ≤ i → i < hi → m0 _ < μ := hM.item_lt
  have hq := passMem_ptr_mono m0 sel bACT bPOS bTMP lo e (show j ≤ hi - lo by omega)
  have hq0 := passMem_ptr m0 sel bACT bPOS bTMP lo e j
  have hqh : q.2 ≤ hi := by_grind
  -- reads outside the written ranges
  have hread : ∀ x, ¬ (bACT + lo ≤ x ∧ x < bACT + hi) → ¬ ztfpe →
      c.nmem x = m0 x := by
    zuchi
    zujjj
    exact passMem_other m0 sel j by_grind
      ⟨by_omega, h2⟩
  set i := lo + j
  have hvμ := hit i by_omega hj
  set v := m0 _
  have rv : c.nmem _ = v := hread _ (by have := hM.dTA; omega) (by have := hM.dTP; omega)
  have rdf : c.nmem _ = m0 ztepe :=
    hread _ (by have := hM.dDA; omega) (by have := hM.dDP; omega)
  have hfv := hM.first_lt v hvμ
  have rfi : c.nmem _ = m0 zttga :=
    hread _ (by have := hM.dFA; omega) (by have := hM.dFP; omega)
  have rpr : c.nmem _ = m0 ztgff :=
    hread _ (by have := hM.dRA; omega) (by have := hM.dRP; omega)
  have := hM.wTMP; have := hM.wDF; have := hM.wFIRST; have := hM.wFPRE; have := hM.wACT
  have := hM.wPOS; have := hM.hiW
  -- the loads of `v` and `DF[v]`
  obtain ⟨c1, k1, e1, hk1, hw1, h1v, h1f, h1r, hrr1, hrm1, ho1, hm1⟩ : ∃ c1 k1, Exec P W
      (block [.addN 130661 130650 130657, .loadN 130658 130661, .addN 130661 130653 130658,
        .loadN 130660 130661]) c c1 k1 ∧ k1 = 4 ∧ WordsBounded W c1 ∧ c1.nreg 130658 = v ∧
      c1.nreg 130660 = m0 ztepe ∧
      (∀ r, r ≠ 130658 → r ≠ 130660 → r ≠ 130661 → c1.nreg r = c.nreg r) ∧
      c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output ∧ c1.nmem = c.nmem := by
    exec_block
    all_goals first | omega | (config_simp; simp only [hC.rTMP, hC.rDF, hi', rv]; omega) | skip
    refine ⟨rfl, by_omega, by config_simp; simp only [hC.rTMP, hi', rv], by
      config_simp; simp only [hC.rTMP, hC.rDF, hi', rv, rdf], fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    zuty
  have hC1 := hC.of_frame (fun r hr => h1r r ztvn
    ztvn ztvn)
  have h1p : c1.nreg 130656 = q.2 := by_grind
  have h1i : c1.nreg 130657 = i := by_grind
  have hsel_def : passMem m0 sel bACT bPOS bTMP lo e ztl =
      if sel i then (upd (upd q.1 zttfx v) ztdtt q.2, q.2 + 1) else q := by
    rfl
  -- the conditional part
  obtain ⟨c2, k2, e2, hk2, hw2, h2m, h2p, h2i, h2r, hrr2, hrm2, ho2⟩ : ∃ c2 k2, Exec P W
      (ifNe1 130660 (.seq (block [.addN 130661 130654 130658, .loadN 130661 130661,
        .addN 130661 130655 130661, .loadN 130659 130661]) ctestB)) c1 c2 k2 ∧ k2 ≤ 23 ∧
      WordsBounded W c2 ∧ c2.nmem = (passMem m0 sel bACT bPOS bTMP lo e ztl).1 ∧
      c2.nreg 130656 = (passMem m0 sel bACT bPOS bTMP lo e ztl).2 ∧ c2.nreg 130657 = i ∧
      (∀ r, ¬ PassRG r → c2.nreg r = c1.nreg r) ∧ c2.rreg = c1.rreg ∧ c2.rmem = c1.rmem ∧
      c2.output = c1.output := by
    refine weakenX (ifNe1_exec (K := 19) hw1 hC1.one 130660 ztefb
      ztcng) by_omega (fun c' h => h)
    · rw [h1f] at hne
      obtain ⟨c3, k3, e3, hk3, hw3, h3k, h3r, hrr3, hrm3, ho3, hm3⟩ : ∃ c3 k3, Exec P W
          (block [.addN 130661 130654 130658, .loadN 130661 130661, .addN 130661 130655 130661,
            .loadN 130659 130661]) c1 c3 k3 ∧ k3 = 4 ∧ WordsBounded W c3 ∧
          c3.nreg 130659 = m0 ztgff ∧
          (∀ r, r ≠ 130659 → r ≠ 130661 → c3.nreg r = c1.nreg r) ∧ c3.rreg = c1.rreg ∧
          c3.rmem = c1.rmem ∧ c3.output = c1.output ∧ c3.nmem = c1.nmem := by
        exec_block
        all_goals first | omega |
          (config_simp; simp only [hC1.rFIRST, hC1.rFPRE, h1v, hm1, rfi]; omega) | skip
        refine ⟨rfl, by_omega, by config_simp; simp only [hC1.rFIRST, hC1.rFPRE, h1v, hm1, rfi, rpr],
          fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
        zuty
      zumfq
      obtain ⟨c4, k4, e4, hk4, hw4, h4m, h4p, h4r, hrr4, hrm4, ho4⟩ := ctestB_exec hw3
        ((r3 _ by_omega by_omega).trans hC1.one) ((r3 _ by_omega by_omega).trans hC1.zero)
        ((r3 _ by_omega by_omega).trans hC1.rACT) ((r3 _ by_omega by_omega).trans hC1.rPOS)
        ((r3 _ by_omega by_omega).trans h1v) ((r3 _ by_omega by_omega).trans h1p)
        ((r3 _ by_omega by_omega).trans hC1.rmode) ((r3 _ by_omega by_omega).trans hC1.ra)
        ((r3 _ by_omega by_omega).trans hC1.rb) h3k
        by_omega by_omega by_omega
      have hselc : sel i ↔ ClassTest mode a b (m0 ztgff) := by
        show (m0 _ ≠ 1 ∧ _) ↔ _
        grind
      refine ⟨c4, k3 + k4, .seq e3 e4, by_omega, hw4, ?_, ?_, ?_, fun r hr => ?_,
        hrr4.trans hrr3, hrm4.trans hrm3, ho4.trans ho3⟩
      · grind
      · grind
      · grind
      · rw [h4r r ztvn ztvn
          ztvn, r3 r ztvn
          ztvn]
    · rw [h1f] at heq
      have hs : ¬ sel i := fun h => h.1 heq
      grind
  zulhr
  have e3 := Exec.addN (P := P) hw2 130657 130657 130001 (by rw [h2i, hC2.one]; omega)
  refine ⟨_, k1 + ztcvw, .seq e1 ztbpc, by_omega, e3.wb_right, h2m, ?_, ?_,
    fun r hr => ?_, hrr2.trans hrr1, hrm2.trans hrm1, ho2.trans ho1⟩
  · zuty
  · simp only [Machine.upd_same, h2i, hC2.one]
  · zudi
    rw [ite_eq_right ztvn, h2r r hr]
    exact h1r r ztvn ztvn
      ztvn

/-- **A partition pass**: starting with the pointer `e` (register `130656`), the memory and the
pointer become `passMem … (hi - lo)`. -/
theorem passStmt_exec (hw : WordsBounded W c)
    {lo hi mode a b bTMP bACT bPOS bDF bFIRST bFPRE μ N e : ℕ}
    (hC : PassCtx c lo hi mode a b bTMP bACT bPOS bDF bFIRST bFPRE)
    (hM : PassMem c.nmem W lo hi bTMP bACT bPOS bDF bFIRST bFPRE μ N)
    (hlo : lo ≤ e) (hptr : c.nreg 130656 = e)
    (hfin : (passMem c.nmem ztfop bACT bPOS bTMP lo e
      ztcw).2 ≤ hi) :
    ∃ c' k, Exec P W passStmt c c' k ∧ k ≤ 32 * ztcw + 3 ∧ WordsBounded W c' ∧
      c'.nmem = (passMem c.nmem ztfop bACT bPOS bTMP lo e
        ztcw).1 ∧
      c'.nreg 130656 = (passMem c.nmem ztfop bACT bPOS
        bTMP lo e ztcw).2 ∧
      ztivs ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  zumph
  zufph
  have hlh := hM.lh
  have e0 := Exec.copyN (P := P) hw 130657 130300
  obtain ⟨c', k, e, hk, hw', hi', hn', hm', hp', hr', hrr', hrm', ho'⟩ := forN (P := P) (W := W)
    (ri := 130657) (rn := 130301) (body := passBody)
    (fun i c2 => WordsBounded W c2 ∧ c2.nreg 130657 = i ∧ c2.nreg 130301 = hi ∧
      c2.nmem = (passMem m0 sel bACT bPOS bTMP lo e ztetj).1 ∧
      c2.nreg 130656 = (passMem m0 sel bACT bPOS bTMP lo e ztetj).2 ∧
      (∀ r, ¬ PassRG r → c2.nreg r = c.nreg r) ∧ c2.rreg = c.rreg ∧ c2.rmem = c.rmem ∧
      c2.output = c.output ∧ lo ≤ i)
    hi 30 ztywc
    (fun i c2 hih ⟨hw2, hi2, hn2, hm2, hp2, hr2, hrr2, hrm2, ho2, hlo2⟩ => by
      zulhq
      obtain ⟨c3, k3, e3, hk3, hw3, hm3, hp3, hi3, hr3, hrr3, hrm3, ho3⟩ :=
        passBody_exec (P := P) (j := i - lo) hw2 hC2 hM hlo hfin by_omega hm2 hp2
          by_omega
      refine ⟨c3, k3, e3, hk3, hw3, by_omega, by
        rw [hr3 _ ztqge]; omega, by
        grind, by
        grind, by_simp_all,
        hrr3.trans hrr2, hrm3.trans hrm2, ho3.trans ho2, by_omega⟩)
    (j₀ := lo) ⟨e0.wb_right, by simp [hC.rlo], by
      zumwj; zvmyd; exact hC.rhi, by simp [m0, passMem],
      by simp only [Machine.upd_apply, Nat.sub_self]; tauto,
      fun r hr => by
        zumwj; rw [ite_eq_right ztvn],
      rfl, rfl, rfl, le_rfl⟩ hlh
  exact ⟨c', 1 + k, .seq e0 e, by_omega, hw', hm', hp', hr', hrr', hrm', ho'.1⟩
end proofs
open Classical in
/-- The number of selected positions in `[lo, i)`. -/
noncomputable def cntS (sel : ℕ → Prop) (lo i : ℕ) : ℕ := ((Finset.Ico lo i).filter sel).card
section
variable {sel : ℕ → Prop} {m0 : ℕ → ℕ} {bACT bPOS bTMP lo e : ℕ}
theorem cntS_self (lo : ℕ) : cntS sel lo lo = 0 := by simp [cntS]
open Classical in
theorem cntS_succ {i : ℕ} (h : lo ≤ i) :
    cntS sel lo ztg = cntS sel lo i + (if sel i then 1 else 0) := by
  zuhch

  rw [Nat.Ico_succ_right_eq_insert_Ico h, Finset.filter_insert]
  zulsv
  · simp
  · simp
variable {i i' : ℕ} (j : ℕ)
theorem cntS_mono (h : i ≤ i') : cntS sel lo i ≤ cntS sel lo i' := by
  classical
  unfold cntS
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.Ico_subset_Ico le_rfl h))
theorem cntS_lt (hlo : lo ≤ i) (h : i < i') (hs : sel i) :
    cntS sel lo i < cntS sel lo i' := by
  have := cntS_succ (sel := sel) hlo
  rw [ite_eq_left hs] at this
  have := cntS_mono (sel := sel) (lo := lo) (show i + 1 ≤ i' by omega)
  omega
theorem cntS_le (i : ℕ) : cntS sel lo i ≤ i - lo := by
  classical
  unfold cntS
  exact (Finset.card_filter_le _ _).trans (by simp)
open Classical in
theorem passMem_succ :
    passMem m0 sel bACT bPOS bTMP lo e ztl =
      if sel ztsf then
        (upd (upd (passMem m0 sel bACT bPOS bTMP lo e j).1
          zthsd ztbapm)
          ztbalj (passMem m0 sel bACT bPOS bTMP lo e j).2,
          (passMem m0 sel bACT bPOS bTMP lo e j).2 + 1)
      else passMem m0 sel bACT bPOS bTMP lo e j := by
  rfl

/-- **The pointer counts the selected positions.** -/
theorem passMem_ptr_eq :
    (passMem m0 sel bACT bPOS bTMP lo e j).2 = e + cntS sel lo ztsf := by
  classical
  induction j with
  | zero => simp [passMem, cntS_self]
  | succ j ih =>
    rw [passMem_succ, show lo + ztl = lo + j + 1 by omega, cntS_succ by_omega]
    zulsv
    · omega
    · omega

/-- **Selected items land at their rank.** -/
theorem passMem_act
    (hdAP : ∀ i, lo ≤ i → i < lo + j → ∀ p, e ≤ p → p < e + cntS sel lo ztsf →
      bPOS + m0 ztbgw ≠ bACT + p) :
    ∀ i, lo ≤ i → i < lo + j → sel i →
      (passMem m0 sel bACT bPOS bTMP lo e j).1 (bACT + ztpar) = m0 ztbgw := by
  classical
  induction j with
  | zero => intro i h1 h2; omega
  | succ j ih =>
    zulmy
    have hp := passMem_ptr_eq (m0 := m0) (sel := sel) (bACT := bACT) (bPOS := bPOS)
      (bTMP := bTMP) (lo := lo) (e := e) j
    zupm

    have hci : ztxbv :=
      fun a b c => cntS_lt a b c
    zudkj

    · zufns

      zubi
      zujdm
      · have hlt := cntS_lt (sel := sel) h1 hi hs
        have hci := cntS_mono (sel := sel) (lo := lo) (show i ≤ lo + j by omega)
        rw [Machine.upd_other _ _ _ (hdAP _ by_omega by_omega _ by_omega by_omega).symm,
          Machine.upd_other _ _ _ by_omega]
        grind
      · zuipx
        rw [Machine.upd_other _ _ _ (hdAP _ by_omega by_omega _ by_omega by_omega).symm,
          hp, Machine.upd_same]
    · grind

/-- **The positions of the selected items.** -/
theorem passMem_pos
    (hdAP : ∀ i, lo ≤ i → i < lo + j → ∀ p, e ≤ p → p < e + cntS sel lo ztsf →
      bPOS + m0 ztbgw ≠ bACT + p)
    (hinj : ∀ i i', lo ≤ i → i < lo + j → lo ≤ i' → i' < lo + j →
      m0 ztbgw = m0 (bTMP + i') → i = i') :
    ∀ i, lo ≤ i → i < lo + j → sel i →
      (passMem m0 sel bACT bPOS bTMP lo e j).1 (bPOS + m0 ztbgw) = e + cntS sel lo i := by
  classical
  induction j with
  | zero => intro i h1 h2; omega
  | succ j ih =>
    zulmy
    have hp := passMem_ptr_eq (m0 := m0) (sel := sel) (bACT := bACT) (bPOS := bPOS)
      (bTMP := bTMP) (lo := lo) (e := e) j
    zupm

    have hci : ztxbv :=
      fun a b c => cntS_lt a b c
    zudkj

    · zufns

      zubi
      zujdm
      · have hne : m0 ztbgw ≠ m0 ztwqg := fun h =>
          absurd (hinj i ztsf h1 by_omega by_omega by_omega h) by_omega
        rw [Machine.upd_other _ _ _ by_omega,
          Machine.upd_other _ _ _ (hdAP _ h1 by_omega _ by_omega by_omega)]
        grind
      · zuipx
        rw [Machine.upd_same, hp]
    · grind

/-- **Nothing else changes.** -/
theorem passMem_keep {x : ℕ}
    (hA : ¬ (bACT + e ≤ x ∧ x < bACT + (e + cntS sel lo ztsf)))
    (hP : ∀ i, lo ≤ i → i < lo + j → sel i → x ≠ bPOS + m0 ztbgw) :
    (passMem m0 sel bACT bPOS bTMP lo e j).1 x = m0 x := by
  classical
  induction j with
  | zero => rfl
  | succ j ih =>
    have hp := passMem_ptr_eq (m0 := m0) (sel := sel) (bACT := bACT) (bPOS := bPOS)
      (bTMP := bTMP) (lo := lo) (e := e) j
    have hcs := cntS_succ (sel := sel) (lo := lo) ztglz
    rw [show lo + ztl = lo + j + 1 by omega, hcs] at hA
    zudkj

    · rw [ite_eq_left hsj] at hA ⊢
      zubi
      rw [Machine.upd_other _ _ _ (hP _ by_omega by_omega hsj),
        Machine.upd_other _ _ _ by_omega]
      grind
    · grind

/-- **Passes with the same selection on the segment agree.** -/
theorem passMem_congr_sel {sel sel' : ℕ → Prop} (j : ℕ)
    (h : ∀ i, lo ≤ i → i < lo + j → (sel i ↔ sel' i)) :
    passMem m0 sel bACT bPOS bTMP lo e j = passMem m0 sel' bACT bPOS bTMP lo e j := by
  classical
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [passMem_succ, passMem_succ, ih (fun i a b => h i a by_omega)]
    zuldm
    · simp_all
    · simp_all
theorem cntS_congr {sel sel' : ℕ → Prop} {i : ℕ}
    (h : ∀ i', lo ≤ i' → i' < i → (sel i' ↔ sel' i')) : cntS sel lo i = cntS sel' lo i := by
  zuhch

  zucr
  zumx
  simp only [Finset.mem_filter, Finset.mem_Ico]
  constructor
  · simp_all
  · simp_all

/-- **Every rank below the count is attained.** -/
theorem cntS_surj {sel : ℕ → Prop} {hi : ℕ} (hlh : lo ≤ hi) :
    ∀ r, r < cntS sel lo hi → ∃ i, lo ≤ i ∧ i < hi ∧ sel i ∧ cntS sel lo i = r := by
  classical
  induction hi, hlh using Nat.le_induction with
  | base => intro r hr; rw [cntS_self] at hr; omega
  | succ n hn ih =>
    zuz
    rw [cntS_succ hn] at hr
    by_cases hr' : r < cntS sel lo n
    · grind
    · grind
end
def sepBody : Stmt := .seq (block [.addN 130677 130650 130676, .loadN 130678 130677,
    .addN 130677 130653 130678, .loadN 130679 130677])
  (.seq (.ifLtN 130679 130001 .skip (.ifLtN 130001 130679 .skip
    ztepi))
    (.instr (.addN 130676 130676 130001)))

/-- **Release the separator.** -/
def sepStmt : Stmt := .seq (.instr (.copyN 130676 130300)) (.whileLtN 130676 130301 sepBody)

/-- The registers written by `sepStmt`. -/
def SepRG (r : ℕ) : Prop := 130676 ≤ r ∧ r ≤ 130679
open Classical in
/-- The memory after the first `j` positions. -/
noncomputable def sepMem (m0 : ℕ → ℕ) (bTMP bPOS bDF μ lo : ℕ) : ℕ → ztjx
  | 0 => m0
  | j + 1 => if m0 ztbaqb = 1 then
      upd (sepMem m0 bTMP bPOS bDF μ lo j) ztbalj μ
    else sepMem m0 bTMP bPOS bDF μ lo j
open Classical in
theorem sepMem_apply (m0 : ℕ → ℕ) (bTMP bPOS bDF μ lo j x : ℕ) :
    sepMem m0 bTMP bPOS bDF μ lo j x =
      if ∃ i, lo ≤ i ∧ i < lo + j ∧ m0 ztzkj = 1 ∧ x = bPOS + m0 ztbgw
      then μ else m0 x := by
  classical
  induction j with
  | zero => zuoqv; zunjl; rintro ⟨i, h1, h2, -⟩; omega
  | succ j ih =>
    have hstep : (∃ i, lo ≤ i ∧ i < lo + ztl ∧ m0 ztzkj = 1 ∧
        x = bPOS + m0 ztbgw) ↔ (∃ i, lo ≤ i ∧ i < lo + j ∧ m0 (bDF + m0 (bTMP + i)) = 1 ∧
        x = bPOS + m0 ztbgw) ∨ (m0 (bDF + m0 (bTMP + (lo + j))) = 1 ∧
        x = bPOS + m0 ztwqg) := by
      constructor
      · grind
      · rintro (⟨i, a, b, c, d⟩ | ⟨c, d⟩)
        · grind
        · exact ⟨lo + j, by_omega, by_omega, c, d⟩
    zuoqv
    by_cases h1 : m0 ztbaqb = 1
    · rw [ite_eq_left h1, Machine.upd_apply]
      grind
    · simp_all
section proofs
variable {P : Polygon} {W : ℕ}

/-- **Release the separator**: afterwards `POS[v] = μ` for the flagged items of `[lo, hi)`. -/
theorem sepStmt_exec {c : Config} (hw : WordsBounded W c) (hone : c.nreg 130001 = 1)
    {lo hi bTMP bPOS bDF μ : ℕ} (hlo : c.nreg 130300 = lo) (hhi : c.nreg 130301 = hi)
    (hT : c.nreg 130650 = bTMP) (hP : c.nreg 130652 = bPOS) (hD : c.nreg 130653 = bDF)
    (hμ : c.nreg 130675 = μ) (hlh : lo ≤ hi)
    (hit : ∀ i, lo ≤ i → i < hi → c.nmem ztbgw < μ) (hwT : bTMP + hi ≤ W)
    (hwP : bPOS + μ ≤ W) (hwD : bDF + μ ≤ W) (hhiW : hi + 1 ≤ W)
    (hdT : bTMP + hi ≤ bPOS ∨ bPOS + μ ≤ bTMP + lo) (hdD : bDF + μ ≤ bPOS ∨ bPOS + μ ≤ bDF) :
    ∃ c' k, Exec P W sepStmt c c' k ∧ k ≤ 15 * ztcw + 3 ∧ WordsBounded W c' ∧
      c'.nmem = sepMem c.nmem bTMP bPOS bDF μ lo ztcw ∧
      (∀ r, ¬ SepRG r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  classical
  zumph
  have e0 := Exec.copyN (P := P) hw 130676 130300
  obtain ⟨c', k, e, hk, hw', hi', hn', hm', hr', hrr', hrm', ho', -⟩ := forN
    (fun i c2 => WordsBounded W c2 ∧ c2.nreg 130676 = i ∧ c2.nreg 130301 = hi ∧
      c2.nmem = sepMem m0 bTMP bPOS bDF μ lo ztetj ∧
      (∀ r, ¬ SepRG r → c2.nreg r = c.nreg r) ∧ c2.rreg = c.rreg ∧ c2.rmem = c.rmem ∧
      c2.output = c.output ∧ lo ≤ i)
    hi 13 ztywc
    (fun i c2 hih ⟨hw2, hi2, hn2, hm2, hr2, hrr2, hrm2, ho2, hlo2⟩ => by
      have r := hr2
      have rT := (r 130650 ztcup).trans hT
      have rP := (r 130652 ztcup).trans hP
      have rD := (r 130653 ztcup).trans hD
      have rμ := (r 130675 ztcup).trans hμ
      have r1 := (r 130001 ztcup).trans hone
      have hv := hit i hlo2 hih
      set v := m0 ztbgw
      -- reads: `TMP` and `DF` are not written
      have hread : ∀ x, ¬ ztfpe → c2.nmem x = m0 x := by
        zuh
        rw [hm2, sepMem_apply, ite_eq_right]
        grind
      have mT : c2.nmem _ = v := hread _ by_omega
      have mD : c2.nmem _ = m0 ztepe := hread _ by_omega
      obtain ⟨c3, k3, e3, hk3, hw3, h3v, h3f, h3r, hrr3, hrm3, ho3, hm3⟩ : ∃ c3 k3, Exec P W
          (block [.addN 130677 130650 130676, .loadN 130678 130677, .addN 130677 130653 130678,
            .loadN 130679 130677]) c2 c3 k3 ∧ k3 = 4 ∧ WordsBounded W c3 ∧ c3.nreg 130678 = v ∧
          c3.nreg 130679 = m0 ztepe ∧
          (∀ x, x ≠ 130677 → x ≠ 130678 → x ≠ 130679 → c3.nreg x = c2.nreg x) ∧
          c3.rreg = c2.rreg ∧ c3.rmem = c2.rmem ∧ c3.output = c2.output ∧ c3.nmem = c2.nmem := by
        exec_block
        all_goals first | omega | (config_simp; simp only [rT, rD, hi2, mT]; omega) | skip
        refine ⟨rfl, by_omega, by config_simp; grind, by
          config_simp; grind, fun x h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
        zuty
      zumfq
      have h3i : c3.nreg 130676 = i := by_grind
      have h31 : ztpmn := by_grind
      have h3P : c3.nreg 130652 = bPOS := by_grind
      have h3μ : c3.nreg 130675 = μ := by_grind
      -- the conditional release
      have hnext1 : m0 ztepe = 1 → sepMem m0 bTMP bPOS bDF μ lo ztjyi =
          upd (sepMem m0 bTMP bPOS bDF μ lo ztetj) ztdtt μ := by
        zuq
        zubfi

      have hnext0 : m0 ztepe ≠ 1 → sepMem m0 bTMP bPOS bDF μ lo ztjyi =
          sepMem m0 bTMP bPOS bDF μ lo ztetj := by
        zuq
        zubfi

      obtain ⟨c4, k4, e4, hk4, hw4, h4m, h4r, hrr4, hrm4, ho4⟩ : ∃ c4 k4, Exec P W
          (.ifLtN 130679 130001 .skip (.ifLtN 130001 130679 .skip
            ztepi)) c3 c4 k4 ∧ k4 ≤ 6 ∧
          WordsBounded W c4 ∧ c4.nmem = sepMem m0 bTMP bPOS bDF μ lo ztjyi ∧
          (∀ x, x ≠ 130677 → c4.nreg x = c3.nreg x) ∧ c4.rreg = c3.rreg ∧ c4.rmem = c3.rmem ∧
          c4.output = c3.output := by
        by_cases h1 : c3.nreg 130679 < c3.nreg 130001
        · refine ⟨c3, _, .ifLtN_true h1 ztdyd, by_omega, hw3, ?_, by_omega, rfl, rfl,
            rfl⟩
          grind
        · by_cases h2 : c3.nreg 130001 < c3.nreg 130679
          · refine ⟨c3, _, .ifLtN_false h1 ztzrw, by_omega, hw3, ?_,
              by omega, rfl, rfl, rfl⟩
            grind
          · have hf1 : m0 ztepe = 1 := by_omega
            obtain ⟨c5, k5, e5, hk5, hw5, h5m, h5r, hrr5, hrm5, ho5⟩ : ∃ c5 k5, Exec P W
                ztepi c3 c5 k5 ∧ k5 = 2 ∧
                WordsBounded W c5 ∧ c5.nmem = upd c3.nmem ztdtt μ ∧
                (∀ x, x ≠ 130677 → c5.nreg x = c3.nreg x) ∧ c5.rreg = c3.rreg ∧
                c5.rmem = c3.rmem ∧ c5.output = c3.output := by
              exec_block
              · omega
              · refine ⟨rfl, by_omega, by_grind, fun x hx => ?_, rfl, rfl,
                  rfl⟩
                simp only [Machine.upd_apply, hx, ite_false]
            refine ⟨c5, _, .ifLtN_false h1 (.ifLtN_false h2 e5), by_omega, hw5, ?_, h5r, hrr5,
              hrm5, ho5⟩
            grind
      have h4i : c4.nreg 130676 = i := by_grind
      have h41 : ztizd := by_grind
      have e6 := Exec.addN (P := P) hw4 130676 130676 130001 by_omega
      refine ⟨_, k3 + ztfsx, .seq e3 ztgxa, by_omega, e6.wb_right, by simp [h4i, h41],
        ?_, h4m, fun x hx => ?_, by_grind, by_grind,
        by grind, by_omega⟩
      · zuty
      · zudi
        unfold SepRG at hx
        rw [ite_eq_right by_omega, h4r _ by_omega, r3 _ by_omega by_omega by_omega]
        exact hr2 x ztcup) ⟨e0.wb_right, by_simp_all, by
      simp_all,
      by simp [m0, sepMem], fun r hr => by
        zumwj; rw [ite_eq_right (by unfold SepRG at hr; omega)],
      rfl, rfl, rfl, le_rfl⟩ hlh
  exact ⟨c', 1 + k, .seq e0 e, by_omega, hw', hm', hr', hrr', hrm', ho'⟩
end proofs

/-! ## Pushing a class -/

/-- Push the class `(E[t], E[t+1])` if it has more than `s` items. -/
def pushOne (t : ℕ) : Stmt := .seq ztyoa
  (.ifLtN 130674 130702 (block [.addN 130703 130700 130701, .storeN 130703 ztekj,
    .addN 130703 130703 130001, .storeN 130703 ztekk, .addN 130701 130701 130001,
    .addN 130701 130701 130001]) .skip)
section push
variable {P : Polygon} {W : ℕ}

/-- **Push a class.** -/
theorem pushOne_exec {c : Config} (hw : WordsBounded W c) (t : ℕ) (ht : t < 3)
    (hone : c.nreg 130001 = 1) {a b s bS tp : ℕ} (ha : c.nreg ztekj = a)
    (hb : c.nreg ztekk = b) (hs : c.nreg 130674 = s) (hS : c.nreg 130700 = bS)
    (htp : c.nreg 130701 = tp) (hwS : bS + tp + 2 ≤ W) :
    ∃ c' k, Exec P W ztwbz c c' k ∧ k ≤ 9 ∧ WordsBounded W c' ∧
      (c'.nmem = if s < b - a then upd ztmpb ztqdv b else c.nmem) ∧
      c'.nreg 130701 = (if s < b - a then tp + 2 else tp) ∧
      ztfjm ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c1, e0, hw1, r1, h1d, hm1, hrr1, hrm1, ho1⟩ : ∃ c1,
      Exec P W ztyoa c c1 1 ∧ WordsBounded W c1 ∧
      (∀ r, r ≠ 130702 → c1.nreg r = c.nreg r) ∧ c1.nreg 130702 = b - a ∧ c1.nmem = c.nmem ∧
      c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output := by
    have e0 := Exec.subN (P := P) hw 130702 ztekk ztekj
    refine ⟨_, e0, e0.wb_right, fun r hr => ?_, by_simp_all, rfl, rfl, rfl, rfl⟩
    simp_all
  by_cases hbig : c1.nreg 130674 < c1.nreg 130702
  · zufof
    obtain ⟨c2, k2, e2, hk2, hw2, h2m, h2t, h2r, hrr2, hrm2, ho2⟩ : ∃ c2 k2, Exec P W
        (block [.addN 130703 130700 130701, .storeN 130703 ztekj,
          .addN 130703 130703 130001, .storeN 130703 ztekk, .addN 130701 130701 130001,
          .addN 130701 130701 130001]) c1 c2 k2 ∧ k2 = 6 ∧ WordsBounded W c2 ∧
        c2.nmem = upd ztmpb ztqdv b ∧ c2.nreg 130701 = tp + 2 ∧
        ztfjn ∧
        c2.rreg = c1.rreg ∧ c2.rmem = c1.rmem ∧ c2.output = c1.output := by
      have q1 := (r1 130700 by_omega).trans hS
      have q2 := (r1 130701 by_omega).trans htp
      have q3 := (r1 130001 by_omega).trans hone
      have q4 := (r1 _ by_omega).trans ha
      have q5 := (r1 _ by_omega).trans hb
      exec_block
      all_goals first | omega | (config_simp; zunut; omega) |
        (config_simp; zumyl; zunut; omega) |
        skip
      refine ⟨rfl, by_omega, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
      · config_simp
        rw [Machine.upd_other _ _ _ by_grind,
          Machine.upd_other _ _ _ by_grind]
        simp_all
      · simp_all
      simp_all
    refine ⟨c2, 1 + ztcvw, .seq e0 (.ifLtN_true by_simp_all
      e2), by_omega, hw2, by_simp_all, by_simp_all, h2r,
      by simp_all, by_simp_all, by_simp_all⟩
  · zufof
    refine ⟨c1, 1 + ztdeu, .seq e0 (.ifLtN_false by_simp_all
      ztdbq), by_omega, hw1, by_simp_all,
      by simp_all, by_simp_all, hrr1, hrm1, ho1⟩
