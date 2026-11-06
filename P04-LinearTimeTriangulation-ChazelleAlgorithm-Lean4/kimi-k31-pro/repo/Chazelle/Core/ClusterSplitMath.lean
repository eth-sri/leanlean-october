module

public import Chazelle.Core.ClusterStarSep
public import Chazelle.Core.ClusterMedian
public import Chazelle.Core.ClusterStack
public import Chazelle.Rwx

/-!
# WP-I, part 20: the split of a piece, in the terms of the RAM

The RAM splits a piece `P` (the items of a segment `[lo, hi)` of the array `act`) at the
centroid face `f` of the star map, found by the climb in the preorder tree `R` of a rooted
cotree `C`.  Here the RAM's tests are identified with the mathematics of
`ClusterCentroid.lean` / `ClusterStarSep.lean`:

* `enc`: star darts as numbers (`inl d ↦ d`, `inr (inl d) ↦ N + d`, `inr (inr d) ↦ 2N + d`);
* `isDesc_iff_anc`: descendants in `C` are descendants in `R` when the parents agree;
* `inClass`: the class test of the RAM for a star dart of `f` (down to a child face, up to the
  parent face, or empty) and `inClass_iff`: it is membership in the side `cross` of the
  fundamental cycle of that dart, for non-tree darts, and false for tree darts;
* `good_iff`: the RAM's good test `GdN` is `Good` of `ClusterCentroid.lean`;
* `split_math`: the three classes of `P` off the marked set (the `T`-ancestors in `P` of the
  corners of `f`) cover `P` off the marks, are disjoint, have at most `|P| / 2` items each and
  are not joined by edges; the marks are at most `3k` when `P` lies in `k` consecutive levels.
-/

namespace Chazelle.Core.Cluster

open Chazelle.Separator Chazelle.Separator.CombMap Equiv

@[expose] public section

/-- The number of a star dart. -/
def enc (N : ℕ) : Fin N ⊕ Fin N ⊕ Fin N → ℕ
  | .inl d => d
  | .inr (.inl d) => N + d
  | .inr (.inr d) => 2 * N + d

theorem enc_lt {N : ℕ} (x : Fin N ⊕ Fin N ⊕ Fin N) : enc N x < 3 * N := by
  rcases x with d | d | d <;> simp only [enc] <;> omega

theorem enc_inj {N : ℕ} {x y : Fin N ⊕ Fin N ⊕ Fin N} (h : enc N x = enc N y) : x = y := by
  rcases x with d | d | d <;> rcases y with e | e | e <;> simp only [enc] at h <;>
    first | (congr 1; exact Fin.ext (by omega)) | (congr 2; exact Fin.ext (by omega)) |
      (exfalso; omega)

@[simp] theorem enc_inl {N : ℕ} (d : Fin N) : enc N (.inl d) = d := rfl
@[simp] theorem enc_inl_inr {N : ℕ} (d : Fin N) : enc N (.inr (.inl d)) = N + d := rfl
@[simp] theorem enc_inr_inr {N : ℕ} (d : Fin N) : enc N (.inr (.inr d)) = 2 * N + d := rfl

/-- The class test of the RAM for the star dart `X` of the face `f`, at the key `κ`. -/
def inClass (sopp sface fparN pre sz : ℕ → ℕ) (r0 X f κ : ℕ) : Prop :=
  if sface (sopp X) ≠ r0 ∧ fparN (sface (sopp X)) = X then
    pre (sface (sopp X)) ≤ κ ∧ κ < pre (sface (sopp X)) + sz (sface (sopp X))
  else if f ≠ r0 ∧ sopp (fparN f) = X then ¬ (pre f ≤ κ ∧ κ < pre f + sz f) else False

variable {μ N : ℕ} {F : Type} [Fintype F] [DecidableEq F] {M : CombMap (Fin μ) F (Fin N)}
  {T : SpanTree M} {a : F → Fin N} {ha : ∀ g, M.face (a g) = g}
  {C : CoTree (starTree T a ha)} {R : BTree}

/-- Descendants in the cotree are descendants in the preorder tree. -/
theorem isDesc_iff_anc (hup : ∀ g : Fin N, R.up g = (C.parent g : ℕ)) (h g : Fin N) :
    C.IsDesc h g ↔ R.Anc g h := by
  have hit : ∀ n (x : Fin N), R.up^[n] x = ((C.parent^[n] x : Fin N) : ℕ) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← ih, hup]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [hit, hn]⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, Fin.ext (by rw [← hit, hn])⟩

/-- **The class test is the side of the fundamental cycle.** -/
theorem inClass_iff (hM : M.Planar) {sopp sface fparN pre sz : ℕ → ℕ} {r0 : ℕ}
    (hsopp : ∀ x, sopp (enc N x) = enc N ((star M).opp x))
    (hsface : ∀ x, sface (enc N x) = ((star M).face x : ℕ))
    (hr0 : r0 = (C.r0 : ℕ))
    (hfpar : ∀ g : Fin N, g ≠ C.r0 → fparN g = enc N (C.fpar g))
    (hint : ∀ g h : Fin N, C.IsDesc h g ↔ pre g ≤ pre h ∧ pre h < pre g + sz g)
    {f : Fin N} {x : Fin N ⊕ Fin N ⊕ Fin N} (hx : (star M).face x = f) (h : Fin N) :
    inClass sopp sface fparN pre sz r0 (enc N x) f (pre h) ↔
      x ∈ (starTree T a ha).coDarts ∧ h ∈ (starTree T a ha).cross x := by
  have hSM  := star_planar M hM
  set gF : Fin N := (star M).face ((star M).opp x) with hgF
  have hg : sface (sopp (enc N x)) = (gF : ℕ) := by rw [hsopp, hsface]
  have hne : ∀ g : Fin N, (g : ℕ) ≠ r0 ↔ g ≠ C.r0 := by
    intro g; rw [hr0]; exact ⟨fun h e => h (by rw [e]), fun h e => h (Fin.ext e)⟩
  unfold inClass
  rw [hg]
  by_cases hd : (gF : ℕ) ≠ r0 ∧ fparN gF = enc N x
  · rw [ite_eq_left hd]
    have hg0  := (hne gF).mp hd.1
    have hfx : C.fpar gF = x := enc_inj (by rw [← hfpar gF hg0]; exact hd.2)
    rw [← hfx, C.cross_fpar hSM hg0, hint]
    exact ⟨fun h => ⟨C.mem gF hg0, h⟩, fun h => h.2⟩
  · rw [ite_eq_right hd]
    by_cases hu : (f : ℕ) ≠ r0 ∧ sopp (fparN f) = enc N x
    · rw [ite_eq_left hu]
      have hf0  := (hne f).mp hu.1
      have hfx : (star M).opp (C.fpar f) = x := by
        apply enc_inj
        rw [← hsopp, ← hfpar f hf0]; exact hu.2
      rw [← hfx, C.cross_opp_fpar hSM hf0, hint]
      exact ⟨fun h => ⟨(starTree T a ha).opp_mem_coDarts (C.mem f hf0), h⟩, fun h => h.2⟩
    · rw [ite_eq_right hu]
      simp only [false_iff, not_and]
      intro hco _
      obtain ⟨g', hg', rfl | rfl⟩ := (C.mem_coDarts_iff hSM).mp hco
      · -- a parent dart: the down test holds
        apply hd
        have : gF = g' := C.head g' hg'
        rw [this]
        exact ⟨(hne g').mpr hg', hfpar g' hg'⟩
      · -- the opposite of a parent dart: the up test holds
        apply hu
        have hfg : f = g' := by rw [← hx]; exact C.head g' hg'
        subst hfg
        exact ⟨(hne _).mpr hg', by rw [hfpar _ hg', hsopp]⟩

/-- The vertex choice of the star map: the old dart `first v` at a real vertex, the spoke of
`a g` at a centre. -/
def delta (first : Fin μ → Fin N) (a : F → Fin N) : Fin μ ⊕ F → Fin N ⊕ Fin N ⊕ Fin N
  | .inl v => .inl (first v)
  | .inr g => .inr (.inl (a g))

omit [Fintype F] [DecidableEq F] in
theorem delta_vert {first : Fin μ → Fin N} (hfirst : ∀ v, M.vert (first v) = v)
    (ha' : ∀ g, M.face (a g) = g) (x : Fin μ ⊕ F) :
    (star M).vert (delta first a x) = x := by
  rcases x with v | g
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
    exact ⟨v, rfl, (@Finset.mem_filter _ _ (Classical.decPred _) _ _).mp hv |>.2⟩
  · rintro ⟨v, rfl, hv⟩
    exact ⟨v, (@Finset.mem_filter _ _ (Classical.decPred _) _ _).mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩

omit [Fintype F] [DecidableEq F] in
theorem card_liftP {P : Finset ℕ} (hP : ∀ v ∈ P, v < μ) : (liftP (μ := μ)
    (F := F) P).card = P.card := by
  classical
  unfold liftP
  rw [Finset.card_map]
  have : P = (@Finset.filter _ (fun v : Fin μ => (v : ℕ) ∈ P) (Classical.decPred _)
      Finset.univ).map Fin.valEmbedding := by
    ext v
    simp only [Finset.mem_map, Fin.valEmbedding_apply]
    constructor
    · intro hv
      exact ⟨⟨v, hP v hv⟩, (@Finset.mem_filter _ _ (Classical.decPred _) _ _).mpr
        ⟨Finset.mem_univ _, hv⟩, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ((@Finset.mem_filter _ _ (Classical.decPred _) _ _).mp hw).2
  conv_rhs => rw [this]
  rw [Finset.card_map]

omit [Fintype F] [DecidableEq F] in
/-- Counting a predicate of lifted vertices. -/
theorem card_filter_liftP {P : Finset ℕ} (hP : ∀ v ∈ P, v < μ) (Q : Fin μ ⊕ F → Prop)
    [DecidablePred Q] (Q' : ℕ → Prop) [DecidablePred Q']
    (hQ : ∀ v : Fin μ, (v : ℕ) ∈ P → (Q (.inl v) ↔ Q' v)) :
    ((liftP (μ := μ) (F := F) P).filter Q).card = (P.filter Q').card := by
  have hP' : ∀ v ∈ P.filter Q', v < μ := fun v hv => hP v (Finset.mem_filter.mp hv).1
  rw [← card_liftP (μ := μ) (F := F) hP']
  congr 1
  ext x
  rw [Finset.mem_filter, mem_liftP, mem_liftP]
  constructor
  · rintro ⟨⟨v, rfl, hv⟩, hq⟩
    exact ⟨v, rfl, Finset.mem_filter.mpr ⟨hv, (hQ v hv).mp hq⟩⟩
  · rintro ⟨v, rfl, hv⟩
    obtain ⟨hv1, hv2⟩ := Finset.mem_filter.mp hv
    exact ⟨⟨v, rfl, hv1⟩, (hQ v hv1).mpr hv2⟩

/-- Positions of a segment and its items. -/
theorem card_items_filter {act : ℕ → ℕ} {lo hi : ℕ}
    (hinj : Set.InjOn act (Finset.Ico lo hi)) (Q : ℕ → Prop) [DecidablePred Q] :
    ((items act (lo, hi)).filter Q).card = ((Finset.Ico lo hi).filter (fun i => Q (act i))).card := by
  unfold items
  simp only
  rw [Finset.filter_image, Finset.card_image_of_injOn]
  intro x hx y hy hxy
  exact hinj (Finset.mem_coe.mpr (Finset.mem_filter.mp hx).1)
    (Finset.mem_coe.mpr (Finset.mem_filter.mp hy).1) hxy

/-- **The good test is `Good`.** -/
theorem good_iff {first : Fin μ → Fin N} {firstN : ℕ → ℕ}
    (hfN : ∀ v : Fin μ, firstN v = first v) {pre sz : ℕ → ℕ}
    (hint : ∀ g h : Fin N, C.IsDesc h g ↔ pre g ≤ pre h ∧ pre h < pre g + sz g)
    {act : ℕ → ℕ} {lo hi : ℕ} (hinj : Set.InjOn act (Finset.Ico lo hi))
    (hlt : ∀ v ∈ items act (lo, hi), v < μ) (z : Fin N) :
    Good C (delta first a) (liftP (μ := μ) (F := F) (items act (lo, hi))) z ↔
      BTree.GdN pre sz (fun i => pre (firstN (act i))) lo hi z := by
  classical
  unfold Good cnt BTree.GdN cntIn
  rw [card_liftP hlt, items_card hinj]
  have hc : ((liftP (μ := μ) (F := F) (items act (lo, hi))).filter
      (fun x => C.IsDesc ((star M).face (delta first a x)) z)).card =
      ((Finset.Ico lo hi).filter (fun i => pre z ≤ pre (firstN (act i)) ∧
        pre (firstN (act i)) < pre z + sz z)).card := by
    rw [card_filter_liftP hlt _ (fun v => pre z ≤ pre (firstN v) ∧ pre (firstN v) < pre z + sz z)
      (fun v hv => by
        simp only [delta, star_face, starFace_inl]
        rw [hint, hfN])]
    exact card_items_filter hinj _
  unfold len
  simp only
  rw [← hc]

/-- The marked vertices of the split at `f`: the `T`-ancestors of the three corners of the star
face `f`. -/
def markN (T : SpanTree M) (a : F → Fin N) (f : Fin N) (v : ℕ) : Prop :=
  ∃ h : v < μ, T.IsAnc ⟨v, h⟩ (M.vert f) ∨ T.IsAnc ⟨v, h⟩ (M.head f) ∨
    T.IsAnc ⟨v, h⟩ (M.vert (a (M.face f)))

theorem markN_iff (f : Fin N) (v : Fin μ) :
    markN T a f v ↔ (Sum.inl v : Fin μ ⊕ F) ∈ (starTree T a ha).sepSet f := by
  rw [star_mem_sepSet_inl]
  unfold markN
  constructor
  · rintro ⟨h, hh⟩; exact hh
  · intro hh; exact ⟨v.2, hh⟩

open Classical in
/-- **The split, in the terms of the RAM.**  With the centroid `f` (good, no good child) of the
piece `P = items act (lo, hi)`, the classes `inClass (enc (starDarts f t))` of the unmarked items
cover them, are disjoint, have at most half of the items each and are not joined by an edge;
the marks in a window of `k` levels are at most `3k`. -/
theorem split_math (hM : M.Planar) {first : Fin μ → Fin N} (hfirst : ∀ v, M.vert (first v) = v)
    {firstN : ℕ → ℕ} (hfN : ∀ v : Fin μ, firstN v = first v)
    {sopp sface fparN pre sz : ℕ → ℕ} {r0 : ℕ}
    (hsopp : ∀ x, sopp (enc N x) = enc N ((star M).opp x))
    (hsface : ∀ x, sface (enc N x) = ((star M).face x : ℕ))
    (hr0 : r0 = (C.r0 : ℕ))
    (hfpar : ∀ g : Fin N, g ≠ C.r0 → fparN g = enc N (C.fpar g))
    (hint : ∀ g h : Fin N, C.IsDesc h g ↔ pre g ≤ pre h ∧ pre h < pre g + sz g)
    {act : ℕ → ℕ} {lo hi : ℕ} (hinj : Set.InjOn act (Finset.Ico lo hi))
    (hlt : ∀ v ∈ items act (lo, hi), v < μ) {f : Fin N}
    (hgood : Good C (delta first a) (liftP (μ := μ) (F := F) (items act (lo, hi))) f)
    (hch : ∀ g, g ≠ C.r0 → C.parent g = f →
      ¬ Good C (delta first a) (liftP (μ := μ) (F := F) (items act (lo, hi))) g) :
    (∀ v ∈ items act (lo, hi), ¬ markN T a f v → ∃ t, t < 3 ∧
      inClass sopp sface fparN pre sz r0 (enc N (starDarts (M := M) f t)) f (pre (firstN v))) ∧
    (∀ v ∈ items act (lo, hi), ¬ markN T a f v → ∀ t t', t < 3 → t' < 3 →
      inClass sopp sface fparN pre sz r0 (enc N (starDarts (M := M) f t)) f (pre (firstN v)) →
      inClass sopp sface fparN pre sz r0 (enc N (starDarts (M := M) f t')) f (pre (firstN v)) →
      t = t') ∧
    (∀ t, t < 3 → 2 * ((items act (lo, hi)).filter (fun v => ¬ markN T a f v ∧
      inClass sopp sface fparN pre sz r0 (enc N (starDarts (M := M) f t)) f
        (pre (firstN v)))).card ≤ hi - lo) ∧
    (∀ (d : Fin N) t t', t < 3 → t' < 3 →
      ((M.vert d : ℕ) ∈ items act (lo, hi) ∧ ¬ markN T a f (M.vert d) ∧
        inClass sopp sface fparN pre sz r0 (enc N (starDarts (M := M) f t)) f
          (pre (firstN (M.vert d)))) →
      ((M.head d : ℕ) ∈ items act (lo, hi) ∧ ¬ markN T a f (M.head d) ∧
        inClass sopp sface fparN pre sz r0 (enc N (starDarts (M := M) f t')) f
          (pre (firstN (M.head d)))) → t = t') := by
  set δ := delta (F := F) first a
  set P' := liftP (μ := μ) (F := F) (items act (lo, hi))
  have hSM : (star M).Planar := star_planar M hM
  have hδ := delta_vert (a := a) hfirst ha
  have hx : ∀ e, (star M).face e = f ↔ ∃ t, t < 3 ∧ starDarts (M := M) f t = e :=
    fun e => star_face_iff f e
  have hxinj : ∀ t t', t < 3 → t' < 3 → starDarts (M := M) f t = starDarts (M := M) f t' →
      t = t' := fun t t' ht ht' h => starDarts_inj f ht ht' h
  obtain ⟨hcov, huniq, hedge⟩ := split_classes (T := starTree T a ha) hSM hδ (P := P') hx hxinj
  -- the class test at a real vertex
  have hic : ∀ (v : Fin μ) t, t < 3 →
      (inClass sopp sface fparN pre sz r0 (enc N (starDarts (M := M) f t)) f (pre (firstN v)) ↔
        starDarts (M := M) f t ∈ (starTree T a ha).coDarts ∧ (star M).face (δ (.inl v)) ∈ (starTree T a ha).cross
          (starDarts (M := M) f t)) := by
    intro v t ht
    have hft : (star M).face (starDarts (M := M) f t) = f := (hx _).mpr ⟨t, ht, rfl⟩
    rw [hfN]
    exact inClass_iff hM hsopp hsface hr0 hfpar hint hft (first v)
  have hmemcls : ∀ (v : Fin μ) t, t < 3 →
      ((.inl v : Fin μ ⊕ F) ∈ cls (starTree T a ha) δ P' f (starDarts (M := M) f) t ↔
        (v : ℕ) ∈ items act (lo, hi) ∧ ¬ markN T a f v ∧
          inClass sopp sface fparN pre sz r0 (enc N (starDarts (M := M) f t)) f
            (pre (firstN v))) := by
    intro v t ht
    rw [mem_cls, hic v t ht, markN_iff (ha := ha)]
    constructor
    · rintro ⟨h1, h2, h3⟩
      obtain ⟨w, hw, hwv⟩ := mem_liftP.mp h1
      cases hw
      exact ⟨hwv, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨mem_liftP.mpr ⟨v, rfl, h1⟩, h2, h3⟩
  refine ⟨fun v hv hm => ?_, fun v hv hm t t' ht ht' h1 h2 => ?_, fun t ht => ?_,
    fun d t t' ht ht' ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ => ?_⟩
  · have hvμ := hlt v hv
    have hm'  := hm
    obtain ⟨t, ht, hvt⟩ := hcov (.inl ⟨v, hvμ⟩) (mem_liftP.mpr ⟨_, rfl, hv⟩)
      (by rwx [← markN_iff (ha := ha)])
    exact ⟨t, ht, ((hmemcls ⟨v, hvμ⟩ t ht).mp hvt).2.2⟩
  · have hvμ := hlt v hv
    exact huniq t t' ht ht' (.inl ⟨v, hvμ⟩) ((hmemcls ⟨v, hvμ⟩ t ht).mpr ⟨hv, hm, h1⟩)
      ((hmemcls ⟨v, hvμ⟩ t' ht').mpr ⟨hv, hm, h2⟩)
  · have hh := cls_half (C := C) hSM hgood hch hx ht
    rw [card_liftP hlt] at hh
    rw [items_card hinj] at hh
    have hc : (cls (starTree T a ha) δ P' f (starDarts (M := M) f) t).card =
        ((items act (lo, hi)).filter (fun v => ¬ markN T a f v ∧
          inClass sopp sface fparN pre sz r0 (enc N (starDarts (M := M) f t)) f
            (pre (firstN v)))).card := by
      have e1 : cls (starTree T a ha) δ P' f (starDarts (M := M) f) t = P'.filter
          (fun x => x ∈ cls (starTree T a ha) δ P' f (starDarts (M := M) f) t) := by
        ext x
        constructor
        · intro hx'
          exact Finset.mem_filter.mpr ⟨(mem_cls.mp hx').1, hx'⟩
        · intro hx'
          exact (Finset.mem_filter.mp hx').2
      rw [e1]
      exact card_filter_liftP hlt _ _ (fun v hv => by
        rw [hmemcls v t ht]; exact ⟨fun h => h.2, fun h => ⟨hv, h⟩⟩)
    rw [← hc]
    unfold len at hh
    simpa using hh
  · have hs := hedge (.inl d) t t' ht ht'
      ((hmemcls (M.vert d) t ht).mpr ⟨a1, a2, a3⟩)
      ((hmemcls (M.head d) t' ht').mpr ⟨b1, b2, b3⟩)
    exact hs

open Classical in
include ha in
/-- **At most `3k` marks in a window of `k` levels.** -/
theorem card_mark_le (f : Fin N) (S : Finset ℕ) (hSμ : ∀ v ∈ S, v < μ) (c j k : ℕ)
    (hS : ∀ v (hv : v ∈ S), j * k ≤ T.level ⟨v, hSμ v hv⟩ + c ∧
      T.level ⟨v, hSμ v hv⟩ + c < j * k + k) :
    (S.filter (fun v => markN T a f v)).card ≤ 3 * k := by
  classical
  set S' : Finset (Fin μ) := Finset.univ.filter (fun v : Fin μ => (v : ℕ) ∈ S)
  have h := star_sep_card T a ha f c j k S' (fun v hv => by
    have hv'  := (Finset.mem_filter.mp hv).2
    exact hS v hv')
  refine le_trans (le_of_eq ?_) h
  rw [← Finset.card_map Fin.valEmbedding]
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_map, Fin.valEmbedding_apply, Finset.mem_univ,
    true_and, S']
  constructor
  · rintro ⟨hv, hm⟩
    refine ⟨⟨v, hSμ v hv⟩, ⟨hv, ?_⟩, rfl⟩
    rwx [← markN_iff (ha := ha)]
  · rintro ⟨w, ⟨hw, hm⟩, rfl⟩
    exact ⟨hw, (markN_iff (ha := ha) f w).mpr hm⟩

end

end Chazelle.Core.Cluster
