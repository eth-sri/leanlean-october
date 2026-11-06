module

public meta import Chazelle.Arithmetic

public import Chazelle.Chain.Chord
public import Chazelle.Visibility.Submap

/-!
# Chord separation in the subchain model (Chazelle's Lemma 2.1)

A *submap* of the chain `C` is a set `S ⊆ chords C`; its free set is `freeOf C S = dom C \ ⋃₀ S`
and its regions `regionsOf C S` are the connected components of the free set.

The main theorem `chord_separates` is Lemma 2.1 in the Euclidean form of
`Chazelle.Visibility.chord_separates`: for `c ∈ S` and a point `z` of `c` in the domain, the
points `z ± (0, ε)` (small `ε > 0`) lie in the free set and in *different* regions.

The proof is uniform for finite chords and box chords.  Every point `q` of the obstacle
`(dom C)ᶜ` that is on the chain, on the slit, or on the perimeter of the box has an *anchor
path*: a polygonal path inside `(dom C)ᶜ` from `q` to the top `slitTop` of the slit
(`exists_anchor`).  For a chord `c = [a, b]` the closed walk `a, b, anchor(b) …, slitTop,
… anchor(a) reversed` is a polygon `Γ` (`walkPoly`) whose boundary lies in `(dom C)ᶜ ∪ c` and
whose only edge meeting the domain is `c`; `Jordan.parity_flip`, valid for any vertex list,
gives the parity flip of `Γ` across `c` (`exists_walk_parity_flip`), and the parity of `Γ` is
constant on every region (regions avoid `Γ.boundary`).
-/

namespace Chazelle

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Jordan

namespace Chain

variable (C : Chain)

/-! ### Polygons from functions -/

/-- The polygon with vertices `W 0, …, W (N - 1)`. -/
def funPoly (W : ℕ → Point) (N : ℕ) : Polygon := ⟨(List.range N).map W⟩

section
variable (W : ℕ → Point)
@[simp] theorem funPoly_n (N : ℕ) : (funPoly W N).n = N := by
  simp [funPoly, Polygon.n]

theorem funPoly_vtx {N i : ℕ} (hi : i < N) : (funPoly W N).vtx i = W i := by
  simp_all [funPoly, Polygon.vtx, List.getD_eq_getElem?_getD] 

theorem funPoly_edge {N i : ℕ} (hi : i + 1 < N) :
    (funPoly W N).edge i = Chazelle.segment (W i) (W (i + 1)) := by
  unfold Polygon.edge
  rw [funPoly_n, Nat.mod_eq_of_lt hi, funPoly_vtx W (by omega), funPoly_vtx W hi]

theorem funPoly_edge_last {N : ℕ} (hN : 0 < N) :
    (funPoly W N).edge (N - 1) = Chazelle.segment (W (N - 1)) (W 0) := by
  unfold Polygon.edge
  rw [funPoly_n, Nat.sub_add_cancel hN, Nat.mod_self, funPoly_vtx W (by omega),
    funPoly_vtx W hN]

/-! ### Good paths in the obstacle -/


end

section
variable (f : ℕ → Point) (L : ℕ)
include f L
/-- A path `f 0, f 1, …, f L` all of whose segments lie in the complement of the domain. -/
def GoodPath : Prop :=
  ∀ i, i < L → Chazelle.segment (f i) (f (i + 1)) ⊆ C.domᶜ

/-- The reverse of the path `f 0, …, f L`. -/
def revPath (i : ℕ) : Point := f (L - i)


end

/-- The concatenation of the path `f 0, …, f L` with the path `g 0, …`. -/
def concatPath (f g : ℕ → Point) (L i : ℕ) : Point := if i ≤ L then f i else g (i - L)

section
variable (f g : ℕ → Point)
theorem concatPath_zero (L : ℕ) : concatPath f g L 0 = f 0 := by
  aesop

theorem concatPath_last {L L' : ℕ} (hjoin : f L = g 0) :
    concatPath f g L (L + L') = g L' := by
  simp_all [concatPath, Nat.add_zero, Nat.add_sub_cancel_left] 


end

/-- The reverse of a good path is a good path. -/
theorem goodPath_reverse {f : ℕ → Point} {L : ℕ} (hf : C.GoodPath f L) :
    C.GoodPath (revPath f L) L := by
  core_grind [Geometry.segment_comm]

/-- Concatenation of good paths meeting at the junction point. -/
theorem goodPath_concat {f g : ℕ → Point} {L L' : ℕ} (hf : C.GoodPath f L) (hg : C.GoodPath g L')
    (hjoin : f L = g 0) : C.GoodPath (concatPath f g L) (L + L') := by
  intro i hi
  simp only [concatPath]
  rcases Nat.lt_or_ge i L with h | h
  · rw [ite_eq_left (show i ≤ L from h.le), ite_eq_left (show i + 1 ≤ L from h)]
    exact hf i h
  · rw [ite_eq_right (show ¬ (i + 1 ≤ L) by omega)]
    rcases h.lt_or_eq with h' | h'
    · rw [ite_eq_right (show ¬ (i ≤ L) by omega)]
      have : i + 1 - L = (i - L) + 1 := by omega
      rw [this]
      exact hg _ (by omega)
    aesop

/-! ### Anchor paths -/

/-- A point is *anchorable* when it is on the chain, on the slit, or on the perimeter of the
box. -/
def Anchorable (q : Point) : Prop :=
  q ∈ C.set ∨ q ∈ C.slit ∨ |q.1| = C.radius ∨ |q.2| = C.radius

theorem Anchorable.not_mem_dom {q : Point} (hq : C.Anchorable q) : q ∉ C.dom := by
  intro hd
  rcases hq with h | h | h | h
  · exact C.not_mem_set_of_mem_dom hd h
  · exact C.not_mem_slit_of_mem_dom hd h
  · exact absurd hd.1.1 (by simp_all)
  · exact absurd hd.1.2 (by simp_all)

theorem slitTop_mem_slit : C.slitTop ∈ C.slit := Geometry.right_mem_segment _ _

theorem slitTop_snd : C.slitTop.2 = C.radius := rfl

/-- A vertical segment on a side `|x| = R` of the box is outside the domain. -/
theorem vertical_side_subset {p q : Point} (hpq : p.1 = q.1) (hp : |p.1| = C.radius) :
    Chazelle.segment p q ⊆ C.domᶜ := by
  intro x hx
  have hx1 := fst_eq_of_mem_segment_vertical hpq hx
  intro hd
  have := hd.1.1
  simp_all

/-- A horizontal segment on a side `|y| = R` of the box is outside the domain. -/
theorem horizontal_side_subset {p q : Point} (hpq : p.2 = q.2) (hp : |p.2| = C.radius) :
    Chazelle.segment p q ⊆ C.domᶜ := by
  intro x hx
  obtain ⟨t, -, -, rfl⟩ := hx
  intro hd
  have := hd.1.2
  simp_all

/-- A segment inside a chain edge is outside the domain. -/
theorem segment_subset_of_mem_chainEdge {j : ℕ} (hj : j < C.m) {p q : Point}
    (hp : p ∈ C.chainEdge j) (hq : q ∈ C.chainEdge j) : Chazelle.segment p q ⊆ C.domᶜ := by
  intro x hx
  have : x ∈ C.chainEdge j := by
    unfold chainEdge Polygon.edge at hp hq ⊢
    exact Geometry.segment_subset_of_convex (Geometry.segment_convex _ _) hp hq hx
  exact C.set_subset_dom_compl ⟨j, hj, this⟩

theorem slit_subset_dom_compl' : Chazelle.segment C.top C.slitTop ⊆ C.domᶜ :=
  C.slit_subset_dom_compl

/-- The anchor path of a chain point `q` on edge `j`: `q, vertex j, vertex (j-1), …, vertex 0,
vertex 1, …, vertex topIdx, slitTop`. -/
noncomputable def chainAnchor (q : Point) (j i : ℕ) : Point :=
  if i = 0 then q
  else if i ≤ j + 1 then C.vertex (j + 1 - i)
  else if i ≤ j + 1 + C.topIdx then C.vertex (i - (j + 1))
  else C.slitTop

section
variable (q : Point) (j : ℕ)
theorem chainAnchor_zero : C.chainAnchor q j 0 = q := by
  aesop

theorem chainAnchor_last :
    C.chainAnchor q j (j + 1 + C.topIdx + 1) = C.slitTop := by
  grind [chainAnchor]


end

/-- The vertices of the chain, seen from the anchor path, step along chain edges. -/
theorem vertex_segment_subset {i : ℕ} (hi : i < C.m) :
    Chazelle.segment (C.vertex i) (C.vertex (i + 1)) ⊆ C.domᶜ := by
  rw [← C.chainEdge_eq i]
  exact fun x hx => C.set_subset_dom_compl ⟨i, hi, hx⟩

/-- The anchor path of a chain point is a good path. -/
theorem goodPath_chainAnchor {q : Point} {j : ℕ} (hj : j < C.m) (hq : q ∈ C.chainEdge j) :
    C.GoodPath (C.chainAnchor q j) (j + 1 + C.topIdx + 1) := by
  have hT := C.topIdx_le
  intro i hi
  simp only [chainAnchor]
  by_cases hi0 : i = 0
  · subst hi0
    rw [ite_eq_left (show 0 = 0 from rfl), ite_eq_right (show ¬ (0 + 1 = 0) by omega),
      ite_eq_left (show 0 + 1 ≤ j + 1 by omega)]
    simp only [zero_add, Nat.add_sub_cancel]
    exact C.segment_subset_of_mem_chainEdge hj hq (C.vertex_mem_chainEdge j)
  rw [ite_eq_right hi0, ite_eq_right (show ¬ (i + 1 = 0) by omega)]
  by_cases hi1 : i ≤ j + 1
  · rw [ite_eq_left hi1]
    rcases hi1.lt_or_eq with hlt | heq
    · -- going backwards along the chain
      rw [ite_eq_left (show i + 1 ≤ j + 1 from hlt)]
      have : j + 1 - i = (j + 1 - (i + 1)) + 1 := by omega
      rw [this, Geometry.segment_comm]
      exact C.vertex_segment_subset (by omega)
    · -- at vertex `0`: go forward to vertex `1`, or to the slit top if the top is vertex `0`
      subst heq
      rw [ite_eq_right (show ¬ (j + 1 + 1 ≤ j + 1) by omega), Nat.sub_self]
      by_cases hT0 : C.topIdx = 0
      · rw [ite_eq_right (show ¬ (j + 1 + 1 ≤ j + 1 + C.topIdx) by omega)]
        have htop : C.vertex 0 = C.top := by grind [top]
        rw [htop]
        exact C.slit_subset_dom_compl'
      · rw [ite_eq_left (show j + 1 + 1 ≤ j + 1 + C.topIdx by omega), Nat.add_sub_cancel_left]
        exact C.vertex_segment_subset (by omega)
  · rw [ite_eq_right hi1, ite_eq_right (show ¬ (i + 1 ≤ j + 1) by omega)]
    by_cases hi2 : i ≤ j + 1 + C.topIdx
    · rw [ite_eq_left hi2]
      rcases hi2.lt_or_eq with hlt | heq
      · rw [ite_eq_left (show i + 1 ≤ j + 1 + C.topIdx from hlt)]
        have : i + 1 - (j + 1) = (i - (j + 1)) + 1 := by omega
        rw [this]
        exact C.vertex_segment_subset (by omega)
      · rw [ite_eq_right (show ¬ (i + 1 ≤ j + 1 + C.topIdx) by omega)]
        have htop : C.vertex (i - (j + 1)) = C.top := by
          grind [top]
        rw [htop]
        exact C.slit_subset_dom_compl'
    omega

/-- **Every anchorable point has an anchor path**: a good path from it to the slit top. -/
theorem exists_anchor {q : Point} (hq : C.Anchorable q) :
    ∃ (f : ℕ → Point) (L : ℕ), f 0 = q ∧ f L = C.slitTop ∧ C.GoodPath f L := by
  rcases hq with hq | hq | hq | hq
  · obtain ⟨j, hj, hqj⟩ := hq
    exact ⟨C.chainAnchor q j, j + 1 + C.topIdx + 1, C.chainAnchor_zero q j,
      C.chainAnchor_last q j, C.goodPath_chainAnchor hj hqj⟩
  · refine ⟨fun i => if i = 0 then q else C.slitTop, 1, by simp, by simp, ?_⟩
    intro i hi
    have : i = 0 := by omega
    subst this
    simp only [ite_true, zero_add, one_ne_zero, ite_false]
    intro x hx
    apply C.slit_subset_dom_compl
    exact Geometry.segment_subset_of_convex (Geometry.segment_convex _ _) hq
      C.slitTop_mem_slit hx
  · -- on a vertical side: go up to the top side, then along it
    refine ⟨fun i => if i = 0 then q else if i = 1 then (q.1, C.radius) else C.slitTop, 2,
      by simp, by simp, ?_⟩
    intro i hi
    rcases Nat.lt_succ_iff.1 hi |>.lt_or_eq with h | h
    · have : i = 0 := by omega
      subst this
      simp only [ite_true, zero_add, one_ne_zero, ite_false]
      exact C.vertical_side_subset rfl hq
    · subst h
      simp only [one_ne_zero, ite_false, ite_true, show (1 + 1 : ℕ) = 2 from rfl,
        OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one]
      apply C.horizontal_side_subset (p := (q.1, C.radius)) (q := C.slitTop) rfl
      grind
  · -- on a horizontal side: go to the right side, up to the corner, then along the top
    refine ⟨fun i => if i = 0 then q else if i = 1 then (C.radius, q.2)
      else if i = 2 then (C.radius, C.radius) else C.slitTop, 3, by simp, by simp, ?_⟩
    intro i hi
    have hR : |C.radius| = C.radius := abs_of_pos C.radius_pos
    rcases Nat.lt_succ_iff.1 hi |>.lt_or_eq with h | h
    · rcases Nat.lt_succ_iff.1 h |>.lt_or_eq with h' | h'
      · have : i = 0 := by omega
        subst this
        simp only [ite_true, zero_add, one_ne_zero, ite_false]
        exact C.horizontal_side_subset rfl hq
      · subst h'
        simp only [one_ne_zero, ite_false, ite_true, show (1 + 1 : ℕ) = 2 from rfl,
          OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one]
        exact C.vertical_side_subset (p := (C.radius, q.2)) rfl hR
    · subst h
      simp only [OfNat.ofNat_ne_zero, ite_false, OfNat.ofNat_ne_one, ite_true,
        show (2 + 1 : ℕ) = 3 from rfl, show (3 : ℕ) ≠ 2 by norm_num]
      exact C.horizontal_side_subset (p := (C.radius, C.radius)) rfl hR

/-! ### The closed walk of a chord -/

section
variable (a : Point) (path : ℕ → Point)
include a path
/-- The closed walk of a segment `[a, b]`: `a` followed by a path `path 0 = b, …, path M = a`. -/
def walkFun (i : ℕ) : Point := if i = 0 then a else path (i - 1)

/-- The closed walk as a polygon with `M + 1` vertices `a, path 0, …, path (M - 1)`. -/
def walkPoly (M : ℕ) : Polygon := funPoly (walkFun a path) (M + 1)


end

section
variable (a : Point) (path : ℕ → Point)
theorem walkFun_zero : walkFun a path 0 = a := by aesop

theorem walkFun_succ (i : ℕ) : walkFun a path (i + 1) = path i := by
  aesop

@[simp] theorem walkPoly_n (M : ℕ) :
    (walkPoly a path M).n = M + 1 := by simp [walkPoly]

/-- The first edge of the walk is the segment `[a, path 0]`. -/
theorem walkPoly_edge_zero {M : ℕ} (hM : 0 < M) :
    (walkPoly a path M).edge 0 = Chazelle.segment a (path 0) := by
  rw [walkPoly, funPoly_edge _ (by omega), walkFun_zero, walkFun_succ]


end

section
variable {a : Point} {path : ℕ → Point} {M : ℕ} (hpath : C.GoodPath path M) (hend : path M = a)
include hpath hend
/-- Every edge of the walk other than the first lies in the obstacle. -/
theorem walkPoly_edge_subset {k : ℕ} (hk0 : 0 < k) (hk : k < M + 1) :
    (walkPoly a path M).edge k ⊆ C.domᶜ := by
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  rcases Nat.lt_or_ge (i + 1 + 1) (M + 1) with hlt | hge
  · rw [walkPoly, funPoly_edge _ hlt, walkFun_succ, walkFun_succ]
    aesop
  · have hi : i + 1 = M + 1 - 1 := by omega
    have hiM : i = M - 1 := by omega
    have hM1 : M + 1 - 1 = i + 1 := by omega
    rw [walkPoly, hi, funPoly_edge_last _ (by omega), walkFun_zero, hM1, walkFun_succ, ← hend,
      hiM]
    have hM : M = (M - 1) + 1 := by omega
    have := hpath (M - 1) (by omega)
    grind

/-- The boundary of the walk lies in the obstacle together with the segment `[a, path 0]`. -/
theorem walkPoly_boundary_subset (hM : 0 < M) :
    (walkPoly a path M).boundary ⊆ C.domᶜ ∪ Chazelle.segment a (path 0) := by
  rintro p ⟨k, hk, hp⟩
  rw [walkPoly_n] at hk
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · right
    rw [walkPoly_edge_zero a path hM] at hp
    exact hp
  · left
    exact C.walkPoly_edge_subset hpath hend hk0 hk hp


end

/-- **The parity flip across a segment with anchorable endpoints.**  For a non-vertical segment
`[a, b]` with `a, b` anchorable and a point `z` of the segment in the domain, there is a closed
walk `Γ` with boundary in `(dom C)ᶜ ∪ [a, b]` whose crossing parity flips across the segment at
`z`. -/
theorem exists_walk_parity_flip {a b : Point} (ha : C.Anchorable a) (hb : C.Anchorable b)
    (hab : a.1 ≠ b.1) {z : Point} (hz : z ∈ Chazelle.segment a b) (hzd : z ∈ C.dom) :
    ∃ Γ : Polygon, Γ.boundary ⊆ C.domᶜ ∪ Chazelle.segment a b ∧
      ∃ ε₀ > (0 : ℝ), ∀ ε, 0 < ε → ε < ε₀ →
        (z.1, z.2 + ε) ∉ Γ.boundary ∧ (z.1, z.2 - ε) ∉ Γ.boundary ∧
          parity Γ (z.1, z.2 + ε) ≠ parity Γ (z.1, z.2 - ε) := by
  obtain ⟨fa, La, ha0, haL, hfa⟩ := C.exists_anchor ha
  obtain ⟨fb, Lb, hb0, hbL, hfb⟩ := C.exists_anchor hb
  set path := concatPath fb (revPath fa La) Lb with hpath_def
  have hjoin : fb Lb = revPath fa La 0 := by grind [revPath]
  have hpath : C.GoodPath path (Lb + La) := C.goodPath_concat hfb (C.goodPath_reverse hfa) hjoin
  have hend : path (Lb + La) = a := by
    rw [hpath_def, concatPath_last _ _ hjoin]
    grind [revPath]
  have hp0 : path 0 = b := by grind [concatPath_zero]
  have hM : 0 < Lb + La := by
    grind
  refine ⟨walkPoly a path (Lb + La), ?_, ?_⟩
  · rw [← hp0]
    exact C.walkPoly_boundary_subset hpath hend hM
  · have h0n : 0 < (walkPoly a path (Lb + La)).n := by simp_all
    have hzΓ : z ∈ (walkPoly a path (Lb + La)).edge 0 := by
      rw [walkPoly_edge_zero a path hM, hp0]; exact hz
    have hv0 : (walkPoly a path (Lb + La)).vtx 0 = a := by
      rw [walkPoly, funPoly_vtx _ (by omega), walkFun_zero]
    have hv1 : (walkPoly a path (Lb + La)).vtx ((0 + 1) % (walkPoly a path (Lb + La)).n) = b := by
      rw [walkPoly_n, Nat.mod_eq_of_lt (by omega), walkPoly, funPoly_vtx _ (by omega),
        walkFun_succ, hp0]
    have hne : ((walkPoly a path (Lb + La)).vtx 0).1 ≠
        ((walkPoly a path (Lb + La)).vtx ((0 + 1) % (walkPoly a path (Lb + La)).n)).1 := by
      simp_all
    have hzu : z ≠ (walkPoly a path (Lb + La)).vtx 0 := by
      rw [hv0]; rintro rfl; exact Anchorable.not_mem_dom C ha hzd
    have hzv : z ≠ (walkPoly a path (Lb + La)).vtx ((0 + 1) % (walkPoly a path (Lb + La)).n) := by
      rw [hv1]; rintro rfl; exact Anchorable.not_mem_dom C hb hzd
    have hother : ∀ k, k < (walkPoly a path (Lb + La)).n → k ≠ 0 →
        z ∉ (walkPoly a path (Lb + La)).edge k := by
      intro k hk hk0 hzk
      rw [walkPoly_n] at hk
      exact C.walkPoly_edge_subset hpath hend (Nat.pos_of_ne_zero hk0) hk hzk hzd
    exact parity_flip (walkPoly a path (Lb + La)) h0n hzΓ hne hzu hzv hother

/-! ### Submaps and chord separation -/



end Chain

end

end Chazelle
