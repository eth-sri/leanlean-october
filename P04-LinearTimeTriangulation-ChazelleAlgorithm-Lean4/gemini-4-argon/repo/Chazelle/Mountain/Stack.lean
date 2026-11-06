module

public import Chazelle.Mountain.Orientation
public import Chazelle.Mountain.Lex
public import Chazelle.EarClip.Abstract

/-!
# Triangulating a monotone mountain with a stack

A polygon is a *monotone mountain* (`IsMountain`) when it is simple and its vertex chain
`v₀, v₁, …, v_{n-1}` is strictly increasing for the `(y, x)`-lexicographic order `ylexLT`; the
closing edge `v_{n-1} v₀` is the *base*.

The stack algorithm (`popLoop`, `walk`, `mountainTriangulation`): walk the chain; keep a stack
of vertex indices (top first); push `0, 1`; for `k = 2, …, n - 1`, while the stack has two
elements `c` (top) and `b` below it and the corner `(b, c, k)` is strictly convex on the interior
side (`0 < σ * det (vtx b) (vtx c) (vtx k)`, with `σ = orient P` the orientation sign), pop
`c` and emit the triangle `(b, c, k)`; then push `k`.  Every test costs one corner evaluation;
`popLoop` and `walk` return the emitted triangles, the new stack and the number of tests.

Correctness (`mountain_triangulates`): the emitted list is a triangulation.  The invariant
(`Inv`): the remaining polygon `subPoly P l`, `l = stack.reverse ++ [k, …, n - 1]`, is simple,
its index list is sorted for `ylexLT`, and its orientation is that of `P`.  Every popped corner is
an ear of the remaining polygon (`isEar_of_convex_corner`): its closed triangle contains no other
vertex because every point of the triangle is `ylexLE`-between its lowest and highest corner
(`ylexLE_of_mem_convexHull_min`, `ylexLE_of_mem_convexHull_max`), and then
`isEar_iff_convex_of_empty` applies.  The stack is a reflex chain (`ReflexIdx`), so at the last
vertex every remaining corner is convex (`convex_last_of_reflex`, via two non-adjacent ears
`exists_two_ears`) and the stack empties down to `[n - 1, 0]`.

Operation count (`mountainTests_le`): at most `2 * n` corner tests.
-/

namespace Chazelle.Mountain

@[expose] public section

open Set Filter Topology
open Chazelle.Jordan
open Chazelle.Existence
open Chazelle.Ears
open Chazelle.EarClip
open Chazelle.Geometry (lerp point_ext point_ext_iff mem_convexHull_triple add_fst add_snd
  smul_fst smul_snd)

/-- Auxiliary real inequality for the convex hull lemmas. -/
theorem hull_aux {w₂ w₃ d₂ d₃ e₂ e₃ : ℝ} (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃) (hd₂ : 0 ≤ d₂)
    (hd₃ : 0 ≤ d₃) (he₂ : d₂ = 0 → 0 ≤ e₂) (he₃ : d₃ = 0 → 0 ≤ e₃) :
    0 < w₂ * d₂ + w₃ * d₃ ∨ (w₂ * d₂ + w₃ * d₃ = 0 ∧ 0 ≤ w₂ * e₂ + w₃ * e₃) := by
  have h2 : 0 ≤ w₂ * d₂ := mul_nonneg hw₂ hd₂
  have h3 : 0 ≤ w₃ * d₃ := mul_nonneg hw₃ hd₃
  by_cases h : w₂ * d₂ + w₃ * d₃ = 0
  · right
    refine ⟨h, ?_⟩
    have h2' : w₂ * d₂ = 0 := by linarith
    have h3' : w₃ * d₃ = 0 := by linarith
    have e2 : 0 ≤ w₂ * e₂ := by
      rcases mul_eq_zero.1 h2' with h' | h'
      · rw [h', zero_mul]
      · exact mul_nonneg hw₂ (he₂ h')
    have e3 : 0 ≤ w₃ * e₃ := by
      rcases mul_eq_zero.1 h3' with h' | h'
      · rw [h', zero_mul]
      · exact mul_nonneg hw₃ (he₃ h')
    linarith
  · left
    exact lt_of_le_of_ne (by linarith) (Ne.symm h)

/-- The data of `ylexLE a b`: the height difference is nonnegative, and when it vanishes the
abscissa difference is nonnegative. -/
theorem ylexLE_data {a b : Point} (h : ylexLE a b) :
    0 ≤ b.2 - a.2 ∧ (b.2 - a.2 = 0 → 0 ≤ b.1 - a.1) := by
  rcases h with h | ⟨h1, h2⟩
  · exact ⟨by linarith, fun h' => by linarith⟩
  · exact ⟨by linarith, fun _ => by linarith⟩

/-- **Every point of a triangle is `ylexLE`-above its lowest corner.** -/
theorem ylexLE_of_mem_convexHull_min {a b c p : Point} (hab : ylexLE a b) (hac : ylexLE a c)
    (hp : p ∈ convexHull ℝ ({a, b, c} : Set Point)) : ylexLE a p := by
  obtain ⟨w₁, w₂, w₃, hw₁, hw₂, hw₃, hw, rfl⟩ := mem_convexHull_triple.1 hp
  obtain ⟨hd₂, he₂⟩ := ylexLE_data hab
  obtain ⟨hd₃, he₃⟩ := ylexLE_data hac
  have e2 : (w₁ • a + w₂ • b + w₃ • c).2 - a.2 = w₂ * (b.2 - a.2) + w₃ * (c.2 - a.2) := by
    simp only [add_snd, smul_snd]; linear_combination a.2 * hw
  have e1 : (w₁ • a + w₂ • b + w₃ • c).1 - a.1 = w₂ * (b.1 - a.1) + w₃ * (c.1 - a.1) := by
    simp only [add_fst, smul_fst]; linear_combination a.1 * hw
  rcases hull_aux hw₂ hw₃ hd₂ hd₃ he₂ he₃ with h | ⟨h, h'⟩
  · left; linarith
  · right; exact ⟨by linarith, by linarith⟩

/-- **Every point of a triangle is `ylexLE`-below its highest corner.** -/
theorem ylexLE_of_mem_convexHull_max {a b c p : Point} (hac : ylexLE a c) (hbc : ylexLE b c)
    (hp : p ∈ convexHull ℝ ({a, b, c} : Set Point)) : ylexLE p c := by
  obtain ⟨w₁, w₂, w₃, hw₁, hw₂, hw₃, hw, rfl⟩ := mem_convexHull_triple.1 hp
  obtain ⟨hd₁, he₁⟩ := ylexLE_data hac
  obtain ⟨hd₂, he₂⟩ := ylexLE_data hbc
  have e2 : c.2 - (w₁ • a + w₂ • b + w₃ • c).2 = w₁ * (c.2 - a.2) + w₂ * (c.2 - b.2) := by
    simp only [add_snd, smul_snd]; linear_combination (-c.2) * hw
  have e1 : c.1 - (w₁ • a + w₂ • b + w₃ • c).1 = w₁ * (c.1 - a.1) + w₂ * (c.1 - b.1) := by
    simp only [add_fst, smul_fst]; linear_combination (-c.1) * hw
  rcases hull_aux hw₁ hw₂ hd₁ hd₂ he₁ he₂ with h | ⟨h, h'⟩
  · left; linarith
  · right; exact ⟨by linarith, by linarith⟩

/-! ### List helpers -/

/-- `getD` of a reversed list. -/
theorem getD_reverse (s : List ℕ) {i : ℕ} (hi : i < s.length) :
    s.reverse.getD i 0 = s.getD (s.length - 1 - i) 0 := by
  rw [getD_eq_getElem_of_lt _ _ (by rwa [List.length_reverse]),
    getD_eq_getElem_of_lt _ _ (by omega), List.getElem_reverse]

/-- `getD` on the left part of an append. -/
theorem getD_append_of_lt (A B : List ℕ) {i : ℕ} (hi : i < A.length) :
    (A ++ B).getD i 0 = A.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

/-- `getD` on the right part of an append. -/
theorem getD_append_of_le (A B : List ℕ) {i : ℕ} (hi : A.length ≤ i) :
    (A ++ B).getD i 0 = B.getD (i - A.length) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

/-- The entry of `A ++ x :: B` at position `A.length + i` is the entry of `x :: B` at `i`. -/
theorem getD_append_cons (A : List ℕ) (x : ℕ) (B : List ℕ) (i : ℕ) :
    (A ++ x :: B).getD (A.length + i) 0 = (x :: B).getD i 0 := by
  rw [getD_append_of_le _ _ (by omega), Nat.add_sub_cancel_left]

/-- The entry of `A ++ x :: B` at position `A.length` is `x`. -/
theorem getD_append_length (A : List ℕ) (x : ℕ) (B : List ℕ) :
    (A ++ x :: B).getD A.length 0 = x := by
  rw [← Nat.add_zero A.length, getD_append_cons, List.getD_cons_zero]

/-- An in-range `getD` entry is a member. -/
theorem getD_mem (l : List ℕ) {i : ℕ} (hi : i < l.length) : l.getD i 0 ∈ l := by
  rw [getD_eq_getElem_of_lt _ _ hi]; exact List.getElem_mem hi

/-- In a `Nodup` list, equal in-range entries have equal positions. -/
theorem getD_inj_of_nodup {l : List ℕ} (hnd : l.Nodup) {i j : ℕ} (hi : i < l.length)
    (hj : j < l.length) (h : l.getD i 0 = l.getD j 0) : i = j := by
  rw [getD_eq_getElem_of_lt _ _ hi, getD_eq_getElem_of_lt _ _ hj] at h
  exact hnd.getElem_inj_iff.1 h

/-- Rotating forward by `r` and then by `l.length - r % l.length` is the identity. -/
theorem rotate_rotate_cancel {α : Type} (l : List α) (r : ℕ) :
    (l.rotate r).rotate (l.length - r % l.length) = l := by
  rcases Nat.eq_zero_or_pos l.length with h0 | hpos
  · rw [List.length_eq_zero_iff.1 h0]; simp
  · rw [List.rotate_rotate]
    have hmod := Nat.mod_lt r hpos
    have hdiv := Nat.div_add_mod r l.length
    have e : r + (l.length - r % l.length) = l.length * (r / l.length + 1) := by
      rw [Nat.mul_succ]
      omega
    rw [e, List.rotate_length_mul]

/-- The clipped list of `A ++ b :: c :: B` at the position of `c` is `A ++ b :: B`, rotated by
`A.length`. -/
theorem clipList_append_cons_cons (A : List ℕ) (b c : ℕ) (B : List ℕ) :
    clipList (A ++ b :: c :: B) (A.length + 1) = (A ++ b :: B).rotate A.length := by
  rw [clipList_eq_rotate_eraseIdx _ (by omega), Nat.add_sub_cancel, List.rotate_append_length_eq,
    List.rotate_append_length_eq]
  simp

/-- The emitted triangle at the position of `c` in `A ++ b :: c :: k :: B` is `(b, c, k)`. -/
theorem earTri_append (A : List ℕ) (b c k : ℕ) (B : List ℕ) :
    earTri (A ++ b :: c :: k :: B) (A.length + 1) = (b, c, k) := by
  unfold earTri
  have hlen : (A ++ b :: c :: k :: B).length = A.length + 3 + B.length := by simp; omega
  rw [hlen]
  have e1 : (A.length + 1 + (A.length + 3 + B.length) - 1) % (A.length + 3 + B.length) =
      A.length := by
    rw [show A.length + 1 + (A.length + 3 + B.length) - 1 = A.length + (A.length + 3 + B.length)
      by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have e2 : (A.length + 1 + 1) % (A.length + 3 + B.length) = A.length + 2 :=
    Nat.mod_eq_of_lt (by omega)
  rw [e1, e2, getD_append_length, getD_append_cons, getD_append_cons]
  rfl

/-! ### Relabelled weak triangulations of index lists -/

/-- `T` (in original indices) is the relabelling of a weak triangulation of `subPoly P l`. -/
def GoodTri (P : Polygon) (l : List ℕ) (T : List Polygon.Triangle) : Prop :=
  ∃ T', WeakTriangulates (subPoly P l) T' ∧ T = T'.map (relabelList l)

variable (P : Polygon)

/-- A list with a relabelled weak triangulation has at least three entries. -/
theorem three_le_length_of_goodTri {l : List ℕ} {T : List Polygon.Triangle}
    (h : GoodTri P l T) : 3 ≤ l.length := by
  obtain ⟨T', hT', -⟩ := h
  have hlen := hT'.2.1
  rw [n_subPoly] at hlen
  by_contra hlt
  have hT0 : T' = [] := by
    rw [List.length_eq_zero_iff.symm]; omega
  have hfill := hT'.2.2.1
  rw [hT0] at hfill
  have h0 : (subPoly P l).vtx 0 ∈ (subPoly P l).filled :=
    Jordan.boundary_subset_filled _ (vtx_mem_boundary _ (by rw [n_subPoly]; omega))
  rw [← hfill] at h0
  obtain ⟨t, ht, -⟩ := h0
  simp at ht

/-- Relabelled weak triangulations are invariant under rotation of the index list. -/
theorem goodTri_rotate {l : List ℕ} {T : List Polygon.Triangle} (h : GoodTri P l T) (r : ℕ) :
    GoodTri P (l.rotate r) T := by
  obtain ⟨T', hT', rfl⟩ := h
  set r' := l.length - r % l.length with hr'
  have hl : subPoly P l = (subPoly P (l.rotate r)).rotate r' := by
    rw [← subPoly_rotate, rotate_rotate_cancel]
  rw [hl] at hT'
  have h1 := weakTriangulates_rotate _ _ hT'
  refine ⟨_, h1, ?_⟩
  rw [List.map_map]
  apply List.map_congr_left
  intro t ht
  obtain ⟨h1, h2, h3, -⟩ := hT'.1 t ht
  rw [n_rotate, n_subPoly, List.length_rotate] at h1 h2 h3
  have hm : 0 < l.length := by omega
  have key : ∀ i, i < l.length →
      (l.rotate r).getD ((r' + i) % l.length) 0 = l.getD i 0 := by
    intro i hi
    rw [getD_rotate _ _ _ (Nat.mod_lt _ hm), Nat.mod_add_mod,
      show r' + i + r = i + (r' + r) by ring]
    have e : r' + r = l.length * (r / l.length + 1) := by
      rw [hr', Nat.mul_succ]
      have := Nat.div_add_mod r l.length
      have := Nat.mod_lt r hm
      omega
    rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
  obtain ⟨t1, t2, t3⟩ := t
  simp only [Function.comp, relabelList, relabel_fst, relabel_snd_fst, relabel_snd_snd,
    n_subPoly, List.length_rotate]
  rw [key _ h1, key _ h2, key _ h3]

/-- The one-triangle case. -/
theorem goodTri_triangle {l : List ℕ} (hQ : (subPoly P l).Simple) (h3 : l.length = 3) :
    GoodTri P l [(l.getD 0 0, l.getD 1 0, l.getD 2 0)] :=
  ⟨[(0, 1, 2)], weakTriangulates_triangle _ hQ (by rw [n_subPoly]; exact h3), rfl⟩

/-- Clipping an ear (position `p` of `l`) extends a relabelled weak triangulation. -/
theorem goodTri_clipList {l : List ℕ} {p : ℕ} (h3 : 3 ≤ l.length) (hp : p < l.length)
    (hQ : (subPoly P l).Simple) (he : IsEar (subPoly P l) p) {T : List Polygon.Triangle}
    (h : GoodTri P (clipList l p) T) : GoodTri P l (earTri l p :: T) := by
  obtain ⟨T', hT', rfl⟩ := h
  refine ⟨earTriangle (subPoly P l) p :: T'.map (clipRelabel l.length p),
    weakTriangulates_clipList P l p h3 hp hQ he hT', ?_⟩
  rw [List.map_cons, List.map_map, relabelList_earTriangle]
  congr 1
  apply List.map_congr_left
  intro t ht
  obtain ⟨h1, h2, h3', -⟩ := hT'.1 t ht
  rw [n_subPoly, length_clipList l p (by omega)] at h1 h2 h3'
  exact (relabelList_clipRelabel l p h3 ⟨h1, h2, h3'⟩).symm

/-- **Popping an ear.**  If the corner at `c` in `A ++ b :: c :: k :: B` is an ear of the
sub-polygon, a relabelled weak triangulation of `A ++ b :: k :: B` extends by `(b, c, k)`. -/
theorem goodTri_pop (A : List ℕ) (b c k : ℕ) (B : List ℕ)
    (hQ : (subPoly P (A ++ b :: c :: k :: B)).Simple)
    (he : IsEar (subPoly P (A ++ b :: c :: k :: B)) (A.length + 1)) {T : List Polygon.Triangle}
    (h : GoodTri P (A ++ b :: k :: B) T) :
    GoodTri P (A ++ b :: c :: k :: B) ((b, c, k) :: T) := by
  rw [← earTri_append A b c k B]
  apply goodTri_clipList P (by simp; omega) (by simp) hQ he
  rw [clipList_append_cons_cons]
  exact goodTri_rotate P h _

/-- A relabelled weak triangulation of `List.range P.n` is a weak triangulation of `P`. -/
theorem weakTriangulates_of_goodTri_range {T : List Polygon.Triangle}
    (h : GoodTri P (List.range P.n) T) : WeakTriangulates P T := by
  obtain ⟨T', hT', rfl⟩ := h
  rw [subPoly_range] at hT'
  have : T'.map (relabelList (List.range P.n)) = T' := by
    conv_rhs => rw [← List.map_id T']
    apply List.map_congr_left
    intro t ht
    obtain ⟨h1, h2, h3, -⟩ := hT'.1 t ht
    exact relabelList_range ⟨h1, h2, h3⟩
  rwa [this]

/-! ### The invariant of the remaining polygon -/

/-- The invariant of the remaining polygon `subPoly P l`: distinct valid indices, at least
three of them, a simple polygon, sorted for `ylexLT`, with the orientation of `P`. -/
def Inv (l : List ℕ) : Prop :=
  l.Nodup ∧ (∀ x ∈ l, x < P.n) ∧ 3 ≤ l.length ∧ (subPoly P l).Simple ∧
  l.Pairwise (fun i j => ylexLT (P.vtx i) (P.vtx j)) ∧ orient (subPoly P l) = orient P

/-- Simplicity of a sub-polygon transfers back along a rotation of the index list. -/
theorem simple_subPoly_of_rotate {l : List ℕ} {r : ℕ} (h : (subPoly P (l.rotate r)).Simple) :
    (subPoly P l).Simple := by
  have := simple_rotate _ (l.length - r % l.length) h
  rwa [← subPoly_rotate, rotate_rotate_cancel] at this

/-- **A convex corner of a sorted remaining polygon is an ear.**  In `l = A ++ b :: c :: k :: B`
with `Inv P l` and at least four entries, if `0 < orient P * det (vtx b) (vtx c) (vtx k)` then
position `A.length + 1` (the vertex `c`) is the apex of an ear of `subPoly P l`. -/
theorem isEar_of_convex_corner (A : List ℕ) (b c k : ℕ) (B : List ℕ)
    (hI : Inv P (A ++ b :: c :: k :: B)) (h4 : 4 ≤ (A ++ b :: c :: k :: B).length)
    (hconv : 0 < orient P * det (P.vtx b) (P.vtx c) (P.vtx k)) :
    IsEar (subPoly P (A ++ b :: c :: k :: B)) (A.length + 1) := by
  obtain ⟨hnd, -, -, hQ, hsort, hor⟩ := hI
  set l := A ++ b :: c :: k :: B with hl
  set Q := subPoly P l with hQdef
  set p := A.length + 1 with hp
  have hlen : l.length = A.length + 3 + B.length := by simp [hl]; omega
  have hpl : p < l.length := by omega
  have hprev : prevIdx Q p = A.length := by
    rw [hQdef, prevIdx_subPoly, hlen,
      show p + (A.length + 3 + B.length) - 1 = A.length + (A.length + 3 + B.length) by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have hsucc : (p + 1) % Q.n = A.length + 2 := by
    rw [hQdef, n_subPoly, hlen]; exact Nat.mod_eq_of_lt (by omega)
  have ea : Q.vtx (prevIdx Q p) = P.vtx b := by
    rw [hprev, hQdef, vtx_subPoly_getD P l (by omega), getD_append_length]
  have ev : Q.vtx p = P.vtx c := by
    rw [hQdef, vtx_subPoly_getD P l hpl, hp, getD_append_cons]; rfl
  have eb : Q.vtx ((p + 1) % Q.n) = P.vtx k := by
    rw [hsucc, hQdef, vtx_subPoly_getD P l (by omega), getD_append_cons]; rfl
  have hdet : det (Q.vtx (prevIdx Q p)) (Q.vtx p) (Q.vtx ((p + 1) % Q.n)) ≠ 0 := by
    rw [ea, ev, eb]; intro h; rw [h, mul_zero] at hconv; exact lt_irrefl _ hconv
  -- the lexicographic facts
  have hpair := hsort
  rw [hl, List.pairwise_append] at hpair
  obtain ⟨-, hrest, hcross⟩ := hpair
  rw [List.pairwise_cons] at hrest
  obtain ⟨hb, hrest⟩ := hrest
  rw [List.pairwise_cons] at hrest
  obtain ⟨hc, hrest⟩ := hrest
  rw [List.pairwise_cons] at hrest
  obtain ⟨hk, -⟩ := hrest
  have hbc : ylexLE (P.vtx b) (P.vtx c) := ylexLE_of_ylexLT (hb c (by simp))
  have hbk : ylexLE (P.vtx b) (P.vtx k) := ylexLE_of_ylexLT (hb k (by simp))
  have hck : ylexLE (P.vtx c) (P.vtx k) := ylexLE_of_ylexLT (hc k (by simp))
  have hnone_elem : ∀ x ∈ l, x ≠ b → x ≠ c → x ≠ k →
      P.vtx x ∉ convexHull ℝ ({P.vtx b, P.vtx c, P.vtx k} : Set Point) := by
    intro x hx hxb hxc hxk hmem
    rw [hl, List.mem_append, List.mem_cons, List.mem_cons, List.mem_cons] at hx
    rcases hx with hx | hx | hx | hx | hx
    · exact not_ylexLE_of_ylexLT (hcross x hx b (by simp))
        (ylexLE_of_mem_convexHull_min hbc hbk hmem)
    · exact hxb hx
    · exact hxc hx
    · exact hxk hx
    · exact not_ylexLE_of_ylexLT (hk x hx) (ylexLE_of_mem_convexHull_max hbk hck hmem)
  have hnone : ∀ j, j < Q.n → j ≠ prevIdx Q p → j ≠ p → j ≠ (p + 1) % Q.n →
      Q.vtx j ∉ convexHull ℝ ({Q.vtx (prevIdx Q p), Q.vtx p, Q.vtx ((p + 1) % Q.n)} : Set Point) := by
    intro j hj hj1 hj2 hj3
    rw [hQdef, n_subPoly] at hj
    rw [ea, ev, eb, hQdef, vtx_subPoly_getD P l hj]
    rw [hprev] at hj1
    rw [hsucc] at hj3
    refine hnone_elem _ (getD_mem l hj) ?_ ?_ ?_
    · intro h
      exact hj1 (getD_inj_of_nodup hnd hj (by omega) (by rw [h, getD_append_length]))
    · intro h
      exact hj2 (getD_inj_of_nodup hnd hj hpl (by rw [h, hp, getD_append_cons]; rfl))
    · intro h
      exact hj3 (getD_inj_of_nodup hnd hj (by omega) (by rw [h, getD_append_cons]; rfl))
  rw [isEar_iff_convex_of_empty hQ (by rwa [hQdef, n_subPoly])
    (by rwa [hQdef, n_subPoly]) hdet hnone, ea, ev, eb, hor]
  exact hconv

/-- The list after a pop is a sublist of the list before. -/
theorem sublist_pop (A : List ℕ) (b c k : ℕ) (B : List ℕ) :
    List.Sublist (A ++ b :: k :: B) (A ++ b :: c :: k :: B) :=
  (List.Sublist.refl A).append (((List.Sublist.refl (k :: B)).cons c).cons_cons b)

/-- The filled region of the polygon with an ear clipped lies in the filled region. -/
theorem filled_clip_subset {Q : Polygon} (hQ : Q.Simple) {p : ℕ} (hp : p < Q.n)
    (he : IsEar Q p) : (clip Q p).filled ⊆ Q.filled := by
  have hn : 2 ≤ Q.n := by have := four_le_of_isEar Q p he; omega
  have hd := isDiagonal_compl Q (prevIdx Q p) 2 he.1
  have hin : Chazelle.segment (Q.vtx ((prevIdx Q p + 2) % Q.n % Q.n))
      (Q.vtx (((prevIdx Q p + 2) % Q.n + (Q.n - 2)) % Q.n)) ⊆ Q.filled := by
    rw [Nat.mod_mod, compl_arc_last_index Q (prevIdx Q p) 2 hn, prevIdx_mod Q hp,
      prevIdx_add_two_mod Q hp, segment_comm]
    exact he.2
  exact filled_arc_subset Q hQ hd hin

/-- **Popping an ear preserves the invariant.** -/
theorem inv_pop (A : List ℕ) (b c k : ℕ) (B : List ℕ) (hI : Inv P (A ++ b :: c :: k :: B))
    (h4 : 4 ≤ (A ++ b :: c :: k :: B).length)
    (he : IsEar (subPoly P (A ++ b :: c :: k :: B)) (A.length + 1)) :
    Inv P (A ++ b :: k :: B) := by
  obtain ⟨hnd, hlt, -, hQ, hsort, hor⟩ := hI
  have hsub := sublist_pop A b c k B
  set l := A ++ b :: c :: k :: B with hl
  set l' := A ++ b :: k :: B with hl'
  have hlen : l.length = A.length + 3 + B.length := by simp [hl]; omega
  have hlen' : l'.length = A.length + 2 + B.length := by simp [hl']; omega
  have hQ' : (subPoly P l').Simple := by
    have := simple_subPoly_clipList P l (A.length + 1) (by omega) (by omega) hQ he
    rw [clipList_append_cons_cons] at this
    exact simple_subPoly_of_rotate P this
  refine ⟨hnd.sublist hsub, fun x hx => hlt x (hsub.subset hx), by omega, hQ',
    hsort.sublist hsub, ?_⟩
  have hfill : (subPoly P l').filled ⊆ (subPoly P l).filled := by
    have e1 : (subPoly P l').filled = (subPoly P (clipList l (A.length + 1))).filled := by
      rw [clipList_append_cons_cons, subPoly_rotate, filled_rotate]
    rw [e1, subPoly_clipList_eq P l _ (by omega) (by omega), filled_rotate]
    exact filled_clip_subset hQ (by rw [n_subPoly]; omega) he
  have key := orient_eq_of_filled_subset hQ' hQ (i := l'.length - 1) (j := l.length - 1)
    (by rw [n_subPoly]; omega) (by rw [n_subPoly]; omega) ?_ ?_ hfill
  · rw [← hor, key]
  · rw [vtx_subPoly_getD P l' (by omega), vtx_subPoly_getD P l (by omega), hlen', hlen,
      show A.length + 2 + B.length - 1 = A.length + (B.length + 1) by omega,
      show A.length + 3 + B.length - 1 = A.length + (B.length + 1 + 1) by omega,
      getD_append_cons, getD_append_cons]
    simp only [List.getD_cons_succ]
  · have e1 : (l'.length - 1 + 1) % (subPoly P l').n = 0 := by
      rw [n_subPoly, Nat.sub_add_cancel (by omega), Nat.mod_self]
    have e2 : (l.length - 1 + 1) % (subPoly P l).n = 0 := by
      rw [n_subPoly, Nat.sub_add_cancel (by omega), Nat.mod_self]
    rw [e1, e2, vtx_subPoly_getD P l' (by omega), vtx_subPoly_getD P l (by omega)]
    rcases A with _ | ⟨a, A⟩ <;> rfl

/-! ### The reflex stack -/

/-- The stack `s` (top first) is a reflex chain: every three consecutive entries
`s[i+2], s[i+1], s[i]` (in chain order) make a corner that is not strictly convex on the
interior side. -/
def ReflexIdx (σ : ℝ) (s : List ℕ) : Prop :=
  ∀ i, i + 2 < s.length →
    σ * det (P.vtx (s.getD (i + 2) 0)) (P.vtx (s.getD (i + 1) 0)) (P.vtx (s.getD i 0)) ≤ 0

/-- Popping the top preserves the reflex property. -/
theorem reflexIdx_pop {σ : ℝ} {c : ℕ} {s : List ℕ} (h : ReflexIdx P σ (c :: s)) :
    ReflexIdx P σ s := by
  intro i hi
  have := h (i + 1) (by simp; omega)
  simpa only [List.getD_cons_succ] using this

/-- Pushing `k` preserves the reflex property provided the new top corner is not strictly
convex. -/
theorem reflexIdx_push {σ : ℝ} {s : List ℕ} (h : ReflexIdx P σ s) (k : ℕ)
    (hk : ∀ c b rest, s = c :: b :: rest → σ * det (P.vtx b) (P.vtx c) (P.vtx k) ≤ 0) :
    ReflexIdx P σ (k :: s) := by
  intro i hi
  rcases i with _ | i
  · rcases s with _ | ⟨c, s⟩
    · simp at hi
    rcases s with _ | ⟨b, s⟩
    · simp at hi
    simpa only [List.getD_cons_succ, List.getD_cons_zero] using hk c b s rfl
  · simp only [List.getD_cons_succ]
    exact h i (by simp at hi; omega)

/-! ### Two non-adjacent ears and the last corner of a reflex chain -/

/-- **Two non-adjacent ears.**  Every simple polygon with at least four vertices has two ear
apexes `p ≠ q` that are not adjacent. -/
theorem exists_two_ears {Q : Polygon} (hQ : Q.Simple) (h4 : 4 ≤ Q.n) :
    ∃ p q, p < Q.n ∧ q < Q.n ∧ IsEar Q p ∧ IsEar Q q ∧ p ≠ q ∧
      (p + 1) % Q.n ≠ q ∧ (q + 1) % Q.n ≠ p := by
  obtain ⟨s, L, hd, hin⟩ := exists_diagonal hQ h4
  have hn : 0 < Q.n := by omega
  have hLn : L + 2 ≤ Q.n := hd.2.1
  obtain ⟨k₁, hk₁0, hk₁, he₁⟩ := exists_ear_in_arc Q hQ hd hin
  have hd' := isDiagonal_compl Q s L hd
  have hin' : Chazelle.segment (Q.vtx ((s + L) % Q.n % Q.n))
      (Q.vtx (((s + L) % Q.n + (Q.n - L)) % Q.n)) ⊆ Q.filled := by
    rwa [Nat.mod_mod, compl_arc_last_index Q s L (by omega), segment_comm]
  obtain ⟨k₂, hk₂0, hk₂, he₂⟩ := exists_ear_in_arc Q hQ hd' hin'
  rw [compl_arc_index, Nat.add_assoc] at he₂
  refine ⟨(s + k₁) % Q.n, (s + (L + k₂)) % Q.n, Nat.mod_lt _ hn, Nat.mod_lt _ hn, he₁, he₂,
    ?_, ?_, ?_⟩
  · intro h
    have := rot_index_inj (n := Q.n) (s := s) (i := k₁) (j := L + k₂) (by omega) (by omega) h
    omega
  · intro h
    rw [mod_add_one_mod] at h
    have := rot_index_inj (n := Q.n) (s := s) (i := k₁ + 1) (j := L + k₂) (by omega) (by omega) h
    omega
  · intro h
    rw [mod_add_one_mod] at h
    rcases Nat.lt_or_ge (L + k₂ + 1) Q.n with hlt | hge
    · have := rot_index_inj (n := Q.n) (s := s) (i := L + k₂ + 1) (j := k₁) hlt (by omega) h
      omega
    · have hEq : L + k₂ + 1 = Q.n := by omega
      rw [hEq, Nat.add_mod_right] at h
      have := rot_index_inj (n := Q.n) (s := s) (i := 0) (j := k₁) hn (by omega)
        (by rwa [Nat.add_zero])
      omega

/-- **The last corner of a reflex chain is convex.**  If every corner at positions
`1, …, n - 3` of a simple polygon `Q` (with `n ≥ 4`) is not strictly convex on the interior side,
then the corner at position `n - 2` is. -/
theorem convex_last_of_reflex {Q : Polygon} (hQ : Q.Simple) (h4 : 4 ≤ Q.n)
    (hreflex : ∀ j, 1 ≤ j → j + 3 ≤ Q.n →
      orient Q * det (Q.vtx (j - 1)) (Q.vtx j) (Q.vtx (j + 1)) ≤ 0) :
    0 < orient Q * det (Q.vtx (Q.n - 3)) (Q.vtx (Q.n - 2)) (Q.vtx (Q.n - 1)) := by
  have key : ∀ p, p < Q.n → IsEar Q p → p = Q.n - 2 ∨ p = 0 ∨ p = Q.n - 1 := by
    intro p hp he
    by_contra hcon
    simp only [not_or] at hcon
    have hpos := orient_det_pos_of_isEar hQ hp he
    rw [prevIdx_eq Q hp, ite_eq_right hcon.2.1, Nat.mod_eq_of_lt (by omega)] at hpos
    have := hreflex p (by omega) (by omega)
    linarith
  have conv : ∀ p, p < Q.n → IsEar Q p → p = Q.n - 2 →
      0 < orient Q * det (Q.vtx (Q.n - 3)) (Q.vtx (Q.n - 2)) (Q.vtx (Q.n - 1)) := by
    intro p hp he hpe
    subst hpe
    have := orient_det_pos_of_isEar hQ hp he
    rwa [prevIdx_eq Q hp, ite_eq_right (by omega), Nat.mod_eq_of_lt (by omega),
      show Q.n - 2 - 1 = Q.n - 3 by omega, show Q.n - 2 + 1 = Q.n - 1 by omega] at this
  obtain ⟨p, q, hp, hq, hep, heq, hpq, hpq1, hqp1⟩ := exists_two_ears hQ h4
  rcases key p hp hep with h | h | h
  · exact conv p hp hep h
  · rcases key q hq heq with h' | h' | h'
    · exact conv q hq heq h'
    · omega
    · exfalso; apply hqp1; rw [h', h, show Q.n - 1 + 1 = Q.n by omega, Nat.mod_self]
  · rcases key q hq heq with h' | h' | h'
    · exact conv q hq heq h'
    · exfalso; apply hpq1; rw [h', h, show Q.n - 1 + 1 = Q.n by omega, Nat.mod_self]
    · omega

/-! ### The stack algorithm -/

/-- The index list of the remaining polygon: the stack (top first) reversed, followed by the
unprocessed vertices `k, …, n - 1`. -/
def stackList (s : List ℕ) (k : ℕ) : List ℕ := s.reverse ++ List.range' k (P.n - k)

theorem stackList_cons_cons {k : ℕ} (hk : k < P.n) (c b : ℕ) (rest : List ℕ) :
    stackList P (c :: b :: rest) k =
      rest.reverse ++ b :: c :: k :: List.range' (k + 1) (P.n - (k + 1)) := by
  simp [stackList, show P.n - k = P.n - (k + 1) + 1 by omega, List.range'_succ]

theorem stackList_cons {k : ℕ} (hk : k < P.n) (c : ℕ) (rest : List ℕ) :
    stackList P (c :: rest) k =
      rest.reverse ++ c :: k :: List.range' (k + 1) (P.n - (k + 1)) := by
  simp [stackList, show P.n - k = P.n - (k + 1) + 1 by omega, List.range'_succ]

theorem stackList_push {k : ℕ} (hk : k < P.n) (s : List ℕ) :
    stackList P (k :: s) (k + 1) = stackList P s k := by
  simp [stackList, show P.n - k = P.n - (k + 1) + 1 by omega, List.range'_succ]

theorem stackList_last (hn : 1 ≤ P.n) (s : List ℕ) :
    stackList P s (P.n - 1) = s.reverse ++ [P.n - 1] := by
  simp [stackList, show P.n - (P.n - 1) = 1 by omega, List.range'_succ]

theorem length_stackList (s : List ℕ) (k : ℕ) :
    (stackList P s k).length = s.length + (P.n - k) := by
  simp [stackList]

open Classical in
/-- **The pop loop** at vertex `k`: while the stack (top first) has two entries `c, b` and the
corner `(b, c, k)` is strictly convex on the interior side, pop `c` and emit `(b, c, k)`.
Returns the emitted triangles, the new stack and the number of corner tests. -/
noncomputable def popLoop (σ : ℝ) (k : ℕ) : List ℕ → List Polygon.Triangle × List ℕ × ℕ
  | c :: b :: rest =>
    if 0 < σ * det (P.vtx b) (P.vtx c) (P.vtx k) then
      ((b, c, k) :: (popLoop σ k (b :: rest)).1, (popLoop σ k (b :: rest)).2.1,
        (popLoop σ k (b :: rest)).2.2 + 1)
    else ([], c :: b :: rest, 1)
  | s => ([], s, 0)

theorem popLoop_nil (σ : ℝ) (k : ℕ) : popLoop P σ k [] = ([], [], 0) := by
  simp [popLoop]

theorem popLoop_singleton (σ : ℝ) (k x : ℕ) : popLoop P σ k [x] = ([], [x], 0) := by
  simp [popLoop]

open Classical in
theorem popLoop_cons_cons (σ : ℝ) (k c b : ℕ) (rest : List ℕ) :
    popLoop P σ k (c :: b :: rest) =
      if 0 < σ * det (P.vtx b) (P.vtx c) (P.vtx k) then
        ((b, c, k) :: (popLoop P σ k (b :: rest)).1, (popLoop P σ k (b :: rest)).2.1,
          (popLoop P σ k (b :: rest)).2.2 + 1)
      else ([], c :: b :: rest, 1) := by
  rw [popLoop]

/-- **The walk** over the vertices `k, k + 1, …, n - 1`: run the pop loop, push the vertex,
continue.  Returns the emitted triangles, the final stack and the number of corner tests. -/
noncomputable def walk (σ : ℝ) : ℕ → List ℕ → List Polygon.Triangle × List ℕ × ℕ
  | k, s =>
    if _h : k < P.n then
      ((popLoop P σ k s).1 ++ (walk σ (k + 1) (k :: (popLoop P σ k s).2.1)).1,
        (walk σ (k + 1) (k :: (popLoop P σ k s).2.1)).2.1,
        (popLoop P σ k s).2.2 + (walk σ (k + 1) (k :: (popLoop P σ k s).2.1)).2.2)
    else ([], s, 0)
termination_by k _ => P.n - k
decreasing_by all_goals omega

theorem walk_of_lt (σ : ℝ) {k : ℕ} (hk : k < P.n) (s : List ℕ) :
    walk P σ k s =
      ((popLoop P σ k s).1 ++ (walk P σ (k + 1) (k :: (popLoop P σ k s).2.1)).1,
        (walk P σ (k + 1) (k :: (popLoop P σ k s).2.1)).2.1,
        (popLoop P σ k s).2.2 + (walk P σ (k + 1) (k :: (popLoop P σ k s).2.1)).2.2) := by
  rw [walk, dite_eq_left hk]

theorem walk_of_le (σ : ℝ) {k : ℕ} (hk : P.n ≤ k) (s : List ℕ) : walk P σ k s = ([], s, 0) := by
  rw [walk, dite_eq_right (by omega)]

/-- **The mountain triangulation**: the triangles emitted by the walk started with the stack
`[1, 0]` at vertex `2`, using the sign `σ` for the convexity tests. -/
noncomputable def mountainTriangulation (σ : ℝ) : List Polygon.Triangle := (walk P σ 2 [1, 0]).1

/-- The number of corner tests performed by the walk. -/
noncomputable def mountainTests (σ : ℝ) : ℕ := (walk P σ 2 [1, 0]).2.2

/-! ### Specification of the pop loop -/

/-- **Specification of the pop loop** at a vertex `k < n`, from a nonempty reflex stack `s`
whose remaining polygon satisfies the invariant: the new stack is nonempty and, with `k`
pushed, reflex; one triangle is emitted per pop; the number of tests is at most one more than
the number of pops; the invariant persists (as long as three vertices remain); and the
emitted triangles extend any relabelled weak triangulation of the new remaining polygon to one
of the old. -/
theorem popLoop_spec {σ : ℝ} (hσ : σ = orient P) {k : ℕ} (hk : k < P.n) :
    ∀ s : List ℕ, s ≠ [] → Inv P (stackList P s k) → ReflexIdx P σ s →
      (popLoop P σ k s).2.1 ≠ [] ∧
      ReflexIdx P σ (k :: (popLoop P σ k s).2.1) ∧
      (popLoop P σ k s).1.length + (popLoop P σ k s).2.1.length = s.length ∧
      (popLoop P σ k s).2.2 ≤ (popLoop P σ k s).1.length + 1 ∧
      (3 ≤ (stackList P (popLoop P σ k s).2.1 k).length →
        Inv P (stackList P (popLoop P σ k s).2.1 k)) ∧
      ∀ T, GoodTri P (stackList P (popLoop P σ k s).2.1 k) T →
        GoodTri P (stackList P s k) ((popLoop P σ k s).1 ++ T) := by
  intro s
  induction s with
  | nil => intro h; exact absurd rfl h
  | cons c s' ih =>
    intro _ hI hR
    rcases s' with _ | ⟨b, rest⟩
    · rw [popLoop_singleton]
      refine ⟨List.cons_ne_nil _ _, ?_, by simp, by simp, fun _ => hI, fun T hT => by simpa using hT⟩
      exact reflexIdx_push P hR k (fun c' b' rest' h => by simp at h)
    · rw [popLoop_cons_cons]
      split_ifs with hconv
      · -- a pop
        rw [stackList_cons_cons P hk] at hI ⊢
        set R := List.range' (k + 1) (P.n - (k + 1)) with hRdef
        by_cases h4 : 4 ≤ (rest.reverse ++ b :: c :: k :: R).length
        · have he := isEar_of_convex_corner P rest.reverse b c k R hI h4 (hσ ▸ hconv)
          have hI' := inv_pop P rest.reverse b c k R hI h4 he
          have hI'' : Inv P (stackList P (b :: rest) k) := by
            rwa [stackList_cons P hk]
          obtain ⟨h1, h2, h3, h4', h5, h6⟩ :=
            ih (List.cons_ne_nil _ _) hI'' (reflexIdx_pop P hR)
          refine ⟨h1, h2, by simp only [List.length_cons] at h3 ⊢; omega, by simp; omega, h5, ?_⟩
          intro T hT
          have := h6 T hT
          rw [stackList_cons P hk] at this
          rw [List.cons_append]
          exact goodTri_pop P rest.reverse b c k R hI.2.2.2.1 he this
        · -- the remaining polygon is a triangle: `rest = []`, `R = []`
          have hlen : (rest.reverse ++ b :: c :: k :: R).length = rest.length + 3 + R.length := by
            simp; omega
          have hrest : rest = [] := by
            rw [← List.length_eq_zero_iff]; omega
          have hlenR : R.length = P.n - (k + 1) := by rw [hRdef, List.length_range']
          have hnk : P.n - k = 1 := by omega
          subst hrest
          rw [popLoop_singleton]
          refine ⟨List.cons_ne_nil _ _, ?_, by simp, by simp, ?_, ?_⟩
          · intro i hi; simp at hi
          · intro h3; rw [length_stackList, hnk] at h3; simp at h3
          · intro T hT
            have := three_le_length_of_goodTri P hT
            rw [length_stackList, hnk] at this; simp at this
      · -- no pop
        refine ⟨List.cons_ne_nil _ _, ?_, by simp, by simp, fun _ => hI, fun T hT => by simpa using hT⟩
        refine reflexIdx_push P hR k ?_
        intro c' b' rest' h
        cases h
        exact not_lt.1 hconv

/-- **The pop loop at the last vertex empties the stack**: from a reflex stack with at least
two entries whose remaining polygon (with the last vertex `n - 1`) satisfies the invariant,
the loop pops everything but the bottom, and the emitted triangles form a relabelled weak
triangulation of the remaining polygon. -/
theorem popLoop_last {σ : ℝ} (hσ : σ = orient P) :
    ∀ s : List ℕ, 2 ≤ s.length → Inv P (stackList P s (P.n - 1)) → ReflexIdx P σ s →
      (popLoop P σ (P.n - 1) s).2.1.length = 1 ∧
      GoodTri P (stackList P s (P.n - 1)) (popLoop P σ (P.n - 1) s).1 := by
  intro s
  induction s with
  | nil => intro h; simp at h
  | cons c s' ih =>
    intro hlen hI hR
    rcases s' with _ | ⟨b, rest⟩
    · simp at hlen
    have hn : 1 ≤ P.n := by
      have := hI.2.1 b (by simp [stackList])
      omega
    have hl : stackList P (c :: b :: rest) (P.n - 1) = rest.reverse ++ b :: c :: [P.n - 1] := by
      rw [stackList_last P hn]; simp
    have hl' : stackList P (b :: rest) (P.n - 1) = rest.reverse ++ b :: [P.n - 1] := by
      rw [stackList_last P hn]; simp
    rw [hl] at hI ⊢
    have hQ : (subPoly P (rest.reverse ++ b :: c :: [P.n - 1])).Simple := hI.2.2.2.1
    have hor : orient (subPoly P (rest.reverse ++ b :: c :: [P.n - 1])) = orient P :=
      hI.2.2.2.2.2
    -- the corner `(b, c, n - 1)` is strictly convex
    have hconv : 0 < orient P * det (P.vtx b) (P.vtx c) (P.vtx (P.n - 1)) := by
      rcases rest with _ | ⟨a, rest'⟩
      · have h3 := orient_det_pos_of_three hQ (by simp)
        rwa [hor, vtx_subPoly_getD P _ (by simp), vtx_subPoly_getD P _ (by simp),
          vtx_subPoly_getD P _ (by simp)] at h3
      · set l := (a :: rest').reverse ++ b :: c :: [P.n - 1] with hldef
        set Q := subPoly P l with hQdef
        have hlen4 : 4 ≤ l.length := by simp [hldef]
        have hQn : Q.n = l.length := n_subPoly P l
        have hreflex : ∀ j, 1 ≤ j → j + 3 ≤ Q.n →
            orient Q * det (Q.vtx (j - 1)) (Q.vtx j) (Q.vtx (j + 1)) ≤ 0 := by
          intro j hj1 hj3
          rw [hQn] at hj3
          have hl2 : l = (c :: b :: a :: rest').reverse ++ [P.n - 1] := by
            rw [hldef]; simp
          set s := c :: b :: a :: rest'
          have hsl : l.length = s.length + 1 := by rw [hl2]; simp
          have hget : ∀ i, i < s.length → l.getD i 0 = s.getD (s.length - 1 - i) 0 := by
            intro i hi
            rw [hl2, getD_append_of_lt _ _ (by rwa [List.length_reverse]), getD_reverse s hi]
          rw [hQdef, vtx_subPoly_getD P l (by omega), vtx_subPoly_getD P l (by omega),
            vtx_subPoly_getD P l (by omega), hget _ (by omega), hget _ (by omega),
            hget _ (by omega), ← hQdef, hor, hσ.symm]
          have := hR (s.length - 2 - j) (by omega)
          rwa [show s.length - 2 - j + 2 = s.length - 1 - (j - 1) by omega,
            show s.length - 2 - j + 1 = s.length - 1 - j by omega,
            show s.length - 2 - j = s.length - 1 - (j + 1) by omega] at this
        have key := convex_last_of_reflex hQ (by rwa [hQn]) hreflex
        have hlen3 : l.length = (a :: rest').reverse.length + 3 := by simp [hldef]
        rwa [hor, hQn, hlen3, hQdef, vtx_subPoly_getD P l (by omega), vtx_subPoly_getD P l (by omega),
          vtx_subPoly_getD P l (by omega),
          show (a :: rest').reverse.length + 3 - 3 = (a :: rest').reverse.length by omega,
          show (a :: rest').reverse.length + 3 - 2 = (a :: rest').reverse.length + 1 by omega,
          show (a :: rest').reverse.length + 3 - 1 = (a :: rest').reverse.length + 2 by omega,
          hldef, getD_append_length, getD_append_cons, getD_append_cons] at key
    rw [popLoop_cons_cons, ite_eq_left (hσ ▸ hconv)]
    rcases rest with _ | ⟨a, rest'⟩
    · rw [popLoop_singleton]
      refine ⟨rfl, ?_⟩
      have := goodTri_triangle P hQ (l := [b, c, P.n - 1]) rfl
      simpa using this
    · have h4 : 4 ≤ ((a :: rest').reverse ++ b :: c :: [P.n - 1]).length := by simp
      have he := isEar_of_convex_corner P (a :: rest').reverse b c (P.n - 1) [] hI h4 hconv
      have hI' := inv_pop P (a :: rest').reverse b c (P.n - 1) [] hI h4 he
      rw [← hl'] at hI'
      obtain ⟨h1, h2⟩ := ih (by simp) hI' (reflexIdx_pop P hR)
      rw [hl'] at h2
      exact ⟨h1, goodTri_pop P _ b c (P.n - 1) [] hQ he h2⟩

/-! ### Specification of the walk -/

/-- **Specification of the walk** from a vertex `k < n` and a nonempty reflex stack whose
remaining polygon satisfies the invariant: the emitted triangles form a relabelled weak
triangulation of the remaining polygon, and the number of tests is at most the number of
emitted triangles plus `n - k`. -/
theorem walk_spec {σ : ℝ} (hσ : σ = orient P) :
    ∀ (d k : ℕ) (s : List ℕ), P.n - k = d → k < P.n → s ≠ [] →
      Inv P (stackList P s k) → ReflexIdx P σ s →
      GoodTri P (stackList P s k) (walk P σ k s).1 ∧
      (walk P σ k s).2.2 ≤ (walk P σ k s).1.length + (P.n - k) := by
  intro d
  induction d with
  | zero => intro k s hd hk; omega
  | succ d ih =>
    intro k s hd hk hs hI hR
    rw [walk_of_lt P σ hk]
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := popLoop_spec P hσ hk s hs hI hR
    rcases Nat.lt_or_ge (k + 1) P.n with hk1 | hk1
    · have hI' : Inv P (stackList P (k :: (popLoop P σ k s).2.1) (k + 1)) := by
        rw [stackList_push P hk]
        apply h5
        rw [length_stackList]
        have : 0 < (popLoop P σ k s).2.1.length := List.length_pos_of_ne_nil h1
        omega
      obtain ⟨g1, g2⟩ := ih (k + 1) _ (by omega) hk1 (List.cons_ne_nil _ _) hI' h2
      rw [stackList_push P hk] at g1
      refine ⟨h6 _ g1, ?_⟩
      simp only [List.length_append]
      omega
    · obtain rfl : k = P.n - 1 := by omega
      rw [walk_of_le P σ (by omega)]
      have hs2 : 2 ≤ s.length := by
        have := hI.2.2.1
        rw [length_stackList] at this
        omega
      obtain ⟨-, g2⟩ := popLoop_last P hσ s hs2 hI hR
      refine ⟨by simpa using g2, ?_⟩
      simp only [List.append_nil, Nat.add_zero]
      omega

/-! ### Monotone mountains -/

/-- **A monotone mountain**: a simple polygon whose vertex chain `v₀, …, v_{n-1}` is strictly
increasing for the `(y, x)`-lexicographic order (the closing edge `v_{n-1} v₀` is the base). -/
def IsMountain (P : Polygon) : Prop :=
  P.Simple ∧ ∀ i, i + 1 < P.n → ylexLT (P.vtx i) (P.vtx (i + 1))

/-- The chain of a mountain is `ylexLT`-increasing between any two indices. -/
theorem ylexLT_of_lt (hM : IsMountain P) {i j : ℕ} (hij : i < j) (hj : j < P.n) :
    ylexLT (P.vtx i) (P.vtx j) := by
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d + 1 := ⟨j - i - 1, by omega⟩
  induction d with
  | zero => exact hM.2 i (by omega)
  | succ d ihd =>
    exact ylexLT_trans (ihd (by omega) (by omega))
      (hM.2 (i + d + 1) (by omega))

/-- The initial index list `List.range P.n` satisfies the invariant. -/
theorem inv_range (hM : IsMountain P) : Inv P (List.range P.n) := by
  have hP := hM.1
  refine ⟨List.nodup_range, fun x hx => List.mem_range.1 hx,
    by rw [List.length_range]; exact hP.1, by rwa [subPoly_range], ?_,
    by rw [subPoly_range]⟩
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [List.getElem_range]
  rw [List.length_range] at hj
  exact ylexLT_of_lt P hM hij hj

/-- The initial remaining polygon is `P` itself. -/
theorem stackList_init (h2 : 2 ≤ P.n) : stackList P [1, 0] 2 = List.range P.n := by
  obtain ⟨m, hm⟩ : ∃ m, P.n = m + 2 := ⟨P.n - 2, by omega⟩
  simp [stackList, hm, List.range_eq_range', List.range'_succ]

/-- **Correctness and cost of the walk on a mountain** (with `σ = orient P`). -/
theorem mountain_goodTri (hM : IsMountain P) {σ : ℝ} (hσ : σ = orient P) :
    GoodTri P (List.range P.n) (mountainTriangulation P σ) ∧
      mountainTests P σ ≤ (mountainTriangulation P σ).length + (P.n - 2) := by
  have h3 : 3 ≤ P.n := hM.1.1
  have := walk_spec P hσ (P.n - 2) 2 [1, 0] rfl (by omega) (List.cons_ne_nil _ _)
    (by rw [stackList_init P (by omega)]; exact inv_range P hM)
    (fun i hi => by simp at hi)
  rwa [stackList_init P (by omega)] at this

/-- **The stack algorithm weakly triangulates a monotone mountain.** -/
theorem mountain_weakTriangulates (hM : IsMountain P) {σ : ℝ} (hσ : σ = orient P) :
    WeakTriangulates P (mountainTriangulation P σ) :=
  weakTriangulates_of_goodTri_range P (mountain_goodTri P hM hσ).1

/-- **The stack algorithm triangulates a monotone mountain**: for a mountain `P` and the
orientation sign `σ = orient P`, `mountainTriangulation P σ` is a triangulation of `P`. -/
theorem mountain_triangulates (hM : IsMountain P) {σ : ℝ} (hσ : σ = orient P) :
    P.Triangulates (mountainTriangulation P σ) :=
  triangulates_of_weak (mountain_weakTriangulates P hM hσ)

/-- The mountain triangulation has `n - 2` triangles. -/
theorem length_mountainTriangulation (hM : IsMountain P) {σ : ℝ} (hσ : σ = orient P) :
    (mountainTriangulation P σ).length = P.n - 2 := by
  have := (mountain_weakTriangulates P hM hσ).2.1
  omega

/-- **Operation count**: the walk performs at most `2 * n - 4` corner tests. -/
theorem mountainTests_le_sub (hM : IsMountain P) {σ : ℝ} (hσ : σ = orient P) :
    mountainTests P σ ≤ 2 * P.n - 4 := by
  have h1 := (mountain_goodTri P hM hσ).2
  have h2 := length_mountainTriangulation P hM hσ
  have h3 : 3 ≤ P.n := hM.1.1
  omega

/-- **Operation count**: the walk performs at most `2 * n` corner tests. -/
theorem mountainTests_le (hM : IsMountain P) {σ : ℝ} (hσ : σ = orient P) :
    mountainTests P σ ≤ 2 * P.n := by
  have := mountainTests_le_sub P hM hσ
  omega

end

end Chazelle.Mountain
