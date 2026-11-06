module

public meta import Chazelle.Arithmetic

public import Chazelle.Existence.SplitDiagonal
public import Chazelle.Existence.Base

/-!
# Ears of a simple polygon

For a simple polygon `P` with `n ≥ 4`, an *ear* at vertex `i` is the triangle
`(prev i, i, next i)` (indices mod `n`) such that the chord from `prev i` to `next i` is an
interior diagonal:

  `IsEar P i := IsDiagonal P (prevIdx P i) 2 ∧ segment (vtx (prev i)) (vtx (next i)) ⊆ P.filled`.

The ear arc `P.arc (prevIdx P i) 2` is the ear triangle; the complementary arc
`clip P i = P.arc ((prevIdx P i + 2) % n) (n - 2)` is the polygon with vertex `i` removed.

* `n_clip`, `vtx_clip`: the clipped polygon has `n - 1` vertices, `vtx k = P.vtx ((i + 1 + k) % n)`.
* `simple_clip`: clipping an ear preserves simplicity.
* `validTriangle_ear`: the ear triangle is a valid (nondegenerate) triangle of `P`.
* `weakTriangulates_clip`: a weak triangulation of `clip P i`, relabelled, together with the ear
  triangle, weakly triangulates `P`.
-/

namespace Chazelle.Ears

@[expose] public section

open Chazelle.Jordan
open Chazelle.Existence

/-! ### Index bookkeeping -/

section
variable (P : Polygon) {i : ℕ} (hi : i < P.n)
include hi
/-- `prevIdx P i + 1 ≡ i` for `i < n`: the vertex after `prev i` is `i`. -/
theorem prevIdx_add_one_mod :
    (prevIdx P i + 1) % P.n = i :=
  prevIdx_succ P hi

/-- `prevIdx P i + 2 ≡ i + 1`. -/
theorem prevIdx_add_two_mod :
    (prevIdx P i + 2) % P.n = (i + 1) % P.n := by
  have h := prevIdx_add_one_mod P hi
  rw [show prevIdx P i + 2 = prevIdx P i + 1 + 1 by omega, ← Nat.mod_add_mod, h]

/-- `prevIdx P i + 2 + k ≡ i + 1 + k`. -/
theorem prevIdx_add_two_add_mod (k : ℕ) :
    ((prevIdx P i + 2) % P.n + k) % P.n = (i + 1 + k) % P.n := by
  rw [prevIdx_add_two_mod P hi, Nat.mod_add_mod]

/-- `prevIdx P i` reduced mod `n` is itself. -/
theorem prevIdx_mod : prevIdx P i % P.n = prevIdx P i :=
  Nat.mod_eq_of_lt (prevIdx_lt P hi)


end

section
variable (P : Polygon) (hn : 0 < P.n)
include hn
/-- The previous index of a reduced index. -/
theorem prevIdx_of_mod (a : ℕ) :
    prevIdx P (a % P.n) = (a + P.n - 1) % P.n := by
  unfold prevIdx
  have h1 : a % P.n + P.n - 1 = a % P.n + (P.n - 1) := by omega
  have h2 : a + P.n - 1 = a + (P.n - 1) := by omega
  simp_all

/-- The previous index of `(s + 1) % n` is `s % n`. -/
theorem prevIdx_succ_mod (s : ℕ) :
    prevIdx P ((s + 1) % P.n) = s % P.n := by
  rw [prevIdx_of_mod P hn, show s + 1 + P.n - 1 = s + P.n by omega, Nat.add_mod_right]


end

/-- A diagonal may be described by its reduced start index. -/
theorem isDiagonal_mod_iff (P : Polygon) (s L : ℕ) :
    IsDiagonal P (s % P.n) L ↔ IsDiagonal P s L := by
  unfold IsDiagonal
  rw [Nat.mod_mod, Nat.mod_add_mod]

/-! ### Ears -/

section
variable (P : Polygon) (i : ℕ)
include P i
/-- **An ear at vertex `i`**: the chord from `prev i` to `next i` is a diagonal of `P` (its open
part avoids the boundary) lying inside the filled region. -/
def IsEar : Prop :=
  IsDiagonal P (prevIdx P i) 2 ∧
    Chazelle.segment (P.vtx (prevIdx P i)) (P.vtx ((i + 1) % P.n)) ⊆ P.filled

/-- The polygon with vertex `i` removed: the complementary arc of the ear chord, with vertices
`next i, …, prev i`. -/
def clip : Polygon := P.arc ((prevIdx P i + 2) % P.n) (P.n - 2)

/-- The ear triangle `(prev i, i, next i)`. -/
def earTriangle : Polygon.Triangle :=
  (prevIdx P i, i, (i + 1) % P.n)


end

variable (P : Polygon) (i : ℕ)

section
variable (hi : i < P.n)
include hi
/-- The ear chord, in the form used by `IsDiagonal`. -/
theorem chord_ear_eq :
    Chazelle.segment (P.vtx (prevIdx P i % P.n)) (P.vtx ((prevIdx P i + 2) % P.n)) =
      Chazelle.segment (P.vtx (prevIdx P i)) (P.vtx ((i + 1) % P.n)) := by
  rw [prevIdx_mod P hi, prevIdx_add_two_mod P hi]

/-- The ear chord lies in the filled region, in the form used by `weakTriangulates_of_diagonal`. -/
theorem chord_ear_subset_filled (he : IsEar P i) :
    Chazelle.segment (P.vtx (prevIdx P i % P.n)) (P.vtx ((prevIdx P i + 2) % P.n)) ⊆ P.filled := by
  rw [chord_ear_eq P i hi]; exact he.2


end

/-- `n ≥ 4` whenever there is an ear. -/
theorem four_le_of_isEar (he : IsEar P i) : 4 ≤ P.n := he.1.2.1

/-- The clipped polygon has `n - 1` vertices. -/
theorem n_clip (hn : 2 ≤ P.n) : (clip P i).n = P.n - 1 := by
  core_grind [n_arc]

section
variable (hP : P.Simple) (he : IsEar P i)
include hP he
/-- **Clipping an ear preserves simplicity.** -/
theorem simple_clip : (clip P i).Simple :=
  simple_arc_compl P (prevIdx P i) 2 hP he.1

/-- The ear arc `P.arc (prevIdx P i) 2` is simple. -/
theorem simple_earArc : (P.arc (prevIdx P i) 2).Simple :=
  simple_arc P (prevIdx P i) 2 hP he.1


end

/-- The three vertices of the ear arc. -/
theorem vtx_earArc (hi : i < P.n) :
    (P.arc (prevIdx P i) 2).vtx 0 = P.vtx (prevIdx P i) ∧
    (P.arc (prevIdx P i) 2).vtx 1 = P.vtx i ∧
    (P.arc (prevIdx P i) 2).vtx 2 = P.vtx ((i + 1) % P.n) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [vtx_arc P _ _ (by norm_num : 0 ≤ 2), Nat.add_zero, prevIdx_mod P hi]
  · rw [vtx_arc P _ _ (by norm_num : 1 ≤ 2), prevIdx_add_one_mod P hi]
  · rw [vtx_arc P _ _ (le_rfl : 2 ≤ 2), prevIdx_add_two_mod P hi]

/-- **The ear triangle is nondegenerate.** -/
theorem det_ear_ne_zero (hP : P.Simple) (hi : i < P.n) (he : IsEar P i) :
    det (P.vtx (prevIdx P i)) (P.vtx i) (P.vtx ((i + 1) % P.n)) ≠ 0 := by
  have h := det_ne_zero_of_simple_three _ (simple_earArc P i hP he) (n_arc P _ _)
  obtain ⟨h0, h1, h2⟩ := vtx_earArc P i hi
  simp_all

/-- Relabelling the triangle `(0, 1, 2)` of the ear arc gives the ear triangle. -/
theorem relabel_ear (hi : i < P.n) :
    relabel (prevIdx P i) P.n (0, 1, 2) = earTriangle P i := by
  unfold relabel earTriangle
  simp only [Nat.add_zero, prevIdx_mod P hi, prevIdx_add_one_mod P hi, prevIdx_add_two_mod P hi]

/-- **Ear clipping preserves weak triangulations.**  A weak triangulation `T` of `clip P i`,
relabelled to the indices of `P` and preceded by the ear triangle, weakly triangulates `P`. -/
theorem weakTriangulates_clip (hP : P.Simple) (hi : i < P.n) (he : IsEar P i)
    {T : List Polygon.Triangle} (h : WeakTriangulates (clip P i) T) :
    WeakTriangulates P
      (earTriangle P i :: T.map (relabel ((prevIdx P i + 2) % P.n) P.n)) := by
  have h₁ : WeakTriangulates (P.arc (prevIdx P i) 2) [(0, 1, 2)] :=
    weakTriangulates_triangle _ (simple_earArc P i hP he) (n_arc P _ _)
  have := weakTriangulates_of_diagonal hP he.1 (chord_ear_subset_filled P i hi he) h₁ h
  rw [List.map_cons, List.map_nil, List.singleton_append, relabel_ear P i hi] at this
  exact this

end

end Chazelle.Ears
