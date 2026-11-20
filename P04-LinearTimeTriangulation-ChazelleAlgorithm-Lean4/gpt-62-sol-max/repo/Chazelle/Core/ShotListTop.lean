module

public import Chazelle.Core.ShotListLev

/-!
# Shooting at a list of arcs with holes, part 8: holes and pieces

* `holesFrom`: the holes of the levels from `ℓ` on, read in the registers; `levLeaves_eq`: the
  pieces of the recursion are the pieces `leaves` of `ShotListMath`.
* `holeList`, `arcAt`, `hiSet`, `loSet`: the vocabulary of the contract; `pcSet_leaves_sub`,
  `loSet_sub`, `leaf_wt`, `leaf_avoid`: the pieces lie in the arcs, cover the arcs outside the
  closed holes, have weight at most the arc's and avoid the origin.
-/

namespace Chazelle.Core

namespace ShotList

open Machine Machine.Stmt Programs SignK SweepPrim
open Chazelle.Chain (sideInArc)

@[expose] public section

/-! ## The holes -/

/-- The hole `j` in the registers. -/
def holeAt (c : Config) (R j : ℕ) : WPos × WPos :=
  (⟨c.nreg (R + 10 + 2 * j), 0⟩, ⟨c.nreg (R + 11 + 2 * j), 0⟩)

/-- The holes of the levels from `ℓ` on (`f` levels). -/
def holesFrom (c : Config) (R : ℕ) : ℕ → ℕ → List (WPos × WPos)
  | 0, _ => []
  | f + 1, ℓ => if c.nreg (R + 30 + ℓ) < c.nreg (R + 9) then holeAt c R ℓ :: holesFrom c R f (ℓ + 1)
      else []

/-- **The pieces of the recursion are the pieces of the holes**, if the level constants hold
(`R + 30 + ℓ` holds `ℓ`). -/
theorem levLeaves_eq (M : Model) (Q : Polygon) (c : Config) (R : ℕ)
    (hk : ∀ ℓ, ℓ ≤ 3 → c.nreg (R + 30 + ℓ) = ℓ) :
    ∀ f ℓ, f + ℓ ≤ 3 → ∀ q, levLeaves M Q c R f ℓ q = leaves (M.key Q) (holesFrom c R f ℓ) q
  | 0, _, _, q => by rfl
  | f + 1, ℓ, hf, q => by
    simp only [levLeaves, holesFrom]
    by_cases hp : c.nreg (R + 30 + ℓ) < c.nreg (R + 9)
    · simp only [levPieces, ite_yes _ _ hp, leaves]
      congr 1
      funext p
      exact levLeaves_eq M Q c R hk f (ℓ + 1) (by omega) p
    · simp only [levPieces, ite_no _ _ hp, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [levLeaves_eq M Q c R hk f (ℓ + 1) (by omega) q]
      have : holesFrom c R f (ℓ + 1) = [] := by
        cases f with
        | zero => rfl
        | succ f =>
          simp only [holesFrom]
          have h1 := hk ℓ (by omega)
          have h2 := hk (ℓ + 1) (by omega)
          rw [show R + 30 + (ℓ + 1) = R + 30 + ℓ + 1 by omega] at h2 ⊢
          rw [ite_no]; omega
      rw [this]

/-- The holes of the contract: the first `min H 3` pairs. -/
def holeList (c : Config) (R : ℕ) : List (WPos × WPos) :=
  (List.range (min (c.nreg (R + 9)) 3)).map (holeAt c R)

/-- The holes of the recursion from level `0` are the holes of the contract. -/
theorem holesFrom_eq (c : Config) (R : ℕ) (hk : ∀ ℓ, ℓ ≤ 3 → c.nreg (R + 30 + ℓ) = ℓ) :
    holesFrom c R 3 0 = holeList c R := by
  have h0 := hk 0 (by omega)
  have h1 := hk 1 (by omega)
  have h2 := hk 2 (by omega)
  simp only [holesFrom, holeList, Nat.add_zero] at h0 ⊢
  rw [show R + 30 + (0 + 1) = R + 30 + 1 by omega, show R + 30 + (0 + 1 + 1) = R + 30 + 2 by omega]
  rw [h0, h1, h2]
  rcases Nat.lt_or_ge (c.nreg (R + 9)) 1 with hH | hH
  · simp_all
  rcases Nat.lt_or_ge (c.nreg (R + 9)) 2 with hH2 | hH2
  · ram_finish [ite_yes, ite_no, show min (c.nreg (R + 9)) 3 = 1 by omega]
  rcases Nat.lt_or_ge (c.nreg (R + 9)) 3 with hH3 | hH3
  · ram_finish [ite_yes, ite_no, show min (c.nreg (R + 9)) 3 = 2 by omega]
  · ram_finish [ite_yes, show min (c.nreg (R + 9)) 3 = 3 by omega]

/-! ## The vocabulary of the contract -/

/-- Arc `j` of the list at `A` (four words: start edge and height code, end edge and height
code). -/
def arcAt (m : ℕ → ℕ) (A j : ℕ) : WPos × WPos :=
  (⟨m (A + 4 * j), m (A + 4 * j + 1)⟩, ⟨m (A + 4 * j + 2), m (A + 4 * j + 3)⟩)

/-- The points of the arcs. -/
def hiSet (M : Model) (Q : Polygon) (m : ℕ → ℕ) (A K : ℕ) : Set Point :=
  ⋃ j ∈ Finset.range K, M.arcSet (M.key Q (arcAt m A j).1) (M.key Q (arcAt m A j).2)

/-- The points of the arcs at a key outside every closed hole. -/
def loSet (M : Model) (Q : Polygon) (m : ℕ → ℕ) (A K : ℕ) (hs : List (WPos × WPos)) :
    Set Point :=
  {x | ∃ p : ℕ, ∃ t : ℝ, p < M.W.n ∧ 0 ≤ t ∧ t ≤ 1 ∧
    (∃ j < K, CIn (M.key Q (arcAt m A j).1) (M.key Q (arcAt m A j).2) (p + t)) ∧
    (∀ g ∈ hs, ¬ CIn (M.key Q g.1) (M.key Q g.2) (p + t)) ∧
    x = Geometry.lerp (M.wa p) (M.wb p) t}

theorem arcSet_iff (M : Model) (a b : ℝ) (x : Point) :
    x ∈ M.arcSet a b ↔ ∃ p : ℕ, ∃ t : ℝ, p < M.W.n ∧ 0 ≤ t ∧ t ≤ 1 ∧ CIn a b (p + t) ∧
      x = Geometry.lerp (M.wa p) (M.wb p) t := by
  rfl

section

variable (M : Model) (Q : Polygon) {hs : List (WPos × WPos)}
include M Q hs

/-- Keys of vertex holes. -/
theorem holesOK_of
    (h : ∀ g ∈ hs, g.1.hgt = 0 ∧ g.2.hgt = 0 ∧ g.1.edge ≠ g.2.edge) : HolesOK (M.key Q) hs := by
  intro g hg
  obtain ⟨h1, h2, h3⟩ := h g hg
  obtain ⟨⟨e1, k1⟩, ⟨e2, k2⟩⟩ := g
  simp only at h1 h2 h3
  subst h1; subst h2
  rw [key_vtx, key_vtx]
  exact_mod_cast h3

/-- **The pieces lie in the arc.** -/
theorem pcSet_leaves_sub
    (hh : HolesOK (M.key Q) hs) (q : WPos × WPos) :
    pcSet M Q (leaves (M.key Q) hs q) ⊆ M.arcSet (M.key Q q.1) (M.key Q q.2) := by
  intro x hx
  simp only [pcSet, Set.mem_iUnion] at hx
  obtain ⟨p, hp, hx⟩ := hx
  obtain ⟨p', t, h1, h2, h3, h4, h5⟩ := (arcSet_iff M _ _ x).1 hx
  exact (arcSet_iff M _ _ x).2 ⟨p', t, h1, h2, h3, (leaves_sub (M.key Q) hh hp h4).1, h5⟩

/-- **The pieces cover the arc outside the closed holes.** -/
theorem mem_pcSet_leaves
    (hh : HolesOK (M.key Q) hs) (q : WPos × WPos) {p : ℕ} {t : ℝ} (hp : p < M.W.n) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hq : CIn (M.key Q q.1) (M.key Q q.2) (p + t))
    (hno : ∀ g ∈ hs, ¬ CIn (M.key Q g.1) (M.key Q g.2) (p + t)) :
    Geometry.lerp (M.wa p) (M.wb p) t ∈ pcSet M Q (leaves (M.key Q) hs q) := by
  obtain ⟨u, hu, hu'⟩ := leaves_cover (M.key Q) hh hq hno
  simp only [pcSet, Set.mem_iUnion]
  exact ⟨u, hu, (arcSet_iff M _ _ _).2 ⟨p, t, hp, ht0, ht1, hu', rfl⟩⟩

/-- **A piece weighs at most its arc.** -/
theorem leaf_wt (hh : HolesOK (M.key Q) hs)
    {q u : WPos × WPos} (hu : u ∈ leaves (M.key Q) hs q) :
    M.arcWt (M.key Q u.1) (M.key Q u.2) ≤ M.arcWt (M.key Q q.1) (M.key Q q.2) :=
  M.arcWt_mono fun _ hk => leaves_open (M.key Q) hh hu hk

/-- **A piece avoids the origin**, if every position of the origin in the arc is inside a hole. -/
theorem leaf_avoid
    (hh : HolesOK (M.key Q) hs) {q u : WPos × WPos} (hu : u ∈ leaves (M.key Q) hs q) {z : Point}
    (hz : ∀ p : ℕ, ∀ t : ℝ, p < M.W.n → 0 ≤ t → t ≤ 1 → Geometry.lerp (M.wa p) (M.wb p) t = z →
      CIn (M.key Q q.1) (M.key Q q.2) (p + t) → ∃ g ∈ hs, sideInArc (M.key Q g.1) (M.key Q g.2) (p + t)) :
    z ∉ M.arcSet (M.key Q u.1) (M.key Q u.2) := by
  intro hmem
  obtain ⟨p, t, h1, h2, h3, h4, h5⟩ := (arcSet_iff M _ _ z).1 hmem
  obtain ⟨hq, hno⟩ := leaves_sub (M.key Q) hh hu h4
  obtain ⟨g, hg, hg'⟩ := hz p t h1 h2 h3 h5.symm hq
  exact hno g hg hg'

end

end

end ShotList

end Chazelle.Core
