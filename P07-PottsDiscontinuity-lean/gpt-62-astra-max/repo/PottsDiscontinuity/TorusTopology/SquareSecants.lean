module
public import PottsDiscontinuity.FK.Lattice
public import PottsDiscontinuity.TorusTopology.CompassWordTurning

/-! # A discrete secant proof of the turning theorem

As the ends of a secant move along two disjoint lattice edges, its winding
increment around the boundary of their parameter square is zero. Summing
these squares compares the turning tangent to the secants at a leftmost
vertex. All the latter are in one closed half-plane, where their winding
increments telescope. No planar filling or Euler characteristic is needed.
-/
@[expose] public section
namespace PottsDiscontinuity.TorusTopology.Secant
open SimpleGraph Planar.Medial FK
abbrev V := ℤ × ℤ
abbrev G := squareLattice
def lab (a b : ℤ × ℤ) : Fin 4 :=
  if a.1 < b.1 then 0 else if a.2 < b.2 then 1 else if b.1 < a.1 then 2 else 3

def vec : Fin 4 → V := ![(1,0),(0,1),(-1,0),(0,-1)]
def idx (d : Fin 4) : ℤ := ((d+3).val : ℕ)
def up (v : V) : ℤ := if 0 < v.2 then 1 else 0
/-- Count crossings of the cut east of zero, between heights zero and one. -/
def cut (v w : V) : ℤ := if 0 < v.1 then up w - up v else 0

lemma vec_eq {a b : V} (h : G.Adj a b) : vec (lab a b) = b-a := by
  have ha := (squareLattice_adj_iff _ _).mp h
  unfold lab; split_ifs <;> apply Prod.ext <;> change _ = _ - _ <;> norm_num [vec] <;> omega

variable {a b c : V} (hab : G.Adj a b)

include hab in
lemma local_turn (hbc : G.Adj b c) (hne : a ≠ c) :
    primalCompassQuarterTurn (lab a b) (lab b c) = idx (lab b c) - idx (lab a b) +
      4 * (cut (b-a) (c-a) + cut (c-a) (c-b)) := by
  have table (d e : Fin 4) (h : vec d + vec e ≠ 0) : primalCompassQuarterTurn d e = idx e - idx d +
      4 * (cut (vec d) (vec d+vec e) + cut (vec d+vec e) (vec e)) := by
    revert h; fin_cases d <;> fin_cases e <;> decide
  have hsum : vec (lab a b) + vec (lab b c) = c-a := by rw [vec_eq hab,vec_eq hbc]; abel
  have hh := table _ _ (by rw [hsum]; exact sub_ne_zero.mpr hne.symm)
  rwa [hsum,vec_eq hab,vec_eq hbc] at hh

/-- Disjoint unit segments give a cell of secants contained in one of the
 coordinate half-planes. The local increment thus has zero circulation. -/
lemma cell {a b x y : V} (hab : G.Adj a b) (hxy : G.Adj x y)
    (hax : a ≠ x) (hay : a ≠ y) (hbx : b ≠ x) (hby : b ≠ y) :
    cut (x-a) (y-a) + cut (y-a) (y-b) = cut (x-a) (x-b) + cut (x-b) (y-b) := by
  have h₁ := (squareLattice_adj_iff _ _).mp hab
  have h₂ := (squareLattice_adj_iff _ _).mp hxy
  simp only [ne_eq, Prod.ext_iff] at hax hay hbx hby
  have h : (((a.1 < x.1 ↔ a.1 < y.1) ∧ (a.1 < x.1 ↔ b.1 < x.1)) ∨
    ((a.2 < x.2 ↔ a.2 < y.2) ∧ (a.2 < x.2 ↔ b.2 < x.2) ∧ (a.2 < x.2 ↔ b.2 < y.2))) := by
    rcases h₁ with ⟨h|h,h'⟩ | ⟨h,h'|h'⟩ <;> rcases h₂ with ⟨g|g,g'⟩ | ⟨g,g'|g'⟩ <;>
      first | (left; constructor <;> omega) | (right; refine ⟨?_,?_,?_⟩ <;> omega) | (by_cases hx : a.1 < x.1 <;> by_cases hy : a.1 < y.1 <;> by_cases hb : b.1 < x.1 <;> first | left; omega | right; omega)
  rcases h with ⟨h1,h2⟩ | ⟨h1,h2,h3⟩
  · simp only [cut, Prod.fst_sub, sub_pos, ← h1, ← h2]; split <;> omega
  · simp only [cut,up,Prod.snd_sub,sub_pos,← h1,← h2,← h3,sub_self,ite_self,add_zero]

include hab in
/-- The corner left after cutting open the polygon at a vertex of least abscissa. -/
lemma corner (hca : G.Adj c a)
    (hb : a.1 ≤ b.1) (hc : a.1 ≤ c.1) (hne : b ≠ c) :
    let t := idx (lab c a) - idx (lab a b) + 4 * (up (c-a) - up (b-a) +
      cut (c-a) (c-b) + cut (c-b) (a-b)) + primalCompassQuarterTurn (lab c a) (lab a b)
    t = 4 ∨ t = -4 := by
  have table (d e : Fin 4) (hd : 0 ≤ (vec d).1) (he : (vec e).1 ≤ 0) (hne : vec d + vec e ≠ 0) :
      let w := idx e - idx d + 4*(up (-vec e)-up (vec d)+ cut (-vec e) (-vec e-vec d)+cut (-vec e-vec d) (-vec d)) + primalCompassQuarterTurn e d
      w = 4 ∨ w = -4 := by revert hd he hne; fin_cases d <;> fin_cases e <;> decide
  have hd := vec_eq hab; have he := vec_eq hca
  have hs : vec (lab a b) + vec (lab c a) = b - c := by rw [hd,he]; abel
  have h := table (lab a b) (lab c a) (by simpa [hd] using hb) (by simpa [he] using hc) (by rwa [hs, sub_ne_zero])
  simpa [hd,he,show c-a-(b-a) = c-b by abel] using h

end PottsDiscontinuity.TorusTopology.Secant
