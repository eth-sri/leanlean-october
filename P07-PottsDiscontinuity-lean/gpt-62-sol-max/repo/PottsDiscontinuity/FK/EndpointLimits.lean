module

public import PottsDiscontinuity.Frozen.Defs.IsRCInfiniteVolumeLimit

/-! Every lattice vertex and edge eventually lies in the origin-centered boxes. -/

@[expose] public section

open Filter

namespace PottsDiscontinuity.FK

/-- Every fixed lattice vertex lies in all sufficiently large frozen boxes. -/
theorem eventually_mem_box (x : ℤ × ℤ) : ∀ᶠ n : ℕ in atTop, x ∈ box n := by
  filter_upwards [eventually_ge_atTop (max x.1.natAbs x.2.natAbs)] with n hn
  simp only [box, Finset.mem_product, Finset.mem_Icc]
  omega

/-- Every fixed lattice edge has a lift to the induced graph on every sufficiently large box. -/
theorem eventually_edge_lift_box (e : squareLattice.edgeSet) :
    ∀ᶠ n : ℕ in atTop,
      ∃ f : (squareLattice.induce (box n : Set (ℤ × ℤ))).edgeSet,
        Sym2.map Subtype.val f.1 = e.1 := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
      filter_upwards [eventually_mem_box x, eventually_mem_box y] with n hx hy
      refine ⟨⟨s(⟨x, hx⟩, ⟨y, hy⟩), ?_⟩, rfl⟩
      exact he

end PottsDiscontinuity.FK
