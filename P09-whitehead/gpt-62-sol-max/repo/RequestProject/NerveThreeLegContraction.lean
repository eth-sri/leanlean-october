module

public import RequestProject.NerveOrderHomotopy

@[expose] public section

/-! A three-leg order contraction supplies actual augmented nerve fillings. -/
namespace FiniteChains.Nerve
universe u
variable {P : Type u} [Preorder P]

theorem exists_bdry_eq_of_cycle_threeLeg (r g : P → P) (d : P)
    (hr : Monotone r) (hg : Monotone g) (hri : id ≤ r ∨ r ≤ id)
    (hrg : r ≤ g ∨ g ≤ r) (hdg : g ≤ (fun _ => d) ∨ (fun _ => d) ≤ g)
    (c : Ch P) (hc : c ∈ Inc P) (hcyc : bdry c = 0) :
    ∃ y ∈ Inc P, bdry y = c := by
  simpa only [cmap_id] using filling_of_comparable_maps monotone_id hr hri hc hcyc
    (filling_of_comparable_maps hr hg hrg hc hcyc
      (filling_of_comparable_maps hg monotone_const hdg hc hcyc
        ⟨_, cone_const_mem_inc d c, by rw [bdry_consMap, ← cmap_bdry, hcyc, map_zero, map_zero, sub_zero]⟩))

end FiniteChains.Nerve
