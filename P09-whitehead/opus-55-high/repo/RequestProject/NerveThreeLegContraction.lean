import RequestProject.NervePrism


/-! A three-leg order contraction supplies actual augmented nerve fillings. -/
namespace FiniteChains.Nerve
universe u
variable {P : Type u} [Preorder P]

theorem exists_bdry_eq_of_cycle_threeLeg r g (d : P)
    (hr : Monotone r) (hg : Monotone g) (hri : ∀ p, r p ≤ p)
    (hrg : ∀ p, r p ≤ g p) (hdg : ∀ p, d ≤ g p)
    c (hc : c ∈ Inc P) (hcyc : bdry c = 0) :
    ∃ y ∈ Inc P, bdry y = c := by
  have h₁ := bdry_prism_add_prism_bdry r id c
  have h₂ := bdry_prism_add_prism_bdry r g c
  have h₃ := bdry_prism_add_prism_bdry (fun _ => d) g c
  have h₄ : bdry (consMap d (cmap (fun _ => d) c)) = cmap (fun _ => d) c := by
    have he : bdry (consMap d (cmap (fun _ => d) c)) +
        consMap d (cmap (fun _ => d) (bdry c)) = cmap (fun _ => d) c := by
      rw [bdry_consMap, cmap_bdry]
      abel
    simp_all
  refine ⟨prism r id c - prism r g c + prism (fun _ => d) g c +
    consMap d (cmap (fun _ => d) c), ?_, ?_⟩
  · exact AddSubgroup.add_mem _
      (AddSubgroup.add_mem _
        (AddSubgroup.sub_mem _ (prism_mem_inc hr monotone_id hri hc)
          (prism_mem_inc hr hg hrg hc))
        (prism_mem_inc monotone_const hg hdg hc)) (cone_const_mem_inc d c)
  simp_all
