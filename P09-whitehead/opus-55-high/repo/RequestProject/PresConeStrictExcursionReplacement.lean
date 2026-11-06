import RequestProject.PresConeStrictGerms


namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

/-- An actual strict-edge excursion through a relator apex has a genuine cylinder path replacement. -/
theorem exists_presCone_strictEdge_excursion_replacement (hpos : 0 < (w j).length)
    (e d : StrictOrdEdge (PresPos w)) (he : e.val.2 = apexOf w j) (hd : d.val.2 = apexOf w j) :
    ∃ l,
      IsPathX (orderCx (PresPos w)) l e.val.1 d.val.1 ∧
      PathIn (· ∈ coneAdjBaseSet (S := circSet w)) l ∧
      Htpy (orderCx (PresPos w)) e.val.1 d.val.1
        (mapPath (strictOrderIncl (PresPos w)) [(e, true), (d, false)]) l := by
  have hx := he ▸ e.property
  have hy := hd ▸ d.property
  obtain ⟨l, hl, hc, hh⟩ := exists_presCone_strict_excursion_replacement w j hpos e.val.1 d.val.1 hx hy
  refine ⟨l, hl, hc, ?_⟩
  have hE : (strictOrderIncl _).onE e =
      ⟨(e.val.1, apexOf w j), hx.le⟩ :=
    Subtype.ext (Prod.ext rfl he)
  have hD : (strictOrderIncl _).onE d =
      ⟨(d.val.1, apexOf w j), hy.le⟩ :=
    Subtype.ext (Prod.ext rfl hd)
  simp_all [mapPath, List.map_cons, List.map_nil, hE, hD, ordPos, ordNeg]
