module

public import RequestProject.QCubeSquareSubdivision
public import RequestProject.StrictLowerIntervalChains

@[expose] public section

/-! Free directions of the square facets of a quotient three-cube. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

variable (c : QCube A)

variable {u v w : V}

theorem threeFacet_uv_spx
    (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w}) (s : ZMod 2) :
    (qCubeFacet c w s).spx = {u, v} := by
  ext x
  simp only [qCubeFacet, hs, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] <;> grind

section

variable (huv : u ≠ v)
include huv

theorem threeFacet_uw_spx (hvw : v ≠ w) (hs : c.spx = {u, v, w}) (s : ZMod 2) :
    (qCubeFacet c v s).spx = {u, w} := by
  grind [threeFacet_uv_spx]

theorem threeFacet_vw_spx (huw : u ≠ w) (hs : c.spx = {u, v, w}) (s : ZMod 2) :
    (qCubeFacet c u s).spx = {v, w} := by
  grind [threeFacet_uv_spx]

end

end FiniteChains.Davis
