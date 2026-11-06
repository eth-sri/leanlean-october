module

public import RequestProject.QCubeSquareSubdivision
public import RequestProject.StrictLowerIntervalChains

@[expose] public section

/-! Actual strict subdivisions of quotient three-cubes. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

theorem threeFacet_uv_spx (c : QCube A) {u v w : V}
    (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w}) (s : ZMod 2) :
    (qCubeFacet c w s).spx = {u, v} := by
  ext x
  simp only [qCubeFacet, hs, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hne, hx | hx | hx⟩
    · exact Or.inl hx
    · exact Or.inr hx
    · exact False.elim (hne hx)
  · rintro (rfl | rfl)
    · exact ⟨huw, Or.inl rfl⟩
    · exact ⟨hvw, Or.inr (Or.inl rfl)⟩

theorem threeFacet_uw_spx (c : QCube A) {u v w : V}
    (huv : u ≠ v) (hvw : v ≠ w) (hs : c.spx = {u, v, w}) (s : ZMod 2) :
    (qCubeFacet c v s).spx = {u, w} := by
  apply threeFacet_uv_spx c huv (Ne.symm hvw)
  rw [hs]
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem threeFacet_vw_spx (c : QCube A) {u v w : V}
    (huv : u ≠ v) (huw : u ≠ w) (hs : c.spx = {u, v, w}) (s : ZMod 2) :
    (qCubeFacet c u s).spx = {v, w} := by
  apply threeFacet_uv_spx c (Ne.symm huv) (Ne.symm huw)
  rw [hs]
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

noncomputable def cubeThreeSquareBoundary (c : QCube A) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w}) :
    (strictOrderCx (QCube A)).F →₀ ℤ :=
  cubeSquareSubdivision (qCubeFacet c w 0) u v huv (threeFacet_uv_spx c huw hvw hs 0) -
  cubeSquareSubdivision (qCubeFacet c w 1) u v huv (threeFacet_uv_spx c huw hvw hs 1) -
  cubeSquareSubdivision (qCubeFacet c v 0) u w huw (threeFacet_uw_spx c huv hvw hs 0) +
  cubeSquareSubdivision (qCubeFacet c v 1) u w huw (threeFacet_uw_spx c huv hvw hs 1) +
  cubeSquareSubdivision (qCubeFacet c u 0) v w hvw (threeFacet_vw_spx c huv huw hs 0) -
  cubeSquareSubdivision (qCubeFacet c u 1) v w hvw (threeFacet_vw_spx c huv huw hs 1)
