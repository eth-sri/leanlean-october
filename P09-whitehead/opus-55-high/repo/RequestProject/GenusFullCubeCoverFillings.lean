import RequestProject.GenusFullCubeMarking
import RequestProject.CombUniversalCover
import RequestProject.CellularHomotopyChain
import RequestProject.Tac


/-! Genuine cap fillings in the path-class universal cover of the full cube quotient. -/
bwd

namespace FiniteChains.Comb
universe u
variable {X : Complex2.{u}} {a : X.V}

/-- A null-homotopic loop has a finite chain filling after lifting at any cover vertex. -/
theorem exists_lifted_boundary_of_null
    {p}
    (hp : IsPathX X p (endV v) (endV v))
    (hn : Htpy X (endV v) (endV v) p []) :
    ∃ c,
      bdry2 (uCover X a) c = pathChain (uLiftPath p v) := by
  have he : extendList p v = v := by
    simpa using extendList_htpy hp hn
  have hl : IsPathX (uCover X a) (uLiftPath p v) v v := by
    have h := isPath_uLiftPath p v _ hp
    aesop
  simpa using (simplyConnected_univCover v _ hl).exists_boundary

end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

/-- Every exact marked cap loop has a filling at every vertex over its base point. -/
theorem fullCubeCover_cap_filling {a : QCube (cmpRel (GenusVertex q))}
    x v
    (hv : endV v = (markedSpineToFullCube q).onV (markedSpineBase q)) :
    ∃ c : (uCover (orderCx (QCube (cmpRel (GenusVertex q)))) a).F →₀ ℤ,
      Comb.bdry2 _ c = pathChain
        (uLiftPath (mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1) v) := by
  apply exists_lifted_boundary_of_null
  · rw [hv]
    exact isPath_mapPath _ (markedSpineLoop q x).2
  · rw [hv]
    exact markedSpineToFullCube_mark_null q x

/-- A chosen filling uses actual universal-cover faces and their actual cellular boundary. -/
noncomputable def fullCubeCoverCapChain {a : QCube (cmpRel (GenusVertex q))}
    (x : Fin q × Bool) (v : UV (orderCx (QCube (cmpRel (GenusVertex q)))) a)
    (hv : endV v = (markedSpineToFullCube q).onV (markedSpineBase q)) :=
  Classical.choose (fullCubeCover_cap_filling q x v hv)

theorem fullCubeCoverCapChain_boundary {a : QCube (cmpRel (GenusVertex q))}
    x (v : UV (orderCx (QCube (cmpRel (GenusVertex q)))) a)
    hv :
    Comb.bdry2 _ (fullCubeCoverCapChain q x v hv) = pathChain
      (uLiftPath (mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1) v) :=
  Classical.choose_spec (fullCubeCover_cap_filling q x v hv)
