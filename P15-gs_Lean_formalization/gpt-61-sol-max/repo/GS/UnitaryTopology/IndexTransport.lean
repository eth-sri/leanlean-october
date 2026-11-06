
import GS.UnitaryTopology.QuaternionRetraction
import GS.NonmanifoldFinal.EuclideanTransport
import GS.Topology.RankReindex



/-!
# Column reindexing of the actual three-row rank cone

The maps preserve mathlib's matrix rank and the inherited matrix topology.
They allow a four-column-block Clifford construction to be stated at an
ordinary scalar matrix width.
-/
namespace GS.UnitaryTopology

variable {κ ν : Type*} [Fintype κ] [Fintype ν]

variable (e : κ ≃ ν)

def rankThreeReindex  : RankThreeCone κ ≃ₜ RankThreeCone ν :=
  GS.Topology.reindexRankOne e



def productRankThreeReindex (e : ℕ) (f : κ ≃ ν) :
    ((Fin e → ℝ) × RankThreeCone κ) ≃ₜ ((Fin e → ℝ) × RankThreeCone ν) :=
  (Homeomorph.refl _).prodCongr (rankThreeReindex f)



end GS.UnitaryTopology
