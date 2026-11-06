import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FunProp
namespace GS.Topology
/-- Relabeling columns preserves the inherited topology and exact matrix rank. -/
def reindexRankOne {ρ κ ν : Type*} [Fintype κ] [Fintype ν] (e : κ ≃ ν) :
    {W : Matrix ρ κ ℝ // W.rank ≤ 1} ≃ₜ {W : Matrix ρ ν ℝ // W.rank ≤ 1} :=
  (Homeomorph.piCongrRight fun _ =>
    (Homeomorph.piCongrLeft (Y := fun _ => ℝ) e.symm).symm).subtype
      (fun W => by rw [← Matrix.rank_reindex (Equiv.refl ρ) e W]; rfl)

end GS.Topology
