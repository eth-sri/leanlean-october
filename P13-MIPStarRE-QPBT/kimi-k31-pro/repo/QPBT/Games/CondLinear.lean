module

public import MIPStarRE.LDT.Basic.DistributionUniform

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

noncomputable def clDistribution [Fintype K] [DecidableEq K]
    (L R : (ι → K) → (ι → K)) :
    Distribution ((ι → K) × (ι → K)) :=
  (uniformDistribution (ι → K)).map (fun z => (L z, R z))

noncomputable def graphDistribution {T : Type*} [Fintype T] [DecidableEq T]
    (E : Finset (Sym2 T)) (_hE : E.Nonempty) : Distribution (T × T) :=
  Distribution.uniformOnFinset
    (Finset.univ.filter fun ab : T × T => Sym2.mk ab.1 ab.2 ∈ E)

theorem graphDistribution_isProbability {T : Type*} [Fintype T] [DecidableEq T]
    (E : Finset (Sym2 T)) (hE : E.Nonempty) :
    (graphDistribution E hE).IsProbability := by
  apply Distribution.uniformOnFinset_isProbability
  obtain ⟨e, he⟩ := hE
  obtain ⟨⟨a, b⟩, rfl⟩ := Sym2.mk_surjective e
  change s(a, b) ∈ E at he
  exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩

theorem graphDistribution_symm {T : Type*} [Fintype T] [DecidableEq T]
    (E : Finset (Sym2 T)) (hE : E.Nonempty) (a b : T) :
    (graphDistribution E hE).weight (a, b) =
      (graphDistribution E hE).weight (b, a) := by
  classical
  simp [graphDistribution, Distribution.uniformOnFinset_weight, Sym2.eq_swap]

end MIPStarRE.QPBT
