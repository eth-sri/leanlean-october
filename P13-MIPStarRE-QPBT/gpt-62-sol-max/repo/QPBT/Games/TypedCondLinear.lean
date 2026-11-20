module

public import QPBT.Games.CondLinear
public import QPBT.Games.DistributionAux

/-! # Typed conditionally linear distributions

Typed question distributions first sample an ordered edge of the type graph and
then sample the corresponding pair of conditionally linear images of one common
uniform seed.

## References

These are blueprint `def:typed-cl-functions` and `def:typed-cl-distributions`,
with paper origin
`references/qpbt-paper/07_types.tex:57-94`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

section

variable {K T ι : Type*}
    [Field K] [Fintype K] [DecidableEq K]
    [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
    (E : Finset (Sym2 T)) (hE : E.Nonempty)
include K T ι E hE

/-- The typed CL distribution: sample a type pair from the graph distribution,
then bind it to the CL distribution selected by those two types. This is
blueprint `def:typed-cl-distributions`, paper
`references/qpbt-paper/07_types.tex:84-94`. -/
noncomputable def typedCLDistribution
    (L R : T → (ι → K) → (ι → K)) :
    Distribution ((T × (ι → K)) × (T × (ι → K))) :=
  Distribution.bind (graphDistribution E hE) fun uv =>
    (clDistribution (L uv.1) (R uv.2)).map fun xy =>
      ((uv.1, xy.1), (uv.2, xy.2))

/-- A typed conditionally linear distribution built from a single family is
symmetric under exchanging the two players: the edge law of
`def:graph-distribution` is symmetric, and exchanging the two types exchanges
the two images of the common seed.  This is not a named statement of the source
article; it is `lem:typed-cl-distribution-symm` in
`blueprint/src/chapter/ch12_qpbt_games.tex`. -/
theorem typedCLDistribution_symm
    (L : T → (ι → K) → (ι → K))
    (c : (T × (ι → K)) × (T × (ι → K))) :
    (typedCLDistribution E hE L L).weight c =
      (typedCLDistribution E hE L L).weight c.swap := by
  classical
  let μ := graphDistribution E hE
  let f (uv : T × T) (z : ι → K) := ((uv.1, L uv.1 z), (uv.2, L uv.2 z))
  have hs (w : _) : (typedCLDistribution E hE L L).weight w =
      ∑ uv, μ.weight uv * ((uniformDistribution (ι → K)).map (f uv)).weight w := by
    simp only [typedCLDistribution, clDistribution, Distribution.map_map, Distribution.bind]
    exact Finset.sum_subset (Finset.subset_univ _) fun uv _ hu => by
      rw [show (graphDistribution E hE).weight uv = 0 from μ.outsideSupport uv hu, zero_mul]
  rw [hs, hs]
  refine Fintype.sum_equiv (Equiv.prodComm T T) _ _ fun ⟨u, v⟩ => ?_
  rw [Equiv.prodComm_apply, graphDistribution_symm E hE u v]
  congr 1
  rcases c with ⟨a, b⟩
  simp only [uniformDistribution_map_weight, f, Prod.swap_prod_mk, Prod.mk.injEq, and_comm]

end

end MIPStarRE.QPBT
