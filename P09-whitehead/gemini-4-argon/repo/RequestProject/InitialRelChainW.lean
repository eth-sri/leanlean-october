module

public import RequestProject.InitialComplex
public import RequestProject.FoxNaturality
public import RequestProject.PresentationDictionary
public import RequestProject.NecessityAlgebraicMod
public import RequestProject.CycleLifting
public import RequestProject.Pi2Dictionary
public import RequestProject.CoverComplex
public import RequestProject.ChainFormula
public import RequestProject.FinitelyDeterminedInf
public import RequestProject.Pigeonhole
public import RequestProject.CoverAcyclic
public import RequestProject.TorsionFreeGroupRing
public import RequestProject.ChainFormulaMod
public import RequestProject.PresCockcroftDictionary
public import RequestProject.CombData
public import RequestProject.CombHurewicz1Pres
public import RequestProject.CombCellularIso
public import RequestProject.MapChainDescent

@[expose] public section

/-!
# The initial pair of Lemma 3.1 as a map-carrying relative chain

`RequestProject/InitialComplex.lean` proves Lemma 3.1 for the complex
`Y_D = ⟨x_i, a_i, b_i | r_j, x_i[a_i,b_i]⁻¹, [y_{i,s}, y_{k,t}]⟩` attached to an acyclic
complex `D` of a finite presentation: `Y_D` is Cockcroft, the inclusion `D ⊂ Y_D` kills
`π₁(D)` and is zero on `π₂`.

The reverse implication of Theorem A uses the extension step in the map-carrying form
`FiniteChains.Comb.RelChainW` of `RequestProject/MapChainDescent.lean`: a relative chain over
`D` together with its inclusions, the Cockcroft property of every stage, the finiteness
bookkeeping and the requirement that each step adds a two-cell.  This file assembles Lemma 3.1
into exactly that shape, giving **the base case, of length one, of the extension step
`FiniteChains.Comb.MapStep`**:

* `FiniteChains.Comb.initialSeq`, `FiniteChains.Comb.initialInclHom`,
  `FiniteChains.Comb.initialInc` — the pair `D ⊂ Y_D` as a sequence of complexes with its
  inclusions;
* `FiniteChains.Comb.initialRelChainW` — that pair as a `RelChainW` of length one;
* `FiniteChains.Comb.nonempty_relChainW_initial_one` — hence, over the presentation complex of
  a finite acyclic presentation with at least one generator, there is a map-carrying relative
  chain of length one;
* `FiniteChains.Comb.isAcyclic_presComplex_of_exp` — a presentation complex whose exponent-sum
  matrix is bijective is acyclic;
* `FiniteChains.Comb.nonempty_strictTopChain_zero_initial` — combining the two with the
  generation statement (3.5) for the identity covering: **condition (1) of Theorem A of length
  one, unconditionally**, for the presentation complex of a finite acyclic presentation with at
  least one generator.
-/

namespace FiniteChains.Comb

universe u

variable {I J : Type u} [LinearOrder I] [DecidableEq I]
variable (r : J → FreeGroup I)

/-! ### Acyclicity of the presentation complex, read off the exponent-sum matrix -/

omit [LinearOrder I] in
theorem bdry2_presComplex_eq_expCol :
    bdry2 (presComplex r) = Finsupp.linearCombination ℤ (expCol r) := by
  refine Finsupp.lhom_ext' fun j => LinearMap.ext_ring ?_
  show bdry2 (presComplex r) (Finsupp.single j (1 : ℤ))
    = Finsupp.linearCombination ℤ (expCol r) (Finsupp.single j (1 : ℤ))
  rw [bdry2_pres_single, Finsupp.linearCombination_single, one_smul, expCol_eq_expVec]
  rfl
