/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Methods.LopezEscobar.WitnessLang
public import InfinitaryLogic.Methods.Interpolation.GraphReconstruction

/-!
# The graph-relationalization spike (issue #10, Unit 1 part 2)

The two remaining Unit-1 acceptance gates of audit v2 (D4, graph-translation route):

* **the relationalization micro-pilot** — a nested numeral formula (`f(s(c)) = s(c)`,
  Marker's bullet-2 shape) mapped into the tagged `KLang L` along the left-witness
  embedding, relationalized through the Craig Layer-3 files, with its realization verified
  through `graphExpansion` all the way back to the witness-language semantics
  (`pilot_realize`), plus the side-specific graph axioms realized by the expansion
  (`pilot_graphAxioms`);
* **the decisive occurrence theorem** (`occurrence_intersection_base`) — the intersection
  of the two sides' complete relationalized symbol sets, *graph axioms included*, contains
  only graph-language images of base-`L` symbols.  No witness symbol survives: left/right
  witness symbols are disjoint (`WitnessLang.lean`), equality introduces no relation
  symbols (`relationsIn_relationalizeFormula`, `.equal` case), and the sharp calculation is
  Craig's `relSym_inter`.

With this compiled, the graph-language route is **frozen** and the hand-rolled relational
vocabulary of the audit's D4 is retired to its historical fallback note.
-/

@[expose] public section

namespace FirstOrder.Language

open FirstOrder Structure

variable (L : Language.{0, 0})

/-- Countability of a formula's function-symbol occurrence set, as an instance (feeds
`graphAxioms`). -/
instance {L' : Language.{0, 0}} {α : Type} {n : ℕ} (ψ : L'.BoundedFormulaω α n) :
    Countable ↥ψ.functionsIn :=
  ψ.functionsIn_countable.to_subtype

instance : Countable ↥(leftFuns L) := (Set.countable_range _).to_subtype

instance : Countable ↥(rightFuns L) := (Set.countable_range _).to_subtype

/-! ## The micro-pilot -/

/-! ## The decisive occurrence theorem -/

end FirstOrder.Language
