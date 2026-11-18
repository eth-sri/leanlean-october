/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Descriptive.SmallVocabulary
public import InfinitaryLogic.Descriptive.SatisfactionBorel
public import InfinitaryLogic.Lomega1omega.QuantifierRank

/-!
# Lifting formulas of the small presentation back to the original language

`liftFormula` sends a formula of `lang L` to the formula of `L` obtained by decoding each relation
symbol through `toLang L`.  It is a self-contained definition: `BoundedFormulaω.mapLanguage`
takes both languages in the same universe pair, which excludes this case, and that definition is
left unchanged.

* `realize_liftFormula`: the lift holds in `c.toStructure` iff the original holds in
  `(code L c).toStructure`, for every valuation.
* `qrank_liftFormula`: the quantifier rank is unchanged.
* `modelsOf_liftFormula`: `ModelsOf (liftFormula L ψ) = code L ⁻¹' ModelsOf ψ`, with the
  pointwise form `code_mem_modelsOf_iff`.

No lowering of `L`-formulas into the small presentation is provided.  The vocabulary is relational,
so terms are variables.
-/

@[expose] public section

universe u v uι u'

namespace FirstOrder.Language.SmallVocabulary

variable (L : Language.{u, v}) [L.IsRelational] [Countable (Σ n, L.Relations n)]

/-- Terms of the small presentation are variables (the vocabulary is relational). -/
def liftTerm {γ : Type u'} : (lang L).Term γ → L.Term γ
  | .var x => .var x
  | .func f _ => isEmptyElim f

omit [L.IsRelational] in
@[simp] theorem liftTerm_var {γ : Type u'} (x : γ) : liftTerm L (.var x : (lang L).Term γ) = .var x :=
  rfl

end FirstOrder.Language.SmallVocabulary
