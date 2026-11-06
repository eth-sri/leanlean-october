module

public import ValuedFieldTheory.LocalField.DiscreteValuationField.IwasawaPrincipalUnits

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Equal-characteristic Laurent-series model

For the positive-characteristic branch of the existence theorem, the local-field classification
identifies a local field with a Laurent-series field over its residue field.
The earlier complete-DVR development constructs the coefficient section and proves that Laurent
series evaluation is onto.  Here we package that concrete evaluation as the
actual field equivalence needed by the Lubin--Tate construction; no existence
or norm-subgroup statement is assumed.
-/

noncomputable section

open scoped PowerSeries LaurentSeries

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The Laurent-series parameter `T`, written through the localization map
from power series so its later transport to the local field is definitional. -/
def equalCharacteristicLaurentUniformizer
    (F : LocalField.{u, v} K) : F.residueField⸨X⸩ :=
  algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩
    (PowerSeries.X : F.residueField⟦X⟧)
