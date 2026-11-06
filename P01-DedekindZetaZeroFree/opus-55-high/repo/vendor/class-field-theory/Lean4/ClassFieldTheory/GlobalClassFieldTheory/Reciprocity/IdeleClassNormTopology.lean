module

public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.NormTopology
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitNormQuotient
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormConductor

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# The norm topology and the ordinary idele-class topology

On every actual fixed field inside the rational separable closure, the
canonical fixed-part model identifies each abstract finite norm subgroup
with the range of the corresponding ordinary idele-class norm.  Since the
latter is open, every abstract norm-open subgroup becomes open in the
ordinary idele-class topology after transport to the actual fixed field.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open LocalClassFieldTheory

/-- Use the canonical quotient group structure before elaborating additive
norm-subgroup maps. -/
@[instance_reducible]
 def normTopologyIdeleClassCommGroup
    (F : Type) [Field F] [NumberField F] :
    CommGroup (IdeleClassGroup F) :=
  QuotientGroup.Quotient.commGroup (IdeleGroup.principalSubgroup F)

attribute [local instance] normTopologyIdeleClassCommGroup
