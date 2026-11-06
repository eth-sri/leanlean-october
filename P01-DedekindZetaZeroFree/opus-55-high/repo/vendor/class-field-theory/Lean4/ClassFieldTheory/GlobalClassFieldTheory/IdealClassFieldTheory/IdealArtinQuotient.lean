module

public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.IdealArtinMap

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# The ideal Artin quotient

For a defining modulus `m`, the ideal-theoretic Artin map is surjective and
has kernel `H_m`.  The first isomorphism theorem therefore identifies
`J_K^m / H_m` with the corresponding idelic norm quotient `C_K / N`.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open NumberField

variable {K : Type} [Field K] [NumberField K]

-- Reuse the normality witness embedded in the imported ideal-Artin definitions.
-- Choosing a different generic witness here makes quotient equivalences compare
-- enormous, propositionally equal but non-definitional terms.
attribute [local instance] ideleClassSubgroupNormal

local instance idealArtinKernelNormal
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N) :
    (idealArtinKernel m N hm).Normal := by
  change (idealArtinMap m N hm).ker.Normal
  infer_instance
