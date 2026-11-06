/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Need
public import ThreeSumApsp.TacticsShort

/-!
# The host of Theorem 17: the parameters and the small case

The first part of the host procedure `et17` (Exact Triangle by Theorem 17) computes `D`, `g` and
`s = ⌊√D⌋` and tests whether `n` is small (`et17Params_spec`).  If it is, the host calls the brute
force (`et17Small_spec`; proof of Theorem 19: "smaller instances are solved by brute force").
-/

public section

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {P₀ R : Program} {ν : Et17Nums} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
  {Dfun Gfun tD tG wD wG : ℕ → ℕ} {lim : Limits} {d : ℕ}

open Et17
end Light.Sec3