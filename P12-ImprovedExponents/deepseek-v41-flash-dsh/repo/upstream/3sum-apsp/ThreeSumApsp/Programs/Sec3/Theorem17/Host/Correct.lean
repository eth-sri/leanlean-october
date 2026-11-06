/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Arrays
public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.ParametersStage
public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.PrimeStage
public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Time
public import ThreeSumApsp.TacticsShort

/-!
# The host of Theorem 17: et17 decides Exact Triangle

The three parts of the host procedure `et17` (Exact Triangle by Theorem 17) and the small case are
put together (`et17_spec`).  Correctness is `HostData.found_m`: a zero triangle is found if and only
if there is one.
-/

public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

end Light.Sec3