/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Arrays
import ThreeSumApsp.Programs.Sec3.Theorem17.Host.ParametersStage
import ThreeSumApsp.Programs.Sec3.Theorem17.Host.PrimeStage
import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Time

/-!
# The host of Theorem 17: et17 decides Exact Triangle

The three parts of the host procedure `et17` (Exact Triangle by Theorem 17) and the small case are
put together (`et17_spec`).  Correctness is `HostData.found_m`: a zero triangle is found if and only
if there is one.
-/



namespace Light.Sec3


