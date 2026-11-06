module

public import HK

/-!
# Solution

The theorems of `Challenge.lean`, restated verbatim from that file and closed from the internal
development in `HK/`: the command `chall` reads each protected statement from the challenge file and
proves it by the internal theorem of the same name with the suffix `_internal`, which the modules of
`HK/` declare with the same statements. This module does not import `Challenge.lean`; the definitions
come from `HK/Defs.lean`, which restates those of the challenge character for character.
-/

@[expose] public section

namespace HK

open Filter Topology

chall

end HK
