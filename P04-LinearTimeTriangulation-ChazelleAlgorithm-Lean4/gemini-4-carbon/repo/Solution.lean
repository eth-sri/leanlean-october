module

public import Chazelle

/-!
# Solution

Comparator checks that the declaration below has exactly the same statement as
its counterpart in `Challenge.lean` and uses only the permitted axioms.

The proof is `Chazelle.Core.linearTimeTriangulation` (`Chazelle/Core/MainTheorem.lean`).
-/

public section

theorem Chazelle.linear_time_triangulation : Chazelle.LinearTimeTriangulation :=
  Chazelle.Core.linearTimeTriangulation

end
