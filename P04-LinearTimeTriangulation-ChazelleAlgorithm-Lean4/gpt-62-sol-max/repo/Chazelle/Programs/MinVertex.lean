module

public import Chazelle.Programs.Tactics

/-!
# The lexicographically smallest vertex

A structured program `minVertexStmt` that scans the vertices of the input polygon and
leaves in natural register `0` the index of the lexicographically smallest vertex (smallest
abscissa, ties broken by smallest ordinate, further ties broken by smallest index).  No
simplicity assumption is made.

## Register allocation

| register | role                              |
|----------|-----------------------------------|
| `nreg 0` | `m`, the current minimiser (result) |
| `nreg 1` | `i`, the loop counter             |
| `nreg 2` | `n = P.n`                         |
| `nreg 3` | the constant `1`                  |
| `rreg 0` | `x_i`                             |
| `rreg 1` | `y_i`                             |
| `rreg 2` | `x_m`                             |
| `rreg 3` | `y_m`                             |

Natural registers `≥ 4`, real registers `≥ 4`, both memories and the output are untouched.

## Costs (exact, in executed machine instructions)

* initialisation: `4`;
* one loop iteration: reads `4`, update `≤ 6`, increment `1`, loop overhead `2`: `≤ 13`;
* loop exit: `2`.

Total: `≤ 13 * (P.n - 1) + 6` (the loop runs `P.n - 1` times), hence `≤ 13 * P.n + 6`.
The natural values manipulated are `0, 1, i ≤ max P.n 1, m < i` and `P.n`, so the word
bound `W` must satisfy `P.n ≤ W` and `1 ≤ W`; `W = P.n + 1` works.

## Main results

* `minVertex_exec`: the spec lemma (cost, result, frame).
* `minVertex_runsWithin`: the compiled program `minVertexProgram = compile minVertexStmt 0 ++
  [halt]` satisfies `RunsWithin minVertexProgram P (P.n + 1) (13 * P.n + 7) []`.
-/

namespace Chazelle

namespace Programs

open Machine Machine.Stmt

@[expose] public section

/-! ### The lexicographic order on points -/

/-- Lexicographic `≤` on points: smaller abscissa, or equal abscissa and `≤` ordinate. -/
def lexLE (p q : Point) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2)

/-! ### The program -/

/-! ### Spec lemmas for the pieces -/

section pieces
variable {P : Polygon} {W : ℕ}

end pieces

/-! ### The main theorem -/

end

end Programs

end Chazelle
