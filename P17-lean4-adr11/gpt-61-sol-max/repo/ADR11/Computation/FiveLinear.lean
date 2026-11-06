module
public import ADR11.Computation.RootedFive
@[expose] public section
namespace ADR11.Five
def rowVal (k j i : ℕ) (v : Fin 5 → ℝ) (r : ℝ) : ℝ :=
  ((coeffs k j i).map fun (n, i) => (n : ℝ) * [1, v 0, v 1, v 2, v 3, v 4, r].getD i 1).sum

def rootBounds (k j : ℕ) (v : Fin 5 → ℝ) (r : ℝ) : Prop :=
  match k with
  | 0 => if j = 0 then r = 1 else r < 1
  | 1 => v 4 < v 0 ∧ match j with
    | 0 => r = v 0
    | 1 => r = v 4
    | 2 => v 4 < r ∧ r < v 0
    | 3 | 4 => r < v 4
    | _ => r < v 0
  | _ => v 3 < v 2 ∧ v 4 < v 2 ∧ match j with
    | 0 | 1 => r < v 3
    | 2 | 3 => r < v 4
    | 4 => r < v 2
    | 5 => v 3 < r ∧ r < v 2
    | 6 => v 4 < r ∧ r < v 2
    | 7 => r = v 2
    | 8 => r = v 3
    | _ => r = v 4

end ADR11.Five
