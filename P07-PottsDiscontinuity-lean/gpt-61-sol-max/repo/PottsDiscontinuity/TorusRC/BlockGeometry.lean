module
public import Mathlib

public import PottsDiscontinuity.TorusRC.ReflectedPairs

/-! # Actual lifted connections supplied by the reflected blocks -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC



variable {N M : ℕ}

/-- Positive double-block probability forces the endpoint parity required
for its prescribed lifted column. -/
theorem rectangleDoubleConnection_endpoint_even (hNp : 0 < N) (hMp : 0 < M)
    (n : ℕ) (i : Fin (3 * n + 1))
    (hE : (rectangleDoubleConnection hNp hMp n i).Nonempty) : Even (i.val : ℤ) := by
  obtain ⟨A,u,v,hu,_,_,_⟩ := hE
  grind

end PottsDiscontinuity.TorusRC
