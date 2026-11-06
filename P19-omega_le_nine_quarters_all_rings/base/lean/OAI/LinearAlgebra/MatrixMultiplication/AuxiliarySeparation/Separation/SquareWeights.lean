module

public import Mathlib.Data.Int.Basic
public import Mathlib.Tactic

public section

@[expose] section

namespace OAI

/-!+# The square weights in auxiliary separation

Sections 4.1–4.3 use the phase `u - v + 2 * (g - h)` to select monomials.
On a selected monomial, the three integer variable weights add to `(g - h)^2`.
Thus the surviving monomials have nonnegative total degree, although individual
variable weights may be negative. Their degree is zero precisely when the guess
`g` matches the sector `h` and the auxiliary labels agree.
-/

namespace MatrixMultiplication.AuxiliarySeparation

/-- The exponent occurring in the finite Fourier projection. -/
def phase (g h u v : ℤ) : ℤ := u - v + 2 * (g - h)

/-- Weight on the first tensor leg, which carries the guessed sector label. -/
def firstWeight (g : ℤ) : ℤ := g ^ 2

/-- Weight on the second tensor leg. -/
def secondWeight (h u : ℤ) : ℤ := h * u - h ^ 2

/-- Weight on the third tensor leg. -/
def thirdWeight (h v : ℤ) : ℤ := -(h * v)

/-- Total weight of a target monomial after the three independent substitutions. -/
def totalWeight (g h u v : ℤ) : ℤ :=
  firstWeight g + secondWeight h u + thirdWeight h v

theorem totalWeight_eq_square_add_phase (g h u v : ℤ) :
    totalWeight g h u v = (g - h) ^ 2 + h * phase g h u v := by
  unfold totalWeight firstWeight secondWeight thirdWeight phase
  ring

/-- The projection equation converts the total weight into a square. -/
theorem totalWeight_eq_sq_of_phase_eq_zero {g h u v : ℤ}
    (hphase : phase g h u v = 0) :
    totalWeight g h u v = (g - h) ^ 2 := by
  rw [totalWeight_eq_square_add_phase, hphase, mul_zero, add_zero]

theorem totalWeight_nonneg_of_phase_eq_zero {g h u v : ℤ}
    (hphase : phase g h u v = 0) : 0 ≤ totalWeight g h u v := by
  rw [totalWeight_eq_sq_of_phase_eq_zero hphase]
  exact sq_nonneg (g - h)

/-- On the Fourier support, precisely the correctly matched terms have weight zero. -/
theorem totalWeight_eq_zero_iff_of_phase_eq_zero {g h u v : ℤ}
    (hphase : phase g h u v = 0) :
    totalWeight g h u v = 0 ↔ g = h ∧ u = v := by
  rw [totalWeight_eq_sq_of_phase_eq_zero hphase, sq_eq_zero_iff]
  constructor
  · intro hzero
    have hgh : g = h := sub_eq_zero.mp hzero
    refine ⟨hgh, ?_⟩
    unfold phase at hphase
    omega
  · rintro ⟨hgh, _⟩
    exact sub_eq_zero.mpr hgh

end MatrixMultiplication.AuxiliarySeparation

end OAI
