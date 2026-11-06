module

public import MIPStarRE.Quantum.Measurement

/-! Shared finite-coordinate, state-vector, and complex-matrix types. -/

@[expose] public section

abbrev MIPStarRE.QPBT.StateVector (ι : Type*) := EuclideanSpace ℂ ι
abbrev MIPStarRE.QPBT.CMatrix (ι : Type*) (κ : Type*) := Matrix ι κ ℂ

abbrev MIPStarRE.QPBT.Coordinates (n : ℕ) (K : Type*) := Fin n → K
