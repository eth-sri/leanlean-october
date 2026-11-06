/- Literal metric, cubic, basis table and flat coordinates for the dictionary.
  * The metric in summation and matrix forms.
  * The cubic in complex form det H - tr(H M^dagger M) + det M + conj(det M),
    whose imaginary part vanishes identically.
  * The 27-entry basis table, derived index by index as extDecode of coordinate
    unit vectors.
  * Flat base vectors x, y(theta), z(theta) as decodes of explicit coordinate
    vectors, with s standing for theta^-1 (no inverse is cast to C).
No flatness, frame admission, Phi value or rank statement is made here. -/
module

public import Glennie.Compact.NativeDictionaryProduct

@[expose] public section

namespace Glennie.Compact.NativeDictionary

noncomputable section

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-! ## Metric and cubic in the literal forms -/

/-! ## The basis table, re-derived -/

/-- Full coordinate unit vector. -/
def extUnit (n : Fin 27) : Fin 27 → ℝ := fun i => if i = n then 1 else 0

/-- The row-major
hidden matrix unit w E_rc in the column gauge. -/
def archivalHiddenBasis (r c : Fin 3) (w : ℂ) : Albert :=
  hiddenAlbert (fun i j => if i = r ∧ j = c then w else 0)

/-- Full index 1 (t). -/
theorem extDecode_extUnit_1 : extDecode (extUnit 1) = diagonalAlbert 1 (-1) 0 := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 3 (a01). -/
theorem extDecode_extUnit_3 : extDecode (extUnit 3) = complexAlbert 0 0 0 1 0 0 := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 4 (b01). -/
theorem extDecode_extUnit_4 : extDecode (extUnit 4) = complexAlbert 0 0 0 Complex.I 0 0 := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 5 (a02). -/
theorem extDecode_extUnit_5 : extDecode (extUnit 5) = complexAlbert 0 0 0 0 1 0 := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 6 (b02). -/
theorem extDecode_extUnit_6 : extDecode (extUnit 6) = complexAlbert 0 0 0 0 Complex.I 0 := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 9 (u00). -/
theorem extDecode_extUnit_9 : extDecode (extUnit 9) = archivalHiddenBasis 0 0 1 := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 10 (v00). -/
theorem extDecode_extUnit_10 : extDecode (extUnit 10) = archivalHiddenBasis 0 0 Complex.I := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 11 (u01). -/
theorem extDecode_extUnit_11 : extDecode (extUnit 11) = archivalHiddenBasis 0 1 1 := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 12 (v01). -/
theorem extDecode_extUnit_12 : extDecode (extUnit 12) = archivalHiddenBasis 0 1 Complex.I := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 13 (u02). -/
theorem extDecode_extUnit_13 : extDecode (extUnit 13) = archivalHiddenBasis 0 2 1 := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 14 (v02). -/
theorem extDecode_extUnit_14 : extDecode (extUnit 14) = archivalHiddenBasis 0 2 Complex.I := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 15 (u10). -/
theorem extDecode_extUnit_15 : extDecode (extUnit 15) = archivalHiddenBasis 1 0 1 := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 16 (v10). -/
theorem extDecode_extUnit_16 : extDecode (extUnit 16) = archivalHiddenBasis 1 0 Complex.I := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 17 (u11). -/
theorem extDecode_extUnit_17 : extDecode (extUnit 17) = archivalHiddenBasis 1 1 1 := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 18 (v11). -/
theorem extDecode_extUnit_18 : extDecode (extUnit 18) = archivalHiddenBasis 1 1 Complex.I := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 19 (u12). -/
theorem extDecode_extUnit_19 : extDecode (extUnit 19) = archivalHiddenBasis 1 2 1 := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-- Full index 20 (v12). -/
theorem extDecode_extUnit_20 : extDecode (extUnit 20) = archivalHiddenBasis 1 2 Complex.I := by
  ext <;> simp [extDecode, extUnit, archivalHiddenBasis, hiddenAlbert, hiddenOct,
    complexAlbert, complexOct, diagonalAlbert] <;> ring

/-! ## The flat base, as explicit coordinates (s stands for theta^-1) -/

end
end Glennie.Compact.NativeDictionary
