module

public import Glennie.Sector
public import Glennie.Theorems.CubicNorm
public import Glennie.Obligations
public import Glennie.Native.CoordinateSimp

@[expose] public section

namespace Glennie


section
/-- Encoder polynomial recovery carries diagonalization to all frame atoms. -/
theorem frame_projectors_diagonal (p : Fin 3 → Albert) (hp : Frame p)
    (he : IsDiagonal (encoder p)) (i : Fin 3) : IsDiagonal (p i) := by
  rw [frame_as_projector p hp]
  fin_cases i <;> simp [projectorFrame, IsDiagonal, albert_coords, he.1, he.2.1, he.2.2]

/-- Frame encoders diagonalize with zero determinant and fixed discriminant square. -/
theorem diagonal_frame_encoder_cubic_zero (p : Fin 3 → Albert) (hp : Frame p)
    (he : IsDiagonal (encoder p)) :
    (encoder p).d0*(encoder p).d1*(encoder p).d2 = 0 := by
  have h := frame_encoder_cubicNorm p hp
  rw [← diagonalAlbert_eq (encoder p) he,newtonCubicNorm_coordinates] at h
  simpa [albert_coords, diagonalAlbert] using h

end
end Glennie
