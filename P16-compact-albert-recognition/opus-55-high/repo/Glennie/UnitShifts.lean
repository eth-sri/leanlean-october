/- Direct native unit shifts before reverse shear.
The first-unit proof uses direct unrestricted diagonal-first reduction.
Hidden helpers use the SectorModel maps. -/
module
public import Glennie.Native.PairReduction
public import Glennie.SectorFactor
public import Glennie.SectorModel

@[expose] public section
namespace Glennie

theorem diagonalAlbert_eq (x : Albert) (hx : IsDiagonal x) :
    diagonalAlbert x.d0 x.d1 x.d2 = x := by ext <;> simp [diagonalAlbert, hx.1, hx.2.1, hx.2.2]

theorem complexAlbert_eq (x : Albert) (hx : InComplexSector x) :
    complexAlbert x.d0 x.d1 x.d2 (complexPart x.o01)
      (complexPart x.o02) (complexPart x.o12) = x :=
  complexProjection_eq_self x hx

theorem phi_of_diagonal_complex (x y z : Albert) (hx : IsDiagonal x)
    (hy : InComplexSector y) :
    phi x y z = (2*(x.d0-x.d1)*(x.d1-x.d2)*(x.d2-x.d0)*
      (complexPart y.o01*complexPart y.o12*star (complexPart y.o02)).im)*
      (hiddenMatrix z).det.im := by
  conv_lhs => rw [← diagonalAlbert_eq x hx, ← complexAlbert_eq y hy]
  exact phi_diagonal_complex_factor _ _ _ _ _ _ _ _ _ _

/-- Reuse the complete native sector linear map. No coordinate
linearity proof or model-preservation assumption is duplicated here. -/
def hiddenMatrixLinear : Albert →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℂ :=
  sectorHiddenLinear

theorem hiddenMatrix_eq_zero (x : Albert) (hx : InComplexSector x) :
    hiddenMatrix x = 0 := by
  have h : complexAlbertLinear (complexCoordinatesLinear x) = x :=
    complexProjection_eq_self x hx
  rw [← h]
  exact hiddenMatrix_complexAlbert _

theorem diagonal_inComplex (x : Albert) (hx : IsDiagonal x) : InComplexSector x := by
  rw [← diagonalAlbert_eq x hx]
  simp [InComplexSector, OctInComplex, diagonalAlbert]

end Glennie
