module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.CubeCosetDiagonalRegulator

@[expose] public section

namespace DedekindZetaZeroFree.KPActualFullKernelArithmetic

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory
open KPLocalStoneVonNeumann KPLocalPrincipalSeries KPRankOneShellContinuation
open KPRankOneOpenCellKernel KPRankOneCenterInducedDiagonalComparison
open KPRankOneLiftedRegulatedDiagonalAlgebra

noncomputable section

variable (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
variable [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]

private alias BoneL := DedekindZetaZeroFree.KPRankOneLiftedDiagonal.CenterInductionDiagonalAction.BoneL
private alias BoneR := DedekindZetaZeroFree.KPRankOneLiftedDiagonal.CenterInductionDiagonalAction.BoneR
private alias BnegR := DedekindZetaZeroFree.KPRankOneLiftedDiagonal.CenterInductionDiagonalAction.BnegR

private alias BnegL := DedekindZetaZeroFree.KPRankOneLiftedDiagonal.CenterInductionDiagonalAction.BnegL
private lemma Bnegleft (a b : (LocalField F q)ˣ) :
    KPHilbert.B3 F ζ hζ (Sum.inr q) (-a) b = KPHilbert.B3 F ζ hζ (Sum.inr q) a b := by
  rw [show -a = (-1) * a by simp, (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).1, BnegL, one_mul]

theorem steinberg_shifted_cube (c y : (LocalField F q)ˣ)
    (hD : (y : LocalField F q)^3 + (c : LocalField F q) ≠ 0) :
    KPHilbert.B3 F ζ hζ (Sum.inr q) c
      (Units.mk0 ((y : LocalField F q)^3 + (c : LocalField F q)) hD) = 1 := by
  let D : (LocalField F q)ˣ := Units.mk0 ((y : LocalField F q)^3 + (c : LocalField F q)) hD
  let B3_laws₀ := KPHilbert.B3_laws F ζ hζ (Sum.inr q)
  let BL (d : (LocalField F q)ˣ) : (LocalField F q)ˣ →* rootsOfUnity 3 F :=
    { toFun := fun x => KPHilbert.B3 F ζ hζ (Sum.inr q) x d
      map_one' := BoneL F ζ hζ q d
      map_mul' := fun x y => (B3_laws₀).1 x y d}
  let BR (d : (LocalField F q)ˣ) : (LocalField F q)ˣ →* rootsOfUnity 3 F :=
    { toFun := KPHilbert.B3 F ζ hζ (Sum.inr q) d
      map_one' := BoneR F ζ hζ q d
      map_mul' := (B3_laws₀).2.1 d}
  have hs := (B3_laws₀).2.2.2.1
    (-(y^3)/c) (D/c) (by simp [D]; field_simp; ring)
  change BL (D/c) (-(y^3)/c) = 1 at hs
  rw [map_div] at hs
  have hn : BL (D/c) (-(y^3)) = 1 := by
    change KPHilbert.B3 F ζ hζ (Sum.inr q) (-(y^3)) (D/c) = 1
    rw [Bnegleft]; exact (B3_laws₀).2.2.2.2.1 _ _ |>.1
  rw [hn, one_div, inv_eq_one] at hs
  change BR c (D/c) = 1 at hs
  rw [map_div] at hs
  simpa [((B3_laws₀).2.2.2.2.2 c |>.1), BR, D] using hs

end
end DedekindZetaZeroFree.KPActualFullKernelArithmetic
