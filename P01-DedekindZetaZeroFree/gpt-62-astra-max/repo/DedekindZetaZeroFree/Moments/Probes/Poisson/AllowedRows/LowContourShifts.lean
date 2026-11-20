module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.ZControls
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.WControls
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.XiControls

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.LowRowContourShifts

noncomputable section

open DedekindZetaZeroFree DedekindZetaZeroFree.Quantitative.LowRowKernelDefinitions

variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (D : FixedData S η)

variable (u : D.Row) (hu : u.u ≠ 1) (Z : ℝ) (hZ : 0 < Z)

include hu hZ in
theorem Iwz_z_shift (ξ : ℂ) (hξ : ξ.re = 4) :
    Iwz D u ξ 4 2 Z = Iwz D u ξ 4 Scales.zLine Z := by
  unfold Iwz comparisonVerticalIntegral
  congr 2
  funext t
  exact LowRowZControls.Iz_shift D u hu Z hZ ξ _ hξ (by simp)

include hu hZ in
theorem Iwz_zw_shift (ξ : ℂ) (hξ : ξ.re = 4) :
    Iwz D u ξ 4 2 Z = Iwz D u ξ Scales.wLine Scales.zLine Z :=
  (Iwz_z_shift D u hu Z hZ ξ hξ).trans (LowRowWControls.Iwz_shift D u hu Z hZ ξ hξ)

include hu hZ in
theorem triple_shift :
    triple D u 4 4 2 Z = triple D u Scales.rightLine Scales.wLine Scales.zLine Z := by
  have h1 : triple D u 4 4 2 Z = triple D u 4 Scales.wLine Scales.zLine Z := by
    unfold triple comparisonVerticalIntegral
    congr 2
    funext t
    exact Iwz_zw_shift D u hu Z hZ _ (by simp)
  exact h1.trans (LowRowXiControls.triple_xi_shift D u hu Z hZ)

include hu hZ in
theorem triple_shift_K :
    comparisonVerticalIntegral 4 (fun ξ => comparisonVerticalIntegral 4
        (fun w => comparisonVerticalIntegral 2 (fun z => PoissonKernel.K D u ξ w z Z))) =
      comparisonVerticalIntegral Scales.rightLine (fun ξ => comparisonVerticalIntegral Scales.wLine
        (fun w => comparisonVerticalIntegral Scales.zLine (fun z => PoissonKernel.K D u ξ w z Z))) :=
  triple_shift D u hu Z hZ

end

end DedekindZetaZeroFree.Quantitative.LowRowContourShifts
