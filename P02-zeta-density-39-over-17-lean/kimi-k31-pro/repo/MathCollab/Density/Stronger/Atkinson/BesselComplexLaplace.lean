module
public import MathCollab.Density.Stronger.Atkinson.BesselK0Mellin
public import WeylPort.Analytic.ComplexLaplace

@[expose] public section
namespace MathCollab.Density.Stronger.Atkinson
export RiemannZeta.GuthMaynard (
  integrableOn_cpow_mul_cexp_neg_complex_mul_Ioi dfiComplexLaplace
  hasDerivAt_dfiComplexLaplace analyticOnNhd_dfiComplexLaplace
  dfiComplexLaplace_ofReal dfiComplexLaplace_eq)
end MathCollab.Density.Stronger.Atkinson
