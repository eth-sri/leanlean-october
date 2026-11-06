module
public import MathCollab.Density.DetectorContour

@[expose] public section
open Complex MathCollab.Density MathCollab.Density.Contour
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement
alias short_detector_finite_rectangle_residue := MathCollab.Density.detector_finite_rectangle_residue
alias short_detector_finite_rectangle_kernel := MathCollab.Density.detector_finite_rectangle_kernel
