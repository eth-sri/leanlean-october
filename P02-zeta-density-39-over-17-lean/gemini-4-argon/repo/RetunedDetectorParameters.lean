module
public import QuadraticWindow
public import MathCollab.Density.Stronger.InitialDetector

@[expose] public section

open Filter
open scoped Topology
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density.Stronger

def smoothingExponent (a : ℝ) : ℝ := 3*a/2

def detectorY (a T : ℝ) : ℝ := T^(smoothingExponent a)




