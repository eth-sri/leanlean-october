module

public import HypoellipticAleksandrov.Parabolic.SpacetimeMollifier
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.GenericPreLiftSpatialDifferenceQuotientEnergyIdentity

open private HypoellipticAleksandrov.Parabolic.tsupport_spacetimeMollification_subset_cthickening from HypoellipticAleksandrov.Parabolic.GenericPreLiftSpatialDifferenceQuotientEnergyIdentity


/-!
# Support of spacetime mollification

This module records the closed-thickening support bound for the fixed
spacetime mollification.
-/

 public section



open MeasureTheory
open scoped Convolution Pointwise

namespace HypoellipticAleksandrov.Parabolic.SpacetimeMollifier

/-- Topological support of a positive-radius mollification lies in the
closed radius thickening of the original topological support. -/
alias tsupport_spacetimeMollification_subset_cthickening := _root_.HypoellipticAleksandrov.Parabolic.tsupport_spacetimeMollification_subset_cthickening


end HypoellipticAleksandrov.Parabolic.SpacetimeMollifier
