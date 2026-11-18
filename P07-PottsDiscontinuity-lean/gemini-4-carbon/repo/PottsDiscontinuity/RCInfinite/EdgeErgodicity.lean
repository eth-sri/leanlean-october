module

public import PottsDiscontinuity.FK.BoxTranslation
public import PottsDiscontinuity.Frozen.Defs.IsTranslationErgodic

@[expose] public section

open MeasureTheory Set

namespace PottsDiscontinuity.RCInfinite
open FK

/-- Translate a bond field by `a`; the new value at `e` is the old value at `e-a`. -/
abbrev edgeTranslate (a : LatticeVertex) : LatticeConfiguration ≃ LatticeConfiguration :=
  latticeConfigurationTranslate a

theorem edgeTranslate_measurable (a : LatticeVertex) : Measurable (edgeTranslate a) :=
  latticeConfigurationTranslate_measurable a




end PottsDiscontinuity.RCInfinite
