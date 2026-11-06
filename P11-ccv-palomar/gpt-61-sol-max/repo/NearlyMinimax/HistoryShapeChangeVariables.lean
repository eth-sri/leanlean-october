module

public import NearlyMinimax.HistoryMaximalDelete

@[expose] public section

/-!
# Actual shape-level append/delete change of variables

The append range is identified with a true maximal-label condition in the
canonical heap. The actual append bijection and source rho factor yield an
exact infinite weighted sum change of variables. Mark integration and weak
transport are separate subsequent steps.
-/

noncomputable section
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

section
variable (dependent : J → J → Prop)
include dependent




end




end NearlyMinimax
