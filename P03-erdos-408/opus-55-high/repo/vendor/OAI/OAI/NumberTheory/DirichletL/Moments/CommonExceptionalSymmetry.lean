module

public import OAI.NumberTheory.DirichletL.Moments.CommonExceptionalSource

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentCommonExceptionalSymmetry
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

lemma same_raw_better_cap (r c d:ℝ):
    max (max (r-c) 0) (max (r-d) 0)=max (r-min c d) 0:=by
  grind

end SevenEighths.CenteredMomentCommonExceptionalSymmetry

end

end OAI
