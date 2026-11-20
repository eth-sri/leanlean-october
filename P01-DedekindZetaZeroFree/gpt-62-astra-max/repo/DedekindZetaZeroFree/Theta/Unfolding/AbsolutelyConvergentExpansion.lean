module

public import DedekindZetaZeroFree.Moments.Reflected.RankOneExpansion

@[expose] public section

namespace DedekindZetaZeroFree.MomentSources
noncomputable section
variable {F : Type} [Field F] [NumberField F]

alias source_exists := DedekindZetaZeroFree.ThetaExpansion.selected_rank_one_expansion

end
end DedekindZetaZeroFree.MomentSources
