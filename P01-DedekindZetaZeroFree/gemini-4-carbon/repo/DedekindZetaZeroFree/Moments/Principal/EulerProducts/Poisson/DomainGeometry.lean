module

public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.Poisson.Domain

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.EulerGeometry

open DedekindZetaZeroFree.Quantitative.EulerDomain

noncomputable section

open DedekindZetaZeroFree

theorem OmegaStar_isOpen : IsOpen OmegaStar := by
  simp only [OmegaStar, Set.setOf_and]
  repeat' apply IsOpen.inter
  all_goals
    first
    | exact isOpen_lt continuous_const (by fun_prop)
    | exact isOpen_lt (by fun_prop) continuous_const

end

end DedekindZetaZeroFree.Quantitative.EulerGeometry
