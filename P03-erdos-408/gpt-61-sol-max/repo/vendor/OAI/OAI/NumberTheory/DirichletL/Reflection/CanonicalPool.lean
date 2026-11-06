module

public import OAI.NumberTheory.DirichletL.Reflection.NormalizedPhysical

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve



lemma maximal_coprime_of_not_dvd (P J : Ideal ActualEisensteinCubic.O) [P.IsMaximal] (h : ¬P∣J) : IsCoprime P J := by
  rw [Ideal.isCoprime_iff_codisjoint]
  apply ((Ideal.isMaximal_def.mp (inferInstance : P.IsMaximal)).not_le_iff_codisjoint).mp
  exact fun hle => h (Ideal.dvd_iff_le.mpr hle)


end SevenEighths.InverseReflectedPhase

end OAI
