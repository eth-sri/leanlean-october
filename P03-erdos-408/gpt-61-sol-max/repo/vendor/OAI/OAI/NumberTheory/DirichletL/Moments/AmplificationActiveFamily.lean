module

public import OAI.NumberTheory.DirichletL.Moments.AmplificationActiveFactor

@[expose] public section

namespace OAI


open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationActiveFamily
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentAmplificationShortening CenteredMomentAmplificationActiveFactor
open CenteredMomentAmplificationFamilyEnergy CenteredMomentAmplificationSourceDomain
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow CenteredMomentChildRows
open CenteredMomentSourceRow CenteredMomentOriginalChildEnergy CenteredMomentGaussEnergy


 theorem actual_error_energy_active  S   p   hp 
    (hs : Supported (Ideal.span {p}))  n  (hn : n=0 ∨ n=5 ∨ n=6)
     c   W   K  :
    sourceGaussEnergy (residualColumns S p hp (n+1)) c
      (fun I => residualCharacter p (n+1) (primaryGenerator I)) W K=
    sourceGaussEnergy (residualColumns S p hp (n+1)) c
      (fun I => residualCharacter p (errorMovingExponent n) (primaryGenerator I)) W K := by
  let Q := residualColumns S p hp (n+1)
  apply congrArg (fun f : supportedColumns Q → ℂ =>
    gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q) f W K)
  funext I
  dsimp only
  rw [residual_column_active S p hp hs n hn I (Finset.mem_filter.mp I.property).1]

end SevenEighths.CenteredMomentAmplificationActiveFamily



end OAI
