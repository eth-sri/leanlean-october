module

public import OAI.NumberTheory.DirichletL.Moments.FirstAnnularAmplification
public import OAI.NumberTheory.DirichletL.Moments.AmplificationChildInput

@[expose] public section

namespace OAI


open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentFirstAnnularInput
open HeckeFamily CanonicalQuadraticSieve CenteredMomentGaussEnergy
open CenteredMomentAmplificationChildInput CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalChildEnergy CenteredMomentSecondHeightFamily
open CenteredMomentHeckeColumnWindow CenteredMomentGaussNormalization
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentCommonAllocationSum

variable {ι:Type*}[Fintype ι]

theorem normalized_input_coefficient (s:Input ι) R seed 
     W  H :
    (gaussEnergy Finset.univ (sourceGenerator (original s R seed).columns)
      (sourceGenerator_supported (original s R seed).columns)
      ((original s R seed).coefficient s.η fixedBadMask s.t (volume s)) W H).re=
      normalizedGaussSource s R seed W H:=by
  unfold OriginalData.coefficient normalizedGaussSource sourceGaussEnergy
  rw [show (fun I:supportedColumns (original s R seed).columns=>
      (Real.sqrt (volume s):ℂ)⁻¹*((original s R seed).beta I*
        CenteredMomentHeckeExpansion.rowWeight s.η fixedBadMask 1 1 s.t I))=
      (fun I:supportedColumns (original s R seed).columns=>(Real.sqrt (volume s):ℂ)⁻¹*
        ((original s R seed).beta I*heightCoeff s.η s.t I)) by
    funext I
    rw [←heightCoeff_eq_fixed_rowWeight s.η s.t I (Finset.mem_filter.mp I.property).2]]
  exact gaussEnergy_central _ _ _ _ (volume s) (volume_pos s) W H

end SevenEighths.CenteredMomentFirstAnnularInput



end OAI
