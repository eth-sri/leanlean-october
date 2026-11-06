module
public import OAI.NumberTheory.DirichletL.Inversion.InitialDetectorSource
public import OAI.NumberTheory.DirichletL.Inversion.SecondChildWindows
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.DetectorDictionaryInverseRawRadial
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialDetectorSource
open InverseInitialRawDictionary InverseInitialConjugateEnergy CanonicalQuadraticSieve
open ConcreteTraceCRT ActualEisensteinCubic
local notation "O"=>HeckeFamily.O

theorem exists_raw_radial_majorant :
    ∃Φ : 𝓢(ℝ,ℂ),HasCompactSupport (Φ:ℝ→ℂ) ∧
      (∀x,0≤(Φ x).re) ∧ (∀x∈Set.Icc (0:ℝ) 1,Φ x=1) := by
  have hsub : Set.Icc (0:ℝ) 1⊆Set.Ioo (-1) 2 := by
    intro x hx
    grind
  obtain ⟨f,hf,_,hs,hone⟩:=exists_contDiff_support_eq_eq_one_iff
    (n:=⊤) isOpen_Ioo isClosed_Icc hsub
  let v : ℝ→ℂ:=fun x=>((f x)^2:ℝ)
  have hv : ContDiff ℝ ∞ v:=Complex.ofRealCLM.contDiff.comp
    ((by grind : ContDiff ℝ ∞ f).pow 2)
  have hsupp : Function.support v⊆Set.Icc (-1) 2 := by
    intro x hx
    have hn : x∈Function.support f := by
      intro hz
      aesop
    rw [hs] at hn
    grind
  have hvc:=HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  refine ⟨hvc.toSchwartzMap hv,hvc,?_,?_⟩
  pm_1109
  aesop

end SevenEighths.DetectorDictionaryInverseRawRadial

end

end OAI
