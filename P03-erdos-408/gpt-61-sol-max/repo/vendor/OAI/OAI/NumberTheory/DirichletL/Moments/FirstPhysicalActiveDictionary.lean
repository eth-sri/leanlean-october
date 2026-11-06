module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.FirstSourceReduction
public import OAI.NumberTheory.DirichletL.Moments.SecondActivePhysicalDictionary

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalActiveDictionary
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSourceRow CenteredMomentRowNorm CenteredMomentHeckeExpansion
open CenteredMomentFirstSectors CenteredMomentFirstSectorEnergy CenteredMomentFirstSectorTransform
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentCompleteCommon
open CenteredMomentSupportedCorrelation CenteredMomentCommonSupport CenteredMomentActive
open CenteredMomentFirstReduced CenteredMomentFirstFrequency CenteredMomentFirstWholeKernel
open CenteredMomentFirstColumns CenteredMomentFirstAssembly CenteredMomentGaussEnergy
open CenteredMomentSmooth CenteredMomentScale CenteredMomentPrimitive IdealMobiusDivisorSum
open CenteredMomentFirstPhysicalSource CenteredMomentActiveSource


theorem columns_active  C D   hD   S 
     β  :
    columns C D hD (activeSource S β)=
      (columns C D hD S).filter (fun I=>β (D*I)≠0) := by
  ext I
  simp only [columns,Finset.mem_filter,mem_residualPool,supportedColumns_active]
  tauto

theorem column_sum_active (C D : Ideal HeckeFamily.O) (hD : D≠0) (S : Finset (Ideal HeckeFamily.O))
    (β f : Ideal HeckeFamily.O→ℂ) (hf : ∀I,β (D*I)=0→f I=0) :
    (∑I∈columns C D hD (activeSource S β),f I)=∑I∈columns C D hD S,f I := by
  rw [columns_active,Finset.sum_filter]
  apply Finset.sum_congr rfl
  simp_all

theorem column_pair_sum_active (C D : Ideal HeckeFamily.O) (hC : C≠0) (hD : D≠0)
    (S : Finset (Ideal HeckeFamily.O)) (β : Ideal HeckeFamily.O→ℂ) (f : Ideal HeckeFamily.O→Ideal HeckeFamily.O→ℂ)
    (hl : ∀I J,β (C*I)=0→f I J=0) (hr : ∀I J,β (D*J)=0→f I J=0) :
    (∑I∈columns C C hC (activeSource S β),∑J∈columns C D hD (activeSource S β),f I J)=
      ∑I∈columns C C hC S,∑J∈columns C D hD S,f I J := by
  simp_rw [column_sum_active C D hD S β _ (hr _)]
  aesop (add safe [column_sum_active, S])

lemma primary_supported  I  (hI : Supported I) :
    Supported (Ideal.span {CompletedGauss.primaryGenerator I}) := by
  rw [primary_span_supported I hI]
  exact hI

def physicalTerm (η : Character) (m A : HeckeFamily.O) (t : ℝ) (β : Ideal HeckeFamily.O→ℂ)
    (C D ) (hC : Supported C) (E : Finset (CommonIndex C D))
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ)
    (h : HeckeFamily.O) (I J : Ideal HeckeFamily.O)  :=
  if hI : Supported I then if hJ : Supported J then
    let na:=CompletedGauss.primaryGenerator I
    let nb:=CompletedGauss.primaryGenerator J
    let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
    let k:=K/‖eisEmbedding e‖^2
    let r:=activeConductor C D
    if IsCoprime I J then
      (tripleRow na nb r (supportedModulusCharacter na (primary_supported I hI))
        (supportedModulusCharacter nb (primary_supported J hJ))⁻¹ (activeFunction C D hC) e *
      ((k/‖eisEmbedding (na*(nb*r))‖^2:ℝ):ℂ)*
      tripleFourier na nb r
        (supported_element_ne_zero _ (primary_supported I hI))
        (supported_element_ne_zero _ (primary_supported J hJ))
        (finitePrimeModulus_ne_zero _) (supportedModulusCharacter na (primary_supported I hI))
        (supportedModulusCharacter nb (primary_supported J hJ))⁻¹ (activeFunction C D hC) h)*
      (coefficient η m A t β C I*star (coefficient η m A t β D J))*
      windows V (k/‖eisEmbedding r‖^2) (‖eisEmbedding h‖^2)
        (‖eisEmbedding na‖^2) (‖eisEmbedding nb‖^2) K₀ H₀ A₀ B₀*
      EisensteinSchwartzPoisson.paperRadialFourier W
        (k*‖eisEmbedding h‖^2/‖eisEmbedding (na*(nb*r))‖^2)
    else 0
  else 0 else 0

theorem physicalTerm_zero_left  η   m A   t   β 
     C D   hC   E 
     W   V   K K₀ H₀ A₀ B₀ 
     h   I J  (hi : β (C*I)=0) :
    physicalTerm η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J=0 := by
  simp_all [physicalTerm, coefficient]

theorem physicalTerm_zero_right  η   m A   t   β 
     C D   hC   E 
     W   V   K K₀ H₀ A₀ B₀ 
     h   I J  (hj : β (D*J)=0) :
    physicalTerm η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J=0 := by
  simp_all [physicalTerm, coefficient]

theorem block_eq_ideal_sums  η   m A   t 
     S   β   C D 
     hC   hD   E 
     rows   W   V   K K₀ H₀ A₀ B₀  :
    block η m A t S β C D hC hD E rows W V K K₀ H₀ A₀ B₀=
      inactiveWeight C D E * ∑h∈rows,
        ∑I∈columns C C hC.1 S,∑J∈columns C D hD.1 S,
          physicalTerm η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J := by
  unfold block
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  calc
    _=∑I:columns C C hC.1 S,∑J:columns C D hD.1 S,
        physicalTerm η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J := by
      apply Finset.sum_congr rfl
      intro I hI
      apply Finset.sum_congr rfl
      intro J hJ
      simp only [physicalTerm,dite_eq_left (column_supported C C hC.1 S I),
        dite_eq_left (column_supported C D hD.1 S J),element]
      rfl
    _=_ := by
      simp_rw [Finset.sum_coe_sort]
      exact Finset.sum_coe_sort (columns C C hC.1 S)
        (fun I=>∑J∈columns C D hD.1 S,
          physicalTerm η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J)

theorem block_active  η   m A   t 
     S   β   C D 
     hC   hD   E 
     rows   W   V   K K₀ H₀ A₀ B₀  :
    block η m A t (activeSource S β) β C D hC hD E rows W V K K₀ H₀ A₀ B₀=
      block η m A t S β C D hC hD E rows W V K K₀ H₀ A₀ B₀ := by
  rw [block_eq_ideal_sums,block_eq_ideal_sums]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  exact column_pair_sum_active C D hC.1 hD.1 S β
    (physicalTerm η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h)
    (physicalTerm_zero_left η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h)
    (physicalTerm_zero_right η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h)

variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _
open CenteredMomentCommonRadialData CenteredMomentFirstRetainedNorm
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentFirstScale
open CenteredMomentSectorLocalization CenteredMomentLogDyadic

theorem original_sectorMass_active (s : Input ι)  R seed 
     m A   t   S   C D 
     hC   hD   W   K X Z ξ  :
    sectorMass s R seed m A t
        (activeSource S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed))
        C D hC hD W K X Z ξ=
      sectorMass s R seed m A t S C D hC hD W K X Z ξ := by
  unfold sectorMass
  apply Finset.sum_congr rfl
  intro E hE
  dsimp only
  apply Finset.sum_congr rfl
  intro n hn
  rw [block_active]

theorem active_sectorMass_sum (s : Input ι)  R seed 
     m A   t   S   Φ   K X Z ξ  :
    let T:=activeSource S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
    (∑p:commonLabels (supportedColumns T) (supportedColumns T),
      sectorMass s R seed m A t T p.val.1 p.val.2
        (commonLabels_supported T p).1 (commonLabels_supported T p).2 Φ K X Z ξ)=
    ∑p:commonLabels (supportedColumns T) (supportedColumns T),
      sectorMass s R seed m A t S p.val.1 p.val.2
        (commonLabels_supported T p).1 (commonLabels_supported T p).2 Φ K X Z ξ := by
  dsimp only
  apply Finset.sum_congr rfl
  grind [original_sectorMass_active, S]

theorem physicalMass_full_source [DecidableEq ι] (s : Input ι)  R seed 
     m A   Φ   K Z ξ  :
    CenteredMomentFirstSourceReduction.physicalMass s R seed m A Φ K Z ξ=
      let S:=CenteredMomentSourceMass.finiteColumns (Fintype.piFinset s.pools)
      let β:=CenteredMomentOriginalCommonHarmonic.coefficient s R seed
      let T:=activeSource S β
      ∑p:commonLabels (supportedColumns T) (supportedColumns T),
        sectorMass s R seed m A s.t S p.val.1 p.val.2
          (commonLabels_supported T p).1 (commonLabels_supported T p).2 Φ K
          (CenteredMomentExceptionalAmplitudePair.volume s.toData) Z ξ := by
  solve_by_elim [active_sectorMass_sum, CenteredMomentSourceMass.finiteColumns, Fintype.piFinset, CenteredMomentExceptionalAmplitudePair.volume]

end SevenEighths.CenteredMomentFirstPhysicalActiveDictionary

end

end OAI
