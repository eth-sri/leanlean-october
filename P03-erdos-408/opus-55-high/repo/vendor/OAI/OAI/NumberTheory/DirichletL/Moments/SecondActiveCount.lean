module

public import OAI.NumberTheory.DirichletL.Moments.ActiveSource
public import OAI.NumberTheory.DirichletL.Moments.RankinScale
public import OAI.NumberTheory.DirichletL.Moments.SecondSourceMask

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentSecondActiveCount
open CenteredMomentSourceRow CenteredMomentActiveSource
open CenteredMomentFirstSectors CenteredMomentCompleteCommon
open CenteredMomentRankinRadical

def commonShell (S : Finset (Ideal ActualEisensteinCubic.O)) (β : Ideal ActualEisensteinCubic.O→ℂ) (Y : ℝ) : Finset (Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O) :=
  (commonLabels (supportedColumns (activeSource S β)) (supportedColumns (activeSource S β))).filter
    (fun p=>(Ideal.absNorm (commonRadical p.1 p.2):ℝ)≤Y)

def partitionLabels (S : Finset (Ideal ActualEisensteinCubic.O)) (β : Ideal ActualEisensteinCubic.O→ℂ) (Y : ℝ) :
    Finset ((Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O)×Finset (Ideal ActualEisensteinCubic.O)) :=
  (commonShell S β Y).biUnion (fun p=>(IdealMobiusDivisorSum.primeSupport (commonRadical p.1 p.2)).powerset.image
    (fun U=>(p,U)))

theorem mem_partitionLabels (S : Finset (Ideal ActualEisensteinCubic.O)) (β : Ideal ActualEisensteinCubic.O→ℂ) (Y : ℝ)
    (p : (Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O)×Finset (Ideal ActualEisensteinCubic.O)) :
    p∈partitionLabels S β Y ↔ p.1∈commonShell S β Y ∧
      p.2⊆IdealMobiusDivisorSum.primeSupport (commonRadical p.1.1 p.1.2) := by
  simp only [partitionLabels,Finset.mem_biUnion,Finset.mem_image,Finset.mem_powerset]
  grind

theorem active_common_data (S : Finset (Ideal ActualEisensteinCubic.O)) (β : Ideal ActualEisensteinCubic.O→ℂ) (s : Ideal ActualEisensteinCubic.O)
    (hs : Squarefree s) (hmask : ∀I∈S,β I≠0 → s∣I) (Y : ℝ)
    (p : Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O) (hp : p∈commonShell S β Y) :
    p.1≠0 ∧ p.2≠0 ∧ CompletedGauss.primeSupport p.1=CompletedGauss.primeSupport p.2 ∧
      s∣p.1 ∧ s∣p.2 := by
  have hm := (Finset.mem_filter.mp hp).1
  obtain ⟨I,hi,J,hj,hIs,hJs,hβi,hβj,hC,hD⟩ := commonLabel_witnesses S β p.1 p.2 hm
  have hsR := old_mask_dvd_commonRadical s I J hs hIs.1 hJs.1 (by grind) (by grind)
  refine ⟨hC ▸ commonPart_ne_zero I J,hD ▸ commonPart_ne_zero J I,?_,?_,?_⟩
  · rw [←hC,←hD]
    exact commonParts_equal_support I J
  · rw [←hC]
    exact hsR.trans (commonRadical_dvd_commonPart I J)
  · rw [←hD]
    have hr : commonRadical I J=commonRadical J I := by unfold commonRadical;rw [Finset.inter_comm]
    rw [hr] at hsR
    exact hsR.trans (commonRadical_dvd_commonPart J I)

end SevenEighths.CenteredMomentSecondActiveCount

end

end OAI
