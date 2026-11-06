module
public import Mathlib

public import PottsDiscontinuity.PottsThm.CriticalParameters
public import PottsDiscontinuity.Potts.FreePottsLimit
public import PottsDiscontinuity.Potts.WiredPottsLimit

@[expose] public section

namespace PottsDiscontinuity.PottsThm

open MeasureTheory

open PottsDiscontinuity.FK
open PottsDiscontinuity.Potts

/-- Select the free limit and all `q` positively pinned limits at the frozen
critical inverse temperature, retaining their Edwards--Sokal colorings. -/
theorem exists_critical_coloured_limits (q : ℕ) (hq : 4 < q) :
    ∃ (μ : Fin (q + 1) → ProbabilityMeasure (SpinSpace q))
      (φ₀ : ProbabilityMeasure LatticeConfiguration)
      (φp : Fin q → ProbabilityMeasure LatticeConfiguration),
      IsRCInfiniteVolumeLimit (criticalFKParameters q hq).toP
        (criticalFKParameters q hq).toQ 0 φ₀.toMeasure ∧
      IsPottsInfiniteVolumeLimit q (pottsCriticalBeta q) 0 (μ 0).toMeasure ∧
      IsFreeEdwardsSokalColouring q φ₀.toMeasure (μ 0).toMeasure ∧
       ∀ i : Fin q,
        IsRCInfiniteVolumeLimit (criticalFKParameters q hq).toP
          (criticalFKParameters q hq).toQ 1 (φp i).toMeasure ∧
        IsPottsInfiniteVolumeLimit q (pottsCriticalBeta q) i.succ
          (μ i.succ).toMeasure ∧
        IsWiredEdwardsSokalColouring q (φp i).toMeasure i.succ
          (by simp only [Fin.val_succ]; omega) (μ i.succ).toMeasure  := by
  
  have hβ  := pottsCriticalBeta_pos q hq
  obtain ⟨φ₀, μ₀, hRC₀, hμ₀, hES₀⟩ :=
    exists_free_potts_limit_with_colouring q (by omega) (pottsCriticalBeta q) hβ
  have hpos (i : Fin q) :
      ∃ (φ : ProbabilityMeasure LatticeConfiguration)
        (μ : ProbabilityMeasure (SpinSpace q)),
        IsRCInfiniteVolumeLimit (criticalFKParameters q hq).toP
          (criticalFKParameters q hq).toQ 1 φ.toMeasure ∧
        IsPottsInfiniteVolumeLimit q (pottsCriticalBeta q) i.succ μ.toMeasure ∧
        IsWiredEdwardsSokalColouring q φ.toMeasure i.succ
          (by simp only [Fin.val_succ]; omega) μ.toMeasure := by
    obtain ⟨φ, μ, hRC, hμ, hES⟩ :=
      exists_wired_potts_limit_with_colouring q (by omega) (pottsCriticalBeta q) hβ
        i.succ (by simp only [Fin.val_succ]; omega)
    refine ⟨φ, μ, ?_, hμ, hES⟩
    all_goals aesop
  choose φp μp hRCp hμp hESp using hpos
  let μ : Fin (q + 1) → ProbabilityMeasure (SpinSpace q) :=
    fun j => Fin.cases μ₀ (μp) j
  refine ⟨μ, φ₀, φp, ?_, ?_, ?_, ?_⟩
  · assumption
  · simpa [μ] using hμ₀
  · simpa [μ] using hES₀
  · aesop

end PottsDiscontinuity.PottsThm
