module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Hecke.DetectorSupportedWitness
public import OAI.NumberTheory.DirichletL.Hecke.DetectorRowCountEndpoint

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorAdaptiveCutoff
open HeckeFamily HeckeDetectorSupportedWitness HeckeDetectorRowCount

def cutoff (δ q : ℝ)  :=
  if δ≤5/6 then Endpoint.balancedCutoff δ (1/2-min (1/2) (max 0 (q/δ))) else 3/2

theorem cutoff_bounds  δ q  (hδ : 0≤δ) : 1≤cutoff δ q ∧ cutoff δ q≤3/2 := by
  unfold cutoff
  split_ifs with hd
  · exact balanced_cutoff_bounds hδ hd (le_min (by norm_num) (le_max_left _ _)) (min_le_left _ _)
  · norm_num

theorem cutoff_eq_balanced  δ q  (hδ : 0<δ) (hd : δ≤5/6)
    (hq : 0≤q) (hq' : q≤δ/2) :
    cutoff δ q=Endpoint.balancedCutoff δ (1/2-q/δ) := by
  have hx : 0≤q/δ := div_nonneg hq hδ.le
  have hx' : q/δ≤1/2 := (div_le_iff₀ hδ).mpr (by linarith)
  simp_all [cutoff]

theorem cutoff_eq_high  δ q  (hδ : 5/6<δ) : cutoff δ q=3/2 := by
  simp only [cutoff,ite_eq_right (not_le_of_gt hδ)]

end SevenEighths.HeckeDetectorAdaptiveCutoff

end

end OAI
