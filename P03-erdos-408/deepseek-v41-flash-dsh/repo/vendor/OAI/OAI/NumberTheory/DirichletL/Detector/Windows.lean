module

public import OAI.NumberTheory.DirichletL.Detector.Physical

@[expose] public section

namespace OAI

noncomputable section

namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss
local notation "O" => ActualEisensteinCubic.O

theorem elementWindow_finite_support (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (R : ℝ) (hR : 0 < R) :
    (Function.support (fun m : O => W (elementNorm m / R))).Finite := by
  obtain ⟨B, hB, hbound⟩ := compact_window_bound W hW
  obtain ⟨M, hM⟩ := exists_nat_gt (B * R)
  apply (ShortDraftLatticeCount.rowNormBall M).finite_toSet.subset
  intro m hm
  apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le
  have hnorm : elementNorm m ≤ B * R := (div_le_iff₀ hR).mp (hbound _ hm)
  unfold elementNorm at hnorm
  exact_mod_cast hnorm.trans hM.le

theorem idealWindow_finite_support (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (R : ℝ) (hR : 0 < R) :
    (Function.support (fun I : Ideal O => W ((Ideal.absNorm I : ℝ) / R))).Finite := by
  obtain ⟨B, hB, hbound⟩ := compact_window_bound W hW
  obtain ⟨M, hM⟩ := exists_nat_gt (B * R)
  apply (Ideal.finite_setOfPred_absNorm_le M).subset
  intro I hI
  have hnorm : (Ideal.absNorm I : ℝ) ≤ B * R := (div_le_iff₀ hR).mp (hbound _ hI)
  exact_mod_cast hnorm.trans hM.le

end SevenEighths.ProbePhysical
end

end OAI
