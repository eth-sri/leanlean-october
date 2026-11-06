module

public import OAI.NumberTheory.DirichletL.Foundation

@[expose] public section

namespace OAI

noncomputable section


namespace SevenEighths.InverseMoment

theorem exists_canonical_reference_cutoff (lo hi : ℝ) :
    ∃ Vlog : SchwartzMap ℝ ℂ, ∃ Alog : ℝ, 0 < Alog ∧
      Alog = CanonicalCubeSeparation.columnWindowRadius lo hi + 1 ∧
      HasCompactSupport Vlog ∧
      tsupport Vlog ⊆ Set.Icc (-Alog) Alog ∧
      (∀ x, Vlog x ≠ 0 → |x| ≤ Alog) ∧
      (∀ x, |x| ≤ CanonicalCubeSeparation.columnWindowRadius lo hi → Vlog x = 1) ∧
      Vlog 0 = 1 := by
  obtain ⟨v, hvc, hvs, hvone, hvbox, hvzero⟩ :=
    FourierBridge.exists_complex_smooth_cutoff
      (CanonicalCubeSeparation.columnWindowRadius lo hi)
      (CanonicalCubeSeparation.columnWindowRadius_nonneg lo hi)
  let Vlog : SchwartzMap ℝ ℂ := hvc.toSchwartzMap hvs
  refine ⟨Vlog, CanonicalCubeSeparation.columnWindowRadius lo hi + 1,
    by linarith [CanonicalCubeSeparation.columnWindowRadius_nonneg lo hi],
    rfl, hvc, hvbox, ?_, hvone, hvzero⟩
  intro x hx
  exact abs_le.mpr (hvbox (subset_tsupport v hx))

theorem eventually_canonical_reference_gates (hi Alog window eta : ℝ)
    (heta : 0 < eta) :
    ∃ Z0 : ℝ, 1 < Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      2 ≤ Z ∧ 2 ≤ Z ^ eta ∧ Real.exp 1 ≤ Z ^ eta ∧
      1 ≤ eta * Real.log Z ∧ hi ≤ Z ^ eta ∧
      Real.exp Alog ≤ Z ^ eta ∧ Real.exp window ≤ Z ^ eta := by
  let R : ℝ := 2 + |hi| + |Alog| + |window|
  have hR : 1 ≤ R := by
    dsimp [R]
    linarith [abs_nonneg hi, abs_nonneg Alog, abs_nonneg window]
  refine ⟨2 + Real.exp (R / eta), by linarith [Real.exp_pos (R / eta)], ?_⟩
  intro Z hZ
  have hZtwo : 2 ≤ Z := by linarith [Real.exp_pos (R / eta)]
  have hZpos : 0 < Z := by linarith
  have hZexp : Real.exp (R / eta) ≤ Z := by linarith
  have hlog := Real.log_le_log (by positivity) hZexp
  rw [Real.log_exp] at hlog
  have hRlog : R ≤ Real.log Z * eta := (div_le_iff₀ heta).mp hlog
  have hpow : Real.exp R ≤ Z ^ eta := by
    rw [Real.rpow_def_of_pos hZpos]
    exact Real.exp_le_exp.mpr hRlog
  have hexp : Real.exp 1 ≤ Z ^ eta :=
    (Real.exp_le_exp.mpr hR).trans hpow
  refine ⟨hZtwo, (by linarith [Real.add_one_le_exp (1 : ℝ)] : 2 ≤ Real.exp 1).trans
    hexp, hexp, by nlinarith, ?_, ?_, ?_⟩
  · have hhi : hi ≤ R := by
      dsimp [R]
      linarith [le_abs_self hi, abs_nonneg Alog, abs_nonneg window]
    exact hhi.trans ((by linarith [Real.add_one_le_exp R] : R ≤ Real.exp R).trans hpow)
  · apply (Real.exp_le_exp.mpr ?_).trans hpow
    grind
  · apply (Real.exp_le_exp.mpr ?_).trans hpow
    grind

end SevenEighths.InverseMoment

end

end OAI
