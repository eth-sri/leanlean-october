module

public import RequestProject.HerglotzSchurPos
public import RequestProject.HerglotzAdmissible

/-!
# Lemma 8.6 (negative index at small energy)

Combining the Schur complement reduction (`SmallEnergyForm.lean`), Lemma 8.2
(`small_energy_imForm_basisVec_neg`), Lemma 8.5 on Herglotz data (`herglotz_imSchur_nonneg`) and
the construction of admissible Herglotz data (`exists_admissible_herglotzVec`), we prove the
analytic core `small_energy_schur_core` and hence Lemma 8.6 (`small_energy_herglotz_bound'`).
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ComplexConjugate Real InnerProductSpace

noncomputable section
namespace PolyaNeumann

/-- **Lemma 8.6 on Herglotz data.** -/
theorem small_energy_herglotz_bound'  (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω)  (hγ : IsBoundaryParam Ω γ) :
    ∃ δ > 0, ∀ E, 0 < E → E < δ → ∀ W : ℝ → Ell2 →L[ℂ] Ell2, IsTransport γ E W →
      ∃ L : (ℝ → ℂ) →ₗ[ℂ] (Fin 1 → ℂ), ∀ a, IsDirDensity a → L a = 0 →
        0 ≤ herglotzForm W γ E a := by
  obtain ⟨δ, hδ, h⟩ : ∃ δ > 0, ∀ E, 0 < E → E < δ → ∀ W : ℝ → Ell2 →L[ℂ] Ell2, IsTransport γ E W → ∀ v : Ell2, imPair (monodromy W) (basisVec 0) v = 0 → 0 ≤ imForm (monodromy W) v := by
    obtain ⟨δ₁, hδ₁, h₁⟩ := small_energy_imForm_basisVec_neg hb hL hγ
    obtain ⟨δ₂, hδ₂, h₂⟩ : ∃ δ > 0, ∀ E, 0 < E → E < δ → ∀ W : ℝ → Ell2 →L[ℂ] Ell2, IsTransport γ E W → ∀ v : Ell2, (∃ N : ℕ, ∀ n, N ≤ n → (v : ℕ → ℂ) n = 0) → ∃ t : ℂ, 0 ≤ imSchur (monodromy W) (basisVec 0) (v + t • basisVec 0) := by
      obtain ⟨z₁, hz₁⟩ := hL.1.2.nonempty
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hL.1.1 z₁ hz₁
      obtain ⟨δ₅, hδ₅, h₅⟩ := herglotz_imSchur_nonneg hb hL hγ hr hball
      obtain ⟨δa, hδa, hadm⟩ := exists_admissible_herglotzVec hb (ENNReal.toReal_pos (hL.1.1.measure_pos volume hL.1.2.nonempty).ne' hb.measure_lt_top.ne) (γ 0) z₁
      refine ⟨min δ₅ (δa ^ 2), lt_min hδ₅ (by positivity), fun E hE hEδ W hW v _ => ?_⟩
      obtain ⟨t, a, ha, hvec, hneg, hmean⟩ := hadm (Real.sqrt E) (by
        rw [abs_of_nonneg (Real.sqrt_nonneg E), show δa = Real.sqrt (δa ^ 2) from
          (Real.sqrt_sq hδa.le).symm]
        exact Real.sqrt_lt_sqrt hE.le (hEδ.trans_le (min_le_right _ _))) v
      refine ⟨t, ?_⟩
      rw [← hvec]
      exact h₅ E hE (hEδ.trans_le (min_le_left _ _)) W hW a ha hneg hmean
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun E hE hEδ W hW v hv => ?_⟩
    refine nonneg_of_imSchur_nonneg (monodromy W) dense_finSupp (fun w hw => ?_) v hv
    obtain ⟨t, ht⟩ := (h₂ E hE (hEδ.trans_le (min_le_right _ _)) W hW) w hw
    rwa [imSchur_add_smul _ (h₁ E hE (hEδ.trans_le (min_le_left _ _)) W hW).ne] at ht
  obtain ⟨K, hK⟩ := hγ.lipschitz
  refine ⟨δ, hδ, fun E hE hEδ W hW => ?_⟩
  set U := monodromy W
  set ℓ : Ell2 →ₗ[ℂ] ℂ :=
    { toFun := fun v => imPair U (basisVec 0) v
      map_add' := fun v w => imPair_add_right U _ v w
      map_smul' := fun c v => imPair_smul_right U _ v c }
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (ℓ.comp (herglotzVecLin (Real.sqrt E) (γ 0)))
  refine ⟨(LinearMap.pi fun _ => g), fun a ha hLa => ?_⟩
  rw [herglotzForm_eq_im hK (by simpa using hγ.periodic 0) hW ha]
  have := h E hE hEδ W hW (herglotzVec ha (Real.sqrt E) (γ 0)) (by rw [← (show g a = imPair U (basisVec 0) (herglotzVec ha (Real.sqrt E) (γ 0)) by
    simpa [ℓ, herglotzVecLin] using (congrArg (fun F => F ⟨a, ha⟩) hg)), show g a = 0 by
    simpa using congrFun hLa 0])
  unfold imForm at this
  exact this

end PolyaNeumann

end
