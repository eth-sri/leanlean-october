module

public import AnalyticESC.Generic.Density
public import AnalyticESC.Generic.Coincidences
public import AnalyticESC.Generic.Continuity
public import AnalyticESC.Main.Dichotomy

@[expose] public section

/-!
# Theorem 1.4

The IFSs of `𝔖_N` that satisfy the SESC contain a `d₂`-open and `d₂`-dense subset of `𝔖_N`, the
union class of decision D1. The open set consists of the systems whose dual IFS satisfies the SSC:
it is open by Lemma 2.7, its systems satisfy the SESC by Theorem 2.2, and it is dense by the
interpolation `IFS.exists_noCoincidence_near` and the density step. The density step combines two perturbations, so
it uses the triangle inequality for `d₂` between systems of `𝔖_N(ε)` for different `ε`. For `N = 0`
the dual IFS has no attractor, and the open set consists of all systems.
-/

namespace AnalyticESC

open Set Metric Filter Topology

namespace OpenDense

/-- The triangle inequality for `sup_{x ∈ I} |F(x) - H(x)|`, for maps continuous on `I`. -/
private theorem iSup_norm_sub_le_add {F G H : ℂ → ℂ}
    (hF : ContinuousOn F (((↑) : ℝ → ℂ) '' I)) (hG : ContinuousOn G (((↑) : ℝ → ℂ) '' I))
    (hH : ContinuousOn H (((↑) : ℝ → ℂ) '' I)) :
    (⨆ x : I, ‖F ((x : ℝ) : ℂ) - H ((x : ℝ) : ℂ)‖) ≤
      (⨆ x : I, ‖F ((x : ℝ) : ℂ) - G ((x : ℝ) : ℂ)‖) +
        ⨆ x : I, ‖G ((x : ℝ) : ℂ) - H ((x : ℝ) : ℂ)‖ :=
  Real.iSup_le (fun x => (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (add_le_add (le_ciSup (IFS.Continuity.bddAbove_range_norm_sub hF hG) x)
      (le_ciSup (IFS.Continuity.bddAbove_range_norm_sub hG hH) x)))
    (add_nonneg (Real.iSup_nonneg fun _ => norm_nonneg _) (Real.iSup_nonneg fun _ => norm_nonneg _))

/-- The `𝒞²` distance on `I` is nonnegative. -/
private theorem d2Map_nonneg (f g : ℂ → ℂ) : 0 ≤ d2Map f g :=
  add_nonneg (add_nonneg (Real.iSup_nonneg fun _ => norm_nonneg _)
    (Real.iSup_nonneg fun _ => norm_nonneg _)) (Real.iSup_nonneg fun _ => norm_nonneg _)

/-- The triangle inequality for `d₂` on `𝔖_N`, for systems in `𝔖_N(ε)` for different `ε`. -/
theorem d2_le_add {N : ℕ} {ε ε' ε'' : ℝ} (Φ : IFS N ε) (Φ' : IFS N ε') (Ψ : IFS N ε'') :
    d2 Φ Ψ ≤ d2 Φ Φ' + d2 Φ' Ψ := by
  refine Real.iSup_le (fun i => ?_)
    (add_nonneg (Real.iSup_nonneg fun _ => d2Map_nonneg _ _)
      (Real.iSup_nonneg fun _ => d2Map_nonneg _ _))
  obtain ⟨hf0, hf1, hf2⟩ := IFS.Continuity.continuousOn_f_deriv Φ i
  obtain ⟨hg0, hg1, hg2⟩ := IFS.Continuity.continuousOn_f_deriv Φ' i
  obtain ⟨hh0, hh1, hh2⟩ := IFS.Continuity.continuousOn_f_deriv Ψ i
  have e0 := iSup_norm_sub_le_add hf0 hg0 hh0
  have e1 := iSup_norm_sub_le_add hf1 hg1 hh1
  have e2 := iSup_norm_sub_le_add hf2 hg2 hh2
  exact (by unfold d2Map; linarith : d2Map (Φ.f i) (Ψ.f i) ≤
    d2Map (Φ.f i) (Φ'.f i) + d2Map (Φ'.f i) (Ψ.f i)).trans
    (add_le_add (le_ciSup (f := fun i => d2Map (Φ.f i) (Φ'.f i)) (finite_range _).bddAbove i)
      (le_ciSup (f := fun i => d2Map (Φ'.f i) (Ψ.f i)) (finite_range _).bddAbove i))

end OpenDense

/-- Theorem 1.4. The systems of `𝔖_N` satisfying the SESC contain a subset `U` of `𝔖_N` that is
open and dense in the `𝒞²` metric. -/
theorem theorem_1_4 (N : ℕ) :
    ∃ U : Set (Fin N → ℂ → ℂ),
      (∀ f ∈ U, ∃ ε : ℝ, ∃ Φ : IFS N ε, Φ.f = f ∧ Φ.SESC) ∧
      (∀ f ∈ U, ∃ r > 0, ∀ g, InUnionClass g → d2Sys f g < r → g ∈ U) ∧
      (∀ f, InUnionClass f → ∀ r > 0, ∃ g ∈ U, d2Sys f g < r) := by
  refine ⟨{f | ∃ ε : ℝ, ∃ Φ : IFS N ε, Φ.f = f ∧ (0 < N → Φ.DualSSC)}, ?_, ?_, ?_⟩
  · rintro _ ⟨ε, Φ, rfl, hΦ⟩
    refine ⟨ε, Φ, rfl, ?_⟩
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · exact ⟨1, one_pos, fun _ i _ hij => absurd (funext fun k => (i k).elim0) hij⟩
    · exact Φ.theorem_2_2 (hΦ hN)
  · rintro _ ⟨ε, Φ, rfl, hΦ⟩
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · exact ⟨1, one_pos, fun g ⟨ε', hε', hg⟩ _ => ⟨ε', ⟨g, hε', hg⟩, rfl, (absurd · (lt_irrefl 0))⟩⟩
    obtain ⟨δ, hδ, hΨ⟩ := Φ.lemma_2_7_union hN (hΦ hN)
    exact ⟨δ, hδ, fun g ⟨ε', hε', hg⟩ hfg =>
      ⟨ε', ⟨g, hε', hg⟩, rfl, fun _ => hΨ (⟨g, hε', hg⟩ : IFS N ε') hfg⟩⟩
  · rintro f ⟨ε, hε, hf⟩ r hr
    let Φ : IFS N ε := ⟨f, hε, hf⟩
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · exact ⟨f, ⟨ε, Φ, rfl, (absurd · (lt_irrefl 0))⟩, by simpa [d2Sys] using hr⟩
    obtain ⟨_, -, Φ₁, -, hΦ₁, hI, hnc⟩ := Φ.exists_noCoincidence_near hN (half_pos hr)
    obtain ⟨ε', Ψ, hΨ, hssc⟩ := IFS.exists_dualSSC_near hN Φ₁ hI hnc (half_pos hr)
    refine ⟨Ψ.f, ⟨ε', Ψ, rfl, fun _ => hssc⟩, ?_⟩
    have := OpenDense.d2_le_add Φ Φ₁ Ψ
    change d2 Φ Ψ < r
    linarith

end AnalyticESC
