module

public import AnalyticESC.Generic.Density
public import AnalyticESC.Generic.Coincidences
public import AnalyticESC.Generic.Continuity
public import AnalyticESC.Main.Dichotomy

public section

/-!
# Theorem 1.4

The IFSs of `𝔖_N` that satisfy the SESC contain a `d₂`-open and `d₂`-dense subset of `𝔖_N`, the
union class of decision D1. The open set consists of the systems whose dual IFS satisfies the SSC:
it is open by Lemma 2.7, its systems satisfy the SESC by Theorem 2.2, and it is dense by the
interpolation `IFS.exists_noCoincidence_near` and the density step. The density step combines two perturbations, so
it uses the triangle inequality for `d₂` between systems of `𝔖_N(ε)` for different `ε`.
-/

namespace AnalyticESC

variable {U : Set ℂ}

open Set

namespace OpenDense

/-- The triangle inequality for `sup_{x ∈ I} |F(x) - H(x)|`, for maps continuous on a set
containing `I`. -/
theorem iSup_norm_sub_le_add {F G H : ℂ → ℂ} (hIU : Iℂ ⊆ U)
    (hF : ContinuousOn F U) (hG : ContinuousOn G U) (hH : ContinuousOn H U) :
    (⨆ x : I, ‖F x - H x‖) ≤
      (⨆ x : I, ‖F x - G x‖) +
        ⨆ x : I, ‖G x - H x‖ := by
  refine Real.iSup_le (fun x => ?_) (add_nonneg (Real.iSup_nonneg fun _ => norm_nonneg _)
    (Real.iSup_nonneg fun _ => norm_nonneg _))
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (add_le_add (le_ciSup (IFS.Continuity.bddAbove_range_norm_sub hIU hF hG) x) (le_ciSup (IFS.Continuity.bddAbove_range_norm_sub hIU hG hH) x))

/-- The triangle inequality for the `𝒞²` distance on `I` between maps holomorphic on an open set
containing `I`. -/
theorem d2Map_le_add {f g h : ℂ → ℂ} (hU : IsOpen U)
    (hIU : Iℂ ⊆ U) (hf : DifferentiableOn ℂ f U)
    (hg : DifferentiableOn ℂ g U) (hh : DifferentiableOn ℂ h U) :
    d2Map f h ≤ d2Map f g + d2Map g h := by
  have e0 := iSup_norm_sub_le_add hIU hf.continuousOn hg.continuousOn hh.continuousOn
  have e1 := iSup_norm_sub_le_add hIU (hf.deriv hU).continuousOn (hg.deriv hU).continuousOn
    (hh.deriv hU).continuousOn
  have e2 := iSup_norm_sub_le_add hIU ((hf.deriv hU).deriv hU).continuousOn
    ((hg.deriv hU).deriv hU).continuousOn ((hh.deriv hU).deriv hU).continuousOn
  unfold d2Map
  linarith

/-- The triangle inequality for `d₂` on `𝔖_N`, for systems in `𝔖_N(ε)` for different `ε`. -/
theorem d2_le_add (Φ : IFS N ε) (Φ' : IFS N ε') (Ψ : IFS N ε'') :
    d2 Φ Ψ ≤ d2 Φ Φ' + d2 Φ' Ψ := by
  set U := 𝔑 ε ∩ 𝔑 ε' ∩ 𝔑 ε''
  have hIU : Iℂ ⊆ U :=
    subset_inter (subset_inter Φ.image_I_subset_nbhd2
      Φ'.image_I_subset_nbhd2)
      Ψ.image_I_subset_nbhd2
  refine Real.iSup_le (fun i => ?_) (add_nonneg (IFS.Continuity.d2_nonneg _ _)
    (IFS.Continuity.d2_nonneg _ _))
  refine (d2Map_le_add ((isOpen_nbhd.inter isOpen_nbhd).inter isOpen_nbhd) hIU ((Φ.inClass i).differentiableOn.mono (inter_subset_left.trans inter_subset_left))
    ((Φ'.inClass i).differentiableOn.mono (inter_subset_left.trans inter_subset_right)) ((Ψ.inClass i).differentiableOn.mono inter_subset_right)).trans
    (add_le_add ?_ ?_)
  · exact le_ciSup (f := fun i => d2Map (Φ.f i) (Φ'.f i)) (Set.finite_range _).bddAbove i
  · exact le_ciSup (f := fun i => d2Map (Φ'.f i) (Ψ.f i)) (Set.finite_range _).bddAbove i

end OpenDense

/-- Theorem 1.4. The systems of `𝔖_N` satisfying the SESC contain a subset `U` of `𝔖_N` that is
open and dense in the `𝒞²` metric. -/
theorem theorem_1_4 N :
    ∃ U : Set (Fin N → ℂ → ℂ),
      (∀ f ∈ U, ∃ ε, ∃ Φ : IFS N ε, Φ.f = f ∧ Φ.SESC) ∧
      (∀ f ∈ U, ∃ r > 0, ∀ g, InUnionClass g → d2Sys f g < r → g ∈ U) ∧
      (∀ f, InUnionClass f → ∀ r > 0, ∃ g ∈ U, d2Sys f g < r) := by
  refine ⟨{f | ∃ ε, ∃ Φ : IFS N ε, Φ.f = f ∧ Φ.DualSSC}, ?_, ?_, ?_⟩
  · rintro _ ⟨ε, Φ, rfl, hΦ⟩
    exact ⟨ε, Φ, rfl, Φ.theorem_2_2 hΦ⟩
  · rintro _ ⟨ε, Φ, rfl, hΦ⟩
    obtain ⟨δ, hδ, hΨ⟩ := Φ.lemma_2_7_union hΦ
    exact ⟨δ, hδ, fun g ⟨ε', hε', hg⟩ hfg =>
      ⟨ε', ⟨g, hε', hg⟩, rfl, hΨ (⟨g, hε', hg⟩ : IFS N ε') hfg⟩⟩
  · -- Density, by the interpolation and the density step.
    rintro f ⟨ε, hε, hf⟩ r hr
    let Φ : IFS N ε := by tauto
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · refine ⟨f, ⟨ε, Φ, rfl, fun i => (i 0).elim0⟩, ?_⟩
      rw [d2Sys, Real.iSup_of_isEmpty]
      exact hr
    obtain ⟨Φ₁, hΦ₁, hI, hnc⟩ := Φ.exists_noCoincidence_near (half_pos hr)
    obtain ⟨ε', Ψ, hΨ, hssc⟩ := IFS.exists_dualSSC_near hN Φ₁ hI hnc (half_pos hr)
    refine ⟨Ψ.f, ⟨ε', Ψ, rfl, hssc⟩, ?_⟩
    have h := OpenDense.d2_le_add Φ Φ₁ Ψ
    change d2 Φ Ψ < r
    linarith

end AnalyticESC
