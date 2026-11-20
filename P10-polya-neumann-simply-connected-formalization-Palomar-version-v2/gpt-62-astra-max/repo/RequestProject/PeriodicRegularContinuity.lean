module

public import RequestProject.NormalizedPeriodicRegular
public import RequestProject.CorrectedKernelEnergy
public import RequestProject.PlanarNotation

/-! Operator norm continuity of the genuine regular periodic family near a nonzero cut. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PolyaNeumann
open Filter Topology Real Set

private theorem periodic_inverse_continuousAt_unit
    {A : Type*} [NormedRing A] [CompleteSpace A] {a : A} (ha : IsUnit a) :
    ContinuousAt (Ring.inverse : A → A) a := by
  obtain ⟨u, rfl⟩ := ha
  exact NormedRing.inverse_continuousAt u

theorem continuousAt_h1RegularResolvent {Ω : Set ℂ} {E₀ E : ℝ}
    (hu : IsUnit (h1ComplementForm Ω E₀ E)) :
    ContinuousAt (h1RegularResolvent Ω E₀) E := @ContinuousAt.clm_comp ℂ _ (NeumannH1 Ω) _ _ (h1ResonantSpace Ω E₀)ᗮ _
    (h1ComplementNormedSpace Ω E₀) (NeumannH1 Ω) _ _ ℝ _ _ _ E continuousAt_const
    (@ContinuousAt.clm_comp ℂ _ (NeumannH1 Ω) _ _ (h1ResonantSpace Ω E₀)ᗮ _
      (h1ComplementNormedSpace Ω E₀) (h1ResonantSpace Ω E₀)ᗮ _ (h1ComplementNormedSpace Ω E₀)
      ℝ _ _ _ E ((periodic_inverse_continuousAt_unit hu).comp
        (continuous_h1ComplementForm Ω E₀).continuousAt) continuousAt_const)

theorem continuousAt_normalizedNeumannRegular {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) {E₀ E : ℝ}
    (hu : IsUnit (h1ComplementForm Ω E₀ E)) :
    ContinuousAt (normalizedNeumannRegular Q E₀) E := continuousAt_const.clm_comp
    ((continuousAt_h1RegularResolvent hu).clm_comp continuousAt_const)

section

variable (W : TransportPath) (δ s : ℝ)
include W s δ

/-- A total operator used to express a limit. Near a nonzero cut its
matrix is genuinely square summable, and it is exactly the actual matrix operator. -/
def correctedRemainderOperator : FourierOp := by
  classical
  exact if h : Summable (fun p => ‖correctedRemainderMatrix W δ s p‖ ^ 2) then
    hsMatrixOp (correctedRemainderMatrix W δ s) h else 0

theorem correctedRemainderOperator_eq
    (h : Summable fun p => ‖correctedRemainderMatrix W δ s p‖ ^ 2) :
    correctedRemainderOperator W δ s = hsMatrixOp (correctedRemainderMatrix W δ s) h := by
  simp [correctedRemainderOperator, dif_pos h]

end

theorem continuousAt_correctedRemainderOperator
    {γ : ℝ → ℂ} {K K' : NNReal} {Ws : ℝ → TransportPath}
    (hK : LipschitzWith K γ)
    (hγ' : ∀ x ∈ angleInterval, ∀ y ∈ angleInterval,
      ‖deriv γ x - deriv γ y‖ ≤ K' * |x - y|)
    (hWs : ∀ E, IsTransport γ E (Ws E)) (E₀ : ℝ)
    (hc : cutVector (Ws E₀) ≠ 0)
    {δ s : ℝ} (hδ : 0 ≤ δ) (hδ' : δ < 1 / 2) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    ContinuousAt (fun E => correctedRemainderOperator (Ws E) δ s) E₀ := by
  
  obtain ⟨hsum, hlim⟩ := tendsto_correctedRemainder_energy hK hγ' hWs E₀ hc hδ hδ' hs0 hs1
  rw [ContinuousAt, correctedRemainderOperator_eq _ _ _ (summable_correctedRemainderMatrix hK hγ' (hWs E₀) hc hδ hδ' hs0 hs1)]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hsum, hlim ε hε] with E hE hnorm
  rw [correctedRemainderOperator_eq _ _ _ hE, dist_eq_norm]
  exact hnorm hE

def normalizedPeriodicRegularFamily {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) (E₀ : ℝ) (Ws : ℝ → TransportPath)
    (E : ℝ) : FourierOp :=
  (2 : ℂ) • (normalizedNeumannRegular Q E₀ E - normalizedInverseAbsOperator) +
    principalNormalized + correctedRemainderOperator (Ws E) 0 0

theorem normalizedPeriodicRegularFamily_eq {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) (E₀ E : ℝ) (Ws : ℝ → TransportPath)
    (h : Summable fun p => ‖correctedRemainderMatrix (Ws E) 0 0 p‖ ^ 2) :
    normalizedPeriodicRegularFamily Q E₀ Ws E =
      normalizedPeriodicRegularOperator Q E₀ E (Ws E) h := by
  simp [normalizedPeriodicRegularFamily, normalizedPeriodicRegularOperator, correctedRemainderOperator_eq _ _ _ h]

theorem continuousAt_normalizedPeriodicRegularFamily {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) {E₀ : ℝ}
    (hu : IsUnit (h1ComplementForm Ω E₀ E₀))
    {γ : ℝ → ℂ} {K K' : NNReal} {Ws : ℝ → TransportPath}
    (hK : LipschitzWith K γ)
    (hγ' : ∀ x ∈ angleInterval, ∀ y ∈ angleInterval,
      ‖deriv γ x - deriv γ y‖ ≤ K' * |x - y|)
    (hWs : ∀ E, IsTransport γ E (Ws E))
    (hc : cutVector (Ws E₀) ≠ 0) :
    ContinuousAt (normalizedPeriodicRegularFamily Q E₀ Ws) E₀ := ((((continuousAt_normalizedNeumannRegular Q hu).sub continuousAt_const).const_smul
    (2 : ℂ)).add continuousAt_const).add
    (continuousAt_correctedRemainderOperator hK hγ' hWs E₀ hc
      (le_refl 0) (by norm_num) (le_refl 0) (by norm_num))

end PolyaNeumann
end
