module

public import NearlyMinimax.HighMarkedResponseEnergy
public import NearlyMinimax.SpatialSubsetEnergy


@[expose] public section

/-! The complete marked generator under its actual iid normalized design.
The factorial series contains genuine raw numerator integrals over the
selected patch observations; no local or global target budget is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

section
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ] {n : ℕ} {A : Set α}

theorem iid_energy_integrable_of_selected (hA : MeasurableSet A)
    {E : (Fin n → α) → ℝ} {H : (S : Finset (Fin n)) → (S → α) → ℝ}
    (hH : ∀ S, Integrable (H S) (Measure.pi (fun _ : S => μ.restrict A)))
    (he : ∀ S x, x ∈ designMembershipCell A S → E x = H S (fun i : S => x i.val)) :
    Integrable E (Measure.pi (fun _ : Fin n => μ)) := by
  have hi : IntegrableOn E (⋃ S : Finset (Fin n), designMembershipCell A S)
      (Measure.pi (fun _ : Fin n => μ)) := by
    apply integrableOn_finite_iUnion.mpr
    intro S
    have hsel := iid_cell_selected_integrable (hH S)
    apply hsel.congr
    filter_upwards [ae_restrict_mem (design_membership_cell_measurable hA S)] with x hx
    exact (he S x hx).symm
  simpa only [membershipCells_cover, integrableOn_univ] using hi

end

section
variable {α ι E : Type*} [MeasurableSpace α] [Fintype ι] [DecidableEq ι] [MeasurableSpace E]

section
variable (r : ℕ) (π : Measure E) (activation : E → ℝ) (a V η : ℝ) (p : α → ℝ) (pReset : E → α → ℝ)
    (cReset : E → ι → ℝ) (g w : α → ℝ) (φ : α → ι → ℝ) (c : ι → ℝ) (x : Fin r → α)

def highMarkedResponseMass (x : α) (y : Fin 3) : ℝ :=
  ternaryMass a (g x + η * w x * ∑ γ, φ x γ * c γ) V y

def highMarkedSampleNumerator (y : TernaryVector r) : ℝ :=
  highMarkedResponseAction π activation a V η (fun z => pReset z ∘ x) cReset
    (g ∘ x) (w ∘ x) (φ ∘ x) y - η ^ 2 * (∏ i, p (x i)) *
      ∑ i, (w (x i)) ^ 2 * highResponseVarianceTerm a V η (g ∘ x) (w ∘ x) (φ ∘ x) c y i

def highMarkedSampleConditionalEnergy : ℝ :=
  selectedConditionalScoreEnergy p (highMarkedResponseMass a V η g w φ c)
    (highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c) x

end

section
variable {n : ℕ} (S : Finset (Fin n)) {r : ℕ} {A : Set α} (π : Measure E) (activation : E → ℝ)
    (a V η : ℝ) (ha : a ≠ 0) (p : α → ℝ) (pReset : E → α → ℝ) (cReset : E → ι → ℝ) (g w : α → ℝ)
    (φ : α → ι → ℝ) (c : ι → ℝ) (x : Fin r → α)

theorem high_marked_sample_score_eq_ratio (y : TernaryVector r) :
    highMarkedLocalScore π activation a V η (p ∘ x) (fun z => pReset z ∘ x) cReset
      (g ∘ x) (w ∘ x) (φ ∘ x) c y =
    highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c x y /
      selectedRawLikelihood p (highMarkedResponseMass a V η g w φ c) x y := rfl

theorem high_marked_sample_energy_integral
    (hp : ∀ z y, 0 < highMarkedResponseMass a V η g w φ c z y) :
    (∫ y, highMarkedLocalScore π activation a V η (p ∘ x) (fun z => pReset z ∘ x) cReset
      (g ∘ x) (w ∘ x) (φ ∘ x) c y ^ 2
      ∂Measure.pi (fun i => ternaryIndexMeasure
        (coefficientRegression η (g ∘ x) (w ∘ x) (φ ∘ x) c i) V ha (fun y => (hp (x i) y).le))) =
    highMarkedSampleConditionalEnergy r π activation a V η p pReset cReset g w φ c x := by
  rw [ternary_index_product_integral]
  unfold highMarkedSampleConditionalEnergy selectedConditionalScoreEnergy
  simp_rw [← high_marked_sample_score_eq_ratio π activation a V η p pReset cReset g w φ c x]
  apply Finset.sum_congr (by ext y; simp)
  intro y hy
  rfl

def selectedDesignEnumeration : Fin S.card ≃ S :=
  (S.orderIsoOfFin rfl).toEquiv

def selectedDesignEmbedding : Fin S.card ↪ Fin n :=
  (S.orderEmbOfFin rfl).toEmbedding

theorem selected_design_embedding_map :
    Finset.univ.map (selectedDesignEmbedding S) = S := Finset.map_orderEmbOfFin_univ S rfl

theorem high_marked_sample_energy_cell_selected
    {S : Finset (Fin n)} {x : Fin n → α} (hx : x ∈ designMembershipCell A S)
    (π : Measure E) (activation : E → ℝ) {a V η : ℝ} (ha : a ≠ 0)
    {p : α → ℝ} {pReset : E → α → ℝ} (cReset : E → ι → ℝ)
    {g w : α → ℝ} {φ : α → ι → ℝ} {c : ι → ℝ}
    (hpd : ∀ z, p z ≠ 0) (hp : ∀ z y, 0 < highMarkedResponseMass a V η g w φ c z y)
    (hw : ∀ z, z ∉ A → w z = 0) (hReset : ∀ e z, z ∉ A → pReset e z = p z) :
    highMarkedSampleConditionalEnergy n π activation a V η p pReset cReset g w φ c x =
      highMarkedSampleConditionalEnergy S.card π activation a V η p pReset cReset g w φ c
        (x ∘ selectedDesignEmbedding S) := by
  have hmem := design_membership_cell_iff A S x |>.mp hx
  have hwo (i : Fin n) (hi : i ∉ Finset.univ.map (selectedDesignEmbedding S)) : w (x i) = 0 := by
    rw [selected_design_embedding_map] at hi
    grind
  have hro (e : E) (i : Fin n) (hi : i ∉ Finset.univ.map (selectedDesignEmbedding S)) :
      pReset e (x i) = p (x i) := by
    rw [selected_design_embedding_map] at hi
    grind
  have he := high_marked_selected_response_energy π activation a V η ha
    (p := (p ∘ x)) (pReset := (fun z => pReset z ∘ x)) cReset (g ∘ x) (w ∘ x) (φ ∘ x) c
    (fun i => hpd (x i)) (fun i y => hp (x i) y) hwo hro
  rw [high_marked_sample_energy_integral π activation a V η ha p pReset cReset g w φ c x hp] at he
  have hs := high_marked_sample_energy_integral π activation a V η ha p pReset cReset
    g w φ c (x ∘ selectedDesignEmbedding S) hp
  exact he.trans hs

end

theorem high_marked_design_raw_factorial_series {ν : Measure α} [IsProbabilityMeasure ν]
    (n : ℕ) {A : Set α} (hA : MeasurableSet A) {m pMinus cMass : ℝ}
    (hpMinus : 0 < pMinus) (hcMass : 0 < cMass) (hm : pMinus ≤ m)
    {π : Measure E} {activation : E → ℝ} {a V η : ℝ} (ha : a ≠ 0)
    {p : α → ℝ} (hpMeas : Measurable p) {pReset : E → α → ℝ} {cReset : E → ι → ℝ}
    {g w : α → ℝ} {φ : α → ι → ℝ} {c : ι → ℝ}
    (hqMeas : ∀ y, Measurable (fun x => highMarkedResponseMass a V η g w φ c x y))
    (hprob : IsProbabilityMeasure (ν.withDensity (fun x => ENNReal.ofReal (p x / m))))
    (hpd : ∀ x, pMinus ≤ p x)
    (hp : ∀ x y, cMass ≤ highMarkedResponseMass a V η g w φ c x y)
    (hw : ∀ x, x ∉ A → w x = 0) (hReset : ∀ e x, x ∉ A → pReset e x = p x)
    (hRMeas : ∀ r y, Measurable (fun x => highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c x y))
    (hRaw : ∀ r, Integrable (selectedRawSquareEnergy
      (highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c))
        (Measure.pi (fun _ : Fin r => ν.restrict A))) :
    let density := ν.withDensity (fun x => ENNReal.ofReal (p x / m))
    let energy := highMarkedSampleConditionalEnergy n π activation a V η p pReset cReset g w φ c
    Integrable (energy)
      (Measure.pi (fun _ : Fin n => density)) ∧
    (∫ x, energy x
      ∂Measure.pi (fun _ : Fin n => density)) ≤
      ∑ r ∈ Finset.range (n + 1),
        ((n : ℝ) * highFixedScoreDenominator pMinus cMass) ^ r / (r.factorial : ℝ) *
          ∫ x, selectedRawSquareEnergy
            (highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c) x
              ∂Measure.pi (fun _ : Fin r => ν.restrict A) := by
  intro density
  let μ := density
  let _  := hprob
  let F (r : ℕ) := highMarkedSampleConditionalEnergy r π activation a V η p pReset cReset g w φ c
  let H (S : Finset (Fin n)) (z : S → α)  := F S.card (z ∘ selectedDesignEnumeration S)
  let J (r : ℕ) := ∫ x, selectedRawSquareEnergy
    (highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c) x
      ∂Measure.pi (fun _ : Fin r => ν.restrict A)
  have hp0 (x : α)  := (hpMinus.trans_le (hpd x)).ne'
  have hq0 (x : α) (y : Fin 3)  := hcMass.trans_le (hp x y)
  have hFI (r : ℕ) := normalized_selected_score_energy_integrable_bound hA
    hpMinus hcMass hm hpMeas hqMeas (hRMeas r) hprob
    (fun x _ => hpd x) (fun x _ y => hp x y) (hRaw r)
  have hHI (S : Finset (Fin n))  :=
    finite_pi_reindex_integrable (selectedDesignEnumeration S).symm (hFI S.card).1
  have hEq (S : Finset (Fin n)) (x : Fin n → α) (hx : x ∈ designMembershipCell A S)  :=
    high_marked_sample_energy_cell_selected hx π activation ha cReset hp0 hq0 hw hReset
  have hFn  :=
    iid_energy_integrable_of_selected hA hHI hEq
  refine ⟨hFn, ?_⟩
  apply iid_local_energy_le_factorial_spatial_series hA hFn (H := H) hHI
    (fun S z => Finset.sum_nonneg (fun y _ => mul_nonneg (Finset.prod_nonneg (fun i _ => (fun x y => (hq0 x y).le) _ _)) (sq_nonneg _))) (fun S x hx => (hEq S x hx).le) ((by unfold highFixedScoreDenominator; positivity : 0 < highFixedScoreDenominator pMinus cMass)).le J
    (fun r => integral_nonneg (fun x => Finset.sum_nonneg (fun y _ => sq_nonneg _)))
  intro S
  have he : (∫ z, F S.card (z ∘ selectedDesignEnumeration S) ∂Measure.pi (fun _ : S => μ.restrict A)) =
      ∫ z, F S.card z ∂Measure.pi (fun _ : Fin S.card => μ.restrict A) :=
    finite_pi_reindex_integral (μ.restrict A) (selectedDesignEnumeration S).symm (F S.card)
  rw [he]
  have hs := (hFI S.card).2
  simp at hs
  assumption

end
end NearlyMinimax
