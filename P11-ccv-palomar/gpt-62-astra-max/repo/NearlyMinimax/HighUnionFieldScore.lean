module

public import NearlyMinimax.HighUnionScore
public import NearlyMinimax.HighLocalFrame


@[expose] public section

/-! Disjoint-patch orthogonality and the exact torus overlap bound for the
complete marked local generator, with its variance correction counted once.
The final endpoint uses the actual polynomial field decomposition. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
attribute [local instance] Classical.propDecidable

section GenericFamily
variable {J ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]

theorem highMarkedLocalScores_orthogonal {n : ℕ}
    {π : J → Measure E} {activation : J → E → ℝ} (a V η : ℝ) (ha : a ≠ 0)
    {p : Fin n → ℝ} {pReset : J → E → Fin n → ℝ}
    (cReset : J → E → ι → ℝ) (g w : J → Fin n → ℝ)
    (φ : J → Fin n → ι → ℝ) (c : J → ι → ℝ) {f : Fin n → ℝ}
    (hreg : ∀ j, coefficientRegression η (g j) (w j) (φ j) (c j) = f)
    {S : J → Finset (Fin n)} (hw : ∀ j i, i ∉ S j → w j i = 0)
    (hpd : ∀ i, p i ≠ 0) (hp : ∀ i b, 0 < ternaryMass a (f i) V b)
    (hInt : ∀ j y, Integrable (fun e => activation j e * (∏ i, pReset j e i) *
      highResponseProduct a V η (g j) (w j) (φ j) (cReset j e) y) (π j))
    (hDensity : ∀ j, (∫ e, activation j e * ∏ i, pReset j e i ∂π j) = 0)
    {j l : J} (hST : Disjoint (S j) (S l)) :
    (∫ y, highMarkedLocalScore (π j) (activation j) a V η p (pReset j) (cReset j)
      (g j) (w j) (φ j) (c j) y *
      highMarkedLocalScore (π l) (activation l) a V η p (pReset l) (cReset l)
        (g l) (w l) (φ l) (c l) y
      ∂Measure.pi (fun i => ternaryIndexMeasure (f i) V ha (fun b => (hp i b).le))) = 0 := by
  let μ  := fun i =>
    ternaryIndexMeasure (f i) V ha (fun b => (hp i b).le)
  have hp' j i b :
      0 < ternaryMass a (coefficientRegression η (g j) (w j) (φ j) (c j) i) V b := by
    rw [hreg j]
    exact hp i b
  apply local_response_scores_orthogonal μ _ _ hST
  · intro y y' hyy
    solve_by_elim [highMarkedLocalScore_depends_on_support]
  · intro y y' hyy
    solve_by_elim [highMarkedLocalScore_depends_on_support]
  · simpa only [hreg j] using highMarkedLocalScore_centered ha hpd (hp' j) (hInt j) (hDensity j)

end GenericFamily

section ActualField
variable {E : Type*} [MeasurableSpace E]

variable {d k D n : ℕ} [NeZero k] (hk : 4 ≤ k) {π : HighWindowLabels d k → Measure E}
    {activation : HighWindowLabels d k → E → ℝ} (hAct : ∀ j, Integrable (activation j) (π j))

def highFrameMarkedScore
    (π : HighWindowLabels d k → Measure E)
    (activation : HighWindowLabels d k → E → ℝ) (a V η : ℝ) (p : Fin n → ℝ)
    (pReset : HighWindowLabels d k → E → Fin n → ℝ)
    (cReset : HighWindowLabels d k → E → HighFrameVector d D)
    (c : HighWindowLabels d k → HighFrameVector d D) (x : DesignSample d n)
    (j : HighWindowLabels d k) (y : TernaryVector n) : ℝ :=
  highMarkedLocalScore (π j) (activation j) a V η p (pReset j) (cReset j)
    (fun i => highLocalFieldWithout η c j (x i))
    (fun i => highPeriodicTensor j (x i))
    (fun i => highLocalFrameFeature j (x i)) (c j) y

include hk hAct in
/-- Conditional orthogonality of the true complete signed-generator scores
is proved from actual response normalization, conditional density zero mass,
and the original window supports. -/
theorem highFrameMarkedScore_orthogonal
    {a V η pPlus : ℝ} (ha : a ≠ 0) (hpPlus : 0 ≤ pPlus) {p : Fin n → ℝ}
    {pReset : HighWindowLabels d k → E → Fin n → ℝ}
    (hReset : ∀ j i, Measurable (fun e => pReset j e i))
    (hBound : ∀ j e i, |pReset j e i| ≤ pPlus)
    {cReset : HighWindowLabels d k → E → HighFrameVector d D}
    (hcReset : ∀ j γ, Measurable (fun e => cReset j e γ))
    {c : HighWindowLabels d k → HighFrameVector d D} {x : DesignSample d n}
    (hpd : ∀ i, p i ≠ 0)
    (hp : ∀ i b, 0 < ternaryMass a
      (highFrameField k η (fun l => highFramePolynomial (c l)) (x i)) V b)
    (hpReset : ∀ j e i b, 0 ≤ ternaryMass a
      (coefficientRegression η (fun i => highLocalFieldWithout η c j (x i))
        (fun i => highPeriodicTensor j (x i))
        (fun i => highLocalFrameFeature j (x i)) (cReset j e) i) V b)
    (hDensity : ∀ j, (∫ e, activation j e * ∏ i, pReset j e i ∂π j) = 0)
    {j l : HighWindowLabels d k} (hjl : l ∉ highNeighborLabels j) :
    (∫ y, highFrameMarkedScore π activation a V η p pReset cReset c x j y *
      highFrameMarkedScore π activation a V η p pReset cReset c x l y
      ∂Measure.pi (fun i => ternaryIndexMeasure
        (highFrameField k η (fun l => highFramePolynomial (c l)) (x i)) V
        ha (fun b => (hp i b).le))) = 0 := highMarkedLocalScores_orthogonal a V η ha cReset
    (fun j i => highLocalFieldWithout η c j (x i))
    (fun j i => highPeriodicTensor j (x i))
    (fun j i => highLocalFrameFeature j (x i)) c
    (fun j => highFrameField_coefficientRegression hk η c j x)
    (fun j i hi => by by_contra h; have hx := highPeriodicTensor_supported_patch j h; exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hx⟩))
    hpd hp (fun j y => highMarkedResponseAction_integrable (hAct j) ha hpPlus (hReset j) (hBound j) (hcReset j) (hpReset j) y) hDensity
    (by apply Finset.disjoint_left.mpr; intro i hi hj; exact Set.disjoint_left.mp (highTorusPatch_disjoint_of_not_neighbor hjl) (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2)

include hk hAct in
/-- The exact source overlap factor is established for the complete union
score, after the single variance correction and the genuine local field
decomposition. No covariance or score-energy bound is a premise. -/
theorem highFrameMarkedScore_energy_bound
    (a V η pPlus : ℝ) (ha : a ≠ 0) (hpPlus : 0 ≤ pPlus) (p : Fin n → ℝ)
    (pReset : HighWindowLabels d k → E → Fin n → ℝ)
    (hReset : ∀ j i, Measurable (fun e => pReset j e i))
    (hBound : ∀ j e i, |pReset j e i| ≤ pPlus)
    {cReset : HighWindowLabels d k → E → HighFrameVector d D}
    (hcReset : ∀ j γ, Measurable (fun e => cReset j e γ))
    (c : HighWindowLabels d k → HighFrameVector d D) (x : DesignSample d n)
    (hpd : ∀ i, p i ≠ 0)
    (hp : ∀ i b, 0 < ternaryMass a
      (highFrameField k η (fun l => highFramePolynomial (c l)) (x i)) V b)
    (hpReset : ∀ j e i b, 0 ≤ ternaryMass a
      (coefficientRegression η (fun i => highLocalFieldWithout η c j (x i))
        (fun i => highPeriodicTensor j (x i))
        (fun i => highLocalFrameFeature j (x i)) (cReset j e) i) V b)
    (hDensity : ∀ j, (∫ e, activation j e * ∏ i, pReset j e i ∂π j) = 0) :
    let productLaw := Measure.pi (fun i => ternaryIndexMeasure (highFrameField k η (fun l => highFramePolynomial (c l)) (x i)) V ha (fun b => (hp i b).le))
    (∫ y, (∑ j, highFrameMarkedScore π activation a V η p pReset cReset c x j y)^2
      ∂productLaw) ≤
      (3^d : ℕ) * ∑ j, ∫ y,
        (highFrameMarkedScore π activation a V η p pReset cReset c x j y)^2
        ∂productLaw := by
  apply finite_overlap_variance_bound _
    (highFrameMarkedScore π activation a V η p pReset cReset c x)
    (windowDepends d k) (3^d)
  · solve_by_elim [highNeighborLabels_symmetric]
  · intro j
    convert highNeighborLabels_card_le j using 1
    simp
  · apply highFrameMarkedScore_orthogonal <;> assumption

end ActualField
end NearlyMinimax
