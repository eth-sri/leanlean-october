module

public import NearlyMinimax.FinePairDensityPacket

@[expose] public section

/-! The actual fine-pair density packet tensored with the original finite
response reset measure, retaining the genuine field and scale marks. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

abbrev FinePairPacketIndex (ι : Type*) (M q : ℕ) := FinePairDensityIndex M × HighResponseMarkIndex ι q

section Packet
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

section
variable {σ : Measure Z} (a b : ℝ) (M q : ℕ) (C : ℝ) {A : Z → ι → ι → ℝ}
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ)
    (h : FinePairPacketIndex ι M q)

abbrev finePairPacketWeight (A : Z → ι → ι → ℝ)
    (e : Z × FinePairPacketIndex ι M q) : ℝ :=
  responseTensorWeight (finePairDensityWeight a b M) q C A e

end

section
variable {σ : Measure Z} (a b : ℝ) (M q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)

def finePairPacketSignedMeasure (σ : Measure Z) (a b : ℝ) (M q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) : SignedMeasure (Z × FinePairPacketIndex ι M q) :=
  (σ.prod Measure.count).withDensityᵥ (finePairPacketWeight a b M q C A)

theorem finePairPacketSignedMeasure_totalVariation [IsFiniteMeasure σ]
    (a b : ℝ) (M q : ℕ) (C : ℝ) {A : Z → ι → ι → ℝ}
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ) :
    ((finePairPacketSignedMeasure σ a b M q C A).variation univ).toReal =
      (∑ h : FinePairDensityIndex M, |finePairDensityWeight a b M h|) *
        responseVariation q * (2 * C ^ 2) *
          (∫ ζ, separatedMatrixCost A ζ ∂σ) :=
  tensorWeight_variation (finePairDensityWeight a b M) q C hA hcost

def finePairPacketObservable {M q : ℕ} (C : ℝ) (c : ι → ℝ)
    (G : Z → ℝ → ℝ → ℝ) (Φ : (ι → ℝ) → ℝ)
    (e : Z × FinePairPacketIndex ι M q) : ℝ :=
  G e.1 (finePairDensityAtom a b e.2.1).1 (finePairDensityAtom a b e.2.1).2 *
    Φ (coefficientReset c (highResponseMarkAtom C e.2.2).2 (highResponseMarkAtom C e.2.2).1)

theorem finePairPacketObservable_finite_action (c : ι → ℝ) (G : Z → ℝ → ℝ → ℝ) (Φ : (ι → ℝ) → ℝ) (ζ : Z) :
    (∑ h : FinePairPacketIndex ι M q, finePairPacketWeight a b M q C A (ζ, h) *
      finePairPacketObservable a b C c G Φ (ζ, h)) =
      (∫ᵛ e, G ζ e.1 e.2 ∂<•finePairDensitySignedRule a b M) * responseMatrixAction q C (A ζ) c Φ := by
  rw [Fintype.sum_prod_type, finePairDensitySignedRule, atomicSignedRule_integral]
  simp [finePairPacketWeight, responseTensorWeight, finePairPacketObservable]
  have he (h : FinePairDensityIndex M) (v : HighResponseMarkIndex ι q) :
      finePairDensityWeight a b M h * highResponseMarkWeight C (A ζ) v *
      (G ζ (finePairDensityAtom a b h).1 (finePairDensityAtom a b h).2 *
        Φ (coefficientReset c (highResponseMarkAtom C v).2 (highResponseMarkAtom C v).1)) =
      (finePairDensityWeight a b M h * G ζ (finePairDensityAtom a b h).1 (finePairDensityAtom a b h).2) *
        (highResponseMarkWeight C (A ζ) v *
          Φ (coefficientReset c (highResponseMarkAtom C v).2 (highResponseMarkAtom C v).1)) := by ring
  simp_rw [he, ← Finset.mul_sum, highResponseMark_action]
  rw [← Finset.sum_mul]

end

variable {U : Type*} {σ : Measure Z} [IsFiniteMeasure σ]

theorem finePairPacketSignedMeasure_factor_integral
    (a b : ℝ) (M q : ℕ) {C : ℝ} {A : Z → ι → ι → ℝ}
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ)
    {c : ι → ℝ} (G : Z → ℝ → ℝ → ℝ) (hG : ∀ z eps, Measurable (fun ζ => G ζ z eps))
    {L : ℝ} (hL : 0 ≤ L) (hGbound : ∀ ζ h,
      |G ζ (finePairDensityAtom a b h).1 (finePairDensityAtom a b (M := M) h).2| ≤ L)
    {Φ : (ι → ℝ) → ℝ} {R : ℝ} (hΦ : ∀ h : HighResponseMarkIndex ι q,
      |Φ (coefficientReset c (highResponseMarkAtom C h).2 (highResponseMarkAtom C h).1)| ≤ R) :
    (∫ᵛ e, finePairPacketObservable a b C c G Φ e ∂<•finePairPacketSignedMeasure σ a b M q C A) =
      ∫ ζ, (∫ᵛ e, G ζ e.1 e.2 ∂<•finePairDensitySignedRule a b M) * responseMatrixAction q C (A ζ) c Φ ∂σ := by
  rw [finePairPacketSignedMeasure, signedDensity_finite_integral (w := finePairPacketWeight a b M q C A)
    (tensorWeight_integrable _ q C hA hcost) (tensorWeight_measurable _ q C hA)
    (fun h => by
      change Measurable (fun ζ => G ζ (finePairDensityAtom a b h.1).1
        (finePairDensityAtom a b h.1).2 *
        Φ (coefficientReset c (highResponseMarkAtom C h.2).2 (highResponseMarkAtom C h.2).1))
      fun_prop) (L * R) (fun ζ h => by
      rw [finePairPacketObservable, Real.norm_eq_abs, abs_mul]
      bound)]
  simp_rw [finePairPacketObservable_finite_action]

theorem finePairPacketSignedMeasure_pair_action
    {a b : ℝ} (ha : 0 < a) (hab : a < b) {M q : ℕ} (hM : 2 ≤ M) {C : ℝ}
    {A : Z → ι → ι → ℝ} (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) {c : ι → ℝ}
    {p : U → ℝ} (hp : ∀ u, p u ∈ Icc a b) (ψ : Z → U → ℝ)
    (hmψ : ∀ u, Measurable (fun ζ => ψ ζ u)) (hψ : ∀ ζ u, |ψ ζ u| ≤ 1)
    (u v : U) {Φ : (ι → ℝ) → ℝ} {R : ℝ} (hΦ : ∀ h : HighResponseMarkIndex ι q,
      |Φ (coefficientReset c (highResponseMarkAtom C h).2 (highResponseMarkAtom C h).1)| ≤ R) :
    (∫ᵛ e, finePairPacketObservable a b C c
      (fun ζ z eps => finePairDensityReset a b z eps p (ψ ζ) u *
        finePairDensityReset a b z eps p (ψ ζ) v) Φ e
      ∂<•finePairPacketSignedMeasure σ a b M q C A) =
      p u * p v * (∫ ζ, ψ ζ u * ψ ζ v * responseMatrixAction q C (A ζ) c Φ ∂σ) := by
  have hm (z eps : ℝ) (u : U) :
      Measurable (fun ζ => finePairDensityReset a b z eps p (ψ ζ) u) := by
    exact measurable_const.add ((hmψ u).const_mul _)
  rw [finePairPacketSignedMeasure_factor_integral a b M q hA hcost
    (fun ζ z eps => finePairDensityReset a b z eps p (ψ ζ) u * finePairDensityReset a b z eps p (ψ ζ) v)
    (fun z eps => (hm z eps u).mul (hm z eps v)) (L := (b ^ 2)) (by positivity) (fun ζ h => by
      rw [abs_mul, pow_two]
      exact mul_le_mul (finePairFieldReset_abs_le ha hab hp hψ (ζ, h) u)
        (finePairFieldReset_abs_le ha hab hp hψ (ζ, h) v) (abs_nonneg _) (ha.trans hab).le) hΦ]
  simp_rw [finePairDensitySignedRule_pair_exact ha hab hM p]
  have he (ζ : Z) : p u * p v * ψ ζ u * ψ ζ v * responseMatrixAction q C (A ζ) c Φ =
      (p u * p v) * (ψ ζ u * ψ ζ v * responseMatrixAction q C (A ζ) c Φ) := by ring
  simp_rw [he]
  exact integral_const_mul _ _

end Packet
end NearlyMinimax
