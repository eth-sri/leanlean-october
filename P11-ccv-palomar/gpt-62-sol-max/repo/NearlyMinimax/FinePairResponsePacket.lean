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

def finePairPacketWeight (a b : ℝ) (M q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (e : Z × FinePairPacketIndex ι M q) : ℝ :=
  responsePacketWeight (finePairDensityWeight a b M) q C A e

theorem finePairPacketWeight_measurable (a b : ℝ) (M q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) :
    Measurable (finePairPacketWeight a b M q C A) :=
  responsePacketWeight_measurable _ q C A hA

theorem finePairPacketWeight_integrable (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (M q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : SeparatedMatrixIntegrable σ A) :
    Integrable (finePairPacketWeight a b M q C A) (σ.prod Measure.count) :=
  responsePacketWeight_integrable _ q C A σ hA

def finePairPacketSignedMeasure (σ : Measure Z) (a b : ℝ) (M q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) : SignedMeasure (Z × FinePairPacketIndex ι M q) :=
  (σ.prod Measure.count).withDensityᵥ (finePairPacketWeight a b M q C A)

def finePairPacketObservable (a b : ℝ) (M q : ℕ) (C : ℝ) (c : ι → ℝ)
    (G : Z → ℝ → ℝ → ℝ) (Φ : (ι → ℝ) → ℝ)
    (e : Z × FinePairPacketIndex ι M q) : ℝ :=
  responsePacketObservable q C (finePairDensityAtom a b M) c (fun ζ x => G ζ x.1 x.2) Φ e

theorem finePairPacketSignedMeasure_product_integral {n : ℕ} (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (M q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (hA : SeparatedMatrixIntegrable σ A) (c : ι → ℝ)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc a b) (ψ : Z → Fin n → ℝ)
    (hmψ : ∀ i, Measurable (fun ζ => ψ ζ i)) (hbψ : ∀ ζ i, |ψ ζ i| ≤ 1)
    (Φ : (ι → ℝ) → ℝ) :
    (∫ᵛ e, finePairPacketObservable a b M q C c
      (fun ζ z eps => ∏ i, finePairDensityReset a b z eps p (ψ ζ) i) Φ e
      ∂<•finePairPacketSignedMeasure σ a b M q C A) =
      ∫ ζ, (∫ᵛ e, ∏ i, finePairDensityReset a b e.1 e.2 p (ψ ζ) i ∂<•finePairDensitySignedRule a b M) *
        responseMatrixAction q C (A ζ) c Φ ∂σ :=
  responsePacket_signed_integral_product (finePairDensityWeight a b M) q C A σ hA
    (finePairDensityAtom a b M) c (fun ζ x i => finePairDensityReset a b x.1 x.2 p (ψ ζ) i)
    (fun _ i => measurable_const.add ((hmψ i).const_mul _)) (ha.trans hab).le
    (fun ζ h i => finePairFieldReset_abs_le a b ha hab M p hp ψ hbψ (ζ,h) i) Φ

end Packet
end NearlyMinimax
