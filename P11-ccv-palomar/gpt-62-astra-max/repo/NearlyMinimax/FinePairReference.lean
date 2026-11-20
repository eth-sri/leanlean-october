module

public import NearlyMinimax.FinePairResponsePacket
public import NearlyMinimax.HighReferenceBalancing

@[expose] public section

/-! The genuine uncentered absolute fine-pair reference law. Reflection of
the actual three-point modulation atoms centers its affine density slope. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem fineModulationNode_reflection (i : Fin 3) : fineModulationNode i.rev = -fineModulationNode i := by
  fin_cases i <;> norm_num [fineModulationNode, Fin.rev]

theorem fineModulationWeight_abs_reflection (i : Fin 3) :
    |fineModulationWeight i.rev| = |fineModulationWeight i| := by
  fin_cases i <;> norm_num [fineModulationWeight, Fin.rev]

def finePairPacketReflection (ι : Type*) (M q : ℕ) : Equiv.Perm (FinePairPacketIndex ι M q) :=
  Equiv.prodCongr (Equiv.prodCongr (Equiv.refl _) Fin.revPerm) (Equiv.refl _)

section Packet
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

section
variable (σ : Measure Z) (a b : ℝ) (M q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ) (ψ : Z → ℝ)
    (e : Z × FinePairPacketIndex ι M q)

def finePairPacketMarkMass : ℝ :=
  signedMarkMass (σ.prod Measure.count) (finePairPacketWeight a b M q C A)

def finePairPacketAbsoluteLaw : Measure (Z × FinePairPacketIndex ι M q) :=
  absoluteMarkLaw (σ.prod Measure.count) (finePairPacketWeight a b M q C A)

def finePairPacketActivation : Z × FinePairPacketIndex ι M q → ℝ :=
  absoluteActivation (σ.prod Measure.count) (finePairPacketWeight a b M q C A)

def finePairPacketIntercept : ℝ :=
  (finePairDensityAtom a b e.2.1).1

def finePairPacketSlope {M q : ℕ} (ψ : Z → ℝ) (e : Z × FinePairPacketIndex ι M q) : ℝ :=
  densityMargin a b (finePairPacketIntercept a b M q e) / b *
    (finePairDensityAtom a b e.2.1).2 * ψ e.1

def finePairPacketResponseVector : ι → ℝ :=
  (highResponseMarkAtom C e.2.2).2

def finePairPacketResponseTime : ℝ :=
  (highResponseMarkAtom 0 e.2.2).1

theorem finePairPacketIntercept_measurable :
    Measurable (finePairPacketIntercept (Z := Z) (ι := ι) a b M q) := by
  apply measurable_from_prod_countable_left
  intro h
  change Measurable (fun _ : Z => (finePairDensityAtom a b h.1).1)
  exact measurable_const

theorem finePairPacketSlope_measurable {ψ : Z → ℝ} (hψ : Measurable ψ) :
    Measurable (finePairPacketSlope (ι := ι) a b (M := M) (q := q) ψ) := by
  apply measurable_from_prod_countable_left
  intro h
  unfold finePairPacketSlope finePairPacketIntercept
  dsimp
  fun_prop

theorem finePairPacketSlope_joint_measurable {U : Type*} [MeasurableSpace U]
    (a b : ℝ) (M q : ℕ) {ψ : Z → U → ℝ}
    (hψ : Measurable (fun zu : Z × U => ψ zu.1 zu.2)) :
    Measurable (fun eu : (Z × FinePairPacketIndex ι M q) × U =>
      finePairPacketSlope a b (fun ζ => ψ ζ eu.2) eu.1) := by
  have hc : Measurable (fun eu : (Z × FinePairPacketIndex ι M q) × U =>
      densityMargin a b (finePairDensityAtom a b eu.1.2.1).1 / b *
        (finePairDensityAtom a b eu.1.2.1).2) :=
    (measurable_of_countable (fun h : FinePairPacketIndex ι M q =>
      densityMargin a b (finePairDensityAtom a b h.1).1 / b *
        (finePairDensityAtom a b h.1).2)).comp (measurable_snd.comp measurable_fst)
  exact hc.mul (by fun_prop)

theorem finePairPacketSlope_bound {a b : ℝ} (ha : 0 < a) (hab : a < b) {M q : ℕ}
    (ψ : Z → ℝ) (hψ : ∀ ζ, |ψ ζ| ≤ 1) (e : Z × FinePairPacketIndex ι M q) :
    |finePairPacketSlope a b ψ e| ≤ (b - a) / (4 * b) :=
  finePairDensityReset_slope_bound ha hab
    (exteriorNode_mem hab.le e.2.1.1) (fineModulationNode_bound e.2.1.2) (hψ e.1)

theorem finePairPacketSlope_absolute_sum_zero (ζ : Z) :
    (∑ h : FinePairPacketIndex ι M q, |finePairPacketWeight a b M q C A (ζ, h)| *
      finePairPacketSlope a b ψ (ζ, h)) = 0 :=
  finite_even_odd_sum_zero
    (by simp [finePairPacketWeight, finePairDensityWeight, finePairPacketReflection, abs_mul, fineModulationWeight_abs_reflection])
    ((by simp [finePairPacketSlope, finePairPacketIntercept, finePairDensityAtom, finePairPacketReflection, fineModulationNode_reflection] : ∀ (h : FinePairPacketIndex ι M q), finePairPacketSlope a b ψ (ζ, (finePairPacketReflection ι M q) h) = -finePairPacketSlope a b ψ (ζ, h)))

end

variable (σ : Measure Z) [IsFiniteMeasure σ] (a b : ℝ) (M q : ℕ) (C : ℝ)
  (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
  (hcost : Integrable (separatedMatrixCost A) σ)
  (hpos : 0 < finePairPacketMarkMass σ a b M q C A)
include hA hcost hpos

theorem finePairPacketAbsoluteLaw_probability :
    IsProbabilityMeasure (finePairPacketAbsoluteLaw σ a b M q C A) :=
  absoluteMarkLaw_probability (tensorWeight_integrable (finePairDensityWeight a b M) q C hA hcost) hpos

theorem finePairPacketActivation_centered :
    (∫ e, finePairPacketActivation σ a b M q C A e ∂finePairPacketAbsoluteLaw σ a b M q C A) = 0 := by
  have h := tensorActivation_density_zero (finePairDensityWeight a b M) q C hA hcost hpos
    (F := fun _ => 1) measurable_const (fun _ => le_rfl)
  simp at h
  exact h

theorem finePairPacketAbsoluteLaw_slope_integral_zero (ha : 0 < a) (hab : a < b)
    {ψ : Z → ℝ} (hmψ : Measurable ψ) (hψ : ∀ ζ, |ψ ζ| ≤ 1) :
    (∫ e, finePairPacketSlope a b ψ e ∂finePairPacketAbsoluteLaw σ a b M q C A) = 0 :=
  absoluteMarkLaw_fiber_zero (w := finePairPacketWeight a b M q C A)
    (tensorWeight_measurable _ q C hA) (tensorWeight_integrable _ q C hA hcost) hpos
    (finePairPacketSlope_measurable a b M q hmψ) (finePairPacketSlope_bound ha hab ψ hψ)
    (finePairPacketSlope_absolute_sum_zero a b M q C A ψ)

end Packet
end NearlyMinimax
