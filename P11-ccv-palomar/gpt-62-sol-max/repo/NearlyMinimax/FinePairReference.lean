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

section
variable (i : Fin 3)

theorem fineModulationNode_reflection : fineModulationNode i.rev = -fineModulationNode i := by
  fin_cases i <;> norm_num [fineModulationNode, Fin.rev]

theorem fineModulationWeight_abs_reflection :
    |fineModulationWeight i.rev| = |fineModulationWeight i| := by
  fin_cases i <;> norm_num [fineModulationWeight, Fin.rev]

end

def finePairPacketReflection (ι : Type*) (M q : ℕ) : Equiv.Perm (FinePairPacketIndex ι M q) :=
  Equiv.prodCongr (Equiv.prodCongr (Equiv.refl _) Fin.revPerm) (Equiv.refl _)

section Packet
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

def finePairPacketMarkMass (σ : Measure Z) (a b : ℝ) (M q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ) : ℝ :=
  signedMarkMass (σ.prod Measure.count) (finePairPacketWeight a b M q C A)

def finePairPacketAbsoluteLaw (σ : Measure Z) (a b : ℝ) (M q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) : Measure (Z × FinePairPacketIndex ι M q) :=
  absoluteMarkLaw (σ.prod Measure.count) (finePairPacketWeight a b M q C A)

def finePairPacketIntercept (a b : ℝ) (M q : ℕ) (e : Z × FinePairPacketIndex ι M q) : ℝ :=
  (finePairDensityAtom a b M e.2.1).1

def finePairPacketSlope (a b : ℝ) (M q : ℕ) (ψ : Z → ℝ) (e : Z × FinePairPacketIndex ι M q) : ℝ :=
  densityMargin a b (finePairPacketIntercept a b M q e) / b *
    (finePairDensityAtom a b M e.2.1).2 * ψ e.1

section
variable (a b : ℝ) (M q : ℕ)

theorem finePairPacketIntercept_measurable :
    Measurable (finePairPacketIntercept (Z := Z) (ι := ι) a b M q) := by
  fun_prop [HighResponseMarkIndex, finePairPacketIntercept, FinePairPacketIndex, FinePairDensityIndex]

theorem finePairPacketSlope_measurable (ψ : Z → ℝ) (hψ : Measurable ψ) :
    Measurable (finePairPacketSlope (ι := ι) a b M q ψ) := by
  apply measurable_from_prod_countable_left
  intro h
  unfold finePairPacketSlope finePairPacketIntercept
  simpa using hψ.const_mul _

end

theorem finePairPacketSlope_joint_measurable {U : Type*} [MeasurableSpace U]
    (a b : ℝ) (M q : ℕ) (ψ : Z → U → ℝ)
    (hψ : Measurable (fun zu : Z × U => ψ zu.1 zu.2)) :
    Measurable (fun eu : (Z × FinePairPacketIndex ι M q) × U =>
      finePairPacketSlope a b M q (fun ζ => ψ ζ eu.2) eu.1) := by
  have hc : Measurable (fun eu : (Z × FinePairPacketIndex ι M q) × U =>
      densityMargin a b (finePairDensityAtom a b M eu.1.2.1).1 / b *
        (finePairDensityAtom a b M eu.1.2.1).2) :=
    (measurable_of_countable (fun h : FinePairPacketIndex ι M q =>
      densityMargin a b (finePairDensityAtom a b M h.1).1 / b *
        (finePairDensityAtom a b M h.1).2)).comp (measurable_snd.comp measurable_fst)
  apply hc.mul <;> fun_prop

section
variable (a b : ℝ)

theorem finePairPacketIntercept_mem (hab : a ≤ b) (M q : ℕ)
    (e : Z × FinePairPacketIndex ι M q) : finePairPacketIntercept a b M q e ∈ Icc a b :=
  by apply exteriorNode_mem <;> assumption

theorem finePairPacketSlope_bound (ha : 0 < a) (hab : a < b) (M q : ℕ)
    (ψ : Z → ℝ) (hψ : ∀ ζ, |ψ ζ| ≤ 1) (e : Z × FinePairPacketIndex ι M q) :
    |finePairPacketSlope a b M q ψ e| ≤ (b - a) / (4 * b) :=
  finePairDensityReset_slope_bound a b ha hab _ _
    (exteriorNode_mem a b hab.le (M + 2) e.2.1.1) (fineModulationNode_bound e.2.1.2)
    (fun _ : Unit => ψ e.1) () (hψ e.1)

section
variable (M q : ℕ)

theorem finePairPacketWeight_abs_reflection (C : ℝ)
    (A : Z → ι → ι → ℝ) (ζ : Z) (h : FinePairPacketIndex ι M q) :
    |finePairPacketWeight a b M q C A (ζ, finePairPacketReflection ι M q h)| =
      |finePairPacketWeight a b M q C A (ζ, h)| := by
  simp only [finePairPacketWeight, responsePacketWeight, finePairDensityWeight, finePairPacketReflection,
    Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
    Equiv.refl_apply, Fin.revPerm_apply, abs_mul,
    fineModulationWeight_abs_reflection]

theorem finePairPacketSlope_reflection (ψ : Z → ℝ) (ζ : Z)
    (h : FinePairPacketIndex ι M q) :
    finePairPacketSlope a b M q ψ (ζ, finePairPacketReflection ι M q h) =
      -finePairPacketSlope a b M q ψ (ζ, h) := by
  simp only [finePairPacketSlope, finePairPacketIntercept, finePairDensityAtom,
    finePairPacketReflection, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
    Equiv.refl_apply, Fin.revPerm_apply,
    fineModulationNode_reflection]
  ring

theorem finePairPacketSlope_absolute_sum_zero (C : ℝ)
    (A : Z → ι → ι → ℝ) (ψ : Z → ℝ) (ζ : Z) :
    (∑ h : FinePairPacketIndex ι M q, |finePairPacketWeight a b M q C A (ζ, h)| *
      finePairPacketSlope a b M q ψ (ζ, h)) = 0 :=
  finite_even_odd_sum_zero (finePairPacketReflection ι M q) _ _
    (finePairPacketWeight_abs_reflection a b M q C A ζ)
    (finePairPacketSlope_reflection a b M q ψ ζ)

end

end

variable (σ : Measure Z) [IsFiniteMeasure σ] (a b : ℝ) (M q : ℕ) (C : ℝ)
  (A : Z → ι → ι → ℝ) (hA : SeparatedMatrixIntegrable σ A)
  (hpos : 0 < finePairPacketMarkMass σ a b M q C A)
include hA hpos

theorem finePairPacketAbsoluteLaw_slope_integral_zero (ha : 0 < a) (hab : a < b)
    (ψ : Z → ℝ) (hmψ : Measurable ψ) (hψ : ∀ ζ, |ψ ζ| ≤ 1) :
    (∫ e, finePairPacketSlope a b M q ψ e ∂finePairPacketAbsoluteLaw σ a b M q C A) = 0 := by
  exact absoluteMarkLaw_integral_zero_of_slices σ _
    (finePairPacketWeight_integrable σ a b M q C A hA)
    (finePairPacketWeight_measurable a b M q C A hA.meas) hpos _
    (finePairPacketSlope_measurable a b M q ψ hmψ)
    (fun e => by simpa only [Real.norm_eq_abs] using finePairPacketSlope_bound a b ha hab M q ψ hψ e)
    (finePairPacketSlope_absolute_sum_zero a b M q C A ψ)

end Packet
end NearlyMinimax
