module

public import NearlyMinimax.HistoryReferenceMeasure
public import NearlyMinimax.ProductDensity

@[expose] public section

/-!
# The actual positive polynomial density on independently marked histories

Each history is evaluated in its canonical word. Its signed weight is the
proved finite upper-set polynomial, not a prescribed prior density.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ENNReal
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

/-- The signed mark at an actual canonical heap occurrence. -/
def historyMarkedPieceWeight (dependent : J → J → Prop) {E : Type*}
    (a : E → ℝ) (h : HistoryMarked dependent E) (x : WordHeapPiece h.1.out dependent) : ℝ :=
  a (h.2 (Fin.cast (historyShapeLength_out dependent h.1).symm x.position))

/-- The source upper-set polynomial on the actual marked dependency heap. -/
def historyMarkedDensity (dependent : J → J → Prop) (ρ t : ℝ) {E : Type*}
    (a : E → ℝ) (h : HistoryMarked dependent E) : ℝ :=
  historyScaledUpperDensity (historyMarkedPieceWeight dependent a h) ρ Finset.univ t

section
variable (dependent : J → J → Prop) (ρ t : ℝ) {E : Type*}
    [MeasurableSpace E] (a : E → ℝ) (ha : Measurable a)
include ha

theorem historyMarkedPieceWeight_fiber_measurable
    (g : HistoryShape (fun i j => ¬ dependent i j)) (x : WordHeapPiece g.out dependent) :
    Measurable (fun marks => historyMarkedPieceWeight dependent a ⟨g, marks⟩ x) :=
  ha.comp (measurable_pi_apply (Fin.cast (historyShapeLength_out dependent g).symm x.position))

theorem historyMarkedSubdensity_fiber_measurable
    (g : HistoryShape (fun i j => ¬ dependent i j)) (S : Finset (WordHeapPiece g.out dependent)) :
    Measurable (fun marks => historyScaledUpperDensity (historyMarkedPieceWeight dependent a ⟨g, marks⟩) ρ S t) := by
  classical
  simp_rw [historyScaledUpperDensity_eq_components, historyComponentWeight]
  exact Finset.measurable_fun_sum _ fun P _ =>
    (Finset.measurable_fun_prod P fun x _ => historyMarkedPieceWeight_fiber_measurable dependent a ha g x).const_mul
      ((t / ρ) ^ P.card * historyOrderVolume P)

theorem historyMarkedDensity_measurable :
    Measurable (historyMarkedDensity dependent ρ t a) :=
  (historySigma_measurable_iff _).2
    (fun g => historyMarkedSubdensity_fiber_measurable dependent ρ t a ha g Finset.univ)

end

/-- The source positivity interval is uniform over all shapes and all bounded marks. -/
theorem historyMarkedDensity_bounds {dependent : J → J → Prop} {Δ : ℕ}
    (geom : HistoryDegreeBound dependent Δ)
    (ρ t B : ℝ) (hρ : 0 < ρ) (ht : 0 ≤ t) (hB : 0 ≤ B)
    {E : Type*} (a : E → ℝ) (ha : ∀ e, |a e| ≤ B)
    (hsmall : t * B / ρ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2)) (h : HistoryMarked dependent E) :
    (1 / 2 : ℝ) ^ Fintype.card J ≤ historyMarkedDensity dependent ρ t a h ∧
      historyMarkedDensity dependent ρ t a h ≤ (3 / 2 : ℝ) ^ Fintype.card J :=
  wordHeap_density_bounds h.1.out geom
    (historyMarkedPieceWeight dependent a h) ρ t B hρ ht hB (fun _ => ha _) hsmall

section
variable {I A E : Type*} [Fintype I] [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (a : E → ℝ)
    (index : A → I) (hi : Function.Injective index) (P : Finset A)
include hi

/-- Restrict to the independent mark coordinates occupied by the pieces in `P`. -/
private theorem history_piece_projection :
    MeasurePreserving (fun marks : I → E => fun x : P => marks (index x))
      (Measure.pi fun _ : I => π) (Measure.pi fun _ : P => π) :=
  finite_probability_pi_embedding_preserving (fun _ => π)
    ⟨fun x : P => index x, fun x y h => Subtype.ext (hi h)⟩

section
variable (ha : Integrable a π)
include ha

theorem historyIntegral_pi_indexed_prod :
    (∫ marks : I → E, ∏ x ∈ P, a (marks (index x)) ∂Measure.pi (fun _ => π)) =
      ∏ _x ∈ P, ∫ e, a e ∂π := by
  let f : (P → E) → ℝ := fun marks => ∏ x, a (marks x)
  have hp := history_piece_projection π index hi P
  have hf : Integrable f (Measure.pi fun _ => π) := Integrable.fintype_prod (fun _ => ha)
  calc
    _ = ∫ marks : I → E, f (fun x => marks (index x)) ∂Measure.pi (fun _ => π) :=
      integral_congr_ae (Filter.Eventually.of_forall fun marks => (Finset.prod_coe_sort P (fun x => a (marks (index x)))).symm)
    _ = ∫ marks, f marks ∂Measure.pi (fun _ => π) := by
      conv_rhs => rw [← hp.map_eq]
      exact (integral_map hp.measurable.aemeasurable (by rw [hp.map_eq]; exact hf.aestronglyMeasurable)).symm
    _ = _ := by rw [integral_fintype_prod_eq_prod]; exact Finset.prod_coe_sort P (fun _ => ∫ e, a e ∂π)

theorem historyIntegrable_pi_indexed_prod :
    Integrable (fun marks : I → E => ∏ x ∈ P, a (marks (index x))) (Measure.pi (fun _ => π)) := by
  exact ((history_piece_projection π index hi P).integrable_comp_of_integrable
      (Integrable.fintype_prod (μ := fun _ : P => π) (f := fun _ => a) (fun _ => ha))).congr
    (Filter.Eventually.of_forall fun marks => Finset.prod_coe_sort P (fun x => a (marks (index x))))

end

end

/-- Occurrences in a canonical heap have distinct independent mark coordinates. -/
def historyMarkedPieceIndex (dependent : J → J → Prop)
    (g : HistoryShape (fun i j => ¬ dependent i j)) : WordHeapPiece g.out dependent → Fin (historyShapeLength dependent g) :=
  fun x => Fin.cast (historyShapeLength_out dependent g).symm x.position

section
variable (dependent : J → J → Prop)

theorem historyMarkedPieceIndex_injective
    (g : HistoryShape (fun i j => ¬ dependent i j)) :
    Function.Injective (historyMarkedPieceIndex dependent g) := by
  intro x y hxy
  apply WordHeapPiece.ext
  exact Fin.cast_injective _ hxy

/-- Centering kills every nonempty upper-set monomial of the actual density. -/
theorem historyMarkedDensity_fiber_integral_one (ρ t : ℝ) {E : Type*}
    [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π]
    (a : E → ℝ) (ha : Integrable a π) (hcenter : ∫ e, a e ∂π = 0)
    (g : HistoryShape (fun i j => ¬ dependent i j)) :
    (∫ marks, historyMarkedDensity dependent ρ t a ⟨g, marks⟩
      ∂Measure.pi (fun _ : Fin (historyShapeLength dependent g) => π)) = 1 := by
  classical
  let index := historyMarkedPieceIndex dependent g
  have hi : Function.Injective index := historyMarkedPieceIndex_injective dependent g
  have hterm : ∀ P : Finset (WordHeapPiece g.out dependent),
      Integrable (fun marks => (t / ρ) ^ P.card * historyOrderVolume P * ∏ x ∈ P, a (marks (index x)))
        (Measure.pi (fun _ : Fin (historyShapeLength dependent g) => π)) := by
    intro P
    exact (historyIntegrable_pi_indexed_prod π a index hi P ha).const_mul _
  unfold historyMarkedDensity
  simp_rw [historyScaledUpperDensity_eq_components, historyComponentWeight]
  change (∫ marks, ∑ P ∈ historyUpperSets (Finset.univ : Finset (WordHeapPiece g.out dependent)),
    (t / ρ) ^ P.card * historyOrderVolume P * ∏ x ∈ P, a (marks (index x))
    ∂Measure.pi (fun _ : Fin (historyShapeLength dependent g) => π)) = 1
  rw [integral_finsetSum _ (fun P _ => hterm P)]
  simp_rw [integral_const_mul, historyIntegral_pi_indexed_prod π a index hi _ ha, hcenter]
  rw [Finset.sum_eq_single ∅]
  · simp
  · simp_all [Finset.prod_const]
  · simpa using (hnot (mem_historyUpperSets.2 ⟨Finset.empty_subset _, by simp⟩)).elim

@[simp] theorem historyMarkedDensity_zero (ρ : ℝ) {E : Type*}
    (a : E → ℝ) (h : HistoryMarked dependent E) : historyMarkedDensity dependent ρ 0 a h = 1 := by
  unfold historyMarkedDensity historyScaledUpperDensity
  exact historyUpperDensity_at_zero _ _

end

/-- The actual polynomial tilts the independent marks within a shape. -/
def historyMarkedFiberPrior (dependent : J → J → Prop) (Δ : ℕ) (t : ℝ) {E : Type*}
    [MeasurableSpace E] (π : Measure E) (a : E → ℝ)
    (g : HistoryShape (fun i j => ¬ dependent i j)) :
    Measure (Fin (historyShapeLength dependent g) → E) :=
  (Measure.pi (fun _ => π)).withDensity
    (fun marks => ENNReal.ofReal (historyMarkedDensity dependent (historyReferenceRho Δ) t a ⟨g, marks⟩))

/-- Positivity is derived from the dependency heap, and normalization from centered marks. -/
theorem historyMarkedFiberPrior_probability {dependent : J → J → Prop} {Δ : ℕ}
    (geom : HistoryDegreeBound dependent Δ)
    (t B : ℝ) (ht : 0 ≤ t) (hB : 0 ≤ B) {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (a : E → ℝ) (ha : Integrable a π)
    (hcenter : ∫ e, a e ∂π = 0) (habound : ∀ e, |a e| ≤ B)
    (hsmall : t * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    (g : HistoryShape (fun i j => ¬ dependent i j)) :
    IsProbabilityMeasure (historyMarkedFiberPrior dependent Δ t π a g) := by
  have he := historyMarkedDensity_fiber_integral_one dependent (historyReferenceRho Δ) t π a ha hcenter g
  have hi := integrable_of_integral_eq_one he
  have hnonneg : ∀ marks, 0 ≤ historyMarkedDensity dependent (historyReferenceRho Δ) t a ⟨g, marks⟩ := by
    intro marks
    have hb := historyMarkedDensity_bounds geom _ t B
      (historyReferenceRho_pos Δ) ht hB a habound hsmall ⟨g, marks⟩
    exact (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1
  constructor
  unfold historyMarkedFiberPrior
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hnonneg), he]
  simp

/-- The actual positive marked-history prior before source reference normalization. -/
def historyMarkedPriorRaw (dependent : J → J → Prop) (Δ : ℕ) (t : ℝ) {E : Type*}
    [MeasurableSpace E] (π : Measure E) (a : E → ℝ) : Measure (HistoryMarked dependent E) :=
  Measure.sum fun g => ENNReal.ofReal (historyShapeReferenceWeight dependent Δ g) •
    Measure.map (Sigma.mk g) (historyMarkedFiberPrior dependent Δ t π a g)

/-- The path uses exactly the same time-independent source normalizer. -/
def historyMarkedPrior (dependent : J → J → Prop) (Δ : ℕ) (t : ℝ) {E : Type*}
    [MeasurableSpace E] (π : Measure E) (a : E → ℝ) : Measure (HistoryMarked dependent E) :=
  (historyMarkedReferenceRaw dependent Δ π Set.univ)⁻¹ • historyMarkedPriorRaw dependent Δ t π a

section
variable {dependent : J → J → Prop} {Δ : ℕ}
    (geom : HistoryDegreeBound dependent Δ)
include geom

theorem historyMarkedPriorRaw_univ
    (t B : ℝ) (ht : 0 ≤ t) (hB : 0 ≤ B) {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (a : E → ℝ) (ha : Integrable a π)
    (hcenter : ∫ e, a e ∂π = 0) (habound : ∀ e, |a e| ≤ B)
    (hsmall : t * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2)) :
    historyMarkedPriorRaw dependent Δ t π a Set.univ = historyMarkedReferenceRaw dependent Δ π Set.univ := by
  rw [historyMarkedReferenceRaw_univ]
  unfold historyMarkedPriorRaw
  rw [Measure.sum_apply _ MeasurableSet.univ]
  congr 1
  funext g
  let : IsProbabilityMeasure (historyMarkedFiberPrior dependent Δ t π a g) :=
    historyMarkedFiberPrior_probability geom t B ht hB π a ha hcenter habound hsmall g
  simp_all

/-- The source path of positive prior measures is genuinely constructed for the whole interval. -/
private theorem historyMarkedPrior_probability (hΔ : 1 ≤ Δ)
    (t B : ℝ) (ht : 0 ≤ t) (hB : 0 ≤ B) {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (a : E → ℝ) (ha : Integrable a π)
    (hcenter : ∫ e, a e ∂π = 0) (habound : ∀ e, |a e| ≤ B)
    (hsmall : t * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2)) :
    IsProbabilityMeasure (historyMarkedPrior dependent Δ t π a) := by
  let : IsFiniteMeasure (historyMarkedReferenceRaw dependent Δ π) :=
    historyMarkedReferenceRaw_finite geom hΔ π
  have hn :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (historyMarkedReferenceRaw_univ_one_le dependent Δ π))
  constructor
  unfold historyMarkedPrior
  rw [Measure.smul_apply, historyMarkedPriorRaw_univ geom t B ht hB π a ha hcenter habound hsmall,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel hn (measure_ne_top _ _)

end

/-- Uniform small-activity conditions for a centered marked-history prior on `[0,T]`. -/
structure HistoryPriorBounds (dependent : J → J → Prop) (Δ : ℕ)
    {E : Type*} [MeasurableSpace E] (π : Measure E) (a : E → ℝ) (T B : ℝ) : Prop
    extends HistoryDegreeBound dependent Δ where
  degree_pos : 1 ≤ Δ
  measurable : Measurable a
  centered : ∫ e, a e ∂π = 0
  bound_nonneg : 0 ≤ B
  bound : ∀ e, |a e| ≤ B
  small : T * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2)

namespace HistoryPriorBounds

variable {dependent : J → J → Prop} {Δ : ℕ} {E : Type*} [MeasurableSpace E]
    {π : Measure E} [IsProbabilityMeasure π] {a : E → ℝ} {T B : ℝ}
    (P : HistoryPriorBounds dependent Δ π a T B)
include P

lemma reference_probability : IsProbabilityMeasure (historyMarkedReference dependent Δ π) :=
  historyMarkedReference_probability P.toHistoryDegreeBound P.degree_pos π

section
variable {t : ℝ}

theorem small_at (ht : t ≤ T) :
    t * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2) :=
  (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht P.bound_nonneg)
    (historyReferenceRho_pos Δ).le).trans P.small

theorem density_bounds (ht : t ∈ Set.Icc 0 T) (h : HistoryMarked dependent E) :
    (1 / 2 : ℝ) ^ Fintype.card J ≤ historyMarkedDensity dependent (historyReferenceRho Δ) t a h ∧
    historyMarkedDensity dependent (historyReferenceRho Δ) t a h ≤ (3 / 2 : ℝ) ^ Fintype.card J :=
  historyMarkedDensity_bounds P.toHistoryDegreeBound _ t B (historyReferenceRho_pos Δ)
    ht.1 P.bound_nonneg a P.bound (P.small_at ht.2) h

theorem density_nonneg (ht : t ∈ Set.Icc 0 T) (h : HistoryMarked dependent E) :
    0 ≤ historyMarkedDensity dependent (historyReferenceRho Δ) t a h :=
  (by positivity : 0 ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans (P.density_bounds ht h).1

theorem probability (ht : t ∈ Set.Icc 0 T) :
    IsProbabilityMeasure (historyMarkedPrior dependent Δ t π a) := by
  exact historyMarkedPrior_probability P.toHistoryDegreeBound P.degree_pos
    t B ht.1 P.bound_nonneg π a (Integrable.of_bound P.measurable.aestronglyMeasurable B
      (.of_forall fun e => by simpa only [Real.norm_eq_abs] using P.bound e))
    P.centered P.bound (P.small_at ht.2)

end

end HistoryPriorBounds

end NearlyMinimax
