module

public import NearlyMinimax.HistoryReferenceMeasure


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

section
variable (dependent : J → J → Prop) (ρ t : ℝ) {E : Type*}

/-- The signed mark at an actual canonical heap occurrence. -/
def historyMarkedPieceWeight
    (a : E → ℝ) (h : HistoryMarked dependent E) (x : WordHeapPiece h.1.out dependent) : ℝ :=
  a (h.2 (Fin.cast (historyShapeLength_out h.1).symm x.position))

/-- The source upper-set polynomial on the actual marked dependency heap. -/
def historyMarkedDensity {dependent : J → J → Prop} (ρ t : ℝ) {E : Type*}
    (a : E → ℝ) (h : HistoryMarked dependent E) : ℝ :=
  historyScaledUpperDensity (historyMarkedPieceWeight dependent a h) ρ Finset.univ t

theorem historyMarkedDensity_fiber_measurable
    [MeasurableSpace E] {a : E → ℝ} (ha : Measurable a)
    (g : DependenceHeap dependent) :
    Measurable (fun marks => historyMarkedDensity ρ t a ⟨g, marks⟩) := by
  classical
  unfold historyMarkedDensity
  simp_rw [historyScaledUpperDensity_eq_components, historyComponentWeight]
  change Measurable (fun marks : Fin (historyShapeLength g) → E =>
    ∑ P ∈ historyUpperSets (Finset.univ : Finset (WordHeapPiece g.out dependent)),
      (t / ρ) ^ P.card * historyOrderVolume P * ∏ x ∈ P,
        a (marks (Fin.cast (historyShapeLength_out g).symm x.position)))
  fun_prop

theorem historyMarkedDensity_measurable
    [MeasurableSpace E] {a : E → ℝ} (ha : Measurable a) :
    Measurable (historyMarkedDensity (dependent := dependent) ρ t a) :=
  (sigma_measurable_iff _).2
    (historyMarkedDensity_fiber_measurable dependent ρ t ha)

end

/-- The source positivity interval is uniform over all shapes and all bounded marks. -/
theorem historyMarkedDensity_bounds {dependent : J → J → Prop}
    [Std.Refl dependent] [Std.Symm dependent]
    {Δ : ℕ} (hlabels : DegreeAtMost dependent Δ)
    {ρ t B : ℝ} (hρ : 0 < ρ) (ht : 0 ≤ t) (hB : 0 ≤ B)
    {E : Type*} {a : E → ℝ} (ha : ∀ e, |a e| ≤ B)
    (hsmall : t * B / ρ ≤ historyActivityRadius Δ) (h : HistoryMarked dependent E) :
    (1 / 2 : ℝ) ^ Fintype.card J ≤ historyMarkedDensity ρ t a h ∧
      historyMarkedDensity ρ t a h ≤ (3 / 2 : ℝ) ^ Fintype.card J :=
  wordHeap_density_bounds hlabels
    (historyMarkedPieceWeight dependent a h) hρ ht hB (fun _ => ha _) hsmall

section
variable {I E : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace E]

/-- A finite product over selected independent coordinates factors into expectations. -/
theorem historyIntegral_pi_finset_prod (π : Measure E) [IsProbabilityMeasure π] (a : E → ℝ) (S : Finset I) :
    (∫ marks : I → E, ∏ i ∈ S, a (marks i) ∂Measure.pi (fun _ => π)) =
      ∏ _i ∈ S, ∫ e, a e ∂π := by
  classical
  have hp : ∀ marks : I → E, (∏ i : I, if i ∈ S then a (marks i) else 1) =
      ∏ i ∈ S, a (marks i) := fun marks => Finset.prod_ite_mem_eq S _
  simp_rw [← hp]
  rw [integral_fintype_prod_eq_prod (fun (i : I) (e : E) => if i ∈ S then a e else 1)]
  calc
    _ = _ := by
      apply Finset.prod_congr rfl
      aesop
    _ = _ := Finset.prod_ite_mem_eq S _

theorem historyIntegrable_pi_finset_prod {π : Measure E} [IsProbabilityMeasure π] {a : E → ℝ}
    (ha : Integrable a π) (S : Finset I) :
    Integrable (fun marks : I → E => ∏ i ∈ S, a (marks i)) (Measure.pi (fun _ => π)) := by
  classical
  have hp := Integrable.fintype_prod (μ := fun _ : I => π)
    (f := fun i e => if i ∈ S then a e else 1)
    (fun i => by by_cases hi : i ∈ S <;> simp [hi, ha])
  simpa using hp

end

section
variable {I A E : Type*} [Fintype I] [DecidableEq I] [DecidableEq A] [MeasurableSpace E]

/-- Selected independent mark products factor even with an injective piece indexing. -/
theorem historyIntegral_pi_indexed_prod (π : Measure E) [IsProbabilityMeasure π]
    (a : E → ℝ) {index : A → I} (hi : Function.Injective index) (P : Finset A) :
    (∫ marks : I → E, ∏ x ∈ P, a (marks (index x)) ∂Measure.pi (fun _ => π)) =
      ∏ _x ∈ P, ∫ e, a e ∂π := by
  have hp : ∀ marks : I → E, (∏ i ∈ P.image index, a (marks i)) =
      ∏ x ∈ P, a (marks (index x)) := fun marks => Finset.prod_image hi.injOn
  calc
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun marks => (hp marks).symm)
    _ = _ := historyIntegral_pi_finset_prod π a _
    _ = _ := Finset.prod_image hi.injOn

theorem historyIntegrable_pi_indexed_prod {π : Measure E} [IsProbabilityMeasure π]
    {a : E → ℝ} (ha : Integrable a π) {index : A → I}
    (hi : Function.Injective index) (P : Finset A) :
    Integrable (fun marks : I → E => ∏ x ∈ P, a (marks (index x))) (Measure.pi (fun _ => π)) := by
  have hp := historyIntegrable_pi_finset_prod ha (P.image index)
  simpa only [Finset.prod_image hi.injOn] using hp

end

section
variable {dependent : J → J → Prop} (ρ : ℝ) (Δ : ℕ) (t : ℝ) {E : Type*} (g : DependenceHeap dependent)

/-- Occurrences in a canonical heap have distinct independent mark coordinates. -/
def historyMarkedPieceIndex : WordHeapPiece g.out dependent → Fin (historyShapeLength g) :=
  fun x => Fin.cast (historyShapeLength_out g).symm x.position

theorem historyMarkedPieceIndex_injective :
    Function.Injective (historyMarkedPieceIndex g) := by
  intro x y hxy
  apply WordHeapPiece.ext
  exact Fin.cast_injective _ hxy

/-- Centering kills every nonempty upper-set monomial of the actual density. -/
theorem historyMarkedDensity_fiber_integral_one
    [MeasurableSpace E] {π : Measure E} [IsProbabilityMeasure π]
    {a : E → ℝ} (ha : Integrable a π) (hcenter : ∫ e, a e ∂π = 0)
    (g : DependenceHeap dependent) :
    (∫ marks, historyMarkedDensity ρ t a ⟨g, marks⟩
      ∂Measure.pi (fun _ : Fin (historyShapeLength g) => π)) = 1 := by
  classical
  let index := historyMarkedPieceIndex g
  have hi  := historyMarkedPieceIndex_injective g
  have hterm : ∀ P : Finset (WordHeapPiece g.out dependent),
      Integrable (fun marks => (t / ρ) ^ P.card * historyOrderVolume P * ∏ x ∈ P, a (marks (index x)))
        (Measure.pi (fun _ : Fin (historyShapeLength g) => π)) := fun P => (historyIntegrable_pi_indexed_prod ha hi P).const_mul _
  unfold historyMarkedDensity
  simp_rw [historyScaledUpperDensity_eq_components, historyComponentWeight]
  change (∫ marks, ∑ P ∈ historyUpperSets Finset.univ,
    (t / ρ) ^ P.card * historyOrderVolume P * ∏ x ∈ P, a (marks (index x))
    ∂Measure.pi (fun _ : Fin (historyShapeLength g) => π)) = 1
  rw [integral_finsetSum _ (fun P _ => hterm P)]
  simp_rw [integral_const_mul, historyIntegral_pi_indexed_prod π a (index := index) hi, hcenter]
  rw [Finset.sum_eq_single ∅]
  · simp
  · aesop
  · simp

@[simp] theorem historyMarkedDensity_zero (dependent : J → J → Prop) (ρ : ℝ) {E : Type*}
    (a : E → ℝ) (h : HistoryMarked dependent E) : historyMarkedDensity ρ 0 a h = 1 := by
  unfold historyMarkedDensity historyScaledUpperDensity
  exact historyUpperDensity_at_zero _ _

/-- The actual polynomial tilts the independent marks within a shape. -/
def historyMarkedFiberPrior
    [MeasurableSpace E] (π : Measure E) (a : E → ℝ)
    (g : DependenceHeap dependent) :
    Measure (Fin (historyShapeLength g) → E) :=
  (Measure.pi (fun _ => π)).withDensity
    (fun marks => ENNReal.ofReal (historyMarkedDensity (historyReferenceRho Δ) t a ⟨g, marks⟩))

/-- Positivity is derived from the dependency heap, and normalization from centered marks. -/
theorem historyMarkedFiberPrior_probability
    [Std.Refl dependent] [Std.Symm dependent]
    {Δ : ℕ} (hlabels : DegreeAtMost dependent Δ)
    {t B : ℝ} (ht : 0 ≤ t) (hB : 0 ≤ B) {E : Type*} [MeasurableSpace E]
    {π : Measure E} [IsProbabilityMeasure π] {a : E → ℝ} (ha : Integrable a π)
    (hcenter : ∫ e, a e ∂π = 0) (habound : ∀ e, |a e| ≤ B)
    (hsmall : t * B / historyReferenceRho Δ ≤ historyActivityRadius Δ)
    (g : DependenceHeap dependent) :
    IsProbabilityMeasure (historyMarkedFiberPrior Δ t π a g) := by
  have he := historyMarkedDensity_fiber_integral_one (historyReferenceRho Δ) t ha hcenter g
  have hi := integrable_of_integral_eq_one he
  have hnonneg : ∀ marks, 0 ≤ historyMarkedDensity (historyReferenceRho Δ) t a ⟨g, marks⟩ := by
    intro marks
    have hb := historyMarkedDensity_bounds hlabels
      (historyReferenceRho_pos Δ) ht hB habound hsmall ⟨g, marks⟩
    exact (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1
  constructor
  unfold historyMarkedFiberPrior
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hnonneg), he]
  simp

end

section
variable (dependent : J → J → Prop) (Δ : ℕ) (t : ℝ) {E : Type*} [MeasurableSpace E] (π : Measure E)
    (a : E → ℝ)

/-- The actual positive marked-history prior before source reference normalization. -/
def historyMarkedPriorRaw : Measure (HistoryMarked dependent E) :=
  Measure.sum fun g => ENNReal.ofReal (historyShapeReferenceWeight Δ g) •
    Measure.map (Sigma.mk g) (historyMarkedFiberPrior Δ t π a g)

/-- The path uses exactly the same time-independent source normalizer. -/
def historyMarkedPrior : Measure (HistoryMarked dependent E) :=
  (historyMarkedReferenceRaw dependent Δ π Set.univ)⁻¹ • historyMarkedPriorRaw dependent Δ t π a

end

variable {dependent : J → J → Prop} [Std.Refl dependent] [Std.Symm dependent] {Δ : ℕ} (hΔ : 1 ≤ Δ)
    (hlabels : DegreeAtMost dependent Δ) {t B : ℝ} (ht : 0 ≤ t) (hB : 0 ≤ B) {E : Type*}
    [MeasurableSpace E] {π : Measure E} [IsProbabilityMeasure π] {a : E → ℝ} (ha : Integrable a π)
    (hcenter : ∫ e, a e ∂π = 0) (habound : ∀ e, |a e| ≤ B)
    (hsmall : t * B / historyReferenceRho Δ ≤ historyActivityRadius Δ)
include hlabels ht hB ha hcenter habound hsmall

theorem historyMarkedPriorRaw_univ :
    historyMarkedPriorRaw dependent Δ t π a Set.univ = historyMarkedReferenceRaw dependent Δ π Set.univ := by
  rw [historyMarkedReferenceRaw_univ]
  unfold historyMarkedPriorRaw
  rw [Measure.sum_apply _ MeasurableSet.univ]
  congr 1
  funext g
  let  :=
    historyMarkedFiberPrior_probability hlabels ht hB ha hcenter habound hsmall g
  simp

include hΔ in
/-- The source path of positive prior measures is genuinely constructed for the whole interval. -/
theorem historyMarkedPrior_probability :
    IsProbabilityMeasure (historyMarkedPrior dependent Δ t π a) := by
  let  :=
    historyMarkedReferenceRaw_finite hΔ hlabels π
  have hn  :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (historyMarkedReferenceRaw_univ_one_le dependent Δ π))
  constructor
  unfold historyMarkedPrior
  rw [Measure.smul_apply, historyMarkedPriorRaw_univ hlabels ht hB ha hcenter habound hsmall,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel hn (measure_ne_top _ _)

end NearlyMinimax
