module

public import HypoellipticAleksandrov.Parabolic.WeakDerivatives
public import HypoellipticAleksandrov.Statements.HormanderHypoellipticity
public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.MeasureTheory.Constructions.Pi

/-! # Test calculus for the parabolic operator

The zeroth coordinate is time. All other coordinate derivatives are spatial. We use the
linear functional on tests associated to a function, so that integration against sums of
compactly supported derivatives does not require separate integrability proofs.
-/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Hypoellipticity
open MeasureTheory Set Filter KineticAleksandrov
open scoped Topology

abbrev Sm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) := ContDiff ℝ (⊤ : ℕ∞) f
abbrev Field (d : ℕ) := {f : TimeVelocity d → ℝ // Sm f}
abbrev Domain (d : ℕ) := TopologicalSpace.Opens (TimeVelocity d)
abbrev Test {d} (U : Domain d) := TestFunction U ℝ (⊤ : ℕ∞)

variable {d : ℕ} {U : Domain d}

abbrev unpack (d : ℕ) := (Fin.consEquivL ℝ (fun _ : Fin (d+1) => ℝ)).symm

private theorem unpack_preserving : MeasurePreserving (unpack d) volume volume := by
  convert volume_preserving_piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0 using 1
  ext x
  · rfl
  · simp [unpack, MeasurableEquiv.piFinSuccAbove, Fin.succAbove_zero]

abbrev dir (i : Fin (d+1)) := unpack d (PDE.basisVec i)

@[simp] theorem dir_zero : dir (0 : Fin (d+1)) = (1,0) := by
  ext j <;> simp [dir, unpack, Fin.tail, PDE.basisVec, Pi.single_apply]

@[simp] theorem dir_succ (i : Fin d) : dir i.succ = (0,PDE.basisVec i) := by
  ext j <;> simp [dir, unpack, Fin.tail, PDE.basisVec, Pi.single_apply]

def pd (i : Fin (d+1)) (f : TimeVelocity d → ℝ) (z : TimeVelocity d) := fderiv ℝ f z (dir i)

theorem pd_sm (i : Fin (d+1)) {f : TimeVelocity d → ℝ} (hf : Sm f) : Sm (pd i f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

def part (i : Fin (d+1)) : Test U →L[ℝ] Test U := TestFunction.lineDerivCLM ℝ (dir i)

@[simp] theorem part_val (i : Fin (d+1)) (φ : Test U) (z) : part i φ z = pd i φ z := by
  simp [part, pd, (φ.contDiff.differentiable (by simp) z).lineDeriv_eq_fderiv]

def times (a : Field d) : Test U →ₗ[ℝ] Test U where
  toFun φ := ⟨a.1 * φ, a.2.mul φ.contDiff, φ.hasCompactSupport.mul_left, tsupport_mul_subset_right.trans φ.tsupport_subset⟩
  map_add' _ _ := TestFunction.ext fun _ => mul_add ..
  map_smul' _ _ := TestFunction.ext fun _ => mul_left_comm ..

@[simp] theorem times_val (a : Field d) (φ : Test U) (z) : times a φ z = a.1 z * φ z := rfl

@[simp] theorem pd_times (i : Fin (d+1)) (a : Field d) (φ : Test U) (z) :
    pd i (times a φ) z = a.1 z * pd i φ z + pd i a.1 z * φ z := by
  change fderiv ℝ (a.1 * ⇑φ) z _ = _
  rw [fderiv_mul (a.2.differentiable (by simp) z) (φ.contDiff.differentiable (by simp) z)]
  simp [pd, mul_comm, add_comm]

def weight (U : Domain d) (f : TimeVelocity d → ℝ) : Test U →L[ℝ] ℝ :=
  TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℝ ℝ) (volume.restrict U) f

theorem weight_apply {f : TimeVelocity d → ℝ} (hf : LocallyIntegrableOn f U (volume.restrict (U : Set _))) (φ : Test U) :
    weight U f φ = ∫ z in U, f z * φ z := by
  rw [weight, TestFunction.integralAgainstBilinCLM_eq_integral hf]
  simp [mul_comm]

/-- Adjoint of a vector field, without the minus sign. Each component is a packed coordinate. -/
def adj (X : Fin (d+1) → Field d) (φ : Test U) : Test U := ∑ j, part j (times (X j) φ)

abbrev liftField (X : Fin (d+1) → Field d) (x : PDE.Vec (d+1)) : PDE.Vec (d+1) :=
  fun j => (X j).1 (unpack d x)

theorem div_comp_unpack (X : Fin (d+1) → Field d) (φ : Test U) (x : PDE.Vec (d+1)) :
    euclideanDivergence (fun y => φ (unpack d y) • liftField X y) x = adj X φ (unpack d x) := by
  unfold euclideanDivergence adj
  simp only [FunLike.coe_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  let g (y : PDE.Vec (d+1)) := φ (unpack d y) • liftField X y
  have hg : Differentiable ℝ g := ((φ.contDiff.comp (unpack d).contDiff).differentiable (by simp)).smul
    (differentiable_pi.mpr fun k => ((X k).2.comp (unpack d).contDiff).differentiable (by simp))
  have h₁ := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d+1) => ℝ) j).hasFDerivAt.comp x (hg x).hasFDerivAt).fderiv
  have h₂ := (((times (X j) φ).contDiff.differentiable (by simp) (unpack d x)).hasFDerivAt.comp x
    (unpack d).hasFDerivAt).fderiv
  have heq : (fun y => g y j) = (times (X j) φ) ∘ unpack d := funext fun _ => mul_comm ..
  exact (congrArg (fun L : PDE.Vec (d+1) →L[ℝ] ℝ => L (PDE.basisVec j))
    ((h₁.symm.trans (congrArg (fun f => fderiv ℝ f x) heq)).trans h₂)).trans (part_val ..).symm

/-- Apply Hörmander in native time–velocity coordinates. -/
theorem smooth_rep {k : ℕ} (X : Fin (k+1) → Fin (d+1) → Field d)
    (span : LieAlgebraSpansOn ((unpack d) ⁻¹' (U : Set _)) (fun i => liftField (X i)))
    {f g : TimeVelocity d → ℝ} (hf : LocallyIntegrableOn f U volume) (hg : Sm g)
    (eqn : ∀ φ : Test U,
      weight U f (-adj (X 0) φ + ∑ i : Fin k, adj (X i.succ) (adj (X i.succ) φ)) = weight U g φ) :
    ∃ w : TimeVelocity d → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) w U ∧ f =ᵐ[volume.restrict U] w := by
  let e := unpack d
  let V := e ⁻¹' (U : Set _)
  have hmp := unpack_preserving (d := d) |>.restrict_preimage_emb e.toHomeomorph.measurableEmbedding (U : Set _)
  have hx (i : Fin (k+1)) : ContDiff ℝ (⊤ : ℕ∞) (liftField (X i)) :=
    contDiff_pi.mpr fun j => ((X i j).2.comp e.contDiff)
  obtain ⟨w, hw, he⟩ := exists_smooth_aeRepresentative_of_hormander (U.isOpen.preimage e.continuous)
    (fun i => liftField (X i)) (fun _ => 0) (g ∘ e) (f ∘ e) (fun i => (hx i).contDiffOn) span
    contDiffOn_const (by
      refine ⟨(locallyIntegrableOn_iff (U.isOpen.preimage e.continuous).isLocallyClosed).mpr ?_, (hg.comp e.contDiff).contDiffOn, ?_⟩
      · intro K hKV hK
        have hi := hf.integrableOn_compact_subset (image_subset_iff.mpr hKV) (hK.image e.continuous)
        simpa only [e, (unpack d).injective.preimage_image] using (unpack_preserving.integrableOn_comp_preimage e.toHomeomorph.measurableEmbedding).mpr hi
      intro ψ hψ hc hs
      let φ : Test U := ⟨ψ ∘ e.symm, hψ.comp e.symm.contDiff,
        hc.comp_isClosedEmbedding e.symm.toHomeomorph.isClosedEmbedding, by
          change tsupport (ψ ∘ e.symm.toHomeomorph) ⊆ _
          rw [tsupport_comp_eq_preimage ψ e.symm.toHomeomorph]
          intro z hz; exact (show e (e.symm z) ∈ U from hs hz) |> fun h => by simpa using h⟩
      have hφ : (fun y => φ (e y)) = ψ := by ext; simp [φ]
      have hD (i : Fin (k+1)) (q : Test U) : (euclideanDivergence fun y => q (e y) • liftField (X i) y) = (fun x => adj (X i) q (e x)) := funext (div_comp_unpack (X i) q)
      have hid (y : PDE.Vec (d+1)) : hormanderAdjointTest (fun i => liftField (X i)) (fun _ => 0) ψ y =
          (-adj (X 0) φ + ∑ i : Fin k, adj (X i.succ) (adj (X i.succ) φ) : Test U) (e y) := by
        rw [← hφ]; simp only [hormanderAdjointTest, hD, zero_mul, add_zero]; simp
      simp_rw [hid, ← hφ]
      have h := eqn φ
      rw [weight_apply (hf.mono_measure Measure.restrict_le_self), weight_apply (hg.continuous.locallyIntegrable.locallyIntegrableOn U)] at h
      exact (hmp.integral_comp e.toHomeomorph.measurableEmbedding _).trans
        (h.trans (hmp.integral_comp e.toHomeomorph.measurableEmbedding _).symm))
  refine ⟨w ∘ e.symm, hw.comp e.symm.contDiff.contDiffOn (fun z hz => by simpa [V] using hz), ?_⟩
  rw [← hmp.map_eq, EventuallyEq, (show MeasurableEmbedding (unpack d) from e.toHomeomorph.measurableEmbedding).ae_map_iff]
  change ∀ᵐ x ∂volume.restrict V, f (e x) = w (e.symm (e x))
  filter_upwards [he] with x hx
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using! hx

end HypoellipticAleksandrov.Parabolic.Hypoellipticity
