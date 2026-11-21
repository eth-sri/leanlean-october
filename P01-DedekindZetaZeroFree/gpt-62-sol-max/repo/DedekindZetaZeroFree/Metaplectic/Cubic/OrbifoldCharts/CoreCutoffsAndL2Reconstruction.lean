module

public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.LocalCharts.LineBundleLocalization
public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.LocalCharts.EllipticityAndCutoffs
public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.LineBundles.UnitaryFrameComparison
public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.SectionSpaces.BoundedLiftingAndDescent

@[expose] public section

noncomputable section
open scoped Classical ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree
namespace CoreChartLocalizers

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
variable (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ))

theorem Chart.rho_unitary {A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U}
    (C : Chart F ζ hζ hF U A) (g : C.G F ζ hζ hF U) :
    ‖(C.rho F ζ hζ hF U g : ℂ)‖ = 1 := by
  exact (A.line C.component).unitary _

section ChartFacts

variable {A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U} (C : Chart F ζ hζ hF U A)
theorem Chart.orthogonal_mem_ball (g : C.G F ζ hζ hF U) (x : E C.n) :
    C.orthogonal g x ∈ Metric.ball 0 C.radius ↔ x ∈ Metric.ball 0 C.radius := by
  simp only [Metric.mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map]
theorem Chart.average_eq_self (f : E C.n → ℂ)
    (heq : ∀ (g : C.G F ζ hζ hF U) x, x ∈ Metric.ball 0 C.radius →
      f (C.orthogonal g x) = (C.rho F ζ hζ hF U g : ℂ) * f x)
    {x : E C.n} (hx : x ∈ Metric.ball 0 C.radius) :
    C.average F ζ hζ hF U f x = f x := by
  rw [Chart.average, Set.indicator_of_mem hx]
  have hs : (∑ g : C.G F ζ hζ hF U,
      (((C.rho F ζ hζ hF U g)⁻¹ : ℂˣ) : ℂ) * f (C.orthogonal g x)) =
      (Fintype.card (C.G F ζ hζ hF U) : ℂ) * f x := by
    simp [heq _ _ hx, ← mul_assoc]
  rw [hs, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]
theorem Chart.average_zero_outside (f : E C.n → ℂ)
    {x : E C.n} (hx : x ∉ Metric.ball 0 C.radius) :
    C.average F ζ hζ hF U f x = 0 := by
  exact Set.indicator_of_notMem hx _

theorem Chart.average_equivariant (f : E C.n → ℂ)
    (h : C.G F ζ hζ hF U) (x : E C.n) :
    C.average F ζ hζ hF U f (C.orthogonal h x) =
      (C.rho F ζ hζ hF U h : ℂ) * C.average F ζ hζ hF U f x := by
  by_cases hx : x ∈ Metric.ball 0 C.radius
  · rw [Chart.average, Set.indicator_of_mem ((C.orthogonal_mem_ball F ζ hζ hF U h x).mpr hx),
      Set.indicator_of_mem hx]
    have hs : (∑ g : C.G F ζ hζ hF U,
        (((C.rho F ζ hζ hF U g)⁻¹ : ℂˣ) : ℂ) * f (C.orthogonal g (C.orthogonal h x))) =
        (C.rho F ζ hζ hF U h : ℂ) *
        ∑ g : C.G F ζ hζ hF U,
          (((C.rho F ζ hζ hF U g)⁻¹ : ℂˣ) : ℂ) * f (C.orthogonal g x) := by
      rw [Finset.mul_sum]
      apply Fintype.sum_equiv (Equiv.mulRight h)
      intro g
      change (((C.rho F ζ hζ hF U g)⁻¹ : ℂˣ) : ℂ) *
        f (C.orthogonal g (C.orthogonal h x)) =
        (C.rho F ζ hζ hF U h : ℂ) *
          ((((C.rho F ζ hζ hF U (g * h))⁻¹ : ℂˣ) : ℂ) *
            f (C.orthogonal (g * h) x))
      simp only [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply,
        mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val]
      have hn := Units.ne_zero (C.rho F ζ hζ hF U h)
      field_simp
    rw [hs]
    ring
  · rw [C.average_zero_outside F ζ hζ hF U f hx,
      C.average_zero_outside F ζ hζ hF U f
        (fun hh => hx ((C.orthogonal_mem_ball F ζ hζ hF U h x).mp hh)), mul_zero]


theorem Chart.coordinates_open_embedding :
    IsOpenEmbedding (Set.restrict C.extendedDomain C.coordinates) := by
  refine ⟨C.coordinates_embedding, ?_⟩
  convert C.coordinates_open using 1
  ext y
  constructor
  · rintro ⟨x, rfl⟩; exact ⟨x.val, x.property, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
theorem Chart.coordinates_ball_open_map :
    IsOpenMap (Set.restrict (Metric.ball (0 : E C.n) C.radius) C.coordinates) := by
  let inc : Metric.ball (0 : E C.n) C.radius → C.extendedDomain := fun x =>
    ⟨x.val, C.closed_ball_in_extension (subset_closure x.property)⟩
  have ho : IsOpenMap inc := by
    exact (Metric.isOpen_ball.isOpenMap_subtype_val).subtype_mk _
  exact (Chart.coordinates_open_embedding F ζ hζ hF U C).isOpenMap.comp ho
theorem Chart.toBase_ball_open_map :
    IsOpenMap (Set.restrict (Metric.ball (0 : E C.n) C.radius) (C.toBase F ζ hζ hF U)) := by
  let Γ := KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative C.component)
  letI : ContinuousConstSMul Γ (KPFiniteCuspAtlas.SymmetricSpace F) :=
    ⟨fun g => KPCuspSiegel.continuous_action F g.val⟩
  have hq : IsOpenMap (KPCuspSiegel.projection F Γ) := isOpenMap_quotient_mk'_mul
  have hc : IsOpenMap (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative C.component)) := by
    have hh := A.components.isOpenMap.comp (isOpenMap_sigmaMk (i := C.component))
    simpa only [Function.comp_def, A.components_formula] using hh
  exact hc.comp (hq.comp (Chart.coordinates_ball_open_map F ζ hζ hF U C))
theorem Chart.open_image : IsOpen (C.O F ζ hζ hF U) := by
  have ho := (Chart.toBase_ball_open_map F ζ hζ hF U C).isOpen_range
  convert ho using 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨x, rfl⟩; exact ⟨x.val, x.property, rfl⟩
theorem Chart.toBase_ball_continuous :
    Continuous (Set.restrict (Metric.ball (0 : E C.n) C.radius) (C.toBase F ζ hζ hF U)) := by
  let inc : Metric.ball (0 : E C.n) C.radius → C.extendedDomain := fun x =>
    ⟨x.val, C.closed_ball_in_extension (subset_closure x.property)⟩
  have hi : Continuous inc := continuous_subtype_val.subtype_mk _
  have hc : Continuous (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative C.component)) := by
    have hh := A.components.continuous.comp (continuous_sigmaMk (i := C.component))
    simpa only [Function.comp_def, A.components_formula] using hh
  exact hc.comp (continuous_quot_mk.comp (C.coordinates_embedding.continuous.comp hi))
theorem Chart.measurePreserving_ball (g : C.G F ζ hζ hF U) :
    MeasurePreserving (C.orthogonal g)
      (volume.restrict (Metric.ball (0 : E C.n) C.radius))
      (volume.restrict (Metric.ball (0 : E C.n) C.radius)) := by
  have he : (C.orthogonal g) ⁻¹' Metric.ball (0 : E C.n) C.radius =
      Metric.ball (0 : E C.n) C.radius := by
    ext x
    exact C.orthogonal_mem_ball F ζ hζ hF U g x
  have hm : MeasurePreserving (C.orthogonal g) (volume : Measure (E C.n)) volume :=
    LinearIsometryEquiv.measurePreserving (C.orthogonal g)
  have hr := hm.restrict_preimage (s := Metric.ball (0 : E C.n) C.radius)
    Metric.isOpen_ball.measurableSet
  rw [he] at hr
  exact hr

def Chart.orthogonalPullback (g : C.G F ζ hζ hF U) :
    Lp ℂ 2 (volume.restrict (Metric.ball (0 : E C.n) C.radius)) →ₗᵢ[ℂ]
      Lp ℂ 2 (volume.restrict (Metric.ball (0 : E C.n) C.radius)) :=
  Lp.compMeasurePreservingₗᵢ ℂ (C.orthogonal g)
    (Chart.measurePreserving_ball F ζ hζ hF U C g)

def Chart.averageLp :
    Lp ℂ 2 (volume.restrict (Metric.ball (0 : E C.n) C.radius)) →L[ℂ]
      Lp ℂ 2 (volume.restrict (Metric.ball (0 : E C.n) C.radius)) :=
  (Fintype.card (C.G F ζ hζ hF U) : ℂ)⁻¹ •
    ∑ g : C.G F ζ hζ hF U, (((C.rho F ζ hζ hF U g)⁻¹ : ℂˣ) : ℂ) •
      (Chart.orthogonalPullback F ζ hζ hF U C g).toContinuousLinearMap
theorem Chart.norm_averageLp_le
    (f : Lp ℂ 2 (volume.restrict (Metric.ball (0 : E C.n) C.radius))) :
    ‖Chart.averageLp F ζ hζ hF U C f‖ ≤ ‖f‖ := by
  simp only [Chart.averageLp, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    norm_smul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (Fintype.card (C.G F ζ hζ hF U) : ℝ)⁻¹ *
        ∑ g : C.G F ζ hζ hF U,
          ‖((((C.rho F ζ hζ hF U g)⁻¹ : ℂˣ) : ℂ) •
            (Chart.orthogonalPullback F ζ hζ hF U C g).toContinuousLinearMap f)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = (Fintype.card (C.G F ζ hζ hF U) : ℝ)⁻¹ *
        ((Fintype.card (C.G F ζ hζ hF U) : ℝ) * ‖f‖) := by
      congr 1
      simp only [norm_smul, Units.val_inv_eq_inv_val, norm_inv,
        C.rho_unitary F ζ hζ hF U, inv_one, one_mul,
        LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ‖f‖ := by
      rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]
theorem Chart.averageLp_formula
    (f : Lp ℂ 2 (volume.restrict (Metric.ball (0 : E C.n) C.radius))) :
    Chart.averageLp F ζ hζ hF U C f =ᵐ[volume.restrict (Metric.ball (0 : E C.n) C.radius)]
      C.average F ζ hζ hF U f := by
  let b : C.G F ζ hζ hF U → ℂ := fun g => (((C.rho F ζ hζ hF U g)⁻¹ : ℂˣ) : ℂ)
  let p := fun g : C.G F ζ hζ hF U => Chart.orthogonalPullback F ζ hζ hF U C g f
  have hp : ∀ g, (p g : E C.n → ℂ) =ᵐ[volume.restrict (Metric.ball (0 : E C.n) C.radius)]
      fun x => f (C.orthogonal g x) := fun g =>
    Lp.coeFn_compMeasurePreserving f (Chart.measurePreserving_ball F ζ hζ hF U C g)
  have hb : ∀ g, ((b g • p g : Lp ℂ 2 (volume.restrict (Metric.ball (0 : E C.n) C.radius))) : E C.n → ℂ)
      =ᵐ[volume.restrict (Metric.ball (0 : E C.n) C.radius)]
        fun x => b g * f (C.orthogonal g x) := by
    intro g
    exact (Lp.coeFn_smul (b g) (p g)).trans ((hp g).const_smul (b g))
  have hsum := Lp.coeFn_finsetSum Finset.univ (fun g => b g • p g)
  have hs := hsum.trans (eventuallyEq_sum fun g _ => hb g)
  have hout := (Lp.coeFn_smul (Fintype.card (C.G F ζ hζ hF U) : ℂ)⁻¹
    (∑ g, b g • p g)).trans (hs.const_smul _)
  filter_upwards [hout, ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hball
  simpa only [Chart.averageLp, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    LinearIsometry.coe_toContinuousLinearMap, Chart.average, Set.indicator_of_mem hball,
    b, p, Pi.smul_apply, smul_eq_mul, Finset.sum_apply] using hx
theorem Chart.average_congr_ae {f k : E C.n → ℂ}
    (hfk : f =ᵐ[volume.restrict (Metric.ball (0 : E C.n) C.radius)] k) :
    C.average F ζ hζ hF U f =ᵐ[volume.restrict (Metric.ball (0 : E C.n) C.radius)]
      C.average F ζ hζ hF U k := by
  have hg : ∀ g : C.G F ζ hζ hF U,
      (fun x => f (C.orthogonal g x)) =ᵐ[volume.restrict (Metric.ball (0 : E C.n) C.radius)]
        fun x => k (C.orthogonal g x) := fun g =>
    (Chart.measurePreserving_ball F ζ hζ hF U C g).quasiMeasurePreserving.ae_eq_comp hfk
  filter_upwards [Filter.eventually_all.mpr hg] with x hx
  by_cases hball : x ∈ Metric.ball (0 : E C.n) C.radius
  · simp only [Chart.average, Set.indicator_of_mem hball]
    congr 1
    apply Finset.sum_congr rfl
    intro g _
    rw [hx g]
  · simp only [Chart.average, Set.indicator_of_notMem hball]

end ChartFacts

theorem cutoff_derivative_bounds {n : ℕ} {f : E n → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ∃ B : ℕ → ℝ, (∀ k, 0 ≤ B k) ∧
      ∀ k x, ‖iteratedFDeriv ℝ k f x‖ ≤ B k := by
  choose B hB hbound using hc.exists_bound_iteratedFDeriv hf
  exact ⟨B, hB, fun k x => hbound k k le_rfl x⟩

end CoreChartLocalizers

end DedekindZetaZeroFree

end
