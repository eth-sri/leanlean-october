module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningSourceProfile

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionTimeKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ExtensionInitial
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Joint smoothness after the actual fixed-domain zero extension -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Set MeasureTheory HypoellipticAleksandrov.Parabolic

open scoped Convolution

/-- An indicator in the convolution can be integrated on a compact superset with restricted volume. -/
theorem spatialMollify_indicator_eq_integral {d : ℕ} {K Ω : Set (XV d)}
    (hK : MeasurableSet K) (hΩ : MeasurableSet Ω) (hsub : Ω ⊆ K)
    (phi : ContDiffBump (0 : XV d)) (g : XV d → ℝ) (q : XV d) :
    spatialMollify phi (Ω.indicator g) q = ∫ y : K, phi.normed volume (q - y) * g y
      ∂(Measure.comap Subtype.val (volume.restrict Ω)) := by
  rw [spatialMollify, convolution_lsmul_swap]
  simp only [smul_eq_mul, ← indicator_mul_right Ω (fun y => phi.normed volume (q - y)) g]
  rw [integral_indicator hΩ, integral_subtype_comap hK (fun y => phi.normed volume (q - y) * g y),
    Measure.restrict_restrict hK, inter_eq_right.mpr hsub]

theorem compact_restrict_comap_finite {d : ℕ} {K Ω : Set (XV d)} (hK : IsCompact K) :
    IsFiniteMeasure (Measure.comap Subtype.val (volume.restrict Ω) : Measure K) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI := IsFiniteMeasureOnCompacts.comap' (volume.restrict Ω) continuous_subtype_val
    (MeasurableEmbedding.subtype_coe hK.measurableSet)
  infer_instance

theorem zeroExtendedProfile_spatial_eq_indicator {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R : ℝ) (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R)
    (hvel : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < R ^ 2) (t : ℝ) :
    (fun y : XV d => zeroExtendedProfile (profileFunction h) alpha r mu R ⟨t, y.1, y.2⟩) =
      {y | profileFunction h y < 1}.indicator (fun y => timeCutoffTheta
        (selectedFlatProfile h r y - Real.exp (-mu * t) * (2 - PDE.vecNormSq y.2 / R ^ 2))) := by
  funext y
  by_cases hy : y ∈ {y | profileFunction h y < 1}
  · rw [indicator_of_mem hy,
      zeroExtendedProfile_eq_raw_on_profile _ alpha r mu R hr hmu hR hvel ⟨t, y.1, y.2⟩ hy]
    rfl
  · rw [indicator_of_notMem hy,
      zeroExtendedProfile_eq_zero_of_profile _ alpha r mu R ⟨t, y.1, y.2⟩ (not_lt.mp hy)]

/-- The time representative is the literal raw time derivative inside the profile domain. -/
def constructionExtendedTimeJet
    {d : ℕ} {alpha : ℝ} (h : CounterProfileStatement d alpha) (r mu R t : ℝ) (q : XV d) : ℝ :=
  {y | profileFunction h y < 1}.indicator
    (fun y => kineticTimeDerivative (timeCutoffProfile (profileFunction h) alpha r mu R)
      ⟨t, y.1, y.2⟩) q

/-- Spatial smoothing of the zero extension is jointly smooth, with time derivative given by
convolving the extended time jet. Both facts use the same fixed compact carrier. -/
theorem spatial_zeroExtendedProfile_regular_of_profile {d : ℕ} {alpha : ℝ}
    (ha : 0 < alpha) (h : CounterProfileStatement d alpha)
    (r mu R : ℝ) (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R)
    (hvel : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < R ^ 2)
    (phi : ContDiffBump (0 : XV d)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × XV d => spatialMollify phi
      (fun y => zeroExtendedProfile (profileFunction h) alpha r mu R ⟨z.1, y.1, y.2⟩) z.2) ∧
      ∀ t q, deriv (fun s => spatialMollify phi
        (fun y => zeroExtendedProfile (profileFunction h) alpha r mu R ⟨s, y.1, y.2⟩) q) t =
        spatialMollify phi (constructionExtendedTimeJet h r mu R t) q := by
  let K : Set (XV d) := {y | profileFunction h y ≤ 1}
  let Ω : Set (XV d) := {y | profileFunction h y < 1}
  have hK : IsCompact K := isCompact_profile_unit_sublevel ha h
  have hΩ : MeasurableSet Ω := measurableSet_lt (selectedProfile_spec h).continuous.measurable measurable_const
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let ν : Measure K := Measure.comap Subtype.val (volume.restrict Ω)
  letI : IsFiniteMeasure ν := compact_restrict_comap_finite hK
  have hm := spatialMollify_indicator_eq_integral hK.measurableSet hΩ
    (show Ω ⊆ K from fun y hy => show profileFunction h y ≤ 1 from
      (show profileFunction h y < 1 from hy).le) phi
  have he (t : ℝ) (q : XV d) :=
    (congrArg (fun g => spatialMollify phi g q)
      (zeroExtendedProfile_spatial_eq_indicator h r mu R hr hmu hR hvel t)).trans (hm _ q)
  simp_rw [he]
  refine ⟨compact_cutoff_mollification_contDiff ν Subtype.val continuous_subtype_val
    (fun y : K => selectedFlatProfile h r y)
    ((continuous_selectedFlatProfile h r).comp continuous_subtype_val) phi mu R, ?_⟩
  intro t q
  rw [construction_deriv_cutoff_integral ν Subtype.val continuous_subtype_val
    (fun y : K => selectedFlatProfile h r y)
    ((continuous_selectedFlatProfile h r).comp continuous_subtype_val)]
  exact (hm (fun y => kineticTimeDerivative (timeCutoffProfile (profileFunction h) alpha r mu R)
    ⟨t, y.1, y.2⟩) q).symm

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
