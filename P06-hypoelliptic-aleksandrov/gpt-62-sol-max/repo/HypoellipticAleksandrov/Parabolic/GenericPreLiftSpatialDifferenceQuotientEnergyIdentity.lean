module

public import HypoellipticAleksandrov.Parabolic.ParabolicMemLpSpatialDifferenceQuotient
public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientWeakDerivatives
public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientTest
public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientL2Transpose
public import HypoellipticAleksandrov.Parabolic.SpatialTranslationWeakDerivatives
public import HypoellipticAleksandrov.Parabolic.SpacetimeMollifierL2
public import HypoellipticAleksandrov.Parabolic.SpacetimeMollifierWeightedTimeEnergy
public import HypoellipticAleksandrov.Parabolic.TimeVelocitySmoothCompactPlateau
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesCompactGlobalization
public import HypoellipticAleksandrov.Parabolic.WeakDerivativeSpacetimeMollification
public import HypoellipticAleksandrov.Parabolic.WeakJetProduct
import HypoellipticAleksandrov.Parabolic.WeakJetLocalization
import HypoellipticAleksandrov.Parabolic.SpacetimeMollificationSupport

/-!
# Quotient-test energy identity

This module begins the direct spacetime-mollification proof of the localized
spatial difference-quotient energy identity.  The private infrastructure below
constructs a precompact shift-safe collar and globalizes the localized value
and its selected weak spatial derivatives.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped Convolution ENNReal Pointwise Topology
open HypoellipticAleksandrov.Parabolic.SpacetimeMollifier
open SpacetimeMollifierWeightedTimeEnergy Analysis

/-- A smooth directional derivative commutes with the spatial quotient. -/
private theorem fderiv_spatialDifferenceQuotient
    {d : ℕ} (k : Fin d) (h : ℝ) {f : TimeVelocity d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (z e : TimeVelocity d) :
    fderiv ℝ (spatialDifferenceQuotient k h f) z e =
      spatialDifferenceQuotient k h (fun y => fderiv ℝ f y e) z := by
  have hd := hf.differentiable (by simp) z
  have ht := (ContDiff.spatialTranslate (k := k) (h := h) hf).differentiable (by simp) z
  rw [spatialDifferenceQuotient_eq_smul, fderiv_const_smul (ht.sub hd), fderiv_sub ht hd]
  have htr : fderiv ℝ (spatialTranslate k h f) z = fderiv ℝ f (spatialShift k h z) :=
    fderiv_comp_add_right (0, h • PDE.basisVec k)
  rw [htr]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, smul_eq_mul,
    spatialDifferenceQuotient_apply, spatialTranslate_apply, div_eq_mul_inv, mul_comm]

/-- Transpose the derivative of a backward quotient using a carrier that contains
both the compact test support and its forward shift. -/
private theorem setIntegral_mul_fderiv_spatialDifferenceQuotient_neg
    {d : ℕ} {S C V : Set (TimeVelocity d)}
    (hS : MeasurableSet S) (hC : MeasurableSet C) (hCS : C ⊆ S) (hVC : V ⊆ C)
    (H : TimeVelocity d → ℝ) (hH : ParabolicMemLpOn C 2 H)
    (k : Fin d) (h : ℝ) (f : TimeVelocity d → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) (hs : tsupport f ⊆ V)
    (hshift : MapsTo (spatialShift k h) V C) (e : TimeVelocity d) :
    (∫ z in S, H z * fderiv ℝ (spatialDifferenceQuotient k (-h) f) z e) =
      -∫ z in V, spatialDifferenceQuotient k h H z * fderiv ℝ f z e := by
  let g := fun z => fderiv ℝ f z e
  have hg : tsupport g ⊆ V := (tsupport_fderiv_apply_subset ℝ e).trans hs
  have hq := tsupport_spatialDifferenceQuotient_subset_of_mapsTo_spatialShift_neg
    k (-h) g hg hVC (by simpa using hshift)
  have h := setIntegral_spatialDifferenceQuotient_mul_eq_neg_mul_spatialDifferenceQuotient_neg
    C k h H g hH ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hc.fderiv_apply ℝ e) (hg.trans hVC) (fun _ hz => hshift (hg hz))
  simp_rw [fderiv_spatialDifferenceQuotient _ _ hf]
  rw [setIntegral_mul_eq_of_tsupport_subset hS hCS _ _ hq]
  rw [setIntegral_mul_eq_of_tsupport_subset hC hVC _ _ hg] at h
  linarith only [h]

section
variable {d : ℕ}

/-- A selected velocity derivative of a backward quotient transposes from a
smooth compact test to the forward quotient of an `L²` factor. -/
private theorem setIntegral_mul_velocityGradient_spatialDifferenceQuotient_neg {S C V : Set (TimeVelocity d)}
    (hSmeas : MeasurableSet S) (hCcompact : IsCompact C)
    (hCS : C ⊆ S) (hVC : V ⊆ C)
    (H : TimeVelocity d → ℝ) (hH : ParabolicMemLpOn C 2 H)
    (k : Fin d) (h : ℝ) (f : TimeVelocity d → ℝ)
    (hfSmooth : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfCompact : HasCompactSupport f) (hfSupport : tsupport f ⊆ V)
    (hfShift : Set.MapsTo (spatialShift k h) V C) (i : Fin d) :
    (∫ z in S, H z * velocityGradient
        (spatialDifferenceQuotient k (-h) f) z i) =
      -∫ z in V, spatialDifferenceQuotient k h H z * velocityGradient f z i := 
  setIntegral_mul_fderiv_spatialDifferenceQuotient_neg hSmeas hCcompact.measurableSet
    hCS hVC H hH k h f hfSmooth hfCompact hfSupport hfShift (0, Pi.single i 1)

/-- Transposition of the time derivative of a backward quotient from a smooth
compact test to the forward quotient of the rough factor, with the latter
pairing restricted to its shift-safe carrier. -/
private theorem setIntegral_mul_timeDerivative_spatialDifferenceQuotient_neg {S V : Set (TimeVelocity d)}
    (hSmeas : MeasurableSet S) (hVS : V ⊆ S)
    (q : TimeVelocity d → ℝ) (hq : ParabolicMemLpOn S 2 q)
    (k : Fin d) (h : ℝ) (f : TimeVelocity d → ℝ)
    (hfSmooth : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfCompact : HasCompactSupport f) (hfSupport : tsupport f ⊆ V)
    (hfShift : Set.MapsTo (spatialShift k h) V S) :
    (∫ z in S, q z * timeDerivative
        (spatialDifferenceQuotient k (-h) f) z) =
      -∫ z in V, spatialDifferenceQuotient k h q z * timeDerivative f z := 
  setIntegral_mul_fderiv_spatialDifferenceQuotient_neg hSmeas hSmeas Subset.rfl
    hVS q hq k h f hfSmooth hfCompact hfSupport hfShift (1, 0)

/-- A local `L²` representative can be globalized without changing the
weighted time-energy pairing near the support of the smooth weight. -/
private theorem tendsto_localized_timeEnergy_spacetimeMollification {V : Set (TimeVelocity d)}
    (hVopen : IsOpen V)
    (qh w : TimeVelocity d → ℝ) (hqh : ParabolicMemLpOn V 2 qh)
    (hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwCompact : HasCompactSupport w) (hwSupport : tsupport w ⊆ V) :
    Filter.Tendsto (fun ε : ℝ ↦ ∫ z in V, qh z *
        timeDerivative (spacetimeMollification ε (fun y ↦ w y * qh y)) z)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((1 / 2 : ℝ) * ∫ z in V,
        timeDerivative w z * qh z ^ 2)) := by
  let Q := V.indicator qh
  have hV := hVopen.measurableSet
  have hQ : MemLp Q 2 volume := (memLp_indicator_iff_restrict hV).2 hqh
  have hwQ : (fun z => w z * Q z) = fun z => w z * qh z := by
    funext z
    by_cases hz : z ∈ V
    · simp [Q, hz]
    · simp [Q, hz, image_eq_zero_of_notMem_tsupport (fun hs => hz (hwSupport hs))]
  have hleft (ε : ℝ) : (∫ z, Q z * timeDerivative (spacetimeMollification ε (fun y => w y * Q y)) z) =
      ∫ z in V, qh z * timeDerivative (spacetimeMollification ε (fun y => w y * qh y)) z := by
    rw [hwQ, ← integral_indicator hV]
    exact integral_congr_ae (ae_of_all _ fun z => by by_cases hz : z ∈ V <;> simp [Q, hz])
  have hright : (∫ z, timeDerivative w z * Q z ^ 2) = ∫ z in V, timeDerivative w z * qh z ^ 2 := by
    rw [← integral_indicator hV]
    exact integral_congr_ae (ae_of_all _ fun z => by by_cases hz : z ∈ V <;> simp [Q, hz])
  simpa only [hleft, hright] using
    tendsto_integral_mul_timeDerivative_spacetimeMollification_mul Q w hQ hwSmooth hwCompact

/-- The localized quotient test and all its selected spatial derivatives have
global `L²` representatives and ambient weak-derivative relations. -/
private theorem exists_global_localizedQuotient_weakGradient {S : Set (TimeVelocity d)} (hS : IsOpen S)
    (q : TimeVelocity d → ℝ) (G : Fin d → TimeVelocity d → ℝ)
    (hq : ParabolicMemLpOn S 2 q)
    (hG : ∀ j, ParabolicMemLpOn S 2 (G j))
    (hWeak : ∀ j, HasWeakVelocityPartialDerivOn S j q (G j))
    (w : TimeVelocity d → ℝ)
    (hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwCompact : HasCompactSupport w) (hwSupport : tsupport w ⊆ S)
    (k : Fin d) (h : ℝ)
    (hwShift : Set.MapsTo (spatialShift k h) (tsupport w) S) :
    ∃ V C : Set (TimeVelocity d), IsOpen V ∧ IsCompact (closure V) ∧
      tsupport w ⊆ V ∧ V ⊆ S ∧
      IsCompact C ∧ V ⊆ C ∧ C ⊆ S ∧
      Set.MapsTo (spatialShift k h) V C ∧
      ParabolicMemLpOn V 2 (spatialDifferenceQuotient k h q) ∧
      (∀ i, ParabolicMemLpOn V 2 (spatialDifferenceQuotient k h (G i))) ∧
      (∀ i, HasWeakVelocityPartialDerivOn V i
        (spatialDifferenceQuotient k h q)
        (spatialDifferenceQuotient k h (G i))) ∧
      MemLp (fun z ↦ w z * spatialDifferenceQuotient k h q z) 2 volume ∧
      (∀ i, MemLp (fun z ↦
        velocityGradient w z i * spatialDifferenceQuotient k h q z +
          w z * spatialDifferenceQuotient k h (G i) z) 2 volume) ∧
      (∀ i, HasWeakVelocityPartialDerivOn Set.univ i
        (fun z ↦ w z * spatialDifferenceQuotient k h q z)
        (fun z ↦ velocityGradient w z i * spatialDifferenceQuotient k h q z +
          w z * spatialDifferenceQuotient k h (G i) z)) ∧
      ∀ i, tsupport (fun z ↦
        velocityGradient w z i * spatialDifferenceQuotient k h q z +
          w z * spatialDifferenceQuotient k h (G i) z) ⊆ V := by
  let K : Set (TimeVelocity d) := tsupport w
  let U : Set (TimeVelocity d) :=
    S ∩ spatialShift k h ⁻¹' S
  have hshiftContinuous : Continuous (spatialShift k h) := by
    convert (Homeomorph.addRight
      ((0, h • PDE.basisVec k) : TimeVelocity d)).continuous using 1
    funext z
    apply Prod.ext
    · simp [spatialShift]
    · rfl
  have hU : IsOpen U := hS.inter (hS.preimage hshiftContinuous)
  have hKU : K ⊆ U := by
    intro z hz
    exact ⟨hwSupport hz, hwShift hz⟩
  obtain ⟨δ, hδ, hcollar⟩ := hwCompact.isCompact.exists_cthickening_subset_open hU hKU
  let V : Set (TimeVelocity d) := Metric.thickening δ K
  have hVopen : IsOpen V := Metric.isOpen_thickening
  have hVclosure : IsCompact (closure V) := by
    apply IsCompact.of_isClosed_subset hwCompact.isCompact.cthickening isClosed_closure
    exact Metric.closure_thickening_subset_cthickening δ K
  have hKV : K ⊆ V := Metric.self_subset_thickening hδ K
  have hVU : V ⊆ U :=
    (Metric.thickening_subset_cthickening δ K).trans hcollar
  have hclosureVU : closure V ⊆ U :=
    (Metric.closure_thickening_subset_cthickening δ K).trans hcollar
  have hVS : V ⊆ S := fun z hz ↦ (hVU hz).1
  have hVshift : Set.MapsTo (spatialShift k h) V S := fun z hz ↦ (hVU hz).2
  let C : Set (TimeVelocity d) :=
    closure V ∪ spatialShift k h '' closure V
  have hCcompact : IsCompact C := by
    exact hVclosure.union (hVclosure.image hshiftContinuous)
  have hVC : V ⊆ C := by
    intro z hz
    exact Or.inl (subset_closure hz)
  have hCS : C ⊆ S := by
    rintro z (hz | ⟨y, hy, rfl⟩)
    · exact (hclosureVU hz).1
    · exact (hclosureVU hy).2
  have hVshiftC : Set.MapsTo (spatialShift k h) V C := by
    intro z hz
    exact Or.inr ⟨z, subset_closure hz, rfl⟩
  let qh : TimeVelocity d → ℝ := spatialDifferenceQuotient k h q
  let Gh : Fin d → TimeVelocity d → ℝ := fun i ↦
    spatialDifferenceQuotient k h (G i)
  let Dψ : Fin d → TimeVelocity d → ℝ := fun i z ↦
    velocityGradient w z i * qh z + w z * Gh i z
  have hqh : ParabolicMemLpOn V 2 qh :=
    hq.spatialDifferenceQuotient_of_subset_mapsTo k h hVS hVshift
  have hGh (i : Fin d) : ParabolicMemLpOn V 2 (Gh i) :=
    (hG i).spatialDifferenceQuotient_of_subset_mapsTo k h hVS hVshift
  have hqhWeak (i : Fin d) : HasWeakVelocityPartialDerivOn V i qh (Gh i) := by
    exact (hWeak i).spatialDifferenceQuotient_of_subset_mapsTo
      (hq.locallyIntegrableOn (by norm_num))
      ((hG i).locallyIntegrableOn (by norm_num)) k h hVS hVshift
  have hj := localized_gradient_jet_univ (b := w) (q := qh) (QG := fun z i => Gh i z)
    hVopen hqh hGh hqhWeak hwSmooth hwCompact hKV
  rcases hj with ⟨hψ, hDψ, hψWeak, _, hDψSupport⟩
  have hDψeq (i : Fin d) : localizedGradient w qh (fun z i => Gh i z) i = Dψ i := by
    funext z
    simp only [localizedGradient, Dψ]
    ring
  simp only [hDψeq] at hDψ hψWeak hDψSupport
  exact ⟨V, C, hVopen, hVclosure, hKV, hVS, hCcompact, hVC, hCS, hVshiftC,
    hqh, hGh, hqhWeak, hψ, hDψ, hψWeak, hDψSupport⟩

/-- Positive-radius mollification of the localized quotient gives smooth
compact tests, their exact selected gradients, and a backward-quotient test
whose support remains in the original open carrier. -/
private theorem exists_mollifiedLocalizedQuotient_testPackage {S V : Set (TimeVelocity d)}
    (hVopen : IsOpen V) (hVcompact : IsCompact (closure V))
    (hVS : V ⊆ S) (k : Fin d) (h : ℝ)
    (hVshift : Set.MapsTo (spatialShift k h) V S)
    (ψ : TimeVelocity d → ℝ) (Dψ : Fin d → TimeVelocity d → ℝ)
    (hψ : MemLp ψ 2 volume) (hDψ : ∀ i, MemLp (Dψ i) 2 volume)
    (hψWeak : ∀ i, HasWeakVelocityPartialDerivOn Set.univ i ψ (Dψ i))
    (hψSupport : tsupport ψ ⊆ V) :
    ∃ r : ℝ, 0 < r ∧
      (∀ ε : ℝ, 0 < ε → ε < r →
        ContDiff ℝ (⊤ : ℕ∞) (spacetimeMollification ε ψ) ∧
        HasCompactSupport (spacetimeMollification ε ψ) ∧
        tsupport (spacetimeMollification ε ψ) ⊆ V ∧
        (∀ i z, velocityGradient (spacetimeMollification ε ψ) z i =
          spacetimeMollification ε (Dψ i) z) ∧
        ContDiff ℝ (⊤ : ℕ∞)
          (spatialDifferenceQuotient k (-h) (spacetimeMollification ε ψ)) ∧
        HasCompactSupport
          (spatialDifferenceQuotient k (-h) (spacetimeMollification ε ψ)) ∧
        tsupport (spatialDifferenceQuotient k (-h)
          (spacetimeMollification ε ψ)) ⊆ S) := by
  have hψCompact : HasCompactSupport ψ :=
    hVcompact.of_isClosed_subset (isClosed_tsupport ψ) (hψSupport.trans subset_closure)
  obtain ⟨r, hr, hcollar⟩ := hψCompact.isCompact.exists_cthickening_subset_open
    hVopen hψSupport
  refine ⟨r, hr, ?_⟩
  intro ε hε hεr
  have hsmooth := contDiff_spacetimeMollification hε ψ
    (hψ.locallyIntegrable (by norm_num))
  have hcompact : HasCompactSupport (spacetimeMollification ε ψ) := by
    exact (spacetimeMollifier_hasCompactSupport hε).convolution
      (ContinuousLinearMap.lsmul ℝ ℝ) hψCompact
  have hsupp : tsupport (spacetimeMollification ε ψ) ⊆ V :=
    (_root_.HypoellipticAleksandrov.Parabolic.SpacetimeMollifier.tsupport_spacetimeMollification_subset_cthickening hε).trans
      ((Metric.cthickening_mono hεr.le (tsupport ψ)).trans hcollar)
  have hgrad (i : Fin d) := velocityGradient_spacetimeMollification hε i ψ (Dψ i)
    (hψ.locallyIntegrable (by norm_num))
    ((hDψ i).locallyIntegrable (by norm_num)) (hψWeak i)
  have htestSmooth : ContDiff ℝ (⊤ : ℕ∞)
      (spatialDifferenceQuotient k (-h) (spacetimeMollification ε ψ)) :=
    ContDiff.spatialDifferenceQuotient hsmooth
  have htestCompact : HasCompactSupport
      (spatialDifferenceQuotient k (-h) (spacetimeMollification ε ψ)) :=
    HasCompactSupport.spatialDifferenceQuotient hcompact
  have htestSupport : tsupport (spatialDifferenceQuotient k (-h)
      (spacetimeMollification ε ψ)) ⊆ S := by
    exact tsupport_spatialDifferenceQuotient_subset_of_mapsTo_spatialShift_neg
      k (-h) (spacetimeMollification ε ψ) hsupp hVS (by simpa using hVshift)
  exact ⟨hsmooth, hcompact, hsupp, fun i z ↦ congrFun (hgrad i) z,
    htestSmooth, htestCompact, htestSupport⟩

/-- Fixed spatial quotients preserve strong `L²` convergence. -/
private theorem strongL2_spatialDifferenceQuotient {ι : Type*} {l : Filter ι} {f : ι → TimeVelocity d → ℝ} {f₀ : TimeVelocity d → ℝ}
    (hf : StrongL2Limit l volume f f₀) (k : Fin d) (h : ℝ) :
    StrongL2Limit l volume (fun ε => spatialDifferenceQuotient k h (f ε))
      (spatialDifferenceQuotient k h f₀) := by
  simp only [spatialDifferenceQuotient_eq_smul]
  exact ((hf.comp_measurePreserving (spatialShift_measurePreserving k h)).sub hf).const_mul h⁻¹

end

section
variable {d : ℕ}

/-- The source stays undifferenced when the mollified localized quotient is
passed to the fixed backward quotient. -/
private theorem tendsto_sourcePairing_mollifiedBackwardQuotient (S : Set (TimeVelocity d)) (R ψ : TimeVelocity d → ℝ)
    (hR : ParabolicMemLpOn S 2 R) (hψ : MemLp ψ 2 volume)
    (k : Fin d) (h : ℝ) :
    Filter.Tendsto (fun ε : ℝ ↦ ∫ z in S, R z *
      spatialDifferenceQuotient k (-h) (spacetimeMollification ε ψ) z)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ z in S, R z * spatialDifferenceQuotient k (-h) ψ z)) := 
  (StrongL2Limit.const hR).pairing
    ((strongL2_spatialDifferenceQuotient (SpacetimeMollifierL2.spacetimeMollification_strongL2 hψ) k (-h)).restrict S)

/-- Rearranging the supplied divergence identity for the mollified
backward-quotient test gives the signs produced by testing with its negative. -/
private theorem testedEquation_neg_mollifiedBackwardQuotient {S : Set (TimeVelocity d)}
    (A : TimeVelocity d → PDE.Mat d) (q R : TimeVelocity d → ℝ)
    (G : Fin d → TimeVelocity d → ℝ)
    (hEq : ∀ φ : TimeVelocity d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ S →
      -(∫ z in S, q z * timeDerivative φ z) -
          ∑ i, ∑ j, ∫ z in S,
            A z i j * G j z * velocityGradient φ z i =
        ∫ z in S, R z * φ z)
    (k : Fin d) (h ε : ℝ) (ψ : TimeVelocity d → ℝ)
    (hεSmooth : ContDiff ℝ (⊤ : ℕ∞)
      (spacetimeMollification ε ψ))
    (hεCompact : HasCompactSupport (spacetimeMollification ε ψ))
    (hTestSupport : tsupport (spatialDifferenceQuotient k (-h)
      (spacetimeMollification ε ψ)) ⊆ S) :
    (∫ z in S, q z * timeDerivative
        (spatialDifferenceQuotient k (-h) (spacetimeMollification ε ψ)) z) +
      ∑ i, ∑ j, ∫ z in S, A z i j * G j z *
        velocityGradient
          (spatialDifferenceQuotient k (-h) (spacetimeMollification ε ψ)) z i =
      -(∫ z in S, R z * spatialDifferenceQuotient k (-h)
        (spacetimeMollification ε ψ) z) := by
  have hTestSmooth : ContDiff ℝ (⊤ : ℕ∞)
      (spatialDifferenceQuotient k (-h) (spacetimeMollification ε ψ)) :=
    ContDiff.spatialDifferenceQuotient hεSmooth
  have hTestCompact : HasCompactSupport
      (spatialDifferenceQuotient k (-h) (spacetimeMollification ε ψ)) :=
    HasCompactSupport.spatialDifferenceQuotient hεCompact
  have heq := hEq
    (spatialDifferenceQuotient k (-h) (spacetimeMollification ε ψ))
    hTestSmooth hTestCompact hTestSupport
  linarith

/-- A spatial difference quotient commutes exactly with a finite sum, without
any regularity or nonzero-step assumption. -/
private theorem spatialDifferenceQuotient_finset_sum {ι : Type*} (s : Finset ι) (k : Fin d) (h : ℝ)
    (H : ι → TimeVelocity d → ℝ) :
    spatialDifferenceQuotient k h (fun x ↦ ∑ j ∈ s, H j x) =
      fun z ↦ ∑ j ∈ s, spatialDifferenceQuotient k h (H j) z := by
  funext z
  simp only [spatialDifferenceQuotient_apply, spatialTranslate_apply]
  rw [← Finset.sum_sub_distrib, Finset.sum_div]

/-- The weighted time-energy density is integrable on the original carrier.
Only local `L²` control of the quotient near the compact weight support is
used. -/
private theorem integrableOn_timeDerivative_mul_spatialDifferenceQuotient_sq {S V : Set (TimeVelocity d)} (hVS : V ⊆ S)
    (q : TimeVelocity d → ℝ) (hq : ParabolicMemLpOn V 2 q)
    (w : TimeVelocity d → ℝ)
    (hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwCompact : HasCompactSupport w) (hwSupport : tsupport w ⊆ V) :
    IntegrableOn (fun z ↦ timeDerivative w z * q z ^ 2) S := by
  have hdtTop : ParabolicMemLpOn V ∞ (timeDerivative w) :=
    ((contDiff_infty_iff_fderiv.mp hwSmooth).2.clm_apply contDiff_const).continuous
      |>.memLp_of_hasCompactSupport
        (by
          change HasCompactSupport (fun z ↦ fderiv ℝ w z (1, 0))
          simpa using hwCompact.fderiv_apply (𝕜 := ℝ) ((1, 0) : TimeVelocity d))
      |>.restrict V
  have hV : IntegrableOn (fun z ↦ timeDerivative w z * q z ^ 2) V := by
    have hp := (hq.mul' (r := 2) hdtTop).integrable_mul hq
    apply hp.congr
    filter_upwards with z
    simp only [Pi.mul_apply]
    ring
  have hsupp : Function.support (fun z ↦ timeDerivative w z * q z ^ 2) ⊆ V := by
    intro z hz
    have hdtz : timeDerivative w z ≠ 0 := by
      intro hzero
      exact hz (by simp [hzero])
    exact hwSupport ((timeDerivative_tsupport _) (subset_tsupport _ hdtz))
  have hglobal := (integrableOn_iff_integrable_of_support_subset hsupp).mp hV
  exact (integrableOn_iff_integrable_of_support_subset (hsupp.trans hVS)).mpr hglobal

/-- Pairing an `L²` source on a carrier with a fixed backward quotient of a
global `L²` function is integrable on that carrier. -/
private theorem integrableOn_source_mul_spatialDifferenceQuotient (S : Set (TimeVelocity d))
    (R ψ : TimeVelocity d → ℝ) (hR : ParabolicMemLpOn S 2 R)
    (hψ : MemLp ψ 2 volume) (k : Fin d) (h : ℝ) :
    IntegrableOn (fun z ↦ R z * spatialDifferenceQuotient k (-h) ψ z) S := 
  hR.integrable_mul ((memLp_spatialDifferenceQuotient hψ k (-h)).restrict S)

/-- The aggregate forward flux quotient paired with a compactly supported
global `L²` test gradient is integrable on the original carrier. -/
private theorem integrableOn_sum_principalFluxQuotient_mul {S C V : Set (TimeVelocity d)}
    (hCcompact : IsCompact C) (hCS : C ⊆ S) (hVC : V ⊆ C)
    (A : TimeVelocity d → PDE.Mat d) (G : Fin d → TimeVelocity d → ℝ)
    (hFlux : ∀ i j, ∀ K : Set (TimeVelocity d), IsCompact K → K ⊆ S →
      ParabolicMemLpOn K 2 (fun z ↦ A z i j * G j z))
    (i k : Fin d) (h : ℝ)
    (hshift : Set.MapsTo (spatialShift k h) V C)
    (Dψ : TimeVelocity d → ℝ) (hDψ : MemLp Dψ 2 volume)
    (hDψSupport : tsupport Dψ ⊆ V) :
    IntegrableOn (fun z ↦ spatialDifferenceQuotient k h
        (fun x ↦ ∑ j, A x i j * G j x) z * Dψ z) S := by
  have hentries (j : Fin d) : ParabolicMemLpOn V 2
      (spatialDifferenceQuotient k h (fun z ↦ A z i j * G j z)) :=
    (hFlux i j C hCcompact hCS).spatialDifferenceQuotient_of_subset_mapsTo
      k h hVC hshift
  have hsum : ParabolicMemLpOn V 2 (fun z ↦ ∑ j,
      spatialDifferenceQuotient k h (fun x ↦ A x i j * G j x) z) :=
    memLp_finset_sum _ fun j _ ↦ hentries j
  have hV : IntegrableOn (fun z ↦ spatialDifferenceQuotient k h
      (fun x ↦ ∑ j, A x i j * G j x) z * Dψ z) V := by
    rw [spatialDifferenceQuotient_finset_sum Finset.univ k h
      (fun j x ↦ A x i j * G j x)]
    exact hsum.integrable_mul (hDψ.mono_measure Measure.restrict_le_self)
  have hsupp : Function.support (fun z ↦ spatialDifferenceQuotient k h
      (fun x ↦ ∑ j, A x i j * G j x) z * Dψ z) ⊆ V := by
    intro z hz
    have hDz : Dψ z ≠ 0 := by
      intro hzero
      exact hz (by simp [hzero])
    exact hDψSupport (subset_tsupport Dψ hDz)
  exact ((integrableOn_iff_integrable_of_support_subset hsupp).mp hV).restrict

end

/-- The quotient-test energy identity obtained from a tested divergence-form
equation by smooth compact approximation. -/
theorem integral_spatialDifferenceQuotient_energyIdentity_of_testedEquation
    (d : ℕ) (S : Set (TimeVelocity d)) (hS : IsOpen S)
    (A : TimeVelocity d → PDE.Mat d) (q R : TimeVelocity d → ℝ)
    (G : Fin d → TimeVelocity d → ℝ)
    (hq : ParabolicMemLpOn S 2 q) (hR : ParabolicMemLpOn S 2 R)
    (hG : ∀ j, ParabolicMemLpOn S 2 (G j))
    (hFlux : ∀ i j, ∀ K : Set (TimeVelocity d), IsCompact K → K ⊆ S →
      ParabolicMemLpOn K 2 (fun z ↦ A z i j * G j z))
    (hWeak : ∀ j, HasWeakVelocityPartialDerivOn S j q (G j))
    (hEq : ∀ φ : TimeVelocity d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ S →
      -(∫ z in S, q z * timeDerivative φ z) -
          ∑ i, ∑ j, ∫ z in S,
            A z i j * G j z * velocityGradient φ z i =
        ∫ z in S, R z * φ z)
    (w : TimeVelocity d → ℝ)
    (hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwCompact : HasCompactSupport w) (hwSupport : tsupport w ⊆ S)
    (k : Fin d) (h : ℝ) (hh : h ≠ 0)
    (hwShift : Set.MapsTo (spatialShift k h) (tsupport w) S) :
    IntegrableOn
        (fun z ↦ timeDerivative w z *
          (spatialDifferenceQuotient k h q z) ^ 2) S ∧
      (∀ i, IntegrableOn
        (fun z ↦ spatialDifferenceQuotient k h
            (fun x ↦ ∑ j, A x i j * G j x) z *
          (velocityGradient w z i * spatialDifferenceQuotient k h q z +
            w z * spatialDifferenceQuotient k h (G i) z)) S) ∧
      IntegrableOn
        (fun z ↦ R z * spatialDifferenceQuotient k (-h)
          (fun x ↦ w x * spatialDifferenceQuotient k h q x) z) S ∧
      (-1 / 2 : ℝ) *
          (∫ z in S, timeDerivative w z *
            (spatialDifferenceQuotient k h q z) ^ 2) -
        ∑ i, ∫ z in S, spatialDifferenceQuotient k h
            (fun x ↦ ∑ j, A x i j * G j x) z *
          (velocityGradient w z i * spatialDifferenceQuotient k h q z +
            w z * spatialDifferenceQuotient k h (G i) z) =
        -(∫ z in S, R z * spatialDifferenceQuotient k (-h)
          (fun x ↦ w x * spatialDifferenceQuotient k h q x) z) := by
  obtain ⟨V, C, hVopen, hVcompact, hwV, hVS, hCcompact, hVC, hCS,
      hVshift, hqh, hGh, hqhWeak, hψ, hDψ, hψWeak, hDψSupport⟩ :=
    exists_global_localizedQuotient_weakGradient hS q G hq hG hWeak w
      hwSmooth hwCompact hwSupport k h hwShift
  let qh : TimeVelocity d → ℝ := spatialDifferenceQuotient k h q
  let ψ : TimeVelocity d → ℝ := fun z ↦ w z * qh z
  let Dψ : Fin d → TimeVelocity d → ℝ := fun i z ↦
    velocityGradient w z i * qh z +
      w z * spatialDifferenceQuotient k h (G i) z
  obtain ⟨r, hr, htest⟩ :=
    exists_mollifiedLocalizedQuotient_testPackage hVopen hVcompact hVS k h
      (fun z hz ↦ hCS (hVshift hz)) ψ Dψ hψ hDψ hψWeak
      (tsupport_mul_subset_left.trans hwV)
  have htimeInt : IntegrableOn (fun z ↦ timeDerivative w z * qh z ^ 2) S :=
    integrableOn_timeDerivative_mul_spatialDifferenceQuotient_sq hVS qh hqh w
      hwSmooth hwCompact hwV
  have hsourceInt : IntegrableOn (fun z ↦ R z *
      spatialDifferenceQuotient k (-h) ψ z) S :=
    integrableOn_source_mul_spatialDifferenceQuotient S R ψ hR hψ k h
  have hfluxInt (i : Fin d) : IntegrableOn (fun z ↦
      spatialDifferenceQuotient k h (fun x ↦ ∑ j, A x i j * G j x) z *
        Dψ i z) S :=
    integrableOn_sum_principalFluxQuotient_mul hCcompact hCS hVC A G hFlux
      i k h hVshift (Dψ i) (hDψ i) (hDψSupport i)
  refine ⟨htimeInt, hfluxInt, hsourceInt, ?_⟩
  let l : Filter ℝ := nhdsWithin 0 (Set.Ioi 0)
  let f : ℝ → TimeVelocity d → ℝ := fun ε ↦ spacetimeMollification ε ψ
  have hevent : ∀ᶠ ε in l, 0 < ε ∧ ε < r := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hr).filter_mono inf_le_left] with ε hε hεr
    exact ⟨hε, hεr⟩
  have htimeLim : Filter.Tendsto (fun ε ↦ ∫ z in V, qh z *
      timeDerivative (f ε) z) l
      (nhds ((1 / 2 : ℝ) * ∫ z in V, timeDerivative w z * qh z ^ 2)) := by
    exact tendsto_localized_timeEnergy_spacetimeMollification hVopen qh w hqh
      hwSmooth hwCompact hwV
  have hsourceLim : Filter.Tendsto (fun ε ↦ ∫ z in S, R z *
      spatialDifferenceQuotient k (-h) (f ε) z) l
      (nhds (∫ z in S, R z * spatialDifferenceQuotient k (-h) ψ z)) := by
    exact tendsto_sourcePairing_mollifiedBackwardQuotient S R ψ hR hψ k h
  have hfluxLim (i j : Fin d) : Filter.Tendsto (fun ε ↦
      ∫ z in V, spatialDifferenceQuotient k h
        (fun x ↦ A x i j * G j x) z * spacetimeMollification ε (Dψ i) z) l
      (nhds (∫ z in V, spatialDifferenceQuotient k h
        (fun x ↦ A x i j * G j x) z * Dψ i z)) := by
    have hentry : ParabolicMemLpOn V 2
        (spatialDifferenceQuotient k h (fun z ↦ A z i j * G j z)) :=
      (hFlux i j C hCcompact hCS).spatialDifferenceQuotient_of_subset_mapsTo
        k h hVC hVshift
    exact (StrongL2Limit.const hentry).pairing
      ((SpacetimeMollifierL2.spacetimeMollification_strongL2 (hDψ i)).restrict V)
  have heqEventually : ∀ᶠ ε in l,
      -(∫ z in V, qh z * timeDerivative (f ε) z) -
          ∑ i, ∑ j, ∫ z in V, spatialDifferenceQuotient k h
            (fun x ↦ A x i j * G j x) z *
              spacetimeMollification ε (Dψ i) z =
        -(∫ z in S, R z * spatialDifferenceQuotient k (-h) (f ε) z) := by
    filter_upwards [hevent] with ε hε
    have hp := htest ε hε.1 hε.2
    have he := testedEquation_neg_mollifiedBackwardQuotient A q R G hEq k h ε ψ
      hp.1 hp.2.1 hp.2.2.2.2.2.2
    have ht := setIntegral_mul_timeDerivative_spatialDifferenceQuotient_neg
      hS.measurableSet hVS q hq k h (f ε) hp.1 hp.2.1 hp.2.2.1
      (fun z hz ↦ hCS (hVshift hz))
    have hf (i j : Fin d) :=
      setIntegral_mul_velocityGradient_spatialDifferenceQuotient_neg
        hS.measurableSet hCcompact hCS hVC (fun z ↦ A z i j * G j z)
        (hFlux i j C hCcompact hCS) k h (f ε) hp.1 hp.2.1 hp.2.2.1
        hVshift i
    dsimp only [f] at ht hf ⊢
    simp_rw [ht, hf, hp.2.2.2.1, Finset.sum_neg_distrib] at he
    linarith only [he]
  have hleftLim : Filter.Tendsto (fun ε ↦
      -(∫ z in V, qh z * timeDerivative (f ε) z) -
        ∑ i, ∑ j, ∫ z in V, spatialDifferenceQuotient k h
          (fun x ↦ A x i j * G j x) z *
            spacetimeMollification ε (Dψ i) z) l
      (nhds (-((1 / 2 : ℝ) * ∫ z in V, timeDerivative w z * qh z ^ 2) -
        ∑ i, ∑ j, ∫ z in V, spatialDifferenceQuotient k h
          (fun x ↦ A x i j * G j x) z * Dψ i z)) := by
    exact htimeLim.neg.sub (tendsto_finset_sum _ fun i _ ↦
      tendsto_finset_sum _ fun j _ ↦
        hfluxLim i j)
  have hrightLim := hsourceLim.neg
  have hlimEq := tendsto_nhds_unique hleftLim (hrightLim.congr' (heqEventually.mono fun _ h => h.symm))
  have ht := setIntegral_mul_eq_of_tsupport_subset hS.measurableSet hVS
    (fun z => qh z ^ 2) _ ((timeDerivative_tsupport _).trans hwV)
  simp_rw [mul_comm (_ ^ 2) (timeDerivative _ _)] at ht
  rw [← ht] at hlimEq
  have hfluxEq (i : Fin d) :
      (∫ z in S, spatialDifferenceQuotient k h
          (fun x ↦ ∑ j, A x i j * G j x) z * Dψ i z) =
        ∑ j, ∫ z in V, spatialDifferenceQuotient k h
          (fun x ↦ A x i j * G j x) z * Dψ i z := by
    have hentryInt (j : Fin d) : IntegrableOn (fun z ↦
        spatialDifferenceQuotient k h (fun x ↦ A x i j * G j x) z *
          Dψ i z) V := by
      exact ((hFlux i j C hCcompact hCS).spatialDifferenceQuotient_of_subset_mapsTo
        k h hVC hVshift).integrable_mul
          ((hDψ i).mono_measure Measure.restrict_le_self)
    rw [setIntegral_mul_eq_of_tsupport_subset hS.measurableSet hVS _ _ (hDψSupport i),
      spatialDifferenceQuotient_finset_sum, ← integral_finset_sum _ (fun j _ => hentryInt j)]
    exact integral_congr_ae (ae_of_all _ fun z => by simp only [Finset.sum_mul, Dψ, qh])
  rw [show (∑ i, ∫ z in S, spatialDifferenceQuotient k h
      (fun x ↦ ∑ j, A x i j * G j x) z * Dψ i z) =
      ∑ i, ∑ j, ∫ z in V, spatialDifferenceQuotient k h
        (fun x ↦ A x i j * G j x) z * Dψ i z by
    exact Finset.sum_congr rfl (fun i _ ↦ hfluxEq i)]
  simp_rw [qh, Dψ] at hlimEq ⊢
  linarith

end HypoellipticAleksandrov.Parabolic
