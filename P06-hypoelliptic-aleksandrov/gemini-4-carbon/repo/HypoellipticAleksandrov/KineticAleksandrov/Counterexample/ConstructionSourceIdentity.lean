module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ExtensionContinuity
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoffGlobalJets
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.Order.Compact
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifyWeakCoordinates
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionLocalBounds
public import PDEFoundation.Sobolev.WeakDerivative.Product
public import PDEFoundation.Sobolev.WeakDerivative.Algebra
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionSecondBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeRegularityIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeRegularityCompact
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.SmoothFunctions
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.BarrierPackedJets

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Set MeasureTheory Filter HypoellipticAleksandrov.Parabolic
open scoped Topology Convolution



/-- The velocity cutoff is one on the profile domain and zero beyond the barrier radius. -/
def constructionVelocityCutoff {d : ℕ} (m R : ℝ) (q : XV d) : ℝ :=
  1 - Real.smoothTransition ((PDE.vecNormSq q.2 - m) / (R ^ 2 - m))


/-- The cutoff equals one below the inner squared-velocity threshold. -/
theorem constructionVelocityCutoff_eq_one {d : ℕ} (m R : ℝ) (hm : m < R ^ 2)
    (q : XV d) (hq : PDE.vecNormSq q.2 ≤ m) : constructionVelocityCutoff m R q = 1 := by
  unfold constructionVelocityCutoff
  rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr hq) (sub_pos.mpr hm).le), sub_zero]

/-- The cutoff is zero at and beyond the barrier radius. -/
theorem constructionVelocityCutoff_eq_zero {d : ℕ} (m R : ℝ) (hm : m < R ^ 2)
    (q : XV d) (hq : R ^ 2 ≤ PDE.vecNormSq q.2) : constructionVelocityCutoff m R q = 0 := by
  unfold constructionVelocityCutoff
  rw [Real.smoothTransition.one_of_one_le
    ((le_div_iff₀ (sub_pos.mpr hm)).mpr (by simpa using sub_le_sub_right hq m)),
    sub_self]

/-- Multiplying the raw cutoff by the smooth velocity cutoff is exactly the zero extension.
This equality holds at every time, including the initial zero interval. -/
theorem construction_zero_extension_eq_cutoff {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R m : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2)
    (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 ≤ m)
    (P : KineticPoint d) :
    zeroExtendedProfile (profileFunction h) alpha r mu R P =
      constructionVelocityCutoff m R (P.position, P.velocity) *
        timeCutoffProfile (profileFunction h) alpha r mu R P := by
  have hvel : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < R ^ 2 :=
    fun q hq => (hmargin q hq).trans_lt hm
  by_cases hq : profileFunction h (P.position, P.velocity) < 1
  · rw [constructionVelocityCutoff_eq_one m R hm _ (hmargin _ hq.le), one_mul]
    exact zeroExtendedProfile_eq_raw_on_profile _ alpha r mu R hr hmu hR hvel P hq
  · rw [zeroExtendedProfile_eq_zero_of_profile _ alpha r mu R P (not_lt.mp hq)]
    by_cases hc : constructionVelocityCutoff m R (P.position, P.velocity) = 0
    · rw [hc, zero_mul]
    · have hv : PDE.vecNormSq P.velocity < R ^ 2 := by
        by_contra hn
        exact hc (constructionVelocityCutoff_eq_zero m R hm _ (not_lt.mp hn))
      have hb : 0 < barrier mu R P := by
        unfold barrier
        exact mul_pos (Real.exp_pos _) (by
          have hh := (div_lt_one (sq_pos_of_pos hR)).mpr hv
          linarith)
      have hu : timeCutoffProfile (profileFunction h) alpha r mu R P = 0 := by
        unfold timeCutoffProfile
        rw [(flatProfile_eq_one_sub (profileFunction h) alpha r hr (P.position, P.velocity) (hscale.trans (not_lt.mp hq)))]
        apply timeCutoffTheta_eq_zero
        linarith [not_lt.mp hq]
      rw [hu, mul_zero]


/-- A packed weak directional derivative transfers back to the native spatial carrier.
The measure-preserving chart introduces no Jacobian factor. -/
theorem construction_weak_directional_native {d : ℕ}
    (u g : PDE.Vec (d + d) → ℝ) (z : PDE.Vec (d + d))
    (hweak : ∀ test : PDE.Vec (d + d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) test →
      HasCompactSupport test →
      (∫ x, u x * fderiv ℝ test x z) = -(∫ x, g x * test x))
    (test : XV d → ℝ) (ht : ContDiff ℝ (⊤ : ℕ∞) test)
    (hs : HasCompactSupport test) :
    (∫ q, u ((spatialCoordinateCLE d).symm q) *
      fderiv ℝ test q (spatialCoordinateCLE d z)) =
      -(∫ q, g ((spatialCoordinateCLE d).symm q) * test q) := by
  let e := spatialCoordinateCLE d
  let psi := test ∘ e
  have hd : ∀ x, fderiv ℝ psi x z = fderiv ℝ test (e x) (e z) := by
    intro x
    rw [((ht.differentiable (by simp) (e x)).hasFDerivAt.comp x e.hasFDerivAt).fderiv]
    rfl
  have hLn : (∫ x, u x * fderiv ℝ psi x z) =
      ∫ q, u (e.symm q) * fderiv ℝ test q (e z) := by
    simpa only [spatialCoordinateMeasurableEquiv_apply,
      hd, e, ContinuousLinearEquiv.symm_apply_apply] using! (measurePreserving_spatialCoordinate d).integral_comp' (fun q => u (e.symm q) * fderiv ℝ test q (e z))
  have hRn : (∫ x, g x * psi x) = ∫ q, g (e.symm q) * test q := by
    simpa [spatialCoordinateMeasurableEquiv_apply, psi, e, ContinuousLinearEquiv.symm_apply_apply] using! (measurePreserving_spatialCoordinate d).integral_comp' (fun q => g (e.symm q) * test q)
  exact hLn.symm.trans ((hweak psi (ht.comp e.contDiff) (hs.comp_homeomorph e.toHomeomorph)).trans (congrArg Neg.neg hRn))

/-- Local integrability transfers to the native carrier through the same chart. -/
theorem construction_locallyIntegrable_native {d : ℕ} (f : PDE.Vec (d + d) → ℝ)
    (hf : LocallyIntegrable f volume) :
    LocallyIntegrable (fun q => f ((spatialCoordinateCLE d).symm q)) volume := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  have hK' :=
    hK.image (spatialCoordinateCLE d).symm.continuous
  have hm := (measurePreserving_spatialCoordinate d).symm.restrict_image_emb
    (spatialCoordinateMeasurableEquiv d).symm.measurableEmbedding K
  have he := hm.integrable_comp_of_integrable (hf.integrableOn_isCompact hK')
  simpa using! he

/-- Almost-everywhere statements transfer to the native carrier without exceptional mass. -/
theorem construction_ae_native {d : ℕ} (prop : PDE.Vec (d + d) → Prop)
    (hp : ∀ᵐ x ∂volume, prop x) :
    ∀ᵐ q ∂volume, prop ((spatialCoordinateCLE d).symm q) :=
  (measurePreserving_spatialCoordinate d).symm.quasiMeasurePreserving.ae hp


/-- The smooth velocity cutoff in packed coordinates. -/
def constructionPackedCutoff (d : ℕ) (m R : ℝ) (x : PDE.Vec (d + d)) : ℝ :=
  constructionVelocityCutoff m R (spatialCoordinateCLE d x)

/-- The selected first weak derivative of the actual extended profile. -/
def constructionExtendedPackedGradient {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R m t : ℝ)
    (x : PDE.Vec (d + d)) (i : Fin (d + d)) : ℝ :=
  constructionPackedCutoff d m R x * spatialPackedCutoffGradient h r mu R t x i +
    spatialPackedCutoffValue h r mu R t x *
      fderiv ℝ (constructionPackedCutoff d m R) x (PDE.basisVec i)

/-- The packed multiplier is smooth at every finite order. -/
theorem contDiff_providerPackedCutoff (d : ℕ) (m R : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (constructionPackedCutoff d m R)  := by
  have contDiff_providerVelocityCutoff :
      ContDiff ℝ (⊤ : ℕ∞) (constructionVelocityCutoff (d := d) m R) := by
    exact contDiff_const.sub (Real.smoothTransition.contDiff.comp
      (((PDE.contDiff_vecNormSq.comp contDiff_snd).sub contDiff_const).div_const _))
  exact (contDiff_providerVelocityCutoff).comp (spatialCoordinateCLE d).contDiff

/-- The exact zero extension satisfies the first compact-test identities globally. -/
theorem construction_zero_extension_weak_first {d : ℕ} (hd : 1 ≤ d)
    {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r mu R m : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2)
    (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 ≤ m)
    (t : ℝ) (i : Fin (d + d)) (test : PDE.Vec (d + d) → ℝ)
    (ht : ContDiff ℝ (⊤ : ℕ∞) test) (hs : HasCompactSupport test) :
    (∫ x, zeroExtendedProfile (profileFunction h) alpha r mu R
        ⟨t, (spatialCoordinateCLE d x).1, (spatialCoordinateCLE d x).2⟩ *
      fderiv ℝ test x (PDE.basisVec i)) =
      -(∫ x, constructionExtendedPackedGradient h r mu R m t x i * test x) := by
  have hu : LocallyIntegrable (spatialPackedCutoffValue h r mu R t)
      (PDE.volumeOn univ) := by
    simpa using
      (construction_cutoffValue_continuous h r mu R t).locallyIntegrable
  have hg : LocallyIntegrable (fun x => spatialPackedCutoffGradient h r mu R t x i)
      (PDE.volumeOn univ) := by
    simpa using
      construction_cutoffGradient_locallyIntegrable h r hr mu R t i
  have he := (weakPartial_on_of_global univ i (spatialPackedCutoffValue h r mu R t) (fun x => spatialPackedCutoffGradient h r mu R t x i) (spatialPackedCutoff_weak_first_of_profile hd ha ha1 h r hr mu R t i)).mul_contDiff (contDiff_providerPackedCutoff d m R) hu hg
    test ht hs (subset_univ _)
  have hz : ∀ x : PDE.Vec (d + d),
      zeroExtendedProfile (profileFunction h) alpha r mu R
        ⟨t, (spatialCoordinateCLE d x).1, (spatialCoordinateCLE d x).2⟩ =
      constructionPackedCutoff d m R x * spatialPackedCutoffValue h r mu R t x := by
    intro x
    exact construction_zero_extension_eq_cutoff h r mu R m hr hmu hR hm hscale hmargin _
  simpa only [Measure.restrict_univ, constructionExtendedPackedGradient, ← hz] using! he

/-- The same selected representatives satisfy the first identities on the native carrier. -/
theorem construction_zero_extension_weak_native {d : ℕ} (hd : 1 ≤ d)
    {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r mu R m : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2)
    (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 ≤ m)
    (t : ℝ) (i : Fin (d + d)) (test : XV d → ℝ)
    (ht : ContDiff ℝ (⊤ : ℕ∞) test) (hs : HasCompactSupport test) :
    (∫ q, zeroExtendedProfile (profileFunction h) alpha r mu R ⟨t, q.1, q.2⟩ *
      fderiv ℝ test q (spatialCoordinateCLE d (PDE.basisVec i))) =
      -(∫ q, constructionExtendedPackedGradient h r mu R m t
        ((spatialCoordinateCLE d).symm q) i * test q) := by
  simpa using! (construction_weak_directional_native (fun x => zeroExtendedProfile (profileFunction h) alpha r mu R ⟨t, (spatialCoordinateCLE d x).1, (spatialCoordinateCLE d x).2⟩) (fun x => constructionExtendedPackedGradient h r mu R m t x i) (PDE.basisVec i) (construction_zero_extension_weak_first hd ha ha1 h r mu R m hr hmu hR hm hscale hmargin t i) test ht hs)


/-- Multiplication by a smooth function preserves a prescribed second weak derivative.
The two first representatives are the ones appearing in both weak identities. -/
theorem construction_weak_second_product {n : ℕ} {D : Set (PDE.Vec n)}
    (u gi gk hik phi : PDE.Vec n → ℝ) (i k : Fin n)
    (hu : PDE.HasWeakPartialDerivOn D i u gi)
    (hg : PDE.HasWeakPartialDerivOn D i gk hik)
    (hphi : ContDiff ℝ (⊤ : ℕ∞) phi)
    (huL : LocallyIntegrable u (PDE.volumeOn D))
    (hgiL : LocallyIntegrable gi (PDE.volumeOn D))
    (hgkL : LocallyIntegrable gk (PDE.volumeOn D))
    (hhL : LocallyIntegrable hik (PDE.volumeOn D)) :
    PDE.HasWeakPartialDerivOn D i
      (fun x => phi x * gk x + u x * fderiv ℝ phi x (PDE.basisVec k))
      (fun x => phi x * hik x + gk x * fderiv ℝ phi x (PDE.basisVec i) +
        fderiv ℝ phi x (PDE.basisVec k) * gi x +
        u x * fderiv ℝ (fun y => fderiv ℝ phi y (PDE.basisVec k)) x
          (PDE.basisVec i)) := by
  let dk := fun x => fderiv ℝ phi x (PDE.basisVec k)
  let di := fun x => fderiv ℝ phi x (PDE.basisVec i)
  have hdk : ContDiff ℝ (⊤ : ℕ∞) dk :=
    (hphi.contDiff_fderiv_apply (by simp)).comp (contDiff_id.prodMk contDiff_const)
  have hdi : Continuous di :=
    (hphi.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdik : Continuous (fun x => fderiv ℝ dk x (PDE.basisVec i)) :=
    (hdk.continuous_fderiv (by simp)).clm_apply continuous_const
  have hD1L :=
    (hhL.continuous_mul hphi.continuous).add (hgkL.mul_continuous hdi)
  have hD2L :=
    (hgiL.continuous_mul hdk.continuous).add (huL.mul_continuous hdik)
  have he := (hg.mul_contDiff hphi hgkL hhL).add (hu.mul_contDiff hdk huL hgiL) (hgkL.continuous_mul hphi.continuous) (huL.continuous_mul hdk.continuous) hD1L hD2L
  have hv : (fun x => phi x * gk x + dk x * u x) =
      (fun x => phi x * gk x + u x * fderiv ℝ phi x (PDE.basisVec k)) := by
    funext x
    dsimp only [dk]
    rw [mul_comm (fderiv ℝ phi x (PDE.basisVec k))]
  change PDE.HasWeakPartialDerivOn D i
    (fun x => phi x * gk x + dk x * u x)
    (fun x => (phi x * hik x + gk x * di x) +
      (dk x * gi x + u x * fderiv ℝ dk x (PDE.basisVec i))) at he
  rw [hv] at he
  simpa only [dk, di, add_assoc] using! he


/-- The literal second representative obtained by differentiating the selected first jet. -/
def constructionExtendedPackedHessian {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R m t : ℝ)
    (x : PDE.Vec (d + d)) (i k : Fin d) : ℝ :=
  constructionPackedCutoff d m R x * spatialPackedCutoffVelocityHessian h r mu R t x i k +
    spatialPackedCutoffGradient h r mu R t x (Fin.natAdd d k) *
      fderiv ℝ (constructionPackedCutoff d m R) x (PDE.basisVec (Fin.natAdd d i)) +
    fderiv ℝ (constructionPackedCutoff d m R) x (PDE.basisVec (Fin.natAdd d k)) *
      spatialPackedCutoffGradient h r mu R t x (Fin.natAdd d i) +
    spatialPackedCutoffValue h r mu R t x *
      fderiv ℝ (fun y => fderiv ℝ (constructionPackedCutoff d m R) y
        (PDE.basisVec (Fin.natAdd d k))) x (PDE.basisVec (Fin.natAdd d i))

/-- The selected extended first jets are locally integrable. -/
theorem construction_extendedGradient_locallyIntegrable {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    (mu R m t : ℝ) (i : Fin (d + d)) :
    LocallyIntegrable (fun x => constructionExtendedPackedGradient h r mu R m t x i)
      volume := by
  have hc := contDiff_providerPackedCutoff d m R
  have hd : Continuous (fun x => fderiv ℝ (constructionPackedCutoff d m R) x
      (PDE.basisVec i)) :=
    (hc.continuous_fderiv (by simp)).clm_apply continuous_const
  exact ((construction_cutoffGradient_locallyIntegrable h r hr mu R t i).continuous_mul
    hc.continuous).add ((construction_cutoffValue_continuous h r mu R t).locallyIntegrable
      |>.mul_continuous hd)

/-- The selected extended Hessian components are locally integrable. -/
theorem construction_extendedHessian_locallyIntegrable {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    (mu R m t : ℝ) (i k : Fin d) :
    LocallyIntegrable (fun x => constructionExtendedPackedHessian h r mu R m t x i k)
      volume := by
  have hc := contDiff_providerPackedCutoff d m R
  have hd (j : Fin d) : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => fderiv ℝ (constructionPackedCutoff d m R) x (PDE.basisVec (Fin.natAdd d j))) :=
    (hc.contDiff_fderiv_apply (by simp)).comp (contDiff_id.prodMk contDiff_const)
  have hdd : Continuous (fun x => fderiv ℝ
      (fun y => fderiv ℝ (constructionPackedCutoff d m R) y
        (PDE.basisVec (Fin.natAdd d k))) x (PDE.basisVec (Fin.natAdd d i))) :=
    ((hd k).continuous_fderiv (by simp)).clm_apply continuous_const
  exact ((((construction_cutoffHessian_locallyIntegrable h r hr mu R t i k).continuous_mul
    hc.continuous).add ((construction_cutoffGradient_locallyIntegrable h r hr mu R t
      (Fin.natAdd d k)).mul_continuous (hd i).continuous)).add
        ((construction_cutoffGradient_locallyIntegrable h r hr mu R t
          (Fin.natAdd d i)).continuous_mul (hd k).continuous)).add
            ((construction_cutoffValue_continuous h r mu R t).locallyIntegrable
              |>.mul_continuous hdd)

/-- The extended first velocity jet has precisely the selected second weak derivative. -/
theorem construction_extended_velocityJet_weak {d : ℕ} (hd : 1 ≤ d)
    {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    (mu R m t : ℝ) (i k : Fin d) (test : PDE.Vec (d + d) → ℝ)
    (ht : ContDiff ℝ (⊤ : ℕ∞) test) (hs : HasCompactSupport test) :
    (∫ x, constructionExtendedPackedGradient h r mu R m t x (Fin.natAdd d k) *
      fderiv ℝ test x (PDE.basisVec (Fin.natAdd d i))) =
      -(∫ x, constructionExtendedPackedHessian h r mu R m t x i k * test x) := by
  have hu := weakPartial_on_of_global univ (Fin.natAdd d i)
    (spatialPackedCutoffValue h r mu R t)
    (fun x => spatialPackedCutoffGradient h r mu R t x (Fin.natAdd d i))
    (spatialPackedCutoff_weak_first_of_profile hd ha ha1 h r hr mu R t (Fin.natAdd d i))
  have hg := weakPartial_on_of_global univ (Fin.natAdd d i)
    (fun x => spatialPackedCutoffGradient h r mu R t x (Fin.natAdd d k))
    (fun x => spatialPackedCutoffVelocityHessian h r mu R t x i k)
    (spatialPackedCutoff_velocityJet_weak_of_profile hd ha ha1 h r hr mu R t i k)
  have huL : LocallyIntegrable (spatialPackedCutoffValue h r mu R t)
      (PDE.volumeOn univ) := by
    simpa using
      (construction_cutoffValue_continuous h r mu R t).locallyIntegrable
  have hgiL : LocallyIntegrable
      (fun x => spatialPackedCutoffGradient h r mu R t x (Fin.natAdd d i))
      (PDE.volumeOn univ) := by
    simpa using
      construction_cutoffGradient_locallyIntegrable h r hr mu R t (Fin.natAdd d i)
  have hgkL : LocallyIntegrable
      (fun x => spatialPackedCutoffGradient h r mu R t x (Fin.natAdd d k))
      (PDE.volumeOn univ) := by
    simpa using
      construction_cutoffGradient_locallyIntegrable h r hr mu R t (Fin.natAdd d k)
  have hhL : LocallyIntegrable
      (fun x => spatialPackedCutoffVelocityHessian h r mu R t x i k)
      (PDE.volumeOn univ) := by
    simpa using
      construction_cutoffHessian_locallyIntegrable h r hr mu R t i k
  have he := construction_weak_second_product _ _ _ _ (constructionPackedCutoff d m R)
    (Fin.natAdd d i) (Fin.natAdd d k) hu hg (contDiff_providerPackedCutoff d m R)
    huL hgiL hgkL hhL test ht hs (subset_univ _)
  simpa only [Measure.restrict_univ, constructionExtendedPackedGradient,
    constructionExtendedPackedHessian] using! he


/-- Differentiation commutes with the compact integral of a smooth formula whose internal
parameter is merely continuous. This identifies the derivative, beyond joint smoothness. -/
theorem construction_deriv_compact_parameter {Y A : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [TopologicalSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A]
    (mu : Measure A) [IsFiniteMeasure mu] (radius : A → Y) (hr : Continuous radius)
    (f : ℝ × Y → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) :
    deriv (fun s => ∫ a, f (s, radius a) ∂mu) t =
      ∫ a, deriv (fun s => f (s, radius a)) t ∂mu := by
  let L : ℝ →L[ℝ] ℝ × Y := (ContinuousLinearMap.id ℝ ℝ).prod 0
  let J :=
    (ContinuousLinearMap.compL ℝ ℝ (ℝ × Y) ℝ).flip L
  let g : ℝ × Y → ℝ →L[ℝ] ℝ := fun w => J (fderiv ℝ f w)
  have hg :=
    J.continuous.comp (hf.continuous_fderiv (by simp))
  have hd (s : ℝ) (a : A) : HasFDerivAt (fun x => f (x, radius a))
      (g (s, radius a)) s :=
    (hf.differentiable (by simp) (s, radius a)).hasFDerivAt.comp s
      ((hasFDerivAt_id s).prodMk (hasFDerivAt_const (radius a) s))
  have hfc :=
    hf.continuous.comp (continuous_fst.prodMk (hr.comp continuous_snd))
  have hgc :=
    hg.comp (continuous_fst.prodMk (hr.comp continuous_snd))
  have he := bellman_compact_parameter_hasFDerivAt mu isOpen_univ
    (fun s a => f (s, radius a)) (fun s a => g (s, radius a))
    hfc.continuousOn hgc.continuousOn (fun s _ a => hd s a) (mem_univ t)
  have hi :=
    bellman_compact_parameter_integrable mu (f := fun s a => g (s, radius a))
      hgc.continuousOn (mem_univ t)
  rw [he.hasDerivAt.deriv, ContinuousLinearMap.integral_apply hi]
  apply integral_congr_ae
  filter_upwards [] with a
  exact (hd t a).hasDerivAt.deriv.symm


/-- A locally integrable weak derivative vanishes on every open region where the value
vanishes almost everywhere. The derivative representative is preserved by uniqueness. -/
theorem construction_weak_derivative_zero_on_open {n : ℕ} (D : Set (PDE.Vec n))
    (hD : IsOpen D) (i : Fin n) (u g : PDE.Vec n → ℝ)
    (hg : LocallyIntegrable g volume)
    (hu : u =ᵐ[volume.restrict D] 0)
    (hw : PDE.HasWeakPartialDerivOn D i u g) :
    g =ᵐ[volume.restrict D] 0 := by
  have hz : PDE.HasWeakPartialDerivOn D i u 0 := by
    intro test _ht _hs _hsub
    have he : (∫ x in D, u x * fderiv ℝ test x (PDE.basisVec i)) = 0 := by
      calc
        _ = ∫ x in D, (0 : ℝ) := by
          apply integral_congr_ae
          filter_upwards [hu] with x hx
          simp at hx
          rw [hx, zero_mul]
        _ = 0 := by simp only [integral_zero]
    simpa [integral_zero] using he
  exact PDE.HasWeakPartialDerivOn.ae_eq hD (hg.locallyIntegrableOn D)
    (continuous_const.locallyIntegrable.locallyIntegrableOn D) hw hz


/-- The selected first and second weak representatives vanish almost everywhere outside
`H < 1`, including the profile boundary. An open zero collar avoids any level-set premise. -/
theorem construction_extended_jets_zero_outside_profile {d : ℕ} (hd : 1 ≤ d)
    {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r mu R m : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2)
    (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 ≤ m) (t : ℝ) :
    ∀ᵐ x ∂volume, 1 ≤ profileFunction h (spatialCoordinateCLE d x) →
      (∀ i, constructionExtendedPackedGradient h r mu R m t x i = 0) ∧
      (∀ i k, constructionExtendedPackedHessian h r mu R m t x i k = 0) := by
  let s := fun x => selectedFlatProfile h r (spatialCoordinateCLE d x) -
    spatialPackedBarrier d mu R t x
  let D : Set (PDE.Vec (d + d)) := {x | s x < 0} ∪
    {x | R ^ 2 < PDE.vecNormSq (spatialCoordinateCLE d x).2}
  let u := fun x => zeroExtendedProfile (profileFunction h) alpha r mu R
    ⟨t, (spatialCoordinateCLE d x).1, (spatialCoordinateCLE d x).2⟩
  have hD : IsOpen D :=
    (isOpen_lt (((continuous_selectedFlatProfile h r).comp
      (spatialCoordinateCLE d).continuous).sub
        (contDiff_spatialPackedBarrier d mu R t).continuous) continuous_const).union
      (isOpen_lt continuous_const (PDE.contDiff_vecNormSq.continuous.comp
        (spatialCoordinateCLE d).continuous.snd))
  have hu : u =ᵐ[volume.restrict D] 0 := by
    filter_upwards [ae_restrict_mem hD.measurableSet] with x hx
    change zeroExtendedProfile (profileFunction h) alpha r mu R
      ⟨t, (spatialCoordinateCLE d x).1, (spatialCoordinateCLE d x).2⟩ = 0
    rw [construction_zero_extension_eq_cutoff h r mu R m hr hmu hR hm hscale hmargin]
    rcases hx with hs | hv
    · change constructionVelocityCutoff m R (spatialCoordinateCLE d x) * timeCutoffTheta (s x) = 0
      rw [timeCutoffTheta_eq_zero _ hs.le, mul_zero]
    · rw [constructionVelocityCutoff_eq_zero m R hm _ hv.le, zero_mul]
  have hsub : ∀ x, 1 ≤ profileFunction h (spatialCoordinateCLE d x) → x ∈ D := by
    intro x hx
    by_cases hv : PDE.vecNormSq (spatialCoordinateCLE d x).2 ≤ R ^ 2
    · left
      have hf := flatProfile_eq_one_sub (profileFunction h) alpha r hr
        (spatialCoordinateCLE d x) (hscale.trans hx)
      have hb : 0 < spatialPackedBarrier d mu R t x := by
        unfold spatialPackedBarrier barrier
        have he := (div_le_one (sq_pos_of_pos hR)).mpr hv
        exact mul_pos (Real.exp_pos _) (by linarith only [he])
      change selectedFlatProfile h r (spatialCoordinateCLE d x) -
        spatialPackedBarrier d mu R t x < 0
      change flatProfile (profileFunction h) flatteningPsi flatteningOffset alpha r
        (spatialCoordinateCLE d x) - _ < 0
      rw [hf]
      linarith only [hx, hb]
    · exact Or.inr (lt_of_not_ge hv)
  have hg (i : Fin (d + d)) :
      (fun x => constructionExtendedPackedGradient h r mu R m t x i) =ᵐ[volume.restrict D] 0 := by
    apply construction_weak_derivative_zero_on_open D hD i u _
      (construction_extendedGradient_locallyIntegrable h r hr mu R m t i) hu
    exact weakPartial_on_of_global D i u _
      (construction_zero_extension_weak_first hd ha ha1 h r mu R m hr hmu hR hm
        hscale hmargin t i)
  have hh (i k : Fin d) :
      (fun x => constructionExtendedPackedHessian h r mu R m t x i k) =ᵐ[volume.restrict D] 0 := by
    apply construction_weak_derivative_zero_on_open D hD (Fin.natAdd d i) _ _
      (construction_extendedHessian_locallyIntegrable h r hr mu R m t i k)
      (hg (Fin.natAdd d k))
    exact weakPartial_on_of_global D (Fin.natAdd d i) _ _
      (construction_extended_velocityJet_weak hd ha ha1 h r hr mu R m t i k)
  have hga := ae_all_iff.mpr hg
  have hha := ae_all_iff.mpr (fun i => ae_all_iff.mpr (hh i))
  have hga' := (ae_restrict_iff' hD.measurableSet).mp hga
  have hha' := (ae_restrict_iff' hD.measurableSet).mp hha
  filter_upwards [hga', hha'] with x hx hy
  intro hprof
  exact ⟨hx (hsub x hprof), hy (hsub x hprof)⟩


/-- The selected first representative on the native carrier. -/
def constructionExtendedNativeGradient {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R m t : ℝ)
    (q : XV d) (i : Fin (d + d)) : ℝ :=
  constructionExtendedPackedGradient h r mu R m t ((spatialCoordinateCLE d).symm q) i

/-- The selected second velocity representative on the native carrier. -/
def constructionExtendedNativeHessian {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R m t : ℝ)
    (q : XV d) (i k : Fin d) : ℝ :=
  constructionExtendedPackedHessian h r mu R m t ((spatialCoordinateCLE d).symm q) i k

/-- Spatial convolution differentiates to convolution of the selected first representatives. -/
theorem construction_mollified_first_jet {d : ℕ} (hd : 1 ≤ d)
    {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r mu R m : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2)
    (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 ≤ m)
    (t : ℝ) (i : Fin (d + d)) (phi : ContDiffBump (0 : XV d)) (q : XV d) :
    fderiv ℝ (spatialMollify phi (fun y =>
      zeroExtendedProfile (profileFunction h) alpha r mu R ⟨t, y.1, y.2⟩)) q
        (spatialCoordinateCLE d (PDE.basisVec i)) =
      spatialMollify phi (fun y => constructionExtendedNativeGradient h r mu R m t y i) q := by
  have hc := continuous_zeroExtendedProfile_spatial_of_profile h r mu R hr hmu hR hscale
    (fun y hy => (hmargin y hy).trans_lt hm) t
  exact mollify_weak_directional_jet phi _ _ hc.locallyIntegrable _
    (construction_zero_extension_weak_native hd ha ha1 h r mu R m hr hmu hR hm
      hscale hmargin t i) q


/-- The actual second velocity derivatives of the mollified value use the same Hessian. -/
theorem construction_mollified_second_velocity_jet {d : ℕ} (hd : 1 ≤ d)
    {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r mu R m : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2)
    (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 ≤ m)
    (t : ℝ) (i k : Fin d) (phi : ContDiffBump (0 : XV d)) (q : XV d) :
    dvv (spatialMollify phi (fun y =>
      zeroExtendedProfile (profileFunction h) alpha r mu R ⟨t, y.1, y.2⟩)) q i k =
      spatialMollify phi (fun y => constructionExtendedNativeHessian h r mu R m t y i k) q  := by
  have construction_mollified_velocityJet_derivative :
      fderiv ℝ (spatialMollify phi (fun y =>
      constructionExtendedNativeGradient h r mu R m t y (Fin.natAdd d k))) q
      (0, PDE.basisVec i) =
      spatialMollify phi (fun y => constructionExtendedNativeHessian h r mu R m t y i k) q := by
    have hL := construction_locallyIntegrable_native _
      (construction_extendedGradient_locallyIntegrable h r hr mu R m t (Fin.natAdd d k))
    apply mollify_weak_directional_jet phi _ _ hL _ _ q
    intro test ht hs
    have he := construction_weak_directional_native
      (fun x => constructionExtendedPackedGradient h r mu R m t x (Fin.natAdd d k))
      (fun x => constructionExtendedPackedHessian h r mu R m t x i k)
      (PDE.basisVec (Fin.natAdd d i))
      (construction_extended_velocityJet_weak hd ha ha1 h r hr mu R m t i k) test ht hs
    simpa only [spatialCoordinate_basis_velocity, constructionExtendedNativeGradient,
      constructionExtendedNativeHessian] using! he
  have he : (fun y => dv (spatialMollify phi (fun z =>
      zeroExtendedProfile (profileFunction h) alpha r mu R ⟨t, z.1, z.2⟩)) y k) =
      spatialMollify phi (fun y => constructionExtendedNativeGradient h r mu R m t y
        (Fin.natAdd d k)) := by
    funext y
    have hj := construction_mollified_first_jet hd ha ha1 h r mu R m hr hmu hR hm
      hscale hmargin t (Fin.natAdd d k) phi y
    rw [spatialCoordinate_basis_velocity] at hj
    simpa only [dv, PDE.basisVec] using! hj
  change fderiv ℝ (fun y => dv (spatialMollify phi (fun z =>
    zeroExtendedProfile (profileFunction h) alpha r mu R ⟨t, z.1, z.2⟩)) y k) q
      (0, PDE.basisVec i) = _
  rw [he]
  exact construction_mollified_velocityJet_derivative


/-- The concrete normalized kernels recover every locally integrable native scalar field. -/
theorem construction_spatialMollify_tendsto_ae {d : ℕ} (f : XV d → ℝ)
    (hf : LocallyIntegrable f volume) :
    ∀ᵐ q ∂volume, Tendsto
      (fun n => spatialMollify (standardMollifierSequence n) f q) atTop (𝓝 (f q)) := by
  exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    standardMollifierSequence_rOut_tendsto
    (Eventually.of_forall standardMollifierSequence_radius_ratio) hf



/-- Differentiating in time acts only on the cutoff, and commutes with its compact integral. -/
theorem construction_deriv_cutoff_integral {d : ℕ} {A : Type*}
    [TopologicalSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A]
    (nu : Measure A) [IsFiniteMeasure nu]
    (y : A → XV d) (hy : Continuous y) (u : A → ℝ) (hu : Continuous u)
    (phi : ContDiffBump (0 : XV d)) (mu R t : ℝ) (q : XV d) :
    deriv (fun s => ∫ a, phi.normed volume (q - y a) * timeCutoffTheta
      (u a - Real.exp (-mu * s) * (2 - PDE.vecNormSq (y a).2 / R ^ 2)) ∂nu) t =
    ∫ a, phi.normed volume (q - y a) *
      deriv (fun s => timeCutoffTheta
        (u a - Real.exp (-mu * s) * (2 - PDE.vecNormSq (y a).2 / R ^ 2))) t ∂nu := by
  let f : ℝ × (XV d × ℝ) → ℝ := fun z =>
    phi.normed volume (q - z.2.1) * timeCutoffTheta
      (z.2.2 - Real.exp (-mu * z.1) * (2 - PDE.vecNormSq z.2.1.2 / R ^ 2))
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    (phi.contDiff_normed.comp (contDiff_const.sub contDiff_snd.fst)).mul
      (contDiff_timeCutoffTheta.comp (contDiff_snd.snd.sub
        ((Real.contDiff_exp.comp (contDiff_const.mul contDiff_fst)).mul
          (contDiff_const.sub
            ((PDE.contDiff_vecNormSq.comp contDiff_snd.fst.snd).div_const (R ^ 2))))))
  have he := construction_deriv_compact_parameter nu (fun a => (y a, u a)) (hy.prodMk hu)
    f hf t
  change deriv (fun s => ∫ a, f (s, (y a, u a)) ∂nu) t = _
  rw [he]
  apply integral_congr_ae
  filter_upwards [] with a
  have hs : DifferentiableAt ℝ (fun s => timeCutoffTheta
      (u a - Real.exp (-mu * s) * (2 - PDE.vecNormSq (y a).2 / R ^ 2))) t := by
    have hb := (((hasDerivAt_id t).const_mul (-mu)).exp).mul_const
      (2 - PDE.vecNormSq (y a).2 / R ^ 2)
    exact (contDiff_timeCutoffTheta.differentiable (by simp)).differentiableAt.comp t
      (hb.const_sub (u a)).differentiableAt
  exact (hs.hasDerivAt.const_mul (phi.normed volume (q - y a))).deriv


/-- The time representative is the literal raw time derivative inside the profile domain. -/
def constructionExtendedTimeJet {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R t : ℝ) (q : XV d) : ℝ :=
  {y | profileFunction h y < 1}.indicator
    (fun y => kineticTimeDerivative (timeCutoffProfile (profileFunction h) alpha r mu R)
      ⟨t, y.1, y.2⟩) q

/-- The actual time derivative of the mollified value is convolution of its time representative.
The fixed compact integration carrier includes the initial collar, so this holds at all times. -/
theorem construction_mollified_time_jet {d : ℕ} {alpha : ℝ}
    (ha : 0 < alpha) (h : CounterProfileStatement d alpha) (r mu R : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R)
    (hvel : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < R ^ 2)
    (phi : ContDiffBump (0 : XV d)) (t : ℝ) (q : XV d) :
    deriv (fun s => spatialMollify phi
      (fun y => zeroExtendedProfile (profileFunction h) alpha r mu R ⟨s, y.1, y.2⟩) q) t =
      spatialMollify phi (constructionExtendedTimeJet h r mu R t) q := by
  let K : Set (XV d) := {y | profileFunction h y ≤ 1}
  let Omega : Set (XV d) := {y | profileFunction h y < 1}
  have hK := isCompact_profile_unit_sublevel ha h
  have hH := (selectedProfile_spec h).2.2.2.2.2.2.1
  have hOmega : MeasurableSet Omega := (isOpen_lt hH continuous_const).measurableSet
  have hOK : Omega ⊆ K := by
    intro y hy
    change profileFunction h y ≤ 1
    exact le_of_lt hy
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let nu : Measure K := Measure.comap Subtype.val (volume.restrict Omega)
  have : IsFiniteMeasureOnCompacts nu := IsFiniteMeasureOnCompacts.comap'
    (volume.restrict Omega) continuous_subtype_val
    (MeasurableEmbedding.subtype_coe hK.measurableSet)
  have : IsFiniteMeasure nu := inferInstance
  have he : (fun s => spatialMollify phi
      (fun y => zeroExtendedProfile (profileFunction h) alpha r mu R ⟨s, y.1, y.2⟩) q) =
      (fun s => ∫ y : K, phi.normed volume (q - y) * timeCutoffTheta
        (selectedFlatProfile h r y - Real.exp (-mu * s) *
          (2 - PDE.vecNormSq (y : XV d).2 / R ^ 2)) ∂nu) := by
    funext s
    rw [spatialMollify, convolution_lsmul_swap]
    simp only [smul_eq_mul]
    dsimp only [nu]
    rw [integral_subtype_comap hK.measurableSet (fun y =>
      phi.normed volume (q - y) * timeCutoffTheta
        (selectedFlatProfile h r y - Real.exp (-mu * s) *
          (2 - PDE.vecNormSq y.2 / R ^ 2)))]
    rw [Measure.restrict_restrict hK.measurableSet, inter_eq_right.mpr hOK]
    rw [← integral_indicator hOmega]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ Omega
    · rw [indicator_of_mem hy,
        zeroExtendedProfile_eq_raw_on_profile _ alpha r mu R hr hmu hR hvel ⟨s, y.1, y.2⟩ hy]
      rfl
    · rw [indicator_of_notMem hy,
        zeroExtendedProfile_eq_zero_of_profile _ alpha r mu R ⟨s, y.1, y.2⟩ (not_lt.mp hy),
        mul_zero]
  rw [he, construction_deriv_cutoff_integral nu (fun y => (y : XV d))
    continuous_subtype_val (fun y => selectedFlatProfile h r y)
    ((continuous_selectedFlatProfile h r).comp continuous_subtype_val)]
  dsimp only [nu]
  rw [integral_subtype_comap hK.measurableSet (fun y => phi.normed volume (q - y) *
    deriv (fun s => timeCutoffTheta (selectedFlatProfile h r y - Real.exp (-mu * s) *
      (2 - PDE.vecNormSq y.2 / R ^ 2))) t)]
  rw [Measure.restrict_restrict hK.measurableSet, inter_eq_right.mpr hOK]
  rw [← integral_indicator hOmega, spatialMollify, convolution_lsmul_swap]
  apply integral_congr_ae
  filter_upwards [] with y
  change Omega.indicator (fun y => phi.normed volume (q - y) *
    deriv (fun s => timeCutoffTheta (selectedFlatProfile h r y - Real.exp (-mu * s) *
      (2 - PDE.vecNormSq y.2 / R ^ 2))) t) y =
    phi.normed volume (q - y) * Omega.indicator
      (fun y => kineticTimeDerivative (timeCutoffProfile (profileFunction h) alpha r mu R)
        ⟨t, y.1, y.2⟩) y
  by_cases hy : y ∈ Omega
  · rw [indicator_of_mem hy, indicator_of_mem hy]
    rfl
  · rw [indicator_of_notMem hy, indicator_of_notMem hy, mul_zero]



/-- The time representative of the actual extension is locally integrable. -/
theorem construction_extendedTimeJet_locallyIntegrable {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R t : ℝ) :
    LocallyIntegrable (constructionExtendedTimeJet h r mu R t) volume  := by
  have construction_rawTimeJet_continuous :
      Continuous (fun q : XV d =>
      kineticTimeDerivative (timeCutoffProfile (profileFunction h) alpha r mu R)
        ⟨t, q.1, q.2⟩) := by
    simp_rw [timeCutoffProfile_timeDerivative, barrier_timeDerivative]
    have hs := ((continuous_selectedFlatProfile h r).sub
      (contDiff_nativeBarrier d mu R t).continuous)
    exact ((contDiff_timeCutoffTheta.continuous_deriv (by simp)).comp hs).neg.mul
      (continuous_const.mul (continuous_const.sub
        ((PDE.contDiff_vecNormSq.continuous.comp continuous_snd).div_const _)))
  have hH := (selectedProfile_spec h).2.2.2.2.2.2.1
  exact (construction_rawTimeJet_continuous).locallyIntegrable.indicator
    (isOpen_lt hH continuous_const).measurableSet


/-- The exact smoothed operator uses convolution of the same three selected weak jets.
Transport retains the velocity of the evaluation point; coefficients are not convolved. -/
theorem construction_smoothed_operator_eq {d : ℕ} (hd : 1 ≤ d)
    {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r mu R m : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2)
    (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 ≤ m)
    (phi : ContDiffBump (0 : XV d)) (A : XV d → PDE.Mat d) (P : KineticPoint d) :
    backwardOperator (fun _t x v => A (x, v)) (smoothedZeroExtendedProfile h r mu R phi) P =
      spatialMollify phi (constructionExtendedTimeJet h r mu R P.time) (P.position, P.velocity) +
      PDE.vecDot P.velocity (fun i => spatialMollify phi
        (fun y => constructionExtendedNativeGradient h r mu R m P.time y (Fin.castAdd d i))
          (P.position, P.velocity)) -
      matrixContraction (A (P.position, P.velocity)) (fun i k => spatialMollify phi
        (fun y => constructionExtendedNativeHessian h r mu R m P.time y i k)
          (P.position, P.velocity)) := by
  let f := spatialMollify phi (fun y =>
    zeroExtendedProfile (profileFunction h) alpha r mu R ⟨P.time, y.1, y.2⟩)
  have hc : ContDiff ℝ (⊤ : ℕ∞) f := spatialMollify_contDiff phi _
    (continuous_zeroExtendedProfile_spatial_of_profile h r mu R hr hmu hR hscale
      (fun y hy => (hmargin y hy).trans_lt hm) P.time).locallyIntegrable
  have hdt : kineticTimeDerivative (smoothedZeroExtendedProfile h r mu R phi) P =
      spatialMollify phi (constructionExtendedTimeJet h r mu R P.time)
        (P.position, P.velocity) :=
    construction_mollified_time_jet ha h r mu R hr hmu hR
      (fun y hy => (hmargin y hy).trans_lt hm) phi P.time (P.position, P.velocity)
  have hx : kineticPositionGradient (smoothedZeroExtendedProfile h r mu R phi) P =
      fun i => spatialMollify phi (fun y =>
        constructionExtendedNativeGradient h r mu R m P.time y (Fin.castAdd d i))
          (P.position, P.velocity) := by
    have he := dx_eq_classicalGradient_at f (P.position, P.velocity)
      (hc.differentiable (by simp)).differentiableAt
    change dx f (P.position, P.velocity) =
      kineticPositionGradient (smoothedZeroExtendedProfile h r mu R phi) P at he
    rw [← he]
    funext i
    have hj := construction_mollified_first_jet hd ha ha1 h r mu R m hr hmu hR hm
      hscale hmargin P.time (Fin.castAdd d i) phi (P.position, P.velocity)
    rw [spatialCoordinate_basis_position] at hj
    simpa only [dx, PDE.basisVec, f] using! hj
  have hh : kineticVelocityHessian (smoothedZeroExtendedProfile h r mu R phi) P =
      fun i k => spatialMollify phi (fun y =>
        constructionExtendedNativeHessian h r mu R m P.time y i k)
          (P.position, P.velocity) := by
    have he := dvv_eq_sliceHessian_at f (P.position, P.velocity)
      (hc.of_le (by simp)).contDiffAt
    change dvv f (P.position, P.velocity) =
      kineticVelocityHessian (smoothedZeroExtendedProfile h r mu R phi) P at he
    rw [← he]
    funext i k
    exact construction_mollified_second_velocity_jet hd ha ha1 h r mu R m hr hmu hR hm
      hscale hmargin P.time i k phi (P.position, P.velocity)
  rw [backwardOperator_apply, hdt, hx, hh]
  rfl


/-- The selected full extended source, with the literal backward-operator sign convention. -/
def constructionExtendedSource {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R m : ℝ) (A : XV d → PDE.Mat d)
    (P : KineticPoint d) : ℝ :=
  constructionExtendedTimeJet h r mu R P.time (P.position, P.velocity) +
    PDE.vecDot P.velocity (fun i => constructionExtendedNativeGradient h r mu R m P.time
      (P.position, P.velocity) (Fin.castAdd d i)) -
    matrixContraction (A (P.position, P.velocity)) (fun i k =>
      constructionExtendedNativeHessian h r mu R m P.time (P.position, P.velocity) i k)

/-- At each time the actual smoothed operator converges almost everywhere to the full
source formed from the same selected representatives. -/
theorem construction_smoothed_operator_tendsto_ae {d : ℕ} (hd : 1 ≤ d)
    {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r mu R m : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2)
    (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 ≤ m)
    (A : XV d → PDE.Mat d) (t : ℝ) :
    ∀ᵐ q : XV d ∂volume, Tendsto (fun n => backwardOperator (fun _t x v => A (x, v))
      (smoothedZeroExtendedProfile h r mu R (standardMollifierSequence n)) ⟨t, q.1, q.2⟩)
      atTop (𝓝 (constructionExtendedSource h r mu R m A ⟨t, q.1, q.2⟩))  := by
  have construction_selected_jets_tendsto_ae :
      ∀ᵐ q ∂volume,
      (∀ i : Fin (d + d), Tendsto
        (fun n => spatialMollify (standardMollifierSequence n)
          (fun y => constructionExtendedNativeGradient h r mu R m t y i) q)
        atTop (𝓝 (constructionExtendedNativeGradient h r mu R m t q i))) ∧
      (∀ i k : Fin d, Tendsto
        (fun n => spatialMollify (standardMollifierSequence n)
          (fun y => constructionExtendedNativeHessian h r mu R m t y i k) q)
        atTop (𝓝 (constructionExtendedNativeHessian h r mu R m t q i k))) := by
    have hg (i : Fin (d + d)) := construction_spatialMollify_tendsto_ae
      (fun y => constructionExtendedNativeGradient h r mu R m t y i)
      (construction_locallyIntegrable_native _
        (construction_extendedGradient_locallyIntegrable h r hr mu R m t i))
    have hh (i k : Fin d) := construction_spatialMollify_tendsto_ae
      (fun y => constructionExtendedNativeHessian h r mu R m t y i k)
      (construction_locallyIntegrable_native _
        (construction_extendedHessian_locallyIntegrable h r hr mu R m t i k))
    exact (ae_all_iff.mpr hg).and (ae_all_iff.mpr fun i => ae_all_iff.mpr (hh i))
  have ht := construction_spatialMollify_tendsto_ae _
    (construction_extendedTimeJet_locallyIntegrable h r mu R t)
  filter_upwards [ht, construction_selected_jets_tendsto_ae] with q hqt hq
  have hx := tendsto_finsetSum Finset.univ (fun i _ =>
    (hq.1 (Fin.castAdd d i)).const_mul (q.2 i))
  have hh := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun k _ => (hq.2 i k).const_mul (A q i k)))
  have he := (hqt.add hx).sub hh
  simp_rw [construction_smoothed_operator_eq hd ha ha1 h r mu R m hr hmu hR hm
    hscale hmargin]
  simpa only [constructionExtendedSource, PDE.vecDot, matrixContraction] using! he


/-- The velocity cutoff can have a strict inner margin on the entire compact domain. -/
theorem construction_exists_strict_velocity_margin {d : ℕ} {alpha : ℝ}
    (ha : 0 < alpha) (h : CounterProfileStatement d alpha) (R : ℝ)
    (hvel : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < R ^ 2) :
    ∃ m : ℝ, m < R ^ 2 ∧ ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < m  := by
  have construction_exists_velocity_margin :
      ∃ m : ℝ, m < R ^ 2 ∧ ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 ≤ m := by
    have hK := isCompact_profile_unit_sublevel ha h
    have hzero := (selectedProfile_spec h).2.2.2.2.2.2.2.1
    have hne : ({q : XV d | profileFunction h q ≤ 1} : Set (XV d)).Nonempty :=
      ⟨0, by change profileFunction h 0 ≤ 1; rw [hzero]; norm_num⟩
    have hc : Continuous (fun q : XV d => PDE.vecNormSq q.2) :=
      PDE.contDiff_vecNormSq.continuous.comp continuous_snd
    obtain ⟨q, hq, hmax⟩ := hK.exists_isMaxOn hne hc.continuousOn
    exact ⟨PDE.vecNormSq q.2, hvel q hq, fun z hz => hmax hz⟩
  obtain ⟨m, hm, hb⟩ := construction_exists_velocity_margin
  refine ⟨(m + R ^ 2) / 2, by linarith only [hm], ?_⟩
  intro q hq
  have hh := hb q hq
  linarith only [hh, hm]


/-- Both orders of cutoff derivatives vanish on the strict inner region. -/
theorem constructionPackedCutoff_jets_zero {d : ℕ} (m R : ℝ) (hm : m < R ^ 2)
    (x : PDE.Vec (d + d)) (hx : PDE.vecNormSq (spatialCoordinateCLE d x).2 < m) :
    fderiv ℝ (constructionPackedCutoff d m R) x = 0 ∧
      ∀ k, fderiv ℝ (fun y => fderiv ℝ (constructionPackedCutoff d m R) y (PDE.basisVec k))
        x = 0  := by
  have constructionPackedCutoff_eventually_one :
      constructionPackedCutoff d m R =ᶠ[𝓝 x] (fun _ => 1) := by
    have hc := PDE.contDiff_vecNormSq.continuous.comp (spatialCoordinateCLE d).continuous.snd
    filter_upwards [hc.continuousAt.eventually (Iio_mem_nhds hx)] with y hy
    exact constructionVelocityCutoff_eq_one m R hm _ hy.le
  have he := constructionPackedCutoff_eventually_one
  have hfirst : fderiv ℝ (constructionPackedCutoff d m R) x = 0 := by
    rw [he.fderiv_eq]
    exact (hasFDerivAt_const 1 x).fderiv
  refine ⟨hfirst, ?_⟩
  intro k
  have hd : (fun y => fderiv ℝ (constructionPackedCutoff d m R) y (PDE.basisVec k)) =ᶠ[𝓝 x]
      (fun _ => 0) := by
    filter_upwards [he.eventually_nhds] with y hy
    have hy' : constructionPackedCutoff d m R =ᶠ[𝓝 y] (fun _ => 1) := hy
    rw [hy'.fderiv_eq, (hasFDerivAt_const 1 y).fderiv]
    rfl
  rw [hd.fderiv_eq]
  exact (hasFDerivAt_const 0 x).fderiv

/-- Throughout the profile domain the extended representatives equal the raw cutoff jets. -/
theorem construction_extended_jets_eq_raw_on_profile {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R m t : ℝ) (hm : m < R ^ 2)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < m)
    (x : PDE.Vec (d + d)) (hx : profileFunction h (spatialCoordinateCLE d x) < 1) :
    (∀ i, constructionExtendedPackedGradient h r mu R m t x i =
      spatialPackedCutoffGradient h r mu R t x i) ∧
    (∀ i k, constructionExtendedPackedHessian h r mu R m t x i k =
      spatialPackedCutoffVelocityHessian h r mu R t x i k) := by
  have hv := hmargin _ hx.le
  have hval : constructionPackedCutoff d m R x = 1 :=
    constructionVelocityCutoff_eq_one m R hm _ hv.le
  obtain ⟨hfirst, hsecond⟩ := constructionPackedCutoff_jets_zero m R hm x hv
  constructor
  · intro i
    simp [constructionExtendedPackedGradient, hval, hfirst, _root_.zero_apply]
  · intro i k
    simp [constructionExtendedPackedHessian, hval, hfirst, hsecond, _root_.zero_apply]


/-- On the profile domain the extended source is exactly the raw cutoff source, with no
extra multiplier terms. The same jointly selected flattened jets occur on both sides. -/
theorem construction_extendedSource_eq_raw_on_profile {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R m t : ℝ) (hm : m < R ^ 2)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < m)
    (q : XV d) (hq : profileFunction h q < 1) :
    constructionExtendedSource h r mu R m (profileMatrix h) ⟨t, q.1, q.2⟩ =
      timeCutoffSourceRepresentative h r mu R ⟨t, q.1, q.2⟩ := by
  have hj := construction_extended_jets_eq_raw_on_profile h r mu R m t hm hmargin
    ((spatialCoordinateCLE d).symm q) (by
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using hq)
  simp only [constructionExtendedSource, constructionExtendedNativeGradient,
    constructionExtendedNativeHessian, hj.1, hj.2]
  have hq' : (q.1, q.2) ∈ {y | profileFunction h y < 1} := hq
  simp only [constructionExtendedTimeJet, indicator_of_mem hq',
    timeCutoffProfile_timeDerivative, timeCutoffSourceRepresentative,
    spatialPackedCutoffGradient, spatialPackedCutoffVelocityHessian,
    spatialPackedGradient, Fin.addCases_left,
    spatialPackedBarrier_positionGradient, spatialPackedBarrier_velocityHessian,
    spatialPackedBarrier,
    ContinuousLinearEquiv.apply_symm_apply, sub_zero, barrier_velocityGradient,
    barrier_velocityHessian, Pi.sub_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [spatialPackedBarrier_velocityGradient,
    ContinuousLinearEquiv.apply_symm_apply, Prod.mk.eta]

/-- The full extended source is the raw source inside the profile domain and zero outside,
almost everywhere at every fixed time. -/
theorem construction_extendedSource_eq_indicator_ae {d : ℕ} (hd : 1 ≤ d)
    {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r mu R m : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2)
    (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < m) (t : ℝ) :
    (fun q : XV d => constructionExtendedSource h r mu R m (profileMatrix h)
        ⟨t, q.1, q.2⟩) =ᵐ[volume]
      {q | profileFunction h q < 1}.indicator
        (fun q => timeCutoffSourceRepresentative h r mu R ⟨t, q.1, q.2⟩) := by
  have hj := construction_ae_native _
    (construction_extended_jets_zero_outside_profile hd ha ha1 h r mu R m hr hmu hR hm
      hscale (fun q hq => (hmargin q hq).le) t)
  filter_upwards [hj] with q hq
  change constructionExtendedSource h r mu R m (profileMatrix h) ⟨t, q.1, q.2⟩ =
    {y | profileFunction h y < 1}.indicator
      (fun y => timeCutoffSourceRepresentative h r mu R ⟨t, y.1, y.2⟩) q
  by_cases hprof : profileFunction h q < 1
  · have hmem : q ∈ {y | profileFunction h y < 1} := hprof
    rw [indicator_of_mem hmem]
    exact construction_extendedSource_eq_raw_on_profile h r mu R m t hm hmargin q hprof
  · have hn : 1 ≤ profileFunction h
        (spatialCoordinateCLE d ((spatialCoordinateCLE d).symm q)) := by
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using (not_lt.mp hprof)
    have hh := hq hn
    have hmem : q ∉ {y | profileFunction h y < 1} := hprof
    rw [indicator_of_notMem hmem]
    simp [constructionExtendedSource, constructionExtendedTimeJet, constructionExtendedNativeGradient, constructionExtendedNativeHessian, indicator_of_notMem hmem, hh.1, hh.2, PDE.vecDot, matrixContraction]

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

