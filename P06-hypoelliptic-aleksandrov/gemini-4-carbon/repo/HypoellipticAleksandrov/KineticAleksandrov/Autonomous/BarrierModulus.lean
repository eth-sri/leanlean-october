module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.BarrierFunctionSpaceLinear
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AnnularNormalizationGeometry
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RatioNormalizationMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureJets
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.UniversalBarrierParameters
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RadialStationary
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BarrierModulusEstimates

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
section
open Set Filter Topology

/-- Equality on a neighborhood identifies the complete Bellman expression. -/
theorem bellman_operator_germ_eq {phi psi : (ℝ × ℝ) → ℝ} {q : ℝ × ℝ}
    (h : phi =ᶠ[𝓝 q] psi) (b : ℝ) : bellmanOperator b phi q = bellmanOperator b psi q := by
  have hv : bellmanDv phi =ᶠ[𝓝 q] bellmanDv psi :=
    (h.fderiv (𝕜 := ℝ)).mono (fun x hx => congrArg (fun L => L (0, 1)) hx)
  unfold bellmanOperator bellmanDx bellmanDvv
  rw [h.fderiv_eq, hv.fderiv_eq]

/-- Constant multiplication scales the complete Bellman expression. -/
theorem bellman_operator_mul (c b : ℝ) (phi : (ℝ × ℝ) → ℝ) (q : ℝ × ℝ) :
    bellmanOperator b (fun z => c * phi z) q = c * bellmanOperator b phi q := by
  change bellmanOperator b (c • phi) q = _
  rw [bellmanOperator, bellmanDx, fderiv_const_smul_field, bellmanDvv_smul]
  simp [smul_apply, bellmanOperator, bellmanDx]
  ring

/-- The Bellman operator has degree alpha minus two on a C² homogeneous function. -/
theorem bellman_homogeneous_operator_scaling {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) (r : ℝ) (hr : 0 < r)
    (q : ℝ × ℝ) (hq : q ∈ bellmanPuncturedSet) (b : ℝ) :
    bellmanOperator b phi (bellmanPlaneDilation r q) =
      r ^ (alpha - 2) * bellmanOperator b phi q := by
  have he : (fun z => phi (bellmanPlaneDilation r z)) =ᶠ[𝓝 q]
      fun z => r ^ alpha * phi z := by
    filter_upwards [bellmanPuncturedSet_isOpen.mem_nhds hq] with z hz
    exact h.2 r hr z hz
  have hj : r ^ 2 * bellmanOperator b phi (bellmanPlaneDilation r q) =
      r ^ alpha * bellmanOperator b phi q := by
    rw [← bellmanOperator_comp_dilation r hr phi h.1 q hq b,
      bellman_operator_germ_eq he b, bellman_operator_mul]
  apply mul_left_cancel₀ (pow_ne_zero 2 hr.ne')
  calc
    r ^ 2 * bellmanOperator b phi (bellmanPlaneDilation r q) =
        r ^ alpha * bellmanOperator b phi q := hj
    _ = r ^ 2 * (r ^ (alpha - 2) * bellmanOperator b phi q) := by
      rw [← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hr]
      congr 2
      ring

end
section
open Set

/-- Normalizing a punctured point by its literal gauge puts it on the source sphere. -/
def bellmanSpherePoint (q : ℝ × ℝ) (hq : q ∈ bellmanPuncturedSet) : BellmanSphere :=
  ⟨bellmanPlaneDilation (bellmanGauge q)⁻¹ q, by
    rw [bellmanGauge_dilation _ (inv_pos.mpr (bellmanGauge_pos q hq)),
      inv_mul_cancel₀ (bellmanGauge_pos q hq).ne']⟩

/-- Dilating the normalized sphere point by its gauge recovers the original point. -/
theorem bellmanSpherePoint_reconstruct (q : ℝ × ℝ) (hq : q ∈ bellmanPuncturedSet) :
    bellmanPlaneDilation (bellmanGauge q) (bellmanSpherePoint q hq).val = q := by
  rw [bellmanSpherePoint, bellmanPlaneDilation_comp,
    mul_inv_cancel₀ (bellmanGauge_pos q hq).ne']
  simp [bellmanPlaneDilation, one_pow]


end
section
open Set

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- The strictly positive cone in the uniform continuous-function space. -/
def bellmanPositiveCone : Set C(X, ℝ) := {f | ∀ x, 0 < f x}

/-- Strict positivity is open in the uniform topology on a compact domain. -/
theorem bellmanPositiveCone_isOpen : IsOpen (bellmanPositiveCone (X := X)) := by
  simpa [bellmanPositiveCone, mapsTo_univ_iff] using
    ContinuousMap.isOpen_setOfPred_mapsTo isCompact_univ isOpen_Ioi

omit [CompactSpace X] in
/-- The strictly positive cone is convex. -/
theorem bellmanPositiveCone_convex : Convex ℝ (bellmanPositiveCone (X := X)) := by
  intro f hf g hg a b ha hb hab x
  change 0 < a * f x + b * g x
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hb' : b = 1 := by linarith only [hab]
    simpa [hb'] using hg x
  · exact add_pos_of_pos_of_nonneg (mul_pos ha' (hf x)) (mul_nonneg hb (hg x).le)


end
section
open Set MeasureTheory
open scoped CompactlySupported

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]

/-- A normalized positive continuous functional has a probability representing it. -/
theorem exists_bellman_functional_probability (L : C(X, ℝ) →L[ℝ] ℝ)
    (h1 : L 1 = 1) (hpos : ∀ f : C(X, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ L f) :
    ∃ mu : Measure X, IsProbabilityMeasure mu ∧
      ∀ f : C(X, ℝ), ∫ x, f x ∂mu = L f := by
  let ell : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
    { toFun := fun f => L f.toContinuousMap
      map_add' := fun f g => by
        exact map_add L _ _
      map_smul' := fun c f => by
        exact map_smul L _ _
      monotone' := fun f g hfg => by
        have hp := hpos (g.toContinuousMap - f.toContinuousMap)
          (fun x => sub_nonneg.mpr (hfg x))
        rw [map_sub] at hp
        exact sub_nonneg.mp hp }
  let mu := RealRMK.rieszMeasure ell
  have ht (f : C(X, ℝ)) : ∫ x, f x ∂mu = L f := by
    let fc : C_c(X, ℝ) := ⟨f, HasCompactSupport.of_compactSpace f⟩
    exact RealRMK.integral_rieszMeasure ell fc
  have hmass : mu.real univ = 1 := by
    simpa using (ht 1).trans h1
  exact ⟨mu, isProbabilityMeasure_iff_real.mpr hmass, ht⟩

/-- A continuous subspace avoiding strict positivity has an annihilating probability. -/
theorem exists_bellman_subspace_probability (S : Submodule ℝ C(X, ℝ))
    (hno : Disjoint (bellmanPositiveCone (X := X)) (S : Set C(X, ℝ))) :
    ∃ mu : Measure X, IsProbabilityMeasure mu ∧
      ∀ f ∈ S, ∫ x, f x ∂mu = 0  := by
  have exists_bellman_positive_functional :
      ∃ L : C(X, ℝ) →L[ℝ] ℝ,
      L 1 = 1 ∧ (∀ f : C(X, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ L f) ∧
      ∀ f ∈ S, L f = 0 := by
    obtain ⟨l, u, hl, hu⟩ := geometric_hahn_banach_open bellmanPositiveCone_convex
      bellmanPositiveCone_isOpen S.topologicalClosure.convex (hno.closure_right bellmanPositiveCone_isOpen)
    have hu0 : u ≤ 0 := by simpa using hu 0 S.topologicalClosure.zero_mem
    have hz : ∀ f ∈ S.topologicalClosure, l f = 0 := by
      intro f hf
      by_contra hn
      have hc := hu (((u - 1) / l f) • f) (S.topologicalClosure.smul_mem _ hf)
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hn] at hc
      linarith only [hc]
    let g := -l
    have hgp : ∀ f ∈ bellmanPositiveCone, 0 < g f := by
      intro f hf
      change 0 < -l f
      linarith only [hl f hf, hu0]
    have hg1 := hgp 1 (fun _ => zero_lt_one)
    have hgn : ∀ f : C(X, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ g f := by
      intro f hf
      by_contra hn
      have hneg := lt_of_not_ge hn
      let c := (g 1 + 1) / (-g f)
      have hc : 0 < c := div_pos (by linarith only [hg1]) (neg_pos.mpr hneg)
      have hp : 1 + c • f ∈ bellmanPositiveCone := by
        intro x
        exact add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hc.le (hf x))
      have h := hgp (1 + c • f) hp
      rw [map_add, map_smul, smul_eq_mul] at h
      have he : c * g f = -(g 1 + 1) := by
        dsimp [c]
        field_simp [hneg.ne]
      rw [he] at h
      linarith only [h]
    refine ⟨(g 1)⁻¹ • g, ?_, ?_, ?_⟩
    · simp [smul_apply, inv_mul_cancel₀ hg1.ne']
    · intro f hf
      exact mul_nonneg (inv_nonneg.mpr hg1.le) (hgn f hf)
    · intro f hf
      simp [smul_apply, g, neg_apply, (hz f (S.le_topologicalClosure hf))]
  obtain ⟨L, h1, hpos, hS⟩ := exists_bellman_positive_functional
  obtain ⟨mu, hmu, ht⟩ := exists_bellman_functional_probability L h1 hpos
  exact ⟨mu, hmu, fun f hf => (ht f).trans (hS f hf)⟩

end
section
open MeasureTheory Set


/-- Literal position rescaling transports unnormalized adjoint pairs with both bounds divided. -/
theorem IsBellmanAdjointPair.rescale_position {lam Lam β : ℝ}
    {μ η : Measure BellmanPuncturedPlane} (hp : IsBellmanAdjointPair lam Lam β μ η)
    (s : ℝ) (hs : 0 < s) :
    IsBellmanAdjointPair (lam / s) (Lam / s) β
      (Measure.map (bellmanPositionHomeomorph s hs) μ)
      (ENNReal.ofReal s⁻¹ • Measure.map (bellmanPositionHomeomorph s hs) η)   := by
  have map_position {μ η : Measure BellmanPuncturedPlane} (hp : IsBellmanStationaryAdjointPair μ η) :
      IsBellmanStationaryAdjointPair (Measure.map (bellmanPositionHomeomorph s hs) μ)
      (ENNReal.ofReal s⁻¹ • Measure.map (bellmanPositionHomeomorph s hs) η) := by
    have bellmanPositionEquiv_fderiv_velocity_twice (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (q : ℝ × ℝ) :
        fderiv ℝ (fun z => fderiv ℝ (fun w => φ (bellmanPositionEquiv s hs w)) z (0, 1))
        q (0, 1) =
      fderiv ℝ (fun z => fderiv ℝ φ z (0, 1)) (bellmanPositionEquiv s hs q) (0, 1) := by
      have bellmanPositionEquiv_fderiv_velocity (φ : ℝ × ℝ → ℝ) (hφ : Differentiable ℝ φ) (q : ℝ × ℝ) :
          fderiv ℝ (fun z => φ (bellmanPositionEquiv s hs z)) q (0, 1) =
          fderiv ℝ φ (bellmanPositionEquiv s hs q) (0, 1) := by
        let T := bellmanPositionEquiv s hs
        have h := ((hφ (T q)).hasFDerivAt.comp q T.hasFDerivAt).fderiv
        change fderiv ℝ (φ ∘ T) q (0, 1) = _
        rw [h, ContinuousLinearMap.comp_apply]
        change fderiv ℝ φ (T q) (s * 0, 1) = _
        simp
        rfl
      simp only [bellmanPositionEquiv_fderiv_velocity φ (hφ.differentiable (by simp))]
      exact bellmanPositionEquiv_fderiv_velocity _
        ((bellman_contDiff_direction hφ (0, 1)).differentiable (by simp)) q
    have bellmanPositionEquiv_fderiv_position (φ : ℝ × ℝ → ℝ) (hφ : Differentiable ℝ φ) (q : ℝ × ℝ) :
        fderiv ℝ (fun z => φ (bellmanPositionEquiv s hs z)) q (1, 0) =
        s * fderiv ℝ φ (bellmanPositionEquiv s hs q) (1, 0) := by
      let T := bellmanPositionEquiv s hs
      have h := ((hφ (T q)).hasFDerivAt.comp q T.hasFDerivAt).fderiv
      change fderiv ℝ (φ ∘ T) q (1, 0) = _
      rw [h, ContinuousLinearMap.comp_apply]
      have he : T (1, 0) = s • (1, 0) := by
        change (s * 1, 0) = (s * 1, s * 0)
        simp
      change fderiv ℝ φ (T q) (T (1, 0)) = _
      rw [he, map_smul, smul_eq_mul]
    intro φ hφ hc haway
    let T := bellmanPositionEquiv s hs
    let H := bellmanPositionHomeomorph s hs
    have hscomp : tsupport (fun q => φ (T q)) ⊆ {q | q ≠ (0, 0)} := by
      intro q hq hzero
      have h := tsupport_comp_subset_preimage φ T.continuous hq
      apply (haway h)
      rw [hzero]
      exact T.map_zero
    have h := hp (fun q => φ (T q)) (hφ.comp T.contDiff) (hc.comp_homeomorph T.toHomeomorph) hscomp
    dsimp only [T] at h
    simp only [bellmanPositionEquiv_fderiv_position φ (hφ.differentiable (by simp)),
      bellmanPositionEquiv_fderiv_velocity_twice φ hφ] at h
    have hfactor : (∫ q : BellmanPuncturedPlane,
        q.val.2 * (s * fderiv ℝ φ (T q.val) (1, 0)) ∂μ) =
        s * ∫ q : BellmanPuncturedPlane, q.val.2 * fderiv ℝ φ (T q.val) (1, 0) ∂μ := by
      rw [← integral_const_mul]
      congr 1
      funext q
      ring
    rw [hfactor] at h
    rw [H.measurableEmbedding.integral_map,
      integral_smul_measure, H.measurableEmbedding.integral_map,
      ENNReal.toReal_ofReal (inv_nonneg.mpr hs.le)]
    change (∫ q : BellmanPuncturedPlane, q.val.2 * fderiv ℝ φ (T q.val) (1, 0) ∂μ) +
      s⁻¹ * (∫ q : BellmanPuncturedPlane,
        fderiv ℝ (fun z => fderiv ℝ φ z (0, 1)) (T q.val) (0, 1) ∂η) = 0
    simpa [mul_add, ← mul_assoc, inv_mul_cancel₀ hs.ne'] using (congrArg (fun a => s⁻¹ * a) h)
  have bellman_ofReal_div (a : ℝ) :
      ENNReal.ofReal (a / s) = ENNReal.ofReal s⁻¹ * ENNReal.ofReal a := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hs.le)]
    congr 1
    ring
  let H := bellmanPositionHomeomorph s hs
  rcases hp with ⟨hμ, hη, hne, hlo, hhi, hstat, hdμ, hdη⟩
  have hμne : μ ≠ 0 :=
    IsBellmanAdjointPair.left_ne_zero ⟨hμ, hη, hne, hlo, hhi, hstat, hdμ, hdη⟩
  refine ⟨hμ.map_homeomorph H,
    (hη.map_homeomorph H).smul _ ENNReal.ofReal_ne_top,
    Or.inl ((Measure.map_ne_zero_iff H.measurable.aemeasurable).mpr hμne), ?_, ?_,
    map_position hstat, hdμ.map_position s hs, (hdη.map_position s hs).smul _⟩
  · rw [bellman_ofReal_div lam, ← smul_smul]
    apply smul_le_smul_left
    have h := Measure.map_mono hlo H.measurable
    rwa [Measure.map_smul _ H.measurable.aemeasurable] at h
  · rw [bellman_ofReal_div Lam, ← smul_smul]
    apply smul_le_smul_left
    have h := Measure.map_mono hhi H.measurable
    rwa [Measure.map_smul _ H.measurable.aemeasurable] at h


end
section
open Set

/-- One homogeneous barrier and constant work for all punctured points and coefficients. -/
theorem exists_bellman_barrier (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    2 ≤ bellmanAdjointExponent (Lam / lam)
      (by apply (le_div_iff₀ hlam).2; simpa only [one_mul] using hLam) ∧
    bellmanAdjointExponent (Lam / lam)
      (by apply (le_div_iff₀ hlam).2; simpa only [one_mul] using hLam) < 3 ∧
    ∀ alpha : ℝ, bellmanAdjointExponent (Lam / lam)
      (by apply (le_div_iff₀ hlam).2; simpa only [one_mul] using hLam) - 2 < alpha →
      alpha < 1 → ∃ phi : (ℝ × ℝ) → ℝ, ∃ c : ℝ,
        IsBellmanHomogeneous alpha phi ∧ 0 < c ∧
          ∀ q ∈ bellmanPuncturedSet, ∀ b ∈ Icc lam Lam,
            c * bellmanGauge q ^ (alpha - 2) ≤ bellmanOperator b phi q   := by
  have exists_positive_bellman_image (alpha : ℝ) (ha : bellmanAdjointExponent (Lam / lam)
      (by apply (le_div_iff₀ hlam).2; simpa using hLam) - 2 < alpha) (ha1 : alpha < 1) :
      ∃ phi : (ℝ × ℝ) → ℝ, IsBellmanHomogeneous alpha phi ∧
      ∀ z : BellmanSphere, ∀ b : BellmanCoefficient lam Lam,
        0 < bellmanOperator b.val phi z.val := open MeasureTheory in by
    have bellman_degrees_normalize (_hLam : lam ≤ Lam) :
        bellmanDegrees lam Lam = bellmanAdmissibleDegrees (Lam / lam) := by
      ext β
      rw [mem_bellmanAdmissibleDegrees_iff]
      constructor
      · rintro ⟨μ, η, hp⟩
        refine ⟨Measure.map (bellmanPositionHomeomorph lam hlam) μ,
          ENNReal.ofReal lam⁻¹ • Measure.map (bellmanPositionHomeomorph lam hlam) η, ?_⟩
        simpa only [div_self hlam.ne'] using hp.rescale_position lam hlam
      · rintro ⟨μ, η, hp⟩
        refine ⟨Measure.map (bellmanPositionHomeomorph lam⁻¹ (inv_pos.mpr hlam)) μ,
          ENNReal.ofReal (lam⁻¹)⁻¹ •
            Measure.map (bellmanPositionHomeomorph lam⁻¹ (inv_pos.mpr hlam)) η, ?_⟩
        have hlow : 1 / lam⁻¹ = lam := by simp
        have hhigh : (Lam / lam) / lam⁻¹ = Lam := by
          simp [div_inv_eq_mul, hlam.ne']
        simpa only [hlow, hhigh] using hp.rescale_position lam⁻¹ (inv_pos.mpr hlam)
    have exists_annihilating_bellman_probability (_hlam : 0 < lam) (_hLam : lam ≤ Lam) (_ha : 0 < alpha) (_ha1 : alpha < 1) (hno : ¬ ∃ phi : (ℝ × ℝ) → ℝ, IsBellmanHomogeneous alpha phi ∧
        ∀ z : BellmanSphere, ∀ b : BellmanCoefficient lam Lam,
          0 < bellmanOperator b.val phi z.val) :
        ∃ pi : Measure (BellmanSphere × BellmanCoefficient lam Lam),
        IsProbabilityMeasure pi ∧
        ∀ phi : (ℝ × ℝ) → ℝ, IsBellmanHomogeneous alpha phi →
          (∫ w, bellmanOperator w.2.val phi w.1.val ∂pi) = 0 := by
      have hd : Disjoint bellmanPositiveCone
          (bellmanImageSpace alpha lam Lam : Set C(BellmanSphere × BellmanCoefficient lam Lam, ℝ)) := by
        refine disjoint_left.mpr ?_
        intro f hf hS
        obtain ⟨phi, hphi, he⟩ := (mem_bellmanImageSpace_iff alpha lam Lam f).mp hS
        apply hno
        refine ⟨phi, hphi, ?_⟩
        intro z b
        have h := hf (z, b)
        rwa [← he] at h
      obtain ⟨pi, hpi, ht⟩ := exists_bellman_subspace_probability
        (bellmanImageSpace alpha lam Lam) hd
      refine ⟨pi, hpi, ?_⟩
      intro phi hphi
      exact ht (bellmanImage lam Lam phi hphi)
        ((mem_bellmanImageSpace_iff alpha lam Lam _).mpr ⟨phi, hphi, rfl⟩)
    obtain ⟨hapos, _, hgap⟩ := bellman_barrier_parameter_range lam Lam hlam hLam alpha ha ha1
    by_contra hno
    obtain ⟨pi, hpi, hann⟩ :=
      exists_annihilating_bellman_probability hlam hLam hapos ha1 hno
    let := hpi
    have hd : 2 + alpha ∈ bellmanDegrees lam Lam := ⟨radialMu alpha pi, radialEta alpha pi, (radial_bellman_pair_stationary lam Lam alpha hlam hLam hapos ha1 pi hann)⟩
    rw [bellman_degrees_normalize hLam] at hd
    exact (not_le_of_gt hgap) ((bellmanAdjointExponent_characterization (Lam / lam) (by apply (le_div_iff₀ hlam).2; simpa using hLam)).1.1 hd)
  have positive_bellman_image_lower_bound (_hlam : 0 < lam) (alpha : ℝ) (phi : (ℝ × ℝ) → ℝ) (hhom : IsBellmanHomogeneous alpha phi) (hpos : ∀ z : BellmanSphere, ∀ b : BellmanCoefficient lam Lam,
      0 < bellmanOperator b.val phi z.val) :
      ∃ c : ℝ, 0 < c ∧ ∀ q ∈ bellmanPuncturedSet, ∀ b ∈ Icc lam Lam,
      c * bellmanGauge q ^ (alpha - 2) ≤ bellmanOperator b phi q := by
    let : Nonempty (BellmanCoefficient lam Lam) := bellmanCoefficient_nonempty lam Lam hLam
    have hc := hhom.image_continuous (lam := lam) (Lam := Lam)
    obtain ⟨w0, _, hmin⟩ := (isCompact_univ : IsCompact
      (univ : Set (BellmanSphere × BellmanCoefficient lam Lam))).exists_isMinOn
        univ_nonempty hc.continuousOn
    refine ⟨bellmanOperator w0.2.val phi w0.1.val, hpos w0.1 w0.2, ?_⟩
    intro q hq b hb
    let z := bellmanSpherePoint q hq
    have hs := bellman_homogeneous_operator_scaling hhom (bellmanGauge q)
      (bellmanGauge_pos q hq) z.val z.ne_zero b
    rw [bellmanSpherePoint_reconstruct q hq] at hs
    rw [hs, mul_comm]
    exact mul_le_mul_of_nonneg_left (hmin (show (z, (⟨b, hb⟩ : BellmanCoefficient lam Lam)) ∈ univ from trivial)) (Real.rpow_nonneg (bellmanGauge_nonneg q) _)
  have hr : 1 ≤ Lam / lam := by
    apply (le_div_iff₀ hlam).2
    simpa using hLam
  obtain ⟨hlo, hhi⟩ := bellmanAdjointExponent_range (Lam / lam) hr
  refine ⟨hlo, hhi, ?_⟩
  intro alpha ha ha1
  obtain ⟨phi, hhom, hpos⟩ := exists_positive_bellman_image alpha ha ha1
  obtain ⟨c, hc, hbound⟩ :=
    positive_bellman_image_lower_bound hlam alpha phi hhom hpos
  exact ⟨phi, c, hhom, hc, hbound⟩

end
end HypoellipticAleksandrov.KineticAleksandrov

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set BarrierRegularization

/-- The source's selected witness and its modulus are chosen before any coefficient field.
Thus both constants and the witness have only the source parameter dependencies. -/
theorem exists_bellman_barrier_with_modulus (lam Lam : ℝ) (hlam : 0 < lam)
    (hLam : lam ≤ Lam) (alpha : ℝ)
    (ha : bellmanAdjointExponent (Lam / lam)
      (by apply (le_div_iff₀ hlam).2; simpa only [one_mul] using hLam) - 2 < alpha)
    (ha1 : alpha < 1) :
    ∃ phi : (ℝ × ℝ) → ℝ, ∃ c C : ℝ,
      IsBellmanHomogeneous alpha phi ∧ 0 < c ∧ 0 ≤ C ∧
      (∀ q ∈ bellmanPuncturedSet, ∀ b ∈ Icc lam Lam,
        c * bellmanGauge q ^ (alpha - 2) ≤ bellmanOperator b phi q) ∧
      ∀ z w : ℝ × ℝ,
        |bellmanOriginExtension phi z - bellmanOriginExtension phi w| ≤
          C * (|z.1 - w.1| ^ (alpha / 3) + |z.2 - w.2| ^ alpha) := by
  obtain ⟨hlo, _, hb⟩ := exists_bellman_barrier lam Lam hlam hLam
  obtain ⟨phi, c, hhom, hc, hbound⟩ := hb alpha ha ha1
  obtain ⟨C, hC, hmod⟩ := barrier_coordinate_modulus hhom (lt_of_le_of_lt (sub_nonneg.mpr hlo) ha) ha1
  exact ⟨phi, c, C, hhom, hc, hC, hbound, hmod⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

