module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripMassQuadraticCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionComparison
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripMassQuadratic
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelCutoffSequence
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceWeakGreenSigned
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.DomainDominationMeasure
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelDense
import Mathlib.Topology.Piecewise
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripTimeMarginal

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Evolution Set MeasureTheory Filter SectionTwo TheoremA
open scoped Topology ENNReal CompactlySupported

/-- A scalar velocity profile, written in the native diffused coordinate. -/
def reconstructionProfile (f : ℝ → ℝ) (p : Point) : ℝ := f (p.position 0)

/-- A twice smooth scalar profile has the required native slice regularity. -/
theorem reconstructionProfile_regular {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (p : Point) :
    IsSliceRegularAt (reconstructionProfile f) p := by
  refine ⟨?_, ?_, ?_⟩
  · change DifferentiableAt ℝ (fun _ : ℝ => f (p.position 0)) p.time
    exact differentiableAt_const _
  · exact (hf.comp (contDiff_apply ℝ ℝ 0)).contDiffAt
  · change ContDiffAt ℝ 2 (fun _ : PDE.Vec 1 => f (p.position 0)) p.velocity
    exact contDiffAt_const

/-- A continuous scalar profile is continuous on native spacetime. -/
theorem reconstructionProfile_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (reconstructionProfile f) :=
  hf.comp ((continuous_apply 0).comp continuous_position)





/-- Positive exponential weights at the two velocity faces. -/
def reconstructionCollarWeight (H : Interval) (δ v : ℝ) : ℝ :=
  Real.exp ((H.lo - v) / δ) + Real.exp ((v - H.hi) / δ)

/-- Scalar diffused profile of the collar supersolution. -/
def reconstructionCollarProfile (H : Interval) (lam δ v : ℝ) : ℝ :=
  δ ^ 2 / lam * (2 - reconstructionCollarWeight H δ v)

/-- Both exponential weights are strictly positive. -/
theorem reconstructionCollarWeight_nonneg (H : Interval) (δ v : ℝ) :
    0 ≤ reconstructionCollarWeight H δ v :=
  add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le

/-- Inside the closed interval each exponential weight is at most one. -/
theorem reconstructionCollarWeight_le_two (H : Interval) {δ v : ℝ}
    (hδ : 0 < δ) (hv : H.lo ≤ v ∧ v ≤ H.hi) :
    reconstructionCollarWeight H δ v ≤ 2 := by
  exact (add_le_add (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hv.1) hδ.le)) (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hv.2) hδ.le))).trans_eq (by norm_num)

/-- The collar profile is nonnegative and uniformly small on the closed interval. -/
theorem reconstructionCollarProfile_bounds (H : Interval) {lam δ v : ℝ}
    (hlam : 0 < lam) (hδ : 0 < δ) (hv : H.lo ≤ v ∧ v ≤ H.hi) :
    0 ≤ reconstructionCollarProfile H lam δ v ∧
      reconstructionCollarProfile H lam δ v ≤ 2 * δ ^ 2 / lam := by
  have hc := div_nonneg (sq_nonneg δ) hlam.le
  refine ⟨mul_nonneg hc (sub_nonneg.mpr (reconstructionCollarWeight_le_two H hδ hv)), ?_⟩
  exact (mul_le_mul_of_nonneg_left (sub_le_self 2 (reconstructionCollarWeight_nonneg H δ v)) hc).trans_eq (by ring)













/-- A proper scalar spatial weight. -/
def reconstructionSpatialWeight (x : ℝ) : ℝ := Real.exp x + Real.exp (-x)

/-- Native spatial supersolution with a backward exponential time factor. -/
def reconstructionSpatialBarrier (B T : ℝ) (p : Point) : ℝ :=
  Real.exp (B * (T - p.time)) * reconstructionSpatialWeight (p.velocity 0)

/-- The spatial weight is globally smooth. -/
theorem reconstructionSpatialWeight_smooth :
    ContDiff ℝ (⊤ : ℕ∞) reconstructionSpatialWeight :=
  contDiff_id.exp.add contDiff_id.neg.exp

/-- The spatial barrier is globally smooth in native product coordinates. -/
theorem reconstructionSpatialBarrier_smooth (B T : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (rawLift (reconstructionSpatialBarrier B T)) :=
  (contDiff_const.mul (contDiff_const.sub contDiff_fst)).exp.mul
    (reconstructionSpatialWeight_smooth.comp
      ((contDiff_apply ℝ ℝ 0).comp contDiff_snd.snd))

/-- The spatial barrier has the required slice regularity. -/
theorem reconstructionSpatialBarrier_regular (B T : ℝ) (p : Point) :
    IsSliceRegularAt (reconstructionSpatialBarrier B T) p :=
  IsSliceRegularAt.of_contDiffAt
    ((reconstructionSpatialBarrier_smooth B T).of_le (by simp)).contDiffAt

/-- The spatial barrier is continuous. -/
theorem reconstructionSpatialBarrier_continuous (B T : ℝ) :
    Continuous (reconstructionSpatialBarrier B T) :=
  (reconstructionSpatialBarrier_smooth B T).continuous.comp
    (KineticPoint.homeomorphProd 1).continuous


/-- The operator of the spatial barrier uses only bounded transport speed. -/
theorem reconstructionSpatialBarrier_operator (a : ℝ → ℝ → ℝ) (B T : ℝ) (p : Point) :
    transportedForwardOperator (evolutionCoefficient a) (identityDrift 1)
      (reconstructionSpatialBarrier B T) p =
        Real.exp (B * (T - p.time)) *
          (-B * reconstructionSpatialWeight (p.velocity 0) +
            p.position 0 * (Real.exp (p.velocity 0) - Real.exp (-p.velocity 0)))  := by
  have spatial_weight_deriv (x : ℝ) :
      HasDerivAt reconstructionSpatialWeight (Real.exp x - Real.exp (-x)) x := by
    simpa [reconstructionSpatialWeight] using!
      (hasDerivAt_id x).exp.add ((hasDerivAt_id x).neg.exp)
  have ht : kineticTimeDerivative (reconstructionSpatialBarrier B T) p =
      (-B * Real.exp (B * (T - p.time))) * reconstructionSpatialWeight (p.velocity 0) := by
    have h := (((hasDerivAt_const p.time T).sub (hasDerivAt_id p.time)).const_mul B).exp
    have hh := h.mul_const (reconstructionSpatialWeight (p.velocity 0))
    change HasDerivAt (fun t => reconstructionSpatialBarrier B T
      ⟨t, p.position, p.velocity⟩) _ p.time at hh
    rw [kineticTimeDerivative, hh.deriv]
    simp only [Pi.sub_apply, id_eq, zero_sub]
    ring
  have hg : kineticVelocityGradient (reconstructionSpatialBarrier B T) p =
      fun _ => Real.exp (B * (T - p.time)) *
        (Real.exp (p.velocity 0) - Real.exp (-p.velocity 0)) := by
    ext i
    have h := ((spatial_weight_deriv (p.velocity 0)).const_mul
      (Real.exp (B * (T - p.time)))).comp_hasFDerivAt p.velocity
        (hasFDerivAt_apply (𝕜 := ℝ) 0 p.velocity)
    change fderiv ℝ (fun z : PDE.Vec 1 => reconstructionSpatialBarrier B T
      ⟨p.time, p.position, z⟩) p.velocity (PDE.basisVec i) = _
    have hd : fderiv ℝ (fun z : PDE.Vec 1 => reconstructionSpatialBarrier B T
        ⟨p.time, p.position, z⟩) p.velocity =
        (Real.exp (B * (T - p.time)) *
          (Real.exp (p.velocity 0) - Real.exp (-p.velocity 0))) •
            ContinuousLinearMap.proj 0 := by
      simpa using! h.fderiv
    rw [hd]
    fin_cases i
    simp [PDE.basisVec]
  have hh : diffusedHessian (reconstructionSpatialBarrier B T) p = 0 := by
    rw [diffusedHessian_eq_sliceHessian]
    change sliceHessian (fun _ : PDE.Vec 1 =>
      Real.exp (B * (T - p.time)) * reconstructionSpatialWeight (p.velocity 0)) p.position = 0
    exact sliceHessian_const _ p.position
  rw [transportedForwardOperator_apply, ht, hg, hh]
  simp [fullKineticCoefficientAt, matrixContraction, Matrix.zero_apply, PDE.vecDot, Fin.sum_univ_one, identityDrift]
  ring


/-- The spatial supersolution absorbs the proper exponential forcing on the native strip. -/
theorem reconstructionSpatialBarrier_operator_le (a : ℝ → ℝ → ℝ) (H : Interval)
    (T : ℝ) (p : Point)
    (hp : p ∈ evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T) :
    transportedForwardOperator (evolutionCoefficient a) (identityDrift 1)
      (reconstructionSpatialBarrier (max |H.lo| |H.hi| + 1) T) p ≤
        -reconstructionSpatialWeight (p.velocity 0)  := by
  have reconstruction_interval_abs_le {v : ℝ} (hv : H.lo ≤ v ∧ v ≤ H.hi) :
      |v| ≤ max |H.lo| |H.hi| := by
    apply abs_le.mpr
    constructor <;> linarith only [(neg_abs_le H.lo), (le_abs_self H.hi), (le_max_left |H.lo| |H.hi|), (le_max_right |H.lo| |H.hi|), hv.1, hv.2]
  let V := max |H.lo| |H.hi|
  have hV : 0 ≤ V := (abs_nonneg H.lo).trans (le_max_left _ _)
  have hv : H.lo ≤ p.position 0 ∧ p.position 0 ≤ H.hi := by
    have hi : p.position ∈ intervalDomain H := by
      simpa [mem_movingDomain_iff, PDE.mem_translateSet_iff_sub_mem] using hp.2
    exact intervalDomain_closure_bounds H (subset_closure hi)
  have hvb := abs_le.mp (reconstruction_interval_abs_le hv)
  have htr : p.position 0 * (Real.exp (p.velocity 0) - Real.exp (-p.velocity 0)) ≤
      V * reconstructionSpatialWeight (p.velocity 0) := by
    unfold reconstructionSpatialWeight
    nlinarith only [(mul_le_mul_of_nonneg_right hvb.2 (Real.exp_pos (p.velocity 0)).le), (mul_le_mul_of_nonneg_right hvb.1 (Real.exp_pos (-p.velocity 0)).le)]
  have hw : 0 ≤ reconstructionSpatialWeight (p.velocity 0) :=
    add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hex : 1 ≤ Real.exp ((V + 1) * (T - p.time)) :=
    Real.one_le_exp_iff.mpr (mul_nonneg (by linarith only [hV]) (sub_nonneg.mpr hp.1.le))
  rw [reconstructionSpatialBarrier_operator]
  calc
    _ ≤ Real.exp ((V + 1) * (T - p.time)) *
        (-(V + 1) * reconstructionSpatialWeight (p.velocity 0) +
          V * reconstructionSpatialWeight (p.velocity 0)) :=
      mul_le_mul_of_nonneg_left (add_le_add_right htr _) (Real.exp_pos _).le
    _ = -(Real.exp ((V + 1) * (T - p.time)) *
        reconstructionSpatialWeight (p.velocity 0)) := by ring
    _ ≤ -reconstructionSpatialWeight (p.velocity 0) := by
      simpa using neg_le_neg (mul_le_mul_of_nonneg_right hex hw)



/-- Signed smooth compact interior sources have continuous actual Duhamel potentials.
A smooth positive shift reduces this to the nonnegative source theorem. -/
theorem reconstruction_compact_duhamel_continuousOn
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (g : Point → ℝ)
    (hgs : ContDiff ℝ (⊤ : ℕ∞) (rawLift g)) (hgc : HasCompactSupport g)
    (hgU : tsupport g ⊆ evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T) :
    ContinuousOn (duhamelPotential E.2 T g)
      (evolutionPastClosedCylinder (intervalDomain H) (fun _ => 0) T) := by
  classical
  let D := evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T
  have hU := (isOpen_duhamelCylinder (γ := fun _ => 0) (isOpen_of_isAdmissibleEvolutionDomain (intervalDomain_admissible H)) continuous_const T).preimage (KineticPoint.homeomorphProd 1).symm.continuous
  have hgcont : Continuous g := by
    have hh := hgs.continuous.comp (KineticPoint.homeomorphProd 1).continuous
    exact hh
  obtain ⟨χ, hχ, hc, hs, hb, hone⟩ := exists_smooth_bump_of_isCompact_subset_isOpen (hgc.isCompact.image (KineticPoint.homeomorphProd 1).continuous) hU
    (by
      rintro x ⟨p, hp, rfl⟩
      change (KineticPoint.equivProd 1).symm (KineticPoint.equivProd 1 p) ∈ D
      simpa using hgU hp)
  let c := χ ∘ KineticPoint.equivProd 1
  have hcD : tsupport c ⊆ D := by
    intro p hp
    have hh := hs ((tsupport_comp_subset_preimage χ
      (KineticPoint.homeomorphProd 1).continuous) hp)
    change (KineticPoint.equivProd 1).symm (KineticPoint.equivProd 1 p) ∈ D at hh
    simpa using hh
  obtain ⟨B, hB⟩ := hgcont.bounded_above_of_compact_support hgc
  let C := max B 0
  have hC : 0 ≤ C := le_max_right _ _
  have hgb : ∀ p, |g p| ≤ C := by
    intro p
    have hh : |g p| ≤ B := by simpa using hB p
    exact hh.trans (le_max_left _ _)
  let f : BoundedBorel Point := ⟨g, hgcont.measurable, ⟨C, hC, hgb⟩⟩
  let b : BoundedBorel Point := ⟨fun p => C * c p,
    measurable_const.mul (hχ.continuous.comp (KineticPoint.homeomorphProd 1).continuous).measurable, ⟨C, hC, fun p => by
      change |C * χ (KineticPoint.equivProd 1 p)| ≤ C
      rw [abs_mul, abs_of_nonneg hC, abs_of_nonneg (hb _).1]
      exact mul_le_of_le_one_right hC (hb _).2⟩⟩
  have hb0 : ∀ p, 0 ≤ b p := fun p => mul_nonneg hC (hb _).1
  have hfb0 : ∀ p, 0 ≤ (f + b) p := by
    intro p
    change 0 ≤ g p + C * c p
    by_cases hp : g p = 0
    · rw [hp, zero_add]
      exact hb0 p
    · have hcp : c p = 1 := hone _ ⟨p, subset_tsupport _ hp, rfl⟩
      rw [hcp, mul_one]
      linarith only [neg_abs_le (g p), hgb p]
  have hbs : ContDiff ℝ (⊤ : ℕ∞) (rawLift b) := contDiff_const.mul (hχ)
  have hbc : HasCompactSupport (b : Point → ℝ) := (hc.comp_homeomorph (KineticPoint.homeomorphProd 1)).mul_left
  have hbD : tsupport (b : Point → ℝ) ⊆ D :=
    (tsupport_mul_subset_right).trans hcD
  have hfbD :=
    (tsupport_add _ _).trans (union_subset hgU hbD)
  have hcont (u : Point → ℝ) (hu0 : ∀ p, 0 ≤ u p)
      (hus : ContDiff ℝ (⊤ : ℕ∞) (rawLift u)) (huc : HasCompactSupport u)
      (huD : tsupport u ⊆ D) : ContinuousOn (duhamelPotential E.2 T u)
        (evolutionPastClosedCylinder (intervalDomain H) (fun _ => 0) T) := by
    obtain ⟨-, -, -, -, -, hcont, -⟩ :=
      kinetic_duhamel hH (by omega) (intervalDomain_admissible H) (zeroCurve_piecewiseC1 1)
        hlam hLam one_pos (evolutionCoefficient A.a) (evolutionCoefficient_smooth A)
        (evolutionCoefficient_symmetric A.a) (evolutionCoefficient_bounds A)
        (identityDrift 1) (identityDrift_smooth 1) (identityDrift_bounds 1)
        E.1 E.2 hE T u hu0 hus huc huD
    exact hcont
  have hh := (hcont (f + b) hfb0 (hgs.add hbs) (hgc.add hbc) hfbD).sub (hcont b hb0 hbs hbc hbD)
  apply hh.congr
  intro p _
  have hs := strip_duhamel_sub H E.2 (f + b) b p T
  rw [add_sub_cancel_right] at hs
  exact hs


/-- Multiplying a locally continuous source by an interior compact cutoff is continuous. -/
theorem reconstruction_cutoff_mul_continuous
    {V : Set (ℝ × PDE.Vec 1 × PDE.Vec 1)} (hV : IsOpen V)
    {g χ : (ℝ × PDE.Vec 1 × PDE.Vec 1) → ℝ}
    (hg : ContinuousOn g V) (hχ : Continuous χ) (hs : tsupport χ ⊆ V) :
    Continuous (fun x => χ x * g x) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ V
  · exact hχ.continuousAt.mul (hg.continuousAt (hV.mem_nhds hx))
  · have ht : x ∈ (tsupport χ)ᶜ := fun hh => hx (hs hh)
    apply (show ContinuousAt (fun _ : ℝ × PDE.Vec 1 × PDE.Vec 1 => (0 : ℝ)) x
      from continuousAt_const).congr
    filter_upwards [(isClosed_tsupport χ |>.isOpen_compl.mem_nhds ht)] with y hy
    have hz : χ y = 0 := by
      by_contra hh
      exact hy (subset_tsupport χ hh)
    simp [hz]

/-- A continuous compact interior function admits a smooth compact interior approximation. -/
theorem reconstruction_smooth_compact_close
    {V : Set (ℝ × PDE.Vec 1 × PDE.Vec 1)} (hV : IsOpen V)
    (g : (ℝ × PDE.Vec 1 × PDE.Vec 1) → ℝ) (hg : Continuous g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ V)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : (ℝ × PDE.Vec 1 × PDE.Vec 1) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ tsupport f ⊆ V ∧
      ∀ x, |f x - g x| ≤ ε := by
  obtain ⟨ψ, hψ, hψc, hψs, hb, hone⟩ :=
    exists_smooth_bump_of_isCompact_subset_isOpen hc.isCompact hV hs
  let G : C_c(ℝ × PDE.Vec 1 × PDE.Vec 1, ℝ) := ⟨⟨g, hg⟩, hc⟩
  obtain ⟨f, hf, hclose⟩ := exists_smooth_compact_probe_close G ε hε
  refine ⟨fun x => ψ x * f x, hψ.mul hf, hψc.mul_right,
    tsupport_mul_subset_left.trans hψs, fun x => ?_⟩
  have hpg : ψ x * g x = g x := by
    by_cases hx : g x = 0
    · simp [hx]
    · rw [hone x (subset_tsupport _ hx), one_mul]
  have heq : ψ x * f x - g x = ψ x * (f x - g x) := by rw [mul_sub, hpg]
  rw [heq, abs_mul, abs_of_nonneg (hb x).1]
  exact (mul_le_of_le_one_left (abs_nonneg _) (hb x).2).trans (hclose x)

/-- Closed scalar truncation, embedded in native product coordinates. -/
def reconstructionTrim (H : Interval) (a T δ R : ℝ) :
    Set (ℝ × PDE.Vec 1 × PDE.Vec 1) :=
  (fun q : ℝ × ℝ × ℝ => (q.1, (fun _ : Fin 1 => q.2.1),
    (fun _ : Fin 1 => q.2.2))) ''
      (Icc a (T - δ) ×ˢ (Icc (H.lo + δ) (H.hi - δ) ×ˢ Icc (-R) R))



/-- Interior source domain in native product coordinates. -/
def reconstructionSourceDomain (H : Interval) (sMinus T : ℝ) :
    Set (ℝ × PDE.Vec 1 × PDE.Vec 1) :=
  {x | sMinus < x.1 ∧ x.1 < T ∧ x.2.1 0 ∈ H.carrier}


/-- The proper exponential weight bounds the absolute spatial coordinate. -/
theorem abs_le_reconstructionSpatialWeight (x : ℝ) :
    |x| ≤ reconstructionSpatialWeight x := by
  unfold reconstructionSpatialWeight
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    linarith only [(Real.add_one_le_exp x), ((Real.exp_pos (-x)).le)]
  · rw [abs_of_nonpos hx]
    linarith only [(Real.add_one_le_exp (-x)), ((Real.exp_pos x).le)]

/-- The localization error weight, including terminal, velocity, and spatial collars. -/
def reconstructionErrorWeight (H : Interval) (T δ R : ℝ)
    (x : ℝ × PDE.Vec 1 × PDE.Vec 1) : ℝ :=
  Real.exp 1 * reconstructionCollarWeight H δ (x.2.1 0) +
    (if T - δ < x.1 then 1 else 0) + reconstructionSpatialWeight (x.2.2 0) / R


/-- Bounded continuous strip sources have actual smooth compact approximants with an
explicit pointwise collar error. -/
theorem exists_reconstruction_compact_source_approx
    (H : Interval) (sMinus a T : ℝ) (ha : sMinus < a) {δ R ε : ℝ}
    (hδ : 0 < δ) (hR : 0 < R) (hε : 0 < ε)
    (g : (ℝ × PDE.Vec 1 × PDE.Vec 1) → ℝ)
    (hg : ContinuousOn g (reconstructionSourceDomain H sMinus T))
    (C : ℝ) (hC : 0 ≤ C) (hgb : ∀ x, |g x| ≤ C) :
    ∃ f : (ℝ × PDE.Vec 1 × PDE.Vec 1) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
      tsupport f ⊆ reconstructionSourceDomain H sMinus T ∧
      ∀ x, a ≤ x.1 →
        |f x - g x| ≤ ε + C * reconstructionErrorWeight H T δ R x     := by
  have mem_reconstructionTrim (a T δ R : ℝ) (x : ℝ × PDE.Vec 1 × PDE.Vec 1) :
      x ∈ reconstructionTrim H a T δ R ↔
      a ≤ x.1 ∧ x.1 ≤ T - δ ∧ H.lo + δ ≤ x.2.1 0 ∧
        x.2.1 0 ≤ H.hi - δ ∧ |x.2.2 0| ≤ R := by
    constructor
    · rintro ⟨q, ⟨ht, hv, hx⟩, rfl⟩
      exact ⟨ht.1, ht.2, hv.1, hv.2, abs_le.mpr hx⟩
    · rintro ⟨htl, htu, hvl, hvu, hx⟩
      refine ⟨(x.1, x.2.1 0, x.2.2 0), ⟨⟨htl, htu⟩, ⟨hvl, hvu⟩, abs_le.mp hx⟩, ?_⟩
      change (x.1, (fun _ : Fin 1 => x.2.1 0), (fun _ : Fin 1 => x.2.2 0)) = x
      refine Prod.ext rfl (Prod.ext ?_ ?_) <;> (funext i; fin_cases i; rfl)
  have reconstructionErrorWeight_ge_one {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) (x : ℝ × PDE.Vec 1 × PDE.Vec 1) (ha : a ≤ x.1) (hx : x ∉ reconstructionTrim H a T δ R) :
      1 ≤ reconstructionErrorWeight H T δ R x := by
    classical
    have hcol : 0 ≤ Real.exp 1 * reconstructionCollarWeight H δ (x.2.1 0) :=
      mul_nonneg (Real.exp_pos _).le (reconstructionCollarWeight_nonneg _ _ _)
    have hsp : 0 ≤ reconstructionSpatialWeight (x.2.2 0) / R :=
      div_nonneg (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) hR.le
    unfold reconstructionErrorWeight
    by_cases ht : T - δ < x.1
    · rw [ite_eq_left ht]
      linarith only [hcol, hsp]
    · rw [ite_eq_right ht, add_zero]
      have htu := le_of_not_gt ht
      by_cases hl : H.lo + δ ≤ x.2.1 0
      · by_cases hh : x.2.1 0 ≤ H.hi - δ
        · have hs : R < |x.2.2 0| := lt_of_not_ge
            (fun hs => hx ((mem_reconstructionTrim a T δ R x).mpr ⟨ha, htu, hl, hh, hs⟩))
          have hd : 1 ≤ reconstructionSpatialWeight (x.2.2 0) / R :=
            (le_div_iff₀ hR).mpr (by
              simpa using hs.le.trans (abs_le_reconstructionSpatialWeight _))
          linarith only [hcol, hd]
        · have hs : H.hi - δ < x.2.1 0 := lt_of_not_ge hh
          have hd : -1 ≤ (x.2.1 0 - H.hi) / δ :=
            (le_div_iff₀ hδ).mpr (by linarith only [hs])
          have he : 1 ≤ Real.exp 1 * Real.exp ((x.2.1 0 - H.hi) / δ) := by
            rw [← Real.exp_add]
            exact Real.one_le_exp_iff.mpr (by linarith only [hd])
          have hn := mul_nonneg (Real.exp_pos 1).le
            (Real.exp_pos ((H.lo - x.2.1 0) / δ)).le
          unfold reconstructionCollarWeight
          nlinarith only [he, hn, hsp]
      · have hs : x.2.1 0 < H.lo + δ := lt_of_not_ge hl
        have hd : -1 ≤ (H.lo - x.2.1 0) / δ :=
          (le_div_iff₀ hδ).mpr (by linarith only [hs])
        have he : 1 ≤ Real.exp 1 * Real.exp ((H.lo - x.2.1 0) / δ) := by
          rw [← Real.exp_add]
          exact Real.one_le_exp_iff.mpr (by linarith only [hd])
        unfold reconstructionCollarWeight
        nlinarith only [he, (mul_nonneg (Real.exp_pos 1).le (Real.exp_pos ((x.2.1 0 - H.hi) / δ)).le), hsp]
  have isOpen_reconstructionSourceDomain :
      IsOpen (reconstructionSourceDomain H sMinus T) := by
    have heq : reconstructionSourceDomain H sMinus T =
        (Prod.fst ⁻¹' Ioo sMinus T) ∩
          ((fun x : ℝ × PDE.Vec 1 × PDE.Vec 1 => x.2.1 0) ⁻¹' H.carrier) := by
      ext x
      simp [reconstructionSourceDomain, mem_ofPred, and_assoc]
    rw [heq]
    exact (isOpen_Ioo.preimage continuous_fst).inter
      (isOpen_Ioo.preimage ((continuous_apply 0).comp continuous_snd.fst))
  have isCompact_reconstructionTrim (a T δ R : ℝ) : IsCompact (reconstructionTrim H a T δ R) :=
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).image
        (continuous_fst.prodMk ((continuous_pi fun _ => continuous_snd.fst).prodMk
          (continuous_pi fun _ => continuous_snd.snd)))
  have hU := isOpen_reconstructionSourceDomain
  have hKU : reconstructionTrim H a T δ R ⊆ reconstructionSourceDomain H sMinus T := by
    intro x hx
    obtain ⟨htl, htu, hvl, hvu, _⟩ := (mem_reconstructionTrim a T δ R x).mp hx
    exact ⟨ha.trans_le htl, by linarith only [htu, hδ],
      by constructor <;> linarith only [hvl, hvu, hδ]⟩
  obtain ⟨χ, hχ, hc, hs, hb, hone⟩ := exists_smooth_bump_of_isCompact_subset_isOpen
    (isCompact_reconstructionTrim a T δ R) hU hKU
  have hcomp : HasCompactSupport (fun x => χ x * g x) := hc.mul_right
  obtain ⟨f, hf, hfc, hfs, hclose⟩ := reconstruction_smooth_compact_close hU
    (fun x => χ x * g x) (reconstruction_cutoff_mul_continuous hU hg hχ.continuous hs) hcomp (tsupport_mul_subset_left.trans hs) hε
  refine ⟨f, hf, hfc, hfs, fun x hax => ?_⟩
  have hweight : 0 ≤ reconstructionErrorWeight H T δ R x := by
    unfold reconstructionErrorWeight
    exact add_nonneg (add_nonneg
      (mul_nonneg (Real.exp_pos _).le (reconstructionCollarWeight_nonneg _ _ _))
      (by split_ifs <;> norm_num))
      (div_nonneg (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) hR.le)
  have herror : |χ x * g x - g x| ≤ C * reconstructionErrorWeight H T δ R x := by
    by_cases hx : x ∈ reconstructionTrim H a T δ R
    · rw [hone _ hx, one_mul, sub_self, abs_zero]
      exact mul_nonneg hC hweight
    · have he : χ x * g x - g x = -(1 - χ x) * g x := by ring
      rw [he, abs_mul, abs_neg, abs_of_nonneg (sub_nonneg.mpr (hb x).2)]
      have hh : (1 - χ x) * |g x| ≤ C :=
        (mul_le_of_le_one_left (abs_nonneg _) (by linarith only [(hb x).1])).trans (hgb x)
      exact hh.trans (le_mul_of_one_le_right hC
        (reconstructionErrorWeight_ge_one hδ hR x hax hx))
  have heq : f x - g x = (f x - χ x * g x) + (χ x * g x - g x) := by ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add (hclose x) herror)


/-- Every Green source time is strictly later than its pole time. -/
theorem reconstruction_green_ae_time_gt (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (T : ℝ)
    (e : StripPole H (T : WithTop ℝ)) :
    ∀ᵐ p ∂stripGreenOfKernel H K T e, e.1.time < p.time := by
  unfold stripGreenOfKernel
  apply (ae_map_iff (measurable_elapsedPhysicalPoint _ _).aemeasurable
    (measurableSet_lt measurable_const continuous_time.measurable)).2
  exact Eventually.of_forall fun q => by
    change e.1.time < e.1.time + q.1.1
    exact lt_add_of_pos_right _ q.1.2.1







/-- A pointwise source approximation gives an explicit actual potential approximation. -/
theorem reconstruction_green_potential_error
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T a : ℝ) (e : StripPole H (T : WithTop ℝ))
    (ha : a ≤ e.1.time) (g f : BoundedBorel Point) (C : ℝ) (hC : 0 ≤ C)
    {δ R ε : ℝ} (hδ : 0 < δ) (hR : 0 < R) (hε : 0 ≤ ε)
    (hgf : ∀ p, a ≤ p.time → |g p - f p| ≤ ε + C * reconstructionErrorWeight H T δ R
      (KineticPoint.equivProd 1 (sectionTwoPoint p))) :
    |stripPotentialOfKernel H E.2 T g e - stripPotentialOfKernel H E.2 T f e| ≤
      ε * (T - e.1.time) + C * (Real.exp 1 * (2 * δ ^ 2 / lam) + δ +
        (Real.exp ((max |H.lo| |H.hi| + 1) * (T - e.1.time)) *
          reconstructionSpatialWeight (e.1.position 0)) / R)        := by
  have reconstruction_green_spatial_weight_bound :
      ∫⁻ p, ENNReal.ofReal (reconstructionSpatialWeight (p.position 0))
        ∂stripGreenOfKernel H E.2 T e ≤
      ENNReal.ofReal (Real.exp ((max |H.lo| |H.hi| + 1) * (T - e.1.time)) *
        reconstructionSpatialWeight (e.1.position 0)) := by
    have reconstruction_green_lintegral_le_barrier (k : Point → ℝ) (q : Point → ℝ) (hk : ContDiff ℝ (⊤ : ℕ∞) (rawLift k)) (hkn : ∀ p, 0 ≤ k p) (hqc : Continuous q) (hqr : ∀ p, IsSliceRegularAt q p) (hqn : ∀ p ∈ evolutionPastClosedCylinder (intervalDomain H) (fun _ => 0) T, 0 ≤ q p) (hqo : ∀ p ∈ evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T,
        transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1)
        q p ≤ -k p) :
        ∫⁻ p, ENNReal.ofReal (k (sectionTwoPoint p)) ∂stripGreenOfKernel H E.2 T e ≤
        ENNReal.ofReal (q (sectionTwoPoint e.1)) := by
      classical
      let D := evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T
      let U := (KineticPoint.equivProd 1).symm ⁻¹' D
      have hU := (isOpen_duhamelCylinder (γ := fun _ => 0) (isOpen_of_isAdmissibleEvolutionDomain (intervalDomain_admissible H)) continuous_const T).preimage (KineticPoint.homeomorphProd 1).symm.continuous
      obtain ⟨χ, hχ, hb, hmono, hcover⟩ := exists_increasing_smooth_interior_cutoffs hU
      let g (n : ℕ) (p : Point) : ℝ :=
        χ n (KineticPoint.equivProd 1 p) * k p
      have hgc (n : ℕ) : HasCompactSupport (g n) :=
        ((hχ n).2.1.comp_homeomorph (KineticPoint.homeomorphProd 1)).mul_right
      have hgs (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (rawLift (g n)) :=
        (hχ n).1.mul hk
      have hgcont (n : ℕ) : Continuous (g n) :=
        ((hχ n).1.continuous.comp (KineticPoint.homeomorphProd 1).continuous).mul
          (hk.continuous.comp (KineticPoint.homeomorphProd 1).continuous)
      have hgn (n : ℕ) (p : Point) : 0 ≤ g n p := mul_nonneg (hb n _).1 (hkn _)
      have hgD (n : ℕ) : tsupport (g n) ⊆ D := by
        intro p hp
        have hy := (tsupport_comp_subset_preimage (χ n)
          (KineticPoint.homeomorphProd 1).continuous) (tsupport_mul_subset_left hp)
        have hu := (hχ n).2.2 hy
        change (KineticPoint.equivProd 1).symm (KineticPoint.equivProd 1 p) ∈ D at hu
        simpa using hu
      have hgb (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ p, |g n p| ≤ C := by
        obtain ⟨B, hB⟩ := (hgcont n).bounded_above_of_compact_support (hgc n)
        refine ⟨max B 0, le_max_right _ _, fun p => ?_⟩
        have hh : |g n p| ≤ B := by simpa using hB p
        exact hh.trans (le_max_left _ _)
      let F (n : ℕ) : BoundedBorel Point :=
        ⟨g n ∘ sectionTwoPoint,
          (hgcont n).measurable.comp (continuous_sectionTwoPoint 1).measurable, by
            obtain ⟨C, hC, hh⟩ := hgb n
            exact ⟨C, hC, fun p => hh (sectionTwoPoint p)⟩⟩
      have hbound (n : ℕ) : stripPotentialOfKernel H E.2 T (F n) e ≤ q (sectionTwoPoint e.1) := by
        have heT := WithTop.coe_lt_coe.mp e.2.1
        let p := sectionTwoPoint e.1
        have hp : p ∈ D := ⟨heT, (stripPoleState H T e).2.1⟩
        have hIeq : stripPotentialOfKernel H E.2 T (F n) e = duhamelPotential E.2 T (g n) p := by
          rw [stripPotentialOfKernel, stripGreenOfKernel,
            integral_map (measurable_elapsedPhysicalPoint _ _).aemeasurable
              (F n).measurable.aestronglyMeasurable]
          exact (duhamelPotential_eq_greenMeasure E.2 (intervalDomain_measurable H) continuous_const T (g n) (hgn n) (hgcont n) (hgc n) e.1.time heT (stripPoleState H T e)).symm
        rw [hIeq]
        exact reconstruction_duhamel_le_barrier hH hlam hLam A H E hE T (g n) q (hgn n) (hgs n) (hgc n) (hgD n) hqc hqr hqn (fun z hz => (hqo z hz).trans (neg_le_neg (mul_le_of_le_one_left (hkn _) (hb n _).2))) p hp
      have hfun : (fun p => ENNReal.ofReal (k (sectionTwoPoint p))) =ᵐ[
          stripGreenOfKernel H E.2 T e] fun p => ⨆ n, ENNReal.ofReal (F n p) := by
        filter_upwards [stripGreenOfKernel_ae_mem_stripPast H E.2 T e] with p hp
        have hnp : sectionTwoPoint p ∈ D := by
          refine ⟨hp.1, ?_⟩
          apply PDE.mem_translateSet_iff_sub_mem.mpr
          simpa [intervalDomain, PDE.mem_oneDimensionalAxisBox_iff, PDE.vecOneCoordinate, sectionTwoPoint, Interval.carrier] using hp.2
        have hnU : KineticPoint.equivProd 1 (sectionTwoPoint p) ∈ U := by
          simpa [U, Equiv.symm_apply_apply] using hnp
        obtain ⟨N, hN⟩ := hcover _ hnU
        apply le_antisymm
        · apply le_iSup_of_le N
          change ENNReal.ofReal (k (sectionTwoPoint p)) ≤
            ENNReal.ofReal (χ N (KineticPoint.equivProd 1 (sectionTwoPoint p)) *
              k (sectionTwoPoint p))
          rw [hN N le_rfl, one_mul]
        · apply iSup_le
          intro n
          exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left (hkn _) (hb n _).2)
      rw [lintegral_congr_ae hfun, lintegral_iSup]
      · apply iSup_le
        intro n
        rw [← ofReal_integral_eq_lintegral_ofReal (stripGreen_integrable_boundedBorel H E.2 T e (F n))
          (Eventually.of_forall (fun p => hgn n (sectionTwoPoint p)))]
        exact ENNReal.ofReal_le_ofReal (hbound n)
      · intro n
        exact (F n).measurable.ennreal_ofReal
      · intro i j hij p
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hmono _ hij) (hkn _))
    exact reconstruction_green_lintegral_le_barrier
      (fun p => reconstructionSpatialWeight (p.velocity 0))
      (reconstructionSpatialBarrier (max |H.lo| |H.hi| + 1) T)
      (reconstructionSpatialWeight_smooth.comp
        ((contDiff_apply ℝ ℝ 0).comp contDiff_snd.snd))
      (fun p => add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      (reconstructionSpatialBarrier_continuous _ _)
      (reconstructionSpatialBarrier_regular _ _)
      (fun p _ => mul_nonneg (Real.exp_pos _).le
        (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))
      (reconstructionSpatialBarrier_operator_le A.a H T)
  have reconstructionCollarWeight_smooth (δ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (reconstructionCollarWeight H δ) :=
    ((contDiff_const.sub contDiff_id).div_const δ).exp.add
        ((contDiff_id.sub contDiff_const).div_const δ).exp
  have reconstruction_green_collar_integrable (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) {δ : ℝ} (hδ : 0 < δ) :
      Integrable (fun p => reconstructionCollarWeight H δ (p.velocity 0))
      (stripGreenOfKernel H K T e) := by
    have hm : Continuous (fun p : Point => reconstructionCollarWeight H δ (p.velocity 0)) :=
      (reconstructionCollarWeight_smooth δ).continuous.comp
        ((continuous_apply 0).comp continuous_velocity)
    apply (integrable_const 2).mono' hm.measurable.aestronglyMeasurable
    filter_upwards [stripGreenOfKernel_ae_mem_stripPast H K T e] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (reconstructionCollarWeight_nonneg _ _ _)]
    exact reconstructionCollarWeight_le_two H hδ ⟨hp.2.1.le, hp.2.2.le⟩
  have reconstruction_green_spatial_integrable :
      Integrable (fun p => reconstructionSpatialWeight (p.position 0))
      (stripGreenOfKernel H E.2 T e) := by
    have hm : Continuous (fun p : Point => reconstructionSpatialWeight (p.position 0)) :=
      reconstructionSpatialWeight_smooth.continuous.comp
        ((continuous_apply 0).comp continuous_position)
    refine ⟨hm.measurable.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun p => add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)).mpr ?_⟩
    exact lt_of_le_of_lt
      (reconstruction_green_spatial_weight_bound)
      ENNReal.ofReal_lt_top
  have reconstruction_green_collar_bound {δ : ℝ} (hδ : 0 < δ) :
      ∫ p, reconstructionCollarWeight H δ (p.velocity 0) ∂stripGreenOfKernel H E.2 T e ≤
      2 * δ ^ 2 / lam := open Parabolic in by
    have collar_right_deriv (δ v : ℝ) :
        HasDerivAt (fun w => Real.exp ((w - H.hi) / δ))
        (Real.exp ((v - H.hi) / δ) * (1 / δ)) v := by
      simpa using!
        (((hasDerivAt_id v).sub (hasDerivAt_const v H.hi)).div_const δ).exp
    have collar_left_deriv (δ v : ℝ) :
        HasDerivAt (fun w => Real.exp ((H.lo - w) / δ))
        (Real.exp ((H.lo - v) / δ) * (-1 / δ)) v := by
      simpa using!
        (((hasDerivAt_const v H.lo).sub (hasDerivAt_id v)).div_const δ).exp
    have reconstructionCollarProfile_smooth (lam δ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (reconstructionCollarProfile H lam δ) :=
      contDiff_const.mul (contDiff_const.sub
          (((contDiff_const.sub contDiff_id).div_const δ).exp.add
            ((contDiff_id.sub contDiff_const).div_const δ).exp))
    let a := A.a
    have reconstructionProfile_operator {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (p : Point) :
        transportedForwardOperator (evolutionCoefficient a) (SectionTwo.identityDrift 1)
        (reconstructionProfile f) p = a (p.velocity 0) (p.position 0) *
          deriv (deriv f) (p.position 0) := by
      have profile_hessian (y : PDE.Vec 1) :
          sliceHessian (fun z : PDE.Vec 1 => f (z 0)) y 0 0 = deriv (deriv f) (y 0) := by
        have profile_gradient {f : ℝ → ℝ} (hf : Differentiable ℝ f) (y : PDE.Vec 1) :
            PDE.classicalGradient (fun z : PDE.Vec 1 => f (z 0)) y =
            fun _ => deriv f (y 0) := by
          ext i
          have h := (hf (y 0)).hasDerivAt.comp_hasFDerivAt y (hasFDerivAt_apply (𝕜 := ℝ) 0 y)
          change fderiv ℝ (fun z : PDE.Vec 1 => f (z 0)) y (PDE.basisVec i) = _
          have hd : fderiv ℝ (fun z : PDE.Vec 1 => f (z 0)) y =
              deriv f (y 0) • ContinuousLinearMap.proj 0 := by
            simpa only [Function.comp_def] using! h.fderiv
          rw [hd]
          fin_cases i
          simp [PDE.basisVec]
        have hg : (fun z => PDE.classicalGradient (fun w : PDE.Vec 1 => f (w 0)) z) =
            fun z _ => deriv f (z 0) :=
          funext (profile_gradient (hf.differentiable (by norm_num)))
        have h := (hf.differentiable_deriv_two (y 0)).hasDerivAt.comp_hasFDerivAt y
          (hasFDerivAt_apply (𝕜 := ℝ) 0 y)
        have hp := hasFDerivAt_pi.mpr (fun _ : Fin 1 => h)
        unfold sliceHessian
        rw [hg]
        have hd : fderiv ℝ (fun z : PDE.Vec 1 => fun _ : Fin 1 => deriv f (z 0)) y =
            ContinuousLinearMap.pi (fun _ : Fin 1 =>
              deriv (deriv f) (y 0) • ContinuousLinearMap.proj 0) := by
          simpa only [Function.comp_def] using! hp.fderiv
        rw [hd]
        simp [PDE.basisVec]
      have hg : kineticVelocityGradient (reconstructionProfile f) p = 0 := by
        ext i
        change fderiv ℝ (fun _ : PDE.Vec 1 => f (p.position 0)) p.velocity (PDE.basisVec i) = 0
        rw [(hasFDerivAt_const (f (p.position 0)) p.velocity).fderiv]
        rfl
      rw [transportedForwardOperator_apply, hg]
      simp [kineticTimeDerivative, reconstructionProfile, deriv_const, PDE.vecDot]
      rw [diffusedHessian_eq_sliceHessian]
      simp only [fullKineticCoefficientAt, evolutionCoefficient, matrixContraction,
        Fin.sum_univ_one, reconstructionProfile]
      rw [profile_hessian]
    have reconstruction_green_le_profile (k : ℝ → ℝ) (q : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C) (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hkn : ∀ v, 0 ≤ k v) (hkb : ∀ v ∈ H.carrier, k v ≤ C) (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hqn : ∀ v, H.lo ≤ v → v ≤ H.hi → 0 ≤ q v) (hqo : ∀ p, transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1)
        (reconstructionProfile q) p ≤ -k (p.position 0)) :
        ∫ p, k (p.velocity 0) ∂stripGreenOfKernel H E.2 T e ≤ q (e.1.velocity 0) := by
      classical
      let D := evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T
      let U := (KineticPoint.equivProd 1).symm ⁻¹' D
      have hD : IsOpen D := isOpen_duhamelCylinder
        (γ := fun _ => 0) (isOpen_of_isAdmissibleEvolutionDomain (intervalDomain_admissible H))
        continuous_const T
      have hU : IsOpen U := hD.preimage (KineticPoint.homeomorphProd 1).symm.continuous
      obtain ⟨χ, hχ, hb, -, hcover⟩ := exists_increasing_smooth_interior_cutoffs hU
      let g (n : ℕ) (p : Point) : ℝ :=
        χ n (KineticPoint.equivProd 1 p) * k (p.position 0)
      have hgc (n : ℕ) : HasCompactSupport (g n) :=
        ((hχ n).2.1.comp_homeomorph (KineticPoint.homeomorphProd 1)).mul_right
      have hgs (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (rawLift (g n)) :=
        (hχ n).1.mul (hk.comp ((contDiff_apply ℝ ℝ (0 : Fin 1)).comp contDiff_snd.fst))
      have hgcont (n : ℕ) : Continuous (g n) :=
        ((hχ n).1.continuous.comp (KineticPoint.homeomorphProd 1).continuous).mul
          (reconstructionProfile_continuous hk.continuous)
      have hgn (n : ℕ) (p : Point) : 0 ≤ g n p := mul_nonneg (hb n _).1 (hkn _)
      have hgD (n : ℕ) : tsupport (g n) ⊆ D := by
        intro p hp
        have hy := (tsupport_comp_subset_preimage (χ n)
          (KineticPoint.homeomorphProd 1).continuous) (tsupport_mul_subset_left hp)
        have hu := (hχ n).2.2 hy
        change (KineticPoint.equivProd 1).symm (KineticPoint.equivProd 1 p) ∈ D at hu
        simpa only [Equiv.symm_apply_apply] using hu
      have hgb (n : ℕ) (p : Point) : |g n p| ≤ C := by
        rw [abs_of_nonneg (hgn n p)]
        by_cases hz : g n p = 0
        · simpa only [hz] using hC
        · have hp := hgD n (subset_tsupport _ hz)
          have hv : p.position 0 ∈ H.carrier := by
            simpa [mem_movingDomain_iff, PDE.mem_translateSet_iff_sub_mem, intervalDomain, PDE.mem_oneDimensionalAxisBox_iff, PDE.vecOneCoordinate, Interval.carrier] using hp.2
          exact (mul_le_of_le_one_left (hkn _) (hb n _).2).trans (hkb _ hv)
      let F (n : ℕ) : BoundedBorel Point :=
        ⟨g n ∘ sectionTwoPoint,
          (hgcont n).measurable.comp (continuous_sectionTwoPoint 1).measurable,
          ⟨C, hC, fun p => hgb n _⟩⟩
      let K : BoundedBorel Point :=
        ⟨fun p => if p.velocity 0 ∈ H.carrier then k (p.velocity 0) else 0,
          (hk.continuous.measurable.comp ((continuous_apply 0).comp
            continuous_velocity).measurable).piecewise
            (isOpen_Ioo.measurableSet.preimage
              ((continuous_apply 0).comp continuous_velocity).measurable) measurable_const,
          ⟨C, hC, fun p => by
            dsimp only
            split_ifs with hp
            · rw [abs_of_nonneg (hkn _)]
              exact hkb _ hp
            · simpa using hC⟩⟩
      have hlim : ∀ᵐ p ∂stripGreenOfKernel H E.2 T e,
          Tendsto (fun n => F n p) atTop (𝓝 (K p)) := by
        filter_upwards [stripGreenOfKernel_ae_mem_stripPast H E.2 T e] with p hp
        have hnp : sectionTwoPoint p ∈ D := by
          refine ⟨hp.1, ?_⟩
          apply PDE.mem_translateSet_iff_sub_mem.mpr
          simpa [intervalDomain, PDE.mem_oneDimensionalAxisBox_iff, PDE.vecOneCoordinate, sectionTwoPoint, Interval.carrier] using hp.2
        have hnU : KineticPoint.equivProd 1 (sectionTwoPoint p) ∈ U := by
          simpa [U, Equiv.symm_apply_apply] using hnp
        obtain ⟨N, hN⟩ := hcover _ hnU
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop N] with n hn
        change K p = χ n (KineticPoint.equivProd 1 (sectionTwoPoint p)) *
          k ((sectionTwoPoint p).position 0)
        change (if p.velocity 0 ∈ H.carrier then k (p.velocity 0) else 0) =
          χ n (KineticPoint.equivProd 1 (sectionTwoPoint p)) * k (p.velocity 0)
        rw [ite_eq_left hp.2, hN n hn, one_mul]
      have hbound (n : ℕ) : stripPotentialOfKernel H E.2 T (F n) e ≤ q (e.1.velocity 0) := by
        have heT : e.1.time < T := WithTop.coe_lt_coe.mp e.2.1
        let p := sectionTwoPoint e.1
        have hp : p ∈ D := ⟨heT, (stripPoleState H T e).2.1⟩
        have hcmp := reconstruction_duhamel_le_barrier hH hlam hLam A H E hE T (g n)
          (reconstructionProfile q) (hgn n) (hgs n) (hgc n) (hgD n)
          (reconstructionProfile_continuous hq.continuous)
          (reconstructionProfile_regular (hq.of_le (by simp)))
          (fun z hz => by
            have hv := intervalDomain_closure_bounds H
              (by simpa [mem_closure_movingDomain_iff] using hz.2)
            exact hqn _ hv.1 hv.2)
          (fun z _ => (hqo z).trans (neg_le_neg
            (mul_le_of_le_one_left (hkn _) (hb n _).2))) p hp
        have hIeq : stripPotentialOfKernel H E.2 T (F n) e = duhamelPotential E.2 T (g n) p := by
          rw [stripPotentialOfKernel, stripGreenOfKernel,
            integral_map (measurable_elapsedPhysicalPoint _ _).aemeasurable
              (F n).measurable.aestronglyMeasurable]
          exact (duhamelPotential_eq_greenMeasure E.2 (intervalDomain_measurable H) continuous_const T (g n) (hgn n) (hgcont n) (hgc n) e.1.time heT (stripPoleState H T e)).symm
        rw [hIeq]
        exact hcmp
      have hle := le_of_tendsto (stripPotentialOfKernel_tendsto H E.2 T e F K C (fun n p => hgb n _) hlim) (Eventually.of_forall hbound)
      have heq : stripPotentialOfKernel H E.2 T K e =
          ∫ p, k (p.velocity 0) ∂stripGreenOfKernel H E.2 T e := by
        apply integral_congr_ae
        filter_upwards [stripGreenOfKernel_ae_mem_stripPast H E.2 T e] with p hp
        change (if p.velocity 0 ∈ H.carrier then k (p.velocity 0) else 0) = _
        exact ite_eq_left hp.2
      rwa [heq] at hle
    have reconstructionCollarProfile_operator_le {δ : ℝ} (hδ : 0 < δ) (p : Point) :
        transportedForwardOperator (evolutionCoefficient A.a) (SectionTwo.identityDrift 1)
        (reconstructionProfile (reconstructionCollarProfile H lam δ)) p ≤
          -reconstructionCollarWeight H δ (p.position 0) := by
      have reconstructionCollarProfile_secondDeriv {δ : ℝ} (hδ : 0 < δ) (v : ℝ) :
          deriv (deriv (reconstructionCollarProfile H lam δ)) v =
          -reconstructionCollarWeight H δ v / lam := by
        have collar_profile_deriv (lam δ v : ℝ) :
            deriv (reconstructionCollarProfile H lam δ) v =
            δ ^ 2 / lam * (Real.exp ((H.lo - v) / δ) - Real.exp ((v - H.hi) / δ)) / δ := by
          have h := ((hasDerivAt_const v (2 : ℝ)).sub
            ((collar_left_deriv δ v).add (collar_right_deriv δ v))).const_mul (δ ^ 2 / lam)
          change HasDerivAt (reconstructionCollarProfile H lam δ) _ v at h
          rw [h.deriv]
          ring
        have heq : deriv (reconstructionCollarProfile H lam δ) =
            fun w => δ ^ 2 / lam *
              (Real.exp ((H.lo - w) / δ) - Real.exp ((w - H.hi) / δ)) / δ :=
          funext (collar_profile_deriv lam δ)
        rw [heq]
        have h := (((collar_left_deriv δ v).sub (collar_right_deriv δ v)).const_mul
          (δ ^ 2 / lam)).div_const δ
        simp at h
        rw [h.deriv]
        unfold reconstructionCollarWeight
        by_cases hl : lam = 0
        · simp [hl]
        · field_simp [hl, ne_of_gt hδ]
          ring
      rw [reconstructionProfile_operator
        ((reconstructionCollarProfile_smooth lam δ).of_le (by simp)),
        reconstructionCollarProfile_secondDeriv hδ]
      have ha := (A.bounds (p.velocity 0) (p.position 0)).1
      have hr : 1 ≤ A.a (p.velocity 0) (p.position 0) / lam :=
        (le_div_iff₀ hlam).mpr (by simpa using ha)
      have hm := mul_le_mul_of_nonneg_right hr (reconstructionCollarWeight_nonneg H δ (p.position 0))
      calc
        A.a (p.velocity 0) (p.position 0) *
            (-reconstructionCollarWeight H δ (p.position 0) / lam) =
          -(A.a (p.velocity 0) (p.position 0) / lam *
            reconstructionCollarWeight H δ (p.position 0)) := by ring
        _ ≤ -reconstructionCollarWeight H δ (p.position 0) := by
          simpa using neg_le_neg hm
    have h := reconstruction_green_le_profile
      (reconstructionCollarWeight H δ) (reconstructionCollarProfile H lam δ) 2 (by norm_num)
      (reconstructionCollarWeight_smooth δ) (reconstructionCollarWeight_nonneg H δ)
      (fun v hv => reconstructionCollarWeight_le_two H hδ ⟨hv.1.le, hv.2.le⟩)
      (reconstructionCollarProfile_smooth lam δ)
      (fun v hlo hhi => (reconstructionCollarProfile_bounds H hlam hδ ⟨hlo, hhi⟩).1)
      (reconstructionCollarProfile_operator_le hδ)
    exact h.trans (reconstructionCollarProfile_bounds H hlam hδ ⟨e.2.2.1.le, e.2.2.2.le⟩).2
  have reconstruction_green_error_integral_bound {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) :
      ∫ p, reconstructionErrorWeight H T δ R
        (KineticPoint.equivProd 1 (sectionTwoPoint p)) ∂stripGreenOfKernel H E.2 T e ≤
      Real.exp 1 * (2 * δ ^ 2 / lam) + δ +
        (Real.exp ((max |H.lo| |H.hi| + 1) * (T - e.1.time)) *
          reconstructionSpatialWeight (e.1.position 0)) / R := by
    have reconstruction_green_terminal_layer (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) {δ : ℝ} (hδ : 0 < δ) :
        ∫ p, (if T - δ < p.time then (1 : ℝ) else 0) ∂stripGreenOfKernel H K T e ≤ δ := by
      classical
      let J : Set Point := {p | p.time ∈ Ioo (T - δ) T}
      have hJ : MeasurableSet J := measurableSet_Ioo.preimage continuous_time.measurable
      have heq : (∫ p, (if T - δ < p.time then (1 : ℝ) else 0)
          ∂stripGreenOfKernel H K T e) = (stripGreenOfKernel H K T e).real J := by
        rw [← integral_indicator_one hJ]
        apply integral_congr_ae
        filter_upwards [stripGreenOfKernel_ae_mem_stripPast H K T e] with p hp
        simp [J, indicator_apply, mem_ofPred, and_iff_left hp.1, Pi.one_apply]
      rw [heq]
      have hm := stripGreenOfKernel_timeMarginal H K T e (Ioo (T - δ) T) measurableSet_Ioo
      have hv : volume (Ioo (T - δ) T) = ENNReal.ofReal δ := by
        rw [Real.volume_Ioo]
        congr 1
        ring
      rw [hv] at hm
      simpa only [Measure.real, ENNReal.toReal_ofReal hδ.le] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
    have reconstruction_green_spatial_integral_bound :
        ∫ p, reconstructionSpatialWeight (p.position 0) ∂stripGreenOfKernel H E.2 T e ≤
        Real.exp ((max |H.lo| |H.hi| + 1) * (T - e.1.time)) *
          reconstructionSpatialWeight (e.1.position 0) := by
      have h := reconstruction_green_spatial_weight_bound
      rw [← ofReal_integral_eq_lintegral_ofReal
        (reconstruction_green_spatial_integrable)
        (Eventually.of_forall fun p => add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)] at h
      have hr : 0 ≤ Real.exp ((max |H.lo| |H.hi| + 1) * (T - e.1.time)) *
          reconstructionSpatialWeight (e.1.position 0) := by
        unfold reconstructionSpatialWeight
        positivity
      exact (ENNReal.ofReal_le_ofReal_iff hr).mp h
    classical
    have hc := reconstruction_green_collar_integrable E.2 hδ
    have ht : Integrable (fun p : Point => if T - δ < p.time then (1 : ℝ) else 0)
        (stripGreenOfKernel H E.2 T e) := by
      have hm : Measurable (fun p : Point => if T - δ < p.time then (1 : ℝ) else 0) :=
        measurable_const.piecewise (measurableSet_lt measurable_const continuous_time.measurable)
          measurable_const
      apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
      exact Eventually.of_forall fun p => by split_ifs <;> norm_num
    change (∫ p, Real.exp 1 * reconstructionCollarWeight H δ (p.velocity 0) +
      (if T - δ < p.time then (1 : ℝ) else 0) + reconstructionSpatialWeight (p.position 0) / R
        ∂stripGreenOfKernel H E.2 T e) ≤ _
    have hadd₁ := integral_add (hc.const_mul (Real.exp 1)) ht
    have hadd₂ := integral_add ((hc.const_mul (Real.exp 1)).add ht) (reconstruction_green_spatial_integrable.div_const R)
    simp at hadd₁ hadd₂
    rw [hadd₂, hadd₁, integral_const_mul, integral_div]
    exact add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left
        (reconstruction_green_collar_bound hδ) (Real.exp_pos _).le)
        (reconstruction_green_terminal_layer E.2 hδ))
      (div_le_div_of_nonneg_right
        (reconstruction_green_spatial_integral_bound) hR.le)
  have reconstruction_green_error_integrable {δ : ℝ} (hδ : 0 < δ) (R : ℝ) :
      Integrable (fun p => reconstructionErrorWeight H T δ R
      (KineticPoint.equivProd 1 (sectionTwoPoint p))) (stripGreenOfKernel H E.2 T e) := by
    classical
    have ht : Integrable (fun p : Point => if T - δ < p.time then (1 : ℝ) else 0)
        (stripGreenOfKernel H E.2 T e) := by
      have hm : Measurable (fun p : Point => if T - δ < p.time then (1 : ℝ) else 0) :=
        measurable_const.piecewise (measurableSet_lt measurable_const continuous_time.measurable)
          measurable_const
      apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
      exact Eventually.of_forall fun p => by split_ifs <;> norm_num
    exact (((reconstruction_green_collar_integrable E.2 hδ).const_mul
      (Real.exp 1)).add ht).add
        ((reconstruction_green_spatial_integrable).div_const R)
  have hi := reconstruction_green_error_integrable hδ R
  have hh := norm_integral_le_of_norm_le ((integrable_const ε).add (hi.const_mul C))
    (f := fun p => g p - f p) (by
      filter_upwards [reconstruction_green_ae_time_gt H E.2 T e] with p hp
      simpa using! hgf p (ha.trans hp.le))
  rw [integral_sub (stripGreen_integrable_boundedBorel H E.2 T e g)
    (stripGreen_integrable_boundedBorel H E.2 T e f), Real.norm_eq_abs] at hh
  simp at hh
  rw [integral_add (integrable_const ε) (hi.const_mul C), integral_const,
    integral_const_mul, smul_eq_mul] at hh
  have hm : (stripGreenOfKernel H E.2 T e).real univ ≤ T - e.1.time := by
    simpa only [Measure.real, ENNReal.toReal_ofReal ((sub_pos.mpr (WithTop.coe_lt_coe.mp e.2.1)).le)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (stripGreenOfKernel_finite_time_mass H E.2 T e)
  exact hh.trans (add_le_add
    (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hm hε)
    (mul_le_mul_of_nonneg_left
      (reconstruction_green_error_integral_bound hδ hR) hC))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

