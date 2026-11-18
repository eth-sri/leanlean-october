module

import HypoellipticAleksandrov.Parabolic.ScalarClassical
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.Operator
public import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem
public import PDEFoundation.Geometry.EuclideanBall.Topology
public import Mathlib.Topology.Algebra.Group.ContinuousDiv
public import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.FieldSimp

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Filter Set Matrix
open scoped MatrixOrder Topology

private theorem hasDerivAt_affine_line
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x q : E) (s : ℝ) :
    HasDerivAt (fun r : ℝ => x + r • q) q s := by
  simpa using
    ((hasDerivAt_id' (𝕜 := ℝ) s).smul_const q).const_add x

private theorem deriv_deriv_nonpos_of_isLocalMax
    {f : ℝ → ℝ} {a c : ℝ}
    (hmax : IsLocalMax f a)
    (hsecond : HasDerivAt (deriv f) c a)
    (hcont : ContinuousAt f a) :
    c ≤ 0 := by
  by_contra hc
  have hcpos := lt_of_not_ge hc
  have heq : f =ᶠ[𝓝 a] fun _ => f a := by
    filter_upwards [hmax, (isLocalMin_of_deriv_deriv_pos (by simpa only [hsecond.deriv] using hcpos) hmax.deriv_eq_zero hcont)] with y hymax hymin
    exact le_antisymm hymax hymin
  have hderivEq : deriv f =ᶠ[𝓝 a] fun _ => 0 := by
    filter_upwards [heq.deriv] with y hy
    rw [hy]
    exact deriv_const y (f a)
  have : c = 0 := by
    calc
      c = deriv (deriv f) a := hsecond.deriv.symm
      _ = deriv (fun _ => 0) a := hderivEq.deriv_eq
      _ = 0 := deriv_const _ _
  exact hcpos.ne' this



private theorem fderiv_fderiv_apply_nonpos_of_isLocalMax_affineLine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {x q : E}
    (hg : ContDiffAt ℝ 2 g x)
    (hmax : IsLocalMax (fun r : ℝ => g (x + r • q)) 0) :
    fderiv ℝ (fderiv ℝ g) x q q ≤ 0  := by
  have hasDerivAt_deriv_restrict_affine_line_of_contDiffAt :
      HasDerivAt (deriv (fun r : ℝ => g (x + r • q)))
      (fderiv ℝ (fderiv ℝ g) x q q) 0 := by
    have hasDerivAt_fderiv_restrict_affine_line [NormedAddCommGroup E] [NormedSpace ℝ E] {g : E → ℝ} {x : E} {H : E →L[ℝ] E →L[ℝ] ℝ} (hsecond : HasFDerivAt (fderiv ℝ g) H x) :
        HasDerivAt
        (fun r : ℝ => fderiv ℝ g (x + r • q) q)
        (H q q) 0 := by
      have hsecond' : HasFDerivAt (fderiv ℝ g) H (x + (0 : ℝ) • q) := by
        simpa using hsecond
      have hgrad : HasDerivAt (fun r : ℝ => fderiv ℝ g (x + r • q)) (H q) 0 :=
        hsecond'.comp_hasDerivAt 0 (hasDerivAt_affine_line x q 0)
      simpa using
        hgrad.clm_apply (hasDerivAt_const (x := 0) (c := q))
    have hgGradDiffAt :=
      (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hEvalLine :=
      hasDerivAt_fderiv_restrict_affine_line hgGradDiffAt.hasFDerivAt
    have hgEventuallyAtLineZero :
        ∀ᶠ y in 𝓝 (x + (0 : ℝ) • q), ContDiffAt ℝ 2 g y := by
      simpa using (hg.eventually (by norm_num))
    apply hEvalLine.congr_of_eventuallyEq
    filter_upwards [
      (hasDerivAt_affine_line x q 0).continuousAt hgEventuallyAtLineZero] with r hr
    change ContDiffAt ℝ 2 g (x + r • q) at hr
    exact (hr.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt
      r (hasDerivAt_affine_line x q r) |>.deriv
  have hgAtLineZero : ContinuousAt g (x + (0 : ℝ) • q) := by
    simpa using hg.continuousAt
  have hcompCont :=
    hgAtLineZero.comp' (f := fun r => x + r • q) ((hasDerivAt_affine_line x q 0).continuousAt)
  exact deriv_deriv_nonpos_of_isLocalMax hmax
    (hasDerivAt_deriv_restrict_affine_line_of_contDiffAt) hcompCont

private theorem scalarSpatialHessian_apply_eq_sndFDeriv {n : ℕ}
    {u : TimeVelocity n → ℝ} {z : TimeVelocity n}
    (hu : ContDiffAt ℝ 2 (fun y : PDE.Vec n => u (z.1, y)) z.2)
    (i j : Fin n) :
    scalarSpatialHessian u z i j =
      fderiv ℝ (fderiv ℝ (fun y : PDE.Vec n => u (z.1, y))) z.2
        (PDE.basisVec i) (PDE.basisVec j) := by
  let g : PDE.Vec n → ℝ := fun y => u (z.1, y)
  have hsecond :=
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hdiff : ∀ j : Fin n,
      DifferentiableAt ℝ (fun y => fderiv ℝ g y (PDE.basisVec j)) z.2 := by
    intro j
    exact (hsecond.clm_apply (hasFDerivAt_const (PDE.basisVec j) z.2)).differentiableAt
  change (fderiv ℝ (fun y => fun j =>
      fderiv ℝ g y (PDE.basisVec j)) z.2 (PDE.basisVec i)) j = _
  rw [fderiv_pi hdiff]
  have hjapply := congrArg (fun L => L (PDE.basisVec i)) ((hsecond.clm_apply (hasFDerivAt_const (PDE.basisVec j) z.2)).fderiv)
  simpa [ContinuousLinearMap.flip_apply] using hjapply




private theorem trace_mul_nonneg_of_posSemidef {n : ℕ} {A H : PDE.Mat n}
    (hA : A.PosSemidef) (hH : H.PosSemidef) :
    0 ≤ (A * H).trace := by
  classical
  let S := CFC.sqrt H
  have hS : S.PosSemidef := by
    dsimp [S]
    exact CFC.sqrt_nonneg H |>.posSemidef
  calc
    0 ≤ (S * A * Sᴴ).trace := (hA.mul_mul_conjTranspose_same S).trace_nonneg
    _ = (S * A * S).trace := by rw [hS.isHermitian.eq]
    _ = (A * S * S).trace := (Matrix.trace_mul_cycle A S S).symm
    _ = (A * (S * S)).trace := by rw [Matrix.mul_assoc]
    _ = (A * H).trace := by rw [show S * S = H by
      dsimp [S]
      exact CFC.sqrt_mul_sqrt_self H hH.nonneg]

private theorem matrixContraction_nonpos_of_psd_neg {n : ℕ} {A H : PDE.Mat n}
    (hA : A.PosSemidef) (hH : (-H).PosSemidef) (hHsymm : H.IsSymm) :
    matrixContraction A H ≤ 0 := by
  rw [matrixContraction_eq_trace_mul_of_isSymm A H hHsymm]
  calc
    (A * H).trace = -((A * (-H)).trace) := by simp
    _ ≤ 0 := neg_nonpos.mpr (trace_mul_nonneg_of_posSemidef hA hH)



/-- Pointwise maximum calculus for the transported operator, with only the
anisotropic derivatives used by the source. -/
theorem transportedForwardOperator_nonpos_of_slice_localMax {d : ℕ}
    {B : FullKineticCoefficient d} {b : PDE.Vec d → PDE.Vec d}
    {u : KineticPoint d → ℝ} {p : KineticPoint d}
    (htime : kineticTimeDerivative u p ≤ 0)
    (hv : ContDiffAt ℝ 2 (fun y => u ⟨p.time, y, p.velocity⟩) p.position)
    (hz : DifferentiableAt ℝ (fun z => u ⟨p.time, p.position, z⟩) p.velocity)
    (hvmax : IsLocalMax (fun y => u ⟨p.time, y, p.velocity⟩) p.position)
    (hzmax : IsLocalMax (fun z => u ⟨p.time, p.position, z⟩) p.velocity)
    (hB : (B p.time p.position p.velocity).PosSemidef) :
    transportedForwardOperator B b u p ≤ 0      := by
  have scalarSpatialHessian_isSymm_of_contDiffAt {n : ℕ} {u : TimeVelocity n → ℝ} {z : TimeVelocity n} (hu : ContDiffAt ℝ 2 (fun y : PDE.Vec n => u (z.1, y)) z.2) :
      (scalarSpatialHessian u z).IsSymm := by
    refine Matrix.IsSymm.ext ?_
    intro i j
    rw [scalarSpatialHessian_apply_eq_sndFDeriv hu,
      scalarSpatialHessian_apply_eq_sndFDeriv hu]
    exact
      (hu.isSymmSndFDerivAt (by norm_num)).eq (PDE.basisVec j) (PDE.basisVec i)
  have scalarSpatialHessian_quadratic_eq {n : ℕ} {u : TimeVelocity n → ℝ} {z : TimeVelocity n} (hu : ContDiffAt ℝ 2 (fun y : PDE.Vec n => u (z.1, y)) z.2) (q : PDE.Vec n) :
      dotProduct q ((scalarSpatialHessian u z).mulVec q) =
      fderiv ℝ (fderiv ℝ (fun y : PDE.Vec n => u (z.1, y))) z.2 q q := by
    let g : PDE.Vec n → ℝ := fun y => u (z.1, y)
    let H := fderiv ℝ (fderiv ℝ g) z.2
    change (∑ i : Fin n, q i * ∑ j : Fin n,
        scalarSpatialHessian u z i j * q j) = H q q
    simp_rw [scalarSpatialHessian_apply_eq_sndFDeriv hu]
    change (∑ i : Fin n, q i * ∑ j : Fin n,
        H (PDE.basisVec i) (PDE.basisVec j) * q j) = H q q
    calc
      (∑ i : Fin n, q i * ∑ j : Fin n,
          H (PDE.basisVec i) (PDE.basisVec j) * q j) =
          ∑ i : Fin n, q i * H (PDE.basisVec i)
            (∑ j : Fin n, q j • PDE.basisVec j) := by
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        rw [map_sum]
        simp
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ∑ i : Fin n, q i * H (PDE.basisVec i) q := by
        rw [PDE.sum_smul_basisVec]
      _ = H (∑ i : Fin n, q i • PDE.basisVec i) q := by
        rw [map_sum, _root_.sum_apply]
        simp
      _ = H q q := by rw [PDE.sum_smul_basisVec]
  have neg_scalarSpatialHessian_posSemidef_of_spatial_localMax {n : ℕ} {u : TimeVelocity n → ℝ} {z : TimeVelocity n} (hu : ContDiffAt ℝ 2 (fun y => u (z.1, y)) z.2) (hmax : IsLocalMax (fun y => u (z.1, y)) z.2) :
      (-scalarSpatialHessian u z).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · apply Matrix.IsHermitian.ext
      intro i j
      simp only [star_trivial]
      change -scalarSpatialHessian u z j i = -scalarSpatialHessian u z i j
      exact congrArg Neg.neg ((scalarSpatialHessian_isSymm_of_contDiffAt hu).apply i j)
    · intro q
      rw [neg_mulVec, dotProduct_neg]
      have hlineMax : IsLocalMax
          (fun r : ℝ => u (z.1, z.2 + r • q)) 0 := by
        have hmaxAtLineZero : IsLocalMax (fun y : PDE.Vec n => u (z.1, y))
            (z.2 + (0 : ℝ) • q) := by
          simpa using hmax
        simpa [Function.comp_def] using hmaxAtLineZero.comp_continuous
          (g := fun r : ℝ => z.2 + r • q)
          (hasDerivAt_affine_line z.2 q 0).continuousAt
      change -dotProduct q
        ((scalarSpatialHessian u z).mulVec q) ≥ 0
      rw [scalarSpatialHessian_quadratic_eq hu q]
      exact neg_nonneg.mpr
        (fderiv_fderiv_apply_nonpos_of_isLocalMax_affineLine hu hlineMax)
  have transported_gradient_eq_zero_of_localMax {u : KineticPoint d → ℝ} {p : KineticPoint d} (hu : DifferentiableAt ℝ (fun z => u ⟨p.time, p.position, z⟩) p.velocity) (hmax : IsLocalMax (fun z => u ⟨p.time, p.position, z⟩) p.velocity) :
      kineticVelocityGradient u p = 0 := by
    ext i
    change fderiv ℝ (fun z => u ⟨p.time, p.position, z⟩)
      p.velocity (PDE.basisVec i) = 0
    rw [hmax.hasFDerivAt_eq_zero hu.hasFDerivAt]
    rfl
  have diffused_contraction_nonpos_of_localMax {u : KineticPoint d → ℝ} {p : KineticPoint d} {A : PDE.Mat d} (hu : ContDiffAt ℝ 2 (fun y => u ⟨p.time, y, p.velocity⟩) p.position) (hmax : IsLocalMax (fun y => u ⟨p.time, y, p.velocity⟩) p.position) (hA : A.PosSemidef) :
      matrixContraction A (diffusedHessian u p) ≤ 0 := by
    let f : TimeVelocity d → ℝ := fun z => u ⟨z.1, z.2, p.velocity⟩
    have heq : scalarSpatialHessian f (p.time, p.position) = diffusedHessian u p := rfl
    rw [← heq]
    exact matrixContraction_nonpos_of_psd_neg hA
      (neg_scalarSpatialHessian_posSemidef_of_spatial_localMax hu hmax)
      (scalarSpatialHessian_isSymm_of_contDiffAt hu)
  rw [transportedForwardOperator_apply,
    transported_gradient_eq_zero_of_localMax hz hzmax]
  simp [PDE.vecDot]
  exact add_nonpos htime (diffused_contraction_nonpos_of_localMax hv hvmax hB)


/-- The finite closed moving tube with unrestricted transported coordinate. -/
def maximumClosedTube {d : ℕ} (Ω : Set (PDE.Vec d)) (γ : ℝ → PDE.Vec d)
    (a b : ℝ) : Set (KineticPoint d) :=
  {p | p.time ∈ Icc a b ∧ p.position ∈ closure (movingDomain Ω γ p.time)}

/-- The finite open moving tube with unrestricted transported coordinate. -/
def maximumOpenTube {d : ℕ} (Ω : Set (PDE.Vec d)) (γ : ℝ → PDE.Vec d)
    (a b : ℝ) : Set (KineticPoint d) :=
  {p | p.time ∈ Ioo a b ∧ p.position ∈ movingDomain Ω γ p.time}

/-- Closure membership is expressed in the fixed translated-back domain. -/
theorem mem_closure_movingDomain_iff {d : ℕ} (Ω : Set (PDE.Vec d))
    (γ : ℝ → PDE.Vec d) (t : ℝ) (v : PDE.Vec d) :
    v ∈ closure (movingDomain Ω γ t) ↔ v - γ t ∈ closure Ω := by
  rw [movingDomain, ← PDE.preimage_subRight_eq_translateSet]
  exact (Set.ext_iff.mp ((Homeomorph.subRight (γ t)).preimage_closure Ω).symm) v

/-- A closed moving tube truncated in the transported coordinate is compact. -/
theorem isCompact_maximumClosedTube_truncated {d : ℕ}
    {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d} {a b R : ℝ}
    (hΩ : IsCompact (closure Ω)) (hγ : ContinuousOn γ (Icc a b)) (hR : 0 ≤ R) :
    IsCompact {p ∈ maximumClosedTube Ω γ a b |
      p.velocity ∈ PDE.euclideanClosedBall 0 R} := by
  let f : ℝ × (PDE.Vec d × PDE.Vec d) → KineticPoint d :=
    fun q => ⟨q.1, q.2.1 + γ q.1, q.2.2⟩
  have hf : ContinuousOn f (Icc a b ×ˢ (closure Ω ×ˢ PDE.euclideanClosedBall 0 R)) := by
    change ContinuousOn ((KineticPoint.homeomorphProd d).symm ∘
      (fun q : ℝ × (PDE.Vec d × PDE.Vec d) =>
        (q.1, (q.2.1 + γ q.1, q.2.2)))) _
    apply (KineticPoint.homeomorphProd d).symm.continuous.comp_continuousOn
    apply ContinuousOn.prodMk continuousOn_fst
    apply ContinuousOn.prodMk
    · exact continuousOn_snd.fst.add (hγ.comp continuousOn_fst (fun q hq => hq.1))
    · exact continuousOn_snd.snd
  have heq : f '' (Icc a b ×ˢ (closure Ω ×ˢ PDE.euclideanClosedBall 0 R)) =
      {p ∈ maximumClosedTube Ω γ a b |
        p.velocity ∈ PDE.euclideanClosedBall 0 R} := by
    ext p
    constructor
    · rintro ⟨q, ⟨ht, hv, hz⟩, rfl⟩
      refine ⟨⟨ht, ?_⟩, hz⟩
      rw [mem_closure_movingDomain_iff]
      simpa only [f, add_sub_cancel_right] using hv
    · rintro ⟨⟨ht, hv⟩, hz⟩
      refine ⟨(p.time, (p.position - γ p.time, p.velocity)), ⟨ht, ?_, hz⟩, ?_⟩
      · exact (mem_closure_movingDomain_iff Ω γ p.time p.position).mp hv
      · simp only [f, sub_add_cancel]
  rw [← heq]
  exact (isCompact_Icc.prod
    (hΩ.prod (PDE.isCompact_euclideanClosedBall 0 hR))).image_of_continuousOn hf


/-- Independence of the transported coordinate on a given tube. -/
def IsTransportIndependentOn {d : ℕ} (u : KineticPoint d → ℝ)
    (K : Set (KineticPoint d)) : Prop :=
  ∀ p ∈ K, ∀ z : PDE.Vec d, u ⟨p.time, p.position, z⟩ = u p

/-- Uniform decay to negative infinity in the explicit Euclidean transported norm. -/
def IsUniformlyNegAtInfinityOn {d : ℕ} (u : KineticPoint d → ℝ)
    (K : Set (KineticPoint d)) : Prop :=
  ∀ M : ℝ, ∃ R : ℝ, 0 ≤ R ∧
    ∀ p ∈ K, R ≤ PDE.vecEuclideanNorm p.velocity → u p ≤ M





/-- Subtract a positive affine function of remaining time. -/
def maximumTerminalTilt {d : ℕ} (u : KineticPoint d → ℝ) (ε T : ℝ) :
    KineticPoint d → ℝ := fun p => u p - ε * (T - p.time)

/-- The diffused Hessian is unchanged by the terminal perturbation. -/
theorem diffusedHessian_maximumTerminalTilt {d : ℕ} (u : KineticPoint d → ℝ)
    (ε T : ℝ) (p : KineticPoint d) :
    diffusedHessian (maximumTerminalTilt u ε T) p = diffusedHessian u p := by
  have heq : (fun y : PDE.Vec d => kineticPositionGradient
      (maximumTerminalTilt u ε T) ⟨p.time, y, p.velocity⟩) =
      fun y => kineticPositionGradient u ⟨p.time, y, p.velocity⟩ := by
    funext y
    ext i
    exact congrArg (fun L : PDE.Vec d →L[ℝ] ℝ => L (PDE.basisVec i))
      (fderiv_sub_const (𝕜 := ℝ) (f := fun v => u ⟨p.time, v, p.velocity⟩)
        (x := y) (ε * (T - p.time)))
  unfold diffusedHessian
  rw [heq]

/-- The transported gradient is unchanged by the terminal perturbation. -/
theorem kineticVelocityGradient_maximumTerminalTilt {d : ℕ} (u : KineticPoint d → ℝ)
    (ε T : ℝ) (p : KineticPoint d) :
    kineticVelocityGradient (maximumTerminalTilt u ε T) p = kineticVelocityGradient u p := by
  ext i
  exact congrArg (fun L : PDE.Vec d →L[ℝ] ℝ => L (PDE.basisVec i))
    (fderiv_sub_const (𝕜 := ℝ) (f := fun z => u ⟨p.time, p.position, z⟩)
      (x := p.velocity) (ε * (T - p.time)))


/-- The terminal perturbation strictly increases the transported operator by ε. -/
theorem transportedForwardOperator_maximumTerminalTilt {d : ℕ}
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    {u : KineticPoint d → ℝ} {p : KineticPoint d}
    (hu : DifferentiableAt ℝ (fun t => u ⟨t, p.position, p.velocity⟩) p.time)
    (ε T : ℝ) :
    transportedForwardOperator B b (maximumTerminalTilt u ε T) p =
      transportedForwardOperator B b u p + ε  := by
  have kineticTimeDerivative_maximumTerminalTilt (ε T : ℝ) :
      kineticTimeDerivative (maximumTerminalTilt u ε T) p = kineticTimeDerivative u p + ε := by
    have hd : HasDerivAt (fun t => maximumTerminalTilt u ε T ⟨t, p.position, p.velocity⟩)
        (kineticTimeDerivative u p + ε) p.time := by
      convert hu.hasDerivAt.sub
        ((hasDerivAt_const (x := p.time) (c := ε)).mul
          ((hasDerivAt_const (x := p.time) (c := T)).sub (hasDerivAt_id p.time))) using 1
      all_goals simp [maximumTerminalTilt, kineticTimeDerivative, Pi.sub_def, Pi.mul_def] <;> ring
    exact hd.deriv
  rw [transportedForwardOperator_apply, transportedForwardOperator_apply,
    kineticTimeDerivative_maximumTerminalTilt,
    diffusedHessian_maximumTerminalTilt, kineticVelocityGradient_maximumTerminalTilt]
  ring




/-- Moving-domain comparison on the entire closed time slab, including its initial slice. -/
theorem nonpos_on_maximumClosedTube {d : ℕ}
    {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d} {a b : ℝ}
    {B : FullKineticCoefficient d} {drift : PDE.Vec d → PDE.Vec d}
    {u : KineticPoint d → ℝ}
    (hab : a < b) (hΩ : IsOpen Ω) (hcΩ : IsCompact (closure Ω))
    (hγ : ContinuousOn γ (Icc a b))
    (hu : ContinuousOn u (maximumClosedTube Ω γ a b))
    (hcontrol : IsTransportIndependentOn u (maximumClosedTube Ω γ a b) ∨
      IsUniformlyNegAtInfinityOn u (maximumClosedTube Ω γ a b))
    (hreg : ∀ p ∈ maximumOpenTube Ω γ a b,
      DifferentiableAt ℝ (fun t => u ⟨t, p.position, p.velocity⟩) p.time ∧
      ContDiffAt ℝ 2 (fun v => u ⟨p.time, v, p.velocity⟩) p.position ∧
      DifferentiableAt ℝ (fun z => u ⟨p.time, p.position, z⟩) p.velocity)
    (hB : ∀ p ∈ maximumOpenTube Ω γ a b,
      (B p.time p.position p.velocity).PosSemidef)
    (hsub : ∀ p ∈ maximumOpenTube Ω γ a b, 0 ≤ transportedForwardOperator B drift u p)
    (hterminal : ∀ p ∈ maximumClosedTube Ω γ a b, p.time = b → u p ≤ 0)
    (hlateral : ∀ p ∈ maximumClosedTube Ω γ a b,
      p.position ∈ frontier (movingDomain Ω γ p.time) → u p ≤ 0)
 :
    ∀ q ∈ maximumClosedTube Ω γ a b, u q ≤ 0   := by
  intro q hq
  have nonpos_on_inset_maximumClosedTube_of_strict {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d} {a α b : ℝ} {B : FullKineticCoefficient d} {drift : PDE.Vec d → PDE.Vec d} {u : KineticPoint d → ℝ} (hΩ : IsOpen Ω) (hcΩ : IsCompact (closure Ω)) (haα : a < α) (hγ : ContinuousOn γ (Icc a b)) (hu : ContinuousOn u (maximumClosedTube Ω γ a b)) (hcontrol : IsTransportIndependentOn u (maximumClosedTube Ω γ a b) ∨
      IsUniformlyNegAtInfinityOn u (maximumClosedTube Ω γ a b)) (hreg : ∀ p ∈ maximumOpenTube Ω γ a b,
      DifferentiableAt ℝ (fun t => u ⟨t, p.position, p.velocity⟩) p.time ∧
      ContDiffAt ℝ 2 (fun v => u ⟨p.time, v, p.velocity⟩) p.position ∧
      DifferentiableAt ℝ (fun z => u ⟨p.time, p.position, z⟩) p.velocity) (hB : ∀ p ∈ maximumOpenTube Ω γ a b,
      (B p.time p.position p.velocity).PosSemidef) (hstrict : ∀ p ∈ maximumOpenTube Ω γ a b, 0 < transportedForwardOperator B drift u p) (hterminal : ∀ p ∈ maximumClosedTube Ω γ a b, p.time = b → u p ≤ 0) (hlateral : ∀ p ∈ maximumClosedTube Ω γ a b,
      p.position ∈ frontier (movingDomain Ω γ p.time) → u p ≤ 0) :
      ∀ q ∈ maximumClosedTube Ω γ α b, u q ≤ 0 := by
    have transportedForwardOperator_nonpos_at_tube_max {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d} {a : ℝ} {b : ℝ} {B : FullKineticCoefficient d} {u : KineticPoint d → ℝ} {p : KineticPoint d} (hΩ : IsOpen Ω) (hγ : ContinuousAt γ p.time) (ht : p.time ∈ Ico a b) (hv : p.position ∈ movingDomain Ω γ p.time) (hmax : IsMaxOn u (maximumClosedTube Ω γ a b) p) (hut : DifferentiableAt ℝ (fun t => u ⟨t, p.position, p.velocity⟩) p.time) (huv : ContDiffAt ℝ 2 (fun y => u ⟨p.time, y, p.velocity⟩) p.position) (huz : DifferentiableAt ℝ (fun z => u ⟨p.time, p.position, z⟩) p.velocity) (hB : (B p.time p.position p.velocity).PosSemidef) :
        transportedForwardOperator B drift u p ≤ 0 := by
      have hvmax : IsLocalMax (fun y => u ⟨p.time, y, p.velocity⟩) p.position := by
        filter_upwards [(isOpen_movingDomain hΩ p.time).mem_nhds hv] with y hy
        exact hmax ⟨⟨ht.1, ht.2.le⟩, subset_closure hy⟩
      have hzmax : IsLocalMax (fun z => u ⟨p.time, p.position, z⟩) p.velocity := by
        exact Filter.Eventually.of_forall (fun z =>
          hmax ⟨⟨ht.1, ht.2.le⟩, subset_closure hv⟩)
      have hmove : ∀ᶠ t in 𝓝 p.time, p.position ∈ movingDomain Ω γ t := by
        have hsub :=
          (PDE.mem_translateSet_iff_sub_mem).mp hv
        have hevent := (continuousAt_const.sub hγ) (hΩ.mem_nhds hsub)
        simp only [Filter.mem_map] at hevent
        filter_upwards [hevent] with t ht
        exact PDE.mem_translateSet_iff_sub_mem.mpr ht
      have htmax : IsLocalMaxOn (fun t => u ⟨t, p.position, p.velocity⟩)
          (Icc a b) p.time := by
        filter_upwards [hmove.filter_mono nhdsWithin_le_nhds,
          self_mem_nhdsWithin] with t htm hti
        exact hmax ⟨hti, subset_closure htm⟩
      have hdir : b - p.time ∈ posTangentConeAt (Icc a b) p.time := by
        apply sub_mem_posTangentConeAt_of_segment_subset
        intro t hti
        exact ⟨le_trans ht.1 (segment_subset_Icc (𝕜 := ℝ) ht.2.le hti).1,
          (segment_subset_Icc (𝕜 := ℝ) ht.2.le hti).2⟩
      have htime : kineticTimeDerivative u p ≤ 0 := by
        have hproduct : (b - p.time) * kineticTimeDerivative u p ≤ 0 := by
          simpa [kineticTimeDerivative, ContinuousLinearMap.toSpanSingleton_apply] using (htmax.hasFDerivWithinAt_nonpos hut.hasDerivAt.hasFDerivAt.hasFDerivWithinAt hdir)
        exact nonpos_of_mul_nonpos_right hproduct (sub_pos.mpr ht.2)
      exact transportedForwardOperator_nonpos_of_slice_localMax htime huv huz hvmax hzmax hB
    have exists_positive_isMaxOn_maximumClosedTube {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d} {a : ℝ} {b : ℝ} {u : KineticPoint d → ℝ} (hΩ : IsCompact (closure Ω)) (hγ : ContinuousOn γ (Icc a b)) (hu : ContinuousOn u (maximumClosedTube Ω γ a b)) (hcontrol : IsTransportIndependentOn u (maximumClosedTube Ω γ a b) ∨
        IsUniformlyNegAtInfinityOn u (maximumClosedTube Ω γ a b)) {q : KineticPoint d} (hq : q ∈ maximumClosedTube Ω γ a b) (hpos : 0 < u q) :
        ∃ p ∈ maximumClosedTube Ω γ a b,
        0 < u p ∧ IsMaxOn u (maximumClosedTube Ω γ a b) p := by
      rcases hcontrol with hind | hinfty
      · let K : Set (KineticPoint d) := {p ∈ maximumClosedTube Ω γ a b |
          p.velocity ∈ PDE.euclideanClosedBall 0 0}
        let q0 : KineticPoint d := ⟨q.time, q.position, 0⟩
        have hq0 : q0 ∈ K := by
          refine ⟨hq, ?_⟩
          simp [q0, PDE.euclideanClosedBall, PDE.euclideanSqDist, PDE.vecNormSq, PDE.vecDot]
        have hK := isCompact_maximumClosedTube_truncated hΩ hγ le_rfl
        obtain ⟨p, hp, hmax⟩ := hK.exists_isMaxOn ⟨q0, hq0⟩ (hu.mono (fun _ h => h.1))
        have hpPos : 0 < u p := by
          have heq := hind q hq 0
          exact lt_of_lt_of_le (heq.symm ▸ hpos) (hmax hq0)
        refine ⟨p, hp.1, hpPos, ?_⟩
        intro x hx
        have hx0 : (⟨x.time, x.position, 0⟩ : KineticPoint d) ∈ K := by
          refine ⟨hx, ?_⟩
          simp [PDE.euclideanClosedBall, PDE.euclideanSqDist, PDE.vecNormSq, PDE.vecDot]
        change u x ≤ u p
        rw [← hind x hx 0]
        exact hmax hx0
      · obtain ⟨R, hR, hbound⟩ := hinfty 0
        let K : Set (KineticPoint d) := {p ∈ maximumClosedTube Ω γ a b |
          p.velocity ∈ PDE.euclideanClosedBall 0 R}
        have hqR : PDE.vecEuclideanNorm q.velocity < R := by
          by_contra hnot
          exact (not_le_of_gt hpos) (hbound q hq (le_of_not_gt hnot))
        have hqK : q ∈ K := by
          refine ⟨hq, ?_⟩
          rw [PDE.mem_euclideanClosedBall_iff_vecEuclideanNorm_le hR]
          simpa using hqR.le
        obtain ⟨p, hp, hmax⟩ := (isCompact_maximumClosedTube_truncated hΩ hγ hR).exists_isMaxOn ⟨q, hqK⟩ (hu.mono (fun _ h => h.1))
        have hpPos := lt_of_lt_of_le hpos (hmax hqK)
        refine ⟨p, hp.1, hpPos, ?_⟩
        intro x hx
        by_cases hxR : x.velocity ∈ PDE.euclideanClosedBall 0 R
        · exact hmax ⟨hx, hxR⟩
        · have hxLarge : R ≤ PDE.vecEuclideanNorm x.velocity := by
            rw [PDE.mem_euclideanClosedBall_iff_vecEuclideanNorm_le hR] at hxR
            simp only [sub_zero] at hxR
            exact (lt_of_not_ge hxR).le
          exact (hbound x hx hxLarge).trans hpPos.le
    have hsub : maximumClosedTube Ω γ α b ⊆ maximumClosedTube Ω γ a b := by
      intro p hp
      exact ⟨⟨haα.le.trans hp.1.1, hp.1.2⟩, hp.2⟩
    have htSub : Icc α b ⊆ Icc a b := Icc_subset_Icc_left haα.le
    have hcontrol' : IsTransportIndependentOn u (maximumClosedTube Ω γ α b) ∨
        IsUniformlyNegAtInfinityOn u (maximumClosedTube Ω γ α b) := by
      rcases hcontrol with hi | hn
      · exact Or.inl (fun p hp => hi p (hsub hp))
      · right
        intro M
        obtain ⟨R, hR, hb⟩ := hn M
        exact ⟨R, hR, fun p hp => hb p (hsub hp)⟩
    intro q hq
    by_contra hnot
    obtain ⟨p, hp, hpos, hmax⟩ := exists_positive_isMaxOn_maximumClosedTube hcΩ
      (hγ.mono htSub) (hu.mono hsub) hcontrol' hq (lt_of_not_ge hnot)
    have hpFull := hsub hp
    have hpt := lt_of_le_of_ne hp.1.2 (by
      intro heq
      exact (not_le_of_gt hpos) (hterminal p hpFull heq))
    have hpv : p.position ∈ movingDomain Ω γ p.time := by
      by_contra hv
      have hfront : p.position ∈ frontier (movingDomain Ω γ p.time) := by
        rw [(isOpen_movingDomain hΩ p.time).frontier_eq]
        exact ⟨hp.2, hv⟩
      exact (not_le_of_gt hpos) (hlateral p hpFull hfront)
    have hpOpen : p ∈ maximumOpenTube Ω γ a b :=
      ⟨⟨haα.trans_le hp.1.1, hpt⟩, hpv⟩
    obtain ⟨hut, huv, huz⟩ := hreg p hpOpen
    have hγp : ContinuousAt γ p.time :=
      (hγ p.time hpFull.1).continuousAt (Icc_mem_nhds hpOpen.1.1 hpOpen.1.2)
    exact (not_le_of_gt (hstrict p hpOpen))
      (transportedForwardOperator_nonpos_at_tube_max hΩ hγp ⟨hp.1.1, hpt⟩ hpv
        hmax hut huv huz (hB p hpOpen))
  have nonpos_at_later_time_maximumClosedTube {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d} {a : ℝ} {b : ℝ} {B : FullKineticCoefficient d} {drift : PDE.Vec d → PDE.Vec d} {u : KineticPoint d → ℝ} (hΩ : IsOpen Ω) (hcΩ : IsCompact (closure Ω)) (hγ : ContinuousOn γ (Icc a b)) (hu : ContinuousOn u (maximumClosedTube Ω γ a b)) (hcontrol : IsTransportIndependentOn u (maximumClosedTube Ω γ a b) ∨
      IsUniformlyNegAtInfinityOn u (maximumClosedTube Ω γ a b)) (hreg : ∀ p ∈ maximumOpenTube Ω γ a b,
      DifferentiableAt ℝ (fun t => u ⟨t, p.position, p.velocity⟩) p.time ∧
      ContDiffAt ℝ 2 (fun v => u ⟨p.time, v, p.velocity⟩) p.position ∧
      DifferentiableAt ℝ (fun z => u ⟨p.time, p.position, z⟩) p.velocity) (hB : ∀ p ∈ maximumOpenTube Ω γ a b,
      (B p.time p.position p.velocity).PosSemidef) (hsub : ∀ p ∈ maximumOpenTube Ω γ a b, 0 ≤ transportedForwardOperator B drift u p) (hterminal : ∀ p ∈ maximumClosedTube Ω γ a b, p.time = b → u p ≤ 0) (hlateral : ∀ p ∈ maximumClosedTube Ω γ a b,
      p.position ∈ frontier (movingDomain Ω γ p.time) → u p ≤ 0) {q : KineticPoint d} (hq : q ∈ maximumClosedTube Ω γ a b) (ht : a < q.time) :
      u q ≤ 0 := by
    by_cases hqb : q.time = b
    · exact hterminal q hq hqb
    by_contra hnot
    let ε : ℝ := u q / (2 * (b - q.time))
    have hε : 0 < ε := div_pos (lt_of_not_ge hnot) (mul_pos (by norm_num) (sub_pos.mpr (lt_of_le_of_ne hq.1.2 hqb)))
    let w := maximumTerminalTilt u ε b
    have hwle : ∀ p ∈ maximumClosedTube Ω γ a b, w p ≤ u p := by
      intro p hp
      exact sub_le_self _ (mul_nonneg hε.le (sub_nonneg.mpr hp.1.2))
    have hwCont : ContinuousOn w (maximumClosedTube Ω γ a b) :=
      hu.sub (continuousOn_const.mul (continuousOn_const.sub continuous_time.continuousOn))
    have hwControl : IsTransportIndependentOn w (maximumClosedTube Ω γ a b) ∨
        IsUniformlyNegAtInfinityOn w (maximumClosedTube Ω γ a b) := by
      rcases hcontrol with hi | hn
      · left
        intro p hp z
        dsimp [w, maximumTerminalTilt]
        rw [hi p hp z]
      · right
        intro M
        obtain ⟨R, hR, hb⟩ := hn M
        exact ⟨R, hR, fun p hp hz => (hwle p hp).trans (hb p hp hz)⟩
    have hwReg : ∀ p ∈ maximumOpenTube Ω γ a b,
        DifferentiableAt ℝ (fun t => w ⟨t, p.position, p.velocity⟩) p.time ∧
        ContDiffAt ℝ 2 (fun v => w ⟨p.time, v, p.velocity⟩) p.position ∧
        DifferentiableAt ℝ (fun z => w ⟨p.time, p.position, z⟩) p.velocity := by
      intro p hp
      obtain ⟨ht, hv, hz⟩ := hreg p hp
      dsimp only [w, maximumTerminalTilt]
      refine ⟨?_, hv.sub contDiffAt_const, hz.sub_const (ε * (b - p.time))⟩
      exact ht.sub ((differentiableAt_const ε).mul
        ((differentiableAt_const b).sub differentiableAt_id))
    have hwStrict : ∀ p ∈ maximumOpenTube Ω γ a b,
        0 < transportedForwardOperator B drift w p := by
      intro p hp
      rw [transportedForwardOperator_maximumTerminalTilt B drift (hreg p hp).1]
      exact add_pos_of_nonneg_of_pos (hsub p hp) hε
    have hresult := nonpos_on_inset_maximumClosedTube_of_strict hΩ hcΩ
      (show a < (a + q.time) / 2 by linarith) hγ hwCont hwControl hwReg hB hwStrict
      (fun p hp heq => (hwle p hp).trans (hterminal p hp heq))
      (fun p hp hf => (hwle p hp).trans (hlateral p hp hf))
      q ⟨⟨by linarith, hq.1.2⟩, hq.2⟩
    have heq : ε * (b - q.time) = u q / 2 := by
      dsimp [ε]
      field_simp
    change u q - ε * (b - q.time) ≤ 0 at hresult
    rw [heq] at hresult
    linarith
  have hlater : ∀ {p : KineticPoint d}, p ∈ maximumClosedTube Ω γ a b →
      a < p.time → u p ≤ 0 :=
    fun {_} => nonpos_at_later_time_maximumClosedTube hΩ hcΩ hγ hu hcontrol
      hreg hB hsub hterminal hlateral
  by_cases hqa : q.time = a
  · let f : ℝ → KineticPoint d :=
      fun t => ⟨t, q.position - γ a + γ t, q.velocity⟩
    have hf : ContinuousOn f (Icc a b) := by
      change ContinuousOn ((KineticPoint.homeomorphProd d).symm ∘
        (fun t => (t, (q.position - γ a + γ t, q.velocity)))) _
      exact (KineticPoint.homeomorphProd d).symm.continuous.comp_continuousOn
        (continuousOn_id.prodMk ((continuousOn_const.add hγ).prodMk continuousOn_const))
    have hfmem : ∀ t ∈ Icc a b, f t ∈ maximumClosedTube Ω γ a b := by
      intro t ht
      refine ⟨ht, ?_⟩
      rw [mem_closure_movingDomain_iff]
      simpa only [f, add_sub_cancel_right, hqa] using ((mem_closure_movingDomain_iff Ω γ q.time q.position).mp hq.2)
    have hfc : ContinuousWithinAt (u ∘ f) (Icc a b) a :=
      (hu.comp hf hfmem) a ⟨le_rfl, hab.le⟩
    have haClosure : a ∈ closure (Ioc a b) := by
      rw [closure_Ioc hab.ne]
      exact ⟨le_rfl, hab.le⟩
    have hbound : (u ∘ f) a ≤ 0 :=
      (hfc.mono Ioc_subset_Icc_self).closure_le haClosure continuousWithinAt_const
        (fun t ht => hlater (hfmem t ⟨ht.1.le, ht.2⟩) ht.1)
    have hfa : f a = q := by
      simp only [f, sub_add_cancel, ← hqa]
    simpa [hfa] using hbound
  · exact hlater hq (lt_of_le_of_ne hq.1.1 (Ne.symm hqa))


/-- The source's bounded admissible domains have compact closure. -/
theorem isCompact_closure_of_maximumPrinciple_domain {d : ℕ}
    {Ω : Set (PDE.Vec d)}
    (hΩ : (∃ c R, 0 < R ∧ Ω = PDE.euclideanBall c R) ∨
      (∃ hd : d = 1, ∃ a b, a < b ∧ hd ▸ Ω = PDE.oneDimensionalAxisBox a b)) :
    IsCompact (closure Ω) := by
  rcases hΩ with ⟨c, R, hR, rfl⟩ | ⟨hd, a, b, hab, heq⟩
  · exact (Metric.isBounded_ball.subset (PDE.euclideanBall_subset_supBall hR)).isCompact_closure
  · cases hd
    have heq' : Ω = PDE.oneDimensionalAxisBox a b := by simpa using heq
    rw [heq']
    exact (PDE.isBoundedDomain_axisBox (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)).isBounded
      |>.isCompact_closure

/-- Maximum principle on the entire closed moving tube over a finite subdivision.
This includes initial, terminal, lateral, and subdivision slices. The source's
piecewise C¹ curve assumption can be weakened to continuity. -/
theorem movingDomain_maximumPrinciple {d : ℕ}
    {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    {B : FullKineticCoefficient d} {drift : PDE.Vec d → PDE.Vec d}
    {u : KineticPoint d → ℝ}
    (hΩ : (∃ c R, 0 < R ∧ Ω = PDE.euclideanBall c R) ∨
      (∃ hd : d = 1, ∃ a b, a < b ∧ hd ▸ Ω = PDE.oneDimensionalAxisBox a b))
    (n : ℕ) :
    ∀ (r : Fin (n + 2) → ℝ) (_ : StrictMono r)
    (_ : ContinuousOn γ (Icc (r 0) (r (Fin.last (n + 1)))))
    (_ : ContinuousOn u (maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 1)))))
    (_ : IsTransportIndependentOn u (maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 1)))) ∨
      IsUniformlyNegAtInfinityOn u (maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 1)))))
    (_ : ∀ i : Fin (n + 1), ∀ p ∈
      maximumOpenTube Ω γ (r i.castSucc) (r i.succ),
      DifferentiableAt ℝ (fun t => u ⟨t, p.position, p.velocity⟩) p.time ∧
      ContDiffAt ℝ 2 (fun v => u ⟨p.time, v, p.velocity⟩) p.position ∧
      DifferentiableAt ℝ (fun z => u ⟨p.time, p.position, z⟩) p.velocity)
    (_ : ∀ i : Fin (n + 1), ∀ p ∈
      maximumOpenTube Ω γ (r i.castSucc) (r i.succ),
      (B p.time p.position p.velocity).PosSemidef)
    (_ : ∀ i : Fin (n + 1), ∀ p ∈
      maximumOpenTube Ω γ (r i.castSucc) (r i.succ),
      0 ≤ transportedForwardOperator B drift u p)
    (_ : ∀ p ∈ maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 1))),
      p.time = r (Fin.last (n + 1)) → u p ≤ 0)
    (_ : ∀ p ∈ maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 1))),
      p.position ∈ frontier (movingDomain Ω γ p.time) → u p ≤ 0),
    ∀ q ∈ maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 1))), u q ≤ 0  := by
  have nonpos_on_piecewise_maximumClosedTube {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d} (hΩ : IsOpen Ω) (hcΩ : IsCompact (closure Ω)) :
      ∀ (r : Fin (n + 2) → ℝ) (_ : StrictMono r)
    (_ : ContinuousOn γ (Icc (r 0) (r (Fin.last (n + 1)))))
    (_ : ContinuousOn u (maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 1)))))
    (_ : IsTransportIndependentOn u (maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 1)))) ∨
      IsUniformlyNegAtInfinityOn u (maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 1)))))
    (_ : ∀ i : Fin (n + 1), ∀ p ∈
      maximumOpenTube Ω γ (r i.castSucc) (r i.succ),
      DifferentiableAt ℝ (fun t => u ⟨t, p.position, p.velocity⟩) p.time ∧
      ContDiffAt ℝ 2 (fun v => u ⟨p.time, v, p.velocity⟩) p.position ∧
      DifferentiableAt ℝ (fun z => u ⟨p.time, p.position, z⟩) p.velocity)
    (_ : ∀ i : Fin (n + 1), ∀ p ∈
      maximumOpenTube Ω γ (r i.castSucc) (r i.succ),
      (B p.time p.position p.velocity).PosSemidef)
    (_ : ∀ i : Fin (n + 1), ∀ p ∈
      maximumOpenTube Ω γ (r i.castSucc) (r i.succ),
      0 ≤ transportedForwardOperator B drift u p)
    (_ : ∀ p ∈ maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 1))),
      p.time = r (Fin.last (n + 1)) → u p ≤ 0)
    (_ : ∀ p ∈ maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 1))),
      p.position ∈ frontier (movingDomain Ω γ p.time) → u p ≤ 0),
    ∀ q ∈ maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 1))), u q ≤ 0 := by
    induction n with
    | zero =>
      intro r hr hγ hu hc hreg hB hsub ht hl
      exact nonpos_on_maximumClosedTube (hr (by decide)) hΩ hcΩ hγ hu hc
        (hreg 0) (hB 0) (hsub 0) ht hl
    | succ n ih =>
      intro r hr hγ hu hc hreg hB hsub ht hl
      let s : Fin (n + 2) → ℝ := fun i => r i.succ
      have hs : StrictMono s := hr.comp Fin.strictMono_succ
      have htail : maximumClosedTube Ω γ (s 0) (s (Fin.last (n + 1))) ⊆
          maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 2))) := by
        intro p hp
        exact ⟨⟨(hr.monotone (Fin.zero_le _)).trans hp.1.1, hp.1.2⟩, hp.2⟩
      have hcTail : IsTransportIndependentOn u
          (maximumClosedTube Ω γ (s 0) (s (Fin.last (n + 1)))) ∨
          IsUniformlyNegAtInfinityOn u
          (maximumClosedTube Ω γ (s 0) (s (Fin.last (n + 1)))) := by
        rcases hc with hi | hn
        · exact Or.inl (fun p hp => hi p (htail hp))
        · right
          intro M
          obtain ⟨R, hR, hb⟩ := hn M
          exact ⟨R, hR, fun p hp => hb p (htail hp)⟩
      have htailResult := ih s hs
        (hγ.mono (Icc_subset_Icc (hr.monotone (Fin.zero_le _)) le_rfl))
        (hu.mono htail) hcTail
        (fun i => hreg i.succ) (fun i => hB i.succ) (fun i => hsub i.succ)
        (fun p hp => ht p (htail hp)) (fun p hp => hl p (htail hp))
      have hhead : maximumClosedTube Ω γ (r 0) (s 0) ⊆
          maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 2))) := by
        intro p hp
        exact ⟨⟨hp.1.1, hp.1.2.trans (hr.monotone (Fin.le_last _))⟩, hp.2⟩
      have hcHead : IsTransportIndependentOn u (maximumClosedTube Ω γ (r 0) (s 0)) ∨
          IsUniformlyNegAtInfinityOn u (maximumClosedTube Ω γ (r 0) (s 0)) := by
        rcases hc with hi | hn
        · exact Or.inl (fun p hp => hi p (hhead hp))
        · right
          intro M
          obtain ⟨R, hR, hb⟩ := hn M
          exact ⟨R, hR, fun p hp => hb p (hhead hp)⟩
      intro q hq
      by_cases hqtime : q.time ≤ s 0
      · exact (nonpos_on_maximumClosedTube (hr (show 0 < (0 : Fin (n + 2)).succ by simp)) hΩ hcΩ (hγ.mono (Icc_subset_Icc le_rfl (hr.monotone (Fin.le_last _)))) (hu.mono hhead) hcHead (hreg 0) (hB 0) (hsub 0) (fun p hp heq => htailResult p ⟨⟨heq.ge, (hhead hp).1.2⟩, hp.2⟩) (fun p hp => hl p (hhead hp))) q ⟨⟨hq.1.1, hqtime⟩, hq.2⟩
      · exact htailResult q ⟨⟨(lt_of_not_ge hqtime).le, hq.1.2⟩, hq.2⟩
  exact nonpos_on_piecewise_maximumClosedTube (isOpen_of_isAdmissibleEvolutionDomain (Or.inr hΩ))
    (isCompact_closure_of_maximumPrinciple_domain hΩ)

end HypoellipticAleksandrov.KineticAleksandrov.Decay

