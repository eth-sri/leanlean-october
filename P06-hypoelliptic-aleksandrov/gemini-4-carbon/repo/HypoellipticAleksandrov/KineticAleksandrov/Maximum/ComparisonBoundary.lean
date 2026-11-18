module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.InnerCylinderGeometry
public import Mathlib.Topology.Algebra.ConstMulAction
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.InnerCylinderReflection
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.UniformSpace.HeineCantor

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
open Set Filter

/-- The retraction has exactly the source formula on relative coordinates. -/
theorem innerRetraction_relative {d : ℕ} (Z₀ P : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2) :
    let ρ := innerRatio R hR δ hδ0 hδlt
    let Q := innerRetraction Z₀ R hR δ hδ0 hδlt P
    Q.time = Z₀.time + δ + ρ ^ 2 * (P.time - Z₀.time) ∧
      relativePosition Z₀ Q = ρ ^ 3 • relativePosition Z₀ P ∧
      relativeVelocity Z₀ Q = ρ • relativeVelocity Z₀ P := by
  refine ⟨rfl,?_,?_⟩
  · ext i
    simp [relativePosition, innerRetraction]
    ring
  · ext i
    simp [relativeVelocity, innerRetraction]

/-- The affine inner map as a homeomorphism, with an explicit positive-scaling inverse. -/
def innerRetractionHomeomorph {d : ℕ} (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2) : KineticPoint d ≃ₜ KineticPoint d :=
  let ρ := innerRatio R hR δ hδ0 hδlt
  let hρ := (innerRatio_spec R hR δ hδ0 hδlt).1.ne'
  let ht := ((Homeomorph.subRight Z₀.time).trans
    (Homeomorph.mulLeft₀ (ρ^2) (pow_ne_zero 2 hρ))).trans
      (Homeomorph.addLeft (Z₀.time+δ))
  let hx := Homeomorph.smulOfNeZero (ρ^3) (pow_ne_zero 3 hρ) (α := PDE.Vec d)
  let hv := Homeomorph.smulOfNeZero ρ hρ (α := PDE.Vec d)
  ((relativeHomeomorph Z₀).trans (ht.prodCongr (hx.prodCongr hv))).trans
    (relativeHomeomorph Z₀).symm

private theorem smul_ball_iff {d : ℕ} (x : PDE.Vec d) (a r : ℝ) (ha : 0 < a) :
    a • x ∈ PDE.euclideanBall 0 (a*r) ↔ x ∈ PDE.euclideanBall 0 r := by
  change PDE.vecNormSq (a • x - 0) < (a*r)^2 ↔ PDE.vecNormSq (x-0) < r^2
  simp [PDE.vecNormSq_smul, mul_pow]
  exact mul_lt_mul_iff_right₀ (sq_pos_of_pos ha)

private theorem smul_sphere_iff {d : ℕ} (x : PDE.Vec d) (a r : ℝ) (ha : 0 < a) :
    a • x ∈ PDE.euclideanSphere 0 (a*r) ↔ x ∈ PDE.euclideanSphere 0 r := by
  change PDE.vecNormSq (a • x - 0) = (a*r)^2 ↔ PDE.vecNormSq (x-0) = r^2
  simp only [sub_zero, PDE.vecNormSq_smul, mul_pow]
  constructor
  · exact mul_left_cancel₀ (ne_of_gt (sq_pos_of_pos ha))
  · intro h
    rw [h]



/-- Retraction is onto on the closures. -/
theorem innerRetraction_image_closure {d : ℕ}
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2) :
    innerRetraction Z₀ R hR δ hδ0 hδlt '' closure (forwardCylinder Z₀ R hR) =
      closure (innerCylinder Z₀ R hR δ hδ0 hδlt)  := by
  have innerRetraction_image_forwardCylinder (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2) :
      innerRetraction Z₀ R hR δ hδ0 hδlt '' forwardCylinder Z₀ R hR =
      innerCylinder Z₀ R hR δ hδ0 hδlt := by
    have retraction_mem_inner_iff (Z₀ P : KineticPoint d) (R : ℝ) (hR : 0 < R) (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2) :
        innerRetraction Z₀ R hR δ hδ0 hδlt P ∈ innerCylinder Z₀ R hR δ hδ0 hδlt ↔
        P ∈ forwardCylinder Z₀ R hR := by
      obtain ⟨hρ,_,hs⟩ := innerRatio_spec R hR δ hδ0 hδlt
      have hr := innerRetraction_relative Z₀ P R hR δ hδ0 hδlt
      dsimp only at hr
      rw [mem_innerCylinder_iff, mem_forwardCylinder_iff, hr.1, hr.2.1, hr.2.2,
        smul_ball_iff _ _ _ hρ, smul_ball_iff _ _ _ (pow_pos hρ 3)]
      have hv : relativeVelocity Z₀ P ∈ PDE.euclideanBall 0 R ↔
          P.velocity ∈ PDE.euclideanBall Z₀.velocity R := by
        simp [relativeVelocity, PDE.euclideanBall, PDE.euclideanSqDist]
      rw [hv]
      constructor <;> rintro ⟨h1,h2,hv,hx⟩ <;> refine ⟨?_,?_,hv,hx⟩ <;>
        nlinarith [sq_pos_of_pos hρ]
    ext P
    constructor
    · rintro ⟨Q,hQ,rfl⟩
      exact (retraction_mem_inner_iff Z₀ Q R hR δ hδ0 hδlt).2 hQ
    · intro hP
      let e := innerRetractionHomeomorph Z₀ R hR δ hδ0 hδlt
      refine ⟨e.symm P,?_,e.apply_symm_apply P⟩
      apply (retraction_mem_inner_iff Z₀ (e.symm P) R hR δ hδ0 hδlt).1
      change e (e.symm P) ∈ innerCylinder Z₀ R hR δ hδ0 hδlt
      simpa using hP
  rw [← innerRetraction_image_forwardCylinder Z₀ R hR δ hδ0 hδlt]
  exact (innerRetractionHomeomorph Z₀ R hR δ hδ0 hδlt).image_closure _



/-- Retraction is onto on the exit boundaries, including grazing points. -/
theorem innerRetraction_image_exitBoundary {d : ℕ}
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2) :
    innerRetraction Z₀ R hR δ hδ0 hδlt '' exitBoundary Z₀ R hR =
      innerExitBoundary Z₀ R hR δ hδ0 hδlt  := by
  have retraction_mem_exit_iff (Z₀ P : KineticPoint d) (R : ℝ) (hR : 0 < R) (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2) :
      innerRetraction Z₀ R hR δ hδ0 hδlt P ∈ innerExitBoundary Z₀ R hR δ hδ0 hδlt ↔
      P ∈ exitBoundary Z₀ R hR := by
    have retraction_dot (Z₀ P : KineticPoint d) (R : ℝ) (hR : 0 < R) (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2) :
        PDE.vecDot (relativeVelocity Z₀ (innerRetraction Z₀ R hR δ hδ0 hδlt P))
          (relativePosition Z₀ (innerRetraction Z₀ R hR δ hδ0 hδlt P)) =
        (innerRatio R hR δ hδ0 hδlt)^4 *
          PDE.vecDot (relativeVelocity Z₀ P) (relativePosition Z₀ P) := by
      have hr := innerRetraction_relative Z₀ P R hR δ hδ0 hδlt
      dsimp only at hr
      rw [hr.2.1,hr.2.2]
      unfold PDE.vecDot
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp
      ring
    obtain ⟨hρ,_,hs⟩ := innerRatio_spec R hR δ hδ0 hδlt
    have hr := innerRetraction_relative Z₀ P R hR δ hδ0 hδlt
    dsimp only at hr
    rw [mem_innerExitBoundary_iff,mem_exitBoundary_iff]
    dsimp only
    rw [← innerRetraction_image_closure Z₀ R hR δ hδ0 hδlt]
    have hi : innerRetraction Z₀ R hR δ hδ0 hδlt P ∈
        innerRetraction Z₀ R hR δ hδ0 hδlt '' closure (forwardCylinder Z₀ R hR) ↔
        P ∈ closure (forwardCylinder Z₀ R hR) :=
      (innerRetractionHomeomorph Z₀ R hR δ hδ0 hδlt).injective.mem_set_image
    rw [hi,hr.1,hr.2.1,hr.2.2,smul_sphere_iff _ _ _ hρ,
      smul_sphere_iff _ _ _ (pow_pos hρ 3)]
    have ht : Z₀.time+δ+(innerRatio R hR δ hδ0 hδlt)^2*(P.time-Z₀.time) =
        Z₀.time+R^2-δ ↔ P.time = Z₀.time+R^2 := by
      constructor <;> intro h <;> nlinarith [sq_pos_of_pos hρ]
    have hv : relativeVelocity Z₀ P ∈ PDE.euclideanSphere 0 R ↔
        P.velocity ∈ PDE.euclideanSphere Z₀.velocity R := by
      simp [relativeVelocity,PDE.euclideanSphere,PDE.euclideanSqDist]
    rw [ht,hv]
    have hd := retraction_dot Z₀ P R hR δ hδ0 hδlt
    rw [hr.2.1,hr.2.2] at hd
    rw [hd, mul_nonneg_iff_of_pos_left (pow_pos hρ 4)]
  ext P
  constructor
  · rintro ⟨Q,hQ,rfl⟩
    exact (retraction_mem_exit_iff Z₀ Q R hR δ hδ0 hδlt).2 hQ
  · intro hP
    let e := innerRetractionHomeomorph Z₀ R hR δ hδ0 hδlt
    refine ⟨e.symm P,?_,e.apply_symm_apply P⟩
    apply (retraction_mem_exit_iff Z₀ (e.symm P) R hR δ hδ0 hδlt).1
    change e (e.symm P) ∈ innerExitBoundary Z₀ R hR δ hδ0 hδlt
    simpa using hP


/-- Exact epsilon formulation of uniform convergence on the original closure. -/
theorem innerRetraction_uniformly_to_identity {d : ℕ}
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2), δ < η →
        ∀ P ∈ closure (forwardCylinder Z₀ R hR),
          dist (innerRetraction Z₀ R hR δ hδ0 hδlt P) P < ε := by
  let f : ℝ → KineticPoint d → KineticPoint d := fun δ P =>
    let ρ := Real.sqrt (1 - 2 * δ / R ^ 2)
    let s := Z₀.time + δ + ρ ^ 2 * (P.time - Z₀.time)
    ⟨s, Z₀.position + (s - Z₀.time) • Z₀.velocity + ρ ^ 3 • relativePosition Z₀ P,
      Z₀.velocity + ρ • relativeVelocity Z₀ P⟩
  have hc : Continuous (Function.uncurry f) := by
    have ht : Continuous (fun q : ℝ × KineticPoint d => q.2.time) :=
      continuous_time.comp continuous_snd
    have hx : Continuous (fun q : ℝ × KineticPoint d => q.2.position) :=
      continuous_position.comp continuous_snd
    have hv : Continuous (fun q : ℝ × KineticPoint d => q.2.velocity) :=
      continuous_velocity.comp continuous_snd
    have hρ : Continuous (fun q : ℝ × KineticPoint d =>
        Real.sqrt (1 - 2 * q.1 / R^2)) :=
      Real.continuous_sqrt.comp (continuous_const.sub
        ((continuous_const.mul continuous_fst).div_const _))
    have hs : Continuous (fun q : ℝ × KineticPoint d => Z₀.time + q.1 +
        (Real.sqrt (1 - 2 * q.1 / R^2))^2 * (q.2.time - Z₀.time)) :=
      (continuous_const.add continuous_fst).add
      ((hρ.pow 2).mul (ht.sub continuous_const))
    exact KineticPoint.continuous_mk hs
      ((continuous_const.add ((hs.sub continuous_const).smul continuous_const)).add
        ((hρ.pow 3).smul ((hx.sub continuous_const).sub
          ((ht.sub continuous_const).smul continuous_const))))
      (continuous_const.add (hρ.smul (hv.sub continuous_const)))
  have h0 : ∀ P, f 0 P = P := by
    intro P
    ext i <;> simp [f, relativePosition, relativeVelocity] <;> ring
  intro ε hε
  obtain ⟨v,hv,he⟩ := (isCompact_closure_forwardCylinder Z₀ R hR).mem_uniformity_of_prod
    (s := univ) (q := 0) hc.continuousOn (mem_univ 0)
    (Metric.dist_mem_uniformity hε)
  have hv' : v ∈ nhds 0 := by simpa using hv
  obtain ⟨η,hη,hηv⟩ := Metric.mem_nhds_iff.mp hv'
  refine ⟨η,hη,?_⟩
  intro δ hδ0 hδlt hδη P hP
  have he' := he δ (hηv (show δ ∈ Metric.ball 0 η by simpa [Real.dist_eq,abs_of_pos hδ0])) P hP
  change dist (f δ P) (f 0 P) < ε at he'
  rw [h0] at he'
  exact he'





/-- Reflection preserves the existing product-metric distance, used only topologically. -/
theorem dist_kineticReflection {d : ℕ} (P Q : KineticPoint d) :
    dist (kineticReflection P) (kineticReflection Q) = dist P Q := by
  change dist (-P.time,(-P.position,P.velocity)) (-Q.time,(-Q.position,Q.velocity)) =
    dist (P.time,(P.position,P.velocity)) (Q.time,(Q.position,Q.velocity))
  simp only [Prod.dist_eq, dist_neg_neg]



/-- Uniform continuity transfers a compact-boundary upper bound through a close map. -/
theorem boundary_value_le_of_close_map {E : Type*} [MetricSpace E]
    {K S : Set E} {u : E → ℝ} (hK : IsCompact K) (hu : ContinuousOn u K)
    (hSK : S ⊆ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ T : E → E,
      (∀ x ∈ S, T x ∈ K) → (∀ x ∈ S, dist (T x) x < η) →
      ∀ x ∈ S, max (u (T x)) 0 ≤ sSup ((fun x => max (u x) 0) '' S) + ε := by
  have hc : ContinuousOn (fun x => max (u x) 0) K := hu.sup continuousOn_const
  obtain ⟨η,hη,hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hc) ε hε
  refine ⟨η,hη,?_⟩
  intro T hTK hdist x hx
  have hd := hclose (T x) (hTK x hx) x (hSK hx) (hdist x hx)
  have hb :=
    (hK.bddAbove_image hc).mono (image_mono hSK)
  have hs := le_csSup hb (mem_image_of_mem (fun x => max (u x) 0) hx)
  rw [Real.dist_eq] at hd
  have hle := (abs_lt.mp hd).2
  linarith

/-- Exit-boundary values on inner cylinders approach the original exit-boundary bound. -/
theorem comparison_exit_boundary_approx {d : ℕ}
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) (u : KineticPoint d → ℝ)
    (hu : ContinuousOn u (closure (forwardCylinder Z₀ R hR)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2),
      δ < η → ∀ P ∈ innerExitBoundary Z₀ R hR δ hδ0 hδlt,
        max (u P) 0 ≤ sSup ((fun P => max (u P) 0) '' exitBoundary Z₀ R hR) + ε := by
  have hS : exitBoundary Z₀ R hR ⊆ closure (forwardCylinder Z₀ R hR) :=
    fun _ h => h.1
  obtain ⟨r,hr,hbound⟩ := boundary_value_le_of_close_map
    (isCompact_closure_forwardCylinder Z₀ R hR) hu hS hε
  obtain ⟨η,hη,hclose⟩ := innerRetraction_uniformly_to_identity Z₀ R hR r hr
  refine ⟨η,hη,?_⟩
  intro δ hδ0 hδlt hδη P hP
  rw [← innerRetraction_image_exitBoundary Z₀ R hR δ hδ0 hδlt] at hP
  obtain ⟨x,hx,rfl⟩ := hP
  apply hbound (innerRetraction Z₀ R hR δ hδ0 hδlt) ?_ ?_ x hx
  · intro y hy
    apply subset_closure (closure_innerCylinder_subset Z₀ R hR δ hδ0 hδlt ?_)
    rw [← innerRetraction_image_closure Z₀ R hR δ hδ0 hδlt]
    exact mem_image_of_mem _ (hS hy)
  · exact fun y hy => hclose δ hδ0 hδlt hδη y (hS hy)

/-- The same compact-boundary passage in the backward kinetic geometry. -/
theorem comparison_kinetic_boundary_approx {d : ℕ}
    (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) (u : KineticPoint d → ℝ)
    (hu : ContinuousOn u (closure (backwardCylinder P₀ R)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2),
      δ < η → ∀ P ∈ kineticBoundary
        ⟨P₀.time - δ, P₀.position - δ • P₀.velocity, P₀.velocity⟩
        (innerRatio R hR δ hδ0 hδlt * R),
        max (u P) 0 ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) + ε     := by
  have reflection_closure_backward (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) :
      kineticReflection '' closure (backwardCylinder P₀ R) =
      closure (forwardCylinder (kineticReflection P₀) R hR) := by
    rw [kineticReflection_image_closure,
      kineticReflection_image_backwardCylinder]
  have reflectedInnerRetraction_uniformly_to_identity (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) :
      ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2), δ < η →
        ∀ P ∈ closure (backwardCylinder P₀ R),
          dist (reflectedInnerRetraction P₀ R hR δ hδ0 hδlt P) P < ε := by
    intro ε hε
    obtain ⟨η,hη,he⟩ := innerRetraction_uniformly_to_identity (kineticReflection P₀) R hR ε hε
    refine ⟨η,hη,?_⟩
    intro δ hδ0 hδlt hδη P hP
    have hp : kineticReflection P ∈ closure (forwardCylinder (kineticReflection P₀) R hR) := by
      rw [← reflection_closure_backward P₀ R hR]
      exact mem_image_of_mem _ hP
    have h := he δ hδ0 hδlt hδη (kineticReflection P) hp
    have hd := dist_kineticReflection
      (innerRetraction (kineticReflection P₀) R hR δ hδ0 hδlt (kineticReflection P))
      (kineticReflection P)
    rw [kineticReflection_involutive P] at hd
    change dist (kineticReflection
      (innerRetraction (kineticReflection P₀) R hR δ hδ0 hδlt (kineticReflection P))) P < ε
    rw [hd]
    exact h
  have reflectedInnerRetraction_image_kineticBoundary (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2) :
      reflectedInnerRetraction P₀ R hR δ hδ0 hδlt '' kineticBoundary P₀ R =
      kineticBoundary
        ⟨P₀.time - δ, P₀.position - δ • P₀.velocity, P₀.velocity⟩
        (innerRatio R hR δ hδ0 hδlt * R) := by
    change (kineticReflection ∘ (innerRetraction (kineticReflection P₀) R hR δ hδ0 hδlt ∘
      kineticReflection)) '' _ = _
    simp
    rw [← image_image kineticReflection
      (fun P => innerRetraction (kineticReflection P₀) R hR δ hδ0 hδlt
        (kineticReflection P)),
      ← image_image (innerRetraction (kineticReflection P₀) R hR δ hδ0 hδlt)
        kineticReflection, kineticReflection_image_kineticBoundary P₀ R hR,
      innerRetraction_image_exitBoundary,kineticReflection_image_innerExitBoundary]
  have reflectedInnerRetraction_image_closure (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2) :
      reflectedInnerRetraction P₀ R hR δ hδ0 hδlt '' closure (backwardCylinder P₀ R) =
      closure (backwardCylinder
        ⟨P₀.time - δ, P₀.position - δ • P₀.velocity, P₀.velocity⟩
        (innerRatio R hR δ hδ0 hδlt * R)) := by
    change (kineticReflection ∘ (innerRetraction (kineticReflection P₀) R hR δ hδ0 hδlt ∘
      kineticReflection)) '' _ = _
    simp
    rw [← image_image kineticReflection
      (fun P => innerRetraction (kineticReflection P₀) R hR δ hδ0 hδlt
        (kineticReflection P)),
      ← image_image (innerRetraction (kineticReflection P₀) R hR δ hδ0 hδlt)
        kineticReflection, reflection_closure_backward P₀ R hR,
      innerRetraction_image_closure,kineticReflection_image_closure,
      kineticReflection_image_innerCylinder]
  have hS : kineticBoundary P₀ R ⊆ closure (backwardCylinder P₀ R) := fun _ h => h.1
  have hcompact : IsCompact (closure (backwardCylinder P₀ R)) := by
    have h := (isCompact_closure_forwardCylinder (kineticReflection P₀) R hR).image
      (continuous_kineticReflection d)
    rw [kineticReflection_image_closure, kineticReflection_image_forwardCylinder,
      kineticReflection_involutive P₀] at h
    exact h
  obtain ⟨r,hr,hbound⟩ := boundary_value_le_of_close_map hcompact hu hS hε
  obtain ⟨η,hη,hclose⟩ := reflectedInnerRetraction_uniformly_to_identity P₀ R hR r hr
  refine ⟨η,hη,?_⟩
  intro δ hδ0 hδlt hδη P hP
  rw [← reflectedInnerRetraction_image_kineticBoundary P₀ R hR δ hδ0 hδlt] at hP
  obtain ⟨x,hx,rfl⟩ := hP
  apply hbound (reflectedInnerRetraction P₀ R hR δ hδ0 hδlt) ?_ ?_ x hx
  · intro y hy
    apply subset_closure ((closure_reflected_innerCylinder_subset P₀ R hR δ hδ0 hδlt) ?_)
    rw [kineticReflection_image_innerCylinder P₀ R hR δ hδ0 hδlt]
    rw [← reflectedInnerRetraction_image_closure P₀ R hR δ hδ0 hδlt]
    exact mem_image_of_mem _ (hS hy)
  · exact fun y hy => hclose δ hδ0 hδlt hδη y (hS hy)

end HypoellipticAleksandrov.KineticAleksandrov

