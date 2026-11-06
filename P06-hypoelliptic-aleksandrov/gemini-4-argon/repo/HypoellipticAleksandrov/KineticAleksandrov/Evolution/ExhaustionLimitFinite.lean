module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitEquation
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitTrace
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.PastGluingFinite
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitClassical
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitBoundary
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.PastGluingLocality
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExternalRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitAdjoint
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCollarApproximation
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitCollar
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitCover
import Mathlib.Topology.UniformSpace.UniformApproximation
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitRegularity
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitWeak

/-!
# Actual finite-slab classical ball solutions

All finite-slab steps are supplied by the actual exhaustion construction:
bounds, continuity, interior smoothness, the pointwise equation, and both traces.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter MeasureTheory
open Evolution
open scoped Topology MatrixOrder

/- Actual finite ball approximants yield a classical finite-slab solution relative
to the explicit Hörmander input. No boundary estimate or weak equation is assumed. -/
theorem isClassicalViscousFiniteSolution_innerBallDirichletLimit
    (hH : HormanderHypoellipticityStatement)
    {n lam Lam Lb m B b}
    (hn : 1 ≤ n) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hm : 0 < m) (hmLb : m ≤ Lb) (hB : HasEverywhereLoewnerBounds lam Lam B)
    (hBs : IsSmoothFullKineticCoefficient B)
    (hBsym : IsSymmetricFullKineticCoefficient B) (hbs : IsSmoothDrift b)
    (hb : HasEuclideanLipschitzDrift Lb b)
    (hbco : HasUnitDirectionDriftCoercivity m b)
    {a α τ r0 d L C ε } (haα : a < α) (hατ : α < τ)
    (hd : 0 < d) (hdr : d < r0 / 4)
    (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C)
    {Γ } (hΓ : IsContinuousPiecewiseC1 Γ)
    (F : BoundedBorel (EvolutionAmbientState n)) (hFC : ∀ q, |F q| ≤ C)
    (hsupp : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      4 * d ≤ r0 - PDE.vecEuclideanNorm (q.1 - Γ τ))
    (β R : ℕ → ℝ) (hβpos : ∀ k, 0 < β k)
    (hβlim : Tendsto β atTop (𝓝 0)) (hRlim : Tendsto R atTop atTop)
    (g : ℕ → ℝ → PDE.Vec n) (hg : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (g k))
    (hgL : ∀ k s t, PDE.vecEuclideanNorm (g k s - g k t) ≤ L * |s - t|)
    (hclose : ∀ k s, s ∈ Icc α τ → PDE.vecEuclideanNorm (g k s - Γ s) ≤ β k / 2)
    (u : ℕ → TimeVelocity (n + n) → ℝ)
    (hu : ∀ k, IsClassicalBackwardDirichletSolution a τ
      (openEllipsoid (straightenedEllipsoidMatrix n (r0 - β k) (R k)))
      (straightenedCoefficient B (g k) ε) (straightenedDrift b (g k))
      (fun _ _ => 0) (fun _ _ => 0)
      (fun x => F (g k τ + spatialY x, spatialZ x)) (fun _ => 0) (u k)) :
    IsClassicalViscousFiniteSolution (PDE.euclideanBall 0 r0) Γ B b ε α τ F
      (innerBallDirichletLimit r0 Γ g u) := by
  have hr0 : 0 < r0 := by linarith
  have htrace := innerBallDirichletLimit_bound_terminal_lateral
    hlam hB hBs hbs hb haα hατ hd hdr hL hε.le hε1 hC hΓ.1
    F hFC hsupp β R hβpos hβlim hRlim g hg hgL hclose u hu
  have hcont : ContinuousOn (innerBallDirichletLimit r0 Γ g u)
      (movingClosedSlab (PDE.euclideanBall 0 r0) Γ α τ) := by
    have hε := hε.le
    have hΓ := hΓ.1
    have hr0 : 0 < r0 := by linarith
    let K := movingClosedSlab (PDE.euclideanBall 0 r0) Γ α τ
    have hbound : ∀ p ∈ movingClosedSlab (PDE.euclideanBall 0 r0) Γ α τ,
        |innerBallDirichletLimit r0 Γ g u p| ≤ C *
          (barrierW (collarKappa L lam) (r0 - PDE.vecEuclideanNorm (p.position - Γ p.time)) /
            barrierW (collarKappa L lam) d) := by
        have hr0 : 0 < r0 := by linarith
        intro p hp
        by_cases hi : p.position ∈ movingDomain (PDE.euclideanBall 0 r0) Γ p.time
        · obtain ⟨δ, S, hδ, hδr, hpK, -⟩ :=
            exists_innerClosedCylinder_mem_nhdsWithin hΓ hr0 hp hi
          rw [innerBallDirichletLimit_eq_limit r0 Γ g u hi]
          exact abs_le_collar_innerBall_dirichlet_limit (S0 := S)
            hlam hB hBs hbs hb haα hατ hδ hδr hd hdr hL hε hε1 hC hΓ
            F hFC hsupp β R hβpos hβlim hRlim g hg hgL hclose u hu p hpK
        · have hn : PDE.vecEuclideanNorm (p.position - Γ p.time) = r0 :=
            le_antisymm (norm_le_of_mem_closure_movingBall hr0 hp.2.2)
              (not_lt.mp (fun hn => hi ((mem_movingBall_iff_norm_lt hr0).mpr hn)))
          simp only [innerBallDirichletLimit, ite_eq_right hi, hn, sub_self, barrierW,
            mul_zero, Real.exp_zero, zero_div, mul_zero, abs_zero, le_refl]

      /- The actual exhaustion limit, extended by zero on the diffused boundary, is continuous
      on the entire original closed slab, including its time faces. -/
    intro p hp
    by_cases hi : p.position ∈ movingDomain (PDE.euclideanBall 0 r0) Γ p.time
    · obtain ⟨δ, S, hδ, hδr, hpK, hKnhds⟩ :=
        exists_innerClosedCylinder_mem_nhdsWithin hΓ hr0 hp hi
      have hc := (continuousOn_bounded_innerBall_dirichlet_limit (S0 := S)
        hlam hB hBs hbs hb haα hατ hδ hδr hd hdr hL hε hε1 hC hΓ
        F hFC hsupp β R hβpos hβlim hRlim g hg hgL hclose u hu).1 p hpK
      have heq : ∀ q ∈ movingClosedSlab (PDE.euclideanBall 0 (r0 - δ)) Γ α τ ∩
          {q | radialSq q ≤ S ^ 2}, innerBallDirichletLimit r0 Γ g u q =
          limUnder atTop (fun k => straightenedPullback (g k) (u k) q) :=
        fun q hq => innerBallDirichletLimit_eq_limit r0 Γ g u
          (innerClosedCylinder_subset_movingBall hδ hδr hq)
      exact (hc.congr heq (innerBallDirichletLimit_eq_limit r0 Γ g u hi)).mono_of_mem_nhdsWithin
        hKnhds
    · have hn : PDE.vecEuclideanNorm (p.position - Γ p.time) = r0 :=
        le_antisymm (norm_le_of_mem_closure_movingBall hr0 hp.2.2)
          (not_lt.mp (fun hn => hi ((mem_movingBall_iff_norm_lt hr0).mpr hn)))
      let G (q : KineticPoint n) := C *
        (barrierW (collarKappa L lam) (r0 - PDE.vecEuclideanNorm (q.position - Γ q.time)) /
          barrierW (collarKappa L lam) d)
      have hdist : Continuous (fun q : KineticPoint n =>
          PDE.vecEuclideanNorm (q.position - Γ q.time)) :=
        PDE.continuous_vecEuclideanNorm.comp
          (continuous_position.sub (hΓ.comp continuous_time))
      have hGc : Continuous G := by dsimp [G, barrierW]; fun_prop
      have hGp : G p = 0 := by
        simp only [G, hn, sub_self, barrierW, mul_zero, Real.exp_zero, zero_div, mul_zero]
      have hGlim : Tendsto G (𝓝[K] p) (𝓝 0) :=
        hGp ▸ hGc.continuousWithinAt.tendsto
      have hKmem : ∀ᶠ q in 𝓝[K] p, q ∈ K := self_mem_nhdsWithin
      have hz : Tendsto (innerBallDirichletLimit r0 Γ g u) (𝓝[K] p) (𝓝 0) :=
        squeeze_zero_norm' (hKmem.mono fun q hq =>
          (show ‖innerBallDirichletLimit r0 Γ g u q‖ ≤ G q from
            (by rw [Real.norm_eq_abs]; exact hbound q hq))) hGlim
      simpa only [ContinuousWithinAt, innerBallDirichletLimit, ite_eq_right hi] using hz
  have hlocal (δ S : ℝ) (hδ : 0 < δ) (hδr : δ < r0) : ContDiffOn ℝ (⊤ : ℕ∞) (innerBallDirichletLimit r0 Γ g u ∘ evolutionHomeomorph n)
      (evolutionHomeomorph n ⁻¹' boundedInnerOpenCylinder (r0 - δ) Γ α τ (S)) ∧
    ∀ p ∈ boundedInnerOpenCylinder (r0 - δ) Γ α τ (S),
      viscousTransportedOperator B b ε (innerBallDirichletLimit r0 Γ g u) p = 0 := by
    let S0 := (S)
    let U := boundedInnerOpenCylinder (r0 - δ) Γ α τ S0
    let vlim (p : KineticPoint n) :=
      limUnder atTop (fun k => straightenedPullback (g k) (u k) p)
    have hU : IsOpen U := isOpen_boundedInnerOpenCylinder _ hΓ.1 _ _ _
    have hV : IsOpen (evolutionHomeomorph n ⁻¹' U) :=
      hU.preimage (evolutionHomeomorph n).continuous
    have hsm : ContDiffOn ℝ (⊤ : ℕ∞)
        ((fun p => limUnder atTop (fun k => straightenedPullback (g k) (u k) p)) ∘
          evolutionHomeomorph n)
        (evolutionHomeomorph n ⁻¹' boundedInnerOpenCylinder (r0 - δ) Γ α τ (S0)) := by
      let S0 := (S0)
      let U := boundedInnerOpenCylinder (r0 - δ) Γ α τ S0
      let vlim (p : KineticPoint n) :=
        limUnder atTop (fun k => straightenedPullback (g k) (u k) p)
      have hU : IsOpen U := isOpen_boundedInnerOpenCylinder _ hΓ.1 _ _ _
      have hw := weakRegularized_innerBall_dirichlet_limit (S0 := S0)
        hn hlam hlamLam hm hmLb hB hBs hBsym hbs hb hbco haα hατ hδ hδr hd hdr
        hL hε hε1 hC hΓ F hFC hsupp β R hβpos hβlim hRlim g hg hgL hclose u hu
      obtain ⟨v, hvs, hae⟩ := exists_smooth_viscous_kinetic_representative
        hH hlam hBs hB hbs U hU ε hε vlim hw
      have hcLim : ContinuousOn vlim U :=
        (continuousOn_bounded_innerBall_dirichlet_limit (S0 := S0)
          hlam hB hBs hbs hb haα hατ hδ hδr hd hdr hL hε.le hε1 hC hΓ.1
          F hFC hsupp β R hβpos hβlim hRlim g hg hgL hclose u hu).1.mono
            (boundedInnerOpenCylinder_subset_closed _ Γ α τ S0)
      have hcPack : ContinuousOn (vlim ∘ evolutionHomeomorph n)
          (evolutionHomeomorph n ⁻¹' U) :=
        hcLim.comp (evolutionHomeomorph n).continuous.continuousOn (fun _ hx => hx)
      have heq := eqOn_of_ae_eq_of_continuousOn_kinetic hU hcPack hvs.continuousOn hae
      exact hvs.congr (fun x hx => heq hx)
    have hw := weakRegularized_innerBall_dirichlet_limit (S0 := S0)
      hn hlam hlamLam hm hmLb hB hBs hBsym hbs hb hbco haα hατ hδ hδr hd hdr
      hL hε hε1 hC hΓ F hFC hsupp β R hβpos hβlim hRlim g hg hgL hclose u hu
    have hwPack := (isWeakRegularizedSolution_comp_iff B b ε U vlim (fun _ => 0)).mpr hw
    have heq := regularizedOperator_eq_zero_of_smooth_weak hV hBs hBsym hbs ε hsm hwPack
    have hinside : ∀ p ∈ U, p.position ∈ movingDomain (PDE.euclideanBall 0 r0) Γ p.time :=
      fun p hp => innerClosedCylinder_subset_movingBall hδ hδr
        (boundedInnerOpenCylinder_subset_closed _ Γ α τ S0 hp)
    refine ⟨hsm.congr (fun x hx => innerBallDirichletLimit_eq_limit r0 Γ g u
      (hinside _ hx)), ?_⟩
    intro p hp
    have hnear : ∀ᶠ q in 𝓝 p,
        q.position ∈ movingDomain (PDE.euclideanBall 0 r0) Γ q.time :=
      (isOpen_setOf_mem_movingDomain (PDE.isOpen_euclideanBall 0 r0) hΓ.1).mem_nhds
        (hinside p hp)
    have hgerm : innerBallDirichletLimit r0 Γ g u =ᶠ[𝓝 p] vlim :=
      hnear.mono (fun q hq => innerBallDirichletLimit_eq_limit r0 Γ g u hq)
    rw [viscousTransportedOperator_congr_germ B b ε hgerm]
    let x := (evolutionHomeomorph n).symm p
    have hx : x ∈ evolutionHomeomorph n ⁻¹' U := by
      change evolutionHomeomorph n x ∈ U
      simpa only [x, Homeomorph.apply_symm_apply] using hp
    have hc2 : ContDiffAt ℝ 2 (vlim ∘ evolutionHomeomorph n) x :=
      (hsm.contDiffAt (hV.mem_nhds hx)).of_le (by norm_num)
    have hOp := regularizedOperator_comp (B := B) (b := b) ε hc2
    have hz := heq x hx
    rw [hOp] at hz
    simpa only [x, Homeomorph.apply_symm_apply, viscousTransportedOperator] using hz
  refine ⟨⟨C, hC, htrace.1⟩, hcont, ?_, ?_, ?_, ?_⟩
  · intro q hq
    let p : KineticPoint n := ⟨q.1, q.2.1, q.2.2⟩
    obtain ⟨δ, S, hδ, hδr, hp⟩ := exists_boundedInnerOpenCylinder_mem hr0
      (p := p) ⟨hq.1, hq.2.1⟩ hq.2.2
    let x := (evolutionProdCLE n).symm q
    have hxp : evolutionHomeomorph n x = p := by
      apply (KineticPoint.equivProd n).injective
      change (evolutionProdCLE n) ((evolutionProdCLE n).symm q) = q
      exact (evolutionProdCLE n).apply_symm_apply q
    have hx : x ∈ evolutionHomeomorph n ⁻¹'
        boundedInnerOpenCylinder (r0 - δ) Γ α τ S := by
      change evolutionHomeomorph n x ∈ boundedInnerOpenCylinder (r0 - δ) Γ α τ S
      rw [hxp]
      exact hp
    have hV := (isOpen_boundedInnerOpenCylinder (r0 - δ) hΓ.1 α τ S).preimage
      (evolutionHomeomorph n).continuous
    have hc := ((hlocal δ S hδ hδr).1.contDiffAt (hV.mem_nhds hx)).comp q
      (evolutionProdCLE n).symm.contDiff.contDiffAt
    have hfun : (innerBallDirichletLimit r0 Γ g u ∘ evolutionHomeomorph n) ∘
        (evolutionProdCLE n).symm = fun q =>
          innerBallDirichletLimit r0 Γ g u ⟨q.1, q.2.1, q.2.2⟩ := by
      funext q
      change innerBallDirichletLimit r0 Γ g u
        (evolutionHomeomorph n ((evolutionProdCLE n).symm q)) =
        innerBallDirichletLimit r0 Γ g u ⟨q.1, q.2.1, q.2.2⟩
      apply congrArg (innerBallDirichletLimit r0 Γ g u)
      apply (KineticPoint.equivProd n).injective
      change (evolutionProdCLE n) ((evolutionProdCLE n).symm q) = q
      exact (evolutionProdCLE n).apply_symm_apply q
    simpa only [hfun] using hc.contDiffWithinAt
  · intro p hp ha
    obtain ⟨δ, S, hδ, hδr, hpU⟩ := exists_boundedInnerOpenCylinder_mem hr0
      ⟨ha, hp.2.1⟩ hp.2.2
    exact (hlocal δ S hδ hδr).2 p hpU
  · intro p hp
    have hpc : p ∈ movingClosedSlab (PDE.euclideanBall 0 r0) Γ α τ :=
      ⟨by rw [hp.1]; exact hατ.le, hp.1.le, by simpa only [hp.1] using hp.2⟩
    exact htrace.2.1 p hpc hp.1
  · intro p _ hp
    exact htrace.2.2 p hp

end HypoellipticAleksandrov.KineticAleksandrov
