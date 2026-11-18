module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitUniform
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCollarApproximation
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitGeometry
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitCover

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter
open scoped Topology MatrixOrder

/-- The actual pointwise exhaustion limit on the original diffused interior,
extended by zero outside that interior. -/
def innerBallDirichletLimit {n : ℕ} (r0 : ℝ) (Γ : ℝ → PDE.Vec n)
    (g : ℕ → ℝ → PDE.Vec n) (u : ℕ → TimeVelocity (n + n) → ℝ)
    (p : KineticPoint n) : ℝ := by
  classical
  exact if p.position ∈ movingDomain (PDE.euclideanBall 0 r0) Γ p.time then
    limUnder atTop (fun k => straightenedPullback (g k) (u k) p) else 0

/-- On the original diffused interior the zero extension is the actual limit. -/
theorem innerBallDirichletLimit_eq_limit {n : ℕ} (r0 : ℝ) (Γ : ℝ → PDE.Vec n)
    (g : ℕ → ℝ → PDE.Vec n) (u : ℕ → TimeVelocity (n + n) → ℝ)
    {p : KineticPoint n}
    (hp : p.position ∈ movingDomain (PDE.euclideanBall 0 r0) Γ p.time) :
    innerBallDirichletLimit r0 Γ g u p =
      limUnder atTop (fun k => straightenedPullback (g k) (u k) p) := by
  classical
  simp only [innerBallDirichletLimit, ite_eq_left hp]

/-- The zero extension inherits the collar estimate on the entire original closed slab. -/
theorem abs_le_collar_innerBallDirichletLimit
    {n : ℕ} {lam Lam Lb : ℝ} {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (hlam : 0 < lam) (hB : HasEverywhereLoewnerBounds lam Lam B)
    (hBs : IsSmoothFullKineticCoefficient B) (hbs : IsSmoothDrift b)
    (hb : HasEuclideanLipschitzDrift Lb b)
    {a α τ r0 d L C ε : ℝ} (haα : a < α) (hατ : α < τ)
    (hd : 0 < d) (hdr : d < r0 / 4)
    (hL : 0 ≤ L) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C)
    {Γ : ℝ → PDE.Vec n} (hΓ : Continuous Γ)
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
    ∀ p ∈ movingClosedSlab (PDE.euclideanBall 0 r0) Γ α τ,
      |innerBallDirichletLimit r0 Γ g u p| ≤ C *
        (barrierW (collarKappa L lam) (r0 - PDE.vecEuclideanNorm (p.position - Γ p.time)) /
          barrierW (collarKappa L lam) d)  := by
  have abs_le_collar_innerBall_dirichlet_limit {n : ℕ} {lam : ℝ} {Lam : ℝ} {Lb : ℝ} {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n} (hlam : 0 < lam) (hB : HasEverywhereLoewnerBounds lam Lam B) (hBs : IsSmoothFullKineticCoefficient B) (hbs : IsSmoothDrift b) (hb : HasEuclideanLipschitzDrift Lb b) {a α τ r0 δ0 S0 d L C ε : ℝ} (haα : a < α) (hατ : α < τ) (hδ0 : 0 < δ0) (hδr : δ0 < r0) (hd : 0 < d) (hdr : d < r0 / 4) (hL : 0 ≤ L) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C) {Γ : ℝ → PDE.Vec n} (hΓ : Continuous Γ) (F : BoundedBorel (EvolutionAmbientState n)) (hFC : ∀ q, |F q| ≤ C) (hsupp : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      4 * d ≤ r0 - PDE.vecEuclideanNorm (q.1 - Γ τ)) (β R : ℕ → ℝ) (hβpos : ∀ k, 0 < β k) (hβlim : Tendsto β atTop (𝓝 0)) (hRlim : Tendsto R atTop atTop) (g : ℕ → ℝ → PDE.Vec n) (hg : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (g k)) (hgL : ∀ k s t, PDE.vecEuclideanNorm (g k s - g k t) ≤ L * |s - t|) (hclose : ∀ k s, s ∈ Icc α τ → PDE.vecEuclideanNorm (g k s - Γ s) ≤ β k / 2) (u : ℕ → TimeVelocity (n + n) → ℝ) (hu : ∀ k, IsClassicalBackwardDirichletSolution a τ
      (openEllipsoid (straightenedEllipsoidMatrix n (r0 - β k) (R k)))
      (straightenedCoefficient B (g k) ε) (straightenedDrift b (g k))
      (fun _ _ => 0) (fun _ _ => 0)
      (fun x => F (g k τ + spatialY x, spatialZ x)) (fun _ => 0) (u k)) :
      ∀ p ∈ movingClosedSlab (PDE.euclideanBall 0 (r0 - δ0)) Γ α τ ∩
      {p | radialSq p ≤ S0 ^ 2},
      |limUnder atTop (fun k => straightenedPullback (g k) (u k) p)| ≤ C *
        (barrierW (collarKappa L lam) (r0 - PDE.vecEuclideanNorm (p.position - Γ p.time)) /
          barrierW (collarKappa L lam) d) := by
    intro p hp
    apply le_of_tendsto ((tendstoUniformlyOn_innerBall_dirichlet (S0 := S0) hlam hB hBs hbs hb haα hατ hδ0 hδr hd hdr hL hε hε1 hC hΓ F hFC hsupp β R hβpos hβlim hRlim g hg hgL hclose u hu).tendsto_at hp |>.abs)
    filter_upwards [(eventually_innerCylinder_mem_straightenedEllipsoid (S := S0) hδ0 hδr β R hβlim hRlim g hclose), hβlim.eventually (gt_mem_nhds hd)] with k hk hβk
    exact abs_le_original_collar_straightened_dirichlet
      hlam hB hBs hbs haα hατ hk.2.1 (hβpos k).le hβk.le hd hdr (hg k) hL
      (hgL k) (hclose k) hε hC F hFC hsupp (u k) (hu k) p
      ⟨⟨hp.1.1, hp.1.2.1⟩, subset_closure (hk.2.2 p hp)⟩
  have hr0 : 0 < r0 := by linarith
  intro p hp
  by_cases hi : p.position ∈ movingDomain (PDE.euclideanBall 0 r0) Γ p.time
  · obtain ⟨δ, S, hδ, hδr, hpK, -⟩ :=
      exists_innerClosedCylinder_mem_nhdsWithin hΓ hr0 hp hi
    rw [innerBallDirichletLimit_eq_limit r0 Γ g u hi]
    exact abs_le_collar_innerBall_dirichlet_limit
      hlam hB hBs hbs hb haα hατ hδ hδr hd hdr hL hε hε1 hC hΓ
      F hFC hsupp β R hβpos hβlim hRlim g hg hgL hclose u hu p hpK
  · have hn : PDE.vecEuclideanNorm (p.position - Γ p.time) = r0 :=
      le_antisymm (norm_le_of_mem_closure_movingBall hr0 hp.2.2)
        (not_lt.mp (fun hn => hi ((mem_movingBall_iff_norm_lt hr0).mpr hn)))
    simp [innerBallDirichletLimit, ite_eq_right hi, hn, barrierW, Real.exp_zero, le_refl]

/-- The actual exhaustion limit, extended by zero on the diffused boundary, is continuous
on the entire original closed slab, including its time faces. -/
theorem continuousOn_innerBallDirichletLimit
    {n : ℕ} {lam Lam Lb : ℝ} {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (hlam : 0 < lam) (hB : HasEverywhereLoewnerBounds lam Lam B)
    (hBs : IsSmoothFullKineticCoefficient B) (hbs : IsSmoothDrift b)
    (hb : HasEuclideanLipschitzDrift Lb b)
    {a α τ r0 d L C ε : ℝ} (haα : a < α) (hατ : α < τ)
    (hd : 0 < d) (hdr : d < r0 / 4)
    (hL : 0 ≤ L) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C)
    {Γ : ℝ → PDE.Vec n} (hΓ : Continuous Γ)
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
    ContinuousOn (innerBallDirichletLimit r0 Γ g u)
      (movingClosedSlab (PDE.euclideanBall 0 r0) Γ α τ) := by
  have hr0 : 0 < r0 := by linarith
  let K := movingClosedSlab (PDE.euclideanBall 0 r0) Γ α τ
  intro p hp
  by_cases hi : p.position ∈ movingDomain (PDE.euclideanBall 0 r0) Γ p.time
  · obtain ⟨δ, S, hδ, hδr, hpK, hKnhds⟩ :=
      exists_innerClosedCylinder_mem_nhdsWithin hΓ hr0 hp hi
    have heq : ∀ q ∈ movingClosedSlab (PDE.euclideanBall 0 (r0 - δ)) Γ α τ ∩
        {q | radialSq q ≤ S ^ 2}, innerBallDirichletLimit r0 Γ g u q =
        limUnder atTop (fun k => straightenedPullback (g k) (u k) q) :=
      fun q hq => innerBallDirichletLimit_eq_limit r0 Γ g u
        (innerClosedCylinder_subset_movingBall hδ hδr hq)
    exact (((continuousOn_bounded_innerBall_dirichlet_limit hlam hB hBs hbs hb haα hατ hδ hδr hd hdr hL hε hε1 hC hΓ F hFC hsupp β R hβpos hβlim hRlim g hg hgL hclose u hu).1 p hpK).congr heq (innerBallDirichletLimit_eq_limit r0 Γ g u hi)).mono_of_mem_nhdsWithin
      hKnhds
  · have hn : PDE.vecEuclideanNorm (p.position - Γ p.time) = r0 :=
      le_antisymm (norm_le_of_mem_closure_movingBall hr0 hp.2.2)
        (not_lt.mp (fun hn => hi ((mem_movingBall_iff_norm_lt hr0).mpr hn)))
    let G (q : KineticPoint n) := C *
      (barrierW (collarKappa L lam) (r0 - PDE.vecEuclideanNorm (q.position - Γ q.time)) /
        barrierW (collarKappa L lam) d)
    have hdist :=
      PDE.continuous_vecEuclideanNorm.comp
        (continuous_position.sub (hΓ.comp continuous_time))
    have hGc : Continuous G := by dsimp [G, barrierW]; fun_prop
    have hGp : G p = 0 := by
      simp [G, hn, barrierW, Real.exp_zero]
    have hGlim : Tendsto G (𝓝[K] p) (𝓝 0) :=
      hGp ▸ hGc.continuousWithinAt.tendsto
    have hKmem : ∀ᶠ q in 𝓝[K] p, q ∈ K := self_mem_nhdsWithin
    have hz :=
      squeeze_zero_norm' (hKmem.mono fun q hq =>
        (show ‖innerBallDirichletLimit r0 Γ g u q‖ ≤ G q from
          (by rw [Real.norm_eq_abs]; exact (abs_le_collar_innerBallDirichletLimit hlam hB hBs hbs hb haα hατ hd hdr hL hε hε1 hC hΓ F hFC hsupp β R hβpos hβlim hRlim g hg hgL hclose u hu) q hq))) hGlim
    simpa only [ContinuousWithinAt, innerBallDirichletLimit, ite_eq_right hi] using hz

end HypoellipticAleksandrov.KineticAleksandrov

