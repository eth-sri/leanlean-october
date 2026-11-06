module

public import HypoellipticAleksandrov.KineticAleksandrov.ClassicalInputs
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.InnerBallExhaustion
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionTerminalApproximation
public import PDEFoundation.Calculus.RegularityOrder


/-!
# Actual finite Dirichlet approximation sequences on a ball

The smooth inner-ball curves are chosen internally. The terminal support condition is
proved uniformly, and the Lieberman premise produces every actual
Dirichlet solution. No convergence or Cauchy estimate is a hypothesis.
-/

 public section



namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov.Parabolic Set Filter
open scoped Topology MatrixOrder

/-- A smooth inner-ball approximation sequence with actual finite Dirichlet solutions
exists relative only to the Lieberman premise. -/
theorem exists_innerBall_dirichlet_sequence
    (hLE : LiebermanEllipsoidDirichletStatement)
    {n : ℕ} {lam Lam : ℝ} {B : FullKineticCoefficient n} {b : PDE.VectorField n}
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hBs : IsSmoothFullKineticCoefficient B) (hBsym : IsSymmetricFullKineticCoefficient B)
    (hB : HasEverywhereLoewnerBounds lam Lam B) (hbs : IsSmoothDrift b)
    {Γ : ℝ → PDE.Vec n} (hΓ : IsContinuousPiecewiseC1 Γ)
    {a τ r0 d ε : ℝ} (haτ : a < τ) (hd : 0 < d) (hdr : d < r0 / 4) (hε : 0 < ε)
    (F : BoundedBorel (EvolutionAmbientState n))
    (hF : ContDiff ℝ PDE.smoothOrder (F : EvolutionAmbientState n → ℝ))
    (hFc : HasCompactSupport (F : EvolutionAmbientState n → ℝ))
    (hsupp : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      4 * d ≤ r0 - PDE.vecEuclideanNorm (q.1 - Γ τ)) :
    ∃ (β R : ℕ → ℝ) (g : ℕ → ℝ → PDE.Vec n) (L : ℝ)
      (u : ℕ → TimeVelocity (n + n) → ℝ),
      0 ≤ L ∧ (∀ k, 0 < β k ∧ β k ≤ d) ∧ Tendsto β atTop (𝓝 0) ∧
      (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) ∧ (∀ k, ContDiff ℝ PDE.smoothOrder (g k)) ∧
      (∀ k s t, PDE.vecEuclideanNorm (g k s - g k t) ≤ L * |s - t|) ∧
      (∀ k s, s ∈ Icc a τ → PDE.vecEuclideanNorm (g k s - Γ s) ≤ β k / 2) ∧
      ∀ k, IsClassicalBackwardDirichletSolution a τ
        (openEllipsoid (straightenedEllipsoidMatrix n (r0 - β k) (R k)))
        (straightenedCoefficient B (g k) ε) (straightenedDrift b (g k))
        (fun _ _ => 0) (fun _ _ => 0)
        (fun x => F (g k τ + spatialY x, spatialZ x)) (fun _ => 0) (u k) := by
  obtain ⟨β0, g0, L, hL, hβ0, -, hβlim, hg0, hc0, hgL0, -, -⟩ :=
    exists_nested_smooth_inner_balls hΓ a τ r0 haτ (by linarith)
  obtain ⟨j0, hj0⟩ := eventually_atTop.1 (hβlim.eventually (gt_mem_nhds hd))
  let β (k : ℕ) := β0 (k + j0)
  let g (k : ℕ) := g0 (k + j0)
  have hβ (k : ℕ) : 0 < β k ∧ β k ≤ d :=
    ⟨(hβ0 _).1, (hj0 _ (by omega)).le⟩
  obtain ⟨Z, -, hZ⟩ := exists_transported_terminal_support_bound hFc
  obtain ⟨R0, hR0, hsize⟩ := exists_transportedRadius_terminal_window
    (by linarith : 0 < r0) hd (by linarith : d < r0) Z
  let R (k : ℕ) := R0 + (k : ℝ) + 1
  have hRR0 (k : ℕ) : R0 ≤ R k := by
    dsimp only [R]

    linarith
  have hRp (k : ℕ)  := hR0.trans_le (hRR0 k)
  have hex (k : ℕ) : ∃ u : TimeVelocity (n + n) → ℝ,
      IsClassicalBackwardDirichletSolution a τ
        (openEllipsoid (straightenedEllipsoidMatrix n (r0 - β k) (R k)))
        (straightenedCoefficient B (g k) ε) (straightenedDrift b (g k))
        (fun _ _ => 0) (fun _ _ => 0)
        (fun x => F (g k τ + spatialY x, spatialZ x)) (fun _ => 0) u := by
    have hr : 0 < r0 - β k := by linarith [(hβ k).2]



    have hsz : (r0 - β k - d) ^ 2 / (r0 - β k) ^ 2 + Z ^ 2 / (R k) ^ 2 < 1 :=
      lt_of_le_of_lt
        (add_le_add (terminal_window_ratio_le_of_radius_le hr (by linarith [(hβ k).2]) hd.le
          (by linarith [(hβ k).1])) (le_refl _)) (hsize _ (hRR0 k))

    obtain ⟨hQ, hl, ho, hsy, hsm, hlo, hup, hbsm, hdatum, hcompact⟩ :=
      straightened_base_premises hBs hBsym hB hbs hlam hlamLam
        (r0 - β k) (R k) hr (hRp k) (g k) (hg0 _) ε hε τ hF hFc
    obtain ⟨u, hu, -⟩ := hLE hQ haτ (min lam ε) (max Lam ε) hl ho
      (straightenedCoefficient B (g k) ε) (straightenedDrift b (g k)) hsy hsm hlo hup hbsm
      (fun x => F (g k τ + spatialY x, spatialZ x)) hdatum hcompact (by
          intro x hx


          have hxF := tsupport_comp_subset_preimage _
            (terminalCoordinateHomeomorph (g k τ)).continuous hx
          let p : KineticPoint n := ⟨τ, g k τ + spatialY x, spatialZ x⟩
          have hm := mem_straightenedEllipsoid_of_terminal_support_window hr (hRp k) hd hL
            (hgL0 (k + j0)) (terminal_support_margin_of_innerBall_close (hβ k).2 hsupp (hc0 _ τ ⟨haτ.le, le_rfl⟩)) hZ hsz (p := p) le_rfl
            (by have : 0 ≤ d / (1 + L) := div_nonneg hd.le (by linarith); dsimp [p]; linarith)
            hxF
          simpa only [p, g, straightenedPoint, add_sub_cancel_left,
            spatialPack_spatialY_spatialZ]
            using hm)
    exact ⟨u, hu⟩
  choose u hu using hex
  refine ⟨β, R, g, L, u, hL, hβ, hβlim.comp (tendsto_add_atTop_nat j0), ?_,
    fun k => hg0 _, fun k => hgL0 _, fun k => hc0 _, hu⟩
  intro k
  dsimp only [R]
  linarith

end HypoellipticAleksandrov.KineticAleksandrov
