module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionTerminalGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.FiniteSlabBarriersTerminal
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCollarGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCauchyRadius
import Mathlib.Analysis.SpecificLimits.Basic
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CurveMollification
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CurveRegularityExhaustion
public import HypoellipticAleksandrov.KineticAleksandrov.ClassicalInputs

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter
open scoped Topology MatrixOrder


/-- Decreasing the diffused radius improves the relative collar-gap condition. -/
theorem terminal_window_ratio_le_of_radius_le {r r0 d : ℝ} (hr : 0 < r)
    (hdr : d < r) (hd : 0 ≤ d) (hrr0 : r ≤ r0) :
    (r - d) ^ 2 / r ^ 2 ≤ (r0 - d) ^ 2 / r0 ^ 2 := by
  have hr0 : 0 < r0 := hr.trans_le hrr0
  have hf := div_le_div_of_nonneg_left hd hr hrr0
  have hl : 0 ≤ 1 - d / r := sub_nonneg.mpr ((div_le_one hr).mpr hdr.le)
  have hm : 1 - d / r ≤ 1 - d / r0 := by linarith
  have hs := pow_le_pow_left₀ hl hm 2
  simpa only [← div_pow, sub_div, div_self hr.ne', div_self hr0.ne'] using hs



/-- A Euclidean ball is the moving ball of the constant curve with that centre. -/
theorem euclideanBall_eq_movingDomain_const {n : ℕ} (x : PDE.Vec n) {R : ℝ} (hR : 0 < R) :
    PDE.euclideanBall x R =
      movingDomain (PDE.euclideanBall (0 : PDE.Vec n) R) (fun _ : ℝ => x) 0 := by
  ext y
  rw [mem_movingDomain_euclideanBall_iff_norm_lt hR,
    PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR, add_zero]

/-- The geometric radii `α k = r / 2 · (1/4)ᵏ`. -/
noncomputable def innerBallRadius (r : ℝ) (k : ℕ) : ℝ := r / 2 * (1 / 4) ^ k

theorem innerBallRadius_pos {r : ℝ} (hr : 0 < r) (k : ℕ) : 0 < innerBallRadius r k := by
  unfold innerBallRadius; positivity

theorem innerBallRadius_lt {r : ℝ} (hr : 0 < r) (k : ℕ) : innerBallRadius r k < r := by
  unfold innerBallRadius
  have : (1 / 4 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  nlinarith

theorem innerBallRadius_succ (r : ℝ) (k : ℕ) :
    innerBallRadius r (k + 1) = innerBallRadius r k / 4 := by
  unfold innerBallRadius; rw [pow_succ]; ring

theorem tendsto_innerBallRadius (r : ℝ) : Tendsto (innerBallRadius r) atTop (𝓝 0) := by
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num)
    (by norm_num)).const_mul (r / 2)
  rw [mul_zero] at this
  exact this




/-- A smooth inner-ball approximation sequence with actual finite Dirichlet solutions
exists relative only to the Lieberman premise. -/
theorem exists_innerBall_dirichlet_sequence
    (hLE : LiebermanEllipsoidDirichletStatement)
    {n : ℕ} {lam Lam : ℝ} {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hBs : IsSmoothFullKineticCoefficient B) (hBsym : IsSymmetricFullKineticCoefficient B)
    (hB : HasEverywhereLoewnerBounds lam Lam B) (hbs : IsSmoothDrift b)
    {Γ : ℝ → PDE.Vec n} (hΓ : IsContinuousPiecewiseC1 Γ)
    {a τ r0 d ε : ℝ} (haτ : a < τ) (hd : 0 < d) (hdr : d < r0 / 4) (hε : 0 < ε)
    (F : BoundedBorel (EvolutionAmbientState n))
    (hF : ContDiff ℝ (⊤ : ℕ∞) (F : EvolutionAmbientState n → ℝ))
    (hFc : HasCompactSupport (F : EvolutionAmbientState n → ℝ))
    (hsupp : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      4 * d ≤ r0 - PDE.vecEuclideanNorm (q.1 - Γ τ)) :
    ∃ (β R : ℕ → ℝ) (g : ℕ → ℝ → PDE.Vec n) (L : ℝ)
      (u : ℕ → TimeVelocity (n + n) → ℝ),
      0 ≤ L ∧ (∀ k, 0 < β k ∧ β k ≤ d) ∧ Tendsto β atTop (𝓝 0) ∧
      (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) ∧ (∀ k, ContDiff ℝ (⊤ : ℕ∞) (g k)) ∧
      (∀ k s t, PDE.vecEuclideanNorm (g k s - g k t) ≤ L * |s - t|) ∧
      (∀ k s, s ∈ Icc a τ → PDE.vecEuclideanNorm (g k s - Γ s) ≤ β k / 2) ∧
      ∀ k, IsClassicalBackwardDirichletSolution a τ
        (openEllipsoid (straightenedEllipsoidMatrix n (r0 - β k) (R k)))
        (straightenedCoefficient B (g k) ε) (straightenedDrift b (g k))
        (fun _ _ => 0) (fun _ _ => 0)
        (fun x => F (g k τ + spatialY x, spatialZ x)) (fun _ => 0) (u k)  := by
  have exists_nested_smooth_inner_balls {γ : ℝ → PDE.Vec n} (hγ : IsContinuousPiecewiseC1 γ) (a τ r : ℝ) (haτ : a < τ) (hr : 0 < r) :
      ∃ (α : ℕ → ℝ) (g : ℕ → ℝ → PDE.Vec n) (L : ℝ),
      0 ≤ L ∧ (∀ k, 0 < α k ∧ α k < r) ∧
      (∀ k, α (k + 1) ≤ α k / 4) ∧ Tendsto α atTop (nhds 0) ∧
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (g k)) ∧
      (∀ k s, s ∈ Icc a τ →
        PDE.vecEuclideanNorm (g k s - γ s) ≤ α k / 2) ∧
      (∀ k s t, PDE.vecEuclideanNorm (g k s - g k t) ≤ L * |s - t|) ∧
      (∀ k s, s ∈ Icc a τ →
        PDE.euclideanBall (g k s) (r - α k) ⊆
          PDE.euclideanBall (g (k + 1) s) (r - α (k + 1))) ∧
      (∀ s ∈ Icc a τ,
        (⋃ k, PDE.euclideanBall (g k s) (r - α k)) =
          PDE.euclideanBall (γ s) r) := by
    obtain ⟨L, hL0, hL⟩ := exists_evolution_curve_lipschitzOn hγ a τ haτ
    have hext := slabExtension_lipschitz haτ.le hL0 hL
    have hcont := continuous_slabExtension hγ.1 a τ
    have hα := innerBallRadius_pos hr
    have hex : ∀ k, ∃ g : ℝ → PDE.Vec n, ContDiff ℝ (⊤ : ℕ∞) g ∧
        (∀ s t, PDE.vecEuclideanNorm (g s - g t) ≤ L * |s - t|) ∧
        ∀ s, PDE.vecEuclideanNorm (g s - slabExtension γ a τ s) ≤ innerBallRadius r k / 2 :=
      fun k => exists_smooth_lipschitz_approx hcont hL0 hext (half_pos (hα k))
    choose g hg hgL hgε using hex
    have hclose : ∀ k s, s ∈ Icc a τ →
        PDE.vecEuclideanNorm (g k s - γ s) ≤ innerBallRadius r k / 2 := by
      intro k s hs
      simpa [slabExtension_eq γ hs] using hgε k s
    refine ⟨innerBallRadius r, g, L, hL0, fun k => ⟨hα k, innerBallRadius_lt hr k⟩,
      fun k => (innerBallRadius_succ r k).le, tendsto_innerBallRadius r, hg, hclose, hgL,
      fun k s hs => ?_, fun s hs => ?_⟩
    · have hk : 0 < r - innerBallRadius r k := by linarith [innerBallRadius_lt hr k]
      have hk' : 0 < r - innerBallRadius r (k + 1) := by
        linarith [innerBallRadius_lt hr (k + 1)]
      rw [euclideanBall_eq_movingDomain_const _ hk, euclideanBall_eq_movingDomain_const _ hk']
      exact movingDomain_approx_mono (innerBallRadius_lt hr k) (hα (k + 1)).le
        (innerBallRadius_succ r k).le (γ := fun _ => γ s) (γ₁ := fun _ => g k s)
        (γ₂ := fun _ => g (k + 1) s) (fun _ => hclose k s hs) (fun _ => hclose (k + 1) s hs) 0
    · have hk : ∀ k, 0 < r - innerBallRadius r k := fun k => by
        linarith [innerBallRadius_lt hr k]
      have := iUnion_movingDomain_approx (c := (0 : PDE.Vec n)) (r₀ := r) (hα) (innerBallRadius_lt hr)
        (tendsto_innerBallRadius r) (γ := fun _ => γ s) (γs := fun k _ => g k s)
        (fun k _ => hclose k s hs) 0
      rw [euclideanBall_eq_movingDomain_const (γ s) hr]
      rw [← this]
      refine iUnion_congr fun k => ?_
      exact euclideanBall_eq_movingDomain_const _ (hk k)
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
    have hk := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hRp (k : ℕ) : 0 < R k := hR0.trans_le (hRR0 k)
  have hex (k : ℕ) : ∃ u : TimeVelocity (n + n) → ℝ,
      IsClassicalBackwardDirichletSolution a τ
        (openEllipsoid (straightenedEllipsoidMatrix n (r0 - β k) (R k)))
        (straightenedCoefficient B (g k) ε) (straightenedDrift b (g k))
        (fun _ _ => 0) (fun _ _ => 0)
        (fun x => F (g k τ + spatialY x, spatialZ x)) (fun _ => 0) u := by
    have hr : 0 < r0 - β k := by linarith [(hβ k).2]
    have hdr' : d < r0 - β k := by linarith [(hβ k).2]
    have hc : PDE.vecEuclideanNorm (g k τ - Γ τ) ≤ β k / 2 := hc0 _ τ ⟨haτ.le, le_rfl⟩
    have hs := terminal_support_margin_of_innerBall_close (hβ k).2 hsupp hc
    have hsz : (r0 - β k - d) ^ 2 / (r0 - β k) ^ 2 + Z ^ 2 / (R k) ^ 2 < 1 :=
      lt_of_le_of_lt
        (add_le_add (terminal_window_ratio_le_of_radius_le hr hdr' hd.le
          (by linarith [(hβ k).1])) (le_refl _)) (hsize _ (hRR0 k))
    have hsupport : tsupport (fun x : PDE.Vec (n + n) =>
        F (g k τ + spatialY x, spatialZ x)) ⊆
        openEllipsoid (straightenedEllipsoidMatrix n (r0 - β k) (R k)) := by
      intro x hx
      let H := terminalCoordinateHomeomorph (g k τ)
      have hx' : x ∈ tsupport ((F : EvolutionAmbientState n → ℝ) ∘ H) := hx
      have hxF := tsupport_comp_subset_preimage (F : EvolutionAmbientState n → ℝ)
        H.continuous hx'
      let p : KineticPoint n := ⟨τ, g k τ + spatialY x, spatialZ x⟩
      have hm := mem_straightenedEllipsoid_of_terminal_support_window hr (hRp k) hd hL
        (hgL0 (k + j0)) hs hZ hsz (p := p) le_rfl
        (by have : 0 ≤ d / (1 + L) := div_nonneg hd.le (by linarith); dsimp [p]; linarith)
        hxF
      simpa only [p, g, straightenedPoint, add_sub_cancel_left,
        spatialPack_spatialY_spatialZ]
        using hm
    obtain ⟨hQ, hl, ho, hsy, hsm, hlo, hup, hbsm, hdatum, hcompact⟩ :=
      straightened_base_premises hBs hBsym hB hbs hlam hlamLam
        (r0 - β k) (R k) hr (hRp k) (g k) (hg0 _) ε hε τ hF hFc
    obtain ⟨u, hu, -⟩ := hLE hQ haτ (min lam ε) (max Lam ε) hl ho
      (straightenedCoefficient B (g k) ε) (straightenedDrift b (g k)) hsy hsm hlo hup hbsm
      (fun x => F (g k τ + spatialY x, spatialZ x)) hdatum hcompact hsupport
    exact ⟨u, hu⟩
  choose u hu using hex
  refine ⟨β, R, g, L, u, hL, hβ, hβlim.comp (tendsto_add_atTop_nat j0), ?_,
    fun k => hg0 _, fun k => hgL0 _, fun k => hc0 _, hu⟩
  intro k
  dsimp only [R]
  linarith

end HypoellipticAleksandrov.KineticAleksandrov

