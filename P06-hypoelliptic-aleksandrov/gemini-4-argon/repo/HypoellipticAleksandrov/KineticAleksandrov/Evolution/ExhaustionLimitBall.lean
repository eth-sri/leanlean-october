module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitFinite
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitSequence
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.PastGluing
import HypoellipticAleksandrov.KineticAleksandrov.BoundedBorel
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitCover

/-!
# Constructed classical evolution on moving balls centred at zero

Both analytic hypotheses are explicit. Compact terminal support supplies
the collar margin internally; actual finite Dirichlet sequences supply all the
finite-slab steps. The gluing lemma gives the whole past solution.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter Evolution
open scoped Topology MatrixOrder

section Data

variable (hLE : LiebermanEllipsoidDirichletStatement) (hH : HormanderHypoellipticityStatement)
variable {n : ℕ} (hn : 1 ≤ n) {lam Lam m Lb : ℝ}
variable (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hm : 0 < m) (hmLb : m ≤ Lb)
variable {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
variable (hBs : IsSmoothFullKineticCoefficient B) (hBsym : IsSymmetricFullKineticCoefficient B)
variable (hB : HasEverywhereLoewnerBounds lam Lam B) (hbs : IsSmoothDrift b)
variable (hb : HasEuclideanLipschitzDrift Lb b) (hbco : HasUnitDirectionDriftCoercivity m b)
variable {Γ : ℝ → PDE.Vec n} (hΓ : IsContinuousPiecewiseC1 Γ) {r0 : ℝ} (hr0 : 0 < r0)

include hLE hH hn hlam hlamLam hm hmLb hBs hBsym hB hbs hb hbco hΓ hr0

/- Actual finite-slab classical solutions on a moving ball exist with the original
terminal-data bound, relative only to explicit Lieberman and Hörmander inputs. -/
theorem exists_finite_viscous_innerBall_solution
    (a τ : ℝ) (haτ : a < τ) (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum (PDE.euclideanBall 0 r0) Γ τ F)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (C ) (hC : 0 ≤ C) (hFC : ∀ q, |F q| ≤ C) :
    ∃ v : KineticPoint n → ℝ,
      IsClassicalViscousFiniteSolution (PDE.euclideanBall 0 r0) Γ B b ε a τ F v ∧
        ∀ p ∈ movingClosedSlab (PDE.euclideanBall 0 r0) Γ a τ, |v p| ≤ C := by
  obtain ⟨d, hd, hdr, hsupp⟩ : ∃ d : ℝ, 0 < d ∧ d < r0 / 4 ∧ ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ), 4 * d ≤ r0 - PDE.vecEuclideanNorm (q.1 - Γ τ) := by
    have hFc := hF.2.1
    have hs : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ), q.1 ∈ movingDomain (PDE.euclideanBall 0 r0) Γ τ := (fun q hq => (hF.2.2 hq).1)
    by_cases hne : (tsupport (F : EvolutionAmbientState n → ℝ)).Nonempty
    · have hc : Continuous (fun q : EvolutionAmbientState n =>
          PDE.vecEuclideanNorm (q.1 - Γ τ)) :=
        PDE.continuous_vecEuclideanNorm.comp (continuous_fst.sub continuous_const)
      obtain ⟨q0, hq0, hmax⟩ := hFc.exists_isMaxOn hne hc.continuousOn
      let gap := r0 - PDE.vecEuclideanNorm (q0.1 - Γ τ)
      have hgap : 0 < gap := sub_pos.mpr ((mem_movingBall_iff_norm_lt hr0).mp (hs q0 hq0))
      let d := min (r0 / 8) (gap / 8)
      have hd : 0 < d := lt_min (by positivity) (by positivity)
      have hdr : d < r0 / 4 := (min_le_left _ _).trans_lt (by linarith)
      refine ⟨d, hd, hdr, fun q hq => ?_⟩
      have hqm : PDE.vecEuclideanNorm (q.1 - Γ τ) ≤
          PDE.vecEuclideanNorm (q0.1 - Γ τ) := hmax hq
      have hdm : d ≤ gap / 8 := min_le_right _ _
      dsimp only [gap] at hgap hdm
      linarith
    · refine ⟨r0 / 8, by positivity, by linarith, fun q hq => ?_⟩
      exact (hne ⟨q, hq⟩).elim
  obtain ⟨β, R, g, L, u, hL, hβ, hβlim, hR, hg, hgL, hclose, hu⟩ :=
    exists_innerBall_dirichlet_sequence hLE hlam hlamLam hBs hBsym hB hbs hΓ
      (show a - 1 < τ by linarith) hd hdr hε F hF.1 hF.2.1 hsupp
  have hRlim :=
    tendsto_atTop_mono (fun k => (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans
      (hR k)) tendsto_natCast_atTop_atTop
  have hc (k : ℕ) (s : ℝ) (hs : s ∈ Icc a τ) :
      PDE.vecEuclideanNorm (g k s - Γ s) ≤ β k / 2 :=
    hclose k s ⟨by linarith [hs.1], hs.2⟩
  have hv := isClassicalViscousFiniteSolution_innerBallDirichletLimit
    hH hn hlam hlamLam hm hmLb hB hBs hBsym hbs hb hbco
    (show a - 1 < a by linarith) haτ hd hdr hL hε hε1 hC hΓ F hFC hsupp
    β R (fun k => (hβ k).1) hβlim hRlim g hg hgL hc u hu
  refine ⟨innerBallDirichletLimit r0 Γ g u, hv, ?_⟩
  exact (innerBallDirichletLimit_bound_terminal_lateral
    hlam hB hBs hbs hb (show a - 1 < a by linarith) haτ hd hdr hL hε.le hε1 hC hΓ.1
    F hFC hsupp β R (fun k => (hβ k).1) hβlim hRlim g hg hgL hc u hu).1

/- The moving zero-centred ball branch of An actual bounded classical viscous
past solution exists and is unique, relative to the two analytic hypotheses. -/
theorem exists_viscous_terminalSolution_innerBall
    (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum (PDE.euclideanBall 0 r0) Γ τ F)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (C ) (hC : 0 ≤ C) (hFC : ∀ q, |F q| ≤ C) :
    ∃ v : KineticPoint n → ℝ,
      IsClassicalViscousTerminalSolution (PDE.euclideanBall 0 r0) Γ B b ε τ F v ∧
      (∀ p ∈ evolutionPastClosedCylinder (PDE.euclideanBall 0 r0) Γ τ, |v p| ≤ C) ∧
      (∀ w : KineticPoint n → ℝ,
        IsClassicalViscousTerminalSolution (PDE.euclideanBall 0 r0) Γ B b ε τ F w →
          EqOn w v (evolutionPastClosedCylinder (PDE.euclideanBall 0 r0) Γ τ)) := by
  apply exists_viscous_terminalSolution_of_finiteSlabs (PDE.isOpen_euclideanBall 0 r0)
    hΓ.1 hlam hB hb hε.le hε1 τ F C hC
  intro a haτ
  exact exists_finite_viscous_innerBall_solution hLE hH hn hlam hlamLam hm hmLb
    hBs hBsym hB hbs hb hbco hΓ hr0 a τ haτ F hF ε hε hε1 C hC hFC

end Data

end HypoellipticAleksandrov.KineticAleksandrov
