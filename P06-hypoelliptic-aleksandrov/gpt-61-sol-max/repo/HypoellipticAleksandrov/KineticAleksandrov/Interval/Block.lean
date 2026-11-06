module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.Killing
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.BlockInterior
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierIntervalGeometry

/-! # The uniform unit-frequency block on arbitrary bounded intervals -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open MeasureTheory
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay

/-- A ball fits whenever both endpoint distances exceed its radius. -/
theorem interval_ball_subset_of_distance {a c R : ℝ} (hR : 0 < R) (v : PDE.Vec 1)
    (hd : R < min (v 0 - a) (c - v 0)) :
    PDE.euclideanBall v R ⊆ PDE.oneDimensionalAxisBox a c := by
  intro w hw
  rw [PDE.mem_oneDimensionalAxisBox_iff]
  rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR,
    vecEuclideanNorm_vec_one] at hw
  have hh := abs_lt.mp hw


  simp only [PDE.vecOneCoordinate]
  simp only [Pi.sub_apply] at hh
  constructor <;> linarith only [hh.1, hh.2, ((lt_min_iff.mp hd).1), ((lt_min_iff.mp hd).2)]

/-- The length-independent boundary branch of the unit block. -/
theorem interval_boundary_block
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam m Lb a c : ℝ} (hac : a < c)
    (B : CoefficientField 1) (b : PDE.VectorField 1)
    (hs : SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b)
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (hr : RealizesTerminalEvolution _ stationary hJ
      (zIndependentCoefficient B) b S K)
    (σ : ℝ) (v : PDE.Vec 1)
    (hv : v ∈ movingDomain (PDE.oneDimensionalAxisBox a c) stationary σ)
    (hb : min (v 0 - a) (c - v 0) ≤ blockOuter Lb)
    (ξ : PDE.Vec 1) (hL : σ ≤ σ + blockTime m Lb)
    (ν : ComplexMeasure (PDE.Vec 1))
    (hν : IsFourierProjection K (movingQuery σ _ hL v 0 hv) ξ ν) :
    TV ν ≤ intervalHeat lam (blockTime m Lb) (blockOuter Lb) := by
  have ht : 0 < blockTime m Lb := by
    unfold blockTime
    have h := blockL0_pos hs.2.2.1
    positivity

  have hkill := interval_killing hH hLE hac B b hs hJ S K hr
    σ (σ + blockTime m Lb) (lt_add_of_pos_right σ ht) v hv
  have htv := interval_fourier_tv_le_mass hJ K B ((interval_evolution_clauses hH hLE hac B b hs hJ S K hr).2.1) σ (σ + blockTime m Lb) hL
    v 0 ξ hv ν hν
  have hnorm : σ + blockTime m Lb - σ = blockTime m Lb := by ring
  rw [hnorm] at hkill
  exact htv.trans (hkill.trans (intervalHeat_mono_distance hs.1.1 ht hb))

/-- Case-I unit blocks have constants depending only on the source bounds. -/
theorem unit_frequency_block_interval
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam m Lb : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hm : 0 < m) (hmLb : m ≤ Lb) :
    ∃ L δ : ℝ, 0 < L ∧ 0 < δ ∧ δ < 1 ∧
      ∀ (a c : ℝ) (_hac : a < c) (B : CoefficientField 1) (b : PDE.VectorField 1),
      SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b →
      ∀ (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
      (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
      (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary),
      RealizesTerminalEvolution _ stationary hJ
        (zIndependentCoefficient B) b S K →
      ∀ (ξ : PDE.Vec 1), PDE.vecNormSq ξ = 1 →
      ∀ (σ : ℝ) (v : PDE.Vec 1)
      (hv : v ∈ movingDomain (PDE.oneDimensionalAxisBox a c) stationary σ)
      (hL : σ ≤ σ + L) (ν : ComplexMeasure (PDE.Vec 1)),
      IsFourierProjection K (movingQuery σ (σ + L) hL v 0 hv) ξ ν → TV ν ≤ 1 - δ := by
  obtain ⟨δ₁, hδ₁, hδ₁one, hi⟩ := interval_interior_block hH hLE lam Lam m Lb
    hlam hlamLam hm hmLb

  have hR : 0 < blockOuter Lb := by
    unfold blockOuter
    have h := blockRho_pos (hm.trans_le hmLb)
    positivity
  let δ₂ := 1 - intervalHeat lam (blockTime m Lb) (blockOuter Lb)

  let δ := min δ₁ (min δ₂ (1 / 2))
  refine ⟨blockTime m Lb, δ, (by
      unfold blockTime
      have h := blockL0_pos hm
      positivity), lt_min hδ₁ (lt_min (sub_pos.mpr (intervalErf_lt_one (div_nonneg hR.le (by positivity)))) (by norm_num)),
    (min_le_right _ _).trans_lt ((min_le_right _ _).trans_lt (by norm_num)), ?_⟩
  intro a c hac B b hs hJ S K hr ξ hξ σ v hv hL ν hν
  obtain ⟨hmono, hpar, _hcov⟩ := interval_evolution_clauses hH hLE hac B b hs hJ S K hr
  by_cases hfit : PDE.euclideanBall v (blockOuter Lb) ⊆ PDE.oneDimensionalAxisBox a c
  · exact (hi a c B b hs hJ S K hr hmono hpar ξ hξ σ v hv hfit hL ν hν).trans
      (sub_le_sub_left (min_le_left _ _) 1)
  ·
    have hbound := interval_boundary_block hH hLE hac B b hs hJ S K hr
      σ v hv (by
          by_contra hn
          exact hfit (interval_ball_subset_of_distance hR v (lt_of_not_ge hn))) ξ hL ν hν
    have hδle : δ ≤ δ₂ := (min_le_right _ _).trans (min_le_left _ _)
    dsimp only [δ₂] at hδle
    linarith

end HypoellipticAleksandrov.KineticAleksandrov.Interval
