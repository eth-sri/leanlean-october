module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.Killing
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.BlockInterior
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierIntervalGeometry

/-! # The uniform unit-frequency block on arbitrary bounded intervals -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov
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
  have hl := (lt_min_iff.mp hd).1
  have hr := (lt_min_iff.mp hd).2
  simp only [PDE.vecOneCoordinate]
  simp only [Pi.sub_apply] at hh
  constructor <;> linarith only [hh.1, hh.2, hl, hr]

/-- The length-independent boundary branch of the unit block. -/
theorem interval_boundary_block
    {lam Lam m Lb : ℝ} (E : IntervalEvolution lam Lam m Lb)
    (σ : ℝ) (v : PDE.Vec 1)
    (hv : v ∈ movingDomain (E.domain) stationary σ)
    (hb : min (v 0 - E.left) (E.right - v 0) ≤ blockOuter Lb)
    (ξ : PDE.Vec 1) (hL : σ ≤ σ + blockTime m Lb)
    (ν : ComplexMeasure (PDE.Vec 1))
    (hν : IsFourierProjection E.kernel (movingQuery σ (σ + blockTime m Lb) hL v 0 hv) ξ ν) :
    TV ν ≤ intervalHeat lam (blockTime m Lb) (blockOuter Lb) := by
  have ht : 0 < blockTime m Lb := by
    unfold blockTime
    have h := blockL0_pos E.setting.2.2.1
    positivity
  have hp := (E.clauses).2.1
  have hkill := interval_killing E
    σ (σ + blockTime m Lb) (lt_add_of_pos_right σ ht) v hv
  have htv := interval_fourier_tv_le_mass E.measurableSet E.kernel E.coefficient hp σ (σ + blockTime m Lb) hL
    v 0 ξ hv ν hν
  have hnorm : σ + blockTime m Lb - σ = blockTime m Lb := by ring
  rw [hnorm] at hkill
  exact htv.trans (hkill.trans (intervalHeat_mono_distance E.setting.1.1 ht hb))

/-- Case-I unit blocks have constants depending only on the source bounds. -/
theorem unit_frequency_block_interval
    (lam Lam m Lb : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hm : 0 < m) (hmLb : m ≤ Lb) :
    ∃ L δ : ℝ, 0 < L ∧ 0 < δ ∧ δ < 1 ∧
      ∀ (E : IntervalEvolution lam Lam m Lb),
      ∀ (ξ : PDE.Vec 1), PDE.vecNormSq ξ = 1 →
      ∀ (σ : ℝ) (v : PDE.Vec 1)
      (hv : v ∈ movingDomain (E.domain) stationary σ)
      (hL : σ ≤ σ + L) (ν : ComplexMeasure (PDE.Vec 1)),
      IsFourierProjection E.kernel (movingQuery σ (σ + L) hL v 0 hv) ξ ν → TV ν ≤ 1 - δ := by
  obtain ⟨δ₁, hδ₁, hδ₁one, hi⟩ := interval_interior_block lam Lam m Lb
    hlam hlamLam hm hmLb
  have ht : 0 < blockTime m Lb := by
    unfold blockTime
    have h := blockL0_pos hm
    positivity
  have hR : 0 < blockOuter Lb := by
    unfold blockOuter
    have h := blockRho_pos (hm.trans_le hmLb)
    positivity
  let δ₂ := 1 - intervalHeat lam (blockTime m Lb) (blockOuter Lb)
  have hδ₂ : 0 < δ₂ := sub_pos.mpr (intervalErf_lt_one (by
    exact div_nonneg hR.le (by positivity)))
  let δ := min δ₁ (min δ₂ (1 / 2))
  refine ⟨blockTime m Lb, δ, ht, lt_min hδ₁ (lt_min hδ₂ (by norm_num)),
    (min_le_right _ _).trans_lt ((min_le_right _ _).trans_lt (by norm_num)), ?_⟩
  intro E ξ hξ σ v hv hL ν hν
  obtain ⟨hmono, hpar, _hcov⟩ := E.clauses
  by_cases hfit : PDE.euclideanBall v (blockOuter Lb) ⊆ E.domain
  · exact (hi E.left E.right E.coefficient E.drift E.setting E.measurableSet E.operator E.kernel E.realizes hmono hpar ξ hξ σ v hv hfit hL ν hν).trans
      (sub_le_sub_left (min_le_left _ _) 1)
  · have hb : min (v 0 - E.left) (E.right - v 0) ≤ blockOuter Lb := by
      by_contra hn
      exact hfit (interval_ball_subset_of_distance hR v (lt_of_not_ge hn))
    have hbound := interval_boundary_block E
      σ v hv hb ξ hL ν hν
    have hδle : δ ≤ δ₂ := (min_le_right _ _).trans (min_le_left _ _)
    dsimp only [δ₂] at hδle
    linarith

end HypoellipticAleksandrov.KineticAleksandrov.Interval
