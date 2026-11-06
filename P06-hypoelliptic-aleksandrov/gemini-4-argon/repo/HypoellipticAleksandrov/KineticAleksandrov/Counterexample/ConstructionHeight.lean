module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionBoundary
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoff
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Order.Basic
import HypoellipticAleksandrov.Analysis.EuclideanNormCalculus
import HypoellipticAleksandrov.KineticAleksandrov.Operator
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # An interior height witness survives all sufficiently late spatial mollifiers -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Filter
open scoped Topology
open Set
open HypoellipticAleksandrov.Parabolic
open scoped BigOperators MatrixOrder

/- The same strictly interior point retains the required height for every late kernel. -/
theorem construction_smoothed_interior_height_eventually {d alpha}
    (h : CounterProfileStatement d alpha) (r mu R S : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hS : 0 < S)
    (hTS : barrierTime mu < S ^ 2)
    (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hsmall : flatteningOffset * Real.rpow r alpha ≤ 1 / 4)
    (hvel : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < R ^ 2) :
    ∃ P ∈ backwardCylinder (⟨barrierTime mu, 0, 0⟩ : KineticPoint d) S,
      ∀ᶠ n in atTop, (1 / 4 : ℝ) ≤
        smoothedZeroExtendedProfile h r mu R (standardMollifierSequence n) P := by
  obtain ⟨_, _, _, _, _, _, _, h0, _⟩ := selectedProfile_spec h
  obtain ⟨t, ht, hT, hh⟩ : ∃ t : ℝ, 0 < t ∧ t < barrierTime mu ∧
      5 / 16 < timeCutoffProfile (profileFunction h) alpha r mu R ⟨t, 0, 0⟩ := by
    let H := (profileFunction h)
    have hh := timeCutoff_height H alpha r mu R h0 hr hmu hsmall
    have hc := (continuous_timeCutoffProfile_time H alpha r mu R (0 : XV d)).continuousAt
      (x := barrierTime mu)
    have he :=
      hc.eventually (Ioi_mem_nhds (by linarith :
        5 / 16 < timeCutoffProfile H alpha r mu R ⟨barrierTime mu, 0, 0⟩))
    obtain ⟨a, b, ⟨hat, htb⟩, hab⟩ := he.exists_Ioo_subset
    let t := (max a 0 + barrierTime mu) / 2
    have hT : 0 < barrierTime mu := by
        exact (
      div_pos (Real.log_pos (by norm_num)) hmu

      /- The terminal exponential factor is exactly one eighth. -/
      )
    have hm := max_lt hat hT
    have ht0 : 0 < t := by dsimp [t]; have := le_max_right a 0; linarith
    have htT : t < barrierTime mu := by dsimp [t]; linarith
    refine ⟨t, ht0, htT, hab ?_⟩
    constructor
    · dsimp [t]; have := le_max_left a 0; linarith
    · exact htT.trans htb
  have hq : profileFunction h (0, 0) < 1 := by
    change profileFunction h 0 < 1
    rw [h0]
    norm_num
  have he := zeroExtendedProfile_eq_raw_on_profile (profileFunction h) alpha r mu R
    hr hmu hR hvel (⟨t, 0, 0⟩ : KineticPoint d) hq
  have hh' : 5 / 16 < zeroExtendedProfile (profileFunction h) alpha r mu R ⟨t, 0, 0⟩ := by
    rw [he]
    exact hh
  have hm := mollify_preserves_height_eventually
    (fun q : XV d => zeroExtendedProfile (profileFunction h) alpha r mu R ⟨t, q.1, q.2⟩)
    (continuous_zeroExtendedProfile_spatial_of_profile h r mu R hr hmu hR hscale hvel t)
    0 hh'
  refine ⟨⟨t, 0, 0⟩, construction_origin_mem_cylinder _ S t hS hTS ht hT, ?_⟩
  filter_upwards [hm] with n hn
  exact hn.le

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
