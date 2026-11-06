module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.Killing
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.BlockInterior
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierIntervalGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Decay.BlockInterior
import HypoellipticAleksandrov.KineticAleksandrov.Decay.CommonSelection
import HypoellipticAleksandrov.KineticAleksandrov.Decay.ContinuedPhase
import HypoellipticAleksandrov.KineticAleksandrov.Decay.ContinuedSelection
import HypoellipticAleksandrov.KineticAleksandrov.Decay.CorridorSelection
import HypoellipticAleksandrov.KineticAleksandrov.Decay.OppositePaths
import HypoellipticAleksandrov.KineticAleksandrov.Decay.UnitBlockEvolution
import HypoellipticAleksandrov.KineticAleksandrov.Decay.UnitBlockRetentionLift
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Interval.FourierKernelsEvolution
import Mathlib.Tactic.Linarith

/-! # The uniform unit-frequency block on arbitrary bounded intervals -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay
open HypoellipticAleksandrov.Parabolic

/- A ball fits whenever both endpoint distances exceed its radius. -/
theorem interval_ball_subset_of_distance {a c R } (hR : 0 < R) (v : PDE.Vec 1)
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

/- The length-independent boundary branch of the unit block. -/
end HypoellipticAleksandrov.KineticAleksandrov.Interval
