module

public import PottsDiscontinuity.Torus.DiamondDisplacement
public import PottsDiscontinuity.TorusRC.LiftedPaths

/-! Potentials on the finite torus telescope along the specified integer lifts.
These lemmas preserve lifted displacements instead of substituting finite torus
connectivity for a winding path. -/

public section

open PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus TorusRC CorrLength
variable {N M : ℕ}

theorem periodicCoordinate_ne_of_unit_difference (hM : 2 ≤ M)
    (hMp : 0 < M) (a b : ℤ) (hab : |a-b| = 1) :
    periodicCoordinate hMp a ≠ periodicCoordinate hMp b := by
  intro he
  have he' := congrArg (fun i : Fin M => (i.val : ℤ)) he
  rw [periodicCoordinate_val,periodicCoordinate_val] at he'
  have hd := Int.modEq_iff_dvd.1 he'
  have hunit : b-a = 1 ∨ b-a = -1 := by
    grind
  have hd1 : (M : ℤ) ∣ 1 := by
    aesop
  have hn : M ∣ 1 := by exact_mod_cast hd1
  simp_all

theorem faceEndpoint_false_y (hN : Even N) (hM : Even M) (e : Fin N × Fin M) :
    (faceEndpoint hN hM true e false).val.2 = e.2 := by
  grind [checker, faceEndpoint, faceEndpointRaw]

section
variable (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M) (A : RCConfig N M) (g : FaceVertex N M true → ℚ) (hg : ∀ e : OpenDiamondEdge A, diamondCoboundary hN hM A g e = -1) (a b : ℤ) {u v : RotatedVertex}
include hg
/-- A potential having vertical edge difference -1 acquires exactly the
integer vertical displacement along any lifted open edge. -/
theorem potential_vertical_difference_of_lifted_adj
    (huv : (liftedStripGraph hNp hMp A a b).Adj u v) :
    g (liftedFaceVertex hN hM hNp hMp v) -
      g (liftedFaceVertex hN hM hNp hMp u) = (v.val.2-u.val.2 : ℤ) := by
  have hyunit := huv.1.2
  have hy : u.val.2-v.val.2 = 1 ∨ u.val.2-v.val.2 = -1 := by
    grind
  let e : OpenDiamondEdge A := ⟨liftedEdgeIndex hNp hMp u v,huv.2.1⟩
  have hge := hg e
  rw [diamondCoboundary_apply] at hge
  have hne := periodicCoordinate_ne_of_unit_difference (by grind) hMp u.val.2 v.val.2 huv.1.2
  have hef := faceEndpoint_false_y hN hM e.val
  change (faceEndpoint hN hM true e.val false).val.2 =
    periodicCoordinate hMp (max u.val.2 v.val.2) at hef
  rcases Sym2.eq_iff.1 (liftedFaceEndpoints_eq hN hM hNp hMp u v huv.1) with h | h
  · have hypos : v.val.2 ≤ u.val.2 := by
      by_contra hn
      rw [max_eq_right_of_lt (by omega), ← h.1] at hef
      tauto
    have hdiff : v.val.2-u.val.2 = -1 := by omega
    rw [h.1,h.2,hdiff]
    grind
  · have hypos : u.val.2 ≤ v.val.2 := by
      by_contra hn
      rw [max_eq_left_of_lt (by omega), ← h.2] at hef
      tauto
    have hdiff : v.val.2-u.val.2 = 1 := by omega
    rw [h.1,h.2,hdiff]
    grind

/-- Telescope along the actual specified lift, retaining its endpoint heights. -/
theorem potential_vertical_difference_of_lifted_walk
    (p : (liftedStripGraph hNp hMp A a b).Walk u v) :
    g (liftedFaceVertex hN hM hNp hMp v) -
      g (liftedFaceVertex hN hM hNp hMp u) = (v.val.2-u.val.2 : ℤ) := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    have he := potential_vertical_difference_of_lifted_adj hN hM hNp hMp A g hg a b h
    grind
end

/-- A genuine lifted vertical period forces a conserved primal chain with
nonzero vertical displacement. No loop/cluster topology is assumed. -/
theorem exists_vertical_cycle_of_lifted_period
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) (a b x : ℤ) (hx : Even x)
    (hconn : (liftedStripGraph hNp hMp A a b).Reachable
      (liftedColumnSite x 0 hx ⟨0,rfl⟩)
      (liftedColumnSite x (M : ℤ) hx (by simp_all))) :
    ∃ f : diamondCycleSpace hN hM A, diamondVerticalDisplacement A f.val ≠ 0 := by
  by_contra hn
  push Not at hn
  obtain ⟨g,hg⟩ := exists_diamondPotential_of_cycle_annihilator hN hM A
    (fun _ => -1) (fun f => by
      simpa only [neg_one_mul,Finset.sum_neg_distrib,diamondVerticalDisplacement] using hn f)
  obtain ⟨p⟩ := hconn
  have he := potential_vertical_difference_of_lifted_walk hN hM hNp hMp A g (by grind) a b p
  rw [← liftedFaceVertex_vertical_period hN hM hNp hMp x hx,sub_self] at he
  have hm : (0 : ℚ) < M := by positivity
  dsimp [liftedColumnSite] at he
  push_cast at he
  linarith

end PottsDiscontinuity.TorusTopology
