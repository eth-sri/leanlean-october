module

public import PottsDiscontinuity.SixVertex.InfinityMoves
public import PottsDiscontinuity.TorusRC.LiftedPaths

/-! Explicit integer lifts of indexed diamond endpoints and vertical deck
translations. These retain the actual open-edge indices, including small periods. -/

@[expose] public section

open PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus TorusRC CorrLength
variable {N M : ℕ}

section
variable (hN : 0 < N)

lemma periodicCoordinate_nat (i : Fin N) :
    periodicCoordinate hN i.val = i := by
  apply Fin.ext
  change (i.val % (N : ℤ)).toNat = i.val
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast i.isLt), Int.toNat_natCast]

lemma periodicCoordinate_sub_one (z : ℤ) :
    periodicCoordinate hN (z-1) = prv (periodicCoordinate hN z) := by
  apply Fin.ext
  apply Int.ofNat.inj
  simp_all [periodicCoordinate_val, finRotate_symm_apply, Fin.coe_int_sub_eq_mod]

lemma periodicCoordinate_add_period_mul (z k : ℤ) :
    periodicCoordinate hN (z + N*k) = periodicCoordinate hN z := by
  simp_all [periodicCoordinate, Int.add_emod]

end

variable (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M) (e : Fin N × Fin M)
    (hx : e.1.val ≠ 0) (b : Bool) (k : ℤ) (u : RotatedVertex)

include e b in
/-- Canonical integer endpoint coordinates of an indexed primal diamond edge. -/
def edgeLiftRaw : ℤ × ℤ :=
  if b then
    (if checker e then e.1.val-1 else e.1.val, e.2.val-1)
  else (if checker e then e.1.val else e.1.val-1, e.2.val)

lemma edgeLiftRaw_even :
    Even ((edgeLiftRaw e b).1 + (edgeLiftRaw e b).2) := by
  have hmod : (e.1.val + e.2.val) % 2 = 0 ∨ (e.1.val + e.2.val) % 2 = 1 := by omega
  rcases hmod with hc | hc
  · have hb : checker e = true := by simp [checker,hc]
    have he := Nat.even_iff.2 hc
    rcases (by exact_mod_cast he) with ⟨k,hk⟩
    cases b <;> simp only [edgeLiftRaw,hb,Bool.false_eq_true,ite_true,ite_false] <;> grind
  · have hb : checker e = false := by simp [checker,hc]
    cases b <;> simp only [edgeLiftRaw,hb,Bool.false_eq_true,ite_true,ite_false] <;>
      exact ⟨(e.1.val+e.2.val)/2,by omega⟩

include e b in
/-- A canonical lift of one endpoint, with no choice of path or representative. -/
def edgeLift : RotatedVertex :=
  ⟨edgeLiftRaw e b,edgeLiftRaw_even e b⟩

theorem edgeLift_adj :
    rotatedLattice.Adj (edgeLift e false) (edgeLift e true) := by
  cases hc : checker e <;> simp [rotatedLattice,edgeLift,edgeLiftRaw,hc]

theorem edgeLift_index :
    liftedEdgeIndex hNp hMp (edgeLift e false) (edgeLift e true) = e := by
  cases hc : checker e <;>
    simp [liftedEdgeIndex,edgeLift,edgeLiftRaw,hc,periodicCoordinate_nat]

theorem edgeLift_projects :
    liftedFaceVertex hN hM hNp hMp (edgeLift e b) = faceEndpoint hN hM true e b := by
  apply Subtype.ext
  cases b <;> cases hc : checker e <;>
    simp [liftedFaceVertex,edgeLift,edgeLiftRaw,faceEndpoint,faceEndpointRaw,hc,
      periodicCoordinate_sub_one,periodicCoordinate_nat]

include hM k u in
/-- Vertical deck translation by an integral number of full periods. -/
def verticalDeck : RotatedVertex :=
  ⟨(u.val.1,u.val.2+M*k), by
    simpa only [add_assoc] using u.property.add ((show Even (M : ℤ) by exact_mod_cast hM).mul_right k)⟩

lemma verticalDeck_projects :
    liftedFaceVertex hN hM hNp hMp (verticalDeck hM k u) =
      liftedFaceVertex hN hM hNp hMp u := by
  apply Subtype.ext
  exact Prod.ext rfl (periodicCoordinate_add_period_mul hMp u.val.2 k)

lemma verticalDeck_index (u v : RotatedVertex) :
    liftedEdgeIndex hNp hMp (verticalDeck hM k u) (verticalDeck hM k v) =
      liftedEdgeIndex hNp hMp u v := by
  apply Prod.ext
  · rfl
  · change periodicCoordinate hMp (max (u.val.2+M*k) (v.val.2+M*k)) = _
    rw [max_add_add_right,periodicCoordinate_add_period_mul]
    rfl

lemma verticalDeck_adj {u v : RotatedVertex}
    (huv : rotatedLattice.Adj u v) :
    rotatedLattice.Adj (verticalDeck hM k u) (verticalDeck hM k v) := by
  simpa [rotatedLattice,verticalDeck] using huv

lemma edgeLift_x {e : Fin N × Fin M} (hx : e.1.val ≠ 0) (b : Bool)
    (hN : Even N) (hM : Even M) :
    (edgeLift e b).val.1 = (faceEndpoint hN hM true e b).val.1.val := by
  have hp := prv_val_of_pos (Nat.pos_of_ne_zero hx)
  have hp' : (prv e.1).val = (e.1.val : ℤ)-1 := by omega
  cases b <;> cases hc : checker e <;>
    simp only [edgeLift,edgeLiftRaw,faceEndpoint,faceEndpointRaw,hc,Bool.false_eq_true,
      ite_true,ite_false] <;> exact hp'.symm

include hx in
/-- Every lift with the finite endpoint's canonical horizontal coordinate is a
unique vertical deck translate of the explicit indexed-edge endpoint. -/
theorem exists_deck_edgeLift_of_projection
    (hproj : liftedFaceVertex hN hM hNp hMp u = faceEndpoint hN hM true e b)
    (hux : u.val.1 = (faceEndpoint hN hM true e b).val.1.val) :
    ∃ k, verticalDeck hM k (edgeLift e b) = u := by
  have hy := congrArg (fun v : FaceVertex N M true => (v.val.2.val : ℤ))
    (hproj.trans (edgeLift_projects hN hM hNp hMp e b).symm)
  change (periodicCoordinate hMp u.val.2).val =
    ((periodicCoordinate hMp (edgeLift e b).val.2).val : ℤ) at hy
  rw [periodicCoordinate_val,periodicCoordinate_val] at hy
  obtain ⟨k,hk⟩ := Int.modEq_iff_dvd.1 hy.symm
  refine ⟨k,Subtype.ext (Prod.ext ?_ ?_)⟩
  · exact (edgeLift_x hx b hN hM).trans hux.symm
  · change (edgeLift e b).val.2+M*k = u.val.2
    omega

end PottsDiscontinuity.TorusTopology
