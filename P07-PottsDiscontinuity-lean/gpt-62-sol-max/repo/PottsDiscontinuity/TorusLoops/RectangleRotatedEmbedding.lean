module

public import PottsDiscontinuity.CorrLength.RotatedLattice
public import PottsDiscontinuity.TorusLoops.RectangleFK

/-!
# Embedding the cut diamond rectangle in a finite square FK box

The face coordinates of the cut rectangle are the coordinates of vertices in
the rotated lattice. The rotated-to-square coordinate map places all of them
inside a finite square box and sends each retained diamond edge to a square
lattice edge.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.Torus
open PottsDiscontinuity.FK
open PottsDiscontinuity.CorrLength
open PottsDiscontinuity.SixVertex

variable {N M : ℕ}

/-- A face centre, unwrapped from the torus, as a vertex of the rotated lattice. -/
def rectangleFaceToRotated (u : FaceVertex N M true) : RotatedVertex := by
  have he : Even (u.val.1.val + u.val.2.val) := by
    rw [Nat.even_iff]
    have hp := u.property
    exact of_decide_eq_true hp
  refine ⟨(u.val.1.val, u.val.2.val), ?_⟩
  grind

private theorem rectangleFaceToRotated_injective :
    Function.Injective (rectangleFaceToRotated (N := N) (M := M)) := by
  intro u v huv
  have hval := congrArg Subtype.val huv
  have hx : (u.val.1.val : ℤ) = (v.val.1.val : ℤ) := by
    simpa [rectangleFaceToRotated] using congrArg Prod.fst hval
  have hy : (u.val.2.val : ℤ) = (v.val.2.val : ℤ) := by
    simpa [rectangleFaceToRotated] using congrArg Prod.snd hval
  grind

/-- A finite box large enough to contain the square-coordinate image of every
face of the cut rectangle. -/
abbrev RectangleRotatedBoxRadius (N M : ℕ) := N + M + 2

/-- The face-vertex embedding into an origin-centred square box. -/
def rectangleFaceBoxEmbedding (_hN : Even N) (_hM : Even M) :
    FaceVertex N M true ↪ BoxVertex (0, 0) (RectangleRotatedBoxRadius N M) where
  toFun u := ⟨rotatedToSquareVertex (rectangleFaceToRotated u), by
    rw [mem_latticeBox]
    simp only [zero_sub, zero_add]
    dsimp [rotatedToSquareVertex, rectangleFaceToRotated]
    omega⟩
  inj' := by
    intro u v huv
    apply rectangleFaceToRotated_injective
    apply rotatedVertexEquiv.injective
    exact congrArg Subtype.val huv

section

variable
  (hN : Even N) (hM : Even M)
    (v : Fin N × Fin M)

private theorem rectangleEndpointXFalse :
    (faceEndpoint hN hM true v false).val.1.val =
      if checker v then v.1.val else (prv v.1).val := by
  cases hc : checker v <;> simp [faceEndpoint, faceEndpointRaw, hc]

private theorem rectangleEndpointXTrue :
    (faceEndpoint hN hM true v true).val.1.val =
      if checker v then (prv v.1).val else v.1.val := by
  cases hc : checker v <;> simp [faceEndpoint, faceEndpointRaw, hc]

private theorem rectangleEndpointYFalse :
    (faceEndpoint hN hM true v false).val.2.val = v.2.val := by
  cases hc : checker v <;> simp [faceEndpoint, faceEndpointRaw, hc]

end

section

variable (hN : Even N) (hM : Even M)

private theorem rectangleEndpointYTrue
    (v : Fin N × Fin M) :
    (faceEndpoint hN hM true v true).val.2.val = (prv v.2).val := by
  cases hc : checker v <;> simp [faceEndpoint, faceEndpointRaw, hc]

private theorem rectangleFaceEndpointToRotated_adj
    (e : RectangleEdgeIndex (N := N) (M := M)) :
    rotatedLattice.Adj
      (rectangleFaceToRotated (faceEndpoint hN hM true e.val false))
      (rectangleFaceToRotated (faceEndpoint hN hM true e.val true)) := by
  have hip := Nat.pos_of_ne_zero e.property.1
  have hjp := Nat.pos_of_ne_zero e.property.2
  have hi := prv_val_of_pos e.val.1 hip
  have hj := prv_val_of_pos e.val.2 hjp
  change |((faceEndpoint hN hM true e.val false).val.1.val : ℤ) -
      ((faceEndpoint hN hM true e.val true).val.1.val : ℤ)| = 1 ∧
    |((faceEndpoint hN hM true e.val false).val.2.val : ℤ) -
      ((faceEndpoint hN hM true e.val true).val.2.val : ℤ)| = 1
  rw [rectangleEndpointXFalse hN hM, rectangleEndpointXTrue hN hM,
    rectangleEndpointYFalse hN hM, rectangleEndpointYTrue hN hM]
  by_cases hc : checker e.val
  · simp_all
  simp_all

/-- The rectangle base graph maps into the indicated finite square box graph. -/
theorem rectangleBaseGraph_map_rectangleFaceBoxEmbedding :
    (rectangleBaseGraph hN hM).map (rectangleFaceBoxEmbedding hN hM) ≤
      boxGraph (0, 0) (RectangleRotatedBoxRadius N M) := by
  intro x y hxy
  rw [SimpleGraph.map_adj] at hxy
  rcases hxy with ⟨u, v, huv, rfl, rfl⟩
  rw [rectangleBaseGraph, SimpleGraph.fromEdgeSet_adj] at huv
  rcases huv with ⟨⟨e, he⟩, hne⟩
  have hadj := (rotatedLattice_adj_iff_square
    (rectangleFaceToRotated (faceEndpoint hN hM true e.val false))
    (rectangleFaceToRotated (faceEndpoint hN hM true e.val true))).mp
      (rectangleFaceEndpointToRotated_adj hN hM e)
  rcases Sym2.eq_iff.mp he with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · subst u
    subst v
    assumption
  · subst u
    subst v
    rw [boxGraph_adj_iff]
    exact hadj.symm

end

end PottsDiscontinuity.TorusLoops
