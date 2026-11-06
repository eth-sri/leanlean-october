/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarFiniteTriangularFaceIndependence
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceEdgeIncidence

@[expose] public noncomputable section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar
open scoped symmDiff

section
variable {n : ℕ}
def parafermionicCoverFacePositiveDartCount (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (u v : ParafermionicCoverBoxVertex n) : ℕ :=
  (S.filter fun i => (u.1, v.1) ∈ parafermionicCoverFiniteFaceDarts i.1).card

def parafermionicCoverFaceBoundaryCoefficient (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (u v : ParafermionicCoverBoxVertex n) : ℤ :=
  (parafermionicCoverFacePositiveDartCount S u v : ℤ) -
    (parafermionicCoverFacePositiveDartCount S v u : ℤ)
end

theorem coverFaceDarts_no_opposite {f : ParafermionicCoverVertex}
    {u v : ParafermionicCoverVertex}
    (huv : (u,v) ∈ parafermionicCoverFiniteFaceDarts f)
    (hvu : (v,u) ∈ parafermionicCoverFiniteFaceDarts f) : False := by
  simp only [parafermionicCoverFiniteFaceDarts, Finset.mem_insert,
    Finset.mem_singleton, parafermionicCoverFaceRightLift_formula,
    parafermionicCoverFaceRightUpLift_formula,
    parafermionicCoverFaceRightUpLeftLift_formula] at huv hvu
  grind

theorem coverFaceSetPositiveDartCount_le_one {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (u v : ParafermionicCoverBoxVertex n) :
    parafermionicCoverFacePositiveDartCount S u v ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hdi : (u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts i.1 :=
    by simp_all
  have hdj : (u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts j.1 :=
    by simp_all
  exact Subtype.ext (parafermionicCoverFiniteFaceDart_unique n i.2 j.2 hdi hdj)

theorem list_countP_xor_mod {α : Type*} (L : List α)
    (p q : α → Bool)
    (h : ∀ a, ¬ (p a = true ∧ q a = true)) :
    (L.countP (fun a => p a != q a)) % 2 =
      (L.countP p + L.countP q) % 2 := by
  induction L with
  | nil => simp
  | cons a L ih =>
      grind

section
variable {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) (u v : ParafermionicCoverBoxVertex n)
theorem coverFacePositiveDartCount_le_one  :
    parafermionicCoverFacePositiveDartCount S u v ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hdi : (u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts i.1 :=
    by simp_all
  have hdj : (u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts j.1 :=
    by simp_all
  exact Subtype.ext (parafermionicCoverFiniteFaceDart_unique n i.2 j.2 hdi hdj)

theorem parafermionicCoverFaceBoundaryCoefficient_antisymm  :
    parafermionicCoverFaceBoundaryCoefficient S u v =
      - parafermionicCoverFaceBoundaryCoefficient S v u := by
  simp [parafermionicCoverFaceBoundaryCoefficient]

theorem parafermionicCoverFaceBoundaryCoefficient_mem  :
    parafermionicCoverFaceBoundaryCoefficient S u v ∈ ({-1, 0, 1} : Set ℤ) := by
  grind [coverFacePositiveDartCount_le_one, parafermionicCoverFacePositiveDartCount, parafermionicCoverFaceBoundaryCoefficient]
end

section
variable {n : ℕ}
theorem coverFaceBoundaryEdge_countP_mod (L : List (ParafermionicCoverFiniteFaceTopIndex n))
    (u v : ParafermionicCoverBoxVertex n)
    [DecidablePred (fun i : ParafermionicCoverFiniteFaceTopIndex n =>
      s(u,v) ∈ (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet)]
    :
    (L.countP fun i => decide
      (s(u,v) ∈ (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet)) % 2 =
    ((L.countP fun i => decide
      ((u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts i.1)) +
      (L.countP fun i => decide
      ((v.1,u.1) ∈ parafermionicCoverFiniteFaceDarts i.1))) % 2 := by
  have horient (i : ParafermionicCoverFiniteFaceTopIndex n) :
      decide (s(u,v) ∈
        (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet) =
      (decide ((u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts i.1) !=
        decide ((v.1,u.1) ∈ parafermionicCoverFiniteFaceDarts i.1)) := by
    have hmem := parafermionicCoverFiniteFaceBoundaryEdge_iff_darts i.1 i.2 u v
    by_cases hp : (u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts i.1
    · have hn : ¬ (v.1,u.1) ∈ parafermionicCoverFiniteFaceDarts i.1 := by
        grind [coverFaceDarts_no_opposite]
      simp_all
    simp_all
  have hcount : L.countP (fun i => decide
      (s(u,v) ∈ (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet)) =
      L.countP (fun i => decide ((u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts i.1) !=
        decide ((v.1,u.1) ∈ parafermionicCoverFiniteFaceDarts i.1)) := by
    induction L with
    | nil => rfl
    | cons i L ih => simp only [List.countP_cons, horient i, ih]
  have hno : ∀ i : ParafermionicCoverFiniteFaceTopIndex n,
      ¬ (decide ((u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts i.1) = true ∧
      decide ((v.1,u.1) ∈ parafermionicCoverFiniteFaceDarts i.1) = true) := by
    intro (i : ParafermionicCoverFiniteFaceTopIndex n) ⟨hp, hq⟩
    exact coverFaceDarts_no_opposite (of_decide_eq_true hp) (of_decide_eq_true hq)
  have hxor := list_countP_xor_mod L
    (fun i => decide ((u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts i.1))
    (fun i => decide ((v.1,u.1) ∈ parafermionicCoverFiniteFaceDarts i.1)) hno
  rwa [hcount]

theorem parafermionicCoverFaceBoundaryCoefficient_ne_zero_iff (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (L : List (ParafermionicCoverFiniteFaceTopIndex n))
    (hL : L.Nodup) (hS : L.toFinset = S)
    (u v : ParafermionicCoverBoxVertex n) :
    parafermionicCoverFaceBoundaryCoefficient S u v ≠ 0 ↔
      s(u,v) ∈ (faceSymmDiffList
        (fun i => parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2) L).edgeSet := by
  classical
  let P : ParafermionicCoverFiniteFaceTopIndex n → Prop := fun i =>
    (u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts i.1
  let Q : ParafermionicCoverFiniteFaceTopIndex n → Prop := fun i =>
    (v.1,u.1) ∈ parafermionicCoverFiniteFaceDarts i.1
  have hcountP : L.countP P = parafermionicCoverFacePositiveDartCount S u v := by
    rw [← hS]
    exact (List.Nodup.card_eq_countP hL).symm
  have hcountQ : L.countP Q = parafermionicCoverFacePositiveDartCount S v u := by
    rw [← hS]
    exact (List.Nodup.card_eq_countP hL).symm
  have hedgepar := faceSymmDiffList_edge_iff_countP_mod
    (fun i => parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2) L (s(u,v))
  have hcoeff :
      parafermionicCoverFaceBoundaryCoefficient S u v ≠ 0 ↔
        (L.countP P + L.countP Q) % 2 = 1 := by
    have hp := coverFacePositiveDartCount_le_one S u v
    have hq := coverFacePositiveDartCount_le_one S v u
    unfold parafermionicCoverFaceBoundaryCoefficient
    omega
  rw [hcoeff, ← (coverFaceBoundaryEdge_countP_mod L u v)]
  exact hedgepar.symm
end

end PottsDiscontinuity.TorusTopology.Planar.Medial
