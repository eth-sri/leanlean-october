/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.RectangleDualCarrier
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial

/-- A finite dual potential with the wired exterior normalized to zero. -/
abbrev RectangleExteriorPotential (a : LatticeVertex) (w h : ℕ) :=
  {φ : RectangleDualVertex a w h → ℝ //
    ∀ z, z.1 ∈ rectangleDualBoundary a w h → φ z = 0}

def rectangleExtendedPotential (a : LatticeVertex) (w h : ℕ)
    (φ : RectangleExteriorPotential a w h) (z : LatticeVertex) : ℝ :=
  if hz : z ∈ rectangleDualExpanded a w h then φ.1 ⟨z, hz⟩ else 0

@[simp] theorem rectangleExtendedPotential_of_mem (a : LatticeVertex) (w h : ℕ)
    (φ : RectangleExteriorPotential a w h) (z : LatticeVertex)
    (hz : z ∈ rectangleDualExpanded a w h) :
    rectangleExtendedPotential a w h φ z = φ.1 ⟨z, hz⟩ := by
  simp [rectangleExtendedPotential, hz]

@[simp] theorem rectangleExtendedPotential_of_not_mem (a : LatticeVertex) (w h : ℕ)
    (φ : RectangleExteriorPotential a w h) (z : LatticeVertex)
    (hz : z ∉ rectangleDualExpanded a w h) :
    rectangleExtendedPotential a w h φ z = 0 := by
  simp [rectangleExtendedPotential, hz]

/-- Primal curl of a dual potential: above-minus-below horizontally and
left-minus-right vertically. -/
def rectangleCurlFlow (a : LatticeVertex) (w h : ℕ)
    (φ : RectangleExteriorPotential a w h) (b : LatticeBond) : ℝ :=
  match b.axis with
  | .horizontal => rectangleExtendedPotential a w h φ (b.faceBase true) -
      rectangleExtendedPotential a w h φ (b.faceBase false)
  | .vertical => rectangleExtendedPotential a w h φ (b.faceBase false) -
      rectangleExtendedPotential a w h φ (b.faceBase true)

/-- The four normalized bonds incident to a vertex, in right/left/up/down order. -/
def rectangleCurlIncidentCandidate (v : LatticeVertex) : Fin 4 → LatticeBond
  | 0 => ⟨v, .horizontal⟩
  | 1 => ⟨(v.1 - 1, v.2), .horizontal⟩
  | 2 => ⟨v, .vertical⟩
  | 3 => ⟨(v.1, v.2 - 1), .vertical⟩

def rectangleCurlCandidateInside (a : LatticeVertex) (w h : ℕ)
    (v : LatticeVertex) (i : Fin 4) : Prop :=
  (rectangleCurlIncidentCandidate v i).source ∈ latticeRectangle a w h ∧
    (rectangleCurlIncidentCandidate v i).target ∈ latticeRectangle a w h

private theorem rectangleCurlIncidentCandidate_injective (v : LatticeVertex) :
    Function.Injective (rectangleCurlIncidentCandidate v) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals solve
    | rfl
    | (simp [rectangleCurlIncidentCandidate, LatticeBond.mk.injEq] at hij)
    | (simp [rectangleCurlIncidentCandidate, LatticeBond.mk.injEq] at hij
       ; have hx := congrArg Prod.fst hij
       ; have hy := congrArg Prod.snd hij
       ; omega)

 theorem rectangleCurlIncidentBond_exists_unique (v : LatticeVertex)
    (b : LatticeBond) (h : b.source = v ∨ b.target = v) :
    ∃! i : Fin 4, rectangleCurlIncidentCandidate v i = b := by
  let v0 := v
  rcases b with ⟨⟨x,y⟩, ax⟩
  cases ax
  · change (x,y) = v ∨ (x+1,y) = v at h
    rcases h with hs | ht
    · subst v
      refine ⟨0, rfl, ?_⟩
      intro i hi
      have h₀ : rectangleCurlIncidentCandidate v0 0 = ⟨(x,y), .horizontal⟩ := rfl
      exact rectangleCurlIncidentCandidate_injective v0 (hi.trans h₀.symm)
    · subst v
      refine ⟨1, ?_, ?_⟩
      · simp [rectangleCurlIncidentCandidate]
      · intro i hi
        have h₁ : rectangleCurlIncidentCandidate v0 1 = ⟨(x,y), .horizontal⟩ := by
          simp [rectangleCurlIncidentCandidate, v0]
        exact rectangleCurlIncidentCandidate_injective v0 (hi.trans h₁.symm)
  · change (x,y) = v ∨ (x,y+1) = v at h
    rcases h with hs | ht
    · subst v
      refine ⟨2, rfl, ?_⟩
      intro i hi
      have h₂ : rectangleCurlIncidentCandidate v0 2 = ⟨(x,y), .vertical⟩ := rfl
      exact rectangleCurlIncidentCandidate_injective v0 (hi.trans h₂.symm)
    · subst v
      refine ⟨3, ?_, ?_⟩
      · simp [rectangleCurlIncidentCandidate]
      · intro i hi
        have h₃ : rectangleCurlIncidentCandidate v0 3 = ⟨(x,y), .vertical⟩ := by
          simp [rectangleCurlIncidentCandidate, v0]
        exact rectangleCurlIncidentCandidate_injective v0 (hi.trans h₃.symm)

private theorem rectangleCurlCandidate_faces_boundary
    (a : LatticeVertex) (w h : ℕ) (v : LatticeVertex) (i : Fin 4)
    (hv : v ∈ latticeRectangle a w h)
    (hout : ¬ rectangleCurlCandidateInside a w h v i) :
    LatticeBond.faceBase (rectangleCurlIncidentCandidate v i) false ∈ rectangleDualBoundary a w h ∧
      LatticeBond.faceBase (rectangleCurlIncidentCandidate v i) true ∈ rectangleDualBoundary a w h := by
  fin_cases i <;>
    simp [rectangleCurlCandidateInside, rectangleCurlIncidentCandidate,
      rectangleDualBoundary, rectangleDualInterior, rectangleDualExpanded,
      mem_latticeRectangle, LatticeBond.source, LatticeBond.target,
      LatticeBond.faceBase] at * <;> omega

theorem rectangleCurlCandidate_flow_zero_of_not_inside
    (a : LatticeVertex) (w h : ℕ) (φ : RectangleExteriorPotential a w h)
    (v : LatticeVertex) (i : Fin 4)
    (hv : v ∈ latticeRectangle a w h)
    (hout : ¬ rectangleCurlCandidateInside a w h v i) :
    rectangleCurlFlow a w h φ (rectangleCurlIncidentCandidate v i) = 0 := by
  obtain ⟨hfalse, htrue⟩ :=
    rectangleCurlCandidate_faces_boundary a w h v i hv hout
  have hexpFalse : LatticeBond.faceBase (rectangleCurlIncidentCandidate v i) false ∈
      rectangleDualExpanded a w h := (Finset.mem_filter.mp hfalse).1
  have hexpTrue : LatticeBond.faceBase (rectangleCurlIncidentCandidate v i) true ∈
      rectangleDualExpanded a w h := (Finset.mem_filter.mp htrue).1
  have hzeroFalse : rectangleExtendedPotential a w h φ
      (LatticeBond.faceBase (rectangleCurlIncidentCandidate v i) false) = 0 := by
    rw [rectangleExtendedPotential_of_mem _ _ _ _ _ hexpFalse]
    exact φ.2 _ hfalse
  have hzeroTrue : rectangleExtendedPotential a w h φ
      (LatticeBond.faceBase (rectangleCurlIncidentCandidate v i) true) = 0 := by
    rw [rectangleExtendedPotential_of_mem _ _ _ _ _ hexpTrue]
    exact φ.2 _ htrue
  cases hi : (rectangleCurlIncidentCandidate v i).axis <;>
    simp [rectangleCurlFlow, hi, hzeroFalse, hzeroTrue]

/-- The true finite set of normalized original bonds incident to `v`. -/
def rectangleActualIncidentBonds (a : LatticeVertex) (w h : ℕ)
    (v : LatticeVertex) :=
  {b : RectanglePrimalBond a w h // b.1.source = v ∨ b.1.target = v}

noncomputable def rectangleActualIncidentCandidateEquiv
    (a : LatticeVertex) (w h : ℕ) (v : LatticeVertex) :
    rectangleActualIncidentBonds a w h v ≃
      {i : Fin 4 // rectangleCurlCandidateInside a w h v i} where
  toFun b := by
    let i := Classical.choose
      (rectangleCurlIncidentBond_exists_unique v b.1.1 b.2)
    have hi := (Classical.choose_spec
      (rectangleCurlIncidentBond_exists_unique v b.1.1 b.2)).1
    refine ⟨i, ?_⟩
    change (rectangleCurlIncidentCandidate v i).source ∈ latticeRectangle a w h ∧
      (rectangleCurlIncidentCandidate v i).target ∈ latticeRectangle a w h
    rw [hi]
    exact b.1.2
  invFun i := by
    rcases i with ⟨ix, hix⟩
    refine ⟨⟨rectangleCurlIncidentCandidate v ix, hix.1, hix.2⟩, ?_⟩
    fin_cases ix <;> simp [rectangleCurlIncidentCandidate, LatticeBond.source,
      LatticeBond.target]
  left_inv b := by
    apply Subtype.ext
    apply Subtype.ext
    let i := Classical.choose
      (rectangleCurlIncidentBond_exists_unique v b.1.1 b.2)
    exact (Classical.choose_spec
      (rectangleCurlIncidentBond_exists_unique v b.1.1 b.2)).1
  right_inv i := by
    rcases i with ⟨ix, hix⟩
    apply Subtype.ext
    apply rectangleCurlIncidentCandidate_injective v
    let j := Classical.choose
      (rectangleCurlIncidentBond_exists_unique v
        (rectangleCurlIncidentCandidate v ix)
        (by fin_cases ix <;> simp [rectangleCurlIncidentCandidate,
          LatticeBond.source, LatticeBond.target]))
    have hj := (Classical.choose_spec
      (rectangleCurlIncidentBond_exists_unique v
        (rectangleCurlIncidentCandidate v ix)
        (by fin_cases ix <;> simp [rectangleCurlIncidentCandidate,
          LatticeBond.source, LatticeBond.target]))).1
    exact hj

noncomputable instance rectangleActualIncidentBondsFintype
    (a : LatticeVertex) (w h : ℕ) (v : LatticeVertex) :
    Fintype (rectangleActualIncidentBonds a w h v) := by
  classical
  letI : Fintype {i : Fin 4 // rectangleCurlCandidateInside a w h v i} := inferInstance
  exact Fintype.ofEquiv _ (Equiv.symm (rectangleActualIncidentCandidateEquiv a w h v))

noncomputable instance rectangleCurlCandidateFintype
    (a : LatticeVertex) (w h : ℕ) (v : LatticeVertex) :
    Fintype {i : Fin 4 // rectangleCurlCandidateInside a w h v i} :=
  by classical exact Fintype.ofFinite _

end PottsDiscontinuity.FK
