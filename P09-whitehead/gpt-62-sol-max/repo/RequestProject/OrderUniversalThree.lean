module

public import RequestProject.OrderPosetCoverThree
public import RequestProject.FinsuppBasis
public import RequestProject.SimplyConnectedCoverEquiv

@[expose] public section

/-! The actual lifted three-simplices of the path-class universal cover of an order nerve. -/

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

/-- A lifted three-simplex is a simplex and a path class at its first vertex. -/
def UOrdTet (P : Type u) [PartialOrder P] (a : P) :=
  {vt : UV (orderCx P) a × OrdTet P // endV vt.1 = vt.2.1.1}

variable {a : P}

/-- Only the first face moves the path class to the next vertex. -/
noncomputable def uOrdTetFace (t : UOrdTet P a) (i : Fin 4) : UF (orderCx P) a :=
  ⟨((if i = 0 then extend (ordPos t.1.2.2.1) t.1.1 else t.1.1), ordTetFace t.1.2 i), by
    fin_cases i
    · exact endV_extend (eb := ordPos t.1.2.2.1) t.2
    all_goals exact t.2⟩

noncomputable def uOrdTetBoundary (t : UOrdTet P a) : UF (orderCx P) a →₀ ℤ :=
  tetrahedronBoundary (uOrdTetFace t)

noncomputable def uOrdBoundary3 : (UOrdTet P a →₀ ℤ) →ₗ[ℤ] (UF (orderCx P) a →₀ ℤ) :=
  Finsupp.linearCombination ℤ uOrdTetBoundary

variable {f : P → Q} (hf : IsPosetCover f) (d₀ : P)

noncomputable def coveredTetLift (t : UOrdTet Q (f d₀)) :=
  liftOrdTet hf.mono hf.liftUp t.1.2
    (coverV (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl t.1.1)
    (by
      exact (onV_coverV (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl t.1.1).trans t.2)

/-- The tetrahedron upstairs that starts at the corresponding lifted vertex. -/
noncomputable def coveredOrdTet (t : UOrdTet Q (f d₀)) : OrdTet P :=
  (coveredTetLift hf d₀ t).1

theorem coveredOrdTet_spec (t : UOrdTet Q (f d₀)) :
    (coveredOrdTet hf d₀ t).1.1 = coverV (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl t.1.1 ∧
    ordTetMap f hf.mono (coveredOrdTet hf d₀ t) = t.1.2 :=
  (coveredTetLift hf d₀ t).2

theorem coveredOrdTet_surjective (hconn : IsConnected (orderCx P)) :
    Function.Surjective (coveredOrdTet hf d₀) := by
  intro t
  obtain ⟨v, hv⟩ := coverV_surjective (d₀ := d₀) (isCovering_orderCxMap hf) hconn t.1.1
  have he : endV v = f t.1.1 := by
    rw [← onV_coverV (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl v, hv]
    rfl
  let s : UOrdTet Q (f d₀) := ⟨(v, ordTetMap f hf.mono t), he⟩
  exact ⟨s, hf.tet_ext ((coveredOrdTet_spec hf d₀ s).1.trans hv)
    (coveredOrdTet_spec hf d₀ s).2⟩

theorem coverF_uOrdTetFace (t : UOrdTet Q (f d₀)) (i : Fin 4) :
    coverF (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl (uOrdTetFace t i) =
      ordTetFace (coveredOrdTet hf d₀ t) i := by
  apply coverF_eq_of_base_and_image (isCovering_orderCxMap hf)
  · change (orderCxMap f hf.mono).onF (ordTetFace (coveredOrdTet hf d₀ t) i) = ordTetFace t.1.2 i
    rw [ordTetMap_face, (coveredOrdTet_spec hf d₀ t).2]
  · fin_cases i
    · have hm := coverV_extend (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl
        (c := t.1.1) (eb := ordPos t.1.2.2.1) t.2
        (x := ordPos (coveredOrdTet hf d₀ t).2.1) (by
          change (coveredOrdTet hf d₀ t).1.1 = _
          exact (coveredOrdTet_spec hf d₀ t).1) (by
          rw [← (coveredOrdTet_spec hf d₀ t).2]; rfl)
      exact hm.symm
    all_goals exact (coveredOrdTet_spec hf d₀ t).1

/-- The canonical cover map carries the full lifted three-boundary to the actual
three-boundary upstairs. -/
theorem coverF_uOrdTetBoundary (t : UOrdTet Q (f d₀)) :
    Finsupp.mapDomain (coverF (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl)
      (uOrdTetBoundary t) = ordTetBoundary (coveredOrdTet hf d₀ t) := by
  rw [uOrdTetBoundary, ordTetBoundary, mapDomain_tetrahedronBoundary]
  exact congrArg tetrahedronBoundary (funext (coverF_uOrdTetFace hf d₀ t))

/-- The canonical covering comparison is a chain map also in degree three. -/
theorem coverHom_uOrdBoundary3 (c : UOrdTet Q (f d₀) →₀ ℤ) :
    chain2 (coverHom (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl)
      (uOrdBoundary3 c) =
    ordBoundary3 (Finsupp.mapDomain (coveredOrdTet hf d₀) c) := by
  finsupp_basis c
  intro t
  change Finsupp.mapDomain
    (coverF (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl)
    (uOrdBoundary3 (Finsupp.single t 1)) = _
  simp_all [uOrdBoundary3, Finsupp.linearCombination_single, coverF_uOrdTetBoundary hf d₀ t, ordBoundary3]

include hf in
/-- Actual full-nerve degree-two exactness transports to the path-class universal cover
 through the constructed covering comparison. -/
theorem exists_uOrdBoundary3_of_cover_exact (hconn : IsConnected (orderCx P))
    (hsc : SimplyConnected (orderCx P))
    (hfill : ∀ z : OrdTri P →₀ ℤ, bdry2 (orderCx P) z = 0 →
      ∃ y : OrdTet P →₀ ℤ, ordBoundary3 y = z)
    (z : UF (orderCx Q) (f d₀) →₀ ℤ)
    (hz : bdry2 (uCover (orderCx Q) (f d₀)) z = 0) :
    ∃ y : UOrdTet Q (f d₀) →₀ ℤ, uOrdBoundary3 y = z := by
  let p := coverHom (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl
  have hz' : bdry2 (orderCx P) (chain2 p z) = 0 := by
    exact chain2_cycle _ hz
  obtain ⟨w, hw⟩ := hfill (chain2 p z) hz'
  obtain ⟨y, hy⟩ := Finsupp.mapDomain_surjective (coveredOrdTet_surjective hf d₀ hconn) w
  refine ⟨y, ?_⟩
  apply Finsupp.mapDomain_injective
    (coverF_injective (d₀ := d₀) (isCovering_orderCxMap hf) hsc)
  change chain2 p (uOrdBoundary3 y) = chain2 p z
  rw [coverHom_uOrdBoundary3 hf d₀ y, hy, hw]

end FiniteChains.Comb
