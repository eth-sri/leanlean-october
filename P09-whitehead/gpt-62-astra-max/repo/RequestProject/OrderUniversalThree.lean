module

public import RequestProject.OrderPosetCoverThree
public import RequestProject.SimplyConnectedCoverEquiv

@[expose] public section

/-! The actual lifted three-simplices of the path-class universal cover of an order nerve. -/
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

/-- A lifted three-simplex is a simplex and a path class at its first vertex. -/
def UOrdTet (P : Type u) [PartialOrder P] (a : P) :=
  {vt : UV (orderCx P) a × OrdTet P // endV vt.1 = vt.2.1.1}

variable {a : P}

variable (t : UOrdTet P a)

/-- The lifted first face starts at the next vertex of the simplex. -/
def uOrdTetFace0 : UF (orderCx P) a :=
  ⟨(extend _ _,
    ⟨(t.1.2.1.2.1, t.1.2.1.2.2.1, t.1.2.1.2.2.2), t.1.2.2.2⟩),
    endV_extend (eb := ordPos t.1.2.2.1) t.2⟩

def uOrdTetFace1 : UF (orderCx P) a :=
  ⟨(t.1.1, ⟨(t.1.2.1.1, t.1.2.1.2.2.1, t.1.2.1.2.2.2),
    t.1.2.2.1.trans t.1.2.2.2.1, t.1.2.2.2.2⟩), t.2⟩

def uOrdTetFace2 : UF (orderCx P) a :=
  ⟨(t.1.1, ⟨(t.1.2.1.1, t.1.2.1.2.1, t.1.2.1.2.2.2),
    t.1.2.2.1, t.1.2.2.2.1.trans t.1.2.2.2.2⟩), t.2⟩

def uOrdTetFace3 : UF (orderCx P) a :=
  ⟨(t.1.1, ⟨(t.1.2.1.1, t.1.2.1.2.1, t.1.2.1.2.2.1),
    t.1.2.2.1, t.1.2.2.2.1⟩), t.2⟩

def uOrdTetBoundary : UF (orderCx P) a →₀ ℤ :=
  Finsupp.single (uOrdTetFace0 t) 1 - Finsupp.single (uOrdTetFace1 t) 1 +
    Finsupp.single (uOrdTetFace2 t) 1 - Finsupp.single (uOrdTetFace3 t) 1

def uOrdBoundary3 : (UOrdTet P a →₀ ℤ) →ₗ[ℤ] (UF (orderCx P) a →₀ ℤ) :=
  Finsupp.linearCombination ℤ uOrdTetBoundary

variable {f : P → Q} (hf : IsPosetCover f) (d₀ : P)

variable (t : UOrdTet Q (f d₀))

/-- The three-cell lift into a simply connected poset covering, extending the canonical
 path-class covering map on vertices and faces. -/
def coveredOrdTet :=
  Classical.choose (hf.existsUnique_tetLift t.1.2
    (@coverV (orderCx P) (orderCx Q) (orderCxMap f hf.mono)
      (f d₀) d₀ (isCovering_orderCxMap hf) rfl t.1.1)
    (by
      have h := @onV_coverV (orderCx P) (orderCx Q) (orderCxMap f hf.mono)
        (f d₀) d₀ (isCovering_orderCxMap hf) rfl t.1.1
      exact h.trans t.2))

theorem coveredOrdTet_spec :
    (coveredOrdTet hf d₀ t).1.1 =
      @coverV _ _ _
        (f d₀) d₀ (isCovering_orderCxMap hf) rfl t.1.1 ∧
    ordTetMap f hf.mono (coveredOrdTet hf d₀ t) = t.1.2 := by
  unfold coveredOrdTet <;> grind

theorem coveredOrdTet_surjective (hconn : IsConnected (orderCx P)) :
    Function.Surjective (coveredOrdTet hf d₀) := by
  intro t
  obtain ⟨v, hv⟩ := coverV_surjective (isCovering_orderCxMap hf) hconn _
  have he : endV v = f t.1.1 := by
    rw [← onV_coverV (isCovering_orderCxMap hf) rfl v, hv]
    rfl
  let s : UOrdTet Q _ := ⟨(v, ordTetMap f hf.mono t), he⟩
  refine ⟨s, ?_⟩
  obtain ⟨w, -, hw⟩ := hf.existsUnique_tetLift (ordTetMap f hf.mono t) _ rfl
  exact (hw _ ⟨(coveredOrdTet_spec hf d₀ s).1.trans hv,
      (coveredOrdTet_spec hf d₀ s).2⟩).trans (hw t ⟨rfl, rfl⟩).symm

variable (t : OrdTet P)

/-- The four actual two-faces of a weak three-simplex. -/
def ordTetFace0 : OrdTri P :=
  ⟨(t.1.2.1, t.1.2.2.1, t.1.2.2.2), t.2.2⟩
def ordTetFace1 : OrdTri P :=
  ⟨(t.1.1, t.1.2.2.1, t.1.2.2.2), t.2.1.trans t.2.2.1, t.2.2.2⟩
def ordTetFace2 : OrdTri P :=
  ⟨(t.1.1, t.1.2.1, t.1.2.2.2), t.2.1, t.2.2.1.trans t.2.2.2⟩
def ordTetFace3 : OrdTri P :=
  ⟨(t.1.1, t.1.2.1, t.1.2.2.1), t.2.1, t.2.2.1⟩

variable (t : UOrdTet Q (f d₀))

theorem coverF_uOrdTetFace1 :
    coverF (isCovering_orderCxMap hf) rfl (uOrdTetFace1 t) =
      ordTetFace1 (coveredOrdTet hf d₀ t) := by
  apply coverF_eq_of_base_and_image _
  · change (orderCxMap f hf.mono).onF _ =
      ordTetFace1 t.1.2
    rw [← (coveredOrdTet_spec hf d₀ t).2] <;> rfl
  · exact (coveredOrdTet_spec hf d₀ t).1

theorem coverF_uOrdTetFace2 :
    coverF (isCovering_orderCxMap hf) rfl (uOrdTetFace2 t) =
      ordTetFace2 (coveredOrdTet hf d₀ t) := by
  apply coverF_eq_of_base_and_image _
  · change (orderCxMap f hf.mono).onF _ =
      ordTetFace2 t.1.2
    rw [← (coveredOrdTet_spec hf d₀ t).2] <;> rfl
  · exact (coveredOrdTet_spec hf d₀ t).1

theorem coverF_uOrdTetFace3 :
    coverF (isCovering_orderCxMap hf) rfl (uOrdTetFace3 t) =
      ordTetFace3 (coveredOrdTet hf d₀ t) := by
  apply coverF_eq_of_base_and_image _
  · change (orderCxMap f hf.mono).onF _ =
      ordTetFace3 t.1.2
    rw [← (coveredOrdTet_spec hf d₀ t).2] <;> rfl
  · exact (coveredOrdTet_spec hf d₀ t).1

theorem coverF_uOrdTetFace0 :
    coverF (isCovering_orderCxMap hf) rfl (uOrdTetFace0 t) =
      ordTetFace0 (coveredOrdTet hf d₀ t) := by
  apply coverF_eq_of_base_and_image _
  · change (orderCxMap f hf.mono).onF _ =
      ordTetFace0 t.1.2
    rw [← (coveredOrdTet_spec hf d₀ t).2] <;> rfl
  · have hm := coverV_extend _ rfl (eb := ordPos t.1.2.2.1) t.2
      (x := ordPos (coveredOrdTet hf d₀ t).2.1)
      ((coveredOrdTet_spec hf d₀ t).1) (by
        rw [← (coveredOrdTet_spec hf d₀ t).2] <;> rfl)
    exact hm.symm

/-- The canonical cover map carries the full lifted three-boundary to the actual
 three-boundary upstairs, face by face. -/
theorem coverF_uOrdTetBoundary :
    Finsupp.mapDomain (coverF (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl)
      (uOrdTetBoundary t) = relTetBoundary (coveredOrdTet hf d₀ t) := by
  have hsub (x y : UF _ _ →₀ ℤ) :
      Finsupp.mapDomain _ (x - y) =
        Finsupp.mapDomain _ x -
          Finsupp.mapDomain _ y :=
    (Finsupp.lmapDomain ℤ ℤ (coverF (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl)).map_sub x y
  simp only [uOrdTetBoundary, hsub, Finsupp.mapDomain_add, Finsupp.mapDomain_single,
    coverF_uOrdTetFace0 hf d₀ t, coverF_uOrdTetFace1 hf d₀ t,
    coverF_uOrdTetFace2 hf d₀ t, coverF_uOrdTetFace3 hf d₀ t]
  rfl

/-- The canonical covering comparison is a chain map also in degree three. -/
theorem coverHom_uOrdBoundary3 (c : UOrdTet Q _ →₀ ℤ) :
    chain2 (coverHom (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl)
      (uOrdBoundary3 c) =
    ordBoundary3 (Finsupp.mapDomain (coveredOrdTet hf d₀) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [map_add, Finsupp.mapDomain_add, hc, hd]
  | single t n =>
    change Finsupp.mapDomain
      (coverF (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl)
      (uOrdBoundary3 _) = _
    simp_all [uOrdBoundary3, Finsupp.linearCombination_single, Finsupp.mapDomain_smul, coverF_uOrdTetBoundary, Finsupp.mapDomain_single, ordBoundary3]

include hf in
/-- Actual full-nerve degree-two exactness transports to the path-class universal cover
 through the constructed covering comparison. -/
theorem exists_uOrdBoundary3_of_cover_exact (hconn : IsConnected (orderCx P))
    (hsc : SimplyConnected (orderCx P))
    (hfill : ∀ z : OrdTri P →₀ ℤ, bdry2 (orderCx P) z = 0 →
      ∃ y : OrdTet P →₀ ℤ, ordBoundary3 y = z)
    (z : UF _ _ →₀ ℤ)
    (hz : bdry2 (uCover _ _) z = 0) :
    ∃ y : UOrdTet Q (f d₀) →₀ ℤ, uOrdBoundary3 y = z := by
  let p := coverHom (isCovering_orderCxMap hf) (x₀ := f d₀) rfl
  have hz' : bdry2 _ (chain2 p z) = 0 := by
    rw [bdry2_chain2, hz, map_zero]
  obtain ⟨w, hw⟩ := hfill _ hz'
  obtain ⟨y, hy⟩ := Finsupp.mapDomain_surjective (coveredOrdTet_surjective hf d₀ hconn) w
  refine ⟨y, ?_⟩
  apply Finsupp.mapDomain_injective
    (coverF_injective (isCovering_orderCxMap hf) hsc)
  change chain2 p _ = chain2 p z
  grind [coverHom_uOrdBoundary3]

end FiniteChains.Comb
