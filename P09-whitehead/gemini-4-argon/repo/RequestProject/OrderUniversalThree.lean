module

public import RequestProject.OrderPosetCoverThree
public import RequestProject.SimplyConnectedCoverEquiv

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

def UOrdTet (P : Type u) [PartialOrder P] (a : P) :=
  {vt : UV (orderCx P) a × OrdTet P // endV vt.1 = vt.2.1.1}

variable {a : P}

def uOrdTetFace0 (t : UOrdTet P a) : UF (orderCx P) a :=
  ⟨(extend (ordPos t.1.2.2.1) t.1.1,
    ⟨(t.1.2.1.2.1, t.1.2.1.2.2.1, t.1.2.1.2.2.2), t.1.2.2.2⟩),
    endV_extend (eb := ordPos t.1.2.2.1) t.2⟩

def uOrdTetFace1 (t : UOrdTet P a) : UF (orderCx P) a :=
  ⟨(t.1.1, ⟨(t.1.2.1.1, t.1.2.1.2.2.1, t.1.2.1.2.2.2),
    t.1.2.2.1.trans t.1.2.2.2.1, t.1.2.2.2.2⟩), t.2⟩

def uOrdTetFace2 (t : UOrdTet P a) : UF (orderCx P) a :=
  ⟨(t.1.1, ⟨(t.1.2.1.1, t.1.2.1.2.1, t.1.2.1.2.2.2),
    t.1.2.2.1, t.1.2.2.2.1.trans t.1.2.2.2.2⟩), t.2⟩

def uOrdTetFace3 (t : UOrdTet P a) : UF (orderCx P) a :=
  ⟨(t.1.1, ⟨(t.1.2.1.1, t.1.2.1.2.1, t.1.2.1.2.2.1),
    t.1.2.2.1, t.1.2.2.2.1⟩), t.2⟩

def uOrdTetBoundary (t : UOrdTet P a) : UF (orderCx P) a →₀ ℤ :=
  Finsupp.single (uOrdTetFace0 t) 1 - Finsupp.single (uOrdTetFace1 t) 1 +
    Finsupp.single (uOrdTetFace2 t) 1 - Finsupp.single (uOrdTetFace3 t) 1

def uOrdBoundary3 : (UOrdTet P a →₀ ℤ) →ₗ[ℤ] (UF (orderCx P) a →₀ ℤ) :=
  Finsupp.linearCombination ℤ uOrdTetBoundary

variable {f : P → Q} (hf : IsPosetCover f) (d₀ : P)

def coveredOrdTet (t : UOrdTet Q (f d₀)) : OrdTet P :=
  Classical.choose (hf.existsUnique_tetLift t.1.2
    (@coverV (orderCx P) (orderCx Q) (orderCxMap f hf.mono) (f d₀) d₀ (isCovering_orderCxMap hf) rfl t.1.1)
    ((@onV_coverV (orderCx P) (orderCx Q) (orderCxMap f hf.mono)
      (f d₀) d₀ (isCovering_orderCxMap hf) rfl t.1.1).trans t.2))

theorem coveredOrdTet_spec (t : UOrdTet Q (f d₀)) :
    (coveredOrdTet hf d₀ t).1.1 =
      @coverV (orderCx P) (orderCx Q) (orderCxMap f hf.mono)
        (f d₀) d₀ (isCovering_orderCxMap hf) rfl t.1.1 ∧
    ordTetMap f hf.mono (coveredOrdTet hf d₀ t) = t.1.2 :=
  (Classical.choose_spec (hf.existsUnique_tetLift t.1.2
    (@coverV (orderCx P) (orderCx Q) (orderCxMap f hf.mono) (f d₀) d₀ (isCovering_orderCxMap hf) rfl t.1.1)
    ((@onV_coverV (orderCx P) (orderCx Q) (orderCxMap f hf.mono)
      (f d₀) d₀ (isCovering_orderCxMap hf) rfl t.1.1).trans t.2))).1

include hf in
theorem exists_uOrdBoundary3_of_cover_exact (hconn : IsConnected (orderCx P))
    (hsc : SimplyConnected (orderCx P))
    (hfill : ∀ z : OrdTri P →₀ ℤ, bdry2 (orderCx P) z = 0 →
      ∃ y : OrdTet P →₀ ℤ, ordBoundary3 y = z)
    (z : UF (orderCx Q) (f d₀) →₀ ℤ)
    (hz : bdry2 (uCover (orderCx Q) (f d₀)) z = 0) :
    ∃ y : UOrdTet Q (f d₀) →₀ ℤ, uOrdBoundary3 y = z := by
  let p := coverHom (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl
  obtain ⟨w, hw⟩ := hfill (chain2 p z) (by rw [bdry2_chain2, hz, map_zero])
  have hsurj : Function.Surjective (coveredOrdTet hf d₀) := fun t => by
    obtain ⟨v, hv⟩ := coverV_surjective (d₀ := d₀) (isCovering_orderCxMap hf) hconn t.1.1
    let s : UOrdTet Q (f d₀) := ⟨(v, ordTetMap f hf.mono t), by
      rw [← onV_coverV (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl v, hv]; rfl⟩
    obtain ⟨_, -, huniq⟩ := hf.existsUnique_tetLift (ordTetMap f hf.mono t) t.1.1 rfl
    exact ⟨s, (huniq _ ⟨(coveredOrdTet_spec hf d₀ s).1.trans hv,
      (coveredOrdTet_spec hf d₀ s).2⟩).trans (huniq t ⟨rfl, rfl⟩).symm⟩
  obtain ⟨y, hy⟩ := Finsupp.mapDomain_surjective hsurj w
  refine ⟨y, Finsupp.mapDomain_injective (coverF_injective (d₀ := d₀) (isCovering_orderCxMap hf) hsc) ?_⟩
  change chain2 p (uOrdBoundary3 y) = chain2 p z
  rw [← hw, ← hy]
  clear hy
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add _ _ hc hd => simp only [map_add, Finsupp.mapDomain_add, hc, hd]
  | single t n =>
      let hcov := isCovering_orderCxMap hf
      have hspec := coveredOrdTet_spec hf d₀ t
      have hf0 : coverF hcov (d₀ := d₀) (x₀ := f d₀) rfl (uOrdTetFace0 t) =
          ⟨((coveredOrdTet hf d₀ t).1.2.1, (coveredOrdTet hf d₀ t).1.2.2.1, (coveredOrdTet hf d₀ t).1.2.2.2),
            (coveredOrdTet hf d₀ t).2.2⟩ :=
        coverF_eq_of_base_and_image hcov _ _
          (Subtype.ext (by dsimp [uOrdTetFace0, orderCxMap]; rw [← hspec.2]; rfl))
          (by exact (coverV_extend hcov (d₀ := d₀) (x₀ := f d₀) rfl (c := t.1.1) (eb := ordPos t.1.2.2.1) t.2
            (x := ordPos (coveredOrdTet hf d₀ t).2.1) (by exact hspec.1)
            (Prod.ext (Subtype.ext (by dsimp [ordPos, orderCxMap]; rw [← hspec.2]; rfl)) rfl)).symm)
      have hf1 : coverF hcov (d₀ := d₀) (x₀ := f d₀) rfl (uOrdTetFace1 t) =
          ⟨((coveredOrdTet hf d₀ t).1.1, (coveredOrdTet hf d₀ t).1.2.2.1, (coveredOrdTet hf d₀ t).1.2.2.2),
            (coveredOrdTet hf d₀ t).2.1.trans (coveredOrdTet hf d₀ t).2.2.1, (coveredOrdTet hf d₀ t).2.2.2⟩ :=
        coverF_eq_of_base_and_image hcov _ _
          (Subtype.ext (by dsimp [uOrdTetFace1, orderCxMap]; rw [← hspec.2]; rfl)) hspec.1
      have hf2 : coverF hcov (d₀ := d₀) (x₀ := f d₀) rfl (uOrdTetFace2 t) =
          ⟨((coveredOrdTet hf d₀ t).1.1, (coveredOrdTet hf d₀ t).1.2.1, (coveredOrdTet hf d₀ t).1.2.2.2),
            (coveredOrdTet hf d₀ t).2.1, (coveredOrdTet hf d₀ t).2.2.1.trans (coveredOrdTet hf d₀ t).2.2.2⟩ :=
        coverF_eq_of_base_and_image hcov _ _
          (Subtype.ext (by dsimp [uOrdTetFace2, orderCxMap]; rw [← hspec.2]; rfl)) hspec.1
      have hf3 : coverF hcov (d₀ := d₀) (x₀ := f d₀) rfl (uOrdTetFace3 t) =
          ⟨((coveredOrdTet hf d₀ t).1.1, (coveredOrdTet hf d₀ t).1.2.1, (coveredOrdTet hf d₀ t).1.2.2.1),
            (coveredOrdTet hf d₀ t).2.1, (coveredOrdTet hf d₀ t).2.2.1⟩ :=
        coverF_eq_of_base_and_image hcov _ _
          (Subtype.ext (by dsimp [uOrdTetFace3, orderCxMap]; rw [← hspec.2]; rfl)) hspec.1
      have hsub (x y : UF (orderCx Q) (f d₀) →₀ ℤ) :
          Finsupp.mapDomain (coverF hcov (d₀ := d₀) (x₀ := f d₀) rfl) (x - y) =
            Finsupp.mapDomain (coverF hcov (d₀ := d₀) (x₀ := f d₀) rfl) x -
              Finsupp.mapDomain (coverF hcov (d₀ := d₀) (x₀ := f d₀) rfl) y :=
        (Finsupp.lmapDomain ℤ ℤ (coverF hcov (d₀ := d₀) (x₀ := f d₀) rfl)).map_sub x y
      change Finsupp.mapDomain (coverF hcov (d₀ := d₀) (x₀ := f d₀) rfl)
        (uOrdBoundary3 (Finsupp.single t n)) = _
      simp only [uOrdBoundary3, Finsupp.linearCombination_single, Finsupp.mapDomain_smul,
        uOrdTetBoundary, hsub, Finsupp.mapDomain_add, Finsupp.mapDomain_single,
        hf0, hf1, hf2, hf3, ordBoundary3]
      rfl
