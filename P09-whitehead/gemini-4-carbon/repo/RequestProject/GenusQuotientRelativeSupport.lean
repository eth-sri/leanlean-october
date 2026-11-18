module

public import RequestProject.OrderNerveOneDecoding
public import RequestProject.CylinderPi1Surjective
public import RequestProject.GenusCollapseIteration
public import RequestProject.GenusLoops
public import RequestProject.CombPi1
public import RequestProject.PresPosetReading
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate
public import Mathlib.AlgebraicTopology.SimplicialSet.Dimension
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Order.WellFounded
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Analysis.Convex.GaugeRescale
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Logic.Equiv.PartialEquiv
public import Mathlib.Topology.CWComplex.Classical.Basic
public import RequestProject.Statement
public import Mathlib.Topology.CWComplex.Classical.Subcomplex

@[expose] public section
noncomputable section
section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

def ordStrictInclusion1 : (StrictOrdEdge P →₀ ℤ) →ₗ[ℤ]
    (OrdEdge P →₀ ℤ) := Finsupp.lmapDomain ℤ ℤ (strictOrderIncl P).onE

theorem ordNormalization_one_boundary (c : OrdEdge P →₀ ℤ) :
    bdry2 (orderCx P) (ordNormalizationHomotopy1 c) =
      c - ordStrictInclusion1 (normalizeOrdChain1 c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, map_add, map_add]; abel
  | single e n =>
    rcases e with ⟨⟨a, b⟩, hab⟩
    by_cases he : a = b
    · subst b
      simp [ordNormalizationHomotopy1, normalizeOrdChain1, normalizeOrdEdge,
        ordStrictInclusion1, bdry2, orderCx, pathChain]
    · simp [ordNormalizationHomotopy1, normalizeOrdChain1, normalizeOrdEdge,
        ordStrictInclusion1, strictOrderIncl, he]

theorem weak_oneCycle_filling_of_strict
    (hfill : ∀ c : StrictOrdEdge P →₀ ℤ, bdry1 (strictOrderCx P) c = 0 →
      ∃ y : StrictOrdTri P →₀ ℤ, bdry2 (strictOrderCx P) y = c)
    (c : OrdEdge P →₀ ℤ) (hc : bdry1 (orderCx P) c = 0) :
    ∃ y : OrdTri P →₀ ℤ, bdry2 (orderCx P) y = c := by
  have hn : bdry1 (strictOrderCx P) (normalizeOrdChain1 c) = 0 := by
    rw [bdry1_normalizeOrdChain1, hc]
  obtain ⟨y, hy⟩ := hfill _ hn
  have hy' : bdry2 (orderCx P) (ordStrictInclusion2 y) =
      ordStrictInclusion1 (normalizeOrdChain1 c) := by
    change bdry2 (orderCx P) (chain2 (strictOrderIncl P) y) = _
    rw [bdry2_chain2, hy]
    rfl
  refine ⟨ordStrictInclusion2 y + ordNormalizationHomotopy1 c, ?_⟩
  rw [map_add, hy', ordNormalization_one_boundary]
  abel

def strictOrdTetWeak (t : StrictOrdTet P) : OrdTet P :=
  ⟨t.1, t.2.1.le, t.2.2.1.le, t.2.2.2.le⟩

theorem ordBoundary3_strict_inclusion (y : StrictOrdTet P →₀ ℤ) :
    ordBoundary3 (Finsupp.mapDomain strictOrdTetWeak y) =
      ordStrictInclusion2 (strictOrdBoundary3 y) := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [Finsupp.mapDomain_add, map_add, hc, hd, map_add, map_add]
  | single t n =>
    rw [Finsupp.mapDomain_single, ordBoundary3, Finsupp.linearCombination_single,
      strictOrdBoundary3, Finsupp.linearCombination_single, map_smul]
    congr 1
    simp only [strictOrdTetBoundary, map_sub, map_add]
    simp [ordTetBoundary, strictOrdTetWeak, ordStrictInclusion2, strictOrderIncl]

theorem weak_twoCycle_filling_of_strict
    (hfill : ∀ c : StrictOrdTri P →₀ ℤ, bdry2 (strictOrderCx P) c = 0 →
      ∃ y : StrictOrdTet P →₀ ℤ, strictOrdBoundary3 y = c)
    (c : OrdTri P →₀ ℤ) (hc : bdry2 (orderCx P) c = 0) :
    ∃ y : OrdTet P →₀ ℤ, ordBoundary3 y = c := by
  obtain ⟨y, hy⟩ := hfill _ (normalizeOrdChain2_cycle c hc)
  refine ⟨Finsupp.mapDomain strictOrdTetWeak y + ordNormalizationHomotopy2 c, ?_⟩
  rw [map_add, ordBoundary3_strict_inclusion, hy, ← ordNormalization_cycle_boundary c hc]
  abel

theorem ordNerveChain3_mem_inc (c : OrdTet P →₀ ℤ) :
    ordNerveChain3 c ∈ Nerve.Inc P := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa using AddSubgroup.add_mem _ hc hd
  | single t n =>
    simp only [ordNerveChain3, Finsupp.linearCombination_single]
    apply AddSubgroup.zsmul_mem
    apply Nerve.of_mem_inc
    simpa [List.isChain_cons] using t.2

theorem nerve_oneCycle_filling_of_strict
    (hfill : ∀ c : StrictOrdEdge P →₀ ℤ, bdry1 (strictOrderCx P) c = 0 →
      ∃ y : StrictOrdTri P →₀ ℤ, bdry2 (strictOrderCx P) y = c)
    (c : Nerve.Ch P) (hi : c ∈ Nerve.Inc P)
    (hd : Nerve.lengthProjection 2 c = c) (hc : Nerve.bdry c = 0) :
    ∃ y ∈ Nerve.Inc P, Nerve.bdry y = c := by
  have he : ordNerveChain1 (decodeOrdNerve1 c) = c := by
    rw [ordNerveChain1_decode hi, hd]
  have hcyc  :=
    (ordNerveChain1_cycle_iff _).mp (by rw [he]; exact hc)
  obtain ⟨y, hy⟩ := weak_oneCycle_filling_of_strict hfill _ hcyc
  refine ⟨ordNerveChain2 y, ordNerveChain2_mem_inc y, ?_⟩
  rw [← ordNerveChain1_bdry2, hy, he]

theorem nerve_twoCycle_filling_of_strict
    (hfill : ∀ c : StrictOrdTri P →₀ ℤ, bdry2 (strictOrderCx P) c = 0 →
      ∃ y : StrictOrdTet P →₀ ℤ, strictOrdBoundary3 y = c)
    (c : Nerve.Ch P) (hi : c ∈ Nerve.Inc P)
    (hd : Nerve.lengthProjection 3 c = c) (hc : Nerve.bdry c = 0) :
    ∃ y ∈ Nerve.Inc P, Nerve.bdry y = c := by
  have he : ordNerveChain2 (decodeOrdNerve2 c) = c := by
    rw [ordNerveChain2_decode hi, hd]
  have hcyc  :=
    (ordNerveChain2_cycle_iff _).mp (by rw [he]; exact hc)
  obtain ⟨y, hy⟩ := weak_twoCycle_filling_of_strict hfill _ hcyc
  refine ⟨ordNerveChain3 y, ordNerveChain3_mem_inc y, ?_⟩
  rw [← ordNerveChain2_ordBoundary3, hy, he]

end FiniteChains.Comb
end

namespace FiniteChains.Comb
universe u
variable {X Y : Complex2.{u}}

theorem univLiftV_deckV (f : Hom X Y) (a : X.V) (g : Pi1 X a) (v : UV X a) :
    univLiftV a f (deckV g v) = deckV (pi1Map f a g) (univLiftV a f v) := by
  induction g using Quotient.ind with
  | _ p =>
    induction v using UV.ind with
    | h q =>
      change UV.mk (mapPathFrom a f (deckP p q)) =
        UV.mk (deckP ⟨mapPath f p.1, isPath_mapPath f p.2⟩ (mapPathFrom a f q))
      congr 1
      apply Subtype.ext
      exact mapPath_append f p.1 q.1

theorem deckV_free (a : X.V) (g : Pi1 X a) (v : UV X a)
    (h : deckV g v = v) : g = 1 := by
  obtain ⟨d, _, hu⟩ := (isRegular_univProj).simply_transitive v v rfl
  exact (hu g h).trans (hu 1 (deckV_one v)).symm

end FiniteChains.Comb

namespace FiniteChains.Comb
universe u
variable {D K : Complex2.{u}} {p : Hom D K} {d₀ : D.V}

theorem coverV_surjective (hcov : IsCovering p) (hconn : IsConnected D) :
    Function.Surjective (coverV hcov (d₀ := d₀) rfl) := by
  intro v
  obtain ⟨m, hm⟩ := hconn d₀ v
  refine ⟨UV.mk (pathFromMap p d₀ hm), ?_⟩
  exact coverV_eq hcov rfl ⟨m, hm, rfl⟩

/-- Simple connectivity removes precisely the ambiguity between lifts of path classes. -/

theorem coverF_injective (hcov : IsCovering p) (hsc : SimplyConnected D) :
    Function.Injective (coverF hcov (d₀ := d₀) rfl) := by
  intro c d he
  apply Subtype.ext
  apply Prod.ext
  · apply (show Function.Injective (coverV hcov rfl) by
    intro c d
    induction c using UV.ind with
    | h q =>
      induction d using UV.ind with
      | h r =>
        intro he
        obtain ⟨m, hm, hmq⟩ := coverV_spec hcov rfl q
        obtain ⟨n, hn, hnr⟩ := coverV_spec hcov rfl r
        rw [← he] at hn
        have htriv  := fun a l hl => mapPath_htpy p (hsc a l hl)
        have hh := htpy_mapPath_of_pi1Trivial htriv hm hn
        rw [hmq, hnr] at hh
        apply UV.sound
        have hend := onV_coverV hcov rfl (UV.mk q)
        rw [hend] at hh
        exact hh)
    rw [← base_coverF, ← base_coverF, he]
  · rw [← onF_coverF hcov rfl c, ← onF_coverF hcov rfl d, he]

/-- Identify a lifted face by its projected cell and its lifted base vertex. -/
theorem coverF_eq_of_base_and_image (hcov : IsCovering p) (c : UF K (p.onV d₀))
    (g : D.F) (himage : p.onF g = c.1.2)
    (hbase : D.base g = coverV hcov (d₀ := d₀) rfl c.1.1) :
    coverF hcov (d₀ := d₀) rfl c = g := by
  obtain ⟨w, -, hw⟩ := exists_unique_liftCell hcov c.1.2
    (coverF_cond hcov rfl c)
  exact (hw _ ⟨onF_coverF hcov rfl c, base_coverF hcov rfl c⟩).trans
    (hw g ⟨himage, hbase⟩).symm

end FiniteChains.Comb

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

/-- A lifted three-simplex is a simplex and a path class at its first vertex. -/
def UOrdTet (P : Type u) [PartialOrder P] (a : P) :=
  {vt : UV (orderCx P) a × OrdTet P // endV vt.1 = vt.2.1.1}

variable {a : P}

/-- The lifted first face starts at the next vertex of the simplex. -/
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

/-- The three-cell lift into a simply connected poset covering, extending the canonical
 path-class covering map on vertices and faces. -/
def coveredOrdTet (t : UOrdTet Q (f d₀)) : OrdTet P :=
  Classical.choose (hf.existsUnique_tetLift t.1.2
    (@coverV (orderCx P) (orderCx Q) (orderCxMap f hf.mono)
      (f d₀) d₀ (isCovering_orderCxMap hf) rfl t.1.1)
    (by
      have h := @onV_coverV (orderCx P) (orderCx Q) (orderCxMap f hf.mono)
        (f d₀) d₀ (isCovering_orderCxMap hf) rfl t.1.1
      exact h.trans t.2))

theorem coveredOrdTet_spec (t : UOrdTet Q (f d₀)) :
    (coveredOrdTet hf d₀ t).1.1 =
      @coverV (orderCx P) (orderCx Q) (orderCxMap f hf.mono)
        (f d₀) d₀ (isCovering_orderCxMap hf) rfl t.1.1 ∧
    ordTetMap f hf.mono (coveredOrdTet hf d₀ t) = t.1.2 := by
  unfold coveredOrdTet
  grind


/-- The four actual two-faces of a weak three-simplex. -/
def ordTetFace0 (t : OrdTet P) : OrdTri P :=
  ⟨(t.1.2.1, t.1.2.2.1, t.1.2.2.2), t.2.2⟩
def ordTetFace1 (t : OrdTet P) : OrdTri P :=
  ⟨(t.1.1, t.1.2.2.1, t.1.2.2.2), t.2.1.trans t.2.2.1, t.2.2.2⟩
def ordTetFace2 (t : OrdTet P) : OrdTri P :=
  ⟨(t.1.1, t.1.2.1, t.1.2.2.2), t.2.1, t.2.2.1.trans t.2.2.2⟩
def ordTetFace3 (t : OrdTet P) : OrdTri P :=
  ⟨(t.1.1, t.1.2.1, t.1.2.2.1), t.2.1, t.2.2.1⟩





/-- The canonical cover map carries the full lifted three-boundary to the actual
 three-boundary upstairs, face by face. -/
theorem coverF_uOrdTetBoundary (t : UOrdTet Q (f d₀)) :
    Finsupp.mapDomain (coverF (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl)
      (uOrdTetBoundary t) = ordTetBoundary (coveredOrdTet hf d₀ t) := by
  have hsub (x y) :
      Finsupp.mapDomain (coverF (isCovering_orderCxMap hf) rfl) (x - y) =
        Finsupp.mapDomain (coverF (isCovering_orderCxMap hf) (x₀ := f d₀) rfl) x -
          Finsupp.mapDomain (coverF (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl) y :=
    (Finsupp.lmapDomain ℤ ℤ (coverF (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl)).map_sub x y
  simp only [uOrdTetBoundary, hsub, Finsupp.mapDomain_add, Finsupp.mapDomain_single,
    (show coverF (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl (uOrdTetFace0 t) =
      ordTetFace0 (coveredOrdTet hf d₀ t) by
      apply coverF_eq_of_base_and_image (isCovering_orderCxMap hf)
      · change (orderCxMap f hf.mono).onF (ordTetFace0 (coveredOrdTet hf d₀ t)) =
          ordTetFace0 t.1.2
        rw [← (coveredOrdTet_spec hf d₀ t).2]
        rfl
      · have hm := coverV_extend (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl
          (c := t.1.1) (eb := ordPos t.1.2.2.1) t.2
          (x := ordPos (coveredOrdTet hf d₀ t).2.1)
          (by exact (coveredOrdTet_spec hf d₀ t).1) (by
            rw [← (coveredOrdTet_spec hf d₀ t).2]
            rfl)
        exact hm.symm), (show coverF (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl (uOrdTetFace1 t) =
      ordTetFace1 (coveredOrdTet hf d₀ t) by
          apply coverF_eq_of_base_and_image (isCovering_orderCxMap hf)
          · change (orderCxMap f hf.mono).onF (ordTetFace1 (coveredOrdTet hf d₀ t)) =
              ordTetFace1 t.1.2
            rw [← (coveredOrdTet_spec hf d₀ t).2]
            rfl
          · exact (coveredOrdTet_spec hf d₀ t).1),
    (show coverF (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl (uOrdTetFace2 t) =
      ordTetFace2 (coveredOrdTet hf d₀ t) by
      apply coverF_eq_of_base_and_image (isCovering_orderCxMap hf)
      · change (orderCxMap f hf.mono).onF (ordTetFace2 (coveredOrdTet hf d₀ t)) =
          ordTetFace2 t.1.2
        rw [← (coveredOrdTet_spec hf d₀ t).2]
        rfl
      · exact (coveredOrdTet_spec hf d₀ t).1), (show coverF (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl (uOrdTetFace3 t) =
      ordTetFace3 (coveredOrdTet hf d₀ t) by
      apply coverF_eq_of_base_and_image (isCovering_orderCxMap hf)
      · change (orderCxMap f hf.mono).onF (ordTetFace3 (coveredOrdTet hf d₀ t)) =
          ordTetFace3 t.1.2
        rw [← (coveredOrdTet_spec hf d₀ t).2]
        rfl
      · exact (coveredOrdTet_spec hf d₀ t).1)]
  rfl

/-- The canonical covering comparison is a chain map also in degree three. -/
theorem coverHom_uOrdBoundary3 (c : UOrdTet Q (f d₀) →₀ ℤ) :
    chain2 (coverHom (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl)
      (uOrdBoundary3 c) =
    ordBoundary3 (Finsupp.mapDomain (coveredOrdTet hf d₀) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.mapDomain_add, hc, hd]
  | single t n =>
    change Finsupp.mapDomain
      (coverF (isCovering_orderCxMap hf) rfl)
      (uOrdBoundary3 (Finsupp.single t n)) = _
    simp only [uOrdBoundary3, Finsupp.linearCombination_single, Finsupp.mapDomain_smul,
      coverF_uOrdTetBoundary hf d₀ t, Finsupp.mapDomain_single, ordBoundary3]

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
    rw [bdry2_chain2, hz, map_zero]
  obtain ⟨w, hw⟩ := hfill (chain2 p z) hz'
  obtain ⟨y, hy⟩ := Finsupp.mapDomain_surjective (by
    intro t
    obtain ⟨v, hv⟩ := coverV_surjective (isCovering_orderCxMap hf) hconn t.1.1
    have he : endV v = f t.1.1 := by
      rw [← onV_coverV (isCovering_orderCxMap hf) (x₀ := f d₀) rfl v, hv]
      rfl
    let s : UOrdTet Q (f d₀) := ⟨(v, ordTetMap f hf.mono t), he⟩
    refine ⟨s, ?_⟩
    obtain ⟨w, -, hw⟩ := hf.existsUnique_tetLift (ordTetMap f hf.mono t) t.1.1 rfl
    exact (hw _ ⟨(coveredOrdTet_spec hf d₀ s).1.trans hv,
        (coveredOrdTet_spec hf d₀ s).2⟩).trans (hw t ⟨rfl, rfl⟩).symm) w
  refine ⟨y, ?_⟩
  apply Finsupp.mapDomain_injective
    (coverF_injective (d₀ := d₀) (isCovering_orderCxMap hf) hsc)
  change chain2 p (uOrdBoundary3 y) = chain2 p z
  rw [coverHom_uOrdBoundary3 hf d₀ y, hy, hw]

end FiniteChains.Comb

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

def uOrderTet (t : OrdTet (UOrder P a)) : UOrdTet P a :=
  ⟨(t.1.1, ⟨(uOrderEnd t.1.1, uOrderEnd t.1.2.1,
    uOrderEnd t.1.2.2.1, uOrderEnd t.1.2.2.2),
    uOrderEnd_monotone t.2.1, uOrderEnd_monotone t.2.2.1,
    uOrderEnd_monotone t.2.2.2⟩), rfl⟩

/-- The four actual lifted faces have precisely the alternating nerve boundary. -/
theorem uOrderTet_boundary (t : OrdTet (UOrder P a)) :
    Finsupp.mapDomain uOrderFace (ordTetBoundary t) = uOrdTetBoundary (uOrderTet t) := by
  obtain ⟨⟨v, w, z, r⟩, hvw, hwz, hzr⟩ := t
  let t : OrdTet (UOrder P a) := ⟨(v, w, z, r), hvw, hwz, hzr⟩
  have h0 : uOrderFace ⟨(w, z, r), hwz, hzr⟩ = uOrdTetFace0 (uOrderTet t) := by
    apply Subtype.ext
    exact Prod.ext hvw.2.symm (Subtype.ext rfl)
  have h1 : uOrderFace ⟨(v, z, r), hvw.trans hwz, hzr⟩ =
      uOrdTetFace1 (uOrderTet t) := rfl
  have h2 : uOrderFace ⟨(v, w, r), hvw, hwz.trans hzr⟩ =
      uOrdTetFace2 (uOrderTet t) := rfl
  have h3 : uOrderFace ⟨(v, w, z), hvw, hwz⟩ = uOrdTetFace3 (uOrderTet t) := rfl
  have hsub (x y : OrdTri (UOrder P a) →₀ ℤ) :
      Finsupp.mapDomain uOrderFace (x - y) =
        Finsupp.mapDomain uOrderFace x - Finsupp.mapDomain uOrderFace y :=
    (Finsupp.lmapDomain ℤ ℤ uOrderFace).map_sub x y
  simp only [ordTetBoundary, hsub, Finsupp.mapDomain_add, Finsupp.mapDomain_single,
    uOrdTetBoundary]
  rw [h0, h1, h2, h3]

/-- The cellular comparison commutes with the full actual universal-cover three-boundary. -/
theorem uOrderHom_ordBoundary3 (c : OrdTet (UOrder P a) →₀ ℤ) :
    chain2 uOrderHom (ordBoundary3 c) = uOrdBoundary3 (Finsupp.mapDomain uOrderTet c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, Finsupp.mapDomain_add, map_add]
  | single t n =>
    rw [ordBoundary3, Finsupp.linearCombination_single, map_smul]
    change n • Finsupp.mapDomain uOrderFace (ordTetBoundary t) = _
    rw [uOrderTet_boundary, Finsupp.mapDomain_single, uOrdBoundary3,
      Finsupp.linearCombination_single]

end FiniteChains.Comb
end

namespace FiniteChains.Davis
open RACG Comb
universe u
variable {V X : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  [PartialOrder X] {att : NeSpx A →o X}

instance qposPartialOrder : PartialOrder (Qpos A X att) where
  toPreorder := qposPreorder
  le_antisymm s t hst hts := by
    cases s with
    | inl c =>
      cases t with
      | inl d => exact congrArg Sum.inl (Subtype.ext (le_antisymm hst hts))
      | inr y => exact hst.elim
    | inr x =>
      cases t with
      | inl d => exact hts.elim
      | inr y => exact congrArg Sum.inr (le_antisymm hst hts)

end FiniteChains.Davis

namespace FiniteChains.Nerve
universe u
variable {P : Type u} [Preorder P]

/-- All homogeneous increasing cycles of list length `n` supported on `U` bound. -/
def FillsDegreeIn (U : P → Prop) (n : ℕ) : Prop :=
  ∀ z ∈ IncOn U, lengthProjection n z = z → bdry z = 0 →
    ∃ y ∈ IncOn U, bdry y = z

/-- Homogeneous cycles of list length `n` are generated by cycles on `Base`,
modulo genuine full-nerve boundaries supported on `U`. -/
def GeneratesDegreeIn (U Base : P → Prop) (n : ℕ) : Prop :=
  ∀ z ∈ IncOn U, lengthProjection n z = z → bdry z = 0 →
    ∃ c ∈ IncOn Base, ∃ y ∈ IncOn U, bdry c = 0 ∧ z = c + bdry y

theorem generatesDegreeIn_of_acyclicRelIn {U Base : P → Prop} {n : ℕ}
    (h : AcyclicRelIn U Base) : GeneratesDegreeIn U Base n := by
  intro z hz _ hc
  exact h z hz hc

theorem generatesDegreeIn_of_fillsDegreeIn {U Base : P → Prop} {n : ℕ}
    (h : FillsDegreeIn U n) : GeneratesDegreeIn U Base n := by
  intro z hz hd hc
  obtain ⟨y, hy, hdy⟩ := h z hz hd hc
  exact ⟨0, AddSubgroup.zero_mem _, y, hy, by simp, by rw [hdy, zero_add]⟩

theorem generatesDegreeIn_union_of_unmixed {A B U Base : P → Prop} {n : ℕ}
    (hU : ∀ p, U p ↔ (A p ∨ B p))
    (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b))
    (hA : GeneratesDegreeIn A Base (n + 1))
    (hB : GeneratesDegreeIn B Base (n + 1))
    (hJ : FillsDegreeIn (fun p => A p ∧ B p) n) :
    GeneratesDegreeIn U Base (n + 1) := by
  intro z hz hdeg hcyc
  obtain ⟨a₀, ha₀, b₀, hb₀, hsplit⟩ := exists_split_of_unmixed hmix hz
  let a := lengthProjection (n + 1) a₀
  let b := lengthProjection (n + 1) b₀
  have ha : a ∈ IncOn A := lengthProjection_mem_incOn _ ha₀
  have hb : b ∈ IncOn B := lengthProjection_mem_incOn _ hb₀
  have had : lengthProjection (n + 1) a = a := lengthProjection_idempotent _ _
  have hbd : lengthProjection (n + 1) b = b := lengthProjection_idempotent _ _
  have hab : z = a + b := by
    rw [← hdeg, hsplit, map_add]
  have hda := bdry_mem_incOn ha
  have hdb := bdry_mem_incOn hb
  have hsum : bdry a + bdry b = 0 := by rw [← map_add, ← hab]; exact hcyc
  have hdaB : bdry a ∈ IncOn B := by
    have h : bdry a = -bdry b := by linear_combination (norm := abel) hsum
    rw [h]
    exact AddSubgroup.neg_mem _ hdb
  have htJ : bdry a ∈ IncOn (fun p => A p ∧ B p) := by
    rw [← incOn_inf]
    exact ⟨hda, hdaB⟩
  have hdad : lengthProjection n (bdry a) = bdry a := by
    rw [lengthProjection_bdry, had]
  obtain ⟨u₀, hu₀, hdu₀⟩ := hJ (bdry a) htJ hdad (by simp [bdry_bdry])
  let t := lengthProjection (n + 1) u₀
  have ht : t ∈ IncOn (fun p => A p ∧ B p) := lengthProjection_mem_incOn _ hu₀
  have htd : lengthProjection (n + 1) t = t := lengthProjection_idempotent _ _
  have hdt : bdry t = bdry a := by
    dsimp only [t]
    rw [← lengthProjection_bdry, hdu₀, hdad]
  have htA : t ∈ IncOn A := incOn_mono (fun _ h => h.1) ht
  have htB : t ∈ IncOn B := incOn_mono (fun _ h => h.2) ht
  obtain ⟨c₁, hc₁, y₁, hy₁, hdc₁, he₁⟩ := hA (a - t)
    (AddSubgroup.sub_mem _ ha htA) (by rw [map_sub, had, htd])
    (by rw [map_sub, hdt, sub_self])
  obtain ⟨c₂, hc₂, y₂, hy₂, hdc₂, he₂⟩ := hB (b + t)
    (AddSubgroup.add_mem _ hb htB) (by rw [map_add, hbd, htd]) (by
      rw [map_add, hdt]
      linear_combination (norm := abel) hsum)
  refine ⟨c₁ + c₂, AddSubgroup.add_mem _ hc₁ hc₂, y₁ + y₂,
    AddSubgroup.add_mem _ ?_ ?_, ?_, ?_⟩
  · exact incOn_mono (fun r hr => (hU r).2 (Or.inl hr)) hy₁
  · exact incOn_mono (fun r hr => (hU r).2 (Or.inr hr)) hy₂
  · simp_all
  · grind

end FiniteChains.Nerve

namespace FiniteChains.Nerve
universe u
variable {P Q : Type u}

theorem lengthProjection_cmap (f : P → Q) (n : ℕ) (c : Ch P) :
    lengthProjection n (cmap f c) = cmap f (lengthProjection n c) := by
  refine ext_apply
    (F := (lengthProjection n).comp (cmap f))
    (G := (cmap f).comp (lengthProjection n)) ?_ c
  intro l
  simp
  split_ifs <;> simp

variable [Preorder P]

theorem fillsDegreeIn_of_subtype {A : P → Prop} {n : ℕ} (hne : ∃ p, A p)
    (hfill : ∀ c ∈ Inc {p : P // A p}, lengthProjection n c = c → bdry c = 0 →
      ∃ y ∈ Inc {p : P // A p}, bdry y = c) : FillsDegreeIn A n := by
  intro c hc hd hcyc
  obtain ⟨c', hc', he⟩ := exists_preimage_of_mem_incOn A hc
  have hd' : lengthProjection n c' = c' := by
    apply cmap_val_injective A hne
    rw [← lengthProjection_cmap, he, hd]
  have hcyc' : bdry c' = 0 := by
    apply cmap_val_injective A hne
    rw [cmap_bdry, he, hcyc, map_zero]
  obtain ⟨y, hy, hdy⟩ := hfill c' hc' hd' hcyc'
  exact ⟨cmap Subtype.val y, cmap_val_mem_incOn A hy, by rw [← cmap_bdry, hdy, he]⟩

theorem fillsDegreeIn_congr {A B : P → Prop} {n : ℕ}
    (he : ∀ p, A p ↔ B p) (h : FillsDegreeIn A n) : FillsDegreeIn B n := by
  rw [show B = A from funext fun p => propext (he p).symm]
  exact h

theorem generatesDegreeIn_congr {A B Base : P → Prop} {n : ℕ}
    (he : ∀ p, A p ↔ B p) (h : GeneratesDegreeIn A Base n) :
    GeneratesDegreeIn B Base n := by
  rw [show B = A from funext fun p => propext (he p).symm]
  exact h

end FiniteChains.Nerve

namespace FiniteChains.Davis
open RACG Mirror Comb Nerve
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {M : CayGroup A → Prop} {att : NeSpx A →o X}

instance zposPartialOrder : PartialOrder (Zpos A X M att) where
  toPreorder := zposPreorder
  le_antisymm s t hst hts := by
    cases s with
    | inl p =>
      cases t with
      | inl q => exact congrArg Sum.inl (Subtype.ext (le_antisymm hst hts))
      | inr y => exact hst.elim
    | inr wx =>
      cases t with
      | inl p => exact hts.elim
      | inr vy => exact congrArg Sum.inr (Prod.ext hst.1 (le_antisymm hst.2 hts.2))

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror Comb Nerve
universe u
variable {V : Type u} [DecidableEq V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {M : CayGroup A → Prop} {att : NeSpx A →o X}
  {P : Type u} [PartialOrder P] {f : P → Zpos A X M att}

/-- The actual preimage of a marked chamber in a poset covering is acyclic relative
to the actual preimage of the inserted base. The retraction is constructed by unique
downward interval lifts of the geometric chamber retraction. -/
theorem acyclicRelIn_cover_marked_chamber [Nonempty X] (hf : IsPosetCover f)
    (w : CayGroup A) (hw : M w) :
    AcyclicRelIn (fun p => InZChamber w (f p)) (fun p => InZBase (f p)) := by
  let S : Set (Zpos A X M att) := {z | InZChamber w z}
  let fc := posetCoverRestriction f S
  have hfc  := IsPosetCover.restriction f S hf
  let g  := zChamberRetr (att := att) hw
  have hgle : ∀ q, g q ≤ q := zChamberRetr_le hw
  let ρ := hfc.downTransform g hgle
  have hmono := hfc.downTransform_monotone g (zChamberRetr_monotone hw) hgle
  have hρle : ∀ q, ρ q ≤ q := hfc.downTransform_le g hgle
  have hbase : ∀ q, InZBase (f (ρ q).1) := by
    intro q
    have he := congrArg Subtype.val (hfc.downTransform_spec g hgle q).2
    obtain ⟨x, hx⟩ := zChamberRetr_mem hw (fc q)
    have hb : InZBase (g (fc q)).1 := by
      change InZBase (zChamberRetr (att := att) hw (fc q)).1
      rw [hx]
      trivial
    change f (ρ q).1 = (g (fc q)).1 at he
    rw [he]
    exact hb
  have hne : ∃ p : P, InZChamber w (f p) := by
    let x : X := Classical.choice inferInstance
    obtain ⟨p, hp⟩ := hf.surj (zNew (att := att) ⟨w, hw⟩ x)
    refine ⟨p, ?_⟩
    rw [hp]
    rfl
  exact acyclicRelIn_of_retraction hne ρ hmono hρle hbase

end FiniteChains.Davis

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] {f : P → Q}

theorem strict_twoCycle_cover_lower_cone (hf : IsPosetCover f) (b : Q)
    (hb : ∀ q, b ≤ q) (c : StrictOrdTri P →₀ ℤ)
    (hc : bdry2 (strictOrderCx P) c = 0) :
    ∃ y : StrictOrdTet P →₀ ℤ, strictOrdBoundary3 y = c := by
  let g := hf.downTransform (fun _ => b) hb
  have hg  := hf.downTransform_monotone _ (fun _ _ _ => le_refl _) hb
  have hgle  := hf.downTransform_le _ hb
  have he : ∀ {v w : P}, v ≤ w → g v = g w := by
    intro v w hvw
    have hv := hf.downTransform_spec (fun _ => b) hb v
    have hw := hf.downTransform_spec (fun _ => b) hb w
    exact hf.down_inj (hv.1.trans hvw) hw.1 (hv.2.trans hw.2.symm)
  exact strict_cycle_boundary_of_downward_collapse g hg hgle he c hc

end FiniteChains.Comb

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {M : CayGroup A → Prop} {att : NeSpx A →o X}
  {P : Type u} [PartialOrder P] {f : P → Zpos A X M att}

/-- All strict two-cycles of the actual preimage of an ordinary chamber bound there,
even if that preimage has more than one connected component. -/
theorem strict_twoCycle_cover_unmarked_chamber (hf : IsPosetCover f)
    (w : CayGroup A) (hw : ¬ M w)
    (c : StrictOrdTri {p : P // InZChamber w (f p)} →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx {p : P // InZChamber w (f p)}) c = 0) :
    ∃ y : StrictOrdTet {p : P // InZChamber w (f p)} →₀ ℤ,
      strictOrdBoundary3 y = c := by
  let S : Set (Zpos A X M att) := {z | InZChamber w z}
  have hfc := IsPosetCover.restriction f S hf
  let b : S := ⟨zApex hw,
    inZChamber_zApex (att := att) hw⟩
  have hb : ∀ q : S, b ≤ q := fun q => zApex_le hw q.2
  exact strict_twoCycle_cover_lower_cone hfc b hb c hc

end FiniteChains.Davis

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

def normalizedStrictChain1 (g : P → P) (hg : Monotone g) :
    (StrictOrdEdge P →₀ ℤ) →ₗ[ℤ] (StrictOrdEdge P →₀ ℤ) :=
  normalizeOrdChain1.comp ((chain1 (orderCxMap g hg)).comp (chain1 (strictOrderIncl P)))

theorem normalizedStrictChain1_single (g : P → P) (hg : Monotone g)
    (e : StrictOrdEdge P) (n : ℤ) :
    normalizedStrictChain1 g hg (Finsupp.single e n) =
      n • normalizeOrdEdge ⟨(g e.1.1, g e.1.2), hg e.2.le⟩ := by
  change normalizeOrdChain1 (Finsupp.mapDomain (orderCxMap g hg).onE
    (Finsupp.mapDomain (strictOrderIncl P).onE (Finsupp.single e n))) = _
  rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single, normalizeOrdChain1_single]
  rfl

theorem normalizedStrictChain1_id (c : StrictOrdEdge P →₀ ℤ) :
    normalizedStrictChain1 id monotone_id c = c := by
  induction c using Finsupp.induction_linear with
  | zero => exact map_zero _
  | add c d hc hd => simp_all
  | single e n =>
    rw [normalizedStrictChain1_single]
    simp [normalizeOrdEdge, e.2.ne]

theorem normalizedStrictChain1_zero_of_comparable_equal
    (g : P → P) (hg : Monotone g) (he : ∀ {a b : P}, a ≤ b → g a = g b)
    (c : StrictOrdEdge P →₀ ℤ) : normalizedStrictChain1 g hg c = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => exact map_zero _
  | add c d hc hd => simp_all
  | single e n =>
    rw [normalizedStrictChain1_single]
    simp [normalizeOrdEdge, he e.2.le]

theorem strict_oneCycle_comparable_boundary (g h : P → P)
    (hg : Monotone g) (hh : Monotone h) (hgh : ∀ x, g x ≤ h x)
    (c : StrictOrdEdge P →₀ ℤ) (hc : bdry1 (strictOrderCx P) c = 0) :
    ∃ y : StrictOrdTri P →₀ ℤ,
      bdry2 (strictOrderCx P) y = normalizedStrictChain1 h hh c -
        normalizedStrictChain1 g hg c := by
  let w := chain1 (strictOrderIncl P) c
  have hw : bdry1 (orderCx P) w = 0 := by
    rw [bdry1_chain1, hc, map_zero]
  let p := Nerve.prism g h (ordNerveChain1 w)
  have hp  :=
    Nerve.prism_mem_inc hg hh hgh (ordNerveChain1_mem_inc w)
  have hd : Nerve.bdry (ordNerveChain1 w) = 0 := by
    rw [← ordNerveChain0_bdry1, hw, map_zero]
  have hb : Nerve.bdry p = Nerve.cmap h (ordNerveChain1 w) -
      Nerve.cmap g (ordNerveChain1 w) := by
    simpa [p, hd] using Nerve.bdry_prism_add_prism_bdry g h (ordNerveChain1 w)
  let b := Nerve.lengthProjection 3 p
  have hbi : b ∈ Nerve.Inc P := Nerve.lengthProjection_mem_inc _ hp
  have hdeg : Nerve.lengthProjection 3 b = b := Nerve.lengthProjection_idempotent _ _
  have hy : bdry2 (orderCx P) (decodeOrdNerve2 b) =
      chain1 (orderCxMap h hh) w - chain1 (orderCxMap g hg) w := by
    apply ordNerveChain1_injective
    rw [ordNerveChain1_bdry2, ordNerveChain2_decode hbi, hdeg, map_sub]
    dsimp only [b]
    rw [← Nerve.lengthProjection_bdry, hb, map_sub,
      ← ordNerveChain1_chain1 h hh, ← ordNerveChain1_chain1 g hg,
      ordNerveChain1_lengthProjection, ordNerveChain1_lengthProjection]
  refine ⟨normalizeOrdChain2 (decodeOrdNerve2 b), ?_⟩
  rw [bdry2_normalizeOrdChain2, hy, map_sub]
  rfl

theorem strict_oneCycle_boundary_of_roof_collapse (g h : P → P)
    (hg : Monotone g) (hh : Monotone h) (hgi : ∀ x, g x ≤ x)
    (hgh : ∀ x, g x ≤ h x) (he : ∀ {a b : P}, a ≤ b → h a = h b)
    (c : StrictOrdEdge P →₀ ℤ) (hc : bdry1 (strictOrderCx P) c = 0) :
    ∃ y : StrictOrdTri P →₀ ℤ, bdry2 (strictOrderCx P) y = c := by
  obtain ⟨y, hy⟩ := strict_oneCycle_comparable_boundary g id hg monotone_id hgi c hc
  obtain ⟨z, hz⟩ := strict_oneCycle_comparable_boundary g h hg hh hgh c hc
  refine ⟨y - z, ?_⟩
  rw [map_sub, hy, hz, normalizedStrictChain1_id,
    normalizedStrictChain1_zero_of_comparable_equal h hh he]
  abel

end FiniteChains.Comb
end

namespace FiniteChains.Comb.IsPosetCover
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] {f : P → Q}
variable (hf : IsPosetCover f) (g : Q → Q) (hg : ∀ q, g q ≤ q)
  (b : Q) (hb : ∀ q, g q ≤ b)

/-- Lift the upper leg from the canonical lower lift, rather than independently
choosing a lift of the endpoint. -/
def roofTransform (a : P) : P :=
  Classical.choose (hf.up (hf.downTransform g hg a) b
    ((hf.downTransform_spec g hg a).2 ▸ hb (f a)))

theorem roofTransform_spec (a : P) :
    hf.downTransform g hg a ≤ hf.roofTransform g hg b hb a ∧
      f (hf.roofTransform g hg b hb a) = b :=
  (Classical.choose_spec (hf.up (hf.downTransform g hg a) b
    ((hf.downTransform_spec g hg a).2 ▸ hb (f a)))).1

/-- Comparable vertices have exactly the same lifted endpoint. -/
theorem roofTransform_comparable_equal (hmono : Monotone g)
    {a a' : P} (haa' : a ≤ a') :
    hf.roofTransform g hg b hb a = hf.roofTransform g hg b hb a' := by
  have ha := hf.roofTransform_spec g hg b hb a
  have ha' := hf.roofTransform_spec g hg b hb a'
  exact hf.up_inj ha.1
    ((hf.downTransform_monotone g hmono hg haa').trans ha'.1)
    (ha.2.trans ha'.2.symm)

theorem roofTransform_monotone (hmono : Monotone g) :
    Monotone (hf.roofTransform g hg b hb) := by
  intro a a' haa'
  exact le_of_eq (hf.roofTransform_comparable_equal g hg b hb hmono haa')

end FiniteChains.Comb.IsPosetCover

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] {f : P → Q}

theorem strict_oneCycle_cover_roof (hf : IsPosetCover f) (g : Q → Q)
    (hmono : Monotone g) (hg : ∀ q, g q ≤ q) (b : Q) (hb : ∀ q, g q ≤ b)
    (c : StrictOrdEdge P →₀ ℤ) (hc : bdry1 (strictOrderCx P) c = 0) :
    ∃ y : StrictOrdTri P →₀ ℤ, bdry2 (strictOrderCx P) y = c := by
  exact strict_oneCycle_boundary_of_roof_collapse
    (hf.downTransform g hg) (hf.roofTransform g hg b hb)
    (hf.downTransform_monotone g hmono hg)
    (hf.roofTransform_monotone g hg b hb hmono)
    (hf.downTransform_le g hg)
    (fun a => (hf.roofTransform_spec g hg b hb a).1)
    (fun {_ _} h => hf.roofTransform_comparable_equal g hg b hb hmono h) c hc

end FiniteChains.Comb

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {M : CayGroup A → Prop} {att : NeSpx A →o X}
  {P : Type u} [PartialOrder P] {f : P → Zpos A X M att}

theorem strict_oneCycle_cover_attaching_intersection (hf : IsPosetCover f)
    (w : CayGroup A) (hw : w ≠ 1)
    (c : StrictOrdEdge {p : P // ZJSet w (f p)} →₀ ℤ)
    (hc : Comb.bdry1 (strictOrderCx {p : P // ZJSet w (f p)}) c = 0) :
    ∃ y : StrictOrdTri {p : P // ZJSet w (f p)} →₀ ℤ,
      Comb.bdry2 (strictOrderCx {p : P // ZJSet w (f p)}) y = c := by
  let S : Set (Zpos A X M att) := {z | ZJSet w z}
  let e := zJSetOrderIso (M := M) (att := att) w
  let g  := fun q => e.symm (interRho (e q))
  let b  := e.symm (interTop hw)
  have hmono : Monotone g := fun _ _ h =>
    e.symm.monotone (interRho_mono (e.monotone h))
  have hg : ∀ q, g q ≤ q := by
    intro q
    have h := e.symm.monotone (interRho_le (e q))
    simpa using h
  have hb  := fun q =>
    e.symm.monotone (interRho_le_top hw (e q))
  exact strict_oneCycle_cover_roof (IsPosetCover.restriction f S hf)
    g hmono hg b hb c hc

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror Comb Nerve
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {M : CayGroup A → Prop} {att : NeSpx A →o X}
  {P : Type u} [PartialOrder P] {f : P → Zpos A X M att}


theorem fillsDegreeIn_cover_attaching_intersection (hf : IsPosetCover f)
    (w : CayGroup A) (hw : w ≠ 1) :
    FillsDegreeIn (fun p : P => ZJSet w (f p)) 2 := by
  let q := (zJSetOrderIso (M := M) (att := att) w).symm (interTop hw)
  have hne : ∃ p : P, ZJSet w (f p) := by
    obtain ⟨p, hp⟩ := hf.surj q.1
    exact ⟨p, hp.symm ▸ q.2⟩
  apply fillsDegreeIn_of_subtype hne
  intro c hi hd hc
  exact nerve_oneCycle_filling_of_strict
    (strict_oneCycle_cover_attaching_intersection hf w hw) c hi hd hc

omit [Fintype V] in
theorem generatesDegreeIn_cover_chamber [Nonempty X] (hf : IsPosetCover f)
    (w : CayGroup A) :
    GeneratesDegreeIn (fun p : P => InZChamber w (f p))
      (fun p => InZBase (f p)) 3 := by
  by_cases hw : M w
  · exact generatesDegreeIn_of_acyclicRelIn (acyclicRelIn_cover_marked_chamber hf w hw)
  · exact generatesDegreeIn_of_fillsDegreeIn (by
    have hne : ∃ p : P, InZChamber w (f p) := by
      obtain ⟨p, hp⟩ := hf.surj (zApex hw)
      refine ⟨p, ?_⟩
      rw [hp]
      exact inZChamber_zApex hw
    apply fillsDegreeIn_of_subtype hne
    intro c hi hd hc
    exact nerve_twoCycle_filling_of_strict
      (strict_twoCycle_cover_unmarked_chamber hf w hw) c hi hd hc)

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror Comb Nerve
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] [Nonempty X]
  {M : CayGroup A → Prop} {att : NeSpx A →o X}
  {P : Type u} [PartialOrder P] {f : P → Zpos A X M att}

theorem generatesDegreeIn_cover_zupto_insert (hf : IsPosetCover f) (n : ℕ)
    (hprev : GeneratesDegreeIn (fun p : P => ZUpto n (f p))
      (fun p => InZBase (f p)) 3) :
    ∀ S : Set (CayGroup A), S.Finite → (∀ y ∈ S, RACG.clen A y = n + 1) →
      GeneratesDegreeIn
        (fun p : P => ZUpto n (f p) ∨ ∃ y ∈ S, InZChamber y (f p))
        (fun p => InZBase (f p)) 3 := by
  intro S hS
  induction S, hS using Set.Finite.induction_on with
  | empty => simp_all
  | @insert x S hxS hSfin ih =>
      intro hlen
      have hPrevGen := ih (fun y hy => hlen y (Set.mem_insert_of_mem _ hy))
      have hxlen  := hlen x (Set.mem_insert _ _)
      have hx1 : x ≠ 1 := by
        intro h
        rw [h, clen_one] at hxlen
        omega
      let Prev  := fun p => ZUpto n (f p) ∨ ∃ y ∈ S, InZChamber y (f p)
      have hup : ∀ p q : P, p ≤ q → Prev p → Prev q := by
        rintro p q hpq (h | ⟨y, hy, hyp⟩)
        · exact Or.inl (zUpto_up (hf.mono hpq) h)
        · exact Or.inr ⟨y, hy, inZChamber_of_le (hf.mono hpq) hyp⟩
      have hinter : ∀ p : P, (Prev p ∧ InZChamber x (f p)) ↔ ZJSet x (f p) := by
        intro p
        constructor
        · rintro ⟨hprev', hpx⟩
          rcases hprev' with ⟨y, hy, hyp⟩ | ⟨y, hyS, hyp⟩
          · exact (mem_shorter_zchamber_iff hpx).1 ⟨y, by omega, hyp⟩
          · refine (mem_earlier_zchamber_iff hpx).1 ⟨y, ?_, ?_, hyp⟩
            · intro hxy
              exact hxS (hxy ▸ hyS)
            · rw [hlen y (Set.mem_insert_of_mem _ hyS), hxlen]
        · intro hJ
          have hpx  := zJSet_imp_inZChamber hJ
          obtain ⟨y, hylt, hyp⟩ := (mem_shorter_zchamber_iff hpx).2 hJ
          exact ⟨Or.inl ⟨y, by omega, hyp⟩, hpx⟩
      have hmain : GeneratesDegreeIn
          (fun p : P => Prev p ∨ InZChamber x (f p)) (fun p => InZBase (f p)) 3 := by
        refine generatesDegreeIn_union_of_unmixed
          (fun _ => Iff.rfl) ?_
          hPrevGen (generatesDegreeIn_cover_chamber hf x)
          (fillsDegreeIn_congr (fun p => (hinter p).symm)
            (fillsDegreeIn_cover_attaching_intersection hf x hx1))
        rintro p q hpq (hp | hp) _
        · grind
        · exact Or.inr ⟨hp, inZChamber_of_le (hf.mono hpq) hp⟩
      refine generatesDegreeIn_congr (fun p => ?_) hmain
      constructor
      · grind
      · grind

theorem generatesDegreeIn_cover_zupto (hf : IsPosetCover f) :
    ∀ n : ℕ, GeneratesDegreeIn (fun p : P => ZUpto n (f p))
      (fun p => InZBase (f p)) 3 := by
  intro n
  induction n with
  | zero =>
      exact generatesDegreeIn_congr (fun p => (zUpto_zero_iff (f p)).symm)
        (generatesDegreeIn_cover_chamber hf 1)
  | succ n ih =>
      have h := generatesDegreeIn_cover_zupto_insert hf n ih
        {x : CayGroup A | RACG.clen A x = n + 1} (level_finite A (n + 1)) (fun _ hy => hy)
      refine generatesDegreeIn_congr (fun p => ?_) h
      constructor
      · rintro (⟨y, hy, hyp⟩ | ⟨y, hy, hyp⟩)
        · exact ⟨y, by omega, hyp⟩
        · exact ⟨y, le_of_eq hy, hyp⟩
      · rintro ⟨y, hy, hyp⟩
        rcases Nat.lt_or_ge (RACG.clen A y) (n + 1) with h' | h'
        · exact Or.inl ⟨y, by omega, hyp⟩
        · exact Or.inr ⟨y, le_antisymm hy h', hyp⟩

def coverChainBound (c : Nerve.Ch P) : ℕ :=
  c.support.sup (fun l => (l.map (fun p => zlen (f p))).sum)


/-- Every homogeneous two-cycle in an actual covering poset is a cycle on the
actual preimage of the inserted bases plus a genuine finite three-boundary. -/
theorem exists_cover_base_twoCycle (hf : IsPosetCover f) {c : Nerve.Ch P}
    (hc : c ∈ Nerve.Inc P) (hd : lengthProjection 3 c = c) (hcyc : Nerve.bdry c = 0) :
    ∃ d ∈ IncOn (fun p => InZBase (f p)), ∃ y ∈ Nerve.Inc P,
      Nerve.bdry d = 0 ∧ c = d + Nerve.bdry y := by
  obtain ⟨d, hdb, y, hy, hdd, he⟩ := generatesDegreeIn_cover_zupto hf
    (coverChainBound (f := f) c) c (by
      rw [mem_incOn_iff]
      intro l hl
      refine ⟨(mem_inc_iff c).1 hc l hl, ?_⟩
      intro p hp
      obtain ⟨y, hy, hyp⟩ := zUpto_zlen (f p)
      refine ⟨y, ?_, hyp⟩
      have h1 : zlen (f p) ≤ (l.map (fun q => zlen (f q))).sum :=
        List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem hp)
      exact hy.trans (h1.trans (Finset.le_sup
        (f := fun l : List P => (l.map (fun q => zlen (f q))).sum) hl))) hd hcyc
  exact ⟨d, hdb, y, incOn_le_inc _ hy, hdd, he⟩

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror Comb Nerve
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] [Nonempty X]
  {M : CayGroup A → Prop} {att : NeSpx A →o X}
  {P : Type u} [PartialOrder P] {f : P → Zpos A X M att}

theorem exists_cover_base_cellular_cycle (hf : IsPosetCover f)
    (z : OrdTri P →₀ ℤ) (hz : Comb.bdry2 (orderCx P) z = 0) :
    ∃ c : OrdTri P →₀ ℤ,
      c ∈ Finsupp.supported ℤ ℤ (ordTriOn (fun p => InZBase (f p))) ∧
      Comb.bdry2 (orderCx P) c = 0 ∧
      ∃ y : OrdTet P →₀ ℤ, z = c + ordBoundary3 y := by
  obtain ⟨c₀, hc₀, y₀, hy₀, hdc₀, he₀⟩ := exists_cover_base_twoCycle hf
    (ordNerveChain2_mem_inc z) (ordNerveChain2_lengthProjection z)
    ((ordNerveChain2_cycle_iff z).mpr hz)
  let c := lengthProjection 3 c₀
  let y := lengthProjection 4 y₀
  have hc : c ∈ IncOn (fun p => InZBase (f p)) := lengthProjection_mem_incOn _ hc₀
  have hy : y ∈ Nerve.Inc P := lengthProjection_mem_inc _ hy₀
  have hdc : Nerve.bdry c = 0 := by
    dsimp only [c]
    rw [← lengthProjection_bdry, hdc₀, map_zero]
  have he : ordNerveChain2 z = c + Nerve.bdry y := by
    have h := congrArg (lengthProjection 3) he₀
    rw [ordNerveChain2_lengthProjection, map_add, lengthProjection_bdry] at h
    exact h
  have hec : ordNerveChain2 (decodeOrdNerve2 c) = c := by
    rw [ordNerveChain2_decode (incOn_le_inc _ hc)]
    exact lengthProjection_idempotent _ _
  have hey : ordNerveChain3 (decodeOrdNerve3 y) = y := by
    rw [ordNerveChain3_decode hy]
    exact lengthProjection_idempotent _ _
  refine ⟨decodeOrdNerve2 c, decodeOrdNerve2_supported hc, ?_, decodeOrdNerve3 y, ?_⟩
  · apply (ordNerveChain2_cycle_iff _).mp
    rw [hec, hdc]
  · apply ordNerveChain2_injective
    rw [map_add, hec, ordNerveChain2_ordBoundary3, hey]
    exact he

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] [Nonempty X]
  {M : CayGroup A → Prop} {att : NeSpx A →o X}

/-- Every actual universal-cover two-cycle is a cycle supported on lifted base
triangles plus the actual alternating boundary of finite lifted tetrahedra. -/
theorem exists_uCover_base_cellular_cycle (a : Zpos A X M att)
    (hconn : IsConnected (orderCx (Zpos A X M att)))
    (z : UF (orderCx (Zpos A X M att)) a →₀ ℤ)
    (hz : Comb.bdry2 (uCover (orderCx (Zpos A X M att)) a) z = 0) :
    ∃ c : UF (orderCx (Zpos A X M att)) a →₀ ℤ,
      (∀ t ∈ c.support, InZBase t.1.2.1.1 ∧ InZBase t.1.2.1.2.1 ∧
        InZBase t.1.2.1.2.2) ∧
      Comb.bdry2 (uCover (orderCx (Zpos A X M att)) a) c = 0 ∧
      ∃ y : UOrdTet (Zpos A X M att) a →₀ ℤ, z = c + uOrdBoundary3 y := by
  classical
  obtain ⟨d, ⟨hd, hdc⟩, _⟩ := exists_unique_uOrder_cycle z hz
  obtain ⟨c, hc, hcc, y, he⟩ := exists_cover_base_cellular_cycle
    (uOrderEnd_isPosetCover hconn) d hdc
  refine ⟨Finsupp.mapDomain uOrderFace c, ?_, ?_, Finsupp.mapDomain uOrderTet y, ?_⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ht)
    have hb := (Finsupp.mem_supported ℤ c).mp hc hs
    exact hb
  · exact (uOrderHom_cycle_iff c).mpr hcc
  · have h := congrArg (chain2 uOrderHom) he
    erw [hd, map_add, uOrderHom_ordBoundary3] at h
    exact h

end FiniteChains.Davis

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u
variable {X Y : Complex2.{u}} {p : Hom X Y} (hp : IsCovering p) (a : X.V)
include hp

theorem univLiftV_injective_of_covering : Function.Injective (univLiftV a p) := by
  intro v w h
  induction v using UV.ind with
  | h m =>
    induction w using UV.ind with
    | h n =>
      have hh : Htpy Y (p.onV a) (p.onV (endpt X a m.1))
          (mapPath p m.1) (mapPath p n.1) := by
        have ht := Quotient.exact h
        change Htpy Y (p.onV a) (endpt Y (p.onV a) (mapPath p m.1))
          (mapPath p m.1) (mapPath p n.1) at ht
        rwa [endpt_mapPath] at ht
      obtain ⟨l, hl, hmap, hml⟩ := lift_htpy hp m.2 hh
      have hn  := liftPath_unique hp l n.1 a _ _ hl n.2 hmap
      apply UV.sound
      rwa [hn] at hml

theorem univLiftV_surjective_of_covering : Function.Surjective (univLiftV a p) := by
  intro v
  induction v using UV.ind with
  | h n =>
    obtain ⟨l, b, hl, hmap⟩ := exists_liftPathAt hp n.1 a _ n.2
    have hl' : IsPath X.src X.tgt l a (endpt X a l) := by
      rw [endpt_eq_of_isPath hl]
      exact hl
    refine ⟨UV.mk ⟨l, hl'⟩, ?_⟩
    rw [univLiftV_mk]
    congr 1
    exact Subtype.ext hmap




theorem univLift_cycle_iff_of_covering (c : UF X a →₀ ℤ) :
    bdry2 (uCover Y (p.onV a)) (chain2 (univLift X p a) c) = 0 ↔
      bdry2 (uCover X a) c = 0 := by
  rw [bdry2_chain2]
  constructor
  · intro h
    apply Finsupp.mapDomain_injective (show Function.Injective (univLiftE a p) by
      intro v w h
      have hv  := univLiftV_injective_of_covering hp a
        (congrArg (fun e : UE Y (p.onV a) => e.1.1) h)
      have he  :=
        congrArg (fun e : UE Y (p.onV a) => e.1.2) h
      have hs  :=
        w.2.symm.trans (congrArg endV hv.symm)
      have hg := liftGerm_unique hp (x := (v.1.2, true))
        (y := (w.1.2, true)) v.2.symm hs (Prod.ext he rfl)
      exact Subtype.ext (Prod.ext hv (congrArg Prod.fst hg)))
    rw [Finsupp.mapDomain_zero]
    exact h
  · simp_all

theorem exists_unique_cycle_lift_of_covering (c : UF Y (p.onV a) →₀ ℤ)
    (hc : bdry2 (uCover Y (p.onV a)) c = 0) :
    ∃! d : UF X a →₀ ℤ,
      chain2 (univLift X p a) d = c ∧ bdry2 (uCover X a) d = 0 := by
  obtain ⟨d, hd⟩ := Finsupp.mapDomain_surjective (show Function.Surjective (univLiftF a p) by
    intro t
    obtain ⟨v, hv⟩ := univLiftV_surjective_of_covering hp a t.1.1
    have he : p.onV (endV v) = endV t.1.1 := by
      rw [← endV_univLiftV, hv]
    obtain ⟨f, ⟨hf, hb⟩, _⟩ := exists_unique_liftCell hp t.1.2 (t.2.symm.trans he.symm)
    refine ⟨⟨(v, f), hb.symm⟩, ?_⟩
    exact Subtype.ext (Prod.ext hv hf)) c
  have hd' : chain2 (univLift X p a) d = c := hd
  refine ⟨d, ⟨hd', (univLift_cycle_iff_of_covering hp a d).mp (by rw [hd']; exact hc)⟩, ?_⟩
  intro e he
  exact Finsupp.mapDomain_injective (by
    intro v w h
    have hv  := univLiftV_injective_of_covering hp a
      (congrArg (fun f : UF Y (p.onV a) => f.1.1) h)
    have hf  :=
      congrArg (fun f : UF Y (p.onV a) => f.1.2) h
    have hb  := v.2.symm.trans ((congrArg endV hv).trans w.2)
    have hc  := hp.cell.1 (Subtype.ext (Prod.ext hf hb))
    exact Subtype.ext (Prod.ext hv hc))
    (he.1.trans hd'.symm)

end FiniteChains.Comb

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

def uOrdTetMap (f : P → Q) (hf : Monotone f) (a : P) (t : UOrdTet P a) : UOrdTet Q (f a) :=
  ⟨(@univLiftV (orderCx P) (orderCx Q) a (orderCxMap f hf) t.1.1, ordTetMap f hf t.1.2), by
    rw [endV_univLiftV, t.2]
    rfl⟩



theorem univLift_uOrdBoundary3 (f : P → Q) (hf : Monotone f) (a : P)
    (y : UOrdTet P a →₀ ℤ) :
    chain2 (univLift (orderCx P) (orderCxMap f hf) a) (uOrdBoundary3 y) =
      uOrdBoundary3 (Finsupp.mapDomain (uOrdTetMap f hf a) y) := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, Finsupp.mapDomain_add, map_add]
  | single t n =>
    rw [uOrdBoundary3, Finsupp.linearCombination_single, map_smul]
    change n • Finsupp.mapDomain (@univLiftF (orderCx P) (orderCx Q) a (orderCxMap f hf))
      (uOrdTetBoundary t) = _
    rw [(show Finsupp.mapDomain (@univLiftF (orderCx P) (orderCx Q) a (orderCxMap f hf))
      (uOrdTetBoundary t) = uOrdTetBoundary (uOrdTetMap f hf a t) by
      let L  :=
        Finsupp.lmapDomain ℤ ℤ (@univLiftF (orderCx P) (orderCx Q) a (orderCxMap f hf))
      change L (uOrdTetBoundary t) = _
      simp only [uOrdTetBoundary, map_sub, map_add]
      simp only [L, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
      rw [(show univLiftF a (orderCxMap f hf) (uOrdTetFace0 t) = uOrdTetFace0 (uOrdTetMap f hf a t) by
        apply Subtype.ext
        apply Prod.ext
        · exact univLiftV_extend a (orderCxMap f hf) (eb := ordPos t.1.2.2.1)
            t.2
        · rfl)]
      rfl), Finsupp.mapDomain_single, uOrdBoundary3,
      Finsupp.linearCombination_single]

end FiniteChains.Comb

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] [Nonempty X] {att : NeSpx A →o X}

def InQBase (q : Qpos A X att) : Prop := ∃ x : X, qNew (A := A) (att := att) x = q

omit [Fintype V] [Nonempty X] in
theorem inQBase_zProj {z : Zpos A X (IsGamma A) att} (hz : InZBase z) :
    InQBase (zProj z) := by
  cases z with
  | inl p => exact hz.elim
  | inr wx => exact ⟨wx.2, rfl⟩

/-- The quotient's actual universal-cover cycles are generated by cycles on the
actual inverse image of its inserted base, modulo genuine lifted three-boundaries. -/
theorem exists_qCover_base_cellular_cycle (a : Zpos A X (IsGamma A) att)
    (hconn : IsConnected (orderCx (Zpos A X (IsGamma A) att)))
    (z : UF (orderCx (Qpos A X att)) (zProj a) →₀ ℤ)
    (hz : Comb.bdry2 (uCover (orderCx (Qpos A X att)) (zProj a)) z = 0) :
    ∃ c : UF (orderCx (Qpos A X att)) (zProj a) →₀ ℤ,
      (∀ t ∈ c.support, InQBase t.1.2.1.1 ∧ InQBase t.1.2.1.2.1 ∧
        InQBase t.1.2.1.2.2) ∧
      Comb.bdry2 (uCover (orderCx (Qpos A X att)) (zProj a)) c = 0 ∧
      ∃ y : UOrdTet (Qpos A X att) (zProj a) →₀ ℤ, z = c + uOrdBoundary3 y := by
  classical
  let p := orderCxMap (zProj (att := att)) zProj_monotone
  have hp : IsCovering p := isCovering_orderCxMap_zProj
  obtain ⟨d, ⟨hd, hdc⟩, _⟩ := exists_unique_cycle_lift_of_covering hp a z hz
  obtain ⟨c, hc, hcc, y, he⟩ := exists_uCover_base_cellular_cycle a hconn d hdc
  refine ⟨Finsupp.mapDomain (@univLiftF (orderCx (Zpos A X (IsGamma A) att))
    (orderCx (Qpos A X att)) a p) c, ?_, ?_,
    Finsupp.mapDomain (uOrdTetMap zProj zProj_monotone a) y, ?_⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ht)
    obtain ⟨h₀, h₁, h₂⟩ := hc s hs
    exact ⟨inQBase_zProj h₀, inQBase_zProj h₁, inQBase_zProj h₂⟩
  · exact (univLift_cycle_iff_of_covering hp a c).mpr hcc
  · have h := congrArg (chain2 (univLift (orderCx (Zpos A X (IsGamma A) att)) p a)) he
    rw [hd, map_add, univLift_uOrdBoundary3] at h
    exact h

end FiniteChains.Davis
end

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

def qBaseOrderIso : {q : Qpos A X att // InQBase q} ≃o X where
  toFun q := Classical.choose q.2
  invFun x := ⟨qNew x, ⟨x, rfl⟩⟩
  left_inv q := Subtype.ext (Classical.choose_spec q.2)
  right_inv x := Sum.inr.inj (Classical.choose_spec (show InQBase (qNew x) from ⟨x, rfl⟩))
  map_rel_iff' {q r} := by
    change Classical.choose q.2 ≤ Classical.choose r.2 ↔ q.1 ≤ r.1
    have h : qNew (A := A) (att := att) (Classical.choose q.2) ≤
        qNew (A := A) (att := att) (Classical.choose r.2) ↔ q.1 ≤ r.1 := by
      rw [Classical.choose_spec q.2, Classical.choose_spec r.2]
    exact h

abbrev QLiftedBase (a : Qpos A X att) :=
  {p : UOrder (Qpos A X att) a // InQBase (uOrderEnd p)}

def qBaseCoverEnd (a : Qpos A X att) (p : QLiftedBase a) : X :=
  qBaseOrderIso ⟨uOrderEnd p.1, p.2⟩

omit [Fintype V] in
theorem qBaseCoverEnd_isPosetCover (a : Qpos A X att)
    (hc : IsConnected (orderCx (Qpos A X att))) : IsPosetCover (qBaseCoverEnd a) := by
  let S : Set (Qpos A X att) := {q | InQBase q}
  have h := IsPosetCover.restriction (uOrderEnd (a := a)) S
    (uOrderEnd_isPosetCover hc)
  exact h.postcompose_orderIso qBaseOrderIso

omit [Fintype V] in
theorem qBaseCoverEnd_spec (a : Qpos A X att) (p : QLiftedBase a) :
    qNew (qBaseCoverEnd a p) = uOrderEnd p.1 := Classical.choose_spec p.2

end FiniteChains.Davis

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

omit [Fintype V] in
theorem qBaseCover_path_projection (a : Qpos A X att)
    (hc : IsConnected (orderCx (Qpos A X att)))
    (l : List ((orderCx (QLiftedBase a)).E × Bool)) :
    mapPath (orderCxMap (qNew (A := A) (X := X) (att := att)) qNew_monotone)
      (mapPath (orderCxMap (qBaseCoverEnd a) (qBaseCoverEnd_isPosetCover a hc).mono) l) =
    mapPath (orderCxMap (uOrderEnd (P := Qpos A X att) (a := a)) uOrderEnd_monotone)
      (mapPath (orderCxMap (Subtype.val : QLiftedBase a → UOrder (Qpos A X att) a)
        (fun _ _ h => h)) l) := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    simp only [mapPath, List.map_cons] at ih ⊢
    erw [ih]
    congr 1
    apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext (qBaseCoverEnd_spec a e.1.1.1) (qBaseCoverEnd_spec a e.1.1.2)
    · rfl

/-- All edge loops of the actual full lifted base are null-homotopic. Its
different components are not identified with one another. -/
theorem qLiftedBase_simplyConnected (a : Qpos A X att)
    (hc : IsConnected (orderCx (Qpos A X att))) :
    SimplyConnected (orderCx (QLiftedBase a)) := by
  let beta := orderCxMap (qBaseCoverEnd a) (qBaseCoverEnd_isPosetCover a hc).mono
  have hcov  := isCovering_orderCxMap (qBaseCoverEnd_isPosetCover a hc)
  let incl := orderCxMap (Subtype.val : QLiftedBase a → UOrder (Qpos A X att) a)
    (fun _ _ h => h)
  let proj := orderCxMap (uOrderEnd (a := a)) uOrderEnd_monotone
  intro b p hp
  have hi := uOrder_complex_simplyConnected (a := a)
    b.1 (mapPath incl p) (isPath_mapPath incl hp)
  have hnull := mapPath_htpy proj hi
  have hq : Htpy (orderCx (Qpos A X att)) (qNew (A := A) (att := att) (qBaseCoverEnd (X := X) a b))
      (qNew (A := A) (att := att) (qBaseCoverEnd (X := X) a b))
      (mapPath (orderCxMap (qNew (A := A) (X := X) (att := att)) qNew_monotone)
        (mapPath beta p)) [] := by
    erw [qBaseCover_path_projection a hc, qBaseCoverEnd_spec]
    exact hnull
  let l : Loop (orderCx X) (qBaseCoverEnd (X := X) a b) := ⟨mapPath beta p, isPath_mapPath beta hp⟩
  have hcl : Pi1.mk l = 1 := by
    apply pi1Map_qNew_injective (A := A) (att := att) (qBaseCoverEnd (X := X) a b)
    erw [map_one]
    exact Quotient.sound hq
  have hl  := Quotient.exact hcl
  obtain ⟨m, _, hmap, hpm⟩ := lift_htpy hcov hp hl
  have hm  := List.map_eq_nil_iff.mp hmap
  rwa [hm] at hpm

end FiniteChains.Davis
end

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [Preorder X] [Nonempty X] {M : CayGroup A → Prop}
  {att : NeSpx A →o X}

omit [Fintype V] [Nonempty X] in
theorem zChamber_reachable (hc : IsConnected (orderCx X)) (w : CayGroup A)
    {p q : Zpos A X M att} (hp : InZChamber w p) (hq : InZChamber w q) :
    Reach (orderCx (Zpos A X M att)) p q := by
  apply (orderComponentLabel_eq_iff p q).mp
  by_cases hw : M w
  · let rp := zChamberRetr hw ⟨p, hp⟩
    let rq := zChamberRetr hw ⟨q, hq⟩
    obtain ⟨x, hx⟩ := zChamberRetr_mem hw ⟨p, hp⟩
    obtain ⟨y, hy⟩ := zChamberRetr_mem hw ⟨q, hq⟩
    have hpx := orderComponentLabel_eq_of_le
      (show rp.1 ≤ p from zChamberRetr_le hw ⟨p, hp⟩)
    have hqy := orderComponentLabel_eq_of_le
      (show rq.1 ≤ q from zChamberRetr_le hw ⟨q, hq⟩)
    have hm : Monotone (zNew (att := att) ⟨w, hw⟩) :=
      fun _ _ h => ⟨rfl, h⟩
    obtain ⟨l, hl⟩ := hc x y
    have hr : Reach (orderCx (Zpos A X M att))
        (zNew (att := att) ⟨w, hw⟩ x) (zNew (att := att) ⟨w, hw⟩ y) :=
      ⟨_, isPath_mapPath (orderCxMap _ hm) hl⟩
    have hxy := (orderComponentLabel_eq_iff _ _).mpr hr
    have hx'  := hx
    have hy'  := hy
    rw [hx'] at hpx
    rw [hy'] at hqy
    exact hpx.symm.trans (hxy.trans hqy)
  · exact (orderComponentLabel_eq_of_le (zApex_le hw hp)).symm.trans
      (orderComponentLabel_eq_of_le (zApex_le hw hq))

omit [Fintype V] in
theorem exists_zChamber_vertex (w : CayGroup A) :
    ∃ p : Zpos A X M att, InZChamber w p := by
  by_cases hw : M w
  · exact ⟨zNew ⟨w, hw⟩ (Classical.choice inferInstance), rfl⟩
  · exact ⟨zApex hw, inZChamber_zApex hw⟩

/-- Connectivity follows from the connected base and the actual nonempty attaching
intersections, by induction on chamber word length. -/
theorem zpos_isConnected (hc : IsConnected (orderCx X)) :
    IsConnected (orderCx (Zpos A X M att)) := by
  obtain ⟨b, hb⟩ := exists_zChamber_vertex (att := att) 1
  have hr : ∀ n w, RACG.clen A w = n → ∀ p : Zpos A X M att,
      InZChamber w p → orderComponentLabel _ p = orderComponentLabel _ b := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hw p hp
      by_cases hw1 : w = 1
      · subst w
        exact (orderComponentLabel_eq_iff _ _).mpr (zChamber_reachable hc 1 hp hb)
      · obtain ⟨j, hj⟩ := exists_zJSet (M := M) (att := att) hw1
        have hjw := zJSet_imp_inZChamber hj
        obtain ⟨y, hy, hjy⟩ := (mem_shorter_zchamber_iff hjw).2 hj
        have hnj : RACG.clen A y < n := by omega
        exact ((orderComponentLabel_eq_iff _ _).mpr
          (zChamber_reachable hc w hp hjw)).trans (ih _ hnj y rfl j hjy)
  intro p q
  obtain ⟨w, hw⟩ := exists_inZChamber p
  obtain ⟨v, hv⟩ := exists_inZChamber q
  exact (orderComponentLabel_eq_iff _ _).mp
    ((hr _ w rfl p hw).trans (hr _ v rfl q hv).symm)

end FiniteChains.Davis

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

/-- Actual deck transformations commute with actual lifted order steps. -/
theorem uOrderStep_deckV (g : Pi1 (orderCx P) a) (v : UOrder P a) (q : P)
    (h : uOrderEnd v ≤ q) :
    uOrderStep (deckV g v) q (by simpa only [uOrderEnd, endV_deckV] using h) =
      deckV g (uOrderStep v q h) := by
  have he : ordPos (by simpa only [uOrderEnd, endV_deckV] using h :
      uOrderEnd (deckV g v) ≤ q) = ordPos h := by
    apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext (endV_deckV g v) rfl
    · rfl
  unfold uOrderStep
  rw [he, extend_deckV]

/-- The actual deck action preserves the genuine lifted partial order. -/
theorem uOrder_deckV_monotone (g : Pi1 (orderCx P) a) :
    @Monotone (UOrder P a) (UOrder P a)
      (uOrderPartialOrder (P := P) (a := a)).toPreorder
      (uOrderPartialOrder (P := P) (a := a)).toPreorder (deckV g) := by
  intro v z hvz
  obtain ⟨h, he⟩ := hvz
  refine ⟨by simpa only [uOrderEnd, endV_deckV] using h, ?_⟩
  have hs := uOrderStep_deckV g v (uOrderEnd z) h
  simpa only [uOrderEnd, endV_deckV] using hs.trans (congrArg (deckV g) he)

/-- Deck transformations are actual order isomorphisms of the path-class cover. -/
def uOrderDeckOrderIso (g : Pi1 (orderCx P) a) : UOrder P a ≃o UOrder P a where
  toFun := deckV g
  invFun := deckV g⁻¹
  left_inv v := by rw [← deckV_mul, inv_mul_cancel, deckV_one]
  right_inv v := by rw [← deckV_mul, mul_inv_cancel, deckV_one]
  map_rel_iff' {v z} := by
    change UOrderLe (deckV g v) (deckV g z) ↔ UOrderLe v z
    constructor
    · intro h
      have hi := uOrder_deckV_monotone g⁻¹ h
      change UOrderLe (deckV g⁻¹ (deckV g v)) (deckV g⁻¹ (deckV g z)) at hi
      simpa only [← deckV_mul, inv_mul_cancel, deckV_one] using hi
    · exact fun h => uOrder_deckV_monotone g h

/-- The deck action on the actual lifted-order type. -/
def uOrderDeck (g : Pi1 (orderCx P) a) (v : UOrder P a) : UOrder P a := deckV g v

theorem uOrderDeck_end (g : Pi1 (orderCx P) a) (v : UOrder P a) :
    uOrderEnd (uOrderDeck g v) = uOrderEnd v := endV_deckV g v

end FiniteChains.Comb
end

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] (S : Set P)

def ordSubposetIncl : Hom (orderCx S) (orderCx P) :=
  orderCxMap Subtype.val (fun _ _ h => h)


theorem ordSubposetIncl_onF_injective :
    Function.Injective (ordSubposetIncl S).onF := by
  intro a b h
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun t : OrdTri P => t.1.1) h
  · apply Prod.ext <;> ext
    · exact congrArg (fun t : OrdTri P => t.1.2.1) h
    · exact congrArg (fun t : OrdTri P => t.1.2.2) h

/-- A triangle is in the induced subcomplex exactly when its three vertices lie in it. -/
theorem ordSubposetIncl_onF_range (t : OrdTri P) :
    t ∈ Set.range (ordSubposetIncl S).onF ↔
      t.1.1 ∈ S ∧ t.1.2.1 ∈ S ∧ t.1.2.2 ∈ S := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.1.1.2, a.1.2.1.2, a.1.2.2.2⟩
  · rintro ⟨ha, hb, hc⟩
    exact ⟨⟨(⟨t.1.1, ha⟩, ⟨t.1.2.1, hb⟩, ⟨t.1.2.2, hc⟩), t.2⟩,
      Subtype.ext rfl⟩

/-- Every finite chain supported on the actual subcomplex is the image of a finite
chain on that subcomplex. If it is a cycle, its unique lift is a cycle too. -/
theorem exists_ordSubposet_cycle (c : OrdTri P →₀ ℤ)
    (hs : ∀ t ∈ c.support, t.1.1 ∈ S ∧ t.1.2.1 ∈ S ∧ t.1.2.2 ∈ S)
    (hc : bdry2 (orderCx P) c = 0) :
    ∃ d : OrdTri S →₀ ℤ,
      chain2 (ordSubposetIncl S) d = c ∧ bdry2 (orderCx S) d = 0 := by
  let d := Finsupp.comapDomain (ordSubposetIncl S).onF c
    (ordSubposetIncl_onF_injective S).injOn
  have hd : chain2 (ordSubposetIncl S) d = c :=
    Finsupp.mapDomain_comapDomain _ (ordSubposetIncl_onF_injective S) c
      (fun t ht => (ordSubposetIncl_onF_range S t).mpr (hs t ht))
  refine ⟨d, hd, ?_⟩
  apply Finsupp.mapDomain_injective (show Function.Injective (ordSubposetIncl S).onE by
    intro a b h
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg (fun e : OrdEdge P => e.1.1) h
    · exact congrArg (fun e : OrdEdge P => e.1.2) h)
  change chain1 (ordSubposetIncl S) (bdry2 (orderCx S) d) =
    Finsupp.mapDomain _ 0
  rw [Finsupp.mapDomain_zero, ← bdry2_chain2, hd, hc]

end FiniteChains.Comb

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}


def qLiftedBaseFaceMap (a : Qpos A X att) :
    OrdTri (QLiftedBase a) → UF (orderCx (Qpos A X att)) a :=
  uOrderFace ∘ (fun t => ⟨(t.1.1.1, t.1.2.1.1, t.1.2.2.1), t.2⟩)

theorem qpos_isConnected_of_zpos
    (hconn : IsConnected (orderCx (Zpos A X (IsGamma A) att))) :
    IsConnected (orderCx (Qpos A X att)) := by
  intro q r
  obtain ⟨v, hv⟩ := zProj_surjective q
  obtain ⟨w, hw⟩ := zProj_surjective r
  obtain ⟨l, hl⟩ := hconn v w
  let p := orderCxMap (zProj (att := att)) zProj_monotone
  have h := isPath_mapPath p hl
  change IsPath (orderCx (Qpos A X att)).src (orderCx (Qpos A X att)).tgt
    (mapPath p l) (zProj v) (zProj w) at h
  erw [hv, hw] at h
  exact ⟨mapPath p l, h⟩

omit [Fintype V] in
theorem exists_qCover_base_cycle_preimage {a : Qpos A X att}
    (c : UF (orderCx (Qpos A X att)) a →₀ ℤ)
    (hs : ∀ t ∈ c.support, InQBase t.1.2.1.1 ∧ InQBase t.1.2.1.2.1 ∧
      InQBase t.1.2.1.2.2)
    (hc : Comb.bdry2 (uCover (orderCx (Qpos A X att)) a) c = 0) :
    ∃ d : OrdTri (QLiftedBase a) →₀ ℤ,
      Comb.bdry2 (orderCx (QLiftedBase a)) d = 0 ∧
      Finsupp.mapDomain (qLiftedBaseFaceMap a) d = c := by
  classical
  obtain ⟨e, ⟨he, hecyc⟩, _⟩ := exists_unique_uOrder_cycle c hc
  have he' : Finsupp.mapDomain uOrderFace e = c := he
  let S : Set (UOrder (Qpos A X att) a) := {p | InQBase (uOrderEnd p)}
  have hes : ∀ t ∈ e.support, t.1.1 ∈ S ∧ t.1.2.1 ∈ S ∧ t.1.2.2 ∈ S := by
    intro t ht
    have ht' : uOrderFace t ∈ c.support := by
      erw [← he', Finsupp.mapDomain_support_of_injective uOrderFace_injective]
      exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
    exact hs _ ht'
  obtain ⟨d, hd, hdcyc⟩ := exists_ordSubposet_cycle S e hes hecyc
  refine ⟨d, hdcyc, ?_⟩
  change Finsupp.mapDomain (uOrderFace ∘ (ordSubposetIncl S).onF) d = c
  rw (config := { transparency := .default }) [Finsupp.mapDomain_comp]
  change Finsupp.mapDomain uOrderFace (chain2 (ordSubposetIncl S) d) = c
  rw (config := { transparency := .default }) [hd, he']

variable [Nonempty X]

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

def InQOld : Qpos A X att → Prop
  | .inl _ => True
  | .inr _ => False

def InQBaseStar : Qpos A X att → Prop
  | .inl c => c.1.sgn = 0
  | .inr _ => True

omit [DecidableEq V] in
theorem inQBase_in_star {p : Qpos A X att} (hp : InQBase p) : InQBaseStar p := by
  obtain ⟨x, rfl⟩ := hp
  trivial

theorem qOld_baseStar_unmixed (p r : Qpos A X att) (h : p ≤ r) :
    (InQOld p ∧ InQOld r) ∨ (InQBaseStar p ∧ InQBaseStar r) := by
  cases p with
  | inl c =>
    cases r with
    | inl d => exact Or.inl ⟨trivial, trivial⟩
    | inr y => exact False.elim h
  | inr x =>
    cases r with
    | inl d => exact Or.inr ⟨trivial, h.1⟩
    | inr y => exact Or.inr ⟨trivial, trivial⟩

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

abbrev QPositiveOld := {p : Qpos A X att // InQOld p ∧ InQBaseStar p}

def qPositiveOldSimplex (p : QPositiveOld (att := att)) : NeSpx A := by
  rcases p with ⟨p, hp⟩
  cases p with
  | inl c =>
    exact ⟨c.1.spx, Finset.nonempty_iff_ne_empty.mpr (fun h => c.2 ⟨h, hp.2⟩), c.1.isSimplex⟩
  | inr x => exact False.elim hp.1

def qPositiveOldPoint (s : NeSpx A) : QPositiveOld (att := att) :=
  ⟨Sum.inl (posQCube s), trivial, rfl⟩

def qPositiveOldOrderIso : QPositiveOld (att := att) ≃o NeSpx A where
  toFun := qPositiveOldSimplex
  invFun := qPositiveOldPoint
  left_inv p := by
    rcases p with ⟨p, hp⟩
    cases p with
    | inl c =>
      apply Subtype.ext
      apply congrArg Sum.inl
      apply Subtype.ext
      apply QCube.ext'
      · rfl
      · intro v _
        exact (congrFun hp.2 v).symm
    | inr x => exact False.elim hp.1
  right_inv s := rfl
  map_rel_iff' := by
    rintro ⟨p, hp⟩ ⟨r, hr⟩
    cases p with
    | inr x => exact False.elim hp.1
    | inl c =>
      cases r with
      | inr x => exact False.elim hr.1
      | inl d =>
        constructor
        · intro h
          refine ⟨h, ?_⟩
          intro v _
          exact (congrFun hp.2 v).trans (congrFun hr.2 v).symm
        · exact fun h => h.1

abbrev QLiftedAttaching (a : Qpos A X att) :=
  {p : UOrder (Qpos A X att) a // InQOld (uOrderEnd p) ∧ InQBaseStar (uOrderEnd p)}

def qAttachingCoverEnd (a : Qpos A X att) (p : QLiftedAttaching a) : NeSpx A :=
  qPositiveOldSimplex ⟨uOrderEnd p.1, p.2⟩

variable [Fintype V]

/-- The cycles extracted by the old/star gluing lie on an actual covering of
the original attaching locus; no abstract surface identification is assumed. -/
theorem qAttachingCoverEnd_isPosetCover (x : X) (hx : IsConnected (orderCx X)) :
    IsPosetCover (qAttachingCoverEnd (qNew (A := A) (att := att) x)) := by
  letI : Nonempty X := ⟨x⟩
  have hc : IsConnected (orderCx (Qpos A X att)) := qpos_isConnected_of_zpos (zpos_isConnected hx)
  have hf := (uOrderEnd_isPosetCover hc).restriction
    (f := uOrderEnd (P := Qpos A X att) (a := qNew x))
    {p | InQOld p ∧ InQBaseStar p}
  exact hf.postcompose_orderIso qPositiveOldOrderIso

end FiniteChains.Davis

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
variable {P : Type} [PartialOrder P]

def ordTriangleCoefficient (t : OrdTri P) : Nerve.Ch P →+ ℤ := by
  classical
  exact FreeAbelianGroup.lift (fun l =>
    if l = [t.1.1, t.1.2.1, t.1.2.2] then 1 else 0)

/-- Reading a flag coefficient in the full nerve agrees with reading its cellular coordinate. -/
theorem ordTriangleCoefficient_encode (t : OrdTri P) (c : OrdTri P →₀ ℤ) :
    ordTriangleCoefficient t (ordNerveChain2 c) = c t := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single w n =>
    have he : [w.1.1, w.1.2.1, w.1.2.2] = [t.1.1, t.1.2.1, t.1.2.2] ↔ w = t := by
      constructor
      · intro h
        apply Subtype.ext
        simp at h
        exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)
      · rintro rfl
        rfl
    simp [ordNerveChain2, ordTriangleCoefficient, FreeAbelianGroup.lift_apply_of,
      Finsupp.single_apply, he]

theorem normalizeOrdChain2_apply (c : OrdTri P →₀ ℤ) (t : StrictOrdTri P) :
    normalizeOrdChain2 c t = c ((strictOrderIncl P).onF t) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single w n =>
    rw [normalizeOrdChain2_single]
    by_cases hw : w.1.1 < w.1.2.1 ∧ w.1.2.1 < w.1.2.2
    · have he : ⟨w.1, hw⟩ = t ↔ w = (strictOrderIncl P).onF t := by
        constructor <;> intro h <;> apply Subtype.ext
        · exact congrArg (fun u : StrictOrdTri P => u.val) h
        · exact congrArg (fun u : OrdTri P => u.val) h
      simp [normalizeOrdTriangle, hw, Finsupp.single_apply, he]
    · have he : w ≠ (strictOrderIncl P).onF t := by
        intro h
        apply hw
        simpa [h, strictOrderIncl] using t.2
      simp [normalizeOrdTriangle, hw, he]

end FiniteChains.Comb
end

namespace FiniteChains.Davis
open FreeAbelianGroup

def flagEdge {P : Type} (a b e : P) : Nerve.Ch P := of [a, e] - of [b, e]

def triangleFlagChain {P : Type} (a b c ab bc ca t : P) : Nerve.Ch P :=
  (of [a, ab, t] - of [b, ab, t]) +
  (of [b, bc, t] - of [c, bc, t]) +
  (of [c, ca, t] - of [a, ca, t])

theorem bdry_triangleFlagChain {P : Type} (a b c ab bc ca t : P) :
    Nerve.bdry (triangleFlagChain a b c ab bc ca t) =
      flagEdge a b ab + flagEdge b c bc + flagEdge c a ca := by
  simp only [triangleFlagChain, map_add, map_sub, Nerve.bdry_of,
    Nerve.bdryOn_cons, Nerve.bdryOn_nil, map_zero, sub_zero, Nerve.consMap_of]
  unfold flagEdge
  abel

theorem flagTriangle_mem_inc {P : Type} [Preorder P] {a e t : P}
    (hae : a ≤ e) (het : e ≤ t) : of [a, e, t] ∈ Nerve.Inc P :=
  Nerve.of_mem_inc (by simp [List.isChain_cons_cons, hae, het])

theorem triangleFlagChain_mem_inc {P : Type} [Preorder P] {a b c ab bc ca t : P}
    (ha : a ≤ ab) (hb : b ≤ ab) (hb' : b ≤ bc) (hc : c ≤ bc)
    (hc' : c ≤ ca) (ha' : a ≤ ca) (hab : ab ≤ t) (hbc : bc ≤ t) (hca : ca ≤ t) :
    triangleFlagChain a b c ab bc ca t ∈ Nerve.Inc P := by
  exact (Nerve.Inc P).add_mem
    ((Nerve.Inc P).add_mem
      ((Nerve.Inc P).sub_mem (flagTriangle_mem_inc ha hab) (flagTriangle_mem_inc hb hab))
      ((Nerve.Inc P).sub_mem (flagTriangle_mem_inc hb' hbc) (flagTriangle_mem_inc hc hbc)))
    ((Nerve.Inc P).sub_mem (flagTriangle_mem_inc hc' hca) (flagTriangle_mem_inc ha' hca))

variable {κ ι : Type} {M : ℕ} [NeZero M]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)

end FiniteChains.Davis

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
open CategoryTheory
universe u
variable (P : Type u) [PartialOrder P]

/-- The project's actual weak edges are precisely Mathlib poset-nerve one-simplices. -/
def ordEdgeNerveEquiv : OrdEdge P ≃ ComposableArrows P 1 where
  toFun e := ComposableArrows.mk₁ (homOfLE e.2)
  invFun s := ⟨(s.obj 0, s.obj 1), s.monotone (by decide : (0 : Fin 2) ≤ 1)⟩
  left_inv e := Subtype.ext rfl
  right_inv s := by
    apply CategoryTheory.Functor.ext (fun i => by fin_cases i <;> rfl)

/-- The project's actual weak triangles are precisely Mathlib poset-nerve two-simplices. -/
def ordTriNerveEquiv : OrdTri P ≃ ComposableArrows P 2 where
  toFun t := ComposableArrows.mk₂ (homOfLE t.2.1) (homOfLE t.2.2)
  invFun s := ⟨(s.obj 0, s.obj 1, s.obj 2),
    s.monotone (by decide : (0 : Fin 3) ≤ 1),
    s.monotone (by decide : (1 : Fin 3) ≤ 2)⟩
  left_inv t := Subtype.ext rfl
  right_inv s := ComposableArrows.ext₂ rfl rfl rfl
    (Subsingleton.elim _ _) (Subsingleton.elim _ _)

/-- The project's actual weak tetrahedra are precisely Mathlib poset-nerve three-simplices. -/
def ordTetNerveEquiv : OrdTet P ≃ ComposableArrows P 3 where
  toFun t := ComposableArrows.mk₃ (homOfLE t.2.1) (homOfLE t.2.2.1) (homOfLE t.2.2.2)
  invFun s := ⟨(s.obj 0, s.obj 1, s.obj 2, s.obj 3),
    s.monotone (by decide : (0 : Fin 4) ≤ 1),
    s.monotone (by decide : (1 : Fin 4) ≤ 2),
    s.monotone (by decide : (2 : Fin 4) ≤ 3)⟩
  left_inv t := Subtype.ext rfl
  right_inv s := by
    apply CategoryTheory.Functor.ext (fun i => by fin_cases i <;> rfl)

/-- The actual alternating tetrahedron boundary is Mathlib's four nerve faces. -/
theorem ordTetBoundary_nerve_faces (t : OrdTet P) :
    Finsupp.mapDomain (ordTriNerveEquiv P) (ordTetBoundary t) =
      Finsupp.single ((nerve P).δ (0 : Fin 4) (ordTetNerveEquiv P t)) 1 -
      Finsupp.single ((nerve P).δ (1 : Fin 4) (ordTetNerveEquiv P t)) 1 +
      Finsupp.single ((nerve P).δ (2 : Fin 4) (ordTetNerveEquiv P t)) 1 -
      Finsupp.single ((nerve P).δ (3 : Fin 4) (ordTetNerveEquiv P t)) 1 := by
  change (Finsupp.lmapDomain ℤ ℤ (ordTriNerveEquiv P)) (ordTetBoundary t) = _
  simp only [ordTetBoundary, map_sub, map_add, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]
  have h0 : ordTriNerveEquiv P
      ⟨(t.1.2.1, t.1.2.2.1, t.1.2.2.2), t.2.2⟩ =
      (nerve P).δ 0 (ordTetNerveEquiv P t) := by
    apply CategoryTheory.Functor.ext (fun i => by fin_cases i <;> rfl)
  have h1 : ordTriNerveEquiv P
      ⟨(t.1.1, t.1.2.2.1, t.1.2.2.2), t.2.1.trans t.2.2.1, t.2.2.2⟩ =
      (nerve P).δ 1 (ordTetNerveEquiv P t) := by
    apply CategoryTheory.Functor.ext (fun i => by fin_cases i <;> rfl)
  have h2 : ordTriNerveEquiv P
      ⟨(t.1.1, t.1.2.1, t.1.2.2.2), t.2.1, t.2.2.1.trans t.2.2.2⟩ =
      (nerve P).δ 2 (ordTetNerveEquiv P t) := by
    apply CategoryTheory.Functor.ext (fun i => by fin_cases i <;> rfl)
  have h3 : ordTriNerveEquiv P
      ⟨(t.1.1, t.1.2.1, t.1.2.2.1), t.2.1, t.2.2.1⟩ =
      (nerve P).δ 3 (ordTetNerveEquiv P t) := by
    apply CategoryTheory.Functor.ext (fun i => by fin_cases i <;> rfl)
  rw [h0, h1, h2, h3]

/-- The actual two-cell boundary agrees with Mathlib's alternating nerve faces. -/
theorem ordTriangleBoundary_nerve_faces (t : OrdTri P) :
    Finsupp.mapDomain (ordEdgeNerveEquiv P)
      (bdry2 (orderCx P) (Finsupp.single t 1)) =
      Finsupp.single ((nerve P).δ (0 : Fin 3) (ordTriNerveEquiv P t)) 1 -
      Finsupp.single ((nerve P).δ (1 : Fin 3) (ordTriNerveEquiv P t)) 1 +
      Finsupp.single ((nerve P).δ (2 : Fin 3) (ordTriNerveEquiv P t)) 1 := by
  have h0 : ordEdgeNerveEquiv P ⟨(t.1.2.1, t.1.2.2), t.2.2⟩ =
      (nerve P).δ 0 (ordTriNerveEquiv P t) := by
    apply CategoryTheory.Functor.ext (fun i => by fin_cases i <;> rfl)
  have h1 : ordEdgeNerveEquiv P ⟨(t.1.1, t.1.2.2), t.2.1.trans t.2.2⟩ =
      (nerve P).δ 1 (ordTriNerveEquiv P t) := by
    apply CategoryTheory.Functor.ext (fun i => by fin_cases i <;> rfl)
  have h2 : ordEdgeNerveEquiv P ⟨(t.1.1, t.1.2.1), t.2.1⟩ =
      (nerve P).δ 2 (ordTriNerveEquiv P t) := by
    apply CategoryTheory.Functor.ext (fun i => by fin_cases i <;> rfl)
  have hb : bdry2 (orderCx P) (Finsupp.single t 1) =
      Finsupp.single ⟨(t.1.1, t.1.2.1), t.2.1⟩ 1 +
      Finsupp.single ⟨(t.1.2.1, t.1.2.2), t.2.2⟩ 1 -
      Finsupp.single ⟨(t.1.1, t.1.2.2), t.2.1.trans t.2.2⟩ 1 := by
    simp [bdry2, orderCx, pathChain]
    abel
  change (Finsupp.lmapDomain ℤ ℤ (ordEdgeNerveEquiv P))
    (bdry2 (orderCx P) (Finsupp.single t 1)) = _
  rw [hb, map_sub, map_add]
  simp only [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, h0, h1, h2]
  abel

end FiniteChains.Comb
end

namespace FiniteChains.Comb
open CategoryTheory Simplicial
universe u

/-- A bounded strictly increasing rank bounds the dimension of every actual
nondegenerate simplex of the poset nerve. -/
theorem orderNerve_nonDegenerate_dimension_le {P : Type u} [PartialOrder P]
    (rank : P → ℕ) (hrank : StrictMono rank) (d : ℕ) (hbound : ∀ p, rank p ≤ d)
    {n : ℕ} (s : (nerve P) _⦋n⦌) (hs : s ∈ (nerve P).nonDegenerate n) : n ≤ d := by
  have hstrict := hrank.comp ((PartialOrder.mem_nerve_nonDegenerate_iff_strictMono s).mp hs)
  let g : Fin (n + 1) → Fin (d + 1) := fun i => ⟨rank (s.obj i), Nat.lt_succ_of_le (hbound _)⟩
  have hg : Function.Injective g := by
    intro i j hij
    apply hstrict.injective
    exact congrArg Fin.val hij
  have hcard := Fintype.card_le_of_injective g hg
  simp_all

/-- The actual Mathlib nerve of a bounded ranked poset has the asserted dimension. -/
theorem orderNerve_hasDimensionLE {P : Type u} [PartialOrder P]
    (rank : P → ℕ) (hrank : StrictMono rank) (d : ℕ) (hbound : ∀ p, rank p ≤ d) :
    (nerve P).HasDimensionLE d := by
  constructor
  intro n hn
  apply Set.eq_univ_of_forall
  intro s
  rw [SSet.mem_degenerate_iff_notMem_nonDegenerate]
  intro hs
  have h := orderNerve_nonDegenerate_dimension_le rank hrank d hbound s hs
  omega

end FiniteChains.Comb

namespace FiniteChains.Comb.IsPosetCover
universe u
variable {P Q R : Type u} [PartialOrder P] [PartialOrder Q] [Preorder R]
  {f : P → Q} (hf : IsPosetCover f)

def lowerMapLift (a : R → P) (b : R → Q)
    (hab : ∀ x, b x ≤ f (a x)) (x : R) : P :=
  Classical.choose (hf.down (a x) (b x) (hab x))

omit [Preorder R] in
theorem lowerMapLift_spec (a : R → P) (b : R → Q)
    (hab : ∀ x, b x ≤ f (a x)) (x : R) :
    hf.lowerMapLift a b hab x ≤ a x ∧ f (hf.lowerMapLift a b hab x) = b x :=
  (Classical.choose_spec (hf.down (a x) (b x) (hab x))).1

theorem lowerMapLift_monotone (a : R → P) (b : R → Q)
    (ha : Monotone a) (hb : Monotone b) (hab : ∀ x, b x ≤ f (a x)) :
    Monotone (hf.lowerMapLift a b hab) := by
  intro x y hxy
  have hx := hf.lowerMapLift_spec a b hab x
  have hy := hf.lowerMapLift_spec a b hab y
  obtain ⟨c, hxc, hcy, hfc⟩ := hf.exists_interval_lift (hx.1.trans (ha hxy)) (b y)
    (hx.2 ▸ hb hxy) (hab y)
  have he := hf.down_inj hcy hy.1 (hfc.trans hy.2.symm)
  exact he ▸ hxc

def upperMapLift (a : R → P) (b : R → Q)
    (hab : ∀ x, f (a x) ≤ b x) (x : R) : P :=
  Classical.choose (hf.up (a x) (b x) (hab x))

omit [Preorder R] in
theorem upperMapLift_spec (a : R → P) (b : R → Q)
    (hab : ∀ x, f (a x) ≤ b x) (x : R) :
    a x ≤ hf.upperMapLift a b hab x ∧ f (hf.upperMapLift a b hab x) = b x :=
  (Classical.choose_spec (hf.up (a x) (b x) (hab x))).1

theorem upperMapLift_monotone (a : R → P) (b : R → Q)
    (ha : Monotone a) (hb : Monotone b) (hab : ∀ x, f (a x) ≤ b x) :
    Monotone (hf.upperMapLift a b hab) := by
  intro x y hxy
  have hx := hf.upperMapLift_spec a b hab x
  have hy := hf.upperMapLift_spec a b hab y
  obtain ⟨c, hxc, hcy, hfc⟩ := hf.exists_interval_lift ((ha hxy).trans hy.1) (b x)
    (hab x) (hy.2 ▸ hb hxy)
  have he := hf.up_inj hxc hx.1 (hfc.trans hx.2.symm)
  exact he ▸ hcy

/-- A constant endpoint lifts to a map constant on every comparability component. -/
theorem upperMapLift_constant_comparable (a : R → P) (ha : Monotone a)
    (b : Q) (hab : ∀ x, f (a x) ≤ b) {x y : R} (hxy : x ≤ y) :
    hf.upperMapLift a (fun _ => b) hab x = hf.upperMapLift a (fun _ => b) hab y := by
  have hx := hf.upperMapLift_spec a (fun _ => b) hab x
  have hy := hf.upperMapLift_spec a (fun _ => b) hab y
  exact hf.up_inj hx.1 ((ha hxy).trans hy.1) (hx.2.trans hy.2.symm)

include hf in
/-- Relabelling the base by an order isomorphism preserves actual interval lifting. -/
theorem postcomp_orderIso {S : Type u} [PartialOrder S] (e : Q ≃o S) :
    IsPosetCover (fun x => e (f x)) := by
  refine ⟨e.monotone.comp hf.mono, e.surjective.comp hf.surj, ?_, ?_⟩
  · intro a q h
    obtain ⟨b, hb, huniq⟩ := hf.up a (e.symm q) (by
      simpa using e.symm.monotone h)
    refine ⟨b, ⟨hb.1, by rw [hb.2, e.apply_symm_apply]⟩, ?_⟩
    intro c hc
    exact huniq c ⟨hc.1, by simpa using congrArg e.symm hc.2⟩
  · intro a q h
    obtain ⟨b, hb, huniq⟩ := hf.down a (e.symm q) (by
      simpa using e.symm.monotone h)
    refine ⟨b, ⟨hb.1, by rw [hb.2, e.apply_symm_apply]⟩, ?_⟩
    intro c hc
    exact huniq c ⟨hc.1, by simpa using congrArg e.symm hc.2⟩

end FiniteChains.Comb.IsPosetCover

namespace FiniteChains.Comb
universe u
variable {P Q R : Type u} [Preorder P] [Preorder Q] [Preorder R]

def PosetCoverPullback (f : P → Q) (g : R → Q) :=
  {x : P × R // f x.1 = g x.2}

instance (f : P → Q) (g : R → Q) : Preorder (PosetCoverPullback f g) :=
  Subtype.preorder _

instance {P Q R : Type u} [PartialOrder P] [Preorder Q] [PartialOrder R]
    (f : P → Q) (g : R → Q) : PartialOrder (PosetCoverPullback f g) :=
  Subtype.partialOrder _

def posetPullbackProjection (f : P → Q) (g : R → Q) (x : PosetCoverPullback f g) : R := x.1.2

def posetPullbackOriginal (f : P → Q) (g : R → Q) (x : PosetCoverPullback f g) : P := x.1.1

omit [Preorder Q] in
theorem posetPullbackProjection_monotone (f : P → Q) (g : R → Q) :
    Monotone (posetPullbackProjection f g) := fun _ _ h => h.2

omit [Preorder Q] in
theorem posetPullbackOriginal_monotone (f : P → Q) (g : R → Q) :
    Monotone (posetPullbackOriginal f g) := fun _ _ h => h.1

/-- No injectivity assumption on the map used to pull back the covering is needed. -/
theorem IsPosetCover.pullback {f : P → Q} (hf : IsPosetCover f)
    (g : R → Q) (hg : Monotone g) : IsPosetCover (posetPullbackProjection f g) := by
  refine ⟨posetPullbackProjection_monotone f g, ?_, ?_, ?_⟩
  · intro r
    obtain ⟨p, hp⟩ := hf.surj (g r)
    exact ⟨⟨(p, r), hp⟩, rfl⟩
  · intro a r h
    obtain ⟨b, hb, huniq⟩ := hf.up a.1.1 (g r) (a.2 ▸ hg h)
    refine ⟨⟨(b, r), hb.2⟩, ⟨⟨hb.1, h⟩, rfl⟩, ?_⟩
    intro c hc
    apply Subtype.ext
    exact Prod.ext (huniq c.1.1 ⟨hc.1.1, c.2.trans (congrArg g hc.2)⟩) hc.2
  · intro a r h
    obtain ⟨b, hb, huniq⟩ := hf.down a.1.1 (g r) (a.2 ▸ hg h)
    refine ⟨⟨(b, r), hb.2⟩, ⟨⟨hb.1, h⟩, rfl⟩, ?_⟩
    intro c hc
    apply Subtype.ext
    exact Prod.ext (huniq c.1.1 ⟨hc.1.1, c.2.trans (congrArg g hc.2)⟩) hc.2

end FiniteChains.Comb

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
open CategoryTheory
variable (P : Type) [PartialOrder P]

/-- Mathlib's free integral module simplicial object of the actual poset nerve. -/
def mathlibOrderNerveModule : SimplicialObject (ModuleCat ℤ) :=
  nerve P ⋙ ModuleCat.free ℤ

/-- The actual Mathlib alternating-face differential on a triangle agrees with
its actual cellular second boundary in order coordinates. -/
theorem mathlibOrderNerve_d2_single (t : OrdTri P) :
    (AlgebraicTopology.AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) 1).hom
      (Finsupp.single (ordTriNerveEquiv P t) 1) =
        Finsupp.mapDomain (ordEdgeNerveEquiv P)
          (bdry2 (orderCx P) (Finsupp.single t 1)) := by
  rw [ordTriangleBoundary_nerve_faces]
  simp [AlgebraicTopology.AlternatingFaceMapComplex.objD, mathlibOrderNerveModule,
    SimplicialObject.δ, Fin.sum_univ_succ, ModuleCat.free]
  abel

/-- The actual Mathlib alternating-face differential on a tetrahedron agrees
with its genuine order-nerve third boundary. -/
theorem mathlibOrderNerve_d3_single (t : OrdTet P) :
    (AlgebraicTopology.AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) 2).hom
      (Finsupp.single (ordTetNerveEquiv P t) 1) =
        Finsupp.mapDomain (ordTriNerveEquiv P) (ordTetBoundary t) := by
  rw [ordTetBoundary_nerve_faces]
  simp [AlgebraicTopology.AlternatingFaceMapComplex.objD, mathlibOrderNerveModule,
    SimplicialObject.δ, Fin.sum_univ_succ, ModuleCat.free]
  abel

/-- Actual finite two-chains satisfy the Mathlib/cellular boundary comparison. -/
theorem mathlibOrderNerve_d2 (c : OrdTri P →₀ ℤ) :
    (AlgebraicTopology.AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) 1).hom
      (Finsupp.mapDomain (ordTriNerveEquiv P) c) =
        Finsupp.mapDomain (ordEdgeNerveEquiv P) (bdry2 (orderCx P) c) := by
  change ((AlgebraicTopology.AlternatingFaceMapComplex.objD
    (mathlibOrderNerveModule P) 1).hom.comp
      (Finsupp.lmapDomain ℤ ℤ (ordTriNerveEquiv P))) c =
    ((Finsupp.lmapDomain ℤ ℤ (ordEdgeNerveEquiv P)).comp (bdry2 (orderCx P))) c
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd]
  | single t n =>
    have hn : Finsupp.single t n = n • Finsupp.single t 1 := by simp
    rw [hn, map_smul, map_smul]
    congr 1
    change (AlgebraicTopology.AlternatingFaceMapComplex.objD
      (mathlibOrderNerveModule P) 1).hom
      (Finsupp.mapDomain (ordTriNerveEquiv P) (Finsupp.single t 1)) = _
    rw [Finsupp.mapDomain_single]
    exact mathlibOrderNerve_d2_single P t

/-- Actual finite three-chains satisfy the Mathlib/order-nerve boundary comparison. -/
theorem mathlibOrderNerve_d3 (c : OrdTet P →₀ ℤ) :
    (AlgebraicTopology.AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) 2).hom
      (Finsupp.mapDomain (ordTetNerveEquiv P) c) =
        Finsupp.mapDomain (ordTriNerveEquiv P) (ordBoundary3 c) := by
  change ((AlgebraicTopology.AlternatingFaceMapComplex.objD
    (mathlibOrderNerveModule P) 2).hom.comp
      (Finsupp.lmapDomain ℤ ℤ (ordTetNerveEquiv P))) c =
    ((Finsupp.lmapDomain ℤ ℤ (ordTriNerveEquiv P)).comp ordBoundary3) c
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd]
  | single t n =>
    have hn : Finsupp.single t n = n • Finsupp.single t 1 := by simp
    rw [hn, map_smul, map_smul]
    congr 1
    change _ = Finsupp.mapDomain (ordTriNerveEquiv P)
      (ordBoundary3 (Finsupp.single t 1))
    rw [ordBoundary3, Finsupp.linearCombination_single, one_smul]
    change (AlgebraicTopology.AlternatingFaceMapComplex.objD
      (mathlibOrderNerveModule P) 2).hom
      (Finsupp.mapDomain (ordTetNerveEquiv P) (Finsupp.single t 1)) = _
    rw [Finsupp.mapDomain_single]
    exact mathlibOrderNerve_d3_single P t

end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory Simplicial Opposite
variable {P Q : Type} [PartialOrder P] [PartialOrder Q]

/-- The triangle dictionary commutes with the actual Mathlib nerve map. -/
theorem ordTriNerveEquiv_map (f : P → Q) (hf : Monotone f) (t : OrdTri P) :
    ordTriNerveEquiv Q ((orderCxMap f hf).onF t) =
      (nerveMap hf.functor).app (op ⦋2⦌) (ordTriNerveEquiv P t) := by
  apply CategoryTheory.Functor.ext (fun i => by fin_cases i <;> rfl)

/-- The tetrahedron dictionary commutes with the actual Mathlib nerve map. -/
theorem ordTetNerveEquiv_map (f : P → Q) (hf : Monotone f) (t : OrdTet P) :
    ordTetNerveEquiv Q (ordTetMap f hf t) =
      (nerveMap hf.functor).app (op ⦋3⦌) (ordTetNerveEquiv P t) := by
  apply CategoryTheory.Functor.ext (fun i => by fin_cases i <;> rfl)

/-- The actual Mathlib simplicial-module map induced by a monotone map. -/
def mathlibOrderNerveModuleMap (f : P → Q) (hf : Monotone f) :
    mathlibOrderNerveModule P ⟶ mathlibOrderNerveModule Q :=
  CategoryTheory.Functor.whiskerRight (nerveMap hf.functor) (ModuleCat.free ℤ)

/-- The actual Mathlib chain map induced by a monotone map. -/
def mathlibOrderNerveChainMap (f : P → Q) (hf : Monotone f) :
    AlgebraicTopology.AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P) ⟶
      AlgebraicTopology.AlternatingFaceMapComplex.obj (mathlibOrderNerveModule Q) :=
  AlgebraicTopology.AlternatingFaceMapComplex.map (mathlibOrderNerveModuleMap f hf)

/-- The actual cellular two-chain pushforward is the actual Mathlib chain map
under the proved order-simplex coordinates. -/
theorem mathlibOrderNerveChainMap_two (f : P → Q) (hf : Monotone f)
    (c : OrdTri P →₀ ℤ) :
    ((mathlibOrderNerveChainMap f hf).f 2).hom
      (Finsupp.mapDomain (ordTriNerveEquiv P) c) =
        Finsupp.mapDomain (ordTriNerveEquiv Q) (chain2 (orderCxMap f hf) c) := by
  change Finsupp.mapDomain ((nerveMap hf.functor).app (op ⦋2⦌))
    (Finsupp.mapDomain (ordTriNerveEquiv P) c) =
      Finsupp.mapDomain (ordTriNerveEquiv Q)
        (Finsupp.mapDomain (orderCxMap f hf).onF c)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro t _
  exact (ordTriNerveEquiv_map f hf t).symm

/-- The actual three-chain dictionary also commutes with the actual Mathlib chain map. -/
theorem mathlibOrderNerveChainMap_three (f : P → Q) (hf : Monotone f)
    (c : OrdTet P →₀ ℤ) :
    ((mathlibOrderNerveChainMap f hf).f 3).hom
      (Finsupp.mapDomain (ordTetNerveEquiv P) c) =
        Finsupp.mapDomain (ordTetNerveEquiv Q)
          (Finsupp.mapDomain (ordTetMap f hf) c) := by
  change Finsupp.mapDomain ((nerveMap hf.functor).app (op ⦋3⦌))
    (Finsupp.mapDomain (ordTetNerveEquiv P) c) =
      Finsupp.mapDomain (ordTetNerveEquiv Q)
        (Finsupp.mapDomain (ordTetMap f hf) c)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro t _
  exact (ordTetNerveEquiv_map f hf t).symm

end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory
variable (P : Type) [PartialOrder P]

/-- The actual Mathlib geometric realization of the actual poset nerve. -/
def orderNerveRealization : TopCat := SSet.toTop.obj (nerve P)

/-- The canonical actual map from the poset nerve to the singular set of its realization. -/
def orderNerveRealizationUnit :
    nerve P ⟶ TopCat.toSSet.obj (orderNerveRealization P) :=
  sSetTopAdj.unit.app (nerve P)

/-- Free integral chains on the actual singular simplicial set of the realization. -/
def orderNerveRealizationSingularModule : SimplicialObject (ModuleCat ℤ) :=
  TopCat.toSSet.obj (orderNerveRealization P) ⋙ ModuleCat.free ℤ

/-- The actual realization-unit chain map into the free singular chains. -/
def orderNerveRealizationChainComparison :
    AlgebraicTopology.AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P) ⟶
      AlgebraicTopology.AlternatingFaceMapComplex.obj
        (orderNerveRealizationSingularModule P) :=
  AlgebraicTopology.AlternatingFaceMapComplex.map
    (CategoryTheory.Functor.whiskerRight (orderNerveRealizationUnit P) (ModuleCat.free ℤ))

/-- The canonical comparison on actual categorical second homology. -/
def orderNerveRealizationH2Comparison :
    (AlgebraicTopology.AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).homology 2 ⟶
      (AlgebraicTopology.AlternatingFaceMapComplex.obj
        (orderNerveRealizationSingularModule P)).homology 2 :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 2).map
    (orderNerveRealizationChainComparison P)

variable {P} {Q : Type} [PartialOrder Q]

/-- The actual realized map induced by a monotone map of posets. -/
def orderNerveRealizationMap (f : P → Q) (hf : Monotone f) :
    orderNerveRealization P ⟶ orderNerveRealization Q :=
  SSet.toTop.map (nerveMap hf.functor)

/-- The canonical realization-unit comparison is natural under actual monotone maps. -/
theorem orderNerveRealizationUnit_natural (f : P → Q) (hf : Monotone f) :
    nerveMap hf.functor ≫ orderNerveRealizationUnit Q =
      orderNerveRealizationUnit P ≫ TopCat.toSSet.map (orderNerveRealizationMap f hf) :=
  sSetTopAdj.unit.naturality (nerveMap hf.functor)

/-- The actual chain map on the free singular chains induced by the realized map. -/
def orderNerveRealizationSingularChainMap (f : P → Q) (hf : Monotone f) :
    AlgebraicTopology.AlternatingFaceMapComplex.obj
      (orderNerveRealizationSingularModule P) ⟶
    AlgebraicTopology.AlternatingFaceMapComplex.obj
      (orderNerveRealizationSingularModule Q) :=
  AlgebraicTopology.AlternatingFaceMapComplex.map
    (CategoryTheory.Functor.whiskerRight
      (TopCat.toSSet.map (orderNerveRealizationMap f hf)) (ModuleCat.free ℤ))

/-- The actual realization comparison is natural on the actual chain complexes. -/
theorem orderNerveRealizationChainComparison_natural (f : P → Q) (hf : Monotone f) :
    mathlibOrderNerveChainMap f hf ≫ orderNerveRealizationChainComparison Q =
      orderNerveRealizationChainComparison P ≫ orderNerveRealizationSingularChainMap f hf := by
  change (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat ℤ)).map _ ≫
      (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat ℤ)).map _ =
    (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat ℤ)).map _ ≫
      (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat ℤ)).map _
  dsimp only [mathlibOrderNerveModuleMap]
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.whiskerRight_comp,
    ← CategoryTheory.Functor.whiskerRight_comp, orderNerveRealizationUnit_natural]

/-- Naturality also holds on actual categorical second homology. -/
theorem orderNerveRealizationH2Comparison_natural (f : P → Q) (hf : Monotone f) :
    (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 2).map
        (mathlibOrderNerveChainMap f hf) ≫ orderNerveRealizationH2Comparison Q =
      orderNerveRealizationH2Comparison P ≫
        (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 2).map
          (orderNerveRealizationSingularChainMap f hf) := by
  change (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 2).map _ ≫
      (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 2).map _ =
    (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 2).map _ ≫
      (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 2).map _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    orderNerveRealizationChainComparison_natural]

end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory

/-- The canonical continuous simplex in the actual geometric realization, obtained
by realizing the Yoneda map of a nerve simplex. -/
def orderNerveRealizationSimplex (P : Type) [PartialOrder P]
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n)) :
    SimplexCategory.toTop.obj n ⟶ orderNerveRealization P :=
  SSet.toTopSimplex.inv.app n ≫ SSet.toTop.map (SSet.yonedaEquiv.symm s)

/-- Realized simplex maps commute with actual monotone maps of posets. -/
theorem orderNerveRealizationSimplex_natural {P Q : Type} [PartialOrder P]
    [PartialOrder Q] (f : P → Q) (hf : Monotone f) {n : SimplexCategory}
    (s : (nerve P).obj (Opposite.op n)) :
    orderNerveRealizationSimplex P s ≫ orderNerveRealizationMap f hf =
      orderNerveRealizationSimplex Q ((nerveMap hf.functor).app _ s) := by
  unfold orderNerveRealizationSimplex orderNerveRealizationMap
  rw [Category.assoc, ← Functor.map_comp]
  congr 2

/-- Canonical realized simplices respect every simplex operator, including faces
and degeneracies. This is the attaching-map compatibility for the realization. -/
theorem orderNerveRealizationSimplex_operator (P : Type) [PartialOrder P]
    {m n : SimplexCategory} (a : m ⟶ n) (s : (nerve P).obj (Opposite.op n)) :
    SimplexCategory.toTop.map a ≫ orderNerveRealizationSimplex P s =
      orderNerveRealizationSimplex P ((nerve P).map a.op s) := by
  unfold orderNerveRealizationSimplex
  rw [← Category.assoc, SSet.toTopSimplex.inv.naturality a, Category.assoc,
    Functor.comp_map, ← Functor.map_comp]
  congr 2

/-- Every point of the actual realization lies in a canonical realized simplex. -/
theorem orderNerveRealizationSimplex_jointly_surjective (P : Type) [PartialOrder P]
    (x : orderNerveRealization P) :
    ∃ (n : SimplexCategory) (s : (nerve P).obj (Opposite.op n))
      (z : SimplexCategory.toTop.obj n), orderNerveRealizationSimplex P s z = x := by
  letI := sSetTopAdj.leftAdjoint_preservesColimits
  have hc := CategoryTheory.Limits.isColimitOfPreserves SSet.toTop
    (CategoryTheory.Presheaf.colimitOfRepresentable (nerve P))
  have ht := CategoryTheory.Limits.isColimitOfPreserves (CategoryTheory.forget TopCat) hc
  obtain ⟨j, y, hy⟩ := CategoryTheory.Limits.Types.jointly_surjective_of_isColimit ht x
  refine ⟨j.unop.1.unop, j.unop.2, SSet.toTopSimplex.hom.app _ y, ?_⟩
  change SSet.toTop.map (SSet.yonedaEquiv.symm j.unop.2)
      (SSet.toTopSimplex.inv.app _ (SSet.toTopSimplex.hom.app _ y)) = x
  have hi := congrArg (fun k => k y) (SSet.toTopSimplex.hom_inv_id_app j.unop.1.unop)
  change SSet.toTopSimplex.inv.app j.unop.1.unop
    (SSet.toTopSimplex.hom.app j.unop.1.unop y) = y at hi
  rw [hi]
  exact hy

/-- Continuity on the actual realization is detected by its canonical continuous simplices. -/
theorem orderNerveRealization_continuous_iff (P : Type) [PartialOrder P]
    {X : Type*} [TopologicalSpace X] (f : orderNerveRealization P → X) :
    Continuous f ↔ ∀ (n : SimplexCategory) (s : (nerve P).obj (Opposite.op n)),
      Continuous (f ∘ orderNerveRealizationSimplex P s) := by
  constructor
  · intro h n s
    exact h.comp (orderNerveRealizationSimplex P s).hom.continuous
  · intro h
    letI := sSetTopAdj.leftAdjoint_preservesColimits
    have hc := CategoryTheory.Limits.isColimitOfPreserves SSet.toTop
      (CategoryTheory.Presheaf.colimitOfRepresentable (nerve P))
    apply (TopCat.continuous_iff_of_isColimit _ hc f).mpr
    intro j
    have hj := (h j.unop.1.unop j.unop.2).comp
      (SSet.toTopSimplex.hom.app j.unop.1.unop).hom.continuous
    convert hj using 1
    all_goals try rfl
    funext y
    change f (SSet.toTop.map (SSet.yonedaEquiv.symm j.unop.2) y) =
      f (SSet.toTop.map (SSet.yonedaEquiv.symm j.unop.2)
        (SSet.toTopSimplex.inv.app j.unop.1.unop
          (SSet.toTopSimplex.hom.app j.unop.1.unop y)))
    have hi := congrArg (fun k => k y) (SSet.toTopSimplex.hom_inv_id_app j.unop.1.unop)
    change SSet.toTopSimplex.inv.app j.unop.1.unop
      (SSet.toTopSimplex.hom.app j.unop.1.unop y) = y at hi
    rw [hi]

/-- The actual realization has the weak topology defined by its canonical simplices. -/
theorem orderNerveRealization_isOpen_iff (P : Type) [PartialOrder P]
    (U : Set (orderNerveRealization P)) :
    IsOpen U ↔ ∀ (n : SimplexCategory) (s : (nerve P).obj (Opposite.op n)),
      IsOpen (orderNerveRealizationSimplex P s ⁻¹' U) := by
  constructor
  · intro h n s
    exact h.preimage (orderNerveRealizationSimplex P s).hom.continuous
  · intro h
    letI := sSetTopAdj.leftAdjoint_preservesColimits
    have hc := CategoryTheory.Limits.isColimitOfPreserves SSet.toTop
      (CategoryTheory.Presheaf.colimitOfRepresentable (nerve P))
    apply (TopCat.isOpen_iff_of_isColimit _ hc U).mpr
    intro j
    have hj := (h j.unop.1.unop j.unop.2).preimage
      (SSet.toTopSimplex.hom.app j.unop.1.unop).hom.continuous
    convert hj using 1
    all_goals try rfl
    ext y
    change SSet.toTop.map (SSet.yonedaEquiv.symm j.unop.2) y ∈ U ↔
      SSet.toTop.map (SSet.yonedaEquiv.symm j.unop.2)
        (SSet.toTopSimplex.inv.app j.unop.1.unop
          (SSet.toTopSimplex.hom.app j.unop.1.unop y)) ∈ U
    have hi := congrArg (fun k => k y) (SSet.toTopSimplex.hom_inv_id_app j.unop.1.unop)
    change SSet.toTopSimplex.inv.app j.unop.1.unop
      (SSet.toTopSimplex.hom.app j.unop.1.unop y) = y at hi
    rw [hi]

/-- Closedness on the actual realization is detected simplex by simplex. -/
theorem orderNerveRealization_isClosed_iff (P : Type) [PartialOrder P]
    (U : Set (orderNerveRealization P)) :
    IsClosed U ↔ ∀ (n : SimplexCategory) (s : (nerve P).obj (Opposite.op n)),
      IsClosed (orderNerveRealizationSimplex P s ⁻¹' U) := by
  simpa using
    orderNerveRealization_isOpen_iff P Uᶜ

end FiniteChains.Comb
end

namespace FiniteChains.Comb
open CategoryTheory Simplicial

/-- Nondegenerate simplices alone cover the actual geometric realization. -/
theorem orderNerveRealization_nonDegenerate_jointly_surjective (P : Type) [PartialOrder P]
    (x : orderNerveRealization P) :
    ∃ (n : ℕ) (s : (nerve P).nonDegenerate n)
      (z : SimplexCategory.toTop.obj ⦋n⦌), orderNerveRealizationSimplex P s.val z = x := by
  obtain ⟨n, s, z, hz⟩ := orderNerveRealizationSimplex_jointly_surjective P x
  induction n using SimplexCategory.rec with | _ n =>
    obtain ⟨m, a, _, t, ht⟩ := (nerve P).exists_nonDegenerate s
    refine ⟨m, t, SimplexCategory.toTop.map a z, ?_⟩
    have h := congrArg (fun k => k z) (orderNerveRealizationSimplex_operator P a t.val)
    rw [← ht] at h
    exact h.trans hz

end FiniteChains.Comb

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
open CategoryTheory
open scoped Classical

/-- Affine interpolation of vertex values on a genuine topological nerve simplex. -/
def orderNerveAffineSimplex {P : Type} [PartialOrder P] (v : P → ℝ)
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n)) :
    C(SimplexCategory.toTop.obj n, ℝ) where
  toFun z := ∑ i, z.down.weights i * v (s.obj i)
  continuous_toFun := by fun_prop

/-- Affine interpolation respects every actual topological simplex operator. -/
theorem orderNerveAffineSimplex_operator {P : Type} [PartialOrder P] (v : P → ℝ)
    {m n : SimplexCategory} (a : m ⟶ n) (s : (nerve P).obj (Opposite.op n))
    (z : SimplexCategory.toTop.obj m) :
    orderNerveAffineSimplex v s (SimplexCategory.toTop.map a z) =
      orderNerveAffineSimplex v ((nerve P).map a.op s) z := by
  change (∑ j, (Finsupp.mapDomain a.toOrderHom z.down.weights) j * v (s.obj j)) =
    ∑ i, z.down.weights i * v (s.obj (a.toOrderHom i))
  have hw : (fun j => (Finsupp.mapDomain a.toOrderHom z.down.weights) j) =
      FunOnFinite.linearMap ℝ ℝ a.toOrderHom z.down.weights := by
    funext j
    simp [FunOnFinite.linearMap_apply_apply, Finsupp.mapDomain_apply, Finsupp.sum_fintype,
      Finsupp.single_apply, Finset.sum_filter, eq_comm]
  change (∑ j, (fun j => (Finsupp.mapDomain a.toOrderHom z.down.weights) j) j * v (s.obj j)) = _
  rw [hw]
  simp only [FunOnFinite.linearMap_apply_apply, Finset.sum_mul]
  have h := Finset.sum_fiberwise Finset.univ a.toOrderHom
    (fun i => z.down.weights i * v (s.obj (a.toOrderHom i)))
  convert h using 1
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i hi
  have ha : a.toOrderHom i = j := (Finset.mem_filter.mp hi).2
  rw [ha]

/-- The compatible affine functions form an actual cocone on the realized
representable-simplex diagram. -/
def orderNerveAffineCocone {P : Type} [PartialOrder P] (v : P → ℝ) :
    CategoryTheory.Limits.Cocone (Presheaf.functorToRepresentables (nerve P) ⋙ SSet.toTop) where
  pt := TopCat.of ℝ
  ι :=
    { app := fun j => SSet.toTopSimplex.hom.app j.unop.1.unop ≫
        TopCat.ofHom (orderNerveAffineSimplex v j.unop.2)
      naturality := by
        intro j k a
        apply TopCat.hom_ext
        ext z
        have hn := congrArg (fun f => f z)
          (SSet.toTopSimplex.hom.naturality a.unop.1.unop)
        change SSet.toTopSimplex.hom.app k.unop.1.unop
            (SSet.toTop.map (SSet.stdSimplex.map a.unop.1.unop) z) =
          SimplexCategory.toTop.map a.unop.1.unop
            (SSet.toTopSimplex.hom.app j.unop.1.unop z) at hn
        change orderNerveAffineSimplex v k.unop.2
            (SSet.toTopSimplex.hom.app k.unop.1.unop
              (SSet.toTop.map (SSet.stdSimplex.map a.unop.1.unop) z)) =
          orderNerveAffineSimplex v j.unop.2 (SSet.toTopSimplex.hom.app j.unop.1.unop z)
        rw [hn, orderNerveAffineSimplex_operator]
        congr 1
        exact congrArg (orderNerveAffineSimplex v) a.unop.2 }

/-- Continuous affine interpolation of arbitrary vertex values on the actual realization. -/
def orderNerveAffineRealization {P : Type} [PartialOrder P] (v : P → ℝ) :
    orderNerveRealization P ⟶ TopCat.of ℝ := by
  letI := sSetTopAdj.leftAdjoint_preservesColimits
  exact (CategoryTheory.Limits.isColimitOfPreserves SSet.toTop
    (Presheaf.colimitOfRepresentable (nerve P))).desc (orderNerveAffineCocone v)

/-- The global affine function has the prescribed formula on each canonical simplex. -/
theorem orderNerveAffineRealization_simplex {P : Type} [PartialOrder P] (v : P → ℝ)
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n)) :
    orderNerveRealizationSimplex P s ≫ orderNerveAffineRealization v =
      TopCat.ofHom (orderNerveAffineSimplex v s) := by
  letI := sSetTopAdj.leftAdjoint_preservesColimits
  have h := (CategoryTheory.Limits.isColimitOfPreserves SSet.toTop
    (Presheaf.colimitOfRepresentable (nerve P))).fac (orderNerveAffineCocone v)
      (Opposite.op (Functor.elementsMk (nerve P) (Opposite.op n) s))
  change SSet.toTop.map (SSet.yonedaEquiv.symm s) ≫ orderNerveAffineRealization v =
    SSet.toTopSimplex.hom.app n ≫ TopCat.ofHom (orderNerveAffineSimplex v s) at h
  unfold orderNerveRealizationSimplex
  simp_all

/-- A vertex indicator recovers each barycentric coordinate of a nondegenerate simplex. -/
theorem orderNerveAffineSimplex_indicator {P : Type} [PartialOrder P]
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n))
    (hs : Function.Injective s.obj) (i : Fin (n.len + 1))
    (z : SimplexCategory.toTop.obj n) :
    orderNerveAffineSimplex (fun p => if p = s.obj i then 1 else 0) s z = z.down.weights i := by
  simp [orderNerveAffineSimplex, hs.eq_iff]

/-- Every simplex with distinct vertices is injectively realized, including its boundary. -/
theorem orderNerveRealizationSimplex_injective {P : Type} [PartialOrder P]
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n))
    (hs : Function.Injective s.obj) : Function.Injective (orderNerveRealizationSimplex P s) := by
  intro z w h
  apply ULift.ext
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro i
  let v : P → ℝ := fun p => if p = s.obj i then 1 else 0
  have hf := congrArg (orderNerveAffineRealization v) h
  have hc := congrArg (fun k => k z) (orderNerveAffineRealization_simplex v s)
  have hd := congrArg (fun k => k w) (orderNerveAffineRealization_simplex v s)
  change orderNerveAffineRealization v (orderNerveRealizationSimplex P s z) =
    orderNerveAffineSimplex v s z at hc
  change orderNerveAffineRealization v (orderNerveRealizationSimplex P s w) =
    orderNerveAffineSimplex v s w at hd
  rw [hc, hd] at hf
  exact (orderNerveAffineSimplex_indicator s hs i z).symm.trans
    (hf.trans (orderNerveAffineSimplex_indicator s hs i w))

end FiniteChains.Comb
end

namespace FiniteChains.Comb
open CategoryTheory
open scoped Classical

/-- At a simplex point with positive barycentric coordinates, a vertex indicator
has positive value precisely on the vertices of that simplex. -/
theorem orderNerveAffineSimplex_indicator_pos_iff {P : Type} [PartialOrder P]
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n))
    (z : SimplexCategory.toTop.obj n) (hz : ∀ i, 0 < z.down.weights i) (p : P) :
    0 < orderNerveAffineSimplex (fun q => if q = p then 1 else 0) s z ↔
      p ∈ Set.range s.obj := by
  constructor
  · intro h
    by_contra hp
    have hn : ∀ i, s.obj i ≠ p := fun i hi => hp ⟨i, hi⟩
    simp [orderNerveAffineSimplex, hn] at h
  · rintro ⟨i, rfl⟩
    have hsum := Finset.single_le_sum
      (f := fun j => z.down.weights j * (if s.obj j = s.obj i then 1 else 0))
      (fun j _ => mul_nonneg (le_of_lt (hz j)) (by split_ifs <;> norm_num))
      (Finset.mem_univ i)
    have hi : z.down.weights i ≤ ∑ j, z.down.weights j * (if s.obj j = s.obj i then 1 else 0) := by
      simpa using hsum
    exact (hz i).trans_le hi

/-- Two actual simplex interiors meeting in the realization have the same vertex set. -/
theorem orderNerveRealizationSimplex_interior_range_eq {P : Type} [PartialOrder P]
    {n m : SimplexCategory} (s : (nerve P).obj (Opposite.op n))
    (t : (nerve P).obj (Opposite.op m))
    (z : SimplexCategory.toTop.obj n) (w : SimplexCategory.toTop.obj m)
    (hz : ∀ i, 0 < z.down.weights i) (hw : ∀ i, 0 < w.down.weights i)
    (h : orderNerveRealizationSimplex P s z = orderNerveRealizationSimplex P t w) :
    Set.range s.obj = Set.range t.obj := by
  ext p
  let v : P → ℝ := fun q => if q = p then 1 else 0
  have hf := congrArg (orderNerveAffineRealization v) h
  have hc := congrArg (fun k => k z) (orderNerveAffineRealization_simplex v s)
  have hd := congrArg (fun k => k w) (orderNerveAffineRealization_simplex v t)
  change orderNerveAffineRealization v (orderNerveRealizationSimplex P s z) =
    orderNerveAffineSimplex v s z at hc
  change orderNerveAffineRealization v (orderNerveRealizationSimplex P t w) =
    orderNerveAffineSimplex v t w at hd
  rw [hc, hd] at hf
  rw [← orderNerveAffineSimplex_indicator_pos_iff s z hz p,
    ← orderNerveAffineSimplex_indicator_pos_iff t w hw p]
  exact congrArg (fun r : ℝ => 0 < r) hf ▸ Iff.rfl

/-- Nondegenerate simplices in the same dimension with meeting interiors are equal. -/
theorem orderNerveRealization_nonDegenerate_interior_eq {P : Type} [PartialOrder P]
    {n : ℕ} (s t : (nerve P).nonDegenerate n)
    (z w : SimplexCategory.toTop.obj (SimplexCategory.mk n))
    (hz : ∀ i, 0 < z.down.weights i) (hw : ∀ i, 0 < w.down.weights i)
    (h : orderNerveRealizationSimplex P s.val z = orderNerveRealizationSimplex P t.val w) :
    s = t := by
  have hrange := orderNerveRealizationSimplex_interior_range_eq s.val t.val z w hz hw h
  have hs := (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono s.val).mp s.property
  have ht := (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono t.val).mp t.property
  have he := (hs.range_inj ht).mp hrange
  apply Subtype.ext
  exact CategoryTheory.Functor.ext (fun i => congrFun he i)

/-- Nondegenerate simplex interiors in different dimensions cannot meet. -/
theorem orderNerveRealization_nonDegenerate_interior_dimension_eq {P : Type}
    [PartialOrder P] {n m : ℕ} (s : (nerve P).nonDegenerate n)
    (t : (nerve P).nonDegenerate m)
    (z : SimplexCategory.toTop.obj (SimplexCategory.mk n))
    (w : SimplexCategory.toTop.obj (SimplexCategory.mk m))
    (hz : ∀ i, 0 < z.down.weights i) (hw : ∀ i, 0 < w.down.weights i)
    (h : orderNerveRealizationSimplex P s.val z = orderNerveRealizationSimplex P t.val w) :
    n = m := by
  have hrange := orderNerveRealizationSimplex_interior_range_eq s.val t.val z w hz hw h
  have hs := (PartialOrder.mem_nerve_nonDegenerate_iff_injective s.val).mp s.property
  have ht := (PartialOrder.mem_nerve_nonDegenerate_iff_injective t.val).mp t.property
  have hc := Nat.card_congr ((Equiv.ofInjective s.val.obj hs).trans
    ((Set.equivOfEq hrange).trans (Equiv.ofInjective t.val.obj ht).symm))
  simp_all

end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory Simplicial

/-- A standard-simplex point with a zero coordinate comes from the corresponding face. -/
theorem topologicalSimplex_zero_coordinate_face {n : ℕ}
    (z : SimplexCategory.toTop.obj ⦋n + 1⦌) (i : Fin (n + 2))
    (hi : z.down.weights i = 0) :
    ∃ w : SimplexCategory.toTop.obj ⦋n⦌, SimplexCategory.toTop.map (SimplexCategory.δ i) w = z := by
  let zold := TopologicalSingular.simplexCoordinates (n + 1) z.down
  have hiold : zold.val i = 0 := hi
  let w : stdSimplex ℝ (Fin (n + 1)) :=
    ⟨fun j => zold.val (i.succAbove j), fun j => zold.property.1 _, by
      have hs := zold.property.2
      rw [Fin.sum_univ_succAbove (fun j : Fin (n + 2) => zold.val j) i,
        hiold, zero_add] at hs
      exact hs⟩
  refine ⟨ULift.up ((TopologicalSingular.simplexCoordinates n).symm w), ?_⟩
  apply ULift.ext
  apply (TopologicalSingular.simplexCoordinates (n + 1)).injective
  change TopologicalSingular.simplexCoordinates (n + 1)
    (Convexity.StdSimplex.map i.succAbove ((TopologicalSingular.simplexCoordinates n).symm w)) = zold
  rw [TopologicalSingular.simplexCoordinates_map, Homeomorph.apply_symm_apply]
  apply Subtype.ext
  funext k
  change (FunOnFinite.linearMap ℝ ℝ i.succAbove w.val) k = zold.val k
  rw [FunOnFinite.linearMap_apply_apply]
  by_cases hk : k = i
  · simp_all
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
    simp [w, Finset.sum_filter]

/-- Every point on a nondegenerate simplex belongs to the interior of a
nondegenerate face of no larger dimension. -/
theorem orderNerveRealizationSimplex_interior_representative (P : Type) [PartialOrder P]
    (n : ℕ) (s : (nerve P).nonDegenerate n) (z : SimplexCategory.toTop.obj ⦋n⦌) :
    ∃ (m : ℕ) (_ : m ≤ n) (t : (nerve P).nonDegenerate m)
      (w : SimplexCategory.toTop.obj ⦋m⦌),
      (∀ i, 0 < w.down.weights i) ∧
        orderNerveRealizationSimplex P t.val w = orderNerveRealizationSimplex P s.val z := by
  induction n with
  | zero =>
    refine ⟨0, le_rfl, s, z, ?_, rfl⟩
    intro i
    haveI : Subsingleton (Fin (⦋0⦌.len + 1)) := by
      simpa using (inferInstance : Subsingleton (Fin 1))
    have h := z.down.total_of_fintype
    change (∑ j : Fin 1, z.down.weights j) = 1 at h
    simp only [Fintype.sum_unique] at h
    have he  :=
      (congrArg z.down.weights (Subsingleton.elim i default)).trans h
    rw [he]
    norm_num
  | succ n ih =>
    by_cases hz : ∀ i, 0 < z.down.weights i
    · grind
    · push_neg at hz
      obtain ⟨i, hi⟩ := hz
      have hi0  := le_antisymm hi (z.down.weights_nonneg i)
      obtain ⟨w, hw⟩ := topologicalSimplex_zero_coordinate_face z i hi0
      have hs := (PartialOrder.mem_nerve_nonDegenerate_iff_injective s.val).mp s.property
      have ht : (nerve P).map (SimplexCategory.δ i).op s.val ∈
          (nerve P).nonDegenerate n := by
        rw [PartialOrder.mem_nerve_nonDegenerate_iff_injective]
        change Function.Injective (fun j => s.val.obj (i.succAbove j))
        exact hs.comp Fin.succAbove_right_injective
      obtain ⟨m, hm, t, u, hu, he⟩ := ih ⟨_, ht⟩ w
      refine ⟨m, hm.trans (Nat.le_succ n), t, u, hu, he.trans ?_⟩
      have h := congrArg (fun k => k w)
        (orderNerveRealizationSimplex_operator P (SimplexCategory.δ i) s.val)
      change orderNerveRealizationSimplex P s.val
        (SimplexCategory.toTop.map (SimplexCategory.δ i) w) = _ at h
      rw [hw] at h
      exact h.symm

/-- Every actual realization point lies in an actual nondegenerate simplex interior. -/
theorem orderNerveRealization_interior_cover (P : Type) [PartialOrder P]
    (x : orderNerveRealization P) :
    ∃ (n : ℕ) (s : (nerve P).nonDegenerate n)
      (z : SimplexCategory.toTop.obj ⦋n⦌),
      (∀ i, 0 < z.down.weights i) ∧ orderNerveRealizationSimplex P s.val z = x := by
  obtain ⟨n, s, z, hz⟩ := orderNerveRealization_nonDegenerate_jointly_surjective P x
  obtain ⟨m, _, t, w, hw, he⟩ := orderNerveRealizationSimplex_interior_representative P n s z
  grind

/-- Every boundary point of an actual simplex is represented in one of its finitely
many codimension-one faces. -/
theorem orderNerveRealizationSimplex_boundary_face {P : Type} [PartialOrder P]
    {n : ℕ} (s : (nerve P).obj (Opposite.op ⦋n + 1⦌))
    (z : SimplexCategory.toTop.obj ⦋n + 1⦌) (hz : ¬ ∀ i, 0 < z.down.weights i) :
    ∃ (i : Fin (n + 2)) (w : SimplexCategory.toTop.obj ⦋n⦌),
      orderNerveRealizationSimplex P ((nerve P).map (SimplexCategory.δ i).op s) w =
        orderNerveRealizationSimplex P s z := by
  push_neg at hz
  obtain ⟨i, hi⟩ := hz
  have hi0  := le_antisymm hi (z.down.weights_nonneg i)
  obtain ⟨w, hw⟩ := topologicalSimplex_zero_coordinate_face z i hi0
  refine ⟨i, w, ?_⟩
  have h := congrArg (fun k => k w)
    (orderNerveRealizationSimplex_operator P (SimplexCategory.δ i) s)
  change orderNerveRealizationSimplex P s
    (SimplexCategory.toTop.map (SimplexCategory.δ i) w) = _ at h
  rw [hw] at h
  exact h.symm

/-- Every face of an actual nondegenerate poset-nerve simplex remains nondegenerate. -/
theorem orderNerve_nonDegenerate_face {P : Type} [PartialOrder P]
    {n : ℕ} (s : (nerve P).nonDegenerate (n + 1)) (i : Fin (n + 2)) :
    (nerve P).map (SimplexCategory.δ i).op s.val ∈ (nerve P).nonDegenerate n := by
  rw [PartialOrder.mem_nerve_nonDegenerate_iff_injective]
  exact ((PartialOrder.mem_nerve_nonDegenerate_iff_injective s.val).mp s.property).comp
    Fin.succAbove_right_injective

/-- The boundary of every nondegenerate simplex maps into a finite family of
actual lower-dimensional closed simplex images. -/
theorem orderNerveRealizationSimplex_boundary_finite_faces {P : Type} [PartialOrder P]
    {n : ℕ} (s : (nerve P).nonDegenerate (n + 1)) :
    ∃ I : Finset ((nerve P).nonDegenerate n),
      ∀ z : SimplexCategory.toTop.obj ⦋n + 1⦌,
        (¬ ∀ i, 0 < z.down.weights i) →
        ∃ t ∈ I, ∃ w : SimplexCategory.toTop.obj ⦋n⦌,
          orderNerveRealizationSimplex P t.val w = orderNerveRealizationSimplex P s.val z := by
  classical
  let face : Fin (n + 2) → (nerve P).nonDegenerate n := fun i =>
    ⟨(nerve P).map (SimplexCategory.δ i).op s.val, orderNerve_nonDegenerate_face s i⟩
  refine ⟨Finset.univ.image face, ?_⟩
  intro z hz
  obtain ⟨i, w, hw⟩ := orderNerveRealizationSimplex_boundary_face s.val z hz
  exact ⟨face i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, w, hw⟩

end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory
open scoped Classical

/-- The actual global barycentric-coordinate map of the poset-nerve realization. -/
def orderNerveRealizationCoordinates (P : Type) [PartialOrder P] :
    C(orderNerveRealization P, P → ℝ) where
  toFun x p := orderNerveAffineRealization (fun q => if q = p then 1 else 0) x
  continuous_toFun := continuous_pi (fun p =>
    (orderNerveAffineRealization (fun q => if q = p then 1 else 0)).hom.continuous)

/-- Global barycentric coordinates separate all points of the actual realization. -/
theorem orderNerveRealizationCoordinates_injective (P : Type) [PartialOrder P] :
    Function.Injective (orderNerveRealizationCoordinates P) := by
  intro x y h
  obtain ⟨n, s, z, hz, hx⟩ := orderNerveRealization_interior_cover P x
  obtain ⟨m, t, w, hw, hy⟩ := orderNerveRealization_interior_cover P y
  have hv : ∀ p, orderNerveAffineSimplex (fun q => if q = p then 1 else 0) s.val z =
      orderNerveAffineSimplex (fun q => if q = p then 1 else 0) t.val w := by
    intro p
    have hc := congrArg (fun k => k z)
      (orderNerveAffineRealization_simplex (fun q => if q = p then 1 else 0) s.val)
    have hd := congrArg (fun k => k w)
      (orderNerveAffineRealization_simplex (fun q => if q = p then 1 else 0) t.val)
    change orderNerveAffineRealization (fun q => if q = p then 1 else 0)
      (orderNerveRealizationSimplex P s.val z) = _ at hc
    change orderNerveAffineRealization (fun q => if q = p then 1 else 0)
      (orderNerveRealizationSimplex P t.val w) = _ at hd
    rw [hx] at hc
    rw [hy] at hd
    exact hc.symm.trans ((congrFun h p).trans hd)
  have hrange : Set.range s.val.obj = Set.range t.val.obj := by
    ext p
    rw [← orderNerveAffineSimplex_indicator_pos_iff s.val z hz p,
      ← orderNerveAffineSimplex_indicator_pos_iff t.val w hw p, hv p]
  have hs := (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono s.val).mp s.property
  have ht := (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono t.val).mp t.property
  have hc := Nat.card_congr ((Equiv.ofInjective s.val.obj hs.injective).trans
    ((Set.equivOfEq hrange).trans (Equiv.ofInjective t.val.obj ht.injective).symm))
  simp at hc
  have hnm : n = m := by omega
  subst m
  have hst : s = t := by
    apply Subtype.ext
    exact CategoryTheory.Functor.ext (fun i => congrFun ((hs.range_inj ht).mp hrange) i)
  subst t
  have hzw : z = w := by
    apply ULift.ext
    apply Convexity.StdSimplex.ext
    apply Finsupp.ext
    intro i
    exact (orderNerveAffineSimplex_indicator s.val hs.injective i z).symm.trans
      ((hv (s.val.obj i)).trans (orderNerveAffineSimplex_indicator s.val hs.injective i w))
  exact hx.symm.trans ((congrArg (orderNerveRealizationSimplex P s.val) hzw).trans hy)

/-- The actual geometric realization of every poset nerve is Hausdorff. -/
instance orderNerveRealization_t2Space (P : Type) [PartialOrder P] :
    T2Space (orderNerveRealization P) :=
  T2Space.of_injective_continuous (orderNerveRealizationCoordinates_injective P)
    (orderNerveRealizationCoordinates P).continuous

/-- Nondegenerate realization simplices are closed embeddings of their compact domains. -/
theorem orderNerveRealization_nonDegenerate_isClosedEmbedding {P : Type} [PartialOrder P]
    {n : ℕ} (s : (nerve P).nonDegenerate n) :
    Topology.IsClosedEmbedding (orderNerveRealizationSimplex P s.val) := by
  haveI : CompactSpace (SimplexCategory.toTop.obj (SimplexCategory.mk n)) :=
    inferInstanceAs (CompactSpace (ULift.{0} (Convexity.StdSimplex ℝ (Fin (n + 1)))))
  exact (orderNerveRealizationSimplex P s.val).hom.continuous.isClosedEmbedding
    (orderNerveRealizationSimplex_injective s.val
      ((PartialOrder.mem_nerve_nonDegenerate_iff_injective s.val).mp s.property))

end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory Simplicial

/-- Closedness is detected by nondegenerate simplex preimages alone. -/
theorem orderNerveRealization_nonDegenerate_isClosed_iff (P : Type) [PartialOrder P]
    (A : Set (orderNerveRealization P)) :
    IsClosed A ↔ ∀ (n : ℕ) (s : (nerve P).nonDegenerate n),
      IsClosed (orderNerveRealizationSimplex P s.val ⁻¹' A) := by
  constructor
  · intro h n s
    exact h.preimage (orderNerveRealizationSimplex P s.val).hom.continuous
  · intro h
    apply (orderNerveRealization_isClosed_iff P A).mpr
    intro n s
    induction n using SimplexCategory.rec with | _ n =>
      obtain ⟨m, a, _, t, ht⟩ := (nerve P).exists_nonDegenerate s
      have hc := (h m t).preimage (SimplexCategory.toTop.map a).hom.continuous
      convert hc using 1
      ext z
      have ha := congrArg (fun k => k z) (orderNerveRealizationSimplex_operator P a t.val)
      rw [← ht] at ha
      exact iff_of_eq (congrArg (fun x => x ∈ A) ha.symm)

/-- The actual realization has weak topology with respect to its nondegenerate
closed simplex images, in the form required by the CW constructor. -/
theorem orderNerveRealization_isClosed_iff_inter_simplex_range (P : Type) [PartialOrder P]
    (A : Set (orderNerveRealization P)) :
    IsClosed A ↔ ∀ (n : ℕ) (s : (nerve P).nonDegenerate n),
      IsClosed (A ∩ Set.range (orderNerveRealizationSimplex P s.val)) := by
  constructor
  · intro h n s
    exact h.inter (orderNerveRealization_nonDegenerate_isClosedEmbedding s).isClosed_range
  · intro h
    apply (orderNerveRealization_nonDegenerate_isClosed_iff P A).mpr
    intro n s
    have hc := (h n s).preimage (orderNerveRealizationSimplex P s.val).hom.continuous
    convert hc using 1
    ext z
    simp only [Set.mem_preimage, Set.mem_inter_iff]
    exact ⟨fun hz => ⟨hz, ⟨z, rfl⟩⟩, fun hz => hz.1⟩

end FiniteChains.Comb

namespace FiniteChains
/-- The standard simplex in its actual dimension, obtained by omitting the first barycentric coordinate. -/
def reducedSimplex (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}
/-- Reinsert the first barycentric coordinate into reduced simplex coordinates. -/
def reducedSimplexToStandard (n : ℕ) (x : reducedSimplex n) :
    stdSimplex ℝ (Fin (n + 1)) :=
  ⟨Fin.cons (1 - ∑ i, x.val i) x.val,
    (by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using sub_nonneg.mpr x.property.2
      · simpa using x.property.1 j),
    (by simp [Fin.sum_univ_succ])⟩
/-- Omit the first barycentric coordinate. -/
def standardSimplexToReduced (n : ℕ) (z : stdSimplex ℝ (Fin (n + 1))) :
    reducedSimplex n :=
  ⟨fun i => z.val i.succ, (fun i => z.property.1 i.succ), by
    have hs := z.property.2
    rw [Fin.sum_univ_succ] at hs
    have h0 := z.property.1 0
    change z.val 0 + ∑ i : Fin n, z.val i.succ = 1 at hs
    linarith⟩
/-- The actual standard simplex is homeomorphic to the reduced-coordinate simplex. -/
def reducedSimplexHomeomorph (n : ℕ) :
    reducedSimplex n ≃ₜ stdSimplex ℝ (Fin (n + 1)) where
  toFun := reducedSimplexToStandard n
  invFun := standardSimplexToReduced n
  left_inv x := rfl
  right_inv z := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · have hs := z.property.2
      rw [Fin.sum_univ_succ] at hs
      change 1 - ∑ j : Fin n, z.val j.succ = z.val 0
      linarith
    · rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · fun_prop
    · fun_prop
  continuous_invFun := by
    exact Continuous.subtype_mk (continuous_pi (fun i =>
      (continuous_apply i.succ).comp continuous_subtype_val)) _
/-- The reduced simplex is closed in its ambient finite-dimensional space. -/
theorem reducedSimplex_isClosed (n : ℕ) : IsClosed (reducedSimplex n) := by
  change IsClosed ({x : Fin n → ℝ | ∀ i, 0 ≤ x i} ∩ {x | ∑ i, x i ≤ 1})
  apply IsClosed.inter
  · simp only [Set.setOf_forall]
    exact isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))
  · exact isClosed_le (continuous_finset_sum _ (fun i _ => continuous_apply i)) continuous_const
/-- The reduced simplex is convex. -/
theorem reducedSimplex_convex (n : ℕ) : Convex ℝ (reducedSimplex n) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · change (∑ i : Fin n, (a * x i + b * y i)) ≤ 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hax := mul_le_mul_of_nonneg_left hx.2 ha
    have hby := mul_le_mul_of_nonneg_left hy.2 hb
    nlinarith
/-- The reduced simplex is compact. -/
theorem reducedSimplex_isCompact (n : ℕ) : IsCompact (reducedSimplex n) := by
  letI : CompactSpace (reducedSimplex n) := (reducedSimplexHomeomorph n).symm.compactSpace
  exact isCompact_iff_compactSpace.mpr inferInstance
/-- The reduced simplex is bounded. -/
theorem reducedSimplex_isBounded (n : ℕ) : Bornology.IsBounded (reducedSimplex n) :=
  (reducedSimplex_isCompact n).isBounded
/-- Strict reduced-coordinate inequalities define the simplex interior candidate. -/
def reducedSimplexPositive (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 < x i) ∧ ∑ i, x i < 1}
 theorem reducedSimplexPositive_isOpen (n : ℕ) : IsOpen (reducedSimplexPositive n) := by
  change IsOpen ({x : Fin n → ℝ | ∀ i, 0 < x i} ∩ {x | ∑ i, x i < 1})
  apply IsOpen.inter
  · simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (continuous_apply i))
  · exact isOpen_lt (continuous_finset_sum _ (fun i _ => continuous_apply i)) continuous_const
 theorem reducedSimplexPositive_subset (n : ℕ) : reducedSimplexPositive n ⊆ reducedSimplex n :=
  fun _ hx => ⟨fun i => le_of_lt (hx.1 i), le_of_lt hx.2⟩
/-- The reduced simplex has nonempty interior, including dimension zero. -/
theorem reducedSimplex_interior_nonempty (n : ℕ) : (interior (reducedSimplex n)).Nonempty := by
  let c  := 1 / ((n : ℝ) + 1)
  have hc : 0 < c := by dsimp [c]; positivity
  have hsum : (∑ _ : Fin n, c) < 1 := by
    simp
    dsimp [c]
    rw [mul_one_div]
    exact (div_lt_one (by positivity)).mpr (by linarith)
  have hx : (fun _ : Fin n => c) ∈ reducedSimplexPositive n := ⟨fun _ => hc, hsum⟩
  exact ⟨_, (interior_maximal (reducedSimplexPositive_subset n)
    (reducedSimplexPositive_isOpen n)) hx⟩
/-- A genuine ambient homeomorphism takes the reduced simplex to the closed unit ball,
its interior to the open unit ball and its frontier to the unit sphere. -/
theorem reducedSimplex_exists_ball_homeomorph (n : ℕ) :
    ∃ h : (Fin n → ℝ) ≃ₜ (Fin n → ℝ),
      h '' interior (reducedSimplex n) = Metric.ball 0 1 ∧
      h '' reducedSimplex n = Metric.closedBall 0 1 ∧
      h '' frontier (reducedSimplex n) = Metric.sphere 0 1 := by
  obtain ⟨h, hi, hc, hf⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (reducedSimplex_convex n) (reducedSimplex_interior_nonempty n) (reducedSimplex_isBounded n)
  rw [(reducedSimplex_isClosed n).closure_eq] at hc
  grind
/-- The strict-coordinate description is exactly the reduced simplex interior. -/
theorem reducedSimplex_interior_eq (n : ℕ) :
    interior (reducedSimplex n) = reducedSimplexPositive n := by
  apply Set.Subset.antisymm
  · intro x hx
    constructor
    · intro i
      have hi := interior_mono (show reducedSimplex n ⊆
          (Function.eval i) ⁻¹' Set.Ici 0 from fun _ h => h.1 i) hx
      have ht := (isOpenMap_eval i).interior_preimage_subset_preimage_interior hi
      simpa using ht
    · cases n with
      | zero => simp
      | succ n =>
        let L : (Fin (n + 1) → ℝ) →L[ℝ] ℝ :=
          { toFun := fun y => ∑ i, y i
            map_add' := by intro y z; simp [Finset.sum_add_distrib]
            map_smul' := by intro a y; simp [Finset.mul_sum]
            cont := continuous_finset_sum _ (fun i _ => continuous_apply i) }
        have hs : Function.Surjective L := by
          intro r
          refine ⟨Pi.single 0 r, ?_⟩
          simp [L, Pi.single_apply, Finset.sum_ite_eq']
        have hi := interior_mono (show reducedSimplex (n + 1) ⊆
            L ⁻¹' Set.Iic 1 from fun _ h => h.2) hx
        have ht := (L.isOpenMap hs).interior_preimage_subset_preimage_interior hi
        have ht' : L x < 1 := by simpa using ht
        exact ht'
  · exact interior_maximal (reducedSimplexPositive_subset n) (reducedSimplexPositive_isOpen n)
/-- Reinserted barycentric coordinates are all positive exactly on the reduced simplex interior. -/
theorem reducedSimplexToStandard_positive_iff (n : ℕ) (x : reducedSimplex n) :
    (∀ i, 0 < (reducedSimplexToStandard n x).val i) ↔ x.val ∈ interior (reducedSimplex n) := by
  rw [reducedSimplex_interior_eq]
  change (∀ i : Fin (n + 1), 0 < (Fin.cons (1 - (∑ j : Fin n, x.val j)) x.val : Fin (n + 1) → ℝ) i) ↔
    (∀ j, 0 < x.val j) ∧ ∑ j, x.val j < 1
  constructor
  · intro h
    constructor
    · intro j
      simpa using h j.succ
    · have h0 := h 0
      simp at h0
      linarith
  · rintro ⟨hp, hs⟩ i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using sub_pos.mpr hs
    · simpa using hp j
/-- The actual ambient homeomorphism furnished by the proved convex-simplex parametrization. -/
def reducedSimplexBallAmbient (n : ℕ) : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) :=
  (reducedSimplex_exists_ball_homeomorph n).choose
 theorem reducedSimplexBallAmbient_properties (n : ℕ) :
    reducedSimplexBallAmbient n '' interior (reducedSimplex n) = Metric.ball 0 1 ∧
    reducedSimplexBallAmbient n '' reducedSimplex n = Metric.closedBall 0 1 ∧
    reducedSimplexBallAmbient n '' frontier (reducedSimplex n) = Metric.sphere 0 1 :=
  (reducedSimplex_exists_ball_homeomorph n).choose_spec
/-- The standard simplex, in every dimension, is homeomorphic to the closed unit ball. -/
def standardSimplexClosedBallHomeomorph (n : ℕ) :
    stdSimplex ℝ (Fin (n + 1)) ≃ₜ (Metric.closedBall 0 1 : Set (Fin n → ℝ)) :=
  (reducedSimplexHomeomorph n).symm.trans
    (((reducedSimplexBallAmbient n).image (reducedSimplex n)).trans
      (Homeomorph.setCongr (reducedSimplexBallAmbient_properties n).2.1))
 theorem standardSimplexClosedBallHomeomorph_val (n : ℕ)
    (z : stdSimplex ℝ (Fin (n + 1))) :
    (standardSimplexClosedBallHomeomorph n z).val =
      reducedSimplexBallAmbient n (standardSimplexToReduced n z).val := rfl
/-- Positive barycentric coordinates correspond exactly to the open unit ball. -/
theorem standardSimplexClosedBallHomeomorph_positive_iff (n : ℕ)
    (z : stdSimplex ℝ (Fin (n + 1))) :
    (∀ i, 0 < z.val i) ↔ (standardSimplexClosedBallHomeomorph n z).val ∈ Metric.ball 0 1 := by
  have hz := (reducedSimplexHomeomorph n).apply_symm_apply z
  have hp := reducedSimplexToStandard_positive_iff n (standardSimplexToReduced n z)
  change (∀ i, 0 < (reducedSimplexHomeomorph n
      ((reducedSimplexHomeomorph n).symm z)).val i) ↔ _ at hp
  rw [hz] at hp
  rw [hp, standardSimplexClosedBallHomeomorph_val,
    ← (reducedSimplexBallAmbient_properties n).1]
  simp only [Set.mem_image, (reducedSimplexBallAmbient n).injective.eq_iff]
  exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨_, h, he⟩ => he ▸ h⟩
end FiniteChains

namespace FiniteChains.Comb
open CategoryTheory Simplicial

def orderNerveSimplexClosedBallHomeomorph (n : ℕ) :
    Convexity.StdSimplex ℝ (Fin (n + 1)) ≃ₜ (Metric.closedBall 0 1 : Set (Fin n → ℝ)) :=
  (TopologicalSingular.simplexCoordinates n).trans (standardSimplexClosedBallHomeomorph n)

theorem orderNerveSimplexClosedBallHomeomorph_positive_iff (n : ℕ)
    (z : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    (∀ i, 0 < z.weights i) ↔ (orderNerveSimplexClosedBallHomeomorph n z).val ∈ Metric.ball 0 1 := by
  exact standardSimplexClosedBallHomeomorph_positive_iff n
    (TopologicalSingular.simplexCoordinates n z)

/-- A genuine continuous closed-ball characteristic chart in the actual realization. -/
def orderNerveClosedBallChart {P : Type} [PartialOrder P]
    {n : ℕ} (s : (nerve P).nonDegenerate n) :
    C((Metric.closedBall 0 1 : Set (Fin n → ℝ)), orderNerveRealization P) where
  toFun x := orderNerveRealizationSimplex P s.val
    (ULift.up ((orderNerveSimplexClosedBallHomeomorph n).symm x))
  continuous_toFun := (orderNerveRealizationSimplex P s.val).hom.continuous.comp
    (continuous_uliftUp.comp (orderNerveSimplexClosedBallHomeomorph n).symm.continuous)

/-- Closed-ball and canonical simplex charts have exactly the same actual image. -/
theorem orderNerveClosedBallChart_range {P : Type} [PartialOrder P]
    {n : ℕ} (s : (nerve P).nonDegenerate n) :
    Set.range (orderNerveClosedBallChart s) = Set.range (orderNerveRealizationSimplex P s.val) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨z, rfl⟩
    refine ⟨orderNerveSimplexClosedBallHomeomorph n z.down, ?_⟩
    change orderNerveRealizationSimplex P s.val
      (ULift.up ((orderNerveSimplexClosedBallHomeomorph n).symm
        (orderNerveSimplexClosedBallHomeomorph n z.down))) = _
    rw [Homeomorph.symm_apply_apply]
    rfl

/-- The closed-ball chart is injective. -/
theorem orderNerveClosedBallChart_injective {P : Type} [PartialOrder P]
    {n : ℕ} (s : (nerve P).nonDegenerate n) : Function.Injective (orderNerveClosedBallChart s) :=
  (orderNerveRealizationSimplex_injective s.val
    ((PartialOrder.mem_nerve_nonDegenerate_iff_injective s.val).mp s.property)).comp
      (ULift.up_injective.comp (orderNerveSimplexClosedBallHomeomorph n).symm.injective)

end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory Simplicial
open scoped Classical

/-- Extend the genuine closed-ball chart to an ambient function, using its centre
value outside the closed ball. Only its closed-ball restriction is characteristic data. -/
def orderNerveCharacteristicFunction {P : Type} [PartialOrder P]
    {n : ℕ} (s : (nerve P).nonDegenerate n) (x : Fin n → ℝ) : orderNerveRealization P :=
  if hx : x ∈ Metric.closedBall 0 1 then orderNerveClosedBallChart s ⟨x, hx⟩
  else orderNerveClosedBallChart s ⟨0, Metric.mem_closedBall_self (by norm_num)⟩

 theorem orderNerveCharacteristicFunction_closedBall {P : Type} [PartialOrder P]
    {n : ℕ} (s : (nerve P).nonDegenerate n) (x : (Metric.closedBall 0 1 : Set (Fin n → ℝ))) :
    orderNerveCharacteristicFunction s x.val = orderNerveClosedBallChart s x := by
  simp [orderNerveCharacteristicFunction, x.property]

 theorem orderNerveCharacteristicFunction_continuousOn {P : Type} [PartialOrder P]
    {n : ℕ} (s : (nerve P).nonDegenerate n) :
    ContinuousOn (orderNerveCharacteristicFunction s) (Metric.closedBall 0 1) := by
  apply continuousOn_iff_continuous_restrict.mpr
  have h : (Metric.closedBall 0 1 : Set (Fin n → ℝ)).domRestrict
      (orderNerveCharacteristicFunction s) = orderNerveClosedBallChart s := by
    funext x
    exact orderNerveCharacteristicFunction_closedBall s x
  rw (config := { transparency := .default }) [h]
  exact (orderNerveClosedBallChart s).continuous

 theorem orderNerveCharacteristicFunction_injOn {P : Type} [PartialOrder P]
    {n : ℕ} (s : (nerve P).nonDegenerate n) :
    Set.InjOn (orderNerveCharacteristicFunction s) (Metric.ball 0 1) := by
  intro x hx y hy h
  have hx' := Metric.ball_subset_closedBall hx
  have hy' := Metric.ball_subset_closedBall hy
  have hc : orderNerveClosedBallChart s ⟨x, hx'⟩ = orderNerveClosedBallChart s ⟨y, hy'⟩ := by
    simpa only [orderNerveCharacteristicFunction_closedBall s ⟨x, hx'⟩,
      orderNerveCharacteristicFunction_closedBall s ⟨y, hy'⟩] using h
  exact congrArg Subtype.val (orderNerveClosedBallChart_injective s hc)

/-- The genuine realization characteristic map as a PartialEquiv with open-ball source. -/
def orderNerveCharacteristicMap {P : Type} [PartialOrder P]
    {n : ℕ} (s : (nerve P).nonDegenerate n) : PartialEquiv (Fin n → ℝ) (orderNerveRealization P) :=
  (orderNerveCharacteristicFunction_injOn s).toPartialEquiv
    (orderNerveCharacteristicFunction s) (Metric.ball 0 1)

 theorem orderNerveCharacteristicMap_source {P : Type} [PartialOrder P]
    {n : ℕ} (s : (nerve P).nonDegenerate n) :
    (orderNerveCharacteristicMap s).source = Metric.ball 0 1 := rfl

 theorem orderNerveCharacteristicMap_continuousOn {P : Type} [PartialOrder P]
    {n : ℕ} (s : (nerve P).nonDegenerate n) :
    ContinuousOn (orderNerveCharacteristicMap s) (Metric.closedBall 0 1) :=
  orderNerveCharacteristicFunction_continuousOn s

/-- The inverse characteristic map is continuous on its actual open-cell target. -/
theorem orderNerveCharacteristicMap_continuousOn_symm {P : Type} [PartialOrder P]
    {n : ℕ} (s : (nerve P).nonDegenerate n) :
    ContinuousOn (orderNerveCharacteristicMap s).symm (orderNerveCharacteristicMap s).target := by
  let e := orderNerveCharacteristicMap s
  let g : e.target → (Metric.closedBall 0 1 : Set (Fin n → ℝ)) := fun x =>
    ⟨e.symm x.val, Metric.ball_subset_closedBall (by
      have h := e.map_target x.property
      change e.symm x.val ∈ Metric.ball 0 1 at h
      exact h)⟩
  have hc  :=
    ((orderNerveClosedBallChart s).continuous.isClosedEmbedding
      (orderNerveClosedBallChart_injective s)).isEmbedding
  have hg : Continuous g := by
    apply hc.isInducing.continuous_iff.mpr
    have he : orderNerveClosedBallChart s ∘ g = Subtype.val := by
      funext x
      have h := orderNerveCharacteristicFunction_closedBall s (g x)
      exact h.symm.trans (e.right_inv x.property)
    erw [he]
    exact continuous_subtype_val
  apply continuousOn_iff_continuous_restrict.mpr
  exact continuous_subtype_val.comp hg

end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory Simplicial

/-- Closed characteristic cells are precisely the canonical simplex images. -/
theorem orderNerveCharacteristicMap_closedCell {P : Type} [PartialOrder P]
    {n : ℕ} (s : (nerve P).nonDegenerate n) :
    orderNerveCharacteristicMap s '' Metric.closedBall 0 1 =
      Set.range (orderNerveRealizationSimplex P s.val) := by
  rw [← orderNerveClosedBallChart_range s]
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨u, hu⟩, (orderNerveCharacteristicFunction_closedBall s ⟨u, hu⟩).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u.val, u.property, orderNerveCharacteristicFunction_closedBall s u⟩

/-- The open characteristic cell consists exactly of the positive-coordinate simplex points. -/
theorem orderNerveCharacteristicMap_openCell {P : Type} [PartialOrder P]
    {n : ℕ} (s : (nerve P).nonDegenerate n) :
    orderNerveCharacteristicMap s '' Metric.ball 0 1 =
      {x | ∃ z : SimplexCategory.toTop.obj ⦋n⦌,
        (∀ i, 0 < z.down.weights i) ∧ orderNerveRealizationSimplex P s.val z = x} := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hc := Metric.ball_subset_closedBall hu
    let v : (Metric.closedBall 0 1 : Set (Fin n → ℝ)) := ⟨u, hc⟩
    let z := (orderNerveSimplexClosedBallHomeomorph n).symm v
    refine ⟨ULift.up z, ?_, ?_⟩
    · apply (orderNerveSimplexClosedBallHomeomorph_positive_iff n z).mpr
      rw [Homeomorph.apply_symm_apply]
      exact hu
    · exact (orderNerveCharacteristicFunction_closedBall s v).symm
  · rintro ⟨z, hz, rfl⟩
    let u := orderNerveSimplexClosedBallHomeomorph n z.down
    have hu  :=
      (orderNerveSimplexClosedBallHomeomorph_positive_iff n z.down).mp hz
    refine ⟨u.val, hu, ?_⟩
    rw [show orderNerveCharacteristicMap s u.val = orderNerveClosedBallChart s u from
      orderNerveCharacteristicFunction_closedBall s u]
    change orderNerveRealizationSimplex P s.val
      (ULift.up ((orderNerveSimplexClosedBallHomeomorph n).symm
        (orderNerveSimplexClosedBallHomeomorph n z.down))) = _
    rw [Homeomorph.symm_apply_apply]
    rfl

/-- The actual characteristic open cells are pairwise disjoint in all dimensions. -/
theorem orderNerveCharacteristicMap_pairwiseDisjoint (P : Type) [PartialOrder P] :
    (Set.univ : Set (Σ n, (nerve P).nonDegenerate n)).PairwiseDisjoint
      (fun a => orderNerveCharacteristicMap a.2 '' Metric.ball 0 1) := by
  intro a _ b _ hab
  apply Set.disjoint_left.mpr
  intro x hxa hxb
  rcases a with ⟨n, s⟩
  rcases b with ⟨m, t⟩
  dsimp only at hxa hxb
  rw [orderNerveCharacteristicMap_openCell] at hxa hxb
  obtain ⟨z, hz, hx⟩ := hxa
  obtain ⟨w, hw, hy⟩ := hxb
  have he := hx.trans hy.symm
  have hnm := orderNerveRealization_nonDegenerate_interior_dimension_eq s t z w hz hw he
  subst m
  have hst := orderNerveRealization_nonDegenerate_interior_eq s t z w hz hw he
  subst t
  exact hab rfl

/-- The actual closed characteristic cells cover the entire realization. -/
theorem orderNerveCharacteristicMap_union (P : Type) [PartialOrder P] :
    (⋃ (n : ℕ) (s : (nerve P).nonDegenerate n),
      orderNerveCharacteristicMap s '' Metric.closedBall 0 1) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨n, s, z, hz⟩ := orderNerveRealization_nonDegenerate_jointly_surjective P x
  apply Set.mem_iUnion.mpr
  refine ⟨n, Set.mem_iUnion.mpr ⟨s, ?_⟩⟩
  rw [orderNerveCharacteristicMap_closedCell]
  exact ⟨z, hz⟩

/-- The characteristic closed cells give the weak topology of the actual realization. -/
theorem orderNerveCharacteristicMap_isClosed (P : Type) [PartialOrder P]
    (A : Set (orderNerveRealization P))
    (h : ∀ n (s : (nerve P).nonDegenerate n),
      IsClosed (A ∩ orderNerveCharacteristicMap s '' Metric.closedBall 0 1)) : IsClosed A := by
  apply (orderNerveRealization_isClosed_iff_inter_simplex_range P A).mpr
  intro n s
  simpa only [orderNerveCharacteristicMap_closedCell] using h n s

/-- Characteristic sphere boundaries lie in finitely many codimension-one closed cells. -/
theorem orderNerveCharacteristicMap_boundary {P : Type} [PartialOrder P]
    {n : ℕ} (s : (nerve P).nonDegenerate (n + 1)) :
    ∃ I : Finset ((nerve P).nonDegenerate n),
      ∀ x ∈ Metric.sphere (0 : Fin (n + 1) → ℝ) 1,
        ∃ t ∈ I, orderNerveCharacteristicMap s x ∈
          orderNerveCharacteristicMap t '' Metric.closedBall 0 1 := by
  obtain ⟨I, hI⟩ := orderNerveRealizationSimplex_boundary_finite_faces s
  refine ⟨I, ?_⟩
  intro x hx
  have hxc  := Metric.sphere_subset_closedBall hx
  let u : (Metric.closedBall 0 1 : Set (Fin (n + 1) → ℝ)) := ⟨x, hxc⟩
  let z := (orderNerveSimplexClosedBallHomeomorph (n + 1)).symm u
  have hz : ¬ ∀ i, 0 < z.weights i := by
    intro hp
    have hb := (orderNerveSimplexClosedBallHomeomorph_positive_iff (n + 1) z).mp hp
    rw [Homeomorph.apply_symm_apply] at hb
    have he := Metric.mem_sphere.mp hx
    have hl := Metric.mem_ball.mp hb
    rw [he] at hl
    exact (lt_irrefl _ hl)
  obtain ⟨t, ht, w, hw⟩ := hI (ULift.up z) hz
  refine ⟨t, ht, ?_⟩
  rw [orderNerveCharacteristicMap_closedCell]
  refine ⟨w, ?_⟩
  exact hw.trans (orderNerveCharacteristicFunction_closedBall s u).symm

end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical

/-- The actual Mathlib realization of a poset nerve has the genuine CW structure
whose cells are its actual nondegenerate simplices. -/
instance orderNerveRealization_cwComplex (P : Type) [PartialOrder P] :
    CWComplex (Set.univ : Set (orderNerveRealization P)) where
  cell n := (nerve P).nonDegenerate n
  map _ s := orderNerveCharacteristicMap s
  source_eq _ s := orderNerveCharacteristicMap_source s
  continuousOn _ s := orderNerveCharacteristicMap_continuousOn s
  continuousOn_symm _ s := orderNerveCharacteristicMap_continuousOn_symm s
  pairwiseDisjoint' := orderNerveCharacteristicMap_pairwiseDisjoint P
  mapsTo' := by
    intro n s
    cases n with
    | zero =>
      refine ⟨fun _ => ∅, ?_⟩
      intro x hx
      have hx0 : x = 0 := Subsingleton.elim _ _
      have he := Metric.mem_sphere.mp hx
      rw [hx0, dist_self] at he
      norm_num at he
    | succ n =>
      obtain ⟨I, hI⟩ := orderNerveCharacteristicMap_boundary s
      let J : ∀ m, Finset ((nerve P).nonDegenerate m) := fun m =>
        if h : m = n then h.symm ▸ I else ∅
      refine ⟨J, ?_⟩
      intro x hx
      obtain ⟨t, ht, hcell⟩ := hI x hx
      simp only [Set.mem_iUnion]
      refine ⟨n, Nat.lt_succ_self n, t, ?_, hcell⟩
      simpa only [J, dif_pos rfl] using ht
  closed' A _ h := orderNerveCharacteristicMap_isClosed P A h
  union' := orderNerveCharacteristicMap_union P

/-- The actual CW realization has no cells above the proved simplicial dimension. -/
theorem orderNerveRealization_cell_isEmpty (P : Type) [PartialOrder P]
    (d : ℕ) [(nerve P).HasDimensionLE d] (n : ℕ) (hn : d < n) :
    IsEmpty (RelCWComplex.cell (Set.univ : Set (orderNerveRealization P)) n) := by
  constructor
  intro s
  exact (not_le_of_gt hn) ((nerve P).dim_le_of_nonDegenerate s d)

end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory Simplicial

/-- The canonical actual realization point of a poset vertex. -/
def orderNerveRealizationVertex {P : Type} [PartialOrder P] (p : P) :
    orderNerveRealization P :=
  orderNerveRealizationSimplex P (n := ⦋0⦌) (ComposableArrows.mk₀ p) default

/-- Every vertex of a simplex belongs to its actual canonical image. -/
theorem orderNerveRealizationVertex_mem_simplex {P : Type} [PartialOrder P]
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n)) (i : Fin (n.len + 1)) :
    ∃ z : SimplexCategory.toTop.obj n,
      orderNerveRealizationSimplex P s z = orderNerveRealizationVertex (s.obj i) := by
  let a : ⦋0⦌ ⟶ n := SimplexCategory.mkHom (OrderHom.const _ i)
  refine ⟨SimplexCategory.toTop.map a default, ?_⟩
  have h := congrArg (fun k => k default) (orderNerveRealizationSimplex_operator P a s)
  have hs : (nerve P).map a.op s = ComposableArrows.mk₀ (s.obj i) := by
    exact CategoryTheory.Functor.ext (fun _ => rfl)
  rw [hs] at h
  exact h

/-- Every actual simplex point is joined by a continuous path to each of its vertices. -/
theorem orderNerveRealizationSimplex_joined_vertex {P : Type} [PartialOrder P]
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n))
    (z : SimplexCategory.toTop.obj n) (i : Fin (n.len + 1)) :
    Joined (orderNerveRealizationSimplex P s z) (orderNerveRealizationVertex (s.obj i)) := by
  obtain ⟨w, hw⟩ := orderNerveRealizationVertex_mem_simplex s i
  have h : Joined (orderNerveRealizationSimplex P s z) (orderNerveRealizationSimplex P s w) :=
    ⟨(PathConnectedSpace.joined z w).somePath.map
      (orderNerveRealizationSimplex P s).hom.continuous⟩
  simp_all

/-- Comparable poset vertices are joined in the actual realization. -/
theorem orderNerveRealizationVertex_joined_of_le {P : Type} [PartialOrder P]
    {p q : P} (h : p ≤ q) : Joined (orderNerveRealizationVertex p) (orderNerveRealizationVertex q) := by
  let s := ComposableArrows.mk₁ (homOfLE h)
  let z : SimplexCategory.toTop.obj ⦋1⦌ := Classical.choice inferInstance
  have hp := orderNerveRealizationSimplex_joined_vertex s z 0
  have hq := orderNerveRealizationSimplex_joined_vertex s z 1
  exact hp.symm.trans hq

/-- Actual realization vertices joined by a combinatorial edge path are topologically joined. -/
theorem orderNerveRealizationVertex_joined_of_isPath {P : Type} [PartialOrder P]
    {a b : P} {p : List (OrdEdge P × Bool)}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a b) :
    Joined (orderNerveRealizationVertex a) (orderNerveRealizationVertex b) := by
  induction p generalizing a with
  | nil =>
    subst b
    exact Joined.refl _
  | cons e p ih =>
    rcases hp with ⟨rfl, hp⟩
    have he : Joined
        (orderNerveRealizationVertex (P := P) (germSrc (orderCx P).src (orderCx P).tgt e))
        (orderNerveRealizationVertex (germTgt (orderCx P).src (orderCx P).tgt e)) := by
      rcases e with ⟨e, o⟩
      cases o
      · exact (orderNerveRealizationVertex_joined_of_le e.property).symm
      · exact orderNerveRealizationVertex_joined_of_le e.property
    exact he.trans (ih hp)

/-- A nonempty combinatorially connected poset has path-connected actual realization. -/
theorem orderNerveRealization_pathConnectedSpace (P : Type) [PartialOrder P] [Nonempty P]
    (hP : IsConnected (orderCx P)) : PathConnectedSpace (orderNerveRealization P) where
  nonempty := ⟨orderNerveRealizationVertex (Classical.choice (inferInstance : Nonempty P))⟩
  joined x y := by
    obtain ⟨n, s, z, hx⟩ := orderNerveRealizationSimplex_jointly_surjective P x
    obtain ⟨m, t, w, hy⟩ := orderNerveRealizationSimplex_jointly_surjective P y
    have hs := orderNerveRealizationSimplex_joined_vertex s z (0 : Fin (n.len + 1))
    have ht := orderNerveRealizationSimplex_joined_vertex t w (0 : Fin (m.len + 1))
    rw [hx] at hs
    rw [hy] at ht
    obtain ⟨p, hp⟩ := hP (s.obj 0) (t.obj 0)
    exact hs.trans ((orderNerveRealizationVertex_joined_of_isPath hp).trans ht.symm)

end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory Topology

/-- The actual realized poset nerve, with its proved topology, CW structure,
connectedness and dimension, is a genuine two-complex of the submission statement. -/
def orderNerveTwoComplex (P : Type) [PartialOrder P] [Nonempty P]
    [(nerve P).HasDimensionLE 2] (hP : IsConnected (orderCx P)) : Whitehead.TwoComplex := by
  letI : PathConnectedSpace (orderNerveRealization P) := orderNerveRealization_pathConnectedSpace P hP
  exact
    { space := orderNerveRealization P
      topology := inferInstance
      hausdorff := inferInstance
      cw := inferInstance
      connected := inferInstance
      dimension := fun n hn => orderNerveRealization_cell_isEmpty P 2 n hn }

end FiniteChains.Comb

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical

/-- Points of the actual realization whose barycentric coordinates vanish outside a vertex subset. -/
def orderNerveRealizationSupported (P : Type) [PartialOrder P] (A : Set P) :
    Set (orderNerveRealization P) :=
  {x | ∀ p, p ∉ A → orderNerveRealizationCoordinates P x p = 0}

/-- A simplex supported on a vertex subset has its entire closed image supported there. -/
theorem orderNerveRealizationSimplex_supported {P : Type} [PartialOrder P] (A : Set P)
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n))
    (hs : ∀ i, s.obj i ∈ A) :
    Set.range (orderNerveRealizationSimplex P s) ⊆ orderNerveRealizationSupported P A := by
  rintro x ⟨z, rfl⟩ p hp
  have h := congrArg (fun k => k z)
    (orderNerveAffineRealization_simplex (fun q => if q = p then 1 else 0) s)
  change orderNerveRealizationCoordinates P (orderNerveRealizationSimplex P s z) p =
    orderNerveAffineSimplex (fun q => if q = p then 1 else 0) s z at h
  rw [h]
  have hn : ∀ i, s.obj i ≠ p := fun i he => hp (he ▸ hs i)
  simp [orderNerveAffineSimplex, hn]

/-- The supported carrier is exactly the union of the open cells whose vertices are selected. -/
theorem orderNerveRealizationSupported_union (P : Type) [PartialOrder P] (A : Set P) :
    (⋃ (n : ℕ) (s : {s : (nerve P).nonDegenerate n // ∀ i, s.val.obj i ∈ A}),
      orderNerveCharacteristicMap s.val '' Metric.ball 0 1) = orderNerveRealizationSupported P A := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    obtain ⟨s, hx⟩ := Set.mem_iUnion.mp hn
    apply orderNerveRealizationSimplex_supported A s.val.val s.property
    exact (orderNerveCharacteristicMap_closedCell s.val ▸
      Set.image_mono Metric.ball_subset_closedBall hx)
  · intro x hx
    obtain ⟨n, s, z, hz, he⟩ := orderNerveRealization_interior_cover P x
    have hs : ∀ i, s.val.obj i ∈ A := by
      intro i
      by_contra hi
      have hc := hx (s.val.obj i) hi
      have hf := congrArg (fun k => k z)
        (orderNerveAffineRealization_simplex (fun q => if q = s.val.obj i then 1 else 0) s.val)
      change orderNerveRealizationCoordinates P (orderNerveRealizationSimplex P s.val z)
        (s.val.obj i) =
        orderNerveAffineSimplex (fun q => if q = s.val.obj i then 1 else 0) s.val z at hf
      rw [he, hc] at hf
      have hp := (orderNerveAffineSimplex_indicator_pos_iff s.val z hz (s.val.obj i)).mpr ⟨i, rfl⟩
      rw [← hf] at hp
      exact lt_irrefl _ hp
    apply Set.mem_iUnion.mpr
    refine ⟨n, Set.mem_iUnion.mpr ⟨⟨s, hs⟩, ?_⟩⟩
    rw [orderNerveCharacteristicMap_openCell]
    exact ⟨z, hz, he⟩

/-- A genuine Mathlib CW subcomplex selecting all simplices supported on a vertex subset. -/
def orderNerveRealizationSubcomplex (P : Type) [PartialOrder P] (A : Set P) :
    CWComplex.Subcomplex (Set.univ : Set (orderNerveRealization P)) :=
  CWComplex.Subcomplex.mk' Set.univ (orderNerveRealizationSupported P A)
    (fun n => (setOf fun s : (nerve P).nonDegenerate n => ∀ i, s.val.obj i ∈ A))
    (by
      intro n s
      change orderNerveCharacteristicMap s.val '' Metric.closedBall 0 1 ⊆ _
      rw [orderNerveCharacteristicMap_closedCell]
      exact orderNerveRealizationSimplex_supported A s.val.val s.property)
    (by
      change (⋃ (n : ℕ) (s : {s : (nerve P).nonDegenerate n // ∀ i, s.val.obj i ∈ A}),
        orderNerveCharacteristicMap s.val '' Metric.ball 0 1) = _
      exact orderNerveRealizationSupported_union P A)

/-- Selecting more vertices enlarges the actual supported subcomplex. -/
theorem orderNerveRealizationSubcomplex_mono {P : Type} [PartialOrder P]
    {A B : Set P} (h : A ⊆ B) :
    (orderNerveRealizationSubcomplex P A : Set (orderNerveRealization P)) ⊆
      orderNerveRealizationSubcomplex P B := by
  intro x hx p hp
  exact hx p (fun ha => hp (h ha))

/-- The actual realization vertices have the expected indicator barycentric coordinates. -/
theorem orderNerveRealizationCoordinates_vertex {P : Type} [PartialOrder P] (p q : P) :
    orderNerveRealizationCoordinates P (orderNerveRealizationVertex p) q =
      if p = q then 1 else 0 := by
  have h := congrArg (fun k => k default)
    (orderNerveAffineRealization_simplex (fun r => if r = q then 1 else 0)
      (ComposableArrows.mk₀ p))
  change orderNerveRealizationCoordinates P (orderNerveRealizationVertex p) q =
    orderNerveAffineSimplex.{0} (fun r => if r = q then 1 else 0)
      (ComposableArrows.mk₀ p) default at h
  rw [h]
  haveI : Unique (Fin (⦋0⦌.len + 1)) := by
    simpa using (inferInstance : Unique (Fin 1))
  simp only [orderNerveAffineSimplex, ContinuousMap.coe_mk, ComposableArrows.mk₀]
  simp only [Fintype.sum_unique, Functor.const_obj_obj, mul_ite, mul_one, mul_zero]
  split_ifs
  · simp
  · rfl

/-- A realization vertex belongs to the supported subcomplex exactly when it is selected. -/
theorem orderNerveRealizationVertex_mem_subcomplex {P : Type} [PartialOrder P]
    (A : Set P) (p : P) :
    orderNerveRealizationVertex p ∈ orderNerveRealizationSubcomplex P A ↔ p ∈ A := by
  constructor
  · intro hx
    by_contra hp
    have h := hx p hp
    rw [orderNerveRealizationCoordinates_vertex] at h
    simp at h
  · intro hp q hq
    have hne : p ≠ q := fun he => hq (he ▸ hp)
    rw [orderNerveRealizationCoordinates_vertex, if_neg hne]

end FiniteChains.Comb
end

namespace FiniteChains.Comb
open CategoryTheory Simplicial
open scoped Classical

/-- Affine interpolation is natural under every actual realized monotone map. -/
theorem orderNerveAffineRealization_natural {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (f : P → Q) (hf : Monotone f) (v : Q → ℝ) (x : orderNerveRealization P) :
    orderNerveAffineRealization v (orderNerveRealizationMap f hf x) =
      orderNerveAffineRealization (v ∘ f) x := by
  obtain ⟨n, s, z, hx⟩ := orderNerveRealizationSimplex_jointly_surjective P x
  subst x
  have hn := congrArg (fun k => k z) (orderNerveRealizationSimplex_natural f hf s)
  change orderNerveRealizationMap f hf (orderNerveRealizationSimplex P s z) =
    orderNerveRealizationSimplex Q ((nerveMap hf.functor).app _ s) z at hn
  rw [hn]
  have hq := congrArg (fun k => k z)
    (orderNerveAffineRealization_simplex v ((nerveMap hf.functor).app _ s))
  have hp := congrArg (fun k => k z) (orderNerveAffineRealization_simplex (v ∘ f) s)
  change orderNerveAffineRealization v
      (orderNerveRealizationSimplex Q ((nerveMap hf.functor).app _ s) z) =
    orderNerveAffineSimplex v ((nerveMap hf.functor).app _ s) z at hq
  change orderNerveAffineRealization (v ∘ f) (orderNerveRealizationSimplex P s z) =
    orderNerveAffineSimplex (v ∘ f) s z at hp
  rw [hq, hp]
  rfl

/-- An injective monotone map preserves each actual barycentric coordinate at its image vertex. -/
theorem orderNerveRealizationCoordinates_map_injective {P Q : Type}
    [PartialOrder P] [PartialOrder Q] (f : P → Q) (hf : Monotone f)
    (hi : Function.Injective f) (x : orderNerveRealization P) (p : P) :
    orderNerveRealizationCoordinates Q (orderNerveRealizationMap f hf x) (f p) =
      orderNerveRealizationCoordinates P x p := by
  change orderNerveAffineRealization (fun q => if q = f p then 1 else 0)
    (orderNerveRealizationMap f hf x) = _
  rw [orderNerveAffineRealization_natural]
  have hv : ((fun q : Q => if q = f p then (1 : ℝ) else 0) ∘ f) =
      (fun q : P => if q = p then 1 else 0) := by
    funext q
    simp only [Function.comp_apply, hi.eq_iff]
  rw [hv]
  rfl

/-- Injective monotone maps induce injective maps of the actual geometric realizations. -/
theorem orderNerveRealizationMap_injective {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (f : P → Q) (hf : Monotone f) (hi : Function.Injective f) :
    Function.Injective (orderNerveRealizationMap f hf) := by
  intro x y h
  apply orderNerveRealizationCoordinates_injective P
  funext p
  have hc := congrArg (fun z => orderNerveRealizationCoordinates Q z (f p)) h
  simpa only [orderNerveRealizationCoordinates_map_injective f hf hi] using hc

/-- Vertices outside the image of a monotone map have zero coordinate in its realization. -/
theorem orderNerveRealizationCoordinates_map_outside {P Q : Type}
    [PartialOrder P] [PartialOrder Q] (f : P → Q) (hf : Monotone f)
    (x : orderNerveRealization P) (q : Q) (hq : q ∉ Set.range f) :
    orderNerveRealizationCoordinates Q (orderNerveRealizationMap f hf x) q = 0 := by
  change orderNerveAffineRealization (fun r => if r = q then 1 else 0)
    (orderNerveRealizationMap f hf x) = 0
  rw [orderNerveAffineRealization_natural]
  obtain ⟨n, s, z, hx⟩ := orderNerveRealizationSimplex_jointly_surjective P x
  subst x
  have he := congrArg (fun k => k z)
    (orderNerveAffineRealization_simplex ((fun r : Q => if r = q then (1 : ℝ) else 0) ∘ f) s)
  change orderNerveAffineRealization _ (orderNerveRealizationSimplex P s z) =
    orderNerveAffineSimplex _ s z at he
  rw [he]
  have hn : ∀ p : P, f p ≠ q := by
    intro p hp
    exact hq ⟨p, hp⟩
  simp [orderNerveAffineSimplex, hn]

/-- The image of a realized monotone map lies in the genuine CW subcomplex
supported on its image vertices. -/
theorem orderNerveRealizationMap_mem_subcomplex {P Q : Type}
    [PartialOrder P] [PartialOrder Q] (f : P → Q) (hf : Monotone f)
    (x : orderNerveRealization P) :
    orderNerveRealizationMap f hf x ∈
      (orderNerveRealizationSubcomplex Q (Set.range f) : Set (orderNerveRealization Q)) := by
  intro q hq
  exact orderNerveRealizationCoordinates_map_outside f hf x q hq

/-- Lift a simplex whose vertices lie in a subset to the induced subposet. -/
def orderNerveSimplexSubtype {P : Type} [PartialOrder P] (A : Set P)
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n))
    (hs : ∀ i, s.obj i ∈ A) : (nerve A).obj (Opposite.op n) where
  obj i := ⟨s.obj i, hs i⟩
  map h := homOfLE (leOfHom (s.map h))

/-- Realizing the induced subposet has exactly the supported CW subcomplex as its image. -/
theorem orderNerveRealizationSubtype_range {P : Type} [PartialOrder P] (A : Set P) :
    Set.range (orderNerveRealizationMap (Subtype.val : A → P)
      (fun _ _ h => h)) =
      (orderNerveRealizationSubcomplex P A : Set (orderNerveRealization P)) := by
  apply Set.Subset.antisymm
  · rintro x ⟨y, rfl⟩
    have h := orderNerveRealizationMap_mem_subcomplex (Subtype.val : A → P)
      (fun _ _ h => h) y
    simpa using h
  · intro x hx
    change x ∈ orderNerveRealizationSupported P A at hx
    rw [← orderNerveRealizationSupported_union P A] at hx
    obtain ⟨n, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨s, hx⟩ := Set.mem_iUnion.mp hx
    rw [orderNerveCharacteristicMap_openCell] at hx
    obtain ⟨z, _, hz⟩ := hx
    let t := orderNerveSimplexSubtype A s.val.val s.property
    refine ⟨orderNerveRealizationSimplex A t z, ?_⟩
    have ht : (nerveMap (show Monotone Subtype.val from
        fun _ _ h => h).functor).app _ t = s.val.val := by
      exact CategoryTheory.Functor.ext (fun _ => rfl)
    have he := congrArg (fun k => k z)
      (orderNerveRealizationSimplex_natural Subtype.val
        (fun _ _ h => h) t)
    rw [ht] at he
    exact he.trans hz

end FiniteChains.Comb

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical

/-- A lifted simplex realizes to the original simplex under subtype inclusion. -/
theorem orderNerveRealizationSimplex_subtype {P : Type} [PartialOrder P] (A : Set P)
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n))
    (hs : ∀ i, s.obj i ∈ A) (z : SimplexCategory.toTop.obj n) :
    orderNerveRealizationMap (Subtype.val : A → P) (fun _ _ h => h)
      (orderNerveRealizationSimplex A (orderNerveSimplexSubtype A s hs) z) =
      orderNerveRealizationSimplex P s z := by
  have ht : (nerveMap (show Monotone Subtype.val from
      fun _ _ h => h).functor).app _ (orderNerveSimplexSubtype A s hs) = s := by
    exact CategoryTheory.Functor.ext (fun _ => rfl)
  have he := congrArg (fun k => k z)
    (orderNerveRealizationSimplex_natural Subtype.val
      (fun _ _ h => h) (orderNerveSimplexSubtype A s hs))
  simp_all

/-- Induced-subposet realization inclusions are closed maps in the actual CW topology. -/
theorem orderNerveRealizationSubtype_isClosedMap {P : Type} [PartialOrder P] (A : Set P) :
    IsClosedMap (orderNerveRealizationMap (Subtype.val : A → P) (fun _ _ h => h)) := by
  intro B hB
  let f := orderNerveRealizationMap (Subtype.val : A → P) (fun _ _ h => h)
  apply (CWComplex.closed (orderNerveRealizationSubcomplex P A)
    (f '' B) ?_).mpr
  · intro n j
    change IsClosed (f '' B ∩ orderNerveCharacteristicMap j.val '' Metric.closedBall 0 1)
    erw [orderNerveCharacteristicMap_closedCell]
    haveI : CompactSpace (SimplexCategory.toTop.obj (SimplexCategory.mk n)) :=
      inferInstanceAs (CompactSpace (ULift.{0} (Convexity.StdSimplex ℝ (Fin (n + 1)))))
    let t := orderNerveSimplexSubtype A j.val.val j.property
    have he : f '' B ∩ Set.range (orderNerveRealizationSimplex P j.val.val) =
        orderNerveRealizationSimplex P j.val.val ''
          (orderNerveRealizationSimplex A t ⁻¹' B) := by
      ext x
      constructor
      · rintro ⟨⟨y, hy, hxy⟩, ⟨z, hzx⟩⟩
        refine ⟨z, ?_, hzx⟩
        have hz : f (orderNerveRealizationSimplex A t z) = f y := by
          rw [orderNerveRealizationSimplex_subtype]
          exact hzx.trans hxy.symm
        change orderNerveRealizationSimplex A t z ∈ B
        erw [orderNerveRealizationMap_injective Subtype.val
          (fun _ _ h => h) Subtype.val_injective hz]
        exact hy
      · rintro ⟨z, hz, rfl⟩
        exact ⟨⟨orderNerveRealizationSimplex A t z, hz,
          orderNerveRealizationSimplex_subtype A j.val.val j.property z⟩, ⟨z, rfl⟩⟩
    rw (config := { transparency := .default }) [he]
    exact ((hB.preimage (orderNerveRealizationSimplex A t).hom.continuous).isCompact.image
      (orderNerveRealizationSimplex P j.val.val).hom.continuous).isClosed
  · rintro x ⟨y, _, rfl⟩
    have h := orderNerveRealizationMap_mem_subcomplex Subtype.val
      (fun _ _ h => h) y
    simpa only [Subtype.range_coe_subtype, Set.setOf_mem_eq, f] using h

/-- The actual realization inclusion of an induced subposet is a closed embedding. -/
theorem orderNerveRealizationSubtype_isClosedEmbedding {P : Type} [PartialOrder P]
    (A : Set P) :
    IsClosedEmbedding (orderNerveRealizationMap (Subtype.val : A → P) (fun _ _ h => h)) :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap
    (orderNerveRealizationMap (Subtype.val : A → P) (fun _ _ h => h)).hom.continuous
    (orderNerveRealizationMap_injective (Subtype.val : A → P)
      (fun _ _ h => h) Subtype.val_injective)
    (orderNerveRealizationSubtype_isClosedMap A)

/-- The induced-subposet realization is homeomorphic to the genuine supported CW carrier. -/
def orderNerveRealizationSubtypeHomeomorph {P : Type} [PartialOrder P]
    (A : Set P) : orderNerveRealization A ≃ₜ
      (orderNerveRealizationSubcomplex P A : Set (orderNerveRealization P)) :=
  (orderNerveRealizationSubtype_isClosedEmbedding A).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (orderNerveRealizationSubtype_range A))

/-- The carrier homeomorphism is the actual realized inclusion on points. -/
theorem orderNerveRealizationSubtypeHomeomorph_coe {P : Type} [PartialOrder P]
    (A : Set P) (x : orderNerveRealization A) :
    (orderNerveRealizationSubtypeHomeomorph A x).val =
      orderNerveRealizationMap (Subtype.val : A → P) (fun _ _ h => h) x := by
  rfl

end FiniteChains.Comb
end

namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical

/-- Actual realization maps compose as the underlying monotone maps do. -/
theorem orderNerveRealizationMap_comp {P Q R : Type}
    [PartialOrder P] [PartialOrder Q] [PartialOrder R]
    (f : P → Q) (hf : Monotone f) (g : Q → R) (hg : Monotone g)
    (x : orderNerveRealization P) :
    orderNerveRealizationMap g hg (orderNerveRealizationMap f hf x) =
      orderNerveRealizationMap (g ∘ f) (hg.comp hf) x := by
  change (SSet.toTop.map (nerveMap hf.functor) ≫
    SSet.toTop.map (nerveMap hg.functor)) x = _
  erw [← Functor.map_comp]
  rfl

end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical

namespace IsPosetCover
variable {P Q : Type} [PartialOrder P] [PartialOrder Q] {f : P → Q}

/-- A poset cover reflects order in every common upper interval. -/
theorem le_of_le_above (hf : IsPosetCover f) {a b v : P}
    (ha : v ≤ a) (hb : v ≤ b) (h : f a ≤ f b) : a ≤ b := by
  obtain ⟨c, ⟨hac, hfc⟩, _⟩ := hf.up a (f b) h
  have hc  := hf.up_inj (ha.trans hac) hb hfc
  exact hc ▸ hac

/-- Every actual simplex has an actual simplex lift through a poset cover. -/
theorem exists_simplex_lift (hf : IsPosetCover f) {n : SimplexCategory}
    (s : (nerve Q).obj (Opposite.op n)) :
    ∃ t : (nerve P).obj (Opposite.op n), (nerveMap hf.mono.functor).app _ t = s := by
  obtain ⟨a, ha⟩ := hf.surj (s.obj 0)
  have hu : ∀ i, ∃ b, a ≤ b ∧ f b = s.obj i := by
    intro i
    have hi : f a ≤ s.obj i := by
      rw [ha]
      exact leOfHom (s.map (homOfLE (Fin.zero_le i)))
    obtain ⟨b, hb, _⟩ := hf.up a (s.obj i) hi
    exact ⟨b, hb⟩
  choose b hb hfb using hu
  let t : (nerve P).obj (Opposite.op n) :=
    { obj := b
      map := fun h => homOfLE (hf.le_of_le_above (hb _) (hb _) (by
        rw [hfb, hfb]
        exact leOfHom (s.map h))) }
  refine ⟨t, ?_⟩
  exact CategoryTheory.Functor.ext hfb

/-- The actual realized map of a poset cover is surjective. -/
theorem realizationMap_surjective (hf : IsPosetCover f) :
    Function.Surjective (orderNerveRealizationMap f hf.mono) := by
  intro x
  obtain ⟨n, s, z, hx⟩ := orderNerveRealizationSimplex_jointly_surjective Q x
  obtain ⟨t, ht⟩ := hf.exists_simplex_lift s
  refine ⟨orderNerveRealizationSimplex P t z, ?_⟩
  have he := congrArg (fun k => k z) (orderNerveRealizationSimplex_natural f hf.mono t)
  rw [ht] at he
  exact he.trans hx

end IsPosetCover
end FiniteChains.Comb

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

def StrictAbove (v : P) := {p : P // v < p}

instance (v : P) : PartialOrder (StrictAbove v) := Subtype.partialOrder _

def strictSourceRayEdge (v : P) (e : StrictOrdEdge P) :
    StrictAbove v →₀ ℤ := by
  classical
  exact if h : e.1.1 = v then Finsupp.single ⟨e.1.2, h ▸ e.2⟩ 1 else 0

def strictSourceRayChain (v : P) :
    (StrictOrdEdge P →₀ ℤ) →ₗ[ℤ] (StrictAbove v →₀ ℤ) :=
  Finsupp.linearCombination ℤ (strictSourceRayEdge v)

def strictBottomLinkTriangle (v : P) (t : StrictOrdTri P) :
    StrictOrdEdge (StrictAbove v) →₀ ℤ := by
  classical
  exact if h : t.1.1 = v then Finsupp.single
    ⟨(⟨t.1.2.1, h ▸ t.2.1⟩, ⟨t.1.2.2, h ▸ t.2.1.trans t.2.2⟩), t.2.2⟩ 1 else 0

def strictBottomLinkChain (v : P) :
    (StrictOrdTri P →₀ ℤ) →ₗ[ℤ] (StrictOrdEdge (StrictAbove v) →₀ ℤ) :=
  Finsupp.linearCombination ℤ (strictBottomLinkTriangle v)

def strictBottomConeTriangle (v : P) (e : StrictOrdEdge (StrictAbove v)) :
    StrictOrdTri P :=
  ⟨(v, e.1.1.val, e.1.2.val), e.1.1.property, e.2⟩

theorem strictBottomLinkChain_apply (v : P) (c : StrictOrdTri P →₀ ℤ)
    (e : StrictOrdEdge (StrictAbove v)) :
    strictBottomLinkChain v c e = c (strictBottomConeTriangle v e) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single t n =>
    rcases t with ⟨⟨z, a, b⟩, hza, hab⟩
    rcases e with ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, hxy⟩
    by_cases ht : z = v
    · subst z
      simp [strictBottomLinkChain, strictBottomLinkTriangle, strictBottomConeTriangle,
        Finsupp.single_apply, StrictOrdTri, StrictOrdEdge, StrictAbove,
        Subtype.mk.injEq, Prod.mk.injEq]
    · simp [strictBottomLinkChain, strictBottomLinkTriangle, ht, strictBottomConeTriangle,
        StrictOrdTri, StrictOrdEdge, StrictAbove]

theorem strictSourceRayChain_apply (v : P) (c : StrictOrdEdge P →₀ ℤ)
    (x : StrictAbove v) :
    strictSourceRayChain v c x = c ⟨(v, x.val), x.property⟩ := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single e n =>
    rcases e with ⟨⟨a, b⟩, hab⟩
    rcases x with ⟨x, hx⟩
    by_cases ha : a = v
    · subst a
      simp [strictSourceRayChain, strictSourceRayEdge, Finsupp.single_apply,
        StrictOrdEdge, StrictAbove, Subtype.mk.injEq, Prod.mk.injEq]
    · simp [strictSourceRayChain, strictSourceRayEdge, ha, StrictOrdEdge, StrictAbove]

/-- At a minimal vertex the extracted upper link has the negative source-ray
boundary.  This identity applies to every finite chain, including relative chains. -/
theorem strictBottomLink_boundary (v : P) (hm : ∀ p, p ≤ v → p = v)
    (c : StrictOrdTri P →₀ ℤ) :
    bdry1 (strictOrderCx (StrictAbove v)) (strictBottomLinkChain v c) =
      -strictSourceRayChain v (bdry2 (strictOrderCx P) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd, neg_add]
  | single t n =>
    have hmid : t.1.2.1 ≠ v := by
      intro he
      have ht := hm t.1.1 (he ▸ t.2.1.le)
      exact (ne_of_lt t.2.1) (ht.trans he.symm)
    erw [strictTriangle_bdry2_single, map_sub, map_add]
    by_cases ht : t.1.1 = v
    · simp [strictSourceRayChain, strictSourceRayEdge, strictBottomLinkChain,
        strictBottomLinkTriangle, strictTriangleEdge01, strictTriangleEdge12,
        strictTriangleEdge02, hmid, ht, bdry1, strictOrderCx, smul_sub,
        neg_sub]
    · simp [strictSourceRayChain, strictSourceRayEdge, strictBottomLinkChain,
        strictBottomLinkTriangle, strictTriangleEdge01, strictTriangleEdge12,
        strictTriangleEdge02, hmid, ht]

/-- Only source-edge boundary vanishing is used; no absolute cycle premise is
introduced when extracting the link of a relative two-chain. -/
theorem strictBottomLink_relative_cycle (v : P) (hm : ∀ p, p ≤ v → p = v)
    (c : StrictOrdTri P →₀ ℤ)
    (hc : ∀ e : StrictOrdEdge P, e.1.1 = v → bdry2 (strictOrderCx P) c e = 0) :
    bdry1 (strictOrderCx (StrictAbove v)) (strictBottomLinkChain v c) = 0 := by
  erw [strictBottomLink_boundary v hm]
  have hz : strictSourceRayChain v (bdry2 (strictOrderCx P) c) = 0 := by
    ext x
    erw [strictSourceRayChain_apply]
    exact hc _ rfl
  simp_all

namespace IsPosetCover
variable {Q : Type u} [PartialOrder Q] {f : P → Q} (hf : IsPosetCover f)

include hf in
theorem upperInterval_le_reflect {a b v : P} (ha : v ≤ a) (hb : v ≤ b)
    (h : f a ≤ f b) : a ≤ b := by
  obtain ⟨c, ⟨hac, hfc⟩, _⟩ := hf.up a (f b) h
  have hc  := hf.up_inj (ha.trans hac) hb hfc
  exact hc ▸ hac

def upperIntervalLift (v : P) (q : StrictAbove (f v)) :
    StrictAbove v := by
  let a := Classical.choose (hf.up v q.1 q.2.le)
  have hs : v ≤ a ∧ f a = q.1 := (Classical.choose_spec (hf.up v q.1 q.2.le)).1
  exact ⟨a, lt_of_le_of_ne hs.1 (by
    intro he
    exact (ne_of_lt q.2) ((congrArg f he).trans hs.2))⟩

theorem upperIntervalLift_projection (v : P) (q : StrictAbove (f v)) :
    f (hf.upperIntervalLift v q).1 = q.1 :=
  (Classical.choose_spec (hf.up v q.1 q.2.le)).1.2

/-- An actual cover identifies each upper link with the actual upper link in
the base.  Distinct pole lifts are not identified by this construction. -/
def upperIntervalOrderIso (v : P) :
    StrictAbove v ≃o StrictAbove (f v) where
  toFun p := ⟨f p.1, hf.strictMono p.2⟩
  invFun := hf.upperIntervalLift v
  left_inv p := Subtype.ext (hf.up_inj (hf.upperIntervalLift v _).2.le p.2.le
    (hf.upperIntervalLift_projection v _))
  right_inv q := Subtype.ext (hf.upperIntervalLift_projection v q)
  map_rel_iff' {a b} := ⟨fun h => upperInterval_le_reflect hf a.2.le b.2.le h,
    fun h => hf.mono h⟩

end IsPosetCover

def strictAboveCongr {a b : P} (h : a = b) : StrictAbove a ≃o StrictAbove b := by
  cases h
  exact OrderIso.refl _

theorem strictAboveCongr_val {a b : P} (h : a = b) (x : StrictAbove a) :
    (strictAboveCongr h x).val = x.val := by
  cases h
  rfl

end FiniteChains.Comb
end

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis
open Comb Cell
universe u
variable {κ ι : Type u} {M : ℕ} [NeZero M]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)

abbrev PolygonPoleLink := StrictAbove (cC hc)

def polygonPoleRadius (p : Fin M) : PolygonPoleLink hc :=
  ⟨cR hc p, ctr_lt_rad hc p⟩

def polygonPoleTriangle (p : Fin M) : PolygonPoleLink hc :=
  ⟨cI hc p, ctr_lt_inn hc p⟩

def polygonPoleEdgePlus (p : Fin M) : StrictOrdEdge (PolygonPoleLink hc) :=
  ⟨(polygonPoleRadius hc p, polygonPoleTriangle hc p),
    (lt_inn_iff hc).2 (Or.inr (Or.inl rfl))⟩

def polygonPoleEdgeMinus (p : Fin M) : StrictOrdEdge (PolygonPoleLink hc) :=
  ⟨(polygonPoleRadius hc (p + 1), polygonPoleTriangle hc p),
    (lt_inn_iff hc).2 (Or.inr (Or.inr (Or.inl rfl)))⟩

/-- All edges of the actual upper link are the two radial incidences of an
actual inner triangle; no presentation of the link is assumed. -/
theorem polygonPoleLink_edge_cases (e : StrictOrdEdge (PolygonPoleLink hc)) :
    ∃ p : Fin M, e = polygonPoleEdgePlus hc p ∨ e = polygonPoleEdgeMinus hc p := by
  rcases e with ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hab⟩
  change toS vc ec hc a < toS vc ec hc b at hab
  obtain ⟨p, hp | hp⟩ := (ctr_lt_iff hc).mp ha
  · subst a
    rcases (rad_lt_iff hc).mp hab with hb' | hb'
    · subst b
      exact ⟨p, Or.inl rfl⟩
    · subst b
      refine ⟨fpred p, Or.inr ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        simp only [polygonPoleEdgeMinus, polygonPoleRadius, cR, toS, fpred_add_one]
      · rfl
  · subst a
    have hh := (lt_iff_plt hc).mp hab
    cases b <;> simp [plt] at hh

@[simp] theorem polygonPoleRadius_eq_iff (p r : Fin M) :
    polygonPoleRadius hc p = polygonPoleRadius hc r ↔ p = r := by
  constructor
  · intro h
    exact Cell.rad.inj (congrArg (fun x : PolygonPoleLink hc => x.val) h)
  · rintro rfl
    rfl

@[simp] theorem polygonPoleTriangle_eq_iff (p r : Fin M) :
    polygonPoleTriangle hc p = polygonPoleTriangle hc r ↔ p = r := by
  constructor
  · intro h
    exact Cell.inn.inj (congrArg (fun x : PolygonPoleLink hc => x.val) h)
  · rintro rfl
    rfl

@[simp] theorem polygonPoleRadius_ne_triangle (p r : Fin M) :
    polygonPoleRadius hc p ≠ polygonPoleTriangle hc r := by
  intro he
  have hh := congrArg Subtype.val he
  cases hh

@[simp] theorem polygonPoleTriangle_ne_radius (p r : Fin M) :
    polygonPoleTriangle hc p ≠ polygonPoleRadius hc r :=
  (polygonPoleRadius_ne_triangle hc r p).symm

@[simp] theorem polygonPoleEdgePlus_eq_iff (p r : Fin M) :
    polygonPoleEdgePlus hc p = polygonPoleEdgePlus hc r ↔ p = r := by
  constructor
  · intro he
    exact (polygonPoleTriangle_eq_iff hc p r).mp
      (congrArg (fun e : StrictOrdEdge (PolygonPoleLink hc) => e.1.2) he)
  · rintro rfl
    rfl

@[simp] theorem polygonPoleEdgeMinus_eq_iff (p r : Fin M) :
    polygonPoleEdgeMinus hc p = polygonPoleEdgeMinus hc r ↔ p = r := by
  constructor
  · intro he
    exact (polygonPoleTriangle_eq_iff hc p r).mp
      (congrArg (fun e : StrictOrdEdge (PolygonPoleLink hc) => e.1.2) he)
  · rintro rfl
    rfl

theorem polygonPoleEdgePlus_ne_minus (hM : 2 ≤ M) (p r : Fin M) :
    polygonPoleEdgePlus hc p ≠ polygonPoleEdgeMinus hc r := by
  intro he
  have hpr  := (polygonPoleTriangle_eq_iff hc p r).mp
    (congrArg (fun e : StrictOrdEdge (PolygonPoleLink hc) => e.1.2) he)
  subst r
  have hr  := (polygonPoleRadius_eq_iff hc p (p + 1)).mp
    (congrArg (fun e : StrictOrdEdge (PolygonPoleLink hc) => e.1.1) he)
  exact fin_succ_ne_self hM p hr.symm

/-- The two actual incidences at an inner-triangle vertex have their genuine
positive boundary signs. -/
theorem polygonPole_boundary_triangle (hM : 2 ≤ M)
    (d : StrictOrdEdge (PolygonPoleLink hc) →₀ ℤ) (p : Fin M) :
    Comb.bdry1 (strictOrderCx (PolygonPoleLink hc)) d (polygonPoleTriangle hc p) =
      d (polygonPoleEdgePlus hc p) + d (polygonPoleEdgeMinus hc p) := by
  classical
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d e hd he => simp only [map_add, Finsupp.add_apply, hd, he]; ring
  | single e n =>
    obtain ⟨r, hr | hr⟩ := polygonPoleLink_edge_cases hc e
    · subst e
      erw [Comb.bdry1_single]
      change (n • (Finsupp.single (polygonPoleTriangle hc r) (1 : ℤ) -
        Finsupp.single (polygonPoleRadius hc r) 1) : PolygonPoleLink hc →₀ ℤ) _ = _
      simp [Finsupp.single_apply, polygonPoleEdgePlus_ne_minus hc hM]
    · subst e
      have hne := fun r p => (polygonPoleEdgePlus_ne_minus hc hM p r).symm
      rw (config := { transparency := .default }) [Comb.bdry1_single]
      change (n • (Finsupp.single (polygonPoleTriangle hc r) (1 : ℤ) -
        Finsupp.single (polygonPoleRadius hc (r + 1)) 1) : PolygonPoleLink hc →₀ ℤ) _ = _
      simp [Finsupp.single_apply, hne]

/-- At a radius, the two actual incidences have their genuine negative signs. -/
theorem polygonPole_boundary_radius (hM : 2 ≤ M)
    (d : StrictOrdEdge (PolygonPoleLink hc) →₀ ℤ) (p : Fin M) :
    Comb.bdry1 (strictOrderCx (PolygonPoleLink hc)) d (polygonPoleRadius hc (p + 1)) =
      -d (polygonPoleEdgePlus hc (p + 1)) - d (polygonPoleEdgeMinus hc p) := by
  classical
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d e hd he => simp only [map_add, Finsupp.add_apply, hd, he]; ring
  | single e n =>
    obtain ⟨r, hr | hr⟩ := polygonPoleLink_edge_cases hc e
    · subst e
      erw [Comb.bdry1_single]
      change (n • (Finsupp.single (polygonPoleTriangle hc r) (1 : ℤ) -
        Finsupp.single (polygonPoleRadius hc r) 1) : PolygonPoleLink hc →₀ ℤ) _ = _
      simp [Finsupp.single_apply, polygonPoleEdgePlus_ne_minus hc hM]
    · subst e
      have hne := fun r p => (polygonPoleEdgePlus_ne_minus hc hM p r).symm
      rw (config := { transparency := .default }) [Comb.bdry1_single]
      change (n • (Finsupp.single (polygonPoleTriangle hc r) (1 : ℤ) -
        Finsupp.single (polygonPoleRadius hc (r + 1)) 1) : PolygonPoleLink hc →₀ ℤ) _ = _
      simp [Finsupp.single_apply, hne]

/-- Every integral one-cycle of the actual polygon-centre link has a single
coefficient.  This is the local coefficient rigidity used at each cover pole. -/
theorem polygonPole_cycle_coefficients (hM : 2 ≤ M)
    (d : StrictOrdEdge (PolygonPoleLink hc) →₀ ℤ)
    (hd : Comb.bdry1 (strictOrderCx (PolygonPoleLink hc)) d = 0) (p : Fin M) :
    d (polygonPoleEdgePlus hc p) = d (polygonPoleEdgePlus hc 0) ∧
      d (polygonPoleEdgeMinus hc p) = -d (polygonPoleEdgePlus hc 0) := by
  have hlocal (r : Fin M) :
      d (polygonPoleEdgeMinus hc r) = -d (polygonPoleEdgePlus hc r) ∧
      d (polygonPoleEdgePlus hc (r + 1)) = d (polygonPoleEdgePlus hc r) := by
    have ht := polygonPole_boundary_triangle hc hM d r
    have hr := polygonPole_boundary_radius hc hM d r
    erw [hd, Finsupp.zero_apply] at ht hr
    omega
  have hall : ∀ n hn,
      d (polygonPoleEdgePlus hc ⟨n, hn⟩) = d (polygonPoleEdgePlus hc 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro hn
      have hp : n < M := by omega
      have hs : (⟨n, hp⟩ : Fin M) + 1 = ⟨n + 1, hn⟩ := by
        ext
        erw [fin_succ_val]
        exact Nat.mod_eq_of_lt hn
      erw [← hs, (hlocal ⟨n, hp⟩).2]
      exact ih hp
  simp_all

/-- Agreement at one actual radial incidence determines the entire pole link. -/
theorem polygonPole_cycle_ext (hM : 2 ≤ M)
    (c d : StrictOrdEdge (PolygonPoleLink hc) →₀ ℤ)
    (hc' : Comb.bdry1 (strictOrderCx (PolygonPoleLink hc)) c = 0)
    (hd : Comb.bdry1 (strictOrderCx (PolygonPoleLink hc)) d = 0)
    (he : c (polygonPoleEdgePlus hc 0) = d (polygonPoleEdgePlus hc 0)) : c = d := by
  ext e
  obtain ⟨p, hp | hp⟩ := polygonPoleLink_edge_cases hc e
  · subst e
    exact (polygonPole_cycle_coefficients hc hM c hc' p).1.trans
      (he.trans (polygonPole_cycle_coefficients hc hM d hd p).1.symm)
  · subst e
    exact (polygonPole_cycle_coefficients hc hM c hc' p).2.trans
      ((congrArg Neg.neg he).trans (polygonPole_cycle_coefficients hc hM d hd p).2.symm)

section Cover
variable {P : Type u} [PartialOrder P] (f : P → SCell vc ec hc)
  (hf : IsPosetCover f)



/-- The actual upper link at each genuine lifted polygon centre. -/
def polygonCoverPoleOrderIso (v : P) (hv : f v = cC hc) :
    StrictAbove v ≃o PolygonPoleLink hc :=
  (hf.upperIntervalOrderIso v).trans (strictAboveCongr hv)

theorem polygonCoverPoleOrderIso_apply_val (v : P) (hv : f v = cC hc)
    (x : StrictAbove v) :
    (polygonCoverPoleOrderIso hc f hf v hv x).val = f x.val := by
  erw [strictAboveCongr_val]
  rfl

def polygonCoverPoleHom (v : P) (hv : f v = cC hc) :
    Hom (strictOrderCx (StrictAbove v)) (strictOrderCx (PolygonPoleLink hc)) :=
  strictOrderCxMap (polygonCoverPoleOrderIso hc f hf v hv)
    (polygonCoverPoleOrderIso hc f hf v hv).strictMono

def polygonCoverPoleLink (v : P) (hv : f v = cC hc)
    (c : StrictOrdTri P →₀ ℤ) : StrictOrdEdge (PolygonPoleLink hc) →₀ ℤ :=
  chain1 (polygonCoverPoleHom hc f hf v hv) (strictBottomLinkChain v c)

/-- A relative chain with boundary on the marked boundary graph gives a cycle
at each lifted pole.  The two-chain itself is not assumed closed. -/
theorem polygonCoverPoleLink_cycle (v : P) (hv : f v = cC hc)
    (c : StrictOrdTri P →₀ ℤ)
    (hrel : ∀ e : StrictOrdEdge P,
      f e.1.1 = cC hc → Comb.bdry2 (strictOrderCx P) c e = 0) :
    Comb.bdry1 (strictOrderCx (PolygonPoleLink hc))
      (polygonCoverPoleLink hc f hf v hv c) = 0 := by
  erw [bdry1_chain1]
  have hlink := strictBottomLink_relative_cycle v
    (by
      intro a ha
      have hfa := hf.mono ha
      erw [hv] at hfa
      exact hf.down_inj ha (le_refl v) ((show (f a) = cC hc by
        change (f a) = cC hc ∨ plt vc ec (f a) ctr at hfa
        rcases hfa with hfa | hfa
        · exact hfa
        · cases (f a) <;> simp [plt] at hfa).trans hv.symm)) c (fun e he => hrel e (he.symm ▸ hv))
  simp_all

/-- Projection within one lifted upper interval keeps every actual coefficient. -/
theorem polygonCoverPoleLink_apply (v : P) (hv : f v = cC hc)
    (c : StrictOrdTri P →₀ ℤ) (e : StrictOrdEdge (StrictAbove v)) :
    polygonCoverPoleLink hc f hf v hv c
      ((polygonCoverPoleHom hc f hf v hv).onE e) =
        c (strictBottomConeTriangle v e) :=
  (strictOrderCxMap_chain1_apply
    (polygonCoverPoleOrderIso hc f hf v hv)
    (polygonCoverPoleOrderIso hc f hf v hv).strictMono
    (polygonCoverPoleOrderIso hc f hf v hv).injective
    (strictBottomLinkChain v c) e).trans (strictBottomLinkChain_apply v c e)

def polygonCoverPoleFlagPlus (v : P) (hv : f v = cC hc)
    (p : Fin M) : StrictOrdTri P :=
  strictBottomConeTriangle v
    ((strictOrderEdgeEquiv (polygonCoverPoleOrderIso hc f hf v hv)).symm
      (polygonPoleEdgePlus hc p))

theorem polygonCoverPoleFlagPlus_projection (v : P) (hv : f v = cC hc) (p : Fin M) :
    f (polygonCoverPoleFlagPlus hc f hf v hv p).1.1 = cC hc ∧
    f (polygonCoverPoleFlagPlus hc f hf v hv p).1.2.1 = cR hc p ∧
    f (polygonCoverPoleFlagPlus hc f hf v hv p).1.2.2 = cI hc p := by
  let iso := polygonCoverPoleOrderIso hc f hf v hv
  let eqv := strictOrderEdgeEquiv iso
  let e := eqv.symm (polygonPoleEdgePlus hc p)
  have he : eqv e = polygonPoleEdgePlus hc p := eqv.apply_symm_apply _
  have h₁ := congrArg (fun z : StrictOrdEdge (PolygonPoleLink hc) => z.1.1.val) he
  have h₂ := congrArg (fun z : StrictOrdEdge (PolygonPoleLink hc) => z.1.2.val) he
  erw [polygonCoverPoleOrderIso_apply_val] at h₁ h₂
  exact ⟨hv, h₁, h₂⟩

theorem polygonCoverPoleLink_plus (v : P) (hv : f v = cC hc)
    (c : StrictOrdTri P →₀ ℤ) (p : Fin M) :
    polygonCoverPoleLink hc f hf v hv c (polygonPoleEdgePlus hc p) =
      c (polygonCoverPoleFlagPlus hc f hf v hv p) := by
  let e := strictOrderEdgeEquiv (polygonCoverPoleOrderIso hc f hf v hv)
  have hh := polygonCoverPoleLink_apply hc f hf v hv c
    (e.symm (polygonPoleEdgePlus hc p))
  change polygonCoverPoleLink hc f hf v hv c
    (e (e.symm (polygonPoleEdgePlus hc p))) = _ at hh
  erw [e.apply_symm_apply] at hh
  exact hh

/-- The actual finite set of nonzero coefficients is indexed by actual pole
lifts, even for disconnected covers with arbitrarily many sheets. -/
abbrev PolygonCoverPole := {v : P // f v = cC hc}

def polygonCoverPoleFlag (v : PolygonCoverPole hc f) : StrictOrdTri P :=
  polygonCoverPoleFlagPlus hc f hf v.1 v.2 0


def polygonCoverPoleCoefficients :
    (StrictOrdTri P →₀ ℤ) →ₗ[ℤ] (PolygonCoverPole hc f →₀ ℤ) :=
  (Finsupp.comapDomain.addMonoidHom (show Function.Injective (polygonCoverPoleFlag hc f hf) by
    intro v w h
    apply Subtype.ext
    exact congrArg (fun t : StrictOrdTri P => t.1.1) h)).toIntLinearMap

theorem polygonCoverPoleCoefficients_apply (c : StrictOrdTri P →₀ ℤ)
    (v : PolygonCoverPole hc f) :
    polygonCoverPoleCoefficients hc f hf c v = c (polygonCoverPoleFlag hc f hf v) := rfl

/-- Equality of the finitely supported pole coefficients forces equality on
every actual triangle incident to a pole.  This is relative coefficient
rigidity in a genuine cover, rather than an augmented statement on the base. -/
theorem polygonCoverPole_relative_ext (hM : 2 ≤ M)
    (c d : StrictOrdTri P →₀ ℤ)
    (hc' : ∀ e : StrictOrdEdge P,
      f e.1.1 = cC hc → Comb.bdry2 (strictOrderCx P) c e = 0)
    (hd : ∀ e : StrictOrdEdge P,
      f e.1.1 = cC hc → Comb.bdry2 (strictOrderCx P) d e = 0)
    (he : polygonCoverPoleCoefficients hc f hf c = polygonCoverPoleCoefficients hc f hf d)
    (t : StrictOrdTri P) (ht : f t.1.1 = cC hc) : c t = d t := by
  let v : PolygonCoverPole hc f := ⟨t.1.1, ht⟩
  have hp : c (polygonCoverPoleFlag hc f hf v) = d (polygonCoverPoleFlag hc f hf v) :=
    congrArg (fun z => z v) he
  have hlink := polygonPole_cycle_ext hc hM
    (polygonCoverPoleLink hc f hf v.1 v.2 c)
    (polygonCoverPoleLink hc f hf v.1 v.2 d)
    (polygonCoverPoleLink_cycle hc f hf v.1 v.2 c hc')
    (polygonCoverPoleLink_cycle hc f hf v.1 v.2 d hd)
    (by simpa only [polygonCoverPoleLink_plus, polygonCoverPoleFlag] using hp)
  let e : StrictOrdEdge (StrictAbove v.1) :=
    ⟨(⟨t.1.2.1, t.2.1⟩, ⟨t.1.2.2, t.2.1.trans t.2.2⟩), t.2.2⟩
  have hh := congrArg (fun z => z ((polygonCoverPoleHom hc f hf v.1 v.2).onE e)) hlink
  convert hh using 1 <;> simp only [polygonCoverPoleLink_apply] <;> rfl

/-- Reindexing the genuine pole lifts by a group gives a full group-ring
coefficient.  The next formula shows explicitly that no sheet is summed away. -/
def polygonCoverGroupCoefficient {G : Type u} [Group G]
    (e : PolygonCoverPole hc f ≃ G) (c : StrictOrdTri P →₀ ℤ) : MonoidAlgebra ℤ G :=
  MonoidAlgebra.ofCoeff (Finsupp.mapDomain e (polygonCoverPoleCoefficients hc f hf c))

end Cover

/-- The one-dimensional identified boundary of the polygon. -/
def InPolygonBoundary : SCell vc ec hc → Prop
  | .vtx _ => True
  | .bed _ => True
  | _ => False

section BoundarySupport
variable {P : Type u} [PartialOrder P] (f : P → SCell vc ec hc)
  (hf : IsPosetCover f)

/-- The relative hypothesis used above follows directly from actual boundary
support on the polygon marking, without a homology or cycle assumption. -/
theorem polygonCover_boundary_vanishes_at_poles
    (c : StrictOrdTri P →₀ ℤ)
    (hboundary : ∀ e ∈ (Comb.bdry2 (strictOrderCx P) c).support,
      InPolygonBoundary hc (f e.1.1)) :
    ∀ e : StrictOrdEdge P,
      f e.1.1 = cC hc → Comb.bdry2 (strictOrderCx P) c e = 0 := by
  intro e he
  by_contra hn
  have hh := hboundary e (Finsupp.mem_support_iff.mpr hn)
  erw [he] at hh
  exact hh

end BoundarySupport

namespace Genus
variable (q : ℕ) [NeZero q]

variable {P : Type} [PartialOrder P]
  (f : P → SCell (gvc q) (gec q) (gc q)) (hf : IsPosetCover f)

end Genus
end FiniteChains.Davis
end

section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb

universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

/-- The normalized one-chain map of a monotone map between different posets. -/
def normalizedChain1To (f : P → Q) (hf : Monotone f) :
    (StrictOrdEdge P →₀ ℤ) →ₗ[ℤ] (StrictOrdEdge Q →₀ ℤ) :=
  normalizeOrdChain1.comp ((chain1 (orderCxMap f hf)).comp (chain1 (strictOrderIncl P)))

end FiniteChains.Comb

namespace FiniteChains.Davis
open RACG Mirror Comb

universe u
variable {P X : Type u} [PartialOrder P] [DecidableEq P]
  [PartialOrder X] (g : P →o X)
  (a : Qpos (cmpRel P) X (nerveAtt g))
  (hc : IsConnected (orderCx (Qpos (cmpRel P) X (nerveAtt g))))

/-- The cover of the original cell poset retains actual universal-cover sheets. -/
abbrev AttachingSurfaceCover := PosetCoverPullback
  (uOrderEnd (P := Qpos (cmpRel P) X (nerveAtt g)) (a := a))
  (fun p : P => qNew (att := nerveAtt g) (g p))

abbrev attachingSurfaceProjection : AttachingSurfaceCover g a → P :=
  posetPullbackProjection _ _


theorem qAttachingCoverEnd_monotone :
    Monotone (qAttachingCoverEnd a) := by
  intro p r hpr
  exact qPositiveOldOrderIso.monotone
    (show (⟨uOrderEnd p.1, p.2⟩ : QPositiveOld) ≤ ⟨uOrderEnd r.1, r.2⟩ from
      uOrderEnd_monotone hpr)

theorem qAttachingCoverEnd_oldPoint (p : QLiftedAttaching a) :
    qOldIncl (att := nerveAtt g) (posQCube (qAttachingCoverEnd a p)) = uOrderEnd p.1 := by
  exact congrArg Subtype.val
    (qPositiveOldOrderIso.symm_apply_apply ⟨uOrderEnd p.1, p.2⟩)

theorem attachingSurface_lower_comparison (p : QLiftedAttaching a) :
    qNew (att := nerveAtt g) (nerveAtt g (qAttachingCoverEnd a p)) ≤ uOrderEnd p.1 := by grind [qAttachingCoverEnd_oldPoint, qNew_att_le_qOldIncl]

/-- Move to the actual lower base lift in the same universal-cover sheet. -/
def attachingSurfaceLowerLift (p : QLiftedAttaching a) :
    UOrder (Qpos (cmpRel P) X (nerveAtt g)) a :=
  (uOrderEnd_isPosetCover hc).lowerMapLift Subtype.val
    (fun p => qNew (att := nerveAtt g) (nerveAtt g (qAttachingCoverEnd a p)))
    (attachingSurface_lower_comparison g a) p

theorem attachingSurfaceLowerLift_spec (p : QLiftedAttaching a) :
    attachingSurfaceLowerLift g a hc p ≤ p.1 ∧
      uOrderEnd (attachingSurfaceLowerLift g a hc p) =
        qNew (att := nerveAtt g) (nerveAtt g (qAttachingCoverEnd a p)) :=
  (uOrderEnd_isPosetCover hc).lowerMapLift_spec _ _ _ p

theorem attachingSurfaceLowerLift_monotone :
    Monotone (attachingSurfaceLowerLift g a hc) :=
  (uOrderEnd_isPosetCover hc).lowerMapLift_monotone
    (Subtype.val : QLiftedAttaching a → UOrder (Qpos (cmpRel P) X (nerveAtt g)) a)
    (fun p => qNew (att := nerveAtt g) (nerveAtt g (qAttachingCoverEnd a p)))
    (fun _ _ h => h)
    (qNew_monotone.comp ((nerveAtt g).monotone.comp (qAttachingCoverEnd_monotone g a)))
    (attachingSurface_lower_comparison g a)

/-- The actual lifted last-vertex map from the subdivided attaching locus. -/
def attachingToSurfaceCover (p : QLiftedAttaching a) : AttachingSurfaceCover g a :=
  ⟨(attachingSurfaceLowerLift g a hc p, chainMax (qAttachingCoverEnd a p)),
    (attachingSurfaceLowerLift_spec g a hc p).2⟩

theorem attachingToSurfaceCover_monotone :
    Monotone (attachingToSurfaceCover g a hc) := by
  intro p r hpr
  exact ⟨attachingSurfaceLowerLift_monotone g a hc hpr,
    chainMax_monotone (qAttachingCoverEnd_monotone g a hpr)⟩

@[simp] theorem attachingToSurfaceCover_projection (p : QLiftedAttaching a) :
    attachingSurfaceProjection g a (attachingToSurfaceCover g a hc p) =
      chainMax (qAttachingCoverEnd a p) := rfl

def attachingSurfaceChain1 : (StrictOrdEdge (QLiftedAttaching a) →₀ ℤ) →ₗ[ℤ]
    (StrictOrdEdge (AttachingSurfaceCover g a) →₀ ℤ) :=
  normalizedChain1To (attachingToSurfaceCover g a hc)
    (attachingToSurfaceCover_monotone g a hc)

/-- The barycentric pullback cover, before applying its last-vertex map. -/
abbrev AttachingSurfaceSubdivision := PosetCoverPullback
  (uOrderEnd (P := Qpos (cmpRel P) X (nerveAtt g)) (a := a))
  (fun σ : NeSpx (cmpRel P) => qNew (att := nerveAtt g) (nerveAtt g σ))

theorem surfaceSubdivision_upper_comparison (p : AttachingSurfaceSubdivision g a) :
    uOrderEnd p.1.1 ≤ qOldIncl (att := nerveAtt g) (posQCube p.1.2) := by
  erw [p.2]
  exact qNew_att_le_qOldIncl p.1.2

/-- The inverse cover comparison is an actual upper interval lift in the
same sheet, rather than a selected homotopy equivalence of presentations. -/
def surfaceSubdivisionUpperLift (p : AttachingSurfaceSubdivision g a) :
    UOrder (Qpos (cmpRel P) X (nerveAtt g)) a :=
  (uOrderEnd_isPosetCover hc).upperMapLift (fun p => p.1.1)
    (fun p => qOldIncl (att := nerveAtt g) (posQCube p.1.2))
    (surfaceSubdivision_upper_comparison g a) p

theorem surfaceSubdivisionUpperLift_spec (p : AttachingSurfaceSubdivision g a) :
    p.1.1 ≤ surfaceSubdivisionUpperLift g a hc p ∧
      uOrderEnd (surfaceSubdivisionUpperLift g a hc p) =
        qOldIncl (att := nerveAtt g) (posQCube p.1.2) :=
  (uOrderEnd_isPosetCover hc).upperMapLift_spec
    (fun p : AttachingSurfaceSubdivision g a => p.1.1)
    (fun p => qOldIncl (att := nerveAtt g) (posQCube p.1.2))
    (surfaceSubdivision_upper_comparison g a) p


def surfaceSubdivisionToAttaching (p : AttachingSurfaceSubdivision g a) :
    QLiftedAttaching a :=
  ⟨surfaceSubdivisionUpperLift g a hc p, by
    rw (config := { transparency := .default }) [(surfaceSubdivisionUpperLift_spec g a hc p).2]
    exact ⟨trivial, rfl⟩⟩

theorem surfaceSubdivisionToAttaching_monotone :
    Monotone (surfaceSubdivisionToAttaching g a hc) :=
  (by
    apply (uOrderEnd_isPosetCover hc).upperMapLift_monotone
      (fun p : AttachingSurfaceSubdivision g a => p.1.1)
      (fun p => qOldIncl (att := nerveAtt g) (posQCube p.1.2))
      ?_ ?_ (surfaceSubdivision_upper_comparison g a)
    · exact fun _ _ h => h.1
    · intro p r hpr
      exact qOldIncl_monotone (⟨hpr.2, fun _ _ => rfl⟩))


end FiniteChains.Davis

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily

variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)

def namedSurfaceLabel : GenusVertex q →o namedBasePos ρ q u :=
  gHom (w := genusNonemptyW (namedPres ρ q u)
      (namedA (α := α) q) (namedB (α := α) q) q) (j₀ := Sum.inr PUnit.unit)
    (genus_hM (namedA (α := α) q) (namedB (α := α) q) q)
    (genus_hvlab (namedA (α := α) q) (namedB (α := α) q) q)
    (genus_helb (namedA (α := α) q) (namedB (α := α) q) q) (gc q)

@[simp] theorem namedAtt_eq_nerveAtt :
    namedAtt ρ q u = nerveAtt (namedSurfaceLabel ρ q u) := rfl

theorem namedQuotientPos_isConnected : IsConnected (orderCx (namedQuotientPos ρ q u)) := by
  letI : Nonempty (namedBasePos ρ q u) := ⟨namedAtt ρ q u (gBase q)⟩
  exact qpos_isConnected_of_zpos (zpos_isConnected (namedBasePos_isConnected ρ q u))

abbrev NamedSurfaceCover :=
  AttachingSurfaceCover (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)

abbrev namedSurfaceProjection : NamedSurfaceCover ρ q u → GenusVertex q :=
  attachingSurfaceProjection (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)

theorem namedSurfaceProjection_isPosetCover : IsPosetCover (namedSurfaceProjection ρ q u) :=
  ((uOrderEnd_isPosetCover (namedQuotientPos_isConnected ρ q u)).pullback _ (qNew_monotone.comp (namedSurfaceLabel ρ q u).monotone))

end FiniteChains.Davis.Genus
end

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

/-- For an actual strict map, the normalized map is its genuine strict cellular chain map. -/
theorem normalizedStrictChain2_eq_strict (f : P → Q) (hf : StrictMono f)
    (c : StrictOrdTri P →₀ ℤ) :
    normalizedStrictChain2 f hf.monotone c = chain2 (strictOrderCxMap f hf) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single t n =>
    have h01 := hf t.2.1
    have h12 := hf t.2.2
    change normalizeOrdChain2 (Finsupp.mapDomain (orderCxMap f hf.monotone).onF
      (Finsupp.mapDomain (strictOrderIncl P).onF (Finsupp.single t n))) =
      Finsupp.mapDomain (strictOrderCxMap f hf).onF (Finsupp.single t n)
    rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single, Finsupp.mapDomain_single,
      normalizeOrdChain2_single]
    simp [normalizeOrdTriangle, orderCxMap, strictOrderIncl, strictOrderCxMap, h01, h12]


/-- Actual strict maps commute with genuine normalization of arbitrary finite weak chains. -/
theorem normalizeOrdChain2_strict_map (f : P → Q) (hf : StrictMono f)
    (c : OrdTri P →₀ ℤ) :
    normalizeOrdChain2 (chain2 (orderCxMap f hf.monotone) c) =
      chain2 (strictOrderCxMap f hf) (normalizeOrdChain2 c) := by
  rw [normalizeOrdChain2_map, normalizedStrictChain2_eq_strict]

end FiniteChains.Comb
end

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
open ASC
variable {P Q : Type} [PartialOrder P] [PartialOrder Q]
  {f : P → Q} (hf : IsPosetCover f)

theorem cover_lt_of_image {a b : P} (hab : a ≤ b) (h : f a < f b) : a < b :=
  lt_of_le_of_ne hab (fun he => h.ne (congrArg f he))

/-- All local surface incidences lift through a genuine poset cover. -/
def coveredSurfaceRank (S : SurfaceRank Q) : SurfaceRank P where
  rk a := S.rk (f a)
  rk_lt_of_lt h := S.rk_lt_of_lt (hf.strictMono h)
  rk_le_two a := S.rk_le_two (f a)
  two_vertices e he := by
    obtain ⟨a, b, hab, ha, hb, hall⟩ := S.two_vertices (f e) he
    obtain ⟨a', ⟨ha'e, hfa⟩, _⟩ := hf.down e a ha.le
    obtain ⟨b', ⟨hb'e, hfb⟩, _⟩ := hf.down e b hb.le
    have ha' : a' < e := cover_lt_of_image ha'e (hfa.symm ▸ ha)
    have hb' : b' < e := cover_lt_of_image hb'e (hfb.symm ▸ hb)
    refine ⟨a', b', ?_, ha', hb', ?_⟩
    · grind
    · intro z hz
      rcases hall (f z) (hf.strictMono hz) with hz' | hz'
      · exact Or.inl (hf.down_inj hz.le ha'e (hz'.trans hfa.symm))
      · exact Or.inr (hf.down_inj hz.le hb'e (hz'.trans hfb.symm))
  two_faces e he := by
    obtain ⟨a, b, hab, ha, hb, hall⟩ := S.two_faces (f e) he
    obtain ⟨a', ⟨hea', hfa⟩, _⟩ := hf.up e a ha.le
    obtain ⟨b', ⟨heb', hfb⟩, _⟩ := hf.up e b hb.le
    have ha' : e < a' := cover_lt_of_image hea' (hfa.symm ▸ ha)
    have hb' : e < b' := cover_lt_of_image heb' (hfb.symm ▸ hb)
    refine ⟨a', b', ?_, ha', hb', ?_⟩
    · grind
    · intro z hz
      rcases hall (f z) (hf.strictMono hz) with hz' | hz'
      · exact Or.inl (hf.up_inj hz.le hea' (hz'.trans hfa.symm))
      · exact Or.inr (hf.up_inj hz.le heb' (hz'.trans hfb.symm))
  two_edges v t hv ht hvt := by
    obtain ⟨a, b, hab, ha, hb, hall⟩ := S.two_edges (f v) (f t) hv ht (hf.strictMono hvt)
    obtain ⟨a', hva', ha't, hfa⟩ := hf.exists_interval_lift hvt.le a ha.1.le ha.2.le
    obtain ⟨b', hvb', hb't, hfb⟩ := hf.exists_interval_lift hvt.le b hb.1.le hb.2.le
    have ha' : v < a' ∧ a' < t :=
      ⟨cover_lt_of_image hva' (hfa.symm ▸ ha.1),
        cover_lt_of_image ha't (hfa.symm ▸ ha.2)⟩
    have hb' : v < b' ∧ b' < t :=
      ⟨cover_lt_of_image hvb' (hfb.symm ▸ hb.1),
        cover_lt_of_image hb't (hfb.symm ▸ hb.2)⟩
    refine ⟨a', b', ?_, ha', hb', ?_⟩
    · grind
    · intro z hz
      rcases hall (f z) ⟨hf.strictMono hz.1, hf.strictMono hz.2⟩ with hz' | hz'
      · exact Or.inl (hf.up_inj hz.1.le hva' (hz'.trans hfa.symm))
      · exact Or.inr (hf.up_inj hz.1.le hvb' (hz'.trans hfb.symm))
  exists_face x := by
    obtain ⟨t, ht, hxt⟩ := S.exists_face (f x)
    obtain ⟨t', ⟨hxt', hft⟩, _⟩ := hf.up x t hxt
    exact ⟨t', hft.symm ▸ ht, hxt'⟩
  exists_vertex t ht := by
    obtain ⟨v, hv, hvt⟩ := S.exists_vertex (f t) ht
    obtain ⟨v', ⟨hv't, hfv⟩, _⟩ := hf.down t v hvt.le
    exact ⟨v', hfv.symm ▸ hv, cover_lt_of_image hv't (hfv.symm ▸ hvt)⟩

/-- Triangular face geometry is preserved in every actual lifted face. -/
theorem coveredSurfaceRank_faceEdges (S : SurfaceRank Q) (hfe : FaceEdges S) :
    FaceEdges (coveredSurfaceRank hf S) := by
  intro v w t hv hw ht hvt hwt hvw
  have hne  := fun he => hvw (hf.down_inj hvt.le hwt.le he)
  obtain ⟨e, hve, hwe, het⟩ := hfe (f v) (f w) (f t) hv hw ht
    (hf.strictMono hvt) (hf.strictMono hwt) hne
  obtain ⟨e', hve', he't, hfe'⟩ := hf.exists_interval_lift hvt.le e hve.le het.le
  have hwe'  := hf.le_of_le_below hwt.le he't (hfe'.symm ▸ hwe.le)
  exact ⟨e', cover_lt_of_image hve' (hfe'.symm ▸ hve),
    cover_lt_of_image hwe' (hfe'.symm ▸ hwe),
    cover_lt_of_image he't (hfe'.symm ▸ het)⟩

section Coefficients
variable (S : SurfaceRank P)
include S

theorem triangle_rank (r : StrictOrdTri P) :
    S.rk r.1.1 = 0 ∧ S.rk r.1.2.1 = 1 ∧ S.rk r.1.2.2 = 2 :=
  S.rk_flag r.2.1 r.2.2

/-- At a fixed edge/face incidence the only boundary contributions are the
two actual flags formed with the edge's endpoints. -/
theorem surfaceBoundary_vertex_pair {a b e t : P}
    (hae : a < e) (hbe : b < e) (het : e < t) (hab : a ≠ b)
    (hall : ∀ x, x < e → x = a ∨ x = b)
    (c : StrictOrdTri P →₀ ℤ) :
    Comb.bdry2 (strictOrderCx P) c ⟨(e, t), het⟩ =
      c ⟨(a, e, t), hae, het⟩ + c ⟨(b, e, t), hbe, het⟩ := by
  classical
  let A : StrictOrdTri P := ⟨(a, e, t), hae, het⟩
  let B : StrictOrdTri P := ⟨(b, e, t), hbe, het⟩
  let E : StrictOrdEdge P := ⟨(e, t), het⟩
  have hAB : A ≠ B := fun h => hab (congrArg (fun r : StrictOrdTri P => r.1.1) h)
  have hrk := S.rk_flag hae het
  have h01 r : strictTriangleEdge01 r ≠ E := by
    intro h
    have hh := congrArg (fun d : StrictOrdEdge P => S.rk d.1.1) h
    have hr := triangle_rank S r
    change S.rk r.1.1 = S.rk e at hh
    omega
  have h02 r : strictTriangleEdge02 r ≠ E := by
    intro h
    have hh := congrArg (fun d : StrictOrdEdge P => S.rk d.1.1) h
    have hr := triangle_rank S r
    change S.rk r.1.1 = S.rk e at hh
    omega
  have h12 (r : StrictOrdTri P) : strictTriangleEdge12 r = E ↔ r = A ∨ r = B := by
    constructor
    · intro h
      have he : r.1.2.1 = e := congrArg (fun d : StrictOrdEdge P => d.1.1) h
      have ht : r.1.2.2 = t := congrArg (fun d : StrictOrdEdge P => d.1.2) h
      rcases hall r.1.1 (he ▸ r.2.1) with hv | hv
      · exact Or.inl (Subtype.ext (Prod.ext hv (Prod.ext he ht)))
      · exact Or.inr (Subtype.ext (Prod.ext hv (Prod.ext he ht)))
    · rintro (rfl | rfl) <;> rfl
  change Comb.bdry2 (strictOrderCx P) c E = c A + c B
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]; ring
  | single r n =>
    rw (config := { transparency := .default }) [strictTriangle_bdry2_single, Finsupp.sub_apply, Finsupp.add_apply]
    by_cases hA : r = A
    · subst r
      simp [Finsupp.single_apply, h01, h02, h12, hAB]
    · by_cases hB : r = B
      · subst r
        simp [Finsupp.single_apply, h01, h02, h12, hAB.symm]
      · simp [h01, h02, h12, hA, hB]

/-- At a vertex/face diagonal the two incident flags both occur negatively. -/
theorem surfaceBoundary_edge_pair {v a b t : P}
    (hva : v < a) (hat : a < t) (hvb : v < b) (hbt : b < t) (hab : a ≠ b)
    (hall : ∀ x, v < x ∧ x < t → x = a ∨ x = b)
    (c : StrictOrdTri P →₀ ℤ) :
    Comb.bdry2 (strictOrderCx P) c ⟨(v, t), hva.trans hat⟩ =
      -c ⟨(v, a, t), hva, hat⟩ - c ⟨(v, b, t), hvb, hbt⟩ := by
  classical
  let A : StrictOrdTri P := ⟨(v, a, t), hva, hat⟩
  let B : StrictOrdTri P := ⟨(v, b, t), hvb, hbt⟩
  let E : StrictOrdEdge P := ⟨(v, t), hva.trans hat⟩
  have hAB : A ≠ B := fun h => hab (congrArg (fun r : StrictOrdTri P => r.1.2.1) h)
  have hrk := S.rk_flag hva hat
  have h01 r : strictTriangleEdge01 r ≠ E := by
    intro h
    have hh := congrArg (fun d : StrictOrdEdge P => S.rk d.1.2) h
    have hr := triangle_rank S r
    change S.rk r.1.2.1 = S.rk t at hh
    omega
  have h12 r : strictTriangleEdge12 r ≠ E := by
    intro h
    have hh := congrArg (fun d : StrictOrdEdge P => S.rk d.1.1) h
    have hr := triangle_rank S r
    change S.rk r.1.2.1 = S.rk v at hh
    omega
  have h02 (r : StrictOrdTri P) : strictTriangleEdge02 r = E ↔ r = A ∨ r = B := by
    constructor
    · intro h
      have hv : r.1.1 = v := congrArg (fun d : StrictOrdEdge P => d.1.1) h
      have ht : r.1.2.2 = t := congrArg (fun d : StrictOrdEdge P => d.1.2) h
      rcases hall r.1.2.1 ⟨hv ▸ r.2.1, ht ▸ r.2.2⟩ with he | he
      · exact Or.inl (Subtype.ext (Prod.ext hv (Prod.ext he ht)))
      · exact Or.inr (Subtype.ext (Prod.ext hv (Prod.ext he ht)))
    · rintro (rfl | rfl) <;> rfl
  change Comb.bdry2 (strictOrderCx P) c E = -c A - c B
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]; ring
  | single r n =>
    rw (config := { transparency := .default }) [strictTriangle_bdry2_single, Finsupp.sub_apply, Finsupp.add_apply]
    by_cases hA : r = A
    · subst r
      simp [Finsupp.single_apply, h01, h12, h02, hAB]
    · by_cases hB : r = B
      · subst r
        simp [Finsupp.single_apply, h01, h12, h02, hAB.symm]
      · simp [h01, h12, h02, hA, hB]

/-- At a vertex/edge incidence the two flags in the adjacent faces occur positively. -/
theorem surfaceBoundary_face_pair {v e a b : P}
    (hve : v < e) (hea : e < a) (heb : e < b) (hab : a ≠ b)
    (hall : ∀ x, e < x → x = a ∨ x = b)
    (c : StrictOrdTri P →₀ ℤ) :
    Comb.bdry2 (strictOrderCx P) c ⟨(v, e), hve⟩ =
      c ⟨(v, e, a), hve, hea⟩ + c ⟨(v, e, b), hve, heb⟩ := by
  classical
  let A : StrictOrdTri P := ⟨(v, e, a), hve, hea⟩
  let B : StrictOrdTri P := ⟨(v, e, b), hve, heb⟩
  let E : StrictOrdEdge P := ⟨(v, e), hve⟩
  have hAB : A ≠ B := fun h => hab (congrArg (fun r : StrictOrdTri P => r.1.2.2) h)
  have hrk := S.rk_flag hve hea
  have h12 r : strictTriangleEdge12 r ≠ E := by
    intro h
    have hh := congrArg (fun d : StrictOrdEdge P => S.rk d.1.1) h
    have hr := triangle_rank S r
    change S.rk r.1.2.1 = S.rk v at hh
    omega
  have h02 r : strictTriangleEdge02 r ≠ E := by
    intro h
    have hh := congrArg (fun d : StrictOrdEdge P => S.rk d.1.2) h
    have hr := triangle_rank S r
    change S.rk r.1.2.2 = S.rk e at hh
    omega
  have h01 (r : StrictOrdTri P) : strictTriangleEdge01 r = E ↔ r = A ∨ r = B := by
    constructor
    · intro h
      have hv : r.1.1 = v := congrArg (fun d : StrictOrdEdge P => d.1.1) h
      have he : r.1.2.1 = e := congrArg (fun d : StrictOrdEdge P => d.1.2) h
      rcases hall r.1.2.2 (he ▸ r.2.2) with ht | ht
      · exact Or.inl (Subtype.ext (Prod.ext hv (Prod.ext he ht)))
      · exact Or.inr (Subtype.ext (Prod.ext hv (Prod.ext he ht)))
    · rintro (rfl | rfl) <;> rfl
  change Comb.bdry2 (strictOrderCx P) c E = c A + c B
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]; ring
  | single r n =>
    rw (config := { transparency := .default }) [strictTriangle_bdry2_single, Finsupp.sub_apply, Finsupp.add_apply]
    by_cases hA : r = A
    · subst r
      simp [Finsupp.single_apply, h01, h12, h02, hAB]
    · by_cases hB : r = B
      · subst r
        simp [Finsupp.single_apply, h01, h12, h02, hAB.symm]
      · simp [h01, h12, h02, hA, hB]

end Coefficients

theorem exactlyTwo_exhaust {X : Type} {R : X → Prop} (h : ExactlyTwo R)
    {a b : X} (ha : R a) (hb : R b) (hab : a ≠ b) :
    ∀ x, R x → x = a ∨ x = b := by
  obtain ⟨x, y, _, _, _, hall⟩ := h
  grind

section Propagation
variable (S : SurfaceRank P) (c : StrictOrdTri P →₀ ℤ)
include S

/-- A zero flag coefficient propagates across a vertex change inside a face. -/
theorem surface_zero_change_vertex {a b e t : P}
    (hae : a < e) (hbe : b < e) (het : e < t)
    (hd : Comb.bdry2 (strictOrderCx P) c ⟨(e, t), het⟩ = 0)
    (hz : c ⟨(a, e, t), hae, het⟩ = 0) :
    c ⟨(b, e, t), hbe, het⟩ = 0 := by
  by_cases hab : a = b
  · simp_all
  · have he  := (S.rk_flag hae het).2.1
    have hpair := surfaceBoundary_vertex_pair S hae hbe het hab
      (exactlyTwo_exhaust (S.two_vertices e he) hae hbe hab) c
    erw [hd, hz] at hpair
    omega

/-- A zero flag coefficient propagates across an edge change inside a face. -/
theorem surface_zero_change_edge {v a b t : P}
    (hva : v < a) (hat : a < t) (hvb : v < b) (hbt : b < t)
    (hd : Comb.bdry2 (strictOrderCx P) c ⟨(v, t), hva.trans hat⟩ = 0)
    (hz : c ⟨(v, a, t), hva, hat⟩ = 0) :
    c ⟨(v, b, t), hvb, hbt⟩ = 0 := by
  by_cases hab : a = b
  · simp_all
  · have hrk := S.rk_flag hva hat
    have hpair := surfaceBoundary_edge_pair S hva hat hvb hbt hab
      (exactlyTwo_exhaust (S.two_edges v t hrk.1 hrk.2.2 (hva.trans hat))
        ⟨hva, hat⟩ ⟨hvb, hbt⟩ hab) c
    erw [hd, hz] at hpair
    omega

/-- A zero flag coefficient crosses an actual shared old edge as soon as the
relative boundary vanishes at that edge incidence. -/
theorem surface_zero_change_face {v e a b : P}
    (hve : v < e) (hea : e < a) (heb : e < b)
    (hd : Comb.bdry2 (strictOrderCx P) c ⟨(v, e), hve⟩ = 0)
    (hz : c ⟨(v, e, a), hve, hea⟩ = 0) :
    c ⟨(v, e, b), hve, heb⟩ = 0 := by
  by_cases hab : a = b
  · simp_all
  · have he  := (S.rk_flag hve hea).2.1
    have hpair := surfaceBoundary_face_pair S hve hea heb hab
      (exactlyTwo_exhaust (S.two_faces e he) hea heb hab) c
    erw [hd, hz] at hpair
    omega

/-- One zero flag coefficient determines all flags of its actual triangular
face.  Only the internal vertex/face and edge/face boundary entries are used. -/
theorem surface_zero_in_face (hfe : FaceEdges S)
    (hrel : ∀ e : StrictOrdEdge P, S.rk e.1.2 = 2 →
      Comb.bdry2 (strictOrderCx P) c e = 0)
    (a b : StrictOrdTri P) (htop : a.1.2.2 = b.1.2.2) (ha : c a = 0) : c b = 0 := by
  rcases a with ⟨⟨v, e, t⟩, hve, het⟩
  rcases b with ⟨⟨w, d, t'⟩, hwd, hdt⟩
  dsimp only at htop
  subst t'
  have hrk := S.rk_flag hve het
  have hrk' := S.rk_flag hwd hdt
  by_cases hvw : v = w
  · subst w
    exact surface_zero_change_edge S c hve het hwd hdt (hrel _ hrk.2.2) ha
  · obtain ⟨r, hvr, hwr, hrt⟩ := hfe v w t hrk.1 hrk'.1 hrk.2.2
      (hve.trans het) (hwd.trans hdt) hvw
    have h₁ : c ⟨(v, r, t), hvr, hrt⟩ = 0 :=
      surface_zero_change_edge S c hve het hvr hrt (hrel _ hrk.2.2) ha
    have h₂ : c ⟨(w, r, t), hwr, hrt⟩ = 0 :=
      surface_zero_change_vertex S c hvr hwr hrt (hrel _ hrk.2.2) h₁
    exact surface_zero_change_edge S c hwr hrt hwd hdt (hrel _ hrk.2.2) h₂

end Propagation
end FiniteChains.Comb

namespace FiniteChains.Davis
open Comb ASC Cell
variable {κ ι P : Type} {M : ℕ} [NeZero M] [PartialOrder P]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)
  (hd : PolygonData vc ec) (f : P → SCell vc ec hc) (hf : IsPosetCover f)

/-- The boundary of a relative surface chain is supported on the actual
identified polygon boundary, in both endpoints of each edge. -/
def PolygonRelativeChain (c : StrictOrdTri P →₀ ℤ) : Prop :=
  ∀ e ∈ (Comb.bdry2 (strictOrderCx P) c).support,
    InPolygonBoundary hc (f e.1.1) ∧ InPolygonBoundary hc (f e.1.2)

theorem polygonBoundary_rank_le_one {a : SCell vc ec hc}
    (ha : InPolygonBoundary hc a) : Cell.rk a ≤ 1 := by
  cases a <;> simp_all [InPolygonBoundary, Cell.rk]

theorem polygonRelative_boundary_zero_of_target
    (c : StrictOrdTri P →₀ ℤ) (hrel : PolygonRelativeChain hc f c)
    (e : StrictOrdEdge P) (he : ¬ InPolygonBoundary hc (f e.1.2)) :
    Comb.bdry2 (strictOrderCx P) c e = 0 := by
  by_contra hn
  exact he ((hrel e (Finsupp.mem_support_iff.mpr hn)).2)

theorem polygonRelative_boundary_zero_at_face
    (c : StrictOrdTri P →₀ ℤ) (hrel : PolygonRelativeChain hc f c)
    (e : StrictOrdEdge P) (he : Cell.rk (f e.1.2) = 2) :
    Comb.bdry2 (strictOrderCx P) c e = 0 := by
  apply polygonRelative_boundary_zero_of_target hc f c hrel e
  intro hb
  have hr := polygonBoundary_rank_le_one hc hb
  omega

include hd hf in
theorem polygonRelative_zero_in_face
    (c : StrictOrdTri P →₀ ℤ) (hrel : PolygonRelativeChain hc f c)
    (a b : StrictOrdTri P) (ht : a.1.2.2 = b.1.2.2) (ha : c a = 0) : c b = 0 :=
  surface_zero_in_face (coveredSurfaceRank hf (surfaceRank_SCell hc hd)) c
    (coveredSurfaceRank_faceEdges hf (surfaceRank_SCell hc hd) (faceEdges_SCell hc hd))
    (polygonRelative_boundary_zero_at_face hc f c hrel) a b ht ha

include hd in
/-- Every flag of every actual lifted inner triangle is forced by the pole
coefficients.  This propagates across all six flags, not only the two centre flags. -/
theorem polygonRelative_zero_inner
    (c : StrictOrdTri P →₀ ℤ) (hrel : PolygonRelativeChain hc f c)
    (hpoles : polygonCoverPoleCoefficients hc f hf c = 0)
    (p : Fin M) (t : StrictOrdTri P) (ht : f t.1.2.2 = cI hc p) : c t = 0 := by
  let S := coveredSurfaceRank hf (surfaceRank_SCell hc hd)
  have hM : 2 ≤ M := by have := hd.three_le; omega
  have hsource  :=
    polygonCover_boundary_vanishes_at_poles hc f c (fun e he => (hrel e he).1)
  have hpole : ∀ a : StrictOrdTri P, f a.1.1 = cC hc → c a = 0 := by
    intro a ha
    have he : polygonCoverPoleCoefficients hc f hf c =
        polygonCoverPoleCoefficients hc f hf 0 := by erw [map_zero]; exact hpoles
    have hh := polygonCoverPole_relative_ext hc f hf hM c 0 hsource
      (by intro e _; simp) he a ha
    exact hh
  obtain ⟨v, ⟨hvt, hfv⟩, _⟩ := hf.down t.1.2.2 (cC hc)
    (by erw [ht]; exact (ctr_lt_inn hc p).le)
  have hvT  := lt_of_le_of_ne hvt (by
    intro he
    have hh := hfv.symm.trans ((congrArg f he).trans ht)
    exact (ctr_lt_inn hc p).ne hh)
  have hvrk : S.rk v = 0 := by change Cell.rk (f v) = 0; erw [hfv]; rfl
  have hTrk  := (S.rk_flag t.2.1 t.2.2).2.2
  obtain ⟨e, _, _, ⟨hve, heT⟩, _, _⟩ := S.two_edges v t.1.2.2 hvrk hTrk hvT
  let a : StrictOrdTri P := ⟨(v, e, t.1.2.2), hve, heT⟩
  exact polygonRelative_zero_in_face hc hd f hf c hrel a t rfl (hpole a hfv)

include hd hf in
/-- Move a zero coefficient from all flags over one actual face across an
internal edge to all flags over its adjacent actual face. -/
theorem polygonRelative_zero_across
    (c : StrictOrdTri P →₀ ℤ) (hrel : PolygonRelativeChain hc f c)
    (t : StrictOrdTri P) (e a : SCell vc ec hc)
    (herk : Cell.rk e = 1) (het : e < f t.1.2.2) (hea : e < a)
    (heboundary : ¬ InPolygonBoundary hc e)
    (ha : ∀ z : StrictOrdTri P, f z.1.2.2 = a → c z = 0) : c t = 0 := by
  let S := coveredSurfaceRank hf (surfaceRank_SCell hc hd)
  obtain ⟨d, ⟨hdT, hfd⟩, _⟩ := hf.down t.1.2.2 e het.le
  have hdT'  := lt_of_le_of_ne hdT (by
    intro he
    exact het.ne (hfd.symm.trans (congrArg f he)))
  obtain ⟨a', ⟨hda, hfa⟩, _⟩ := hf.up d a (by erw [hfd]; exact hea.le)
  have hda'  := lt_of_le_of_ne hda (by
    intro he
    exact hea.ne (hfd.symm.trans ((congrArg f he).trans hfa)))
  have hdrk : S.rk d = 1 := by change Cell.rk (f d) = 1; erw [hfd]; exact herk
  obtain ⟨v, _, _, hvd, _, _⟩ := S.two_vertices d hdrk
  let z : StrictOrdTri P := ⟨(v, d, a'), hvd, hda'⟩
  let w : StrictOrdTri P := ⟨(v, d, t.1.2.2), hvd, hdT'⟩
  have hbd : Comb.bdry2 (strictOrderCx P) c ⟨(v, d), hvd⟩ = 0 :=
    polygonRelative_boundary_zero_of_target hc f c hrel _ (hfd.symm ▸ heboundary)
  have hw  := surface_zero_change_face S c hvd hda' hdT' hbd (ha z hfa)
  exact polygonRelative_zero_in_face hc hd f hf c hrel w t rfl hw

include hd in
/-- The genuine `ced` incidence carries rigidity from the fan into every
lifted inner collar triangle. -/
theorem polygonRelative_zero_inner_collar
    (c : StrictOrdTri P →₀ ℤ) (hrel : PolygonRelativeChain hc f c)
    (hpoles : polygonCoverPoleCoefficients hc f hf c = 0)
    (p : Fin M) (t : StrictOrdTri P) (ht : f t.1.2.2 = cT2 hc p) : c t = 0 := by
  apply polygonRelative_zero_across hc hd f hf c hrel t (cF hc p) (cI hc p) rfl
  · erw [ht]
    exact lt_of_le_of_ne (cF_le_cT2 hc p) (by intro h; cases h)
  · exact lt_of_le_of_ne (cF_le_cI hc p) (by intro h; cases h)
  · exact fun h => h
  · exact polygonRelative_zero_inner hc hd f hf c hrel hpoles p

include hd in
/-- The genuine `gdi` incidence carries rigidity to every lifted outer
collar triangle.  The identified boundary is never crossed. -/
theorem polygonRelative_zero_outer_collar
    (c : StrictOrdTri P →₀ ℤ) (hrel : PolygonRelativeChain hc f c)
    (hpoles : polygonCoverPoleCoefficients hc f hf c = 0)
    (p : Fin M) (t : StrictOrdTri P) (ht : f t.1.2.2 = cT1 hc p) : c t = 0 := by
  apply polygonRelative_zero_across hc hd f hf c hrel t (cG hc p) (cT2 hc p) rfl
  · erw [ht]
    exact lt_of_le_of_ne (cG_le_cT1 hc p) (by intro h; cases h)
  · exact lt_of_le_of_ne (cG_le_cT2 hc p) (by intro h; cases h)
  · exact fun h => h
  · exact polygonRelative_zero_inner_collar hc hd f hf c hrel hpoles p

include hd in
/-- The complete relative two-chain in an actual surface cover is detected by
its actual pole coefficients, after propagation through every fan and collar
flag.  No global connectedness or group faithfulness premise is used. -/
theorem polygonRelative_zero_of_pole_coefficients
    (c : StrictOrdTri P →₀ ℤ) (hrel : PolygonRelativeChain hc f c)
    (hpoles : polygonCoverPoleCoefficients hc f hf c = 0) : c = 0 := by
  ext t
  have hrk := (surfaceRank_SCell hc hd).rk_flag (hf.strictMono t.2.1) (hf.strictMono t.2.2)
  have ht : Cell.rk (f t.1.2.2) = 2 := hrk.2.2
  generalize he : f t.1.2.2 = a at ht
  cases a with
  | inn p => exact polygonRelative_zero_inner hc hd f hf c hrel hpoles p t he
  | tr2 p => exact polygonRelative_zero_inner_collar hc hd f hf c hrel hpoles p t he
  | tr1 p => exact polygonRelative_zero_outer_collar hc hd f hf c hrel hpoles p t he
  | _ => simp [Cell.rk] at ht


theorem PolygonRelativeChain.zero : PolygonRelativeChain hc f (0 : StrictOrdTri P →₀ ℤ) := by
  intro e he
  simp at he

theorem PolygonRelativeChain.add {c d : StrictOrdTri P →₀ ℤ}
    (hc' : PolygonRelativeChain hc f c) (hd' : PolygonRelativeChain hc f d) :
    PolygonRelativeChain hc f (c + d) := by
  intro e he
  have hn  := Finsupp.mem_support_iff.mp he
  by_cases hce : Comb.bdry2 (strictOrderCx P) c e = 0
  · have hde : Comb.bdry2 (strictOrderCx P) d e ≠ 0 := by
      intro hd0
      apply hn
      erw [map_add, Finsupp.add_apply, hce, hd0, add_zero]
    exact hd' e (Finsupp.mem_support_iff.mpr hde)
  · exact hc' e (Finsupp.mem_support_iff.mpr hce)

theorem PolygonRelativeChain.smul {c : StrictOrdTri P →₀ ℤ}
    (hc' : PolygonRelativeChain hc f c) (n : ℤ) : PolygonRelativeChain hc f (n • c) := by
  intro e he
  have hn  := Finsupp.mem_support_iff.mp he
  have hce : Comb.bdry2 (strictOrderCx P) c e ≠ 0 := by
    intro hzero
    apply hn
    erw [map_smul, Finsupp.smul_apply, hzero, smul_zero]
  exact hc' e (Finsupp.mem_support_iff.mpr hce)

include hd in
/-- Full relative surface-chain reconstruction is unique for its finite family
of pole coefficients, including all six flags and both collar triangles. -/
theorem polygonRelative_ext
    (c d : StrictOrdTri P →₀ ℤ)
    (hc' : PolygonRelativeChain hc f c) (hd' : PolygonRelativeChain hc f d)
    (hpoles : polygonCoverPoleCoefficients hc f hf c =
      polygonCoverPoleCoefficients hc f hf d) : c = d := by
  apply sub_eq_zero.mp
  apply polygonRelative_zero_of_pole_coefficients hc hd f hf (c - d)
    (by
      intro e he
      have hn  := Finsupp.mem_support_iff.mp he
      by_cases hce : Comb.bdry2 (strictOrderCx P) c e = 0
      · have hde : Comb.bdry2 (strictOrderCx P) d e ≠ 0 := by
          intro hd0
          apply hn
          erw [map_sub, Finsupp.sub_apply, hce, hd0, sub_self]
        exact hd' e (Finsupp.mem_support_iff.mpr hde)
      · exact hc' e (Finsupp.mem_support_iff.mpr hce))
  simp_all

end FiniteChains.Davis
end

section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis
open Comb Cell
variable {κ ι P : Type} {M : ℕ} [NeZero M] [PartialOrder P]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)
  (f : P → SCell vc ec hc) (hf : IsPosetCover f)

/-- A lifted copy of the polygon before its boundary sides are identified.
Different boundary positions may represent different points of the cover. -/
structure CoveredPolygon (v : PolygonCoverPole hc f) where
  V : Fin M → P
  W : Fin M → P
  E : Fin M → P
  D : Fin M → P
  G : Fin M → P
  F : Fin M → P
  R : Fin M → P
  T1 : Fin M → P
  T2 : Fin M → P
  I : Fin M → P
  projV : ∀ p, f (V p) = cV hc p
  projW : ∀ p, f (W p) = cW hc p
  projE : ∀ p, f (E p) = cE hc p
  projD : ∀ p, f (D p) = cD hc p
  projG : ∀ p, f (G p) = cG hc p
  projF : ∀ p, f (F p) = cF hc p
  projR : ∀ p, f (R p) = cR hc p
  projT1 : ∀ p, f (T1 p) = cT1 hc p
  projT2 : ∀ p, f (T2 p) = cT2 hc p
  projI : ∀ p, f (I p) = cI hc p
  ve : ∀ p, V p ≤ E p
  v1e : ∀ p, V (p + 1) ≤ E p
  vd : ∀ p, V p ≤ D p
  wd : ∀ p, W p ≤ D p
  vg : ∀ p, V p ≤ G p
  w1g : ∀ p, W (p + 1) ≤ G p
  wf : ∀ p, W p ≤ F p
  w1f : ∀ p, W (p + 1) ≤ F p
  cr : ∀ p, v.1 ≤ R p
  wr : ∀ p, W p ≤ R p
  et1 : ∀ p, E p ≤ T1 p
  d1t1 : ∀ p, D (p + 1) ≤ T1 p
  gt1 : ∀ p, G p ≤ T1 p
  gt2 : ∀ p, G p ≤ T2 p
  ft2 : ∀ p, F p ≤ T2 p
  dt2 : ∀ p, D p ≤ T2 p
  ri : ∀ p, R p ≤ I p
  fi : ∀ p, F p ≤ I p
  r1i : ∀ p, R (p + 1) ≤ I p

include hf in
/-- Every actual pole determines an actual lifted disk.  Only the proved
unique upper/lower interval lifting of a poset cover is used. -/

def coveredPolygon (v : PolygonCoverPole hc f) : CoveredPolygon hc f v :=
  Classical.choice (by
    have lup (a : P) (b : SCell vc ec hc) (h : f a ≤ b) :
        ∃ x, a ≤ x ∧ f x = b := (hf.up a b h).exists
    have ldown (a : P) (b : SCell vc ec hc) (h : b ≤ f a) :
        ∃ x, x ≤ a ∧ f x = b := (hf.down a b h).exists
    choose R hR using fun p : Fin M => lup v.1 (cR hc p)
      (by erw [v.2]; exact cC_le_cR hc p)
    choose I hI using fun p : Fin M => lup v.1 (cI hc p)
      (by erw [v.2]; exact (ctr_lt_inn hc p).le)
    have hri (p : Fin M) : R p ≤ I p :=
      hf.le_of_le_above (hR p).1 (hI p).1 (by
        erw [(hR p).2, (hI p).2]; exact cR_le_cI hc p)
    have hr1i (p : Fin M) : R (p + 1) ≤ I p :=
      hf.le_of_le_above (hR (p + 1)).1 (hI p).1 (by
        erw [(hR (p + 1)).2, (hI p).2]; exact cR1_le_cI hc p)
    choose W hW using fun p : Fin M => ldown (R p) (cW hc p)
      (by erw [(hR p).2]; exact cW_le_cR hc p)
    choose F hF using fun p : Fin M => ldown (I p) (cF hc p)
      (by erw [(hI p).2]; exact cF_le_cI hc p)
    have hwf (p : Fin M) : W p ≤ F p :=
      hf.le_of_le_below ((hW p).1.trans (hri p)) (hF p).1 (by
        erw [(hW p).2, (hF p).2]; exact cW_le_cF hc p)
    have hw1f (p : Fin M) : W (p + 1) ≤ F p :=
      hf.le_of_le_below ((hW (p + 1)).1.trans (hr1i p)) (hF p).1 (by
        erw [(hW (p + 1)).2, (hF p).2]; exact cW1_le_cF hc p)
    choose T2 hT2 using fun p : Fin M => lup (F p) (cT2 hc p)
      (by erw [(hF p).2]; exact cF_le_cT2 hc p)
    choose V hV using fun p : Fin M => ldown (T2 p) (cV hc p)
      (by erw [(hT2 p).2]; exact cV_le_cT2 hc p)
    choose D hD using fun p : Fin M => ldown (T2 p) (cD hc p)
      (by erw [(hT2 p).2]; exact cD_le_cT2 hc p)
    choose G hG using fun p : Fin M => ldown (T2 p) (cG hc p)
      (by erw [(hT2 p).2]; exact cG_le_cT2 hc p)
    have hvd (p : Fin M) : V p ≤ D p := hf.le_of_le_below (hV p).1 (hD p).1 (by
      erw [(hV p).2, (hD p).2]; exact cV_le_cD hc p)
    have hwd (p : Fin M) : W p ≤ D p := hf.le_of_le_below
      ((hwf p).trans (hT2 p).1) (hD p).1 (by
        erw [(hW p).2, (hD p).2]; exact cW_le_cD hc p)
    have hvg (p : Fin M) : V p ≤ G p := hf.le_of_le_below (hV p).1 (hG p).1 (by
      erw [(hV p).2, (hG p).2]; exact cV_le_cG hc p)
    have hw1g (p : Fin M) : W (p + 1) ≤ G p := hf.le_of_le_below
      ((hw1f p).trans (hT2 p).1) (hG p).1 (by
        erw [(hW (p + 1)).2, (hG p).2]; exact cW1_le_cG hc p)
    choose T1 hT1 using fun p : Fin M => lup (G p) (cT1 hc p)
      (by erw [(hG p).2]; exact cG_le_cT1 hc p)
    have hd1t1 (p : Fin M) : D (p + 1) ≤ T1 p := hf.le_of_le_above
      (hwd (p + 1)) ((hw1g p).trans (hT1 p).1) (by
        erw [(hD (p + 1)).2, (hT1 p).2]; exact cD1_le_cT1 hc p)
    choose E hE using fun p : Fin M => ldown (T1 p) (cE hc p)
      (by erw [(hT1 p).2]; exact cE_le_cT1 hc p)
    have hve (p : Fin M) : V p ≤ E p := hf.le_of_le_below
      ((hvg p).trans (hT1 p).1) (hE p).1 (by
        erw [(hV p).2, (hE p).2]; exact cV_le_cE hc p)
    have hv1e (p : Fin M) : V (p + 1) ≤ E p := hf.le_of_le_below
      ((hvd (p + 1)).trans (hd1t1 p)) (hE p).1 (by
        erw [(hV (p + 1)).2, (hE p).2]; exact cV1_le_cE hc p)
    exact ⟨{
      V := V, W := W, E := E, D := D, G := G, F := F, R := R,
      T1 := T1, T2 := T2, I := I,
      projV := fun p => (hV p).2, projW := fun p => (hW p).2,
      projE := fun p => (hE p).2, projD := fun p => (hD p).2,
      projG := fun p => (hG p).2, projF := fun p => (hF p).2,
      projR := fun p => (hR p).2, projT1 := fun p => (hT1 p).2,
      projT2 := fun p => (hT2 p).2, projI := fun p => (hI p).2,
      ve := hve, v1e := hv1e, vd := hvd, wd := hwd, vg := hvg, w1g := hw1g,
      wf := hwf, w1f := hw1f, cr := fun p => (hR p).1,
      wr := fun p => (hW p).1, et1 := fun p => (hE p).1,
      d1t1 := hd1t1, gt1 := fun p => (hT1 p).1,
      gt2 := fun p => (hG p).1, ft2 := fun p => (hT2 p).1,
      dt2 := fun p => (hD p).1, ri := hri, fi := fun p => (hF p).1,
      r1i := hr1i }⟩)

namespace CoveredPolygon
variable {hc f}
variable {v : PolygonCoverPole hc f} (D : CoveredPolygon hc f v)

def sector (p : Fin M) : Nerve.Ch P :=
  triangleFlagChain (D.V p) (D.V (p + 1)) (D.W (p + 1))
    (D.E p) (D.D (p + 1)) (D.G p) (D.T1 p) +
  triangleFlagChain (D.V p) (D.W (p + 1)) (D.W p)
    (D.G p) (D.F p) (D.D p) (D.T2 p) +
  triangleFlagChain v.1 (D.W p) (D.W (p + 1))
    (D.R p) (D.F p) (D.R (p + 1)) (D.I p)

def fundamental : Nerve.Ch P := ∑ p : Fin M, D.sector p

theorem sector_mem_inc (p : Fin M) : D.sector p ∈ Nerve.Inc P := by
  exact (Nerve.Inc _).add_mem ((Nerve.Inc _).add_mem
    (triangleFlagChain_mem_inc (D.ve p) (D.v1e p) (D.vd (p + 1)) (D.wd (p + 1))
      (D.w1g p) (D.vg p) (D.et1 p) (D.d1t1 p) (D.gt1 p))
    (triangleFlagChain_mem_inc (D.vg p) (D.w1g p) (D.w1f p) (D.wf p)
      (D.wd p) (D.vd p) (D.gt2 p) (D.ft2 p) (D.dt2 p)))
    (triangleFlagChain_mem_inc (D.cr p) (D.wr p) (D.wf p) (D.w1f p)
      (D.wr (p + 1)) (D.cr (p + 1)) (D.ri p) (D.fi p) (D.r1i p))

theorem fundamental_mem_inc : D.fundamental ∈ Nerve.Inc P :=
  (Nerve.Inc _).sum_mem (fun p _ => D.sector_mem_inc p)

theorem fundamental_degree : Nerve.lengthProjection 3 D.fundamental = D.fundamental := by
  simp [fundamental, sector, triangleFlagChain]

theorem sector_boundary (p : Fin M) :
    Nerve.bdry (D.sector p) =
      flagEdge (D.V p) (D.V (p + 1)) (D.E p) +
      flagEdge (D.V (p + 1)) (D.W (p + 1)) (D.D (p + 1)) -
      flagEdge (D.V p) (D.W p) (D.D p) +
      flagEdge v.1 (D.W p) (D.R p) -
      flagEdge v.1 (D.W (p + 1)) (D.R (p + 1)) := by
  simp only [sector, map_add, bdry_triangleFlagChain, flagEdge]
  abel

/-- All lifted collar and radial terms cancel before any projection. -/

def cellularFundamental : StrictOrdTri P →₀ ℤ :=
  normalizeOrdChain2 (decodeOrdNerve2 D.fundamental)


def boundaryEdges : OrdEdge P →₀ ℤ :=
  ∑ p : Fin M,
    (Finsupp.single ⟨(D.V p, D.E p), D.ve p⟩ 1 -
      Finsupp.single ⟨(D.V (p + 1), D.E p), D.v1e p⟩ 1)


theorem decodedFundamental_boundary :
    Comb.bdry2 (orderCx P) (decodeOrdNerve2 D.fundamental) = D.boundaryEdges := by
  apply ordNerveChain1_injective
  erw [ordNerveChain1_bdry2, ordNerveChain2_decode D.fundamental_mem_inc,
    D.fundamental_degree, (show Nerve.bdry D.fundamental =
      ∑ p : Fin M, flagEdge (D.V p) (D.V (p + 1)) (D.E p) by
      have hshift (g : Fin M → Nerve.Ch P) : (∑ p : Fin M, g (p + 1)) = ∑ p : Fin M, g p :=
        Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun _ => rfl)
      simp only [fundamental, map_sum, sector_boundary,
        Finset.sum_add_distrib, Finset.sum_sub_distrib]
      grind), (show ordNerveChain1 D.boundaryEdges =
    ∑ p : Fin M, flagEdge (D.V p) (D.V (p + 1)) (D.E p) by
      simp [boundaryEdges, ordNerveChain1, flagEdge])]

theorem V_ne_E (p : Fin M) : D.V p ≠ D.E p := by
  intro h
  have hh := congrArg f h
  erw [D.projV, D.projE] at hh
  cases hh

theorem V1_ne_E (p : Fin M) : D.V (p + 1) ≠ D.E p := by
  intro h
  have hh := congrArg f h
  erw [D.projV, D.projE] at hh
  cases hh

def boundaryEdgeLeft (p : Fin M) : StrictOrdEdge P :=
  ⟨(D.V p, D.E p), lt_of_le_of_ne (D.ve p) (D.V_ne_E p)⟩

def boundaryEdgeRight (p : Fin M) : StrictOrdEdge P :=
  ⟨(D.V (p + 1), D.E p), lt_of_le_of_ne (D.v1e p) (D.V1_ne_E p)⟩

/-- The boundary of the genuine normalized lifted filling consists exactly of
the lifted polygon sides, with their actual endpoints and coefficients. -/

theorem cellularFundamental_relative : PolygonRelativeChain hc f D.cellularFundamental := by
  intro e he
  have hn  :=
    Finsupp.mem_support_iff.mp he
  have hleft p :
      InPolygonBoundary hc (f (D.boundaryEdgeLeft p).1.1) ∧
        InPolygonBoundary hc (f (D.boundaryEdgeLeft p).1.2) := by
    erw [D.projV, D.projE]
    exact ⟨trivial, trivial⟩
  have hright p :
      InPolygonBoundary hc (f (D.boundaryEdgeRight p).1.1) ∧
        InPolygonBoundary hc (f (D.boundaryEdgeRight p).1.2) := by
    erw [D.projV, D.projE]
    exact ⟨trivial, trivial⟩
  by_contra hb
  have hneL p : D.boundaryEdgeLeft p ≠ e := by
    intro hh
    exact hb (hh ▸ hleft p)
  have hneR p : D.boundaryEdgeRight p ≠ e := by
    intro hh
    exact hb (hh ▸ hright p)
  apply hn
  erw [(show Comb.bdry2 (strictOrderCx P) D.cellularFundamental =
    ∑ p : Fin M, (Finsupp.single (D.boundaryEdgeLeft p) 1 -
      Finsupp.single (D.boundaryEdgeRight p) 1) by
    erw [cellularFundamental, bdry2_normalizeOrdChain2, D.decodedFundamental_boundary]
    simp [boundaryEdges, normalizeOrdEdge, D.V_ne_E, D.V1_ne_E,
      boundaryEdgeLeft, boundaryEdgeRight])]
  simp [hneL, hneR]

variable (hc f)

/-- The chosen lift has coefficient one at its own pole and zero at every
other pole.  This computes the full lifted coefficients before any projection. -/
theorem cellularFundamental_pole_coefficient (hM : 2 ≤ M)
    (u : PolygonCoverPole hc f) :
    D.cellularFundamental (polygonCoverPoleFlag hc f hf u) = if v = u then 1 else 0 := by
  let t := polygonCoverPoleFlag hc f hf u
  have ht := polygonCoverPoleFlagPlus_projection hc f hf u.1 u.2 0
  have hv p : D.V p ≠ t.1.1 := by
    intro h
    have hh := (D.projV p).symm.trans ((congrArg f h).trans ht.1)
    cases hh
  have hw p : D.W p ≠ t.1.1 := by
    intro h
    have hh := (D.projW p).symm.trans ((congrArg f h).trans ht.1)
    cases hh
  have hplus p :
      [v.1, D.R p, D.I p] = [t.1.1, t.1.2.1, t.1.2.2] ↔ v = u ∧ p = 0 := by
    constructor
    · intro h
      simp at h
      have hpu : p = 0 := by
        have hh := (D.projI p).symm.trans ((congrArg f h.2.2).trans ht.2.2)
        exact Cell.inn.inj hh
      exact ⟨Subtype.ext h.1, hpu⟩
    · rintro ⟨rfl, rfl⟩
      have hr  := hf.up_inj (D.cr 0) t.2.1.le
        ((D.projR 0).trans ht.2.1.symm)
      have hi  := hf.up_inj ((D.cr 0).trans (D.ri 0))
        (t.2.1.trans t.2.2).le ((D.projI 0).trans ht.2.2.symm)
      simp only [hr, hi]
      rfl
  have hminus (p : Fin M) :
      [v.1, D.R (p + 1), D.I p] ≠ [t.1.1, t.1.2.1, t.1.2.2] := by
    intro h
    simp only [List.cons.injEq, and_true] at h
    have hp : p = 0 := by
      have hh := (D.projI p).symm.trans ((congrArg f h.2.2).trans ht.2.2)
      exact Cell.inn.inj hh
    have hp' : p + 1 = 0 := by
      have hh := (D.projR (p + 1)).symm.trans ((congrArg f h.2.1).trans ht.2.1)
      exact Cell.rad.inj hh
    exact fin_succ_ne_self hM p (hp'.trans hp.symm)
  change D.cellularFundamental t = _
  rw (config := { transparency := .default }) [(show D.cellularFundamental t = ordTriangleCoefficient ((strictOrderIncl P).onF t)
      D.fundamental by
    erw [cellularFundamental, normalizeOrdChain2_apply, ← ordTriangleCoefficient_encode,
      ordNerveChain2_decode D.fundamental_mem_inc, D.fundamental_degree])]
  simp only [fundamental, sector, triangleFlagChain, map_sum, map_add, map_sub,
    ordTriangleCoefficient, FreeAbelianGroup.lift_apply_of, strictOrderIncl]
  simp only [hplus, hminus, if_false]
  simp only [List.cons.injEq, and_true, hv, hw, false_and, if_false,
    sub_zero, zero_add, add_zero]
  by_cases h : v = u <;> simp [h]


end CoveredPolygon

/-- The actual oriented polygon filling attached to one actual pole lift. -/
def polygonCoverFilling (v : PolygonCoverPole hc f) : StrictOrdTri P →₀ ℤ :=
  (coveredPolygon hc f hf v).cellularFundamental



/-- Reconstruct a finite relative two-chain from its actual polygon coefficients. -/
def polygonCoverReconstruct :
    (PolygonCoverPole hc f →₀ ℤ) →ₗ[ℤ] (StrictOrdTri P →₀ ℤ) :=
  Finsupp.linearCombination ℤ (polygonCoverFilling hc f hf)

theorem polygonCoverReconstruct_relative (a : PolygonCoverPole hc f →₀ ℤ) :
    PolygonRelativeChain hc f (polygonCoverReconstruct hc f hf a) := by
  induction a using Finsupp.induction_linear with
  | zero => erw [map_zero]; exact PolygonRelativeChain.zero hc f
  | add a b ha hb =>
    erw [map_add]
    exact PolygonRelativeChain.add hc f ha hb
  | single v n =>
    erw [polygonCoverReconstruct, Finsupp.linearCombination_single]
    exact PolygonRelativeChain.smul hc f ((coveredPolygon hc f hf v).cellularFundamental_relative) n

theorem polygonCoverReconstruct_coefficients (hM : 2 ≤ M)
    (a : PolygonCoverPole hc f →₀ ℤ) :
    polygonCoverPoleCoefficients hc f hf (polygonCoverReconstruct hc f hf a) = a := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp_all
  | single v n =>
    erw [polygonCoverReconstruct, Finsupp.linearCombination_single, map_smul,
      (show polygonCoverPoleCoefficients hc f hf (coveredPolygon hc f hf v).cellularFundamental = Finsupp.single v 1 by
        ext u
        erw [polygonCoverPoleCoefficients_apply,
          CoveredPolygon.cellularFundamental_pole_coefficient hc f hf (coveredPolygon hc f hf v) hM u]
        simp only [Finsupp.single_apply])]
    simp [Finsupp.smul_single]

/-- Every genuine relative two-chain in every actual surface cover is exactly
the finite sum of genuine lifted polygon fillings with its actual pole
coefficients.  All internal flags and the collar are included. -/
theorem polygonRelative_reconstruct (hd : PolygonData vc ec)
    (c : StrictOrdTri P →₀ ℤ) (hrel : PolygonRelativeChain hc f c) :
    c = polygonCoverReconstruct hc f hf (polygonCoverPoleCoefficients hc f hf c) := by
  apply polygonRelative_ext hc hd f hf c _ hrel (polygonCoverReconstruct_relative hc f hf _)
  symm
  apply polygonCoverReconstruct_coefficients hc f hf
  have := hd.three_le
  omega

namespace Genus
variable (q : ℕ) [NeZero q] (f : P → SCell (gvc q) (gec q) (gc q))
  (hf : IsPosetCover f)

end Genus
end FiniteChains.Davis
end

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis
open Comb Cell
variable {κ ι P Q : Type} {M : ℕ} [NeZero M] [PartialOrder P] [PartialOrder Q]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)
  (f : P → SCell vc ec hc) (hf : IsPosetCover f)

namespace CoveredPolygon
variable {v : PolygonCoverPole hc f} (D E : CoveredPolygon hc f v)

include hf in
/-- All positions in a lifted polygon are forced by its centre, including the
identified boundary positions. This removes all dependence on interval choices. -/
theorem fundamental_unique : D.fundamental = E.fundamental := by
  have hR  := funext fun p => hf.up_inj (D.cr p) (E.cr p)
    ((D.projR p).trans (E.projR p).symm)
  have hI  := funext fun p => hf.up_inj
    ((D.cr p).trans (D.ri p)) ((E.cr p).trans (E.ri p))
    ((D.projI p).trans (E.projI p).symm)
  have hW  := funext fun p => hf.down_inj (D.wr p)
    (by erw [hR]; exact E.wr p) ((D.projW p).trans (E.projW p).symm)
  have hF  := funext fun p => hf.down_inj (D.fi p)
    (by erw [hI]; exact E.fi p) ((D.projF p).trans (E.projF p).symm)
  have hT2  := funext fun p => hf.up_inj (D.ft2 p)
    (by erw [hF]; exact E.ft2 p) ((D.projT2 p).trans (E.projT2 p).symm)
  have hV  := funext fun p => hf.down_inj
    ((D.vd p).trans (D.dt2 p))
    (by erw [hT2]; exact (E.vd p).trans (E.dt2 p))
    ((D.projV p).trans (E.projV p).symm)
  have hD  := funext fun p => hf.down_inj (D.dt2 p)
    (by erw [hT2]; exact E.dt2 p) ((D.projD p).trans (E.projD p).symm)
  have hG  := funext fun p => hf.down_inj (D.gt2 p)
    (by erw [hT2]; exact E.gt2 p) ((D.projG p).trans (E.projG p).symm)
  have hT1  := funext fun p => hf.up_inj (D.gt1 p)
    (by erw [hG]; exact E.gt1 p) ((D.projT1 p).trans (E.projT1 p).symm)
  have hE  := funext fun p => hf.down_inj (D.et1 p)
    (by rw (config := { transparency := .default }) [hT1]; exact E.et1 p) ((D.projE p).trans (E.projE p).symm)
  simp only [fundamental, sector, hR, hI, hW, hF, hT2, hV, hD, hG, hT1, hE]

include hf in
theorem cellularFundamental_unique : D.cellularFundamental = E.cellularFundamental := by grind [cellularFundamental, fundamental_unique]

variable (g : Q → SCell vc ec hc) (h : P → Q) (hm : Monotone h)
  (hp : ∀ p, g (h p) = f p)

def mapPole : PolygonCoverPole hc g := ⟨h v.1, (hp v.1).trans v.2⟩

/-- Mapping every actual polygon position through a map of covers preserves
the complete disk diagram. -/
def map : CoveredPolygon hc g (mapPole hc f g h hp (v := v)) where
  V := h ∘ D.V
  W := h ∘ D.W
  E := h ∘ D.E
  D := h ∘ D.D
  G := h ∘ D.G
  F := h ∘ D.F
  R := h ∘ D.R
  T1 := h ∘ D.T1
  T2 := h ∘ D.T2
  I := h ∘ D.I
  projV p := (hp _).trans (D.projV p)
  projW p := (hp _).trans (D.projW p)
  projE p := (hp _).trans (D.projE p)
  projD p := (hp _).trans (D.projD p)
  projG p := (hp _).trans (D.projG p)
  projF p := (hp _).trans (D.projF p)
  projR p := (hp _).trans (D.projR p)
  projT1 p := (hp _).trans (D.projT1 p)
  projT2 p := (hp _).trans (D.projT2 p)
  projI p := (hp _).trans (D.projI p)
  ve p := hm (D.ve p)
  v1e p := hm (D.v1e p)
  vd p := hm (D.vd p)
  wd p := hm (D.wd p)
  vg p := hm (D.vg p)
  w1g p := hm (D.w1g p)
  wf p := hm (D.wf p)
  w1f p := hm (D.w1f p)
  cr p := hm (D.cr p)
  wr p := hm (D.wr p)
  et1 p := hm (D.et1 p)
  d1t1 p := hm (D.d1t1 p)
  gt1 p := hm (D.gt1 p)
  gt2 p := hm (D.gt2 p)
  ft2 p := hm (D.ft2 p)
  dt2 p := hm (D.dt2 p)
  ri p := hm (D.ri p)
  fi p := hm (D.fi p)
  r1i p := hm (D.r1i p)

theorem map_fundamental :
    (D.map hc f g h hm hp).fundamental = Nerve.cmap h D.fundamental := by
  simp only [fundamental, sector, map, triangleFlagChain, map_add, map_sub, map_sum,
    Nerve.cmap_of, List.map_cons, List.map_nil, Function.comp_apply, mapPole]

theorem map_cellularFundamental (hs : StrictMono h) :
    (D.map hc f g h hm hp).cellularFundamental =
      chain2 (strictOrderCxMap h hs) D.cellularFundamental := by
  have he : decodeOrdNerve2 ((D.map hc f g h hm hp).fundamental) =
      chain2 (orderCxMap h hs.monotone) (decodeOrdNerve2 D.fundamental) := by
    apply ordNerveChain2_injective
    erw [ordNerveChain2_decode (D.map hc f g h hm hp).fundamental_mem_inc,
      (D.map hc f g h hm hp).fundamental_degree, ordNerveChain2_chain2,
      ordNerveChain2_decode D.fundamental_mem_inc, D.fundamental_degree,
      map_fundamental]
  erw [cellularFundamental, he, normalizeOrdChain2_strict_map]
  rfl

end CoveredPolygon

/-- Canonical lifted polygon fillings are natural under genuine strict maps of
surface covers. No equivariant choice is imposed on interval lifts. -/
theorem polygonCoverFilling_map
    (g : Q → SCell vc ec hc) (hg : IsPosetCover g)
    (h : P → Q) (hs : StrictMono h) (hp : ∀ p, g (h p) = f p)
    (v : PolygonCoverPole hc f) :
    chain2 (strictOrderCxMap h hs) (polygonCoverFilling hc f hf v) =
      polygonCoverFilling hc g hg ⟨h v.1, (hp v.1).trans v.2⟩ := by
  let D := coveredPolygon hc f hf v
  erw [show polygonCoverFilling hc f hf v = D.cellularFundamental from rfl,
    ← CoveredPolygon.map_cellularFundamental hc f D g h hs.monotone hp hs]
  exact CoveredPolygon.cellularFundamental_unique hc g hg _ _

/-- With an actual transitive deck parametrization of the pole fibre, the
finite sheet coefficient is precisely a group-ring multiple of one canonical
polygon filling. -/
theorem polygonRelative_eq_deck_sum (hd : PolygonData vc ec)
    {G : Type} [Group G] (deck : G → P ≃o P)
    (hdeck : ∀ g p, f (deck g p) = f p)
    (v : PolygonCoverPole hc f) (e : G ≃ PolygonCoverPole hc f)
    (he : ∀ g, (e g).1 = deck g v.1)
    (c : StrictOrdTri P →₀ ℤ) (hrel : PolygonRelativeChain hc f c) :
    c = Finsupp.linearCombination ℤ
      (fun g : G => chain2 (strictOrderCxMap (deck g) (deck g).strictMono)
        (polygonCoverFilling hc f hf v))
      (polygonCoverGroupCoefficient hc f hf e.symm c).coeff := by
  have hsum a :
      polygonCoverReconstruct hc f hf a = Finsupp.linearCombination ℤ
        (fun g : G => chain2 (strictOrderCxMap (deck g) (deck g).strictMono)
          (polygonCoverFilling hc f hf v)) (Finsupp.mapDomain e.symm a) := by
    induction a using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp_all
    | single w n =>
      erw [polygonCoverReconstruct, Finsupp.linearCombination_single,
        Finsupp.mapDomain_single, Finsupp.linearCombination_single,
        polygonCoverFilling_map hc f hf f hf (deck (e.symm w))
          (deck (e.symm w)).strictMono (hdeck (e.symm w)) v]
      apply congrArg (fun x => n • polygonCoverFilling hc f hf x)
      ext
      have hh := he (e.symm w)
      simpa using hh
  exact (polygonRelative_reconstruct hc f hf hd c hrel).trans
    (hsum (polygonCoverPoleCoefficients hc f hf c))

end FiniteChains.Davis
end

section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily

variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)

abbrev NamedPolygonDeckGroup :=
  Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)

/-- The genuine deck action on the first coordinate of the actual surface
pullback cover; the surface cell itself remains fixed. -/
def namedSurfaceDeck (g : NamedPolygonDeckGroup ρ q u) :
    NamedSurfaceCover ρ q u ≃o NamedSurfaceCover ρ q u where
  toFun p := ⟨(uOrderDeck g p.1.1, p.1.2), (uOrderDeck_end g p.1.1).trans p.2⟩
  invFun p := ⟨(uOrderDeck g⁻¹ p.1.1, p.1.2), (uOrderDeck_end g⁻¹ p.1.1).trans p.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · change deckV g⁻¹ (deckV g p.1.1) = p.1.1
      rw [← deckV_mul, inv_mul_cancel, deckV_one]
    · rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · change deckV g (deckV g⁻¹ p.1.1) = p.1.1
      rw [← deckV_mul, mul_inv_cancel, deckV_one]
    · rfl
  map_rel_iff' {p r} := by
    change (uOrderDeck g p.1.1 ≤ uOrderDeck g r.1.1 ∧ p.1.2 ≤ r.1.2) ↔
      (p.1.1 ≤ r.1.1 ∧ p.1.2 ≤ r.1.2)
    exact and_congr (uOrderDeckOrderIso g).map_rel_iff Iff.rfl

@[simp] theorem namedSurfaceDeck_projection (g : NamedPolygonDeckGroup ρ q u)
    (p : NamedSurfaceCover ρ q u) :
    namedSurfaceProjection ρ q u (namedSurfaceDeck ρ q u g p) =
      namedSurfaceProjection ρ q u p := rfl


theorem namedSurfaceDeck_mul (g h : NamedPolygonDeckGroup ρ q u)
    (p : NamedSurfaceCover ρ q u) :
    namedSurfaceDeck ρ q u (g * h) p =
      namedSurfaceDeck ρ q u g (namedSurfaceDeck ρ q u h p) := by
  apply Subtype.ext
  exact Prod.ext (deckV_mul g h p.1.1) rfl

abbrev NamedPolygonPole := PolygonCoverPole (gc q) (namedSurfaceProjection ρ q u)

/-- One actual pole lift, chosen from the proved surjectivity of the actual
surface projection. -/
def namedPolygonPole : NamedPolygonPole ρ q u :=
  ⟨Classical.choose ((namedSurfaceProjection_isPosetCover ρ q u).surj (cC (gc q))),
    Classical.choose_spec ((namedSurfaceProjection_isPosetCover ρ q u).surj (cC (gc q)))⟩

def namedPolygonPoleOrbit (g : NamedPolygonDeckGroup ρ q u) : NamedPolygonPole ρ q u :=
  ⟨namedSurfaceDeck ρ q u g (namedPolygonPole ρ q u).1, (namedPolygonPole ρ q u).2⟩

/-- Regularity applies on the exact original universal-cover endpoint fibre;
the pullback's surface coordinate is fixed at the polygon centre. -/
theorem namedPolygonPoleOrbit_bijective :
    Function.Bijective (namedPolygonPoleOrbit ρ q u) := by
  constructor
  · intro g h he
    have hfirst := congrArg (fun p : NamedPolygonPole ρ q u => p.1.1.1) he
    obtain ⟨d, _, hd⟩ := (isRegular_univProj
      (X := orderCx (namedQuotientPos ρ q u))).simply_transitive
      (namedPolygonPole ρ q u).1.1.1
      (deckV g (namedPolygonPole ρ q u).1.1.1)
      (endV_deckV g (namedPolygonPole ρ q u).1.1.1).symm
    exact (hd g rfl).trans (hd h hfirst.symm).symm
  · intro v
    let v₀ := namedPolygonPole ρ q u
    have hcell  := v₀.2.trans v.2.symm
    have hend  :=
      v₀.1.2.trans ((congrArg (fun x =>
        qNew (namedSurfaceLabel ρ q u x)) hcell).trans v.1.2.symm)
    obtain ⟨g, hg, _⟩ := (isRegular_univProj
     ).simply_transitive
      v₀.1.1.1 v.1.1.1 hend
    refine ⟨g, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext hg hcell

/-- The actual quotient fundamental group, rather than any hypothesized block
embedding, indexes the complete pole fibre. -/
def namedPolygonPoleEquiv : NamedPolygonDeckGroup ρ q u ≃ NamedPolygonPole ρ q u :=
  Equiv.ofBijective (namedPolygonPoleOrbit ρ q u) (namedPolygonPoleOrbit_bijective ρ q u)

@[simp] theorem namedPolygonPoleEquiv_apply (g : NamedPolygonDeckGroup ρ q u) :
    (namedPolygonPoleEquiv ρ q u g).1 =
      namedSurfaceDeck ρ q u g (namedPolygonPole ρ q u).1 := rfl

/-- Rebase the actual sheet coordinates at any prescribed actual pole. This
allows the reference pole to be transported from the pre-substitution cover. -/
def namedPolygonPoleEquivAt (v : NamedPolygonPole ρ q u) :
    NamedPolygonDeckGroup ρ q u ≃ NamedPolygonPole ρ q u :=
  (Equiv.mulRight ((namedPolygonPoleEquiv ρ q u).symm v)).trans
    (namedPolygonPoleEquiv ρ q u)

theorem namedPolygonPoleEquivAt_apply (v : NamedPolygonPole ρ q u)
    (g : NamedPolygonDeckGroup ρ q u) :
    (namedPolygonPoleEquivAt ρ q u v g).1 = namedSurfaceDeck ρ q u g v.1 := by
  change (namedPolygonPoleEquiv ρ q u (g * (namedPolygonPoleEquiv ρ q u).symm v)).1 = _
  rw [namedPolygonPoleEquiv_apply, namedSurfaceDeck_mul]
  have he := congrArg Subtype.val ((namedPolygonPoleEquiv ρ q u).apply_symm_apply v)
  rw [namedPolygonPoleEquiv_apply] at he
  rw [he]


def namedPolygonCoefficientAt (v : NamedPolygonPole ρ q u)
    (c : StrictOrdTri (NamedSurfaceCover ρ q u) →₀ ℤ) :
    MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u) :=
  polygonCoverGroupCoefficient (gc q) (namedSurfaceProjection ρ q u)
    (namedSurfaceProjection_isPosetCover ρ q u) (namedPolygonPoleEquivAt ρ q u v).symm c

def namedPolygonFillingAt (v : NamedPolygonPole ρ q u) :
    StrictOrdTri (NamedSurfaceCover ρ q u) →₀ ℤ :=
  polygonCoverFilling (gc q) (namedSurfaceProjection ρ q u)
    (namedSurfaceProjection_isPosetCover ρ q u) v

def namedPolygonMultipleAt (v : NamedPolygonPole ρ q u) :
    MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u) →ₗ[ℤ]
      (StrictOrdTri (NamedSurfaceCover ρ q u) →₀ ℤ) :=
  (Finsupp.linearCombination ℤ (fun g => chain2
    (strictOrderCxMap (namedSurfaceDeck ρ q u g) (namedSurfaceDeck ρ q u g).strictMono)
    (namedPolygonFillingAt ρ q u v))).comp (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap

/-- The actual scalar reconstruction can be based at the particular pole
arising from the chosen pre-substitution geometric reference. -/
theorem namedPolygon_reconstruct_at_pole (v : NamedPolygonPole ρ q u)
    (c : StrictOrdTri (NamedSurfaceCover ρ q u) →₀ ℤ)
    (hrel : PolygonRelativeChain (gc q) (namedSurfaceProjection ρ q u) c) :
    c = namedPolygonMultipleAt ρ q u v (namedPolygonCoefficientAt ρ q u v c) :=
  polygonRelative_eq_deck_sum (gc q) (namedSurfaceProjection ρ q u)
    (namedSurfaceProjection_isPosetCover ρ q u) (genus_polygonData q)
    (namedSurfaceDeck ρ q u) (namedSurfaceDeck_projection ρ q u)
    v (namedPolygonPoleEquivAt ρ q u v) (namedPolygonPoleEquivAt_apply ρ q u v) c hrel

end FiniteChains.Davis.Genus
end

namespace FiniteChains.Nerve
universe u
variable {P : Type u} [Preorder P]

/-- A homogeneous chain in `B` that bounds in `U` already bounds in `B`. -/
def ReflectsBoundsIn (U B : P → Prop) (n : ℕ) : Prop :=
  ∀ c ∈ IncOn B, lengthProjection n c = c →
    (∃ y ∈ IncOn U, bdry y = c) → ∃ y ∈ IncOn B, bdry y = c

/-- The injectivity half of the chain gluing argument. Only intersection cycles
in the degree of the chain being filled need to bound. -/
theorem reflectsBoundsIn_union_of_unmixed {A B U : P → Prop} {n : ℕ}
    (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b))
    (hJ : FillsDegreeIn (fun p => A p ∧ B p) n) : ReflectsBoundsIn U A n := by
  intro c hc hd hbound
  obtain ⟨y, hy, hdy⟩ := hbound
  obtain ⟨a₀, ha₀, b₀, hb₀, hsplit⟩ := exists_split_of_unmixed hmix hy
  let a := lengthProjection (n + 1) a₀
  let b := lengthProjection (n + 1) b₀
  have ha : a ∈ IncOn A := lengthProjection_mem_incOn _ ha₀
  have hb : b ∈ IncOn B := lengthProjection_mem_incOn _ hb₀
  have hsum : bdry a + bdry b = c := by
    rw [← map_add, ← map_add, ← hsplit, ← lengthProjection_bdry, hdy, hd]
  have hdbA : bdry b ∈ IncOn A := by
    have he : bdry b = c - bdry a := by rw [← hsum]; abel
    rw [he]
    exact AddSubgroup.sub_mem _ hc (bdry_mem_incOn ha)
  have hdbJ : bdry b ∈ IncOn (fun p => A p ∧ B p) := by
    rw [← incOn_inf]
    exact ⟨hdbA, bdry_mem_incOn hb⟩
  have hdbd : lengthProjection n (bdry b) = bdry b := by
    rw [lengthProjection_bdry]
    exact congrArg bdry (lengthProjection_idempotent _ _)
  obtain ⟨z, hz, hdz⟩ := hJ (bdry b) hdbJ hdbd (by simp [bdry_bdry])
  refine ⟨a + z, AddSubgroup.add_mem _ ha (incOn_mono (fun _ h => h.1) hz), ?_⟩
  rw [map_add, hdz, hsum]

theorem reflectsBoundsIn_trans {U B C : P → Prop} {n : ℕ}
    (hCB : ∀ p, C p → B p) (hUB : ReflectsBoundsIn U B n)
    (hBC : ReflectsBoundsIn B C n) : ReflectsBoundsIn U C n := by
  intro c hc hd hbound
  exact hBC c hc hd (hUB c (incOn_mono hCB hc) hd hbound)

end FiniteChains.Nerve

namespace FiniteChains.Nerve
universe u
variable {P : Type u} [Preorder P]

/-- Ambient generation and one-degree-lower fillings in the other piece give
actual relative fillings in the first piece. The input is not assumed to be a cycle. -/
theorem relative_filling_intersection_of_ambient {A B U : P → Prop} {n : ℕ}
    (hAU : ∀ p, A p → U p) (hBU : ∀ p, B p → U p)
    (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b))
    (hgen : GeneratesDegreeIn U B (n + 1)) (hfill : FillsDegreeIn B n)
    (z : Ch P) (hz : z ∈ IncOn A) (hd : lengthProjection (n + 1) z = z)
    (hdz : bdry z ∈ IncOn B) :
    ∃ t ∈ IncOn (fun p => A p ∧ B p), lengthProjection (n + 1) t = t ∧
      bdry t = bdry z ∧ ∃ y ∈ IncOn A, lengthProjection (n + 2) y = y ∧
        z = t + bdry y := by
  have hdd : lengthProjection n (bdry z) = bdry z := by
    rw [lengthProjection_bdry, hd]
  obtain ⟨v₀, hv₀, hdv₀⟩ := hfill (bdry z) hdz hdd (bdry_bdry z)
  let v := lengthProjection (n + 1) v₀
  have hv : v ∈ IncOn B := lengthProjection_mem_incOn _ hv₀
  have hvd : lengthProjection (n + 1) v = v := lengthProjection_idempotent _ _
  have hdv : bdry v = bdry z := by
    rw [← lengthProjection_bdry, hdv₀, hdd]
  obtain ⟨c, hc, y, hy, _, he⟩ := hgen (z - v)
    (AddSubgroup.sub_mem _ (incOn_mono hAU hz) (incOn_mono hBU hv))
    (by rw [map_sub, hd, hvd]) (by rw [map_sub, hdv, sub_self])
  obtain ⟨a, ha, b, hb, hyab⟩ := exists_split_of_unmixed hmix hy
  let t₀ := z - bdry a
  have htA  := AddSubgroup.sub_mem _ hz (bdry_mem_incOn ha)
  have htB : t₀ ∈ IncOn B := by
    have ht : t₀ = v + c + bdry b := by
      rw [hyab, map_add] at he
      dsimp only [t₀]
      linear_combination (norm := abel) he
    rw [ht]
    exact AddSubgroup.add_mem _ (AddSubgroup.add_mem _ hv hc) (bdry_mem_incOn hb)
  have htJ : t₀ ∈ IncOn (fun p => A p ∧ B p) := by
    rw [← incOn_inf]
    exact ⟨htA, htB⟩
  have hdt : bdry t₀ = bdry z := by simp only [t₀, map_sub, bdry_bdry, sub_zero]
  have he₀ : z = t₀ + bdry a := by dsimp only [t₀]; abel
  refine ⟨lengthProjection (n + 1) t₀, lengthProjection_mem_incOn _ htJ,
    lengthProjection_idempotent _ _, ?_, lengthProjection (n + 2) a,
    lengthProjection_mem_incOn _ ha, lengthProjection_idempotent _ _, ?_⟩
  · rw [← lengthProjection_bdry, hdt, hdd]
  · have h := congrArg (lengthProjection (n + 1)) he₀
    rw [hd, map_add, lengthProjection_bdry] at h
    exact h

end FiniteChains.Nerve

namespace FiniteChains.Nerve
universe u
variable {P Q : Type u} [Preorder P] [Preorder Q]

theorem filling_of_lower_composite (r : P → Q) (s : Q → P)
    (hr : Monotone r) (hs : Monotone s) (hle : ∀ p, s (r p) ≤ p) (n : ℕ)
    (hfill : ∀ c ∈ Inc Q, lengthProjection n c = c → bdry c = 0 →
      ∃ y ∈ Inc Q, bdry y = c)
    (c : Ch P) (hc : c ∈ Inc P) (hd : lengthProjection n c = c)
    (hcyc : bdry c = 0) : ∃ y ∈ Inc P, bdry y = c := by
  obtain ⟨b, hb, hdb⟩ := hfill (cmap r c) (cmap_mem_inc_of_monotone hr hc)
    (by rw [lengthProjection_cmap, hd]) (by rw [← cmap_bdry, hcyc, map_zero])
  have hp := bdry_prism_add_prism_bdry (s ∘ r) id c
  rw [hcyc, map_zero, add_zero, cmap_id] at hp
  refine ⟨cmap s b + prism (s ∘ r) id c,
    AddSubgroup.add_mem _ (cmap_mem_inc_of_monotone hs hb)
      (prism_mem_inc (hs.comp hr) monotone_id hle hc), ?_⟩
  rw [map_add, ← cmap_bdry, hdb, hp, cmap_comp]
  abel

end FiniteChains.Nerve

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

/-- A componentwise path contraction gives actual finite cellular fillings.
Connectedness or finiteness of the whole poset is not required. -/

theorem nerve_oneCycle_filling_of_simplyConnected (hsc : SimplyConnected (orderCx P))
    (c : Nerve.Ch P) (hi : c ∈ Nerve.Inc P)
    (hd : Nerve.lengthProjection 2 c = c) (hc : Nerve.bdry c = 0) :
    ∃ y ∈ Nerve.Inc P, Nerve.bdry y = c := by
  have he : ordNerveChain1 (decodeOrdNerve1 c) = c := by
    rw [ordNerveChain1_decode hi, hd]
  have hcyc  :=
    (ordNerveChain1_cycle_iff _).mp (by rw [he]; exact hc)
  obtain ⟨y, hy⟩ := (show ∃ y : OrdTri P →₀ ℤ, bdry2 (orderCx P) y = _ by
    let r  := fun v => Quotient.out (orderComponentLabel P v)
    have hr (e : OrdEdge P) : r e.1.1 = r e.1.2 :=
      congrArg Quotient.out (orderComponentLabel_eq_of_le e.2)
    have hreach v : Reach (orderCx P) (r v) v :=
      (orderComponentLabel_eq_iff _ _).mp (Quotient.out_eq _)
    choose p hp using hreach
    have hface e : ∃ y : OrdTri P →₀ ℤ,
        bdry2 (orderCx P) y = Finsupp.single e 1 + pathChain (p e.1.1) -
          pathChain (p e.1.2) := by
      let l := p e.1.1 ++ [(e, true)] ++ revPath (p e.1.2)
      have hrev : IsPath (orderCx P).src (orderCx P).tgt (revPath (p e.1.2))
          e.1.2 (r e.1.1) := by
        rw [hr e]
        exact isPath_revPath (hp e.1.2)
      have hl  :=
        ((hp e.1.1).append (show IsPath (orderCx P).src (orderCx P).tgt
          [(e, true)] e.1.1 e.1.2 from ⟨rfl, rfl⟩)).append hrev
      obtain ⟨y, hy⟩ := (hsc _ l hl).exists_boundary
      refine ⟨y, ?_⟩
      simpa [l, pathChain_append, pathChain_cons, pathChain_revPath,
        sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hy
    choose f hf using hface
    let s :=
      Finsupp.linearCombination ℤ (fun v => pathChain (p v))
    let t  :=
      Finsupp.linearCombination ℤ f
    have hs v : s (Finsupp.single v 1) = pathChain (p v) := by
      simp [s]
    have ht z : bdry2 (orderCx P) (t z) =
        z - s (bdry1 (orderCx P) z) := by
      induction z using Finsupp.induction_linear with
      | zero => simp
      | add z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add]; abel
      | single e n =>
        rw [Finsupp.linearCombination_single, map_smul, hf, bdry1_single,
          map_smul, map_sub, hs, hs, smul_sub, smul_add, smul_sub]
        simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
        simp only [orderCx]
        abel
    exact ⟨t _, by rw [ht, hcyc, map_zero, sub_zero]⟩)
  refine ⟨ordNerveChain2 y, ordNerveChain2_mem_inc y, ?_⟩
  rw [← ordNerveChain1_bdry2, hy, he]

end FiniteChains.Comb
end

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

/-- Every actual lifted nerve tetrahedron is an actual tetrahedron in the lifted order. -/
theorem uOrderTet_surjective : Function.Surjective (uOrderTet (P := P) (a := a)) := by
  rintro ⟨⟨v, t⟩, hv⟩
  have hv' : uOrderEnd v = t.1.1 := hv
  let h  := hv'.le.trans t.2.1
  let w := uOrderStep v t.1.2.1 h
  let h'  := (uOrderStep_end v _ h).le.trans t.2.2.1
  let z := uOrderStep w t.1.2.2.1 h'
  let h''  := (uOrderStep_end w _ h').le.trans t.2.2.2
  let r := uOrderStep z t.1.2.2.2 h''
  refine ⟨⟨(v, w, z, r), uOrderStep_le v _ h, uOrderStep_le w _ h',
    uOrderStep_le z _ h''⟩, ?_⟩
  exact Subtype.ext (Prod.ext rfl (Subtype.ext
    (Prod.ext hv (Prod.ext (uOrderStep_end v _ h)
      (Prod.ext (uOrderStep_end w _ h') (uOrderStep_end z _ h''))))))

/-- Genuine finite three-chains lift to genuine finite lifted-order three-chains. -/
theorem exists_uOrder_three_chain (c : UOrdTet P a →₀ ℤ) :
    ∃ d : OrdTet (UOrder P a) →₀ ℤ, Finsupp.mapDomain uOrderTet d = c :=
  Finsupp.mapDomain_surjective uOrderTet_surjective c

end FiniteChains.Comb

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
namespace FiniteChains.Davis
open RACG Mirror Comb Nerve
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

theorem qUniversal_generatesDegreeIn_base (x : X) (hx : IsConnected (orderCx X)) :
    GeneratesDegreeIn (fun _ : UOrder (Qpos A X att) (qNew x) => True)
      (fun p => InQBase (uOrderEnd p)) 3 := by
  letI : Nonempty X := ⟨x⟩
  let a : Zpos A X (IsGamma A) att := zNew ⟨1, isGamma_one⟩ x
  let S : Set (UOrder (Qpos A X att) (qNew x)) := {p | InQBase (uOrderEnd p)}
  intro c hc hd hcyc
  let z := decodeOrdNerve2 c
  have hz : ordNerveChain2 z = c := by
    erw [ordNerveChain2_decode (incOn_le_inc _ hc), hd]
  have hzc  :=
    (ordNerveChain2_cycle_iff z).mp (by rw (config := { transparency := .default }) [hz]; exact hcyc)
  have hgen := exists_qCover_base_cellular_cycle a
    (zpos_isConnected hx) (chain2 uOrderHom z) ((uOrderHom_cycle_iff z).mpr hzc)
  simp only [a, zProj_zNew] at hgen
  obtain ⟨d, hds, hdc, y, he⟩ := hgen
  obtain ⟨b, hbc, hbd⟩ := exists_qCover_base_cycle_preimage d hds hdc
  change (OrdTri S →₀ ℤ) at b
  have hbcN : Nerve.bdry (ordNerveChain2 b) = 0 :=
    (ordNerveChain2_cycle_iff b).mpr hbc
  obtain ⟨v, hv⟩ := exists_uOrder_three_chain y
  have hbd' : chain2 uOrderHom (chain2 (ordSubposetIncl S) b) = d := by
    change Finsupp.mapDomain uOrderFace (Finsupp.mapDomain (ordSubposetIncl S).onF b) = d
    rw (config := { transparency := .default }) [← Finsupp.mapDomain_comp]
    exact hbd
  let b' : OrdTri (UOrder (Qpos A X att) (qNew x)) →₀ ℤ :=
    chain2 (ordSubposetIncl S) b
  have hb' : chain2 uOrderHom b' = d := hbd'
  have hze : z = b' + ordBoundary3 v := by
    apply uOrderHom_chain2_injective
    rw (config := { transparency := .default }) [map_add, hb', uOrderHom_ordBoundary3, hv]
    exact he
  refine ⟨cmap Subtype.val (ordNerveChain2 b),
    cmap_val_mem_incOn _ (ordNerveChain2_mem_inc b), ordNerveChain3 v, ?_, ?_, ?_⟩
  · simpa only [cmap_id] using cmap_mem_incOn_of_maps (f := id) monotone_id
      (fun _ => True.intro) (ordNerveChain3_mem_inc v)
  · rw (config := { transparency := .default }) [← cmap_bdry, hbcN, map_zero]
  · rw (config := { transparency := .default }) [← hz, hze, map_add, ordNerveChain2_ordBoundary3]
    congr 1
    exact ordNerveChain2_chain2 Subtype.val monotone_subtypeVal b

end FiniteChains.Davis
end

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

abbrev QBaseStar := {p : Qpos A X att // InQBaseStar p}

def qBaseStarToBase : QBaseStar (att := att) → X
  | ⟨.inl c, hp⟩ => att (qPositiveOldSimplex ⟨.inl c, trivial, hp⟩)
  | ⟨.inr x, _⟩ => x


def qBaseStarRetraction (p : QBaseStar (att := att)) : Qpos A X att :=
  qNew (qBaseStarToBase p)

theorem qBaseStarRetraction_monotone : Monotone (qBaseStarRetraction (att := att)) :=
  qNew_monotone.comp (by
    rintro ⟨p, hp⟩ ⟨r, hr⟩ h
    cases p with
    | inl c =>
      cases r with
      | inl d => exact att.monotone h.1
      | inr y => exact False.elim h
    | inr x =>
      cases r with
      | inl d =>
        obtain ⟨_, hn, hh⟩ := h
        exact hh
      | inr y => exact h)

theorem qBaseStarRetraction_le (p : QBaseStar (att := att)) :
    qBaseStarRetraction p ≤ p.1 := by
  rcases p with ⟨p, hp⟩
  cases p with
  | inl c =>
    exact ⟨hp, Finset.nonempty_iff_ne_empty.mpr (fun h => c.2 ⟨h, hp⟩), le_refl _⟩
  | inr x => exact le_refl _

omit [DecidableEq V] in
theorem qBaseStarRetraction_mem_base (p : QBaseStar (att := att)) :
    InQBase (qBaseStarRetraction p) := ⟨qBaseStarToBase p, rfl⟩

omit [DecidableEq V] in
@[simp] theorem qBaseStarRetraction_new (x : X) :
    qBaseStarRetraction (att := att) ⟨qNew x, trivial⟩ = qNew x := rfl

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

abbrev QLiftedBaseStar (a : Qpos A X att) :=
  {p : UOrder (Qpos A X att) a // InQBaseStar (uOrderEnd p)}

def qBaseIntoStar (a : Qpos A X att) (p : QLiftedBase a) : QLiftedBaseStar a :=
  ⟨p.1, inQBase_in_star p.2⟩

theorem qBaseIntoStar_monotone (a : Qpos A X att) : Monotone (qBaseIntoStar a) :=
  fun _ _ h => h

variable (a : Qpos A X att) (hc : IsConnected (orderCx (Qpos A X att)))

def qLiftedStarRetraction (p : QLiftedBaseStar a) : QLiftedBase a :=
  ⟨(uOrderEnd_isPosetCover hc).lowerMapLift Subtype.val
    (fun p : QLiftedBaseStar a => qBaseStarRetraction ⟨uOrderEnd p.1, p.2⟩)
    (fun p => qBaseStarRetraction_le ⟨uOrderEnd p.1, p.2⟩) p, by
      have h := (uOrderEnd_isPosetCover hc).lowerMapLift_spec Subtype.val
        (fun p : QLiftedBaseStar a => qBaseStarRetraction ⟨uOrderEnd p.1, p.2⟩)
        (fun p => qBaseStarRetraction_le ⟨uOrderEnd p.1, p.2⟩) p
      rw [h.2]
      exact qBaseStarRetraction_mem_base _⟩

theorem qLiftedStarRetraction_monotone : Monotone (qLiftedStarRetraction a hc) := by
  intro p r h
  exact (uOrderEnd_isPosetCover hc).lowerMapLift_monotone Subtype.val
    (fun p : QLiftedBaseStar a => qBaseStarRetraction ⟨uOrderEnd p.1, p.2⟩)
    monotone_subtypeVal (fun _ _ h => qBaseStarRetraction_monotone (uOrderEnd_monotone h))
    (fun p => qBaseStarRetraction_le ⟨uOrderEnd p.1, p.2⟩) h

theorem qLiftedStarRetraction_le (p : QLiftedBaseStar a) :
    qBaseIntoStar a (qLiftedStarRetraction a hc p) ≤ p :=
  ((uOrderEnd_isPosetCover hc).lowerMapLift_spec Subtype.val
    (fun p : QLiftedBaseStar a => qBaseStarRetraction ⟨uOrderEnd p.1, p.2⟩)
    (fun p => qBaseStarRetraction_le ⟨uOrderEnd p.1, p.2⟩) p).1

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror Comb Nerve
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

theorem qLiftedBaseStar_oneCycle_filling (a : Qpos A X att)
    (hc : IsConnected (orderCx (Qpos A X att)))
    (c : Ch (QLiftedBaseStar a)) (hi : c ∈ Inc _)
    (hd : lengthProjection 2 c = c) (hcyc : Nerve.bdry c = 0) :
    ∃ y ∈ Inc (QLiftedBaseStar a), Nerve.bdry y = c :=
  filling_of_lower_composite (qLiftedStarRetraction a hc) (qBaseIntoStar a)
    (qLiftedStarRetraction_monotone a hc) (qBaseIntoStar_monotone a)
    (qLiftedStarRetraction_le a hc) 2
    (nerve_oneCycle_filling_of_simplyConnected (qLiftedBase_simplyConnected a hc))
    c hi hd hcyc

theorem qUniversal_baseStar_fillsDegree_two (x : X) (hx : IsConnected (orderCx X)) :
    FillsDegreeIn
      (fun p : UOrder (Qpos A X att) (qNew x) => InQBaseStar (uOrderEnd p)) 2 := by
  letI : Nonempty X := ⟨x⟩
  have hc : IsConnected (orderCx (Qpos A X att)) :=
    qpos_isConnected_of_zpos (zpos_isConnected hx)
  apply fillsDegreeIn_of_subtype
  · obtain ⟨p, hp⟩ := (uOrderEnd_isPosetCover hc).surj (qNew x)
    exact ⟨p, by rw [hp]; trivial⟩
  · exact qLiftedBaseStar_oneCycle_filling (qNew x) hc

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror Comb Nerve
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

/-- An old two-chain whose boundary is on the attaching locus is an attaching
two-chain modulo an old three-boundary, with exactly the same boundary.
In particular, the original chain is not assumed to be an absolute cycle. -/
theorem qUniversal_old_relative_filling (x : X) (hx : IsConnected (orderCx X))
    (z : Ch (UOrder (Qpos A X att) (qNew x)))
    (hz : z ∈ IncOn (fun p => InQOld (uOrderEnd p)))
    (hd : lengthProjection 3 z = z)
    (hdz : Nerve.bdry z ∈ IncOn
      (fun p => InQOld (uOrderEnd p) ∧ InQBaseStar (uOrderEnd p))) :
    ∃ t ∈ IncOn (fun p => InQOld (uOrderEnd p) ∧ InQBaseStar (uOrderEnd p)),
      lengthProjection 3 t = t ∧ Nerve.bdry t = Nerve.bdry z ∧
      ∃ y ∈ IncOn (fun p => InQOld (uOrderEnd p)),
        lengthProjection 4 y = y ∧ z = t + Nerve.bdry y := by
  have hgen : GeneratesDegreeIn (fun _ : UOrder (Qpos A X att) (qNew x) => True)
      (fun p => InQBaseStar (uOrderEnd p)) 3 := by
    intro c hc hdc hcyc
    obtain ⟨b, hb, y, hy, hbc, he⟩ := qUniversal_generatesDegreeIn_base x hx c hc hdc hcyc
    exact ⟨b, incOn_mono (fun _ h => inQBase_in_star h) hb, y, hy, hbc, he⟩
  exact relative_filling_intersection_of_ambient
    (fun _ _ => True.intro) (fun _ _ => True.intro)
    (fun a b hab _ _ => qOld_baseStar_unmixed _ _ (uOrderEnd_monotone hab))
    hgen (qUniversal_baseStar_fillsDegree_two x hx) z hz hd
    (incOn_mono (fun _ h => h.2) hdz)

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror Comb Nerve
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

/-- A relative old two-chain is replaced by a two-chain on the genuine
attaching cover, with its prescribed boundary there. No zero-boundary input
is imposed on the original chain. -/
theorem qUniversal_old_relative_chain_from_attaching (x : X)
    (hx : IsConnected (orderCx X)) (σ : NeSpx A)
    (z : Ch (UOrder (Qpos A X att) (qNew x)))
    (hz : z ∈ IncOn (fun p => InQOld (uOrderEnd p)))
    (hd : lengthProjection 3 z = z)
    (b : Ch (QLiftedAttaching (qNew (A := A) (att := att) x))) (hb : b ∈ Inc _)
    (hbz : Nerve.bdry z = cmap Subtype.val b) :
    ∃ c : Ch (QLiftedAttaching (qNew (A := A) (att := att) x)),
      c ∈ Inc _ ∧ lengthProjection 3 c = c ∧ Nerve.bdry c = b ∧
      ∃ y ∈ IncOn (fun p => InQOld (uOrderEnd p)),
        lengthProjection 4 y = y ∧ z = cmap Subtype.val c + Nerve.bdry y := by
  letI : Nonempty X := ⟨x⟩
  let J := fun p : UOrder (Qpos A X att) (qNew x) =>
    InQOld (uOrderEnd p) ∧ InQBaseStar (uOrderEnd p)
  have hnonempty : ∃ p, J p := by
    have hc : IsConnected (orderCx (Qpos A X att)) :=
      qpos_isConnected_of_zpos (zpos_isConnected hx)
    obtain ⟨p, hp⟩ := (uOrderEnd_isPosetCover hc).surj
      (Sum.inl (posQCube σ))
    refine ⟨p, ?_⟩
    change InQOld (uOrderEnd p) ∧ InQBaseStar (uOrderEnd p)
    rw [hp]
    exact ⟨trivial, rfl⟩
  have hdz : Nerve.bdry z ∈ IncOn J := by
    rw [hbz]
    exact cmap_val_mem_incOn J hb
  obtain ⟨t, ht, htd, hdt, y, hy, hyd, he⟩ :=
    qUniversal_old_relative_filling x hx z hz hd hdz
  obtain ⟨c, hc, hct⟩ := exists_preimage_of_mem_incOn J ht
  refine ⟨c, hc, ?_, ?_, y, hy, hyd, ?_⟩
  · apply cmap_val_injective J hnonempty
    rw [← lengthProjection_cmap, hct, htd]
  · apply cmap_val_injective J hnonempty
    rw [cmap_bdry, hct, hdt, hbz]
  · rw [hct]
    exact he

end FiniteChains.Davis

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

/-- The actual cover edges, expressed in lifted-order nerve coordinates. -/
def universalNerveChain1 :
    (UE (orderCx P) a →₀ ℤ) →ₗ[ℤ] Nerve.Ch (UOrder P a) :=
  ordNerveChain1.comp (chain1 uOrderHomInv)

/-- The actual cover faces, expressed in lifted-order nerve coordinates. -/
def universalNerveChain2 :
    (UF (orderCx P) a →₀ ℤ) →ₗ[ℤ] Nerve.Ch (UOrder P a) :=
  ordNerveChain2.comp (chain2 uOrderHomInv)

theorem uOrderHomInv_edge_projection (e : UE (orderCx P) a) :
    (orderCxMap uOrderEnd uOrderEnd_monotone).onE (uOrderHomInv.onE e) = e.1.2 := by
  exact congrArg (fun e : UE (orderCx P) a => e.1.2)
    (homInv_onE_apply uOrderHom Function.bijective_id
      ⟨uOrderEdge_injective, uOrderEdge_surjective⟩
      ⟨uOrderFace_injective, uOrderFace_surjective⟩ e)

theorem uOrderHomInv_face_projection (t : UF (orderCx P) a) :
    (orderCxMap uOrderEnd uOrderEnd_monotone).onF (uOrderHomInv.onF t) = t.1.2 := by
  exact congrArg (fun t : UF (orderCx P) a => t.1.2)
    (homInv_onF_apply uOrderHom Function.bijective_id
      ⟨uOrderEdge_injective, uOrderEdge_surjective⟩
      ⟨uOrderFace_injective, uOrderFace_surjective⟩ t)

/-- This is an equality for arbitrary chains, including relative chains. -/
theorem universalNerveChain2_bdry (c : UF (orderCx P) a →₀ ℤ) :
    Nerve.bdry (universalNerveChain2 c) =
      universalNerveChain1 (Comb.bdry2 (uCover (orderCx P) a) c) := by
  change Nerve.bdry (ordNerveChain2 (chain2 uOrderHomInv c)) =
    ordNerveChain1 (chain1 uOrderHomInv (Comb.bdry2 (uCover (orderCx P) a) c))
  rw [← ordNerveChain1_bdry2, bdry2_chain2]

theorem universalNerveChain2_lengthProjection (c : UF (orderCx P) a →₀ ℤ) :
    Nerve.lengthProjection 3 (universalNerveChain2 c) = universalNerveChain2 c :=
  ordNerveChain2_lengthProjection _

theorem universalNerveChain2_mem_inc (c : UF (orderCx P) a →₀ ℤ) :
    universalNerveChain2 c ∈ Nerve.Inc (UOrder P a) :=
  ordNerveChain2_mem_inc _


/-- A face whose projection lies in a subposet has all lifted vertices over that subposet. -/
theorem universalNerveChain2_single_mem_incOn (S : P → Prop)
    (t : UF (orderCx P) a) (n : ℤ) (ht : t.1.2 ∈ ordTriOn S) :
    universalNerveChain2 (Finsupp.single t n) ∈
      Nerve.IncOn (fun v => S (uOrderEnd v)) := by
  rw [(show universalNerveChain2 (Finsupp.single t n) =
      n • FreeAbelianGroup.of [(uOrderHomInv.onF t).1.1,
        (uOrderHomInv.onF t).1.2.1, (uOrderHomInv.onF t).1.2.2] by
    change ordNerveChain2 (Finsupp.mapDomain uOrderHomInv.onF (Finsupp.single t n)) = _
    rw [Finsupp.mapDomain_single]
    simp only [ordNerveChain2, Finsupp.linearCombination_single])]
  apply AddSubgroup.zsmul_mem
  apply Nerve.of_mem_incOn
  · grind
  · rw [← uOrderHomInv_face_projection t] at ht
    change S (uOrderEnd (uOrderHomInv.onF t).1.1) ∧
      S (uOrderEnd (uOrderHomInv.onF t).1.2.1) ∧
      S (uOrderEnd (uOrderHomInv.onF t).1.2.2) at ht
    intro v hv
    simp at hv
    rcases hv with rfl | rfl | rfl
    · simp_all
    · simp_all
    · simp_all

/-- Finite cellular support over a subposet becomes nerve support over that same subposet.
No cycle or connectedness hypothesis is required. -/
theorem universalNerveChain2_mem_incOn (S : P → Prop)
    (c : UF (orderCx P) a →₀ ℤ)
    (hc : ∀ t ∈ c.support, t.1.2 ∈ ordTriOn S) :
    universalNerveChain2 c ∈ Nerve.IncOn (fun v => S (uOrderEnd v)) := by
  have he : c = ∑ t ∈ c.support, Finsupp.single t (c t) :=
    (Finsupp.sum_single c).symm
  rw [he, map_sum]
  apply AddSubgroup.sum_mem
  intro t ht
  exact universalNerveChain2_single_mem_incOn S t (c t) (hc t ht)

end FiniteChains.Comb

namespace FiniteChains.Davis
open RACG Mirror Comb Nerve
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

/-- The relative attaching-chain theorem applied to the actual supported cellular chain
in the quotient's universal cover. Its boundary is prescribed through the exact
degree-one conversion; the original chain need not be a cycle. -/
theorem qUniversal_old_cellular_relative_chain_from_attaching (x : X)
    (hx : IsConnected (orderCx X)) (σ : NeSpx A)
    (z : UF (orderCx (Qpos A X att)) (qNew x) →₀ ℤ)
    (hz : ∀ t ∈ z.support, t.1.2 ∈ ordTriOn InQOld)
    (b : Ch (QLiftedAttaching (qNew (A := A) (att := att) x))) (hb : b ∈ Inc _)
    (hbz : universalNerveChain1 (Comb.bdry2 (uCover (orderCx (Qpos A X att)) (qNew x)) z) =
      cmap Subtype.val b) :
    ∃ c : Ch (QLiftedAttaching (qNew (A := A) (att := att) x)),
      c ∈ Inc _ ∧ lengthProjection 3 c = c ∧ Nerve.bdry c = b ∧
      ∃ y ∈ IncOn (fun p => InQOld (uOrderEnd p)),
        lengthProjection 4 y = y ∧
          universalNerveChain2 z = cmap Subtype.val c + Nerve.bdry y := by
  apply qUniversal_old_relative_chain_from_attaching x hx σ (universalNerveChain2 z)
    (universalNerveChain2_mem_incOn InQOld z hz)
    (universalNerveChain2_lengthProjection z) b hb
  rw [universalNerveChain2_bdry, hbz]

end FiniteChains.Davis

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

/-- Actual cover faces whose projected triangle lies in the chosen subposet. -/
def supportedUniversalFaces (S : P → Prop) :
    Submodule ℤ (UF (orderCx P) a →₀ ℤ) :=
  Finsupp.supported ℤ ℤ {t | t.1.2 ∈ ordTriOn S}


theorem chain2_mem_supportedUniversalFaces {K : Complex2.{u}}
    (S : P → Prop) (f : Hom K (uCover (orderCx P) a))
    (hf : ∀ t, (f.onF t).1.2 ∈ ordTriOn S) (c : K.F →₀ ℤ) :
    chain2 f c ∈ supportedUniversalFaces S := by
  apply Finsupp.supported_comap_lmapDomain ℤ ℤ f.onF {t | t.1.2 ∈ ordTriOn S}
  intro t _
  exact hf t

/-- Deck translation changes the sheet and leaves every projected face unchanged. -/
theorem deck_mem_supportedUniversalFaces (S : P → Prop)
    (g : Pi1 (orderCx P) a) (c : UF (orderCx P) a →₀ ℤ)
    (hc : c ∈ supportedUniversalFaces S) :
    (univDeck (orderCx P) a).faceChains g c ∈ supportedUniversalFaces S := by
  apply Finsupp.supported_comap_lmapDomain ℤ ℤ (deckF g) {t | t.1.2 ∈ ordTriOn S}
  exact hc

end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
open scoped Classical
variable (q : ℕ) [NeZero q] {α Jr : Type}
  (ρ : Jr ⊕ PUnit.{1} → FreeGroup α) (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

theorem receivedSpineToQuotient_face_old (t : (singleReceivedSpineCover q ρ u).F) :
    ((receivedSpineToQuotient q ρ u hrho).onF t).1.2 ∈ ordTriOn InQOld := ⟨trivial, trivial, trivial⟩

theorem receivedSpineToQuotient_chain_old
    (c : (singleReceivedSpineCover q ρ u).F →₀ ℤ) :
    chain2 (receivedSpineToQuotient q ρ u hrho) c ∈ supportedUniversalFaces InQOld :=
  chain2_mem_supportedUniversalFaces InQOld (receivedSpineToQuotient q ρ u hrho)
    (receivedSpineToQuotient_face_old q ρ u hrho) c

theorem oldCoverToNamedQuotient_face_old
    (t : (uCover (spineOldCx q) (spineOldBase q)).F) :
    ((oldCoverToNamedQuotient q ρ u).onF t).1.2 ∈ ordTriOn InQOld := ⟨trivial, trivial, trivial⟩



theorem quotientMarkingCorrections_old
    (c : (PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ) :
    quotientMarkingCorrections q ρ u hrho c ∈ supportedUniversalFaces InQOld := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa using Submodule.add_mem _ hc hd
  | single x n =>
      erw [quotientMarkingCorrections, Finsupp.linearCombination_single]
      exact Submodule.smul_mem _ n (deck_mem_supportedUniversalFaces InQOld (finiteSpineToQuotient ρ q u hrho (x.1))
    (chain2 (oldCoverToNamedQuotient q ρ u) (spineOldMarkingCorrection q (x.2)))
    (chain2_mem_supportedUniversalFaces InQOld (oldCoverToNamedQuotient q ρ u)
    (oldCoverToNamedQuotient_face_old q ρ u) (spineOldMarkingCorrection q (x.2))))

/-- Both the received faces and the explicit marking correction are supported on old faces. -/

theorem quotientCorrectedRelativeChain_face_support
    (β : NamedSpineRel q → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (finiteSpineWordBlock q u)))) :
    ∀ t ∈ (quotientCorrectedRelativeChain q ρ u hrho β).support,
      t.1.2 ∈ ordTriOn InQOld :=
  (Iff.rfl).mp
    (Submodule.sub_mem _
    (receivedSpineToQuotient_chain_old q ρ u hrho _)
    (quotientMarkingCorrections_old q ρ u hrho _))

def quotientCorrectedRelativeNerveChain
    (β : NamedSpineRel q → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (finiteSpineWordBlock q u)))) :
    Ch (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u)) :=
  universalNerveChain2 (quotientCorrectedRelativeChain q ρ u hrho β)

theorem quotientCorrectedRelativeNerveChain_boundary
    (β : NamedSpineRel q → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (finiteSpineWordBlock q u))))
    (hβ : ∀ z : SpinePresentationGen q,
      (∑ m, β m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0) :
    Nerve.bdry (quotientCorrectedRelativeNerveChain q ρ u hrho β) =
      universalNerveChain1 (quotientSurfaceMarkingChains q ρ u hrho
        ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => β (Sum.inr i)))) := by
  erw [quotientCorrectedRelativeNerveChain, universalNerveChain2_bdry,
    quotientCorrectedRelativeChain_boundary q ρ u hrho β hβ]

end FiniteChains.Davis.Genus
end
