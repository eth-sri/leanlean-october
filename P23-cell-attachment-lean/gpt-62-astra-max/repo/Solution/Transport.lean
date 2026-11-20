module
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.LocallyConvex.Basic
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.Tactic

@[expose] public noncomputable section
namespace CellAttachment
open CategoryTheory unitInterval Set
variable {X Y D K G ι : Type*} [Group G] [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace D] [TopologicalSpace K]

/-! The two local-to-global criteria below use arbitrary group-valued edge
labels. Afterwards we construct such labels from ordinary paths. -/

/-- Exactness of edge labels after pullback to a parameter space. -/
def Potential (w : C(I, X) → G) (F : C(D, X)) :=
  ∃ v : D → G, ∀ e : C(I, D), w (F.comp e) = v (e 1) * (v (e 0))⁻¹

section Cover

variable {U : ι → TopologicalSpace.Opens X} (hc : ∀ x, ∃ i, x ∈ U i)

abbrev hor (a : I) := (ContinuousMap.id I).prodMk (.const I a)
abbrev ver (a : I) := (ContinuousMap.const I a).prodMk (.id I)

variable {w : C(I, X) → G}
include hc

/-- If every small edge label is in R, the potential stays locally in a
single right coset. Connectedness propagates this to the entire interval. -/
lemma generated {p : C(I, X)} {R : Subgroup G}
    (small : ∀ (e : C(I, X)) i, (∀ t, e t ∈ U i) → w e ∈ R) : Potential w p → w p ∈ R := by
  rintro ⟨v, hv⟩
  let _ : LocallyPathConnectedSpace I := (convex_Icc ..).locallyPathConnectedSpace
  let S := (QuotientGroup.rightRel R).comap v
  have := S.iseqv.stdSymm
  erw [hv (.id I)]
  refine QuotientGroup.rightRel_apply.mp (PreconnectedSpace.induction₂ S.r ?_ S.iseqv.isTrans 0 1)
  intro a
  obtain ⟨i, hi⟩ := hc (p a)
  filter_upwards [pathComponentIn_mem_nhds (((U i).isOpen.preimage p.continuous).mem_nhds hi)] with b ⟨e, he⟩
  apply QuotientGroup.rightRel_apply.mpr
  simpa [hv e.toContinuousMap] using small (p.comp e.toContinuousMap) i he

/-- Flat labels commute around each little square of a null-homotopy.
The subdivision theorem is applied on the parameter space, never on X. -/
lemma null_boundary {x : X} {p : Path x x}
    (H : p.Homotopy (.refl x))
    (flat : ∀ (F : C(I × I, X)) i, (∀ t, F t ∈ U i) → Potential w F) : Potential w p.toContinuousMap → w p.toContinuousMap = 1 := by
  rintro ⟨v, hv⟩
  let F := H.toContinuousMap
  obtain ⟨t, h0, hm, ⟨N, hN⟩, hs⟩ := exists_monotone_Icc_subset_open_cover_unitInterval_prod_self
    (fun i => (U i).isOpen.preimage F.continuous) (fun _ _ => mem_iUnion.mpr (hc _))
  have hn := hN N le_rfl
  let e i : C(I, I) := { toFun := Icc.convexComb (t i) (t (i + 1)) }
  have bounds i r : e i r ∈ Icc (t i) (t (i + 1)) := by
    dsimp [e]; grind [Monotone]
  let V i j := w ((F.comp (ver (t i))).comp (e j))
  let B i j := w ((F.comp (hor (t j))).comp (e i))
  have cell i j : V (i + 1) j * B i j = B i (j + 1) * V i j := by
    obtain ⟨k, hk⟩ := hs i j
    let f := F.comp ((e i).prodMap (e j))
    obtain ⟨u, hu⟩ := flat f k (fun r => hk ⟨bounds i _, bounds j _⟩)
    let label := w ∘ f.comp
    have hh : label (ver 1) * label (hor 0) = label (hor 1) * label (ver 0) := by
      simp [label, hu, hor, ver, mul_assoc]
    dsimp only [label, Function.comp_apply] at hh
    convert! hh using 3 <;> simp [f, e, hor, ver, ContinuousMap.ext_iff]
  -- A constant edge factors through an endpoint of p.
  have wc {q : C(I, X)} (h : ∀ t, q t = x) : w q = 1 := by
    convert hv (.const I 0) using 2 <;> simp [ContinuousMap.ext_iff, h]
  -- Extend the left column's primitive one horizontal step at a time.
  let g (i j : ℕ) : G := i.rec (v (t j)) (fun n a => B n j * a)
  have adj i j : V i j * g i j = g i (j + 1) := by
    induction i with
    | zero =>
      rw [← eq_mul_inv_iff_mul_eq]; convert! hv (e j) using 2 <;> simp [g, F, ver, e, h0, ContinuousMap.ext_iff]
    | succ i ih => change _ * (B i j * _) = B i (j + 1) * _; rw [← mul_assoc, cell, mul_assoc, ih]
  -- Both horizontal sides and the last vertical side are constant.
  have side i : g i 0 = v 0 ∧ g i N = v 1 := by
    induction i <;> simp_all [g, B, hor, F]
  have ends j : g N j = g N 0 := by induction j <;> simp [← adj, V, ver, F, *]
  simpa [← (side N).1, ← (side N).2, ends N] using hv (.id I)

end Cover

set_option backward.isDefEq.respectTransparency false
abbrev Way (x y : X) := FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y
abbrev move (f : C(X, Y)) {x y : X} (p : Way x y) : Way (f x) (f y) := (FundamentalGroupoid.map f).map p
attribute [local simp↓] move Functor.map_comp Functor.map_inv Functor.map_id
abbrev route [PathConnectedSpace X] (x y : X) : Way x y := .mk (PathConnectedSpace.somePath x y)
instance [SimplyConnectedSpace X] (x y : X) : Subsingleton (Way x y) :=
  inferInstanceAs (Subsingleton (Path.Homotopic.Quotient x y))
instance : ContractibleSpace I := (convex_Icc ..).contractibleSpace ⟨0, unitInterval.zero_mem⟩

/-- Marks are path coordinates; only the endpoint has to vary continuously. -/
structure Mark (x : X) where
  pt : X
  path : Way x pt
instance {x : X} : TopologicalSpace (Mark x) := .induced Mark.pt inferInstance
namespace Mark
variable {x : X}
abbrev endpoint : C(Mark x, X) := ⟨pt, continuous_induced_dom⟩
-- Normalize the arbitrary paths at the base vertex.
def pick [PathConnectedSpace X] (x : X) : C(X, Mark x) :=
  ⟨fun y => ⟨y, inv (route x x) ≫ route x y⟩,
   continuous_induced_rng.mpr continuous_id⟩
@[simp] lemma pick_self [PathConnectedSpace X] (x : X) : (pick x x).path = 𝟙 _ := by simp [pick]

variable (s : C(D, Mark x)) {a b : D}
def read (p : Way a b) : FundamentalGroup X x := (s a).path ≫ move (endpoint.comp s) p ≫ Groupoid.inv (s b).path
/-- Read one parameterized edge in the chosen endpoint coordinates. -/
def edge (p : C(I, Mark x)) := read p (.mk Path.id)
lemma edge_path (p : Path a b) :
    edge (s.comp p.toContinuousMap) = read s (.mk p) := by
  rcases p with ⟨p, rfl, rfl⟩; rfl
/-- In a simply connected parameter space, the label of every edge is a
vertex difference, also after applying any group homomorphism. -/
lemma primitive [SimplyConnectedSpace D]
    (φ : FundamentalGroup X x →* G) : Potential (φ ∘ edge) s := by
  let a : D := Classical.ofNonempty
  refine ⟨fun b => φ (read s (route a b)), fun e => ?_⟩
  let p := move e (.mk Path.id)
  erw [eq_mul_inv_iff_mul_eq, ← map_mul]
  change φ (read s p * _) = φ (read s _)
  rw [Subsingleton.elim (route a (e 1)) (route a (e 0) ≫ p)]; simp [read, End.mul_def]
end Mark

/-- Maps with a whisker at the source vertex compose, acting both on marks and on loops. -/
structure Leg (d : D) (x : X) where
  map : C(D, X)
  path : Way x (map d)
namespace Leg
open Mark
variable {d : D} {x : X} {a : K} (L : Leg d x)
def ofMap (f : C(D, X)) (d : D) : Leg d (f d) := ⟨f, 𝟙 _⟩
def act : C(Mark d, Mark x) := ⟨fun m => ⟨_, L.path ≫ move L.map m.path⟩,
  continuous_induced_rng.mpr (L.map.continuous.comp endpoint.continuous)⟩
/-- Follow a whisker and the chosen path in its source. -/
abbrev trail [PathConnectedSpace D] (a : D) := (L.act (pick d a)).path
def loops := ((Groupoid.isoEquivHom ..).symm L.path).symm.conj.toMonoidHom.comp (FundamentalGroup.map L.map d)
def comp (M : Leg a d) : Leg a x := ⟨L.map.comp M.map, L.path ≫ move L.map M.path⟩
@[local simp] lemma loops_apply (g) : L.loops g = L.path ≫ move L.map g ≫ Groupoid.inv L.path := rfl
lemma comp_act (M : Leg a d) (m) : (L.comp M).act m = L.act (M.act m) := by
  dsimp [act, comp]; simp [Path.Homotopic.Quotient.map_comp]
lemma comp_loops (M : Leg a d) (g) : (L.comp M).loops g = L.loops (M.loops g) := by
  simp [comp, Path.Homotopic.Quotient.map_comp]
lemma edge_act {t : C(I, Mark x)} (s : C(I, Mark d)) (h : ∀ a, t a = L.act (s a)) :
    edge t = L.loops (edge s) := by
  obtain rfl : t = L.act.comp s := ContinuousMap.ext h
  simp [edge, Mark.read, act]; congr 3
@[simp] lemma ofMap_loops (f : C(D, X)) (d g) : (ofMap f d).loops g = FundamentalGroup.map f d g := by
  simp [ofMap]
lemma loops_one [SimplyConnectedSpace D] (g) : L.loops g = 1 := by rw [Subsingleton.elim g 1, map_one]
/-- Lift a whisker across an equality which factors the underlying map. -/
def extend (b : C(D, K)) (k : C(K, X)) (h : L.map = k.comp b) :
    {p : Way x (k (b d)) // (Leg.mk k p).comp (ofMap b d) = L} := by
  rcases L with ⟨f, p⟩; cases h.symm
  exact ⟨p, congrArg (Leg.mk _) (Category.comp_id p)⟩
end Leg
end CellAttachment
