/-
Attaching arbitrary families of two-cells, Hatcher Proposition 1.26.
Authors: Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz.
First-party sources released under Apache-2.0.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Product
public import Mathlib.Topology.Subpath
public import Mathlib.Topology.CompactOpen
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.NormNum

@[expose] public section

noncomputable section
open Set Topology
open scoped unitInterval
open Path.Homotopic.Quotient (mk mk_surjective mk_refl map_comp)
open Path.Homotopic (prod)
local notation "Q" => Path.Homotopic.Quotient

namespace CellAttachment
namespace PathTransport

/-! ### Comparing compatible path evaluations on an open cover

Subdivision of a path gives a product of local evaluations. A subdivided
homotopy compares such products on its two boundary paths by composing the
relations around each small rectangle. All classes are ordinary path homotopy
classes; there is no local path-connectivity assumption on the cover.
-/

variable {X : Type*} [TopologicalSpace X] {G : Type*} [Group G]

abbrev left (U V : Set X) := ContinuousMap.inclusion (inter_subset_left : U ∩ V ⊆ U)
abbrev right (U V : Set X) := ContinuousMap.inclusion (inter_subset_right : U ∩ V ⊆ V)

def intoChart {A : Type*} [TopologicalSpace A] (f : C(A, X)) {V : Set X} (h : ∀ x, f x ∈ V) : C(A, V) where
  toFun x := ⟨f x,h x⟩

lemma class_map_trans {Y : Type*} [TopologicalSpace Y] (f : C(X,Y)) {x y z : X}
    (p : Q x y) (q : Q y z) : (p.trans q).map f = (p.map f).trans (q.map f) :=
  Quotient.inductionOn₂ p q fun a b => congrArg mk (Path.map_trans a b f.continuous)

section LocalCharts
variable {J : Type*} {U : J → Set X}

/-- Local evaluations take composition in the same order as multiplication in π₁. -/
structure Local (U : J → Set X) (G : Type*) [Group G] where
  act (i : J) {x y : U i} : Q x y → G
  trans (i : J) {x y z : U i} (p : Q x y) (q : Q y z) :
    act i (p.trans q) = act i q * act i p
  agree {i j : J} {x y : ↥(U i ∩ U j)} (p : Q x y) :
    act i (p.map (left (U i) (U j))) = act j (p.map (right (U i) (U j)))

namespace Local
variable (L : Local U G)

lemma refl (i : J) (x : U i) : L.act i (.refl x) = 1 := by
  simpa using (L.trans i (.refl x) (.refl x)).symm

lemma eval_segment_whole {A : Type*} (F : {x y : X} → Q x y → A) {x y : X} (p : Path x y) :
    F (.mk (p.subpath 0 1)) = F (.mk p) := by
  rcases p with ⟨p,rfl,rfl⟩
  simp [Path.cast]; rfl

abbrev inclIcc {a b : I} : C(Icc (a : ℝ) b, I) := .inclusion (Icc_subset_Icc a.2.1 b.2.2)

/-- The straight path in a subinterval. -/
def line {a b : I} (h : a ≤ b) : Path (⟨a, le_rfl, h⟩ : Icc (a : ℝ) b) ⟨b, h, le_rfl⟩ :=
  ⟨⟨_, Icc.continuous_convexComb ..⟩, Icc.convexComb_zero .., Icc.convexComb_one ..⟩

def stepPath (p : C(I, X)) {a b : I} (hab : a ≤ b) {V : Set X} (h : MapsTo p (Icc a b) V) :=
  (line hab).map (intoChart (p.comp inclIcc) (fun t => h t.2)).continuous

def edge (p : C(I, X)) {a b : I} (hab : a ≤ b) {i : J} (h : MapsTo p (Icc a b) (U i)) : G :=
  L.act i (.mk (stepPath p hab h))

lemma edge_eq {p : C(I, X)} {a b : I} (hab : a ≤ b) {i j : J}
    (hi : MapsTo p (Icc a b) (U i)) (hj : MapsTo p (Icc a b) (U j)) :
    L.edge p hab hi = L.edge p hab hj :=
  L.agree (.mk (stepPath p hab (hi.inter hj)))

/-- The product along a chart-labelled subdivision (in the order of π₁). -/
def accumulate (p : C(I, X)) {t : ℕ → I} (ht : Monotone t) {d : ℕ → J}
    (hc : ∀ k, MapsTo p (Icc (t k) (t (k + 1))) (U (d k))) : ℕ → G
  | 0 => 1
  | k + 1 => L.edge p (ht (Nat.le_succ k)) (hc k) * accumulate p ht hc k

/-- A rectangular subdivision compares the chart evaluations at the two ends. -/
lemma act_homotopy (hU : ∀ i, IsOpen (U i)) (cover : ∀ x, ∃ i, x ∈ U i)
    (i : J) {x y : U i} (p q : Path x y)
    (H : (p.map continuous_subtype_val).Homotopy (q.map continuous_subtype_val)) :
    L.act i (.mk p) = L.act i (.mk q) := by
  let F := H.toHomotopy.toContinuousMap
  let col := (F.comp .prodSwap).curry
  obtain ⟨t, ht, hm, ⟨n, hn⟩, hc⟩ := exists_monotone_Icc_subset_open_cover_unitInterval_prod_self
    (c := fun i => F ⁻¹' U i) (fun i => (hU i).preimage F.continuous)
    (fun a _ => mem_iUnion.mpr (cover (F a)))
  choose d hd using hc
  have hm' (k : ℕ) : t k ≤ t (k + 1) := hm (Nat.le_succ k)
  have hrow (m k : ℕ) : MapsTo (F.curry (t m)) (Icc (t k) (t (k + 1))) (U (d m k)) :=
    fun _ h => hd m k ⟨left_mem_Icc.mpr (hm' m), h⟩
  have hcol (m k : ℕ) : MapsTo (col (t k)) (Icc (t m) (t (m + 1))) (U (d m k)) :=
    fun _ h => hd m k ⟨h, left_mem_Icc.mpr (hm' k)⟩
  let hor m k := L.edge (F.curry (t m)) (hm' k) (hrow m k)
  let ver m k := L.edge (col (t k)) (hm' m) (hcol m k)
  -- The two edge routes across a rectangle lie in a single chart.
  have square m k : ver m (k + 1) * hor m k = hor (m + 1) k * ver m k := by
    let i := d m k
    have hi := hd m k
    unfold ver hor
    rw [L.edge_eq _ (hcol m (k+1)) (j := i) (fun _ h => hi ⟨h, right_mem_Icc.mpr (hm' k)⟩),
      L.edge_eq _ (hrow (m+1) k) (j := i) (fun _ h => hi ⟨right_mem_Icc.mpr (hm' m), h⟩)]
    let f := intoChart (F.comp (inclIcc.prodMap inclIcc)) (fun z => hi ⟨z.1.2,z.2.2⟩)
    let l := Path.Homotopic.Quotient.mk (line (hm' m))
    let r := Path.Homotopic.Quotient.mk (line (hm' k))
    have e : (prod (.refl _) r).trans (prod l (.refl _)) = (prod l (.refl _)).trans (prod (.refl _) r) := by
      simp [Path.Homotopic.comp_prod_eq_prod_comp]
    simpa only [class_map_trans,L.trans,edge] using! congrArg (fun g => L.act i (g.map f)) e
  let accum m := L.accumulate (F.curry (t m)) hm (hrow m)
  have ends (m k : ℕ) (hk : t k = 0 ∨ t k = 1) : ver m k = 1 := by
    have e : col (t k) = .const I (F (t m, t k)) := by
      ext s
      rcases hk with e | e <;> simp [col, F, e]
    suffices ∀ h, L.edge (col (t k)) (hm' m) h = 1 from this _
    rw [e]
    exact fun _ => L.refl ..
  -- Cancel the vertical edges, first within each strip and then along the boundary.
  have commute (m k : ℕ) : ver m k * accum m k = accum (m + 1) k := by
    induction k with
    | zero => simp [accum, accumulate, ends m 0 (.inl ht)]
    | succ k ih =>
      change ver m (k + 1) * (hor m k * _) = hor (m + 1) k * _
      rw [← mul_assoc, square, mul_assoc, ih]
  have all (m : ℕ) : accum 0 n = accum m n :=
    Nat.rec rfl (fun m ih => ih.trans (by simpa only [ends m n (.inr (hn n le_rfl)), one_mul] using commute m n)) m
  have endval (r : Path x y) (g : C(I, X)) {d : ℕ → J}
      (hc' : ∀ k, MapsTo g (Icc (t k) (t (k+1))) (U (d k)))
      (he : g = (ContinuousMap.subtypeVal (U i)).comp r.toContinuousMap) :
      L.accumulate g hm hc' n = L.act i (.mk r) := by
    subst g
    have eval (m : ℕ) : L.accumulate _ hm hc' m =
        L.act i (.mk (r.subpath (t 0) (t m))) := by
      induction m with
      | zero => simp [accumulate, L.refl]
      | succ n ih =>
        rw [accumulate, ih, L.edge_eq _ (hc' n) (j := i) (fun t _ => (r t).2)]
        erw [← L.trans, Path.Homotopic.mk_subpath_trans_mk_subpath]
        rfl
    rw [eval, ht, hn n le_rfl, eval_segment_whole (L.act i) r]
  exact (endval p _ _ (ht ▸ congrArg Path.toContinuousMap H.eval_zero)).symm.trans
    ((all n).trans (endval q _ _ (hn n le_rfl ▸ congrArg Path.toContinuousMap H.eval_one)))

end Local
end LocalCharts

section Whiskering

variable {x y z b : X}
open Path.Homotopic.Quotient (trans_assoc)

/-- A path class expressed as a based loop using its two endpoint paths. -/
def whisker (c : Q b x) (d : Q b y) (p : Q x y) : FundamentalGroup X b :=
  c.trans (p.trans d.symm)

def whiskerEquiv (c : Q b x) : FundamentalGroup X x ≃* FundamentalGroup X b :=
  ((CategoryTheory.Groupoid.isoEquivHom (FundamentalGroupoid.mk b) (FundamentalGroupoid.mk x)).symm c).symm.conj

@[simp] lemma whisker_refl (c : Q b x) : whisker c c (.refl x) = 1 := map_one (whiskerEquiv c)

lemma whisker_trans (c : Q b x) (d : Q b y) (e : Q b z) (p : Q x y) (q : Q y z) :
    whisker c e (p.trans q) = whisker d e q * whisker c d p := by
  simp [whisker, FundamentalGroup.mul_def, ← trans_assoc d.symm d]

lemma whisker_map {A : Type*} [TopologicalSpace A] (f : C(X, A))
    (c : Q b x) (d : Q b y) (p : Q x y) :
    FundamentalGroup.map f b (whisker c d p) = whisker (c.map f) (d.map f) (p.map f) := by
  change (c.trans (p.trans d.symm)).map f = _
  simp only [whisker, class_map_trans]
  rcases d with ⟨d⟩; rfl

lemma whisker_cancel (a : Q b x) {x' y' : X} (c : Q x x') (d : Q x y') (p : Q x' y') :
    whisker (a.trans c) (a.trans d) p = whisker a a (whisker c d p) := by
  have e : (a.trans d).symm = d.symm.trans a.symm :=
    Quotient.inductionOn₂ a d fun p q => congrArg mk (Path.trans_symm p q)
  simp [whisker, e]

/-- Killing a transported loop is independent of the chosen whisker. -/
lemma whisker_killed (q : FundamentalGroup X b →* G) (c d : Q b x) (g : Q x x)
    (h : q (whisker c c g) = 1) : q (whisker d d g) = 1 := by
  let k : FundamentalGroup X b := d.trans c.symm
  rw [← show k.trans c = d from by simp [k], whisker_cancel]
  exact (MonoidHom.normal_ker q).conj_mem' _ h k

end Whiskering

set_option backward.isDefEq.respectTransparency false

/-! ### A cover by a connected left set and disjoint simply connected sets -/
section

variable {ι : Type*} {U : Set X} {V : ι → Set X}

abbrev charts (U : Set X) (V : ι → Set X) : Option ι → Set X := fun i => i.elim U V

/-- An open cover by a path-connected set and disjoint simply connected sets.
    A quotient of the left vertex group realizes the ambient group if it kills the
    transported overlap loops and its map back agrees with the actual inclusion. -/
lemma glue (b : U) (reach : ∀ x : U, Q b x) (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hcover : ∀ x, ∃ i, x ∈ charts U V i)
    (unique : ∀ {x i j}, x ∈ V i → x ∈ V j → i = j)
    (simply : ∀ i, SimplyConnectedSpace (V i))
    {A : Type*} [TopologicalSpace A] [PathConnectedSpace A] (E : ∀ i, A ≃ₜ ↥(U ∩ V i))
    (a : A)
    (q : FundamentalGroup U b →* G) (m : G →* FundamentalGroup X (b : X))
    (factor : ∀ g, m (q g) = FundamentalGroup.map (ContinuousMap.subtypeVal U) b g)
    (kill : ∀ i p (g : FundamentalGroup A a),
      q (whisker p p (g.toPath.map ((left U (V i)).comp (E i)))) = 1) :
    Function.Surjective m ∧ (FundamentalGroup.map (ContinuousMap.subtypeVal U) b).ker ≤ q.ker := by
  classical
  let p i := reach (left U (V i) (E i a))
  -- Choose based paths whose restrictions to each overlap use the same anchor.
  let trace i (z : ↥(U ∩ V i)) : Q (E i a) z :=
    let := (E i).pathConnectedSpace; .mk (PathConnectedSpace.somePath _ _)
  let anchor i (z : ↥(U ∩ V i)) := (p i).trans ((trace i z).map (left U (V i)))
  have pres (x : U) : ∃ s : Q b x, ∀ i (hi : (x : X) ∈ V i), s = anchor i ⟨x,x.2,hi⟩ := by
    by_cases h : ∃ i, (x : X) ∈ V i
    · obtain ⟨i,hi⟩ := h
      refine ⟨anchor i ⟨x,x.2,hi⟩, fun j hj => ?_⟩
      cases unique hi hj
      rfl
    · exact ⟨reach x, fun i hi => (h ⟨i,hi⟩).elim⟩
  choose s hs using pres
  let P i := (p i).map (ContinuousMap.subtypeVal U)
  -- Extend those paths to the ambient space using the disjoint charts.
  have pc (x : X) : ∃ c : Q (b : X) x,
      (∀ hx : x ∈ U, c = (s ⟨x, hx⟩).map (ContinuousMap.subtypeVal U)) ∧
      (∀ i (hi : x ∈ V i), ∃ t : Q (right U (V i) (E i a)) ⟨x, hi⟩,
        c = (P i).trans (t.map (ContinuousMap.subtypeVal (V i)))) := by
    by_cases hx : x ∈ U
    · refine ⟨(s ⟨x,hx⟩).map (ContinuousMap.subtypeVal U), fun _ => rfl, ?_⟩
      intro i hi
      refine ⟨(trace i ⟨x,hx,hi⟩).map (right U (V i)), ?_⟩
      rw [hs _ i hi]
      dsimp only [anchor]
      rw [class_map_trans]
      rfl
    · obtain ⟨_ | i,hi⟩ := hcover x
      · exact (hx hi).elim
      let := simply i
      let t := mk (PathConnectedSpace.somePath (right U (V i) (E i a)) ⟨x,hi⟩)
      refine ⟨(P i).trans (t.map (ContinuousMap.subtypeVal (V i))), fun h => (hx h).elim, fun j hj => ?_⟩
      obtain rfl := unique hi hj
      exact ⟨t,rfl⟩
  choose c hc hc' using pc
  have surj i : Function.Surjective (FundamentalGroup.map (toContinuousMap (E i)) a) :=
    (FundamentalGroupoidFunctor.equivOfHomotopyEquiv (E i).toHomotopyEquiv).functor.map_surjective
  let act : (i : Option ι) → {x y : charts U V i} → Q x y → G
    | none, x, y, g => q (whisker (s x) (s y) g)
    | some _, _, _, _ => 1
  have cross i {x y : ↥(U ∩ V i)} (g : Q x y) : act none (g.map (left U (V i))) = 1 := by
    dsimp only [act]
    rw [hs _ i x.2.2, hs _ i y.2.2]
    dsimp only [anchor]
    rw [whisker_cancel, ← whisker_map]
    obtain ⟨k,hk⟩ := surj i (whisker (trace i x) (trace i y) g)
    change k.toPath.map (toContinuousMap (E i)) = _ at hk
    simpa only [map_comp, hk] using! kill i (p i) k
  let L : Local (charts U V) G := {
    act := act
    trans := by
      rintro (_ | i) x y z f g
      · exact (congrArg q (whisker_trans ..)).trans (map_mul ..)
      · simp only [act, mul_one]
    agree := by
      rintro (_ | i) (_ | j) x y g
      · rfl
      · exact cross j g
      · simpa only [← map_comp] using! (cross i (g.map (toContinuousMap (Homeomorph.setCongr (inter_comm (V i) U))))).symm
      · rfl }
  have hcharts : ∀ i, IsOpen (charts U V i) := fun i => i.casesOn hU hV
  have realize (i : Option ι) {x y : charts U V i} (g : Q x y) :
      m (L.act i g) = whisker (c x) (c y) (g.map (ContinuousMap.subtypeVal (charts U V i))) := by
    cases i with
    | none =>
      change ↥U at x y
      rw [hc x x.2, hc y y.2]
      exact (factor _).trans (whisker_map ..)
    | some i =>
      change ↥(V i) at x y
      obtain ⟨r,hr⟩ := hc' x i x.2
      obtain ⟨t,ht⟩ := hc' y i y.2
      let := simply i
      rw [hr, ht, whisker_cancel]
      erw [← whisker_map, Subsingleton.elim (whisker r t g) 1, map_one, map_one]
      exact (whisker_refl _).symm
  constructor
  · -- The image of each local evaluation is the corresponding based ambient loop.
    intro g
    obtain ⟨r,rfl⟩ := ((whiskerEquiv (c b)).surjective.comp mk_surjective) g
    let F := r.toContinuousMap
    obtain ⟨t, ht, hm, ⟨n, hn⟩, hc⟩ := exists_monotone_Icc_subset_open_cover_unitInterval
      (c := fun i => F ⁻¹' charts U V i) (fun i => (hcharts i).preimage F.continuous)
      (fun a _ => mem_iUnion.mpr (hcover (F a)))
    choose d hc using hc
    have step (k : ℕ) : m (L.accumulate F hm hc k) =
        whisker (c (F (t 0))) (c (F (t k))) (mk (r.subpath (t 0) (t k))) := by
      induction k with
      | zero =>
        simp only [Local.accumulate, map_one, Path.subpath_self]
        exact (whisker_refl _).symm
      | succ k ih =>
        rw [Local.accumulate, map_mul, ih, ← Path.Homotopic.mk_subpath_trans_mk_subpath r (t 0) (t k) (t (k + 1)), whisker_trans]
        congr 1
        exact realize ..
    refine ⟨_, (step n).trans ?_⟩
    rw [ht, hn n le_rfl]
    exact Local.eval_segment_whole (fun g => whisker (c _) (c _) g) r
  · -- A null-homotopy in the ambient space forces the quotient evaluation to be trivial.
    rintro ⟨g⟩ hg
    obtain ⟨H⟩ := Quotient.exact hg
    have e := L.act_homotopy hcharts hcover none g (.refl b) H
    change (act none _ = act none (.refl b)) at e
    have hg' := whisker_killed q (s b) (.refl b) (mk g) (by simpa only [act, whisker_refl, map_one] using e)
    change q (1 * _ * 1) = 1 at hg'
    simpa only [one_mul, mul_one] using! hg'

end
end PathTransport

universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v}
variable (f : ι → C(Circle, X))

/-!
# Genuine adjunction space for an arbitrary family of two-cells
The carrier is the quotient of the topological disjoint union of the original
space and the indexed closed complex unit disks. The relation is generated by
exactly the prescribed boundary identifications; the topology is the quotient
topology. No separation or finiteness assumptions are used.
-/
/-- The closed two-dimensional unit disk in the complex plane. -/
abbrev Disk := {z : ℂ // ‖z‖ ≤ 1}
/-- The inclusion of the unit circle into the closed disk. -/
def boundaryInclusion : C(Circle, Disk) where
  toFun z := ⟨z, le_of_eq (Circle.norm_coe z)⟩
  continuous_toFun := by fun_prop
/-- The actual topological disjoint union before attaching the disks. -/
abbrev Raw (X : Type u) (ι : Type v) := X ⊕ (Σ _ : ι, Disk)
/-- Only boundary points are identified with their prescribed attaching images. -/
inductive AttachingRel (f : ι → C(Circle, X)) : Raw X ι → Raw X ι → Prop
  | boundary (i : ι) (z : Circle) :
      AttachingRel f (.inr ⟨i, boundaryInclusion z⟩) (.inl (f i z))
/-- The adjunction quotient, with its induced quotient topology. -/
def Space := Quot (AttachingRel f)
instance : TopologicalSpace (Space f) :=
  inferInstanceAs (TopologicalSpace (Quot (AttachingRel f)))
/-- The quotient map from the unglued topological disjoint union. -/
def quotientMap : C(Raw X ι, Space f) :=
  ⟨Quot.mk _, continuous_quot_mk⟩
/-- The actual continuous inclusion of the original space. -/
def inclusion : C(X, Space f) where
  toFun x := quotientMap f (.inl x)
  continuous_toFun := (quotientMap f).continuous.comp continuous_inl
/-- The characteristic map of an attached closed disk. -/
def characteristic (i : ι) : C(Disk, Space f) :=
  (quotientMap f).comp ⟨fun z => .inr ⟨i,z⟩, continuous_inr.comp continuous_sigmaMk⟩
theorem characteristic_boundary (i : ι) :
    (characteristic f i).comp boundaryInclusion = (inclusion f).comp (f i) :=
  ContinuousMap.ext fun z => Quot.sound (.boundary i z)
/-- The quotient map is a quotient map, not merely a continuous surjection. -/
theorem quotientMap_isQuotientMap :
    Topology.IsQuotientMap (quotientMap f) := isQuotientMap_quot_mk
/-- The specified map on fundamental groups is induced by the actual inclusion. -/
def inclusionPi1 (x₀ : X) :
    FundamentalGroup X x₀ →* FundamentalGroup (Space f) (inclusion f x₀) :=
  FundamentalGroup.map (inclusion f) x₀

abbrev OpenDisk := {z : ℂ // ‖z‖ < 1}

lemma openDisk_subset_disk : {z : ℂ | ‖z‖ < 1} ⊆ {z | ‖z‖ ≤ 1} := fun z h => le_of_lt (a := ‖z‖) h

abbrev openDiskInclusion : C(OpenDisk, Disk) := .inclusion openDisk_subset_disk

abbrev rawInteriorMap (i : ι) (z : OpenDisk) : Raw X ι := .inr ⟨i, openDiskInclusion z⟩

def cellInteriorMap (i : ι) : C(OpenDisk, Space f) :=
  (characteristic f i).comp openDiskInclusion

def rawCoordinate : Raw X ι → ℂ := Sum.elim (fun _ => 0) fun w => w.2.1

/-- Interior representatives are isolated for the identifying relation. -/
@[simp] lemma rawInterior_eq {a : Raw X ι} (i : ι) (z : OpenDisk) :
    quotientMap f a = cellInteriorMap f i z ↔ a = rawInteriorMap i z := by
  refine ⟨fun h => ?_, fun h => congrArg (quotientMap f) h⟩
  let test : Space f → Prop := Quot.lift (· = rawInteriorMap i z) (by
    rintro _ _ ⟨j,w⟩
    apply propext
    simp only [Sum.inl_ne_inr, iff_false]
    intro e
    have h := congrArg (norm ∘ rawCoordinate) e
    exact z.2.ne (h.symm.trans (Circle.norm_coe w)))
  exact (congrArg test h).mpr rfl

/-- A single disk interior is openly embedded; the full quotient need not be open. -/
lemma cellInteriorMap_isOpenEmbedding (i : ι) : IsOpenEmbedding (cellInteriorMap f i) := by
  refine .of_continuous_injective_isOpenMap (cellInteriorMap f i).continuous ?_ ?_
  · intro z w h
    exact Subtype.ext (congrArg rawCoordinate ((rawInterior_eq f i w).mp h))
  · intro S hS
    rw [← (quotientMap_isQuotientMap f).isCoinducing.isOpen_preimage]
    have e : quotientMap f ⁻¹' (cellInteriorMap f i '' S) = rawInteriorMap i '' S := by
      ext a
      simp only [mem_preimage, mem_image, eq_comm (a := cellInteriorMap f i _), rawInterior_eq, eq_comm (a := a)]
    rw [e]
    have ho := (isOpen_lt continuous_norm continuous_const).isOpenMap_inclusion openDisk_subset_disk
    exact (isOpenMap_inr.comp ((isOpenMap_sigmaMk (i := i)).comp ho)) S hS

abbrev cellInterior (i : ι) : Set (Space f) := range (cellInteriorMap f i)

lemma interior_index_unique {y : Space f} {i j : ι}
    (hi : y ∈ cellInterior f i) (hj : y ∈ cellInterior f j) : i = j := by
  rcases hi with ⟨z,rfl⟩
  obtain ⟨w,h⟩ := hj
  exact (congrArg Sigma.fst (Sum.inr.inj ((rawInterior_eq f i z).mp h))).symm

/-- The neighborhood represented by the base and the nonzero disk coordinates. -/
def puncturedNeighborhood : Set (Space f) :=
  Quot.lift (fun
    | .inl _ => True
    | .inr ⟨_,z⟩ => (z : ℂ) ≠ 0) (by
      rintro _ _ ⟨i,z⟩
      simp [boundaryInclusion])

lemma isOpen_space_iff {S : Set (Space f)} :
    IsOpen S ↔ IsOpen (inclusion f ⁻¹' S) ∧ ∀ i, IsOpen (characteristic f i ⁻¹' S) := by
  rw [← (quotientMap_isQuotientMap f).isCoinducing.isOpen_preimage, isOpen_sum_iff, isOpen_sigma_iff]
  rfl

lemma puncturedNeighborhood_isOpen : IsOpen (puncturedNeighborhood f) :=
  (isOpen_space_iff f).mpr ⟨isOpen_univ, fun _ => isOpen_ne.preimage continuous_subtype_val⟩

lemma cover_cells (y : Space f) : ∃ i, y ∈ PathTransport.charts (puncturedNeighborhood f) (cellInterior f) i := by
  rcases y with ⟨x | ⟨i,z,hz⟩⟩
  · exact ⟨none,trivial⟩
  · rcases eq_or_ne z 0 with rfl | h
    · exact ⟨some i,⟨0,by simp⟩,rfl⟩
    · exact ⟨none,h⟩

/-! The complex circle generator, via the exponential covering.
The original backport was based on work by Ruize Chen (2026) and Junyan Xu (2025)
in Mathlib, released under the Apache 2.0 license.
-/
/-- The standard positively oriented circle loop, `t ↦ exp(2πt)`, based at `1`. -/
def circleGenerator : Path (1 : Circle) 1 where
  toFun t := Circle.exp ((t : ℝ) * (2 * Real.pi))
  source' := by simp
  target' := by simp
  continuous_toFun := by fun_prop
/-- The corresponding homotopy class in the actual fundamental group. -/
def circleGeneratorClass : FundamentalGroup Circle (1 : Circle) :=
  .mk circleGenerator
lemma circleGenerator_generates (g : FundamentalGroup Circle 1) :
    ∃ n : ℤ, circleGeneratorClass ^ n = g := by
  let cov := Circle.isAddQuotientCoveringMap_exp
  let a : AddSubgroup.zmultiples (2 * Real.pi) := ⟨_, AddSubgroup.mem_zmultiples _⟩
  let e := cov.fundamentalGroupEquiv ⟨0,Circle.exp_zero⟩
  let l : C(I, ℝ) := ⟨fun t => t * (2 * Real.pi), by fun_prop⟩
  have h : e circleGeneratorClass = MulOpposite.op (Multiplicative.ofAdd a) := by
    apply cov.fundamentalGroupToMulOpposite_apply_eq_Iff.mpr
    change (a : ℝ) + 0 = cov.isCoveringMap.liftPath circleGenerator 0 _ 1
    rw [← (cov.isCoveringMap.eq_liftPath_iff' (Γ := l) _).mpr ⟨rfl, by simp [l]⟩]
    simp [a, l]
  obtain ⟨n, hn⟩ := (e g).unop.toAdd.2
  refine ⟨n, e.injective ?_⟩
  rw [map_zpow, h]
  exact MulOpposite.unop_injective (Subtype.ext hn)

/-! Use polar coordinates from mathlib. Restrict the radius to the appropriate real interval. -/
abbrev PolarDisk := Circle × Ioc (0 : ℝ) 1
abbrev Annulus := Circle × Ioo (0 : ℝ) 1
/-- Polar coordinates on a disk with a specified radial bound and its center deleted. -/
def polarModel (P : ℝ → Prop) :
    (Circle × {r : ℝ // 0 < r ∧ P r}) ≃ₜ {z : {z : ℂ // P ‖z‖} // (z : ℂ) ≠ 0} where
  toFun p :=
    ⟨⟨(p.2 : ℝ) • (p.1 : ℂ), by simpa [abs_of_nonneg p.2.2.1.le] using p.2.2.2⟩,
      smul_ne_zero p.2.2.1.ne' (Circle.coe_ne_zero p.1)⟩
  invFun z :=
    let p := homeomorphUnitSphereProd ℂ ⟨z.1,z.2⟩
    have h : P (p.2 : ℝ) := (homeomorphUnitSphereProd_apply_snd_coe ℂ ⟨z.1,z.2⟩).symm ▸ z.1.2
    (p.1, ⟨p.2, p.2.2, h⟩)
  left_inv p := by
    have e := (homeomorphUnitSphereProd ℂ).apply_symm_apply (p.1, ⟨p.2,p.2.2.1⟩)
    exact Prod.ext congr(($e).1) (Subtype.ext congr(($e).2.1))
  right_inv z := by
    have e := (homeomorphUnitSphereProd ℂ).symm_apply_apply ⟨z.1,z.2⟩
    exact Subtype.ext (Subtype.ext congr(($e).1))

abbrev diskFromPolar (p : PolarDisk) : Disk := (polarModel (· ≤ 1) p).1

def diskCoords (z : Disk) : PolarDisk :=
  if hz : (z : ℂ) ≠ 0 then (polarModel (· ≤ 1)).symm ⟨z,hz⟩ else (1,1)

@[simp] lemma diskCoords_fromPolar (p : PolarDisk) : diskCoords (diskFromPolar p) = p := by
  erw [diskCoords, dite_eq_left (polarModel (· ≤ 1) p).2]
  exact (polarModel (· ≤ 1)).symm_apply_apply p

instance annulus_pathConnectedSpace : PathConnectedSpace Annulus := by
  let := ((convex_Ioo (𝕜 := ℝ) (0 : ℝ) 1).contractibleSpace (nonempty_Ioo.mpr zero_lt_one))
  infer_instance

@[simp] lemma diskFromPolar_top (z : Circle) : diskFromPolar (z,1) = boundaryInclusion z :=
  Subtype.ext (one_smul ℝ (z : ℂ))

/-- Interpolate to radius one while fixing the angle. -/
def radialDeformation : C(PolarDisk × I, PolarDisk) where
  toFun := fun (p,t) => (p.1, ⟨AffineMap.lineMap (p.2 : ℝ) 1 (t : ℝ),
    (convex_Ioc (𝕜 := ℝ) 0 1).lineMap_mem p.2.2 ⟨zero_lt_one,le_rfl⟩ t.2⟩)
  continuous_toFun := by simp only [AffineMap.lineMap_apply]; fun_prop

/-! ### The punctured neighborhood retracts onto the original space -/
abbrev neighborhoodInclusion : C(X, puncturedNeighborhood f) :=
  PathTransport.intoChart (inclusion f) fun _ => trivial

abbrev neighborhoodCell (i : ι) : C(PolarDisk, puncturedNeighborhood f) :=
  PathTransport.intoChart ((characteristic f i).comp ⟨diskFromPolar, (polarModel (· ≤ 1)).continuous.subtype_val⟩)
    fun p => (polarModel (· ≤ 1) p).2

@[simp] lemma neighborhoodCell_top (i : ι) (z : Circle) :
    neighborhoodCell f i (z,1) = neighborhoodInclusion f (f i z) := by
  refine Subtype.ext (show characteristic f i (diskFromPolar (z,1)) = _ from ?_)
  rw [diskFromPolar_top]
  exact DFunLike.congr_fun (characteristic_boundary f i) z

section Descend
variable {Z : Type*} [TopologicalSpace Z]
variable (base : C(X, Z)) (cell : ι → C(PolarDisk, Z))
variable (boundary : ∀ i z, cell i (z,1) = base (f i z))

/-- Descend a compatible map from the base and the punctured disks. The values
at the centers are only used to define the lift on the entire quotient;
continuity is proved on the punctured neighborhood. -/
def descend : C(puncturedNeighborhood f, Z) := by
  let F : Space f → Z := Quot.lift (Sum.elim base fun w => cell w.1 (diskCoords w.2)) (by
    rintro _ _ ⟨i,z⟩
    change cell i (diskCoords (boundaryInclusion z)) = base (f i z)
    rw [← diskFromPolar_top, diskCoords_fromPolar, boundary])
  refine ⟨fun y => F y, ContinuousOn.domRestrict ?_⟩
  apply (continuousOn_open_iff (puncturedNeighborhood_isOpen f)).mpr
  intro S hS
  refine (isOpen_space_iff f).mpr ⟨?_, fun i => ?_⟩
  · change IsOpen (univ ∩ base ⁻¹' S)
    simpa using hS.preimage base.continuous
  have hd : ContinuousOn diskCoords {z : Disk | (z : ℂ) ≠ 0} :=
    continuousOn_iff_continuous_domRestrict.mpr <|
      (polarModel (· ≤ 1)).symm.continuous.congr fun z => by
        change _ = diskCoords z
        simp [diskCoords,z.2]; rfl
  exact (continuousOn_open_iff (isOpen_ne.preimage continuous_subtype_val)).mp
    ((cell i).continuous.comp_continuousOn hd) S hS

@[simp] lemma descend_cell (i : ι) (p : PolarDisk) :
    descend f base cell boundary (neighborhoodCell f i p) = cell i p := by
  change cell i (diskCoords (diskFromPolar p)) = _
  rw [diskCoords_fromPolar]
end Descend

abbrev neighborhoodRetraction : C(puncturedNeighborhood f, X) :=
  descend f (.id _) (fun i => (f i).comp .fst) (fun _ _ => rfl)

def radialTrack : C(puncturedNeighborhood f, C(I, puncturedNeighborhood f)) :=
  descend f (ContinuousMap.const'.comp (neighborhoodInclusion f)) (fun i => ((neighborhoodCell f i).comp radialDeformation).curry)
    (by intro i z; ext t; simp [radialDeformation])

@[simp] lemma neighborhoodRetraction_cell (i : ι) (p : PolarDisk) :
    neighborhoodRetraction f (neighborhoodCell f i p) = f i p.1 := descend_cell ..

/-- Joint radial deformation, fixing the original space pointwise. -/
def neighborhoodDeformation :
    (ContinuousMap.id _).Homotopy
      ((neighborhoodInclusion f).comp (neighborhoodRetraction f)) := by
  refine ⟨(radialTrack f).uncurry.comp .prodSwap, ?_, ?_⟩
  all_goals
    rintro ⟨⟨x | ⟨i,z⟩⟩,hy⟩
    · rfl
    obtain ⟨p : PolarDisk,hp⟩ := (polarModel (· ≤ 1)).surjective ⟨z,hy⟩
    obtain rfl := congrArg Subtype.val hp
    first
    | change radialTrack f (neighborhoodCell f i p) 0 = neighborhoodCell f i p
    | change radialTrack f (neighborhoodCell f i p) 1 =
        neighborhoodInclusion f (neighborhoodRetraction f (neighborhoodCell f i p))
    simp [radialTrack, radialDeformation]

variable (x₀ : X)

def cellOverlapHomeomorph (i : ι) : Annulus ≃ₜ ↥(puncturedNeighborhood f ∩ cellInterior f i) := by
  refine (polarModel (· < 1)).trans <| (Homeomorph.setCongr ?_).trans <|
    (cellInteriorMap_isOpenEmbedding f i).isEmbedding.homeomorphOfSubsetRange inter_subset_right
  ext z
  exact (and_iff_left (mem_range_self z)).symm

instance openDisk_contractibleSpace : ContractibleSpace OpenDisk :=
  (by simpa [Metric.ball, dist_zero_right] using convex_ball (0 : ℂ) 1 :
    Convex ℝ {z : ℂ | ‖z‖ < 1}).contractibleSpace ⟨0, by simp⟩

instance disk_contractibleSpace : ContractibleSpace Disk :=
  (by simpa [Metric.closedBall, dist_zero_right] using convex_closedBall (0 : ℂ) 1 :
    Convex ℝ {z : ℂ | ‖z‖ ≤ 1}).contractibleSpace ⟨0, by simp⟩

/-! ### Attaching loops and the exact fundamental-group statement -/
section
variable (γ : ∀ i, Path x₀ (f i 1))

/-- The actual attaching loop in X, whiskered chronologically from the basepoint
along a chosen path, around the attaching circle once, and back. -/
def attachingLoop (i : ι) : Path x₀ x₀ :=
  (γ i).trans ((circleGenerator.map (f i).continuous).trans (γ i).symm)
/-- Its class in Mathlib's ordinary continuous-path fundamental group. -/
def attachingLoopClass : ι → FundamentalGroup X x₀ :=
  fun i => .mk (attachingLoop f x₀ γ i)
/-- Precisely the normal subgroup generated by the chosen conjugated attaching loops. -/
def attachingNormalClosure : Subgroup (FundamentalGroup X x₀) :=
  Subgroup.normalClosure (Set.range (attachingLoopClass f x₀ γ))
instance attachingNormalClosure_normal : (attachingNormalClosure f x₀ γ).Normal := by
  unfold attachingNormalClosure
  infer_instance
end

/-- The full arbitrary-family two-cell attachment theorem, including compatibility
of the quotient equivalence with the actual inclusion-induced map. The index
universe and the space universe are independent. -/
def completeStatement : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [PathConnectedSpace X] {ι : Type v}
    (f : ι → C(Circle, X)) (x₀ : X) (γ : ∀ i, Path x₀ (f i 1)),
    Function.Surjective (inclusionPi1 f x₀) ∧
    (inclusionPi1 f x₀).ker = attachingNormalClosure f x₀ γ ∧
    ∃ e : FundamentalGroup X x₀ ⧸ attachingNormalClosure f x₀ γ ≃*
      FundamentalGroup (Space f) (inclusion f x₀),
      e.toMonoidHom.comp (QuotientGroup.mk' (attachingNormalClosure f x₀ γ)) =
        inclusionPi1 f x₀

open PathTransport

/-- The actual inclusion is surjective with the required kernel and a compatible quotient equivalence. -/
theorem two_cell_attachment : completeStatement.{u,v} := by
  intro X _ _ ι f x₀ γ
  let N := attachingNormalClosure f x₀ γ
  let q₀ := QuotientGroup.mk' N
  let path i := mk (γ i)
  -- Each attaching loop bounds its characteristic disk in the quotient.
  have hN : N ≤ (inclusionPi1 f x₀).ker := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i,rfl⟩
    change FundamentalGroup.map (inclusion f) x₀
      (whisker (path i) (path i) (circleGeneratorClass.toPath.map (f i))) = 1
    have h : circleGeneratorClass.toPath.map ((inclusion f).comp (f i)) = .refl _ := by
      rw [← characteristic_boundary f i, map_comp]
      exact congrArg (·.map (characteristic f i))
        (Subsingleton.elim (circleGeneratorClass.toPath.map boundaryInclusion) (.refl _))
    rw [whisker_map, ← map_comp, h]
    exact whisker_refl _
  let inc := neighborhoodInclusion f
  let b := inc x₀
  let r := neighborhoodRetraction f
  let H := neighborhoodDeformation f
  let q := q₀.comp (FundamentalGroup.map r b)
  let m := QuotientGroup.lift N (inclusionPi1 f x₀) hN
  have factor g : m (q g) = FundamentalGroup.map (ContinuousMap.subtypeVal (puncturedNeighborhood f)) b g := by
    obtain ⟨p,rfl⟩ := mk_surjective g
    have h := Path.Homotopic.Quotient.eq.mpr (Path.Homotopic.map_trans_evalAt H p)
    change (mk p).trans (.refl b) = (Path.Homotopic.Quotient.refl b).trans (mk _) at h
    rw [Path.Homotopic.Quotient.trans_refl, Path.Homotopic.Quotient.refl_trans] at h
    exact congrArg (·.map (ContinuousMap.subtypeVal _)) h.symm
  let reach y := mk (((PathConnectedSpace.somePath x₀ (r y)).map inc.continuous).trans (H.evalAt y).symm)
  let a : Annulus := (1, ⟨1 / 2, by norm_num, by norm_num⟩)
  let j i := (left (puncturedNeighborhood f) (cellInterior f i)).comp (toContinuousMap (cellOverlapHomeomorph f i))
  -- On each overlap the retraction is the angle projection followed by the attaching map.
  have kill i c (g : FundamentalGroup Annulus a) : q (whisker c c (g.toPath.map (j i))) = 1 := by
    change q₀ (FundamentalGroup.map r b _) = 1
    rw [whisker_map, ← map_comp]
    suffices ∀ c, q₀ (whisker c c (g.toPath.map (r.comp (j i)))) = 1 from this _
    rw [show r.comp (j i) = (f i).comp .fst from
      ContinuousMap.ext fun z => neighborhoodRetraction_cell f i (z.1, ⟨z.2,z.2.2.1,z.2.2.2.le⟩), map_comp]
    intro d
    apply whisker_killed (c := path i)
    let e := q₀.comp ((whiskerEquiv (path i)).toMonoidHom.comp (FundamentalGroup.map (f i) 1))
    change e (FundamentalGroup.map .fst a g) = 1
    obtain ⟨n,hn⟩ := circleGenerator_generates (FundamentalGroup.map .fst a g)
    have he : e circleGeneratorClass = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure (mem_range_self i))
    simp only [← hn, map_zpow, he, one_zpow]
  obtain ⟨hs,hk⟩ := glue (V := cellInterior f) b reach (puncturedNeighborhood_isOpen f)
    (fun i => (cellInteriorMap_isOpenEmbedding f i).isOpen_range) (cover_cells f)
    (interior_index_unique f)
    (fun i => (cellInteriorMap_isOpenEmbedding f i).isEmbedding.toHomeomorph.symm.toHomotopyEquiv.simplyConnectedSpace)
    (cellOverlapHomeomorph f) a q m factor kill
  have su := hs.comp (QuotientGroup.mk'_surjective N)
  have ke : (inclusionPi1 f x₀).ker = N := le_antisymm (by
    rintro ⟨l⟩ hl
    exact (QuotientGroup.eq_one_iff _).mp (@hk (mk (l.map inc.continuous)) hl)) hN
  exact ⟨su,ke,QuotientGroup.liftEquiv _ su ke.symm,rfl⟩

end CellAttachment
