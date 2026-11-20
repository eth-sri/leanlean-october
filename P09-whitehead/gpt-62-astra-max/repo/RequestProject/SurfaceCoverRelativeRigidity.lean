module

public import Mathlib.LinearAlgebra.Finsupp.Supported
public import RequestProject.GenusReceivedPolygonCoefficient
public import RequestProject.SurfaceDual

@[expose] public section

/-! Relative coefficient propagation in actual covers of the polygon surface. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
open ASC
variable {P Q : Type} [PartialOrder P] [PartialOrder Q]
  {f : P → Q} (hf : IsPosetCover f)

theorem cover_lt_of_image {a b : P} (hab : a ≤ b) (h : f a < f b) : a < b :=
  lt_of_le_of_ne hab (fun he => h.ne (congrArg f he))

/-- Pull a two-element incidence fibre back along a bijection on that fibre. -/
private theorem liftExactlyTwo {A : P → Prop} {B : Q → Prop} (h : ExactlyTwo B)
    (pres : ∀ x, A x → B (f x)) (onto : ∀ y, B y → ∃ x, A x ∧ f x = y)
    (inj : ∀ x y, A x → A y → f x = f y → x = y) : ExactlyTwo A := by
  obtain ⟨u, v, huv, hu, hv, hall⟩ := h
  obtain ⟨a, ha, hfa⟩ := onto u hu
  obtain ⟨b, hb, hfb⟩ := onto v hv
  exact ⟨a, b, by grind, ha, hb, fun x hx => by specialize hall _ (pres x hx); grind⟩

/-- All local surface incidences lift through a genuine poset cover. -/
noncomputable def coveredSurfaceRank (S : SurfaceRank Q) : SurfaceRank P where
  rk a := S.rk _
  rk_lt_of_lt h := S.rk_lt_of_lt (hf.strictMono h)
  rk_le_two a := S.rk_le_two _
  two_vertices e he := by
    apply liftExactlyTwo (f := f) (S.two_vertices _ he) (fun _ h => hf.strictMono h) _
      (fun _ _ hx hy => hf.down_inj hx.le hy.le)
    intro y hy
    obtain ⟨x, ⟨hx, he⟩, _⟩ := hf.down e y hy.le
    exact ⟨x, cover_lt_of_image hx (he.symm ▸ hy), he⟩
  two_faces e he := by
    apply liftExactlyTwo (f := f) (S.two_faces _ he) (fun _ h => hf.strictMono h) _
      (fun _ _ hx hy => hf.up_inj hx.le hy.le)
    intro y hy
    obtain ⟨x, ⟨hx, he⟩, _⟩ := hf.up e y hy.le
    exact ⟨x, cover_lt_of_image hx (he.symm ▸ hy), he⟩
  two_edges v t hv ht hvt := by
    apply liftExactlyTwo (f := f) (S.two_edges _ _ hv ht (hf.strictMono hvt))
      (fun _ h => ⟨hf.strictMono h.1, hf.strictMono h.2⟩) _
      (fun _ _ hx hy => hf.up_inj hx.1.le hy.1.le)
    intro y hy
    obtain ⟨x, hvx, hxt, he⟩ := hf.exists_interval_lift hvt.le y hy.1.le hy.2.le
    exact ⟨x, ⟨cover_lt_of_image hvx (he.symm ▸ hy.1), cover_lt_of_image hxt (he.symm ▸ hy.2)⟩, he⟩
  exists_face x := by
    obtain ⟨t, ht, hxt⟩ := S.exists_face _
    obtain ⟨t', ⟨hxt', hft⟩, _⟩ := hf.up x t hxt <;> grind
  exists_vertex t ht := by
    obtain ⟨v, hv, hvt⟩ := S.exists_vertex _ ht
    obtain ⟨v', ⟨hv't, hfv⟩, _⟩ := hf.down t v hvt.le
    exact ⟨v', hfv.symm ▸ hv, cover_lt_of_image hv't (hfv.symm ▸ hvt)⟩

/-- Triangular face geometry is preserved in every actual lifted face. -/
theorem coveredSurfaceRank_faceEdges (S : SurfaceRank Q) (hfe : FaceEdges S) :
    FaceEdges (coveredSurfaceRank hf S) := by
  intro v w t hv hw ht hvt hwt hvw
  obtain ⟨e, hve, hwe, het⟩ := hfe _ _ _ hv hw ht
    (hf.strictMono hvt) (hf.strictMono hwt) (fun he => hvw (hf.down_inj hvt.le hwt.le he))
  obtain ⟨e', hve', he't, hfe'⟩ := hf.exists_interval_lift hvt.le e hve.le het.le
  exact ⟨e', cover_lt_of_image hve' (hfe'.symm ▸ hve),
    cover_lt_of_image (hf.le_of_le_below hwt.le he't (hfe'.symm ▸ hwe.le)) (hfe'.symm ▸ hwe),
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
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]; ring
  | single r n =>
    rcases r with ⟨⟨x, y, z⟩, hxy, hyz⟩
    have := S.rk_flag hxy hyz
    have := S.rk_flag hae het
    erw [strictTriangle_bdry2_single, Finsupp.sub_apply, Finsupp.add_apply]
    simp [strictTriangleEdge01, strictTriangleEdge12, strictTriangleEdge02, Finsupp.single_apply]
    grind

/-- At a vertex/face diagonal the two incident flags both occur negatively. -/
theorem surfaceBoundary_edge_pair {v a b t : P}
    (hva : v < a) (hat : a < t) (hvb : v < b) (hbt : b < t) (hab : a ≠ b)
    (hall : ∀ x, v < x ∧ x < t → x = a ∨ x = b)
    (c : StrictOrdTri P →₀ ℤ) :
    Comb.bdry2 (strictOrderCx P) c ⟨(v, t), hva.trans hat⟩ =
      -c ⟨(v, a, t), hva, hat⟩ - c ⟨(v, b, t), hvb, hbt⟩ := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]; ring
  | single r n =>
    rcases r with ⟨⟨x, y, z⟩, hxy, hyz⟩
    have := S.rk_flag hxy hyz
    have := S.rk_flag hva hat
    erw [strictTriangle_bdry2_single, Finsupp.sub_apply, Finsupp.add_apply]
    simp [strictTriangleEdge01, strictTriangleEdge12, strictTriangleEdge02, Finsupp.single_apply]
    grind

/-- At a vertex/edge incidence the two flags in the adjacent faces occur positively. -/
theorem surfaceBoundary_face_pair {v e a b : P}
    (hve : v < e) (hea : e < a) (heb : e < b) (hab : a ≠ b)
    (hall : ∀ x, e < x → x = a ∨ x = b)
    (c : StrictOrdTri P →₀ ℤ) :
    Comb.bdry2 (strictOrderCx P) c ⟨(v, e), hve⟩ =
      c ⟨(v, e, a), hve, hea⟩ + c ⟨(v, e, b), hve, heb⟩ := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]; ring
  | single r n =>
    rcases r with ⟨⟨x, y, z⟩, hxy, hyz⟩
    have := S.rk_flag hxy hyz
    have := S.rk_flag hve hea
    erw [strictTriangle_bdry2_single, Finsupp.sub_apply, Finsupp.add_apply]
    simp [strictTriangleEdge01, strictTriangleEdge12, strictTriangleEdge02, Finsupp.single_apply]
    grind

end Coefficients

theorem exactlyTwo_exhaust {X : Type} {R : X → Prop} (h : ExactlyTwo R)
    {a b : X} (ha : R a) (hb : R b) (hab : a ≠ b) :
    ∀ x, R x → x = a ∨ x = b := by
  obtain ⟨x, y, _, _, _, hall⟩ := h <;> grind

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
  · have hpair := surfaceBoundary_vertex_pair S hae hbe het hab
      (exactlyTwo_exhaust (S.two_vertices e (S.rk_flag hae het).2.1) hae hbe hab) c
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
  · have hpair := surfaceBoundary_face_pair S hve hea heb hab
      (exactlyTwo_exhaust (S.two_faces e (S.rk_flag hve hea).2.1) hea heb hab) c
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
  by_cases hvw : v = w
  · subst w
    exact surface_zero_change_edge S c hve het hwd hdt (hrel _ hrk.2.2) ha
  · obtain ⟨r, hvr, hwr, hrt⟩ := hfe v w t hrk.1 (S.rk_flag hwd hdt).1 hrk.2.2
      (hve.trans het) (hwd.trans hdt) hvw
    have h₂ :=
      surface_zero_change_vertex S c hvr hwr hrt (hrel _ hrk.2.2) (surface_zero_change_edge S c hve het hvr hrt (hrel _ hrk.2.2) ha)
    exact surface_zero_change_edge S c hwr hrt hwd hdt (hrel _ hrk.2.2) h₂

end Propagation
end FiniteChains.Comb

namespace FiniteChains.Davis
open Comb ASC Cell
variable {κ ι P : Type} {M : ℕ} [NeZero M] [PartialOrder P]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)
  (hd : PolygonData vc ec) (f : P → SCell vc ec hc) (hf : IsPosetCover f)

/-- Relative chains form the inverse image, under the boundary, of the
submodule of edge chains supported on the polygon boundary. -/
noncomputable def polygonRelativeSubmodule : Submodule ℤ (StrictOrdTri P →₀ ℤ) :=
  (Finsupp.supported ℤ ℤ {e : StrictOrdEdge P | InPolygonBoundary hc (f e.1.1) ∧
    InPolygonBoundary hc (f e.1.2)}).comap (Comb.bdry2 (strictOrderCx P))

abbrev PolygonRelativeChain (c : StrictOrdTri P →₀ ℤ) := c ∈ polygonRelativeSubmodule hc f

theorem polygonBoundary_rank_le_one {a : SCell vc ec hc}
    (ha : InPolygonBoundary hc a) : Cell.rk a ≤ 1 := by
  cases a <;> simp_all [InPolygonBoundary, Cell.rk]

section

variable (c : StrictOrdTri P →₀ ℤ) (hrel : PolygonRelativeChain hc f c)
include hrel

variable (e : StrictOrdEdge P)

theorem polygonRelative_boundary_zero_of_target (he : ¬ InPolygonBoundary hc (f e.1.2)) :
    Comb.bdry2 (strictOrderCx P) c e = 0 := by
  by_contra hn
  exact he ((hrel (Finsupp.mem_support_iff.mpr hn)).2)

theorem polygonRelative_boundary_zero_at_face (he : Cell.rk (f e.1.2) = 2) :
    Comb.bdry2 (strictOrderCx P) c e = 0 := by
  grind [polygonRelative_boundary_zero_of_target, polygonBoundary_rank_le_one]

include hd hf in
theorem polygonRelative_zero_in_face
    (a b : StrictOrdTri P) (ht : a.1.2.2 = b.1.2.2) (ha : c a = 0) : c b = 0 :=
  surface_zero_in_face _ c
    (coveredSurfaceRank_faceEdges hf (surfaceRank_SCell hc hd) (faceEdges_SCell hc hd))
    (polygonRelative_boundary_zero_at_face hc f c hrel) a b ht ha

include hd in
/-- Every flag of every actual lifted inner triangle is forced by the pole
coefficients.  This propagates across all six flags, not only the two centre flags. -/
theorem polygonRelative_zero_inner
    (hpoles : polygonCoverPoleCoefficients hc f hf c = 0)
    (p : Fin M) (t : StrictOrdTri P) (ht : f t.1.2.2 = cI hc p) : c t = 0 := by
  let S := coveredSurfaceRank hf (surfaceRank_SCell hc hd)
  have hpole : ∀ a : StrictOrdTri P, f a.1.1 = cC hc → c a = 0 := by
    intro a ha
    have hh := polygonCoverPole_relative_ext hc f hf (by have := hd.three_le; omega) c 0 (polygonCover_boundary_vanishes_at_poles hc f c (fun e he => (hrel he).1))
      (by simp) (by erw [map_zero]; exact hpoles) a ha
    exact hh
  obtain ⟨v, ⟨hvt, hfv⟩, _⟩ := hf.down _ (cC hc)
    (by erw [ht]; exact (ctr_lt_inn hc p).le)
  have hvT := lt_of_le_of_ne hvt (by
    intro he
    exact (ctr_lt_inn hc p).ne (hfv.symm.trans ((congrArg f he).trans ht)))
  have hvrk : S.rk v = 0 := by change Cell.rk _ = 0; erw [hfv]; rfl
  obtain ⟨e, _, _, ⟨hve, heT⟩, _, _⟩ := S.two_edges v _ hvrk (S.rk_flag t.2.1 t.2.2).2.2 hvT
  let a : StrictOrdTri P := ⟨(v, e, t.1.2.2), hve, heT⟩
  exact polygonRelative_zero_in_face hc hd f hf c hrel a t rfl (hpole a hfv)

include hd hf in
/-- Move a zero coefficient from all flags over one actual face across an
internal edge to all flags over its adjacent actual face. -/
theorem polygonRelative_zero_across
    (t : StrictOrdTri P) (e a : SCell vc ec hc)
    (herk : Cell.rk e = 1) (het : e < f t.1.2.2) (hea : e < a)
    (heboundary : ¬ InPolygonBoundary hc e)
    (ha : ∀ z : StrictOrdTri P, f z.1.2.2 = a → c z = 0) : c t = 0 := by
  let S := coveredSurfaceRank hf (surfaceRank_SCell hc hd)
  obtain ⟨d, ⟨hdT, hfd⟩, _⟩ := hf.down _ e het.le
  have hdT' := lt_of_le_of_ne hdT (by
    grind)
  obtain ⟨a', ⟨hda, hfa⟩, _⟩ := hf.up d a (by grind)
  have hda' := lt_of_le_of_ne hda (by
    grind)
  obtain ⟨v, _, _, hvd, _, _⟩ := S.two_vertices d (by change Cell.rk (f d) = 1; grind)
  have hw := surface_zero_change_face S c hvd hda' hdT' (polygonRelative_boundary_zero_of_target hc f c hrel _ (hfd.symm ▸ heboundary)) (ha (⟨(v, d, a'), hvd, hda'⟩) hfa)
  exact polygonRelative_zero_in_face hc hd f hf c hrel (⟨(v, d, t.1.2.2), hvd, hdT'⟩) t rfl hw

section

variable (hpoles : polygonCoverPoleCoefficients hc f hf c = 0)
include hpoles

variable (p : Fin M) (t : StrictOrdTri P)

include hd in
/-- The genuine `ced` incidence carries rigidity from the fan into every
lifted inner collar triangle. -/
theorem polygonRelative_zero_inner_collar (ht : f t.1.2.2 = cT2 hc p) : c t = 0 := by
  apply polygonRelative_zero_across hc hd f hf c hrel t (cF hc p) _ rfl
  · erw [ht]
    exact lt_of_le_of_ne (cF_le_cT2 hc p) (by intro h; cases h)
  · exact lt_of_le_of_ne (cF_le_cI hc p) (by intro h; cases h)
  · solve_by_elim
  · apply polygonRelative_zero_inner <;> assumption

include hd in
/-- The genuine `gdi` incidence carries rigidity to every lifted outer
collar triangle.  The identified boundary is never crossed. -/
theorem polygonRelative_zero_outer_collar (ht : f t.1.2.2 = cT1 hc p) : c t = 0 := by
  apply polygonRelative_zero_across hc hd f hf c hrel t (cG hc p) _ rfl
  · erw [ht]
    exact lt_of_le_of_ne (cG_le_cT1 hc p) (by intro h; cases h)
  · exact lt_of_le_of_ne (cG_le_cT2 hc p) (by intro h; cases h)
  · solve_by_elim
  · apply polygonRelative_zero_inner_collar <;> assumption

include hd in
/-- The complete relative two-chain in an actual surface cover is detected by
its actual pole coefficients, after propagation through every fan and collar
flag.  No global connectedness or group faithfulness premise is used. -/
theorem polygonRelative_zero_of_pole_coefficients : c = 0 := by
  ext t
  have ht : Cell.rk _ = 2 := ((surfaceRank_SCell hc hd).rk_flag (hf.strictMono t.2.1) (hf.strictMono t.2.2)).2.2
  generalize he : f _ = a at ht
  cases a with
  | inn p => solve_by_elim [polygonRelative_zero_inner]
  | tr2 p => solve_by_elim [polygonRelative_zero_inner_collar]
  | tr1 p => solve_by_elim [polygonRelative_zero_outer_collar]
  | _ => simp_all [Cell.rk]

end

end

include hd in
/-- Full relative surface-chain reconstruction is unique for its finite family
of pole coefficients, including all six flags and both collar triangles. -/
theorem polygonRelative_ext
    (c d : StrictOrdTri P →₀ ℤ)
    (hc' : PolygonRelativeChain hc f c) (hd' : PolygonRelativeChain hc f d)
    (hpoles : polygonCoverPoleCoefficients hc f hf c =
      polygonCoverPoleCoefficients hc f hf d) : c = d := by
  apply sub_eq_zero.mp
  apply polygonRelative_zero_of_pole_coefficients hc hd f hf _
    ((polygonRelativeSubmodule hc f).sub_mem hc' hd') <;> simp_all

end FiniteChains.Davis
