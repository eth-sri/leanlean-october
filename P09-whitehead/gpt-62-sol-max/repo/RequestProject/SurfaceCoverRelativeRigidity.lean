module

public import RequestProject.GenusReceivedPolygonCoefficient
public import RequestProject.SurfaceDual
public import RequestProject.FinsuppBasis
public import Mathlib.LinearAlgebra.Finsupp.Supported

@[expose] public section

/-! Relative coefficient propagation in actual covers of the polygon surface. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
open ASC
variable {P Q : Type} [PartialOrder P] [PartialOrder Q]
  {f : P → Q} (hf : IsPosetCover f)

theorem cover_lt_of_image {a b : P} (hab : a ≤ b) (h : f a < f b) : a < b :=
  lt_of_le_of_ne hab (fun he => h.ne (congrArg f he))

/-- A predicate having two elements lifts through unique existence over its image. -/
private theorem exactlyTwo_lift {X Y : Type} {f : X → Y} {R : X → Prop} {T : Y → Prop}
    (h : ExactlyTwo T) (hm : ∀ p, R p → T (f p))
    (hl : ∀ q, T q → ∃! p, R p ∧ f p = q) : ExactlyTwo R := by
  obtain ⟨a, b, hab, ha, hb, hall⟩ := h
  obtain ⟨x, ⟨hx, hxa⟩, hux⟩ := hl a ha
  obtain ⟨y, ⟨hy, hyb⟩, huy⟩ := hl b hb
  refine ⟨x, y, by grind, hx, hy, ?_⟩
  intro z hz
  exact (hall (f z) (hm z hz)).imp (fun h => hux z ⟨hz, h⟩) (fun h => huy z ⟨hz, h⟩)

/-- All local surface incidences lift through a genuine poset cover. -/
noncomputable def coveredSurfaceRank (S : SurfaceRank Q) : SurfaceRank P where
  rk a := S.rk (f a)
  rk_lt_of_lt h := S.rk_lt_of_lt (hf.strictMono h)
  rk_le_two a := S.rk_le_two (f a)
  two_vertices e he := by
    apply exactlyTwo_lift (S.two_vertices (f e) he) (fun _ h => hf.strictMono h)
    intro a ha
    obtain ⟨v, ⟨hv, rfl⟩, hvu⟩ := hf.down e a ha.le
    exact ⟨v, ⟨cover_lt_of_image hv ha, rfl⟩, fun z hz => hvu z ⟨hz.1.le, hz.2⟩⟩
  two_faces e he := by
    apply exactlyTwo_lift (S.two_faces (f e) he) (fun _ h => hf.strictMono h)
    intro a ha
    obtain ⟨v, ⟨hv, rfl⟩, hvu⟩ := hf.up e a ha.le
    exact ⟨v, ⟨cover_lt_of_image hv ha, rfl⟩, fun z hz => hvu z ⟨hz.1.le, hz.2⟩⟩
  two_edges v t hv ht hvt := by
    apply exactlyTwo_lift (S.two_edges (f v) (f t) hv ht (hf.strictMono hvt))
      (fun _ h => ⟨hf.strictMono h.1, hf.strictMono h.2⟩)
    intro a ha
    obtain ⟨e, hve, het, rfl⟩ := hf.exists_interval_lift hvt.le a ha.1.le ha.2.le
    exact ⟨e, ⟨⟨cover_lt_of_image hve ha.1, cover_lt_of_image het ha.2⟩, rfl⟩,
      fun _ h => hf.up_inj h.1.1.le hve h.2⟩
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

open scoped Classical

/-- At an edge, all incident triangles contribute with the same sign, given by the endpoint ranks. -/
private theorem surfaceBoundary_pair {e : StrictOrdEdge P} {a b : StrictOrdTri P}
    (hab : a ≠ b) (h : ∀ r, strictTriangleEdge01 r = e ∨ strictTriangleEdge12 r = e ∨
      strictTriangleEdge02 r = e ↔ r = a ∨ r = b) (c : StrictOrdTri P →₀ ℤ) :
    Comb.bdry2 (strictOrderCx P) c e =
      (if S.rk e.1.1 = 0 ∧ S.rk e.1.2 = 2 then -1 else 1) * (c a + c b) := by
  finsupp_basis c
  intro r
  erw [strictTriangle_bdry2_single, Finsupp.sub_apply, Finsupp.add_apply]
  have hr := triangle_rank S r
  have hs₁ (he : strictTriangleEdge01 r = e) : S.rk e.1.1 = 0 ∧ S.rk e.1.2 = 1 :=
    he ▸ ⟨hr.1, hr.2.1⟩
  have hs₂ (he : strictTriangleEdge12 r = e) : S.rk e.1.1 = 1 ∧ S.rk e.1.2 = 2 :=
    he ▸ hr.2
  have hs₃ (he : strictTriangleEdge02 r = e) : S.rk e.1.1 = 0 ∧ S.rk e.1.2 = 2 :=
    he ▸ ⟨hr.1, hr.2.2⟩
  simp only [Finsupp.single_apply]
  have H := h r
  split_ifs <;> grind

private theorem surface_zero_pair (c : StrictOrdTri P →₀ ℤ) {e : StrictOrdEdge P}
    {a b : StrictOrdTri P}
    (h : a ≠ b → ∀ r, strictTriangleEdge01 r = e ∨ strictTriangleEdge12 r = e ∨
      strictTriangleEdge02 r = e ↔ r = a ∨ r = b)
    (hd : bdry2 (strictOrderCx P) c e = 0) (ha : c a = 0) : c b = 0 := by
  by_cases hab : a = b
  · exact hab ▸ ha
  have he := surfaceBoundary_pair S hab (h hab) c
  erw [hd, ha, zero_add] at he
  split_ifs at he <;> omega

omit S in
private theorem exactlyTwo_exhaust {X : Type} {R : X → Prop} (h : ExactlyTwo R)
    {a b : X} (ha : R a) (hb : R b) (hab : a ≠ b) :
    ∀ x, R x → x = a ∨ x = b := by
  obtain ⟨x, y, _, _, _, hall⟩ := h
  intro z hz
  grind

variable (c : StrictOrdTri P →₀ ℤ)

private theorem surface_zero_change_vertex {a b e t : P}
    (hae : a < e) (hbe : b < e) (het : e < t)
    (hd : bdry2 (strictOrderCx P) c ⟨(e, t), het⟩ = 0)
    (hz : c ⟨(a, e, t), hae, het⟩ = 0) :
    c ⟨(b, e, t), hbe, het⟩ = 0 := by
  apply surface_zero_pair S c _ hd hz
  intro h r
  have hr := triangle_rank S r
  have hrk := S.rk_flag hae het
  have hall := exactlyTwo_exhaust (S.two_vertices e hrk.2.1) hae hbe
    (fun he => h (by subst b; rfl))
  simp only [strictTriangleEdge01, strictTriangleEdge12, strictTriangleEdge02,
    Subtype.ext_iff, Prod.mk.injEq, StrictOrdEdge, StrictOrdTri]
  have := r.2.1
  grind

private theorem surface_zero_change_edge {v a b t : P}
    (hva : v < a) (hat : a < t) (hvb : v < b) (hbt : b < t)
    (hd : bdry2 (strictOrderCx P) c ⟨(v, t), hva.trans hat⟩ = 0)
    (hz : c ⟨(v, a, t), hva, hat⟩ = 0) :
    c ⟨(v, b, t), hvb, hbt⟩ = 0 := by
  apply surface_zero_pair S c _ hd hz
  intro h r
  have hr := triangle_rank S r
  have hrk := S.rk_flag hva hat
  have hall := exactlyTwo_exhaust (S.two_edges v t hrk.1 hrk.2.2 (hva.trans hat))
    ⟨hva, hat⟩ ⟨hvb, hbt⟩ (fun he => h (by subst b; rfl))
  simp only [strictTriangleEdge01, strictTriangleEdge12, strictTriangleEdge02,
    Subtype.ext_iff, Prod.mk.injEq, StrictOrdEdge, StrictOrdTri]
  have := r.2.1
  have := r.2.2
  grind

/-- A zero flag coefficient crosses a shared edge with zero relative boundary. -/
theorem surface_zero_change_face {v e a b : P}
    (hve : v < e) (hea : e < a) (heb : e < b)
    (hd : bdry2 (strictOrderCx P) c ⟨(v, e), hve⟩ = 0)
    (hz : c ⟨(v, e, a), hve, hea⟩ = 0) :
    c ⟨(v, e, b), hve, heb⟩ = 0 := by
  apply surface_zero_pair S c _ hd hz
  intro h r
  have hr := triangle_rank S r
  have hrk := S.rk_flag hve hea
  have hall := exactlyTwo_exhaust (S.two_faces e hrk.2.1) hea heb
    (fun he => h (by subst b; rfl))
  simp only [strictTriangleEdge01, strictTriangleEdge12, strictTriangleEdge02,
    Subtype.ext_iff, Prod.mk.injEq, StrictOrdEdge, StrictOrdTri]
  have := r.2.2
  grind

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
    have h₁  :=
      surface_zero_change_edge S c hve het hvr hrt (hrel _ hrk.2.2) ha
    have h₂  :=
      surface_zero_change_vertex S c hvr hwr hrt (hrel _ hrk.2.2) h₁
    exact surface_zero_change_edge S c hwr hrt hwd hdt (hrel _ hrk.2.2) h₂

end Coefficients
end FiniteChains.Comb

namespace FiniteChains.Davis
open Comb ASC Cell
variable {κ ι P : Type} {M : ℕ} [NeZero M] [PartialOrder P]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)
  (hd : PolygonData vc ec) (f : P → SCell vc ec hc) (hf : IsPosetCover f)

/-- The boundary of a relative surface chain is supported on the polygon boundary. -/
noncomputable def polygonRelativeSubmodule : Submodule ℤ (StrictOrdTri P →₀ ℤ) :=
  (Finsupp.supported ℤ ℤ {e : StrictOrdEdge P |
    InPolygonBoundary hc (f e.1.1) ∧ InPolygonBoundary hc (f e.1.2)}).comap
      (Comb.bdry2 (strictOrderCx P))

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
    tauto)
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
    ((polygonRelativeSubmodule hc f).sub_mem hc' hd')
  erw [map_sub, hpoles, sub_self]

end FiniteChains.Davis
