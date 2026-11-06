module

public import RequestProject.GenusReceivedPolygonCoefficient
public import RequestProject.SurfaceDual

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
open ASC
variable {P Q : Type} [PartialOrder P] [PartialOrder Q]
  {f : P → Q} (hf : IsPosetCover f)

theorem cover_lt_of_image {a b : P} (hab : a ≤ b) (h : f a < f b) : a < b :=
  lt_of_le_of_ne hab fun he => h.ne (congrArg f he)

noncomputable def coveredSurfaceRank (S : SurfaceRank Q) : SurfaceRank P where
  rk a := S.rk (f a)
  rk_lt_of_lt h := S.rk_lt_of_lt (hf.strictMono h)
  rk_le_two a := S.rk_le_two (f a)
  two_vertices e he := by
    obtain ⟨a, b, hab, ha, hb, hall⟩ := S.two_vertices (f e) he
    obtain ⟨a', ⟨ha'e, hfa⟩, _⟩ := hf.down e a ha.le
    obtain ⟨b', ⟨hb'e, hfb⟩, _⟩ := hf.down e b hb.le
    refine ⟨a', b', fun h => hab (hfa.symm.trans ((congrArg f h).trans hfb)),
      cover_lt_of_image ha'e (hfa.symm ▸ ha), cover_lt_of_image hb'e (hfb.symm ▸ hb), fun z hz => ?_⟩
    exact (hall (f z) (hf.strictMono hz)).imp
      (fun hz' => hf.down_inj hz.le ha'e (hz'.trans hfa.symm))
      (fun hz' => hf.down_inj hz.le hb'e (hz'.trans hfb.symm))
  two_faces e he := by
    obtain ⟨a, b, hab, ha, hb, hall⟩ := S.two_faces (f e) he
    obtain ⟨a', ⟨hea', hfa⟩, _⟩ := hf.up e a ha.le
    obtain ⟨b', ⟨heb', hfb⟩, _⟩ := hf.up e b hb.le
    refine ⟨a', b', fun h => hab (hfa.symm.trans ((congrArg f h).trans hfb)),
      cover_lt_of_image hea' (hfa.symm ▸ ha), cover_lt_of_image heb' (hfb.symm ▸ hb), fun z hz => ?_⟩
    exact (hall (f z) (hf.strictMono hz)).imp
      (fun hz' => hf.up_inj hz.le hea' (hz'.trans hfa.symm))
      (fun hz' => hf.up_inj hz.le heb' (hz'.trans hfb.symm))
  two_edges v t hv ht hvt := by
    obtain ⟨a, b, hab, ha, hb, hall⟩ := S.two_edges (f v) (f t) hv ht (hf.strictMono hvt)
    obtain ⟨a', hva', ha't, hfa⟩ := hf.exists_interval_lift hvt.le a ha.1.le ha.2.le
    obtain ⟨b', hvb', hb't, hfb⟩ := hf.exists_interval_lift hvt.le b hb.1.le hb.2.le
    refine ⟨a', b', fun h => hab (hfa.symm.trans ((congrArg f h).trans hfb)),
      ⟨cover_lt_of_image hva' (hfa.symm ▸ ha.1), cover_lt_of_image ha't (hfa.symm ▸ ha.2)⟩,
      ⟨cover_lt_of_image hvb' (hfb.symm ▸ hb.1), cover_lt_of_image hb't (hfb.symm ▸ hb.2)⟩,
      fun z hz => ?_⟩
    exact (hall (f z) ⟨hf.strictMono hz.1, hf.strictMono hz.2⟩).imp
      (fun hz' => hf.up_inj hz.1.le hva' (hz'.trans hfa.symm))
      (fun hz' => hf.up_inj hz.1.le hvb' (hz'.trans hfb.symm))
  exists_face x := by
    obtain ⟨t, ht, hxt⟩ := S.exists_face (f x)
    obtain ⟨t', ⟨hxt', hft⟩, _⟩ := hf.up x t hxt
    exact ⟨t', hft.symm ▸ ht, hxt'⟩
  exists_vertex t ht := by
    obtain ⟨v, hv, hvt⟩ := S.exists_vertex (f t) ht
    obtain ⟨v', ⟨hv't, hfv⟩, _⟩ := hf.down t v hvt.le
    exact ⟨v', hfv.symm ▸ hv, cover_lt_of_image hv't (hfv.symm ▸ hvt)⟩

theorem coveredSurfaceRank_faceEdges (S : SurfaceRank Q) (hfe : FaceEdges S) :
    FaceEdges (coveredSurfaceRank hf S) := by
  intro v w t hv hw ht hvt hwt hvw
  obtain ⟨e, hve, hwe, het⟩ := hfe (f v) (f w) (f t) hv hw ht
    (hf.strictMono hvt) (hf.strictMono hwt) fun he => hvw (hf.down_inj hvt.le hwt.le he)
  obtain ⟨e', hve', he't, hfe'⟩ := hf.exists_interval_lift hvt.le e hve.le het.le
  exact ⟨e', cover_lt_of_image hve' (hfe'.symm ▸ hve),
    cover_lt_of_image (hf.le_of_le_below hwt.le he't (hfe'.symm ▸ hwe.le)) (hfe'.symm ▸ hwe),
    cover_lt_of_image he't (hfe'.symm ▸ het)⟩

theorem exactlyTwo_exhaust {X : Type} {R : X → Prop} (h : ExactlyTwo R)
    {a b : X} (ha : R a) (hb : R b) (hab : a ≠ b) :
    ∀ x, R x → x = a ∨ x = b := by
  obtain ⟨x, y, _, _, _, hall⟩ := h
  intro z hz
  rcases hall a ha, hall b hb, hall z hz with ⟨rfl | rfl, rfl | rfl, rfl | rfl⟩ <;> tauto

open scoped Classical

theorem bdry2_pair_zero {c : StrictOrdTri P →₀ ℤ} {E : StrictOrdEdge P} {A B : StrictOrdTri P}
    (hAB : A ≠ B) {s : ℤ} (hs : s = 1 ∨ s = -1)
    (h : ∀ r n, Comb.bdry2 (strictOrderCx P) (.single r n) E =
      if r = A ∨ r = B then s * n else 0)
    (hd : Comb.bdry2 (strictOrderCx P) c E = 0) (hz : c A = 0) : c B = 0 := by
  have hsum : Comb.bdry2 (strictOrderCx P) c E = s * (c A + c B) := by
    clear hd hz
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]; ring
    | single r n =>
      rw [h]
      by_cases hA : r = A <;> by_cases hB : r = B <;>
        simp [Finsupp.single_apply, hA, hB, hAB, Ne.symm hAB]
  rcases hs with rfl | rfl <;> omega

section
variable (S : SurfaceRank P) (c : StrictOrdTri P →₀ ℤ)
include S

theorem surface_zero_change_vertex {a b e t : P}
    (hae : a < e) (hbe : b < e) (het : e < t)
    (hd : Comb.bdry2 (strictOrderCx P) c ⟨(e, t), het⟩ = 0)
    (hz : c ⟨(a, e, t), hae, het⟩ = 0) :
    c ⟨(b, e, t), hbe, het⟩ = 0 := by
  by_cases hab : a = b
  · exact hab ▸ hz
  classical
  have hrk := S.rk_flag hae het
  have hall := exactlyTwo_exhaust (S.two_vertices e hrk.2.1) hae hbe hab
  refine bdry2_pair_zero (fun h => hab (congrArg (·.1.1) h)) (.inl rfl) (fun r n => ?_) hd hz
  have hr := S.rk_flag r.2.1 r.2.2
  have h01 : strictTriangleEdge01 r ≠ ⟨(e, t), het⟩ := fun h => by
    have := congrArg (fun d : StrictOrdEdge P => S.rk d.1.1) h; change S.rk r.1.1 = S.rk e at this; omega
  have h02 : strictTriangleEdge02 r ≠ ⟨(e, t), het⟩ := fun h => by
    have := congrArg (fun d : StrictOrdEdge P => S.rk d.1.1) h; change S.rk r.1.1 = S.rk e at this; omega
  have h12 : strictTriangleEdge12 r = ⟨(e, t), het⟩ ↔
      r = ⟨(a, e, t), hae, het⟩ ∨ r = ⟨(b, e, t), hbe, het⟩ :=
    ⟨fun h => by
      obtain ⟨he, ht⟩ : r.1.2.1 = e ∧ r.1.2.2 = t := Prod.mk.inj (congrArg Subtype.val h)
      exact (hall r.1.1 (he ▸ r.2.1)).imp
        (fun hv => Subtype.ext (Prod.ext hv (Prod.ext he ht)))
        (fun hv => Subtype.ext (Prod.ext hv (Prod.ext he ht))),
     by rintro (rfl | rfl) <;> rfl⟩
  erw [strictTriangle_bdry2_single, Finsupp.sub_apply, Finsupp.add_apply]
  simp [Finsupp.single_apply, h01, h02, h12]

theorem surface_zero_change_edge {v a b t : P}
    (hva : v < a) (hat : a < t) (hvb : v < b) (hbt : b < t)
    (hd : Comb.bdry2 (strictOrderCx P) c ⟨(v, t), hva.trans hat⟩ = 0)
    (hz : c ⟨(v, a, t), hva, hat⟩ = 0) :
    c ⟨(v, b, t), hvb, hbt⟩ = 0 := by
  by_cases hab : a = b
  · exact hab ▸ hz
  classical
  have hrk := S.rk_flag hva hat
  have hall := exactlyTwo_exhaust (S.two_edges v t hrk.1 hrk.2.2 (hva.trans hat))
    ⟨hva, hat⟩ ⟨hvb, hbt⟩ hab
  refine bdry2_pair_zero (fun h => hab (congrArg (·.1.2.1) h)) (.inr rfl) (fun r n => ?_) hd hz
  have hr := S.rk_flag r.2.1 r.2.2
  have h01 : strictTriangleEdge01 r ≠ ⟨(v, t), hva.trans hat⟩ := fun h => by
    have := congrArg (fun d : StrictOrdEdge P => S.rk d.1.2) h; change S.rk r.1.2.1 = S.rk t at this; omega
  have h12 : strictTriangleEdge12 r ≠ ⟨(v, t), hva.trans hat⟩ := fun h => by
    have := congrArg (fun d : StrictOrdEdge P => S.rk d.1.1) h; change S.rk r.1.2.1 = S.rk v at this; omega
  have h02 : strictTriangleEdge02 r = ⟨(v, t), hva.trans hat⟩ ↔
      r = ⟨(v, a, t), hva, hat⟩ ∨ r = ⟨(v, b, t), hvb, hbt⟩ :=
    ⟨fun h => by
      obtain ⟨hv, ht⟩ : r.1.1 = v ∧ r.1.2.2 = t := Prod.mk.inj (congrArg Subtype.val h)
      exact (hall r.1.2.1 ⟨hv ▸ r.2.1, ht ▸ r.2.2⟩).imp
        (fun he => Subtype.ext (Prod.ext hv (Prod.ext he ht)))
        (fun he => Subtype.ext (Prod.ext hv (Prod.ext he ht))),
     by rintro (rfl | rfl) <;> rfl⟩
  erw [strictTriangle_bdry2_single, Finsupp.sub_apply, Finsupp.add_apply]
  simp only [Finsupp.single_apply, h01, h12, h02, if_false, sub_zero, zero_add]
  split_ifs <;> ring

theorem surface_zero_change_face {v e a b : P}
    (hve : v < e) (hea : e < a) (heb : e < b)
    (hd : Comb.bdry2 (strictOrderCx P) c ⟨(v, e), hve⟩ = 0)
    (hz : c ⟨(v, e, a), hve, hea⟩ = 0) :
    c ⟨(v, e, b), hve, heb⟩ = 0 := by
  by_cases hab : a = b
  · exact hab ▸ hz
  classical
  have hrk := S.rk_flag hve hea
  have hall := exactlyTwo_exhaust (S.two_faces e hrk.2.1) hea heb hab
  refine bdry2_pair_zero (fun h => hab (congrArg (·.1.2.2) h)) (.inl rfl) (fun r n => ?_) hd hz
  have hr := S.rk_flag r.2.1 r.2.2
  have h12 : strictTriangleEdge12 r ≠ ⟨(v, e), hve⟩ := fun h => by
    have := congrArg (fun d : StrictOrdEdge P => S.rk d.1.1) h; change S.rk r.1.2.1 = S.rk v at this; omega
  have h02 : strictTriangleEdge02 r ≠ ⟨(v, e), hve⟩ := fun h => by
    have := congrArg (fun d : StrictOrdEdge P => S.rk d.1.2) h; change S.rk r.1.2.2 = S.rk e at this; omega
  have h01 : strictTriangleEdge01 r = ⟨(v, e), hve⟩ ↔
      r = ⟨(v, e, a), hve, hea⟩ ∨ r = ⟨(v, e, b), hve, heb⟩ :=
    ⟨fun h => by
      obtain ⟨hv, he⟩ : r.1.1 = v ∧ r.1.2.1 = e := Prod.mk.inj (congrArg Subtype.val h)
      exact (hall r.1.2.2 (he ▸ r.2.2)).imp
        (fun ht => Subtype.ext (Prod.ext hv (Prod.ext he ht)))
        (fun ht => Subtype.ext (Prod.ext hv (Prod.ext he ht))),
     by rintro (rfl | rfl) <;> rfl⟩
  erw [strictTriangle_bdry2_single, Finsupp.sub_apply, Finsupp.add_apply]
  simp [Finsupp.single_apply, h01, h12, h02]

theorem surface_zero_in_face (hfe : FaceEdges S)
    (hrel : ∀ e : StrictOrdEdge P, S.rk e.1.2 = 2 →
      Comb.bdry2 (strictOrderCx P) c e = 0)
    (a b : StrictOrdTri P) (htop : a.1.2.2 = b.1.2.2) (ha : c a = 0) : c b = 0 := by
  rcases a with ⟨⟨v, e, t⟩, hve, het⟩
  rcases b with ⟨⟨w, d, t'⟩, hwd, hdt⟩
  dsimp only at htop; subst t'
  have hrk := S.rk_flag hve het
  have hrk' := S.rk_flag hwd hdt
  by_cases hvw : v = w
  · subst w; exact surface_zero_change_edge S c hve het hwd hdt (hrel _ hrk.2.2) ha
  · obtain ⟨r, hvr, hwr, hrt⟩ := hfe v w t hrk.1 hrk'.1 hrk.2.2 (hve.trans het) (hwd.trans hdt) hvw
    exact surface_zero_change_edge S c hwr hrt hwd hdt (hrel _ hrk.2.2)
      (surface_zero_change_vertex S c hvr hwr hrt (hrel _ hrk.2.2)
        (surface_zero_change_edge S c hve het hvr hrt (hrel _ hrk.2.2) ha))

end
end FiniteChains.Comb

namespace FiniteChains.Davis
open Comb ASC Cell
variable {κ ι P : Type} {M : ℕ} [NeZero M] [PartialOrder P]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)
  (hd : PolygonData vc ec) (f : P → SCell vc ec hc) (hf : IsPosetCover f)

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

include hd hf in
theorem polygonRelative_zero_in_face
    (c : StrictOrdTri P →₀ ℤ) (hrel : PolygonRelativeChain hc f c)
    (a b : StrictOrdTri P) (ht : a.1.2.2 = b.1.2.2) (ha : c a = 0) : c b = 0 :=
  surface_zero_in_face (coveredSurfaceRank hf (surfaceRank_SCell hc hd)) c
    (coveredSurfaceRank_faceEdges hf (surfaceRank_SCell hc hd) (faceEdges_SCell hc hd))
    (fun e he => polygonRelative_boundary_zero_of_target hc f c hrel e fun hb => by
      change Cell.rk (f e.1.2) = 2 at he
      have := polygonBoundary_rank_le_one hc hb; omega) a b ht ha

include hd in
theorem polygonRelative_zero_inner
    (c : StrictOrdTri P →₀ ℤ) (hrel : PolygonRelativeChain hc f c)
    (hpoles : polygonCoverPoleCoefficients hc f hf c = 0)
    (p : Fin M) (t : StrictOrdTri P) (ht : f t.1.2.2 = cI hc p) : c t = 0 := by
  let S := coveredSurfaceRank hf (surfaceRank_SCell hc hd)
  have hM : 2 ≤ M := by have := hd.three_le; omega
  have hpole (a : StrictOrdTri P) (ha : f a.1.1 = cC hc) : c a = 0 :=
    polygonCoverPole_relative_ext hc f hf hM c 0
      (polygonCover_boundary_vanishes_at_poles hc f c fun e he => (hrel e he).1)
      (by simp) (by erw [map_zero]; exact hpoles) a ha
  obtain ⟨v, ⟨hvt, hfv⟩, _⟩ := hf.down t.1.2.2 (cC hc) (ht.symm ▸ (ctr_lt_inn hc p).le)
  have hvT : v < t.1.2.2 := lt_of_le_of_ne hvt fun he =>
    (ctr_lt_inn hc p).ne (hfv.symm.trans ((congrArg f he).trans ht))
  have hvrk : S.rk v = 0 := by change Cell.rk (f v) = 0; erw [hfv]; rfl
  obtain ⟨e, _, _, ⟨hve, heT⟩, _, _⟩ :=
    S.two_edges v t.1.2.2 hvrk (S.rk_flag t.2.1 t.2.2).2.2 hvT
  exact polygonRelative_zero_in_face hc hd f hf c hrel ⟨(v, e, t.1.2.2), hve, heT⟩ t rfl
    (hpole _ hfv)

include hd hf in
theorem polygonRelative_zero_across
    (c : StrictOrdTri P →₀ ℤ) (hrel : PolygonRelativeChain hc f c)
    (t : StrictOrdTri P) (e a : SCell vc ec hc)
    (herk : Cell.rk e = 1) (het : e < f t.1.2.2) (hea : e < a)
    (heboundary : ¬ InPolygonBoundary hc e)
    (ha : ∀ z : StrictOrdTri P, f z.1.2.2 = a → c z = 0) : c t = 0 := by
  let S := coveredSurfaceRank hf (surfaceRank_SCell hc hd)
  obtain ⟨d, ⟨hdT, hfd⟩, _⟩ := hf.down t.1.2.2 e het.le
  have hdT' : d < t.1.2.2 := cover_lt_of_image hdT (hfd.symm ▸ het)
  obtain ⟨a', ⟨hda, hfa⟩, _⟩ := hf.up d a (hfd.symm ▸ hea.le)
  have hda' : d < a' := cover_lt_of_image (f := f) hda (by erw [hfd, hfa]; exact hea)
  have hdrk : S.rk d = 1 := by change Cell.rk (f d) = 1; erw [hfd]; exact herk
  obtain ⟨v, _, _, hvd, _, _⟩ := S.two_vertices d hdrk
  exact polygonRelative_zero_in_face hc hd f hf c hrel ⟨(v, d, t.1.2.2), hvd, hdT'⟩ t rfl
    (surface_zero_change_face S c hvd hda' hdT'
      (polygonRelative_boundary_zero_of_target hc f c hrel _ (hfd.symm ▸ heboundary))
      (ha ⟨(v, d, a'), hvd, hda'⟩ hfa))

include hd in
theorem polygonRelative_zero_inner_collar
    (c : StrictOrdTri P →₀ ℤ) (hrel : PolygonRelativeChain hc f c)
    (hpoles : polygonCoverPoleCoefficients hc f hf c = 0)
    (p : Fin M) (t : StrictOrdTri P) (ht : f t.1.2.2 = cT2 hc p) : c t = 0 :=
  polygonRelative_zero_across hc hd f hf c hrel t (cF hc p) (cI hc p) rfl
    (ht.symm ▸ lt_of_le_of_ne (cF_le_cT2 hc p) nofun)
    (lt_of_le_of_ne (cF_le_cI hc p) nofun) id
    (polygonRelative_zero_inner hc hd f hf c hrel hpoles p)

include hd in
theorem polygonRelative_zero_outer_collar
    (c : StrictOrdTri P →₀ ℤ) (hrel : PolygonRelativeChain hc f c)
    (hpoles : polygonCoverPoleCoefficients hc f hf c = 0)
    (p : Fin M) (t : StrictOrdTri P) (ht : f t.1.2.2 = cT1 hc p) : c t = 0 :=
  polygonRelative_zero_across hc hd f hf c hrel t (cG hc p) (cT2 hc p) rfl
    (ht.symm ▸ lt_of_le_of_ne (cG_le_cT1 hc p) nofun)
    (lt_of_le_of_ne (cG_le_cT2 hc p) nofun) id
    (polygonRelative_zero_inner_collar hc hd f hf c hrel hpoles p)

include hd in
theorem polygonRelative_zero_of_pole_coefficients
    (c : StrictOrdTri P →₀ ℤ) (hrel : PolygonRelativeChain hc f c)
    (hpoles : polygonCoverPoleCoefficients hc f hf c = 0) : c = 0 := by
  ext t
  have ht : Cell.rk (f t.1.2.2) = 2 :=
    ((surfaceRank_SCell hc hd).rk_flag (hf.strictMono t.2.1) (hf.strictMono t.2.2)).2.2
  generalize he : f t.1.2.2 = a at ht
  cases a with
  | inn p => exact polygonRelative_zero_inner hc hd f hf c hrel hpoles p t he
  | tr2 p => exact polygonRelative_zero_inner_collar hc hd f hf c hrel hpoles p t he
  | tr1 p => exact polygonRelative_zero_outer_collar hc hd f hf c hrel hpoles p t he
  | _ => nomatch ht

theorem PolygonRelativeChain.zero : PolygonRelativeChain hc f (0 : StrictOrdTri P →₀ ℤ) := by
  intro e he; simp at he

theorem PolygonRelativeChain.add {c d : StrictOrdTri P →₀ ℤ}
    (hc' : PolygonRelativeChain hc f c) (hd' : PolygonRelativeChain hc f d) :
    PolygonRelativeChain hc f (c + d) := fun e he => by
  by_cases hce : Comb.bdry2 (strictOrderCx P) c e = 0
  · refine hd' e (Finsupp.mem_support_iff.mpr fun hd0 => Finsupp.mem_support_iff.mp he ?_)
    erw [map_add, Finsupp.add_apply, hce, hd0, add_zero]
  · exact hc' e (Finsupp.mem_support_iff.mpr hce)

theorem PolygonRelativeChain.sub {c d : StrictOrdTri P →₀ ℤ}
    (hc' : PolygonRelativeChain hc f c) (hd' : PolygonRelativeChain hc f d) :
    PolygonRelativeChain hc f (c - d) := fun e he => by
  by_cases hce : Comb.bdry2 (strictOrderCx P) c e = 0
  · refine hd' e (Finsupp.mem_support_iff.mpr fun hd0 => Finsupp.mem_support_iff.mp he ?_)
    erw [map_sub, Finsupp.sub_apply, hce, hd0, sub_self]
  · exact hc' e (Finsupp.mem_support_iff.mpr hce)

theorem PolygonRelativeChain.smul {c : StrictOrdTri P →₀ ℤ}
    (hc' : PolygonRelativeChain hc f c) (n : ℤ) : PolygonRelativeChain hc f (n • c) :=
  fun e he => hc' e (Finsupp.mem_support_iff.mpr fun h0 =>
    Finsupp.mem_support_iff.mp he (by erw [map_smul, Finsupp.smul_apply, h0, smul_zero]))

include hd in
theorem polygonRelative_ext
    (c d : StrictOrdTri P →₀ ℤ)
    (hc' : PolygonRelativeChain hc f c) (hd' : PolygonRelativeChain hc f d)
    (hpoles : polygonCoverPoleCoefficients hc f hf c =
      polygonCoverPoleCoefficients hc f hf d) : c = d :=
  sub_eq_zero.mp (polygonRelative_zero_of_pole_coefficients hc hd f hf (c - d)
    (PolygonRelativeChain.sub hc f hc' hd') (by erw [map_sub, hpoles, sub_self]))
