import Mathlib.Tactic

import RequestProject.SurfaceRegular

/-!
# The links of the vertices of the surface are connected

The local conditions verified in `RequestProject/SurfaceRegular.lean` make every vertex link of
the subdivision a disjoint union of cycles.  A polygon with identified sides is a closed surface
exactly when each of these links is a *single* cycle, i.e. when the corners of the polygon lying
over one vertex of the surface are glued to one another in a single cycle.

* `FiniteChains.Davis.CornerAdj` — two positions of the boundary are corners at the same vertex
  of the surface which share a side of the polygon;
* `FiniteChains.Davis.CornersConnected` — the corners over each vertex form a single cycle;
* `FiniteChains.Davis.linkConnected_SCell` — **under this hypothesis every vertex link of the
  subdivision is connected**;
* `FiniteChains.Davis.closedSurfacePoset_SCell` — hence the polygon with identified sides is a
  closed surface, in the combinatorial sense of `FiniteChains.ASC.ClosedSurfacePoset`.

The proof is the expected walk.  Around the centre one goes from one radius to the next through
the triangle of the fan between them; around a collar vertex one goes once around the ten cells
through it; around a vertex of the identified boundary one first walks, inside one corner of the
polygon, from the outgoing side to the incoming side through the two triangles and the two
diagonals of that corner, and then passes to the next corner through the side which glues them.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis


open Cell ASC Relation


section

variable {κ ι : Type u} {M : ℕ} [NeZero M] {vc : Fin M → κ} {ec : Fin M → ι}
  (hc : Compat vc ec)

/-! ### Elementary steps of a link -/

theorem linkAdj_symmetric (v : SCell vc ec hc) : Symmetric (LinkAdj v) := by
  rintro x y ⟨h1, h2, h3⟩
  exact ⟨h2, h1, h3.symm⟩

theorem linkAdj_of_lt {v x y : SCell vc ec hc} (hx : v < x) (hy : v < y) (h : x ≤ y) :
    LinkAdj v x y := ⟨hx, hy, Or.inl h⟩

/-! ### The link of the centre -/

theorem ctr_lt_iff {y : Cell κ ι M} :
    (toS vc ec hc ctr < toS vc ec hc y) ↔ (∃ p : Fin M, y = rad p ∨ y = inn p) := by
  rw [lt_iff_plt]
  cases y <;> simp [plt]

variable (r : Fin M)
theorem ctr_lt_rad  : toS vc ec hc ctr < toS vc ec hc (rad r) :=
  (lt_rad_iff hc).2 (Or.inl rfl)

theorem ctr_lt_inn  : toS vc ec hc ctr < toS vc ec hc (inn r) :=
  (lt_inn_iff hc).2 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

variable (q : Fin M)
abbrev conn_rad_step   :=
  have s1 :=
    FiniteChains.Davis.linkAdj_of_lt hc (FiniteChains.Davis.ctr_lt_rad hc q) (FiniteChains.Davis.ctr_lt_inn hc q)
      (le_of_lt ((FiniteChains.Davis.lt_inn_iff hc).mpr (Or.inr (Or.inl rfl))));
  have s2 :=
    ⟨FiniteChains.Davis.ctr_lt_inn hc q,
      ⟨FiniteChains.Davis.ctr_lt_rad hc (q + 1),
        Or.inr (le_of_lt ((FiniteChains.Davis.lt_inn_iff hc).mpr (Or.inr (Or.inr (Or.inl rfl)))))⟩⟩;
  Relation.ReflTransGen.tail (Relation.ReflTransGen.single s1) s2

theorem conn_rad (n : ℕ) : ∀ p : Fin M, p.val = n →
    ReflTransGen (LinkAdj (toS vc ec hc ctr)) (toS vc ec hc (rad 0)) (toS vc ec hc (rad p)) := by
  induction n with
  | zero =>
      aesop
  | succ n ih =>
      intro p hp
      
      have h1 : (fpred p).val = n := by
        rw [fpred_val, if_neg (by omega)]
        omega
      have h2 := ih (fpred p) h1
      have h3  := fpred_add_one p
      have h4 := conn_rad_step hc (fpred p)
      rw [h3] at h4
      exact h2.trans h4

theorem reflTransGen_symm {α : Type*} {r : α → α → Prop}
    (hr : Symmetric r) {a b : α} (h : ReflTransGen r a b) : ReflTransGen r b a := by
  letI : Std.Symm r := ⟨fun _ _ h => hr h⟩
  exact Relation.ReflTransGen.stdSymm.symm _ _ h

variable (x y : SCell vc ec hc)
/-- **The link of the centre of the polygon is connected**: it is the cycle of the collar. -/
theorem link_connected_ctr  (hx : toS vc ec hc ctr < x)
    (hy : toS vc ec hc ctr < y) : ReflTransGen (LinkAdj (toS vc ec hc ctr)) x y := by
  have key : ∀ z : Cell κ ι M, toS vc ec hc ctr < toS vc ec hc z →
      ReflTransGen (LinkAdj (toS vc ec hc ctr)) (toS vc ec hc (rad 0)) (toS vc ec hc z) := by
    intro z hz
    obtain ⟨p, hp | hp⟩ := (ctr_lt_iff hc).1 hz
    · subst hp; exact conn_rad hc p.val p rfl
    · subst hp
      refine (conn_rad hc p.val p rfl).tail ?_
      exact linkAdj_of_lt hc (ctr_lt_rad hc p) (ctr_lt_inn hc p)
        (le_of_lt ((lt_inn_iff hc).2 (Or.inr (Or.inl rfl))))
  exact (reflTransGen_symm (linkAdj_symmetric hc _) (key x hx)).trans (key y hy)

/-! ### The link of a collar vertex -/

theorem cvx_lt_iff {p : Fin M} {y : Cell κ ι M} :
    (toS vc ec hc (cvx p) < toS vc ec hc y) ↔
      (y = ced p ∨ y = ced (fpred p) ∨ y = dia p ∨ y = gdi (fpred p) ∨ y = rad p ∨
        y = tr1 (fpred p) ∨ y = tr2 p ∨ y = tr2 (fpred p) ∨ y = inn p ∨ y = inn (fpred p)) := by
  rw [lt_iff_plt]
  have key : ∀ r : Fin M, (p = r + 1) ↔ (r = fpred p) := by
    aesop (add simp [fpred_succ, fpred_add_one])
  cases y <;> simp [plt, key, eq_comm]

/-- **The link of a collar vertex is connected**: it is the cycle of the ten cells through it. -/
theorem link_connected_cvx  
    (hx : toS vc ec hc (cvx (q + 1)) < x) (hy : toS vc ec hc (cvx (q + 1)) < y) :
    ReflTransGen (LinkAdj (toS vc ec hc (cvx (q + 1)))) x y := by
  let v := toS vc ec hc (cvx (q + 1))
  let l := ([ced (q + 1), tr2 (q + 1), dia (q + 1), tr1 q, gdi q,
    tr2 q, ced q, inn q, rad (q + 1), inn (q + 1)] : List (Cell κ ι M)).map (toS vc ec hc)
  have hl : l.IsChain (LinkAdj v) := by
    simp [l, v, List.isChain_cons_cons, LinkAdj, le_iff_lt_or_eq, lt_iff_plt, plt]
  have hm (z : Cell κ ι M) (hz : v < toS vc ec hc z) : toS vc ec hc z ∈ l := by
    have h := (cvx_lt_iff hc).1 hz
    simp_all [l, fpred_succ, toS, SCell]
    tauto
  have hr := hl.induction (ReflTransGen (LinkAdj v) (toS vc ec hc (ced (q + 1)))) l
    (fun _ _ h r => r.tail h) (fun _ => ReflTransGen.refl)
  exact (reflTransGen_symm (linkAdj_symmetric hc v) (hr x (hm x hx))).trans (hr y (hm y hy))

/-! ### The cells at a corner of the polygon -/

variable {w : κ}
  {i : Fin M}
theorem vtx_lt_bed_out   (hi : vc i = w) :
    toS vc ec hc (vtx w) < toS vc ec hc (bed (ec i)) :=
  (lt_bed_iff hc).2 (Or.inl (by rw [hi]))

theorem vtx_lt_bed_in   (hi : vc i = w) :
    toS vc ec hc (vtx w) < toS vc ec hc (bed (ec (fpred i))) := by
  classical simp_all [FiniteChains.Davis.lt_bed_iff, Or.inr, FiniteChains.Davis.fpred_add_one]

theorem vtx_lt_tr1_out   (hi : vc i = w) :
    toS vc ec hc (vtx w) < toS vc ec hc (tr1 i) :=
  (lt_tr1_iff hc).2 (Or.inr (Or.inr (Or.inr (Or.inl (by rw [hi])))))

theorem vtx_lt_tr1_in   (hi : vc i = w) :
    toS vc ec hc (vtx w) < toS vc ec hc (tr1 (fpred i)) := by
  classical simp_all [FiniteChains.Davis.lt_tr1_iff, Or.inr, Or.inl, FiniteChains.Davis.fpred_add_one]

theorem vtx_lt_gdi   (hi : vc i = w) :
    toS vc ec hc (vtx w) < toS vc ec hc (gdi i) :=
  (lt_gdi_iff hc).2 (Or.inl (by rw [hi]))

theorem vtx_lt_dia   (hi : vc i = w) :
    toS vc ec hc (vtx w) < toS vc ec hc (dia i) :=
  (lt_dia_iff hc).2 (Or.inl (by rw [hi]))

theorem vtx_lt_tr2   (hi : vc i = w) :
    toS vc ec hc (vtx w) < toS vc ec hc (tr2 i) :=
  (lt_tr2_iff hc).2 (Or.inr (Or.inr (Or.inr (Or.inl (by rw [hi])))))

/-! ### Going around one corner of the polygon -/

abbrev conn_tr1_bed   (hi : vc i = w)  :=
  ReflTransGen.single ((linkAdj_symmetric hc _)
    (linkAdj_of_lt hc (vtx_lt_bed_out hc hi) (vtx_lt_tr1_out hc hi)
      (le_of_lt ((lt_tr1_iff hc).2 (Or.inl rfl)))))

abbrev conn_gdi_bed   (hi : vc i = w)  :=
  Relation.ReflTransGen.trans
    (Relation.ReflTransGen.single
      (FiniteChains.Davis.linkAdj_of_lt hc (FiniteChains.Davis.vtx_lt_gdi hc hi) (FiniteChains.Davis.vtx_lt_tr1_out hc hi)
        (le_of_lt ((FiniteChains.Davis.lt_tr1_iff hc).mpr (Or.inr (Or.inr (Or.inl rfl)))))))
    (FiniteChains.Davis.conn_tr1_bed hc hi)

abbrev conn_tr2_bed   (hi : vc i = w)  :=
  (ReflTransGen.single ((linkAdj_symmetric hc _) (linkAdj_of_lt hc (vtx_lt_gdi hc hi)
    (vtx_lt_tr2 hc hi)
    (le_of_lt ((lt_tr2_iff hc).2 (Or.inr (Or.inr (Or.inl rfl)))))))).trans (conn_gdi_bed hc hi)

abbrev conn_dia_bed   (hi : vc i = w)  :=
  Relation.ReflTransGen.trans
    (Relation.ReflTransGen.single
      (FiniteChains.Davis.linkAdj_of_lt hc (FiniteChains.Davis.vtx_lt_dia hc hi) (FiniteChains.Davis.vtx_lt_tr2 hc hi)
        (le_of_lt ((FiniteChains.Davis.lt_tr2_iff hc).mpr (Or.inr (Or.inl rfl))))))
    (FiniteChains.Davis.conn_tr2_bed hc hi)

theorem conn_tr1in_bed   (hi : vc i = w) :
    ReflTransGen (LinkAdj (toS vc ec hc (vtx w))) (toS vc ec hc (tr1 (fpred i)))
      (toS vc ec hc (bed (ec i))) := by
  refine (ReflTransGen.single ((linkAdj_symmetric hc _) (linkAdj_of_lt hc (vtx_lt_dia hc hi)
    (vtx_lt_tr1_in hc hi) ?_))).trans (conn_dia_bed hc hi)
  refine le_of_lt ((lt_tr1_iff hc).2 (Or.inr (Or.inl ?_)))
  rw [fpred_add_one]

/-- **The two sides of the polygon at one corner are joined inside the link.** -/
abbrev conn_bedin_bed   (hi : vc i = w)  :=
  Relation.ReflTransGen.trans
    (Relation.ReflTransGen.single
      (FiniteChains.Davis.linkAdj_of_lt hc (FiniteChains.Davis.vtx_lt_bed_in hc hi)
        (FiniteChains.Davis.vtx_lt_tr1_in hc hi) (le_of_lt ((FiniteChains.Davis.lt_tr1_iff hc).mpr (Or.inl rfl)))))
    (FiniteChains.Davis.conn_tr1in_bed hc hi)

/-- Every cell through a vertex of the identified boundary is joined, inside the link, to the
side of the polygon at one of the corners over that vertex. -/
theorem conn_to_bed  (z : Cell κ ι M) (hz : toS vc ec hc (vtx w) < toS vc ec hc z) :
    ∃ i : Fin M, vc i = w ∧ ReflTransGen (LinkAdj (toS vc ec hc (vtx w))) (toS vc ec hc z)
      (toS vc ec hc (bed (ec i))) := by
  rw [lt_iff_plt] at hz
  cases z with
  | bed e =>
      obtain ⟨j, hj, hv⟩ := hz
      subst hj
      rcases hv with hv | hv
      · exact ⟨j, hv, ReflTransGen.refl⟩
      · refine ⟨j + 1, hv, ?_⟩
        have hb := conn_bedin_bed hc hv
        rwa [fpred_succ] at hb
  | dia p => exact ⟨p, hz, conn_dia_bed hc hz⟩
  | gdi p => exact ⟨p, hz, conn_gdi_bed hc hz⟩
  | tr2 p => exact ⟨p, hz, conn_tr2_bed hc hz⟩
  | tr1 p =>
      rcases hz with hv | hv
      · exact ⟨p, hv, conn_tr1_bed hc hv⟩
      · refine ⟨p + 1, hv, ?_⟩
        have hb := conn_tr1in_bed hc hv
        rwa [fpred_succ] at hb
  | _ => simp [plt] at hz

/-! ### Passing from one corner to the next -/

/-- **Two corners of the polygon at the same vertex sharing a side**: the positions `i` and `j`
carry the same vertex, and one of the two sides through `i` is identified with one of the two
sides through `j`. -/
def CornerAdj (vc : Fin M → κ) (ec : Fin M → ι) (i j : Fin M)  :=
  vc i = vc j ∧ (ec i = ec j ∨ ec i = ec (fpred j) ∨ ec (fpred i) = ec j ∨
    ec (fpred i) = ec (fpred j))

variable {i j : Fin M}
theorem cornerAdj_symm  (h : CornerAdj vc ec i j) : CornerAdj vc ec j i := by
  aesop (add simp [FiniteChains.Davis.CornerAdj])

theorem vc_eq_of_reflTransGen  (h : ReflTransGen (CornerAdj vc ec) i j) :
    vc i = vc j := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans hstep.1

/-- **The corners of the polygon over one vertex of the surface form a single cycle.** -/
def CornersConnected (vc : Fin M → κ) (ec : Fin M → ι)  :=
  ∀ i j : Fin M, vc i = vc j → ReflTransGen (CornerAdj vc ec) i j

theorem conn_corner_step   (hi : vc i = w) (hj : vc j = w)
    (h : CornerAdj vc ec i j) :
    ReflTransGen (LinkAdj (toS vc ec hc (vtx w))) (toS vc ec hc (bed (ec i)))
      (toS vc ec hc (bed (ec j))) := by
  obtain ⟨-, hh⟩ := h
  rcases hh with h | h | h | h
  · rw [h]
  · rw [h]
    exact conn_bedin_bed hc hj
  · have hb := conn_bedin_bed hc hi
    rw [h] at hb
    exact reflTransGen_symm (linkAdj_symmetric hc _) hb
  · have hb := conn_bedin_bed hc hi
    rw [h] at hb
    exact (reflTransGen_symm (linkAdj_symmetric hc _) hb).trans (conn_bedin_bed hc hj)

theorem conn_corner   (hi : vc i = w)
    (h : ReflTransGen (CornerAdj vc ec) i j) :
    ReflTransGen (LinkAdj (toS vc ec hc (vtx w))) (toS vc ec hc (bed (ec i)))
      (toS vc ec hc (bed (ec j))) := by
  induction h with
  | refl => exact ReflTransGen.refl
  | @tail b c hib hbc ih =>
      have hb  := (vc_eq_of_reflTransGen hib).symm.trans hi
      have hcv  := hbc.1.symm.trans hb
      exact (ih).trans (conn_corner_step hc hb hcv hbc)

/-- **The link of a vertex of the identified boundary is connected.** -/
theorem link_connected_vtx (hcorners : CornersConnected vc ec) (w : κ) (x y : SCell vc ec hc)
    (hx : toS vc ec hc (vtx w) < x) (hy : toS vc ec hc (vtx w) < y) :
    ReflTransGen (LinkAdj (toS vc ec hc (vtx w))) x y := by
  obtain ⟨i, hi, hxi⟩ := conn_to_bed hc x hx
  obtain ⟨j, hj, hyj⟩ := conn_to_bed hc y hy
  have hij  := hcorners i j (by rw [hi, hj])
  exact (hxi.trans (conn_corner hc hi hij)).trans
    (reflTransGen_symm (linkAdj_symmetric hc _) hyj)

/-! ### The closed surface -/

variable (hd : PolygonData vc ec)
/-- **Every vertex link of the subdivision of the surface is connected.** -/
theorem linkConnected_SCell  (hcorners : CornersConnected vc ec) :
    LinkConnected (surfaceRank_SCell hc hd) := by
  intro v hv x y hx hy
  cases v with
  | vtx w => exact link_connected_vtx hc hcorners w x y hx hy
  | cvx p =>
      have hp  := fpred_add_one p
      rw [← hp] at hx hy ⊢
      exact link_connected_cvx hc (fpred p) x y hx hy
  | ctr => exact link_connected_ctr hc x y hx hy
  | _ => simp [surfaceRank_SCell, Cell.rk] at hv

/-- **The polygon with identified sides is a closed surface**: the local incidence conditions
hold and all vertex links are connected. -/
def closedSurfacePoset_SCell  (hcorners : CornersConnected vc ec) :
    ClosedSurfacePoset (SCell vc ec hc) where
  toSurfaceRank := surfaceRank_SCell hc hd
  link_connected := linkConnected_SCell hc hd hcorners

end

end FiniteChains.Davis

