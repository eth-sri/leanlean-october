import RequestProject.OrderComplexSurface
import RequestProject.SurfaceLabel


/-!
# The polygon with identified sides is a closed surface: the local conditions

`RequestProject/SurfacePoset.lean` builds the face poset `SCell vc ec hc` of a polygon with `M`
boundary positions whose sides are identified by the labellings `vc` and `ec`.  The nerve of the
block is the comparability graph of this poset, so the simplicial complex of the construction is
its order complex.

This file verifies, for that poset, the local conditions of a two-dimensional closed cell
structure (`FiniteChains.ASC.SurfaceRank`), under the hypotheses which say that the boundary
identification is the identification of the sides of a polygon:

* `FiniteChains.Davis.EdgePairs` — every edge of the surface comes from exactly two positions of
  the boundary of the polygon (the sides are glued in pairs);
* `FiniteChains.Davis.NoLoopSide` — no side of the polygon is a loop, i.e. the two endpoints of
  a side stay distinct after the identification;
* surjectivity of `vc` and `ec` — every vertex and every edge of the surface really occurs.

The result is `FiniteChains.Davis.surfaceRank_SCell`, and with it
`FiniteChains.Davis.edgeInTwoTriangles_SCell`: **every edge of the subdivision lies in exactly
two triangles**.  Connectedness of the vertex links — the condition which distinguishes a closed
surface from a pinched one — is treated in `RequestProject/SurfaceLink.lean`.
-/

namespace FiniteChains.Davis

open Cell ASC

universe u

/-! ### Arithmetic of the boundary cycle -/

section FinAux

variable {M : ℕ} [NeZero M]

theorem succ_mod_eq n m (h : n < m) : (n + 1) % m = if n + 1 = m then 0 else n + 1 := by
  split
  · simp_all
  · next he => exact Nat.mod_eq_of_lt (by omega)

/-- The predecessor of a position of the boundary cycle. -/
def fpred (p : Fin M) : Fin M := ⟨(p.val + (M - 1)) % M, Nat.mod_lt _ M.pos_of_neZero⟩

theorem fpred_val (p : Fin M) : (fpred p).val = if p.val = 0 then M - 1 else p.val - 1 := by
  show (p.val + (M - 1)) % M = _
  split
  · simp_all
  · next he =>
      have hrw : p.val + (M - 1) = M + (p.val - 1) := by omega
      rw [hrw, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

theorem fpred_add_one (p : Fin M) : fpred p + 1 = p := by
  apply Fin.ext
  rw [fin_succ_val, fpred_val]
  split
  · next he => rw [succ_mod_eq _ _ (by omega), if_pos (by omega)]; omega
  · next he => rw [succ_mod_eq _ _ (by omega), if_neg (by omega)]; omega

theorem fin_add_one_injective (a b : Fin M) (hab : a + 1 = b + 1) : a = b := by
  simp_all

theorem fpred_succ (p : Fin M) : fpred (p + 1) = p :=
  fin_add_one_injective _ _ (fpred_add_one _)

theorem fin_succ_ne_self (hM : 2 ≤ M) (p : Fin M) : p + 1 ≠ p := by
  aesop

end FinAux

section Regular

variable {κ ι : Type u} {M : ℕ} [NeZero M] {vc : Fin M → κ} {ec : Fin M → ι}

/-- **The sides of the polygon are glued in pairs**: every edge of the surface comes from
exactly two positions of the boundary. -/
def EdgePairs (ec : Fin M → ι) :=
  ∀ i, ∃ j : Fin M, j ≠ i ∧ ec j = ec i ∧ ∀ k, ec k = ec i → k = i ∨ k = j

/-- **No side of the polygon becomes a loop**: the two endpoints of a side stay distinct after
the identification. -/
def NoLoopSide (vc : Fin M → κ) := ∀ i, vc i ≠ vc (i + 1)

/-- The identification data of a polygon whose sides are glued in pairs. -/
structure PolygonData (vc : Fin M → κ) (ec : Fin M → ι) : Prop where
  /-- The polygon has at least three positions. -/
  three_le : 3 ≤ M
  /-- The sides are glued in pairs. -/
  pairs : EdgePairs ec
  /-- No side becomes a loop. -/
  noLoop : NoLoopSide vc
  /-- Every vertex of the surface occurs on the boundary. -/
  vc_surj : Function.Surjective vc
  /-- Every edge of the surface occurs on the boundary. -/
  ec_surj : Function.Surjective ec

variable (hc : Compat vc ec)

/-- In the face poset, `x < y` means that `x` is a proper face of `y`. -/
theorem lt_iff_plt :
    (toS vc ec hc x < toS vc ec hc y) ↔ plt vc ec x y := by
  constructor
  · rintro ⟨hle, hnle⟩
    rcases hle with h | h
    · tauto
    · exact h
  · intro h
    refine lt_of_le_of_ne (Or.inr h) ?_
    intro he
    have hxy : x = y := he
    exact plt_irrefl (vc := vc) (ec := ec) x (hxy ▸ h)

/-! ### The faces of a cell -/

/-- The vertices of a boundary edge. -/
theorem lt_bed_iff {x} :
    (toS vc ec hc x < toS vc ec hc (bed (ec i))) ↔ (x = vtx (vc i) ∨ x = vtx (vc (i + 1))) := by
  rw [lt_iff_plt]
  cases x with
  | vtx v =>
      simp [Cell.vtx.injEq]
      constructor
      · rintro ⟨j, hj, hv⟩
        rcases hc j i hj with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hv with hv | hv <;> simp_all
      · rintro (rfl | rfl)
        · exact ⟨i, rfl, Or.inl rfl⟩
        · exact ⟨i, rfl, Or.inr rfl⟩
  | _ => tauto

/-- The vertices of a collar edge. -/
theorem lt_ced_iff {x} :
    (toS vc ec hc x < toS vc ec hc (ced p)) ↔ (x = cvx p ∨ x = cvx (p + 1)) := by
  rw [lt_iff_plt]
  cases x <;> simp [plt]

/-- The vertices of the edge `dia p`. -/
theorem lt_dia_iff {x} :
    (toS vc ec hc x < toS vc ec hc (dia p)) ↔ (x = vtx (vc p) ∨ x = cvx p) := by
  rw [lt_iff_plt]
  cases x <;> simp [plt, eq_comm]

/-- The vertices of the edge `gdi p`. -/
theorem lt_gdi_iff {x} :
    (toS vc ec hc x < toS vc ec hc (gdi p)) ↔ (x = vtx (vc p) ∨ x = cvx (p + 1)) := by
  rw [lt_iff_plt]
  cases x <;> simp [plt, eq_comm]

/-- The vertices of a radius. -/
theorem lt_rad_iff {x} :
    (toS vc ec hc x < toS vc ec hc (rad p)) ↔ (x = ctr ∨ x = cvx p) := by
  rw [lt_iff_plt]
  cases x <;> simp [plt]

/-- The faces through a boundary edge: the outer triangles at the positions carrying it. -/
theorem bed_lt_iff :
    (toS vc ec hc (bed (ec i)) < toS vc ec hc y) ↔ ∃ p, ec p = ec i ∧ y = tr1 p := by
  rw [lt_iff_plt]
  cases y with
  | tr1 p =>
      constructor
      · intro h
        exact ⟨p, h.symm, rfl⟩
      · rintro ⟨p', hp', hy⟩
        have : p = p' := by injection hy
        exact (this ▸ hp').symm
  | _ => tauto

/-- The faces through a collar edge. -/
theorem ced_lt_iff :
    (toS vc ec hc (ced p) < toS vc ec hc y) ↔ (y = tr2 p ∨ y = inn p) := by
  rw [lt_iff_plt]
  cases y <;> simp [plt, eq_comm]

/-- The faces through the edge `dia p`. -/
theorem dia_lt_iff :
    (toS vc ec hc (dia p) < toS vc ec hc y) ↔ (y = tr2 p ∨ y = tr1 (fpred p)) := by
  rw [lt_iff_plt]
  cases y with
  | tr1 s =>
      simp [plt, Cell.tr1.injEq, reduceCtorEq, false_or]
      constructor
      · intro h; rw [h, fpred_succ]
      · intro h; rw [h, fpred_add_one]
  | tr2 s => simp [plt, eq_comm]
  | _ => tauto

/-- The faces through the edge `gdi p`. -/
theorem gdi_lt_iff :
    (toS vc ec hc (gdi p) < toS vc ec hc y) ↔ (y = tr1 p ∨ y = tr2 p) := by
  rw [lt_iff_plt]
  cases y <;> simp [plt, eq_comm]

/-- The faces through a radius. -/
theorem rad_lt_iff :
    (toS vc ec hc (rad p) < toS vc ec hc y) ↔ (y = inn p ∨ y = inn (fpred p)) := by
  rw [lt_iff_plt]
  cases y with
  | inn s =>
      simp [plt, Cell.inn.injEq]
      constructor
      · rintro (h | h)
        · exact Or.inl h.symm
        · exact Or.inr (by rw [h, fpred_succ])
      · rintro (h | h)
        · exact Or.inl h.symm
        · exact Or.inr (by rw [h, fpred_add_one])
  | _ => tauto

/-- The proper faces of an outer triangle. -/
theorem lt_tr1_iff {x} :
    (toS vc ec hc x < toS vc ec hc (tr1 p)) ↔
      (x = bed (ec p) ∨ x = dia (p + 1) ∨ x = gdi p ∨
        x = vtx (vc p) ∨ x = vtx (vc (p + 1)) ∨ x = cvx (p + 1)) := by
  rw [lt_iff_plt]
  cases x <;> simp [plt, eq_comm]

/-- The proper faces of an inner triangle of the collar. -/
theorem lt_tr2_iff {x} :
    (toS vc ec hc x < toS vc ec hc (tr2 p)) ↔
      (x = ced p ∨ x = dia p ∨ x = gdi p ∨
        x = vtx (vc p) ∨ x = cvx p ∨ x = cvx (p + 1)) := by
  rw [lt_iff_plt]
  cases x <;> simp [plt, eq_comm]

/-- The proper faces of a triangle of the fan. -/
theorem lt_inn_iff {x} :
    (toS vc ec hc x < toS vc ec hc (inn p)) ↔
      (x = ced p ∨ x = rad p ∨ x = rad (p + 1) ∨
        x = ctr ∨ x = cvx p ∨ x = cvx (p + 1)) := by
  rw [lt_iff_plt]
  cases x <;> simp [plt, eq_comm]

/-! ### The local closed surface conditions -/

/-! ### The incidence counts -/

theorem toS_inj (h : toS vc ec hc x = toS vc ec hc y) : x = y := h

theorem fpred_ne_self (hM : 2 ≤ M) (p : Fin M) : fpred p ≠ p := by
  intro h
  have hp := fpred_add_one p
  simp_all

theorem not_lt_rk_zero (hv : Cell.rk v = 0) (hz : Cell.rk z = 0)
    (h : toS vc ec hc v < toS vc ec hc z) : False := by
  have := rk_lt_of_plt ((lt_iff_plt hc).1 h)
  omega

/-- **Every edge of the surface has exactly two endpoints.** -/
theorem two_vertices_SCell (hd : PolygonData vc ec) :
    ∀ e : SCell vc ec hc, Cell.rk e = 1 → ExactlyTwo (· < e) := by
  have hM2 : 2 ≤ M := by have := hd.three_le; omega
  intro e he
  cases e with
  | bed e' =>
      obtain ⟨i, rfl⟩ := hd.ec_surj e'
      refine ⟨vtx (vc i), vtx (vc (i + 1)), ?_, (lt_bed_iff hc).2 (Or.inl rfl),
        (lt_bed_iff hc).2 (Or.inr rfl), fun z hz => (lt_bed_iff hc).1 hz⟩
      intro h
      exact hd.noLoop i (by grind)
  | ced p =>
      refine ⟨cvx p, cvx (p + 1), ?_, (lt_ced_iff hc).2 (Or.inl rfl),
        (lt_ced_iff hc).2 (Or.inr rfl), fun z hz => (lt_ced_iff hc).1 hz⟩
      intro h
      have h' := toS_inj hc h
      simp_all
  | dia p =>
      refine ⟨vtx (vc p), cvx p, ?_, (lt_dia_iff hc).2 (Or.inl rfl),
        (lt_dia_iff hc).2 (Or.inr rfl), fun z hz => (lt_dia_iff hc).1 hz⟩
      tauto
  | gdi p =>
      refine ⟨vtx (vc p), cvx (p + 1), ?_, (lt_gdi_iff hc).2 (Or.inl rfl),
        (lt_gdi_iff hc).2 (Or.inr rfl), fun z hz => (lt_gdi_iff hc).1 hz⟩
      tauto
  | rad p =>
      refine ⟨ctr, cvx p, ?_, (lt_rad_iff hc).2 (Or.inl rfl),
        (lt_rad_iff hc).2 (Or.inr rfl), fun z hz => (lt_rad_iff hc).1 hz⟩
      tauto
  | _ => grind [Cell.rk]

/-- **Every edge of the surface lies in exactly two triangles.** -/
theorem two_faces_SCell (hd : PolygonData vc ec) :
    ∀ e : SCell vc ec hc, Cell.rk e = 1 → ExactlyTwo (e < ·) := by
  have hM2 : 2 ≤ M := by have := hd.three_le; omega
  intro e he
  cases e with
  | bed e' =>
      obtain ⟨i, rfl⟩ := hd.ec_surj e'
      obtain ⟨j, hji, hecj, huniq⟩ := hd.pairs i
      refine ⟨tr1 i, tr1 j, ?_, (bed_lt_iff hc).2 (by simp),
        (bed_lt_iff hc).2 (by simp_all), ?_⟩
      · grind
      · intro z hz
        obtain ⟨p, hp, rfl⟩ := (bed_lt_iff hc).1 hz
        grind
  | ced p =>
      refine ⟨tr2 p, inn p, ?_, (ced_lt_iff hc).2 (Or.inl rfl),
        (ced_lt_iff hc).2 (Or.inr rfl), fun z hz => (ced_lt_iff hc).1 hz⟩
      tauto
  | dia p =>
      refine ⟨tr2 p, tr1 (fpred p), ?_, (dia_lt_iff hc).2 (Or.inl rfl),
        (dia_lt_iff hc).2 (Or.inr rfl), fun z hz => (dia_lt_iff hc).1 hz⟩
      tauto
  | gdi p =>
      refine ⟨tr1 p, tr2 p, ?_, (gdi_lt_iff hc).2 (Or.inl rfl),
        (gdi_lt_iff hc).2 (Or.inr rfl), fun z hz => (gdi_lt_iff hc).1 hz⟩
      tauto
  | rad p =>
      refine ⟨inn p, inn (fpred p), ?_, (rad_lt_iff hc).2 (Or.inl rfl),
        (rad_lt_iff hc).2 (Or.inr rfl), fun z hz => (rad_lt_iff hc).1 hz⟩
      intro h
      have h' := toS_inj hc h
      injection h' with h''
      exact fpred_ne_self hM2 p h''.symm
  | _ => grind [Cell.rk]

/-- **Every vertex of a triangle lies in exactly two of its edges.** -/
theorem two_edges_SCell (hd : PolygonData vc ec) :
    ∀ v f : SCell vc ec hc, Cell.rk v = 0 → Cell.rk f = 2 → v < f →
      ExactlyTwo (fun e => v < e ∧ e < f) := by
  have hM2 : 2 ≤ M := by have := hd.three_le; omega
  intro v f hv hf hvf
  cases f with
  | tr1 p =>
      rcases (lt_tr1_iff hc).1 hvf with h | h | h | h | h | h <;> subst h
      · tauto
      · tauto
      · tauto
      · -- `v` is the initial vertex of the boundary edge
        refine ⟨bed (ec p), gdi p, by tauto,
          ⟨(lt_bed_iff hc).2 (Or.inl rfl), (lt_tr1_iff hc).2 (Or.inl rfl)⟩,
          ⟨(lt_gdi_iff hc).2 (Or.inl rfl), (lt_tr1_iff hc).2 (by simp)⟩, ?_⟩
        rintro z ⟨hz1, hz2⟩
        rcases (lt_tr1_iff hc).1 hz2 with h | h | h | h | h | h <;> subst h
        · exact Or.inl rfl
        · rcases (lt_dia_iff hc).1 hz1 with h' | h'
          · exact absurd (hd.noLoop p) (by simp_all)
          simp_all
        · exact Or.inr rfl
        · grind
        · exact absurd (not_lt_rk_zero hc hv rfl hz1) not_false
        · exact absurd (not_lt_rk_zero hc hv rfl hz1) not_false
      · -- `v` is the terminal vertex of the boundary edge
        refine ⟨bed (ec p), dia (p + 1), by tauto,
          ⟨(lt_bed_iff hc).2 (Or.inr rfl), (lt_tr1_iff hc).2 (Or.inl rfl)⟩,
          ⟨(lt_dia_iff hc).2 (Or.inl rfl), (lt_tr1_iff hc).2 (Or.inr (Or.inl rfl))⟩, ?_⟩
        rintro z ⟨hz1, hz2⟩
        rcases (lt_tr1_iff hc).1 hz2 with h | h | h | h | h | h <;> subst h
        · exact Or.inl rfl
        · exact Or.inr rfl
        · rcases (lt_gdi_iff hc).1 hz1 with h' | h'
          · exact absurd (hd.noLoop p) (by simp_all)
          simp_all
        · exact absurd (not_lt_rk_zero hc hv rfl hz1) not_false
        · grind
        · exact absurd (not_lt_rk_zero hc hv rfl hz1) not_false
      · -- `v` is the collar vertex
        refine ⟨dia (p + 1), gdi p, by tauto,
          ⟨(lt_dia_iff hc).2 (Or.inr rfl), (lt_tr1_iff hc).2 (Or.inr (Or.inl rfl))⟩,
          ⟨(lt_gdi_iff hc).2 (Or.inr rfl), (lt_tr1_iff hc).2 (by simp)⟩, ?_⟩
        rintro z ⟨hz1, hz2⟩
        rcases (lt_tr1_iff hc).1 hz2 with h | h | h | h | h | h <;> subst h
        · rcases (lt_bed_iff hc).1 hz1 with h' | h' <;> exact by simp_all
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd (not_lt_rk_zero hc hv rfl hz1) not_false
        · exact absurd (not_lt_rk_zero hc hv rfl hz1) not_false
        grind
  | tr2 p =>
      rcases (lt_tr2_iff hc).1 hvf with h | h | h | h | h | h <;> subst h
      · tauto
      · tauto
      · tauto
      · -- `v` is the boundary vertex
        refine ⟨dia p, gdi p, by tauto,
          ⟨(lt_dia_iff hc).2 (Or.inl rfl), (lt_tr2_iff hc).2 (Or.inr (Or.inl rfl))⟩,
          ⟨(lt_gdi_iff hc).2 (Or.inl rfl), (lt_tr2_iff hc).2 (by simp)⟩, ?_⟩
        rintro z ⟨hz1, hz2⟩
        rcases (lt_tr2_iff hc).1 hz2 with h | h | h | h | h | h <;> subst h
        · rcases (lt_ced_iff hc).1 hz1 with h' | h' <;> exact by simp_all
        · exact Or.inl rfl
        · exact Or.inr rfl
        · grind
        · exact absurd (not_lt_rk_zero hc hv rfl hz1) not_false
        · exact absurd (not_lt_rk_zero hc hv rfl hz1) not_false
      · -- `v` is the collar vertex at `p`
        refine ⟨ced p, dia p, by tauto,
          ⟨(lt_ced_iff hc).2 (Or.inl rfl), (lt_tr2_iff hc).2 (Or.inl rfl)⟩,
          ⟨(lt_dia_iff hc).2 (Or.inr rfl), (lt_tr2_iff hc).2 (Or.inr (Or.inl rfl))⟩, ?_⟩
        rintro z ⟨hz1, hz2⟩
        rcases (lt_tr2_iff hc).1 hz2 with h | h | h | h | h | h <;> subst h
        · exact Or.inl rfl
        · exact Or.inr rfl
        · rcases (lt_gdi_iff hc).1 hz1 with h' | h'
          · simp_all
          simp_all
        · exact absurd (not_lt_rk_zero hc hv rfl hz1) not_false
        · grind
        · exact absurd (not_lt_rk_zero hc hv rfl hz1) not_false
      · -- `v` is the collar vertex at `p+1`
        refine ⟨ced p, gdi p, by tauto,
          ⟨(lt_ced_iff hc).2 (Or.inr rfl), (lt_tr2_iff hc).2 (Or.inl rfl)⟩,
          ⟨(lt_gdi_iff hc).2 (Or.inr rfl), (lt_tr2_iff hc).2 (by simp)⟩, ?_⟩
        rintro z ⟨hz1, hz2⟩
        rcases (lt_tr2_iff hc).1 hz2 with h | h | h | h | h | h <;> subst h
        · exact Or.inl rfl
        · rcases (lt_dia_iff hc).1 hz1 with h' | h'
          · simp_all
          simp_all
        · exact Or.inr rfl
        · exact absurd (not_lt_rk_zero hc hv rfl hz1) not_false
        · exact absurd (not_lt_rk_zero hc hv rfl hz1) not_false
        grind
  | inn p =>
      rcases (lt_inn_iff hc).1 hvf with h | h | h | h | h | h <;> subst h
      · tauto
      · tauto
      · tauto
      · -- `v` is the centre
        refine ⟨rad p, rad (p + 1), ?_,
          ⟨(lt_rad_iff hc).2 (Or.inl rfl), (lt_inn_iff hc).2 (Or.inr (Or.inl rfl))⟩,
          ⟨(lt_rad_iff hc).2 (Or.inl rfl), (lt_inn_iff hc).2 (by simp)⟩, ?_⟩
        · intro h
          have h' := toS_inj hc h
          simp_all
        rintro z ⟨hz1, hz2⟩
        rcases (lt_inn_iff hc).1 hz2 with h | h | h | h | h | h <;> subst h
        · rcases (lt_ced_iff hc).1 hz1 with h' | h' <;> exact by simp_all
        · exact Or.inl rfl
        · exact Or.inr rfl
        · grind
        · exact absurd (not_lt_rk_zero hc hv rfl hz1) not_false
        · exact absurd (not_lt_rk_zero hc hv rfl hz1) not_false
      · -- `v` is the collar vertex at `p`
        refine ⟨ced p, rad p, by tauto,
          ⟨(lt_ced_iff hc).2 (Or.inl rfl), (lt_inn_iff hc).2 (Or.inl rfl)⟩,
          ⟨(lt_rad_iff hc).2 (Or.inr rfl), (lt_inn_iff hc).2 (Or.inr (Or.inl rfl))⟩, ?_⟩
        rintro z ⟨hz1, hz2⟩
        rcases (lt_inn_iff hc).1 hz2 with h | h | h | h | h | h <;> subst h
        · exact Or.inl rfl
        · exact Or.inr rfl
        · rcases (lt_rad_iff hc).1 hz1 with h' | h'
          · simp_all
          simp_all
        · exact absurd (not_lt_rk_zero hc hv rfl hz1) not_false
        · grind
        · exact absurd (not_lt_rk_zero hc hv rfl hz1) not_false
      · -- `v` is the collar vertex at `p+1`
        refine ⟨ced p, rad (p + 1), by tauto,
          ⟨(lt_ced_iff hc).2 (Or.inr rfl), (lt_inn_iff hc).2 (Or.inl rfl)⟩,
          ⟨(lt_rad_iff hc).2 (Or.inr rfl), (lt_inn_iff hc).2 (by simp)⟩, ?_⟩
        rintro z ⟨hz1, hz2⟩
        rcases (lt_inn_iff hc).1 hz2 with h | h | h | h | h | h <;> subst h
        · exact Or.inl rfl
        · rcases (lt_rad_iff hc).1 hz1 with h' | h'
          · simp_all
          simp_all
        · exact Or.inr rfl
        · exact absurd (not_lt_rk_zero hc hv rfl hz1) not_false
        · exact absurd (not_lt_rk_zero hc hv rfl hz1) not_false
        grind
  | _ => grind [Cell.rk]

/-- Every cell of the surface is a face of a triangle. -/
theorem exists_face_SCell (hd : PolygonData vc ec) :
    ∀ x, ∃ f : SCell vc ec hc, Cell.rk f = 2 ∧ x ≤ f := by
  intro x
  cases x with
  | vtx v =>
      obtain ⟨i, rfl⟩ := hd.vc_surj v
      exact ⟨tr1 i, rfl, by tauto⟩
  | bed e =>
      obtain ⟨i, rfl⟩ := hd.ec_surj e
      exact ⟨tr1 i, rfl, by tauto⟩
  | cvx p =>
      exact ⟨tr2 p, rfl,
        by tauto⟩
  | ced p => exact ⟨tr2 p, rfl, by tauto⟩
  | dia p => exact ⟨tr2 p, rfl, by tauto⟩
  | gdi p => exact ⟨tr2 p, rfl, by tauto⟩
  | tr1 p => aesop
  | tr2 p => aesop
  | ctr =>
      exact ⟨inn 0, rfl, by tauto⟩
  | rad p => exact ⟨inn p, rfl, by tauto⟩
  | inn p => aesop

/-- Every triangle of the surface has a vertex. -/
theorem exists_vertex_SCell :
    ∀ f : SCell vc ec hc, Cell.rk f = 2 → ∃ v : SCell vc ec hc, Cell.rk v = 0 ∧ v < f := by
  intro f hf
  cases f with
  | tr1 p =>
      exact ⟨vtx (vc p), rfl, (lt_tr1_iff hc).2 (by simp)⟩
  | tr2 p =>
      exact ⟨vtx (vc p), rfl, (lt_tr2_iff hc).2 (by simp)⟩
  | inn p => exact ⟨ctr, rfl, (lt_inn_iff hc).2 (by simp)⟩
  | _ => grind [Cell.rk]

/-- **The face poset of a polygon with identified sides satisfies the local conditions of a
two-dimensional closed cell structure**: every edge has exactly two endpoints, every edge lies
in exactly two triangles, and every vertex of a triangle lies in exactly two of its edges. -/
def surfaceRank_SCell (hd : PolygonData vc ec) : SurfaceRank (SCell vc ec hc) where
  rk := Cell.rk
  rk_lt_of_lt := by
    intro x y h
    exact rk_lt_of_plt ((lt_iff_plt hc).1 h)
  rk_le_two := rk_le_two
  two_vertices := two_vertices_SCell hc hd
  two_faces := two_faces_SCell hc hd
  two_edges := two_edges_SCell hc hd
  exists_face := exists_face_SCell hc hd
  exists_vertex := exists_vertex_SCell hc

/-- **Every edge of the subdivision of the surface lies in exactly two triangles.** -/
theorem edgeInTwoTriangles_SCell [DecidableEq κ] [DecidableEq ι] (hd : PolygonData vc ec) :
    EdgeInTwoTriangles (orderComplex (SCell vc ec hc)) :=
  (surfaceRank_SCell hc hd).edgeInTwoTriangles
