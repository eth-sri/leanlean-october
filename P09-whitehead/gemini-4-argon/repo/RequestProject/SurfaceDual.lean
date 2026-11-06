module

public import RequestProject.SurfaceRegular
public import RequestProject.OrderComplexDual
public import RequestProject.SpineCollapse

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis

open Cell ASC Relation

variable {κ ι : Type} {M : ℕ} [NeZero M]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)

theorem faceEdges_SCell (hd : PolygonData vc ec) : FaceEdges (surfaceRank_SCell hc hd) := by
  intro v v' f hv hv' hf hvf hv'f hne
  have L {a b c : SCell vc ec hc} (h1 : a < c) (h2 : b < c) (h3 : c < f) :
      ∃ e, (a < e ∧ b < e ∧ e < f) ∧ (b < e ∧ a < e ∧ e < f) :=
    ⟨c, ⟨h1, h2, h3⟩, ⟨h2, h1, h3⟩⟩
  cases f with
  | tr1 p =>
      obtain ⟨e1, h1, h2⟩ := L ((lt_bed_iff hc).2 (.inl rfl)) ((lt_bed_iff hc).2 (.inr rfl))
        ((bed_lt_iff hc).2 ⟨p, rfl, rfl⟩)
      obtain ⟨e2, h3, h4⟩ := L ((lt_gdi_iff hc).2 (.inl rfl)) ((lt_gdi_iff hc).2 (.inr rfl))
        ((gdi_lt_iff hc).2 (.inl rfl))
      obtain ⟨e3, h5, h6⟩ := L ((lt_dia_iff hc).2 (.inl rfl)) ((lt_dia_iff hc).2 (.inr rfl))
        ((dia_lt_iff hc).2 (.inr (by rw [fpred_succ])))
      have hv1 : v = vtx (vc p) ∨ v = vtx (vc (p + 1)) ∨ v = cvx (p + 1) := by
        rcases (lt_tr1_iff hc).1 hvf with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [surfaceRank_SCell, Cell.rk]
      have hv1' : v' = vtx (vc p) ∨ v' = vtx (vc (p + 1)) ∨ v' = cvx (p + 1) := by
        rcases (lt_tr1_iff hc).1 hv'f with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [surfaceRank_SCell, Cell.rk]
      rcases hv1 with rfl | rfl | rfl <;> rcases hv1' with rfl | rfl | rfl <;>
        first | contradiction | exact ⟨_, h1⟩ | exact ⟨_, h2⟩ | exact ⟨_, h3⟩ | exact ⟨_, h4⟩ | exact ⟨_, h5⟩ | exact ⟨_, h6⟩
  | tr2 p =>
      obtain ⟨e1, h1, h2⟩ := L ((lt_dia_iff hc).2 (.inl rfl)) ((lt_dia_iff hc).2 (.inr rfl))
        ((dia_lt_iff hc).2 (.inl rfl))
      obtain ⟨e2, h3, h4⟩ := L ((lt_gdi_iff hc).2 (.inl rfl)) ((lt_gdi_iff hc).2 (.inr rfl))
        ((gdi_lt_iff hc).2 (.inr rfl))
      obtain ⟨e3, h5, h6⟩ := L ((lt_ced_iff hc).2 (.inl rfl)) ((lt_ced_iff hc).2 (.inr rfl))
        ((ced_lt_iff hc).2 (.inl rfl))
      have hv2 : v = vtx (vc p) ∨ v = cvx p ∨ v = cvx (p + 1) := by
        rcases (lt_tr2_iff hc).1 hvf with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [surfaceRank_SCell, Cell.rk]
      have hv2' : v' = vtx (vc p) ∨ v' = cvx p ∨ v' = cvx (p + 1) := by
        rcases (lt_tr2_iff hc).1 hv'f with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [surfaceRank_SCell, Cell.rk]
      rcases hv2 with rfl | rfl | rfl <;> rcases hv2' with rfl | rfl | rfl <;>
        first | contradiction | exact ⟨_, h1⟩ | exact ⟨_, h2⟩ | exact ⟨_, h3⟩ | exact ⟨_, h4⟩ | exact ⟨_, h5⟩ | exact ⟨_, h6⟩
  | inn p =>
      obtain ⟨e1, h1, h2⟩ := L ((lt_rad_iff hc).2 (.inl rfl)) ((lt_rad_iff hc).2 (.inr rfl))
        ((rad_lt_iff hc).2 (.inl rfl))
      obtain ⟨e2, h3, h4⟩ := L ((lt_rad_iff hc).2 (.inl rfl)) ((lt_rad_iff hc).2 (.inr rfl))
        ((rad_lt_iff hc).2 (.inr (by rw [fpred_succ])))
      obtain ⟨e3, h5, h6⟩ := L ((lt_ced_iff hc).2 (.inl rfl)) ((lt_ced_iff hc).2 (.inr rfl))
        ((ced_lt_iff hc).2 (.inr rfl))
      have hvi : v = ctr ∨ v = cvx p ∨ v = cvx (p + 1) := by
        rcases (lt_inn_iff hc).1 hvf with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [surfaceRank_SCell, Cell.rk]
      have hvi' : v' = ctr ∨ v' = cvx p ∨ v' = cvx (p + 1) := by
        rcases (lt_inn_iff hc).1 hv'f with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [surfaceRank_SCell, Cell.rk]
      rcases hvi with rfl | rfl | rfl <;> rcases hvi' with rfl | rfl | rfl <;>
        first | contradiction | exact ⟨_, h1⟩ | exact ⟨_, h2⟩ | exact ⟨_, h3⟩ | exact ⟨_, h4⟩ | exact ⟨_, h5⟩ | exact ⟨_, h6⟩
  | _ => simp [surfaceRank_SCell, Cell.rk] at hf

variable [DecidableEq κ] [DecidableEq ι] [Fintype κ] [Fintype ι]

theorem exists_spine_collapse_SCell (hd : PolygonData vc ec) :
    ∃ l : List (Cube (SCell vc ec hc)),
      Collapse.IsCollapse (spineInc (orderComplex (SCell vc ec hc))) l
        (topCubes (orderComplex (SCell vc ec hc))) := by
  have hs {f f' : SCell vc ec hc} (h : FaceAdj (surfaceRank_SCell hc hd) f f') :
      FaceAdj (surfaceRank_SCell hc hd) f' f := let ⟨e, he, h1, h2⟩ := h; ⟨e, he, h2, h1⟩
  have hkey (k : ℕ) : ∀ r : Fin M, r.val = k →
      ReflTransGen (FaceAdj (surfaceRank_SCell hc hd)) (inn 0) (inn r) := by
    induction k with
    | zero => intro r hr; rw [show r = 0 from Fin.ext (by simpa using hr)]
    | succ n ih =>
        intro r hr
        have hstep : FaceAdj (surfaceRank_SCell hc hd) (inn (fpred r)) (inn (fpred r + 1)) :=
          ⟨rad (fpred r + 1), rfl, (rad_lt_iff hc).2 (.inr (by rw [fpred_succ])),
            (rad_lt_iff hc).2 (.inl rfl)⟩
        rw [fpred_add_one] at hstep
        exact (ih (fpred r) (by rw [fpred_val, if_neg (by omega)]; omega)).tail hstep
  have hconn (f : SCell vc ec hc) (hf : Cell.rk f = 2) :
      ReflTransGen (FaceAdj (surfaceRank_SCell hc hd)) (inn 0) f := by
    cases f with
    | tr1 p =>
        exact ((hkey p.val p rfl).tail
          (hs ⟨ced p, rfl, (ced_lt_iff hc).2 (.inl rfl), (ced_lt_iff hc).2 (.inr rfl)⟩)).tail
          (hs ⟨gdi p, rfl, (gdi_lt_iff hc).2 (.inl rfl), (gdi_lt_iff hc).2 (.inr rfl)⟩)
    | tr2 p =>
        exact (hkey p.val p rfl).tail
          (hs ⟨ced p, rfl, (ced_lt_iff hc).2 (.inl rfl), (ced_lt_iff hc).2 (.inr rfl)⟩)
    | inn p => exact hkey p.val p rfl
    | _ => simp [Cell.rk] at hf
  letI : Std.Symm (FaceAdj (surfaceRank_SCell hc hd)) := ⟨fun _ _ => hs⟩
  refine exists_spine_collapse_of_surface (edgeInTwoTriangles_SCell hc hd)
    ((surfaceRank_SCell hc hd).dual_connected (faceEdges_SCell hc hd) fun f f' hf hf' =>
      (ReflTransGen.stdSymm.symm _ _ (hconn f hf)).trans (hconn f' hf'))
    (fun v => let ⟨s, hs, hcard, hv⟩ := (surfaceRank_SCell hc hd).vertexInTriangle v; ⟨s, ⟨hs, hcard⟩, hv⟩)
    (isTri_of_flag ((lt_rad_iff (p := 0) hc).2 (.inl rfl)) ((rad_lt_iff (p := 0) hc).2 (.inl rfl)))
