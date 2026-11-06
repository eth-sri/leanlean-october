module

public import RequestProject.SurfaceRegular

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis

open Cell ASC Relation

universe u

variable {κ ι : Type u} {M : ℕ} [NeZero M] {vc : Fin M → κ} {ec : Fin M → ι}
variable (hc : Compat vc ec)

theorem linkAdj_symmetric (v : SCell vc ec hc) : Symmetric (LinkAdj v) :=
  fun _ _ ⟨h1, h2, h3⟩ => ⟨h2, h1, h3.symm⟩

theorem reflTransGen_symm {α : Type*} {r : α → α → Prop}
    (hr : Symmetric r) {a b : α} (h : ReflTransGen r a b) : ReflTransGen r b a := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact (ReflTransGen.single (hr hstep)).trans ih

theorem ctr_lt_iff {y : Cell κ ι M} :
    (toS vc ec hc ctr < toS vc ec hc y) ↔ (∃ p : Fin M, y = rad p ∨ y = inn p) := by
  rw [lt_iff_plt]; cases y <;> simp [plt]

theorem ctr_lt_rad (r : Fin M) : toS vc ec hc ctr < toS vc ec hc (rad r) :=
  (lt_rad_iff hc).2 (Or.inl rfl)

theorem ctr_lt_inn (r : Fin M) : toS vc ec hc ctr < toS vc ec hc (inn r) :=
  (lt_inn_iff hc).2 (by simp)

theorem link_connected_ctr (x y : SCell vc ec hc) (hx : toS vc ec hc ctr < x)
    (hy : toS vc ec hc ctr < y) : ReflTransGen (LinkAdj (toS vc ec hc ctr)) x y := by
  have conn_rad (n : ℕ) : ∀ p : Fin M, p.val = n →
      ReflTransGen (LinkAdj (toS vc ec hc ctr)) (toS vc ec hc (rad 0)) (toS vc ec hc (rad p)) := by
    induction n with
    | zero => intro p hp; rw [show p = 0 from Fin.ext (by simpa using hp)]
    | succ n ih =>
        intro p hp
        have := Nat.pos_of_neZero M
        have hstep : ReflTransGen (LinkAdj (toS vc ec hc ctr))
            (toS vc ec hc (rad (fpred p))) (toS vc ec hc (rad (fpred p + 1))) :=
          (ReflTransGen.single ⟨ctr_lt_rad hc (fpred p), ctr_lt_inn hc (fpred p),
            .inl (le_of_lt ((lt_inn_iff hc).2 (by simp)))⟩).tail
            ⟨ctr_lt_inn hc (fpred p), ctr_lt_rad hc _, .inr (le_of_lt ((lt_inn_iff hc).2 (by simp)))⟩
        rw [fpred_add_one] at hstep
        exact (ih (fpred p) (by rw [fpred_val, if_neg (by omega)]; omega)).trans hstep
  have key (z : Cell κ ι M) (hz : toS vc ec hc ctr < toS vc ec hc z) :
      ReflTransGen (LinkAdj (toS vc ec hc ctr)) (toS vc ec hc (rad 0)) (toS vc ec hc z) := by
    obtain ⟨p, rfl | rfl⟩ := (ctr_lt_iff hc).1 hz
    · exact conn_rad p.val p rfl
    · exact (conn_rad p.val p rfl).tail ⟨ctr_lt_rad hc p, ctr_lt_inn hc p,
        .inl (le_of_lt ((lt_inn_iff hc).2 (by simp)))⟩
  exact (reflTransGen_symm (linkAdj_symmetric hc _) (key x hx)).trans (key y hy)

attribute [local simp] lt_bed_iff lt_ced_iff lt_dia_iff lt_gdi_iff lt_rad_iff
  lt_tr1_iff lt_tr2_iff lt_inn_iff fpred_add_one fpred_succ

theorem link_connected_cvx (q : Fin M) (x y : SCell vc ec hc)
    (hx : toS vc ec hc (cvx (q + 1)) < x) (hy : toS vc ec hc (cvx (q + 1)) < y) :
    ReflTransGen (LinkAdj (toS vc ec hc (cvx (q + 1)))) x y := by
  set v : SCell vc ec hc := toS vc ec hc (cvx (q + 1))
  have step (a b : Cell κ ι M)
      (ha : v < toS vc ec hc a := by simp [v])
      (hb : v < toS vc ec hc b := by simp [v])
      (h : toS vc ec hc a ≤ toS vc ec hc b ∨ toS vc ec hc b ≤ toS vc ec hc a := by
        first | (refine .inl (le_of_lt ?_); simp; done) | (refine .inr (le_of_lt ?_); simp; done)) :
      LinkAdj v (toS vc ec hc a) (toS vc ec hc b) := ⟨ha, hb, h⟩
  have e_tr2a := ReflTransGen.single (step (tr2 (q + 1)) (ced (q + 1)))
  have e_dia := (ReflTransGen.single (step (dia (q + 1)) (tr2 (q + 1)))).trans e_tr2a
  have e_inna := ReflTransGen.single (step (inn (q + 1)) (ced (q + 1)))
  have e_rad := (ReflTransGen.single (step (rad (q + 1)) (inn (q + 1)))).trans e_inna
  have e_innb := (ReflTransGen.single (step (inn q) (rad (q + 1)))).trans e_rad
  have e_ced0 := (ReflTransGen.single (step (ced q) (inn q))).trans e_innb
  have e_tr2b := (ReflTransGen.single (step (tr2 q) (ced q))).trans e_ced0
  have e_gdi := (ReflTransGen.single (step (gdi q) (tr2 q))).trans e_tr2b
  have e_tr1 := (ReflTransGen.single (step (tr1 q) (gdi q))).trans e_gdi
  have key (z : Cell κ ι M) (hz : v < toS vc ec hc z) :
      ReflTransGen (LinkAdj v) (toS vc ec hc z) (toS vc ec hc (ced (q + 1))) := by
    have hcases : z = ced (q + 1) ∨ z = ced q ∨ z = dia (q + 1) ∨ z = gdi q ∨ z = rad (q + 1) ∨
        z = tr1 q ∨ z = tr2 (q + 1) ∨ z = tr2 q ∨ z = inn (q + 1) ∨ z = inn q := by
      rw [lt_iff_plt] at hz
      have hk (r : Fin M) : (q + 1 = r + 1) ↔ (r = q) :=
        ⟨fun h => by simpa using (congrArg fpred h).symm, fun h => by rw [h]⟩
      cases z <;> simpa [plt, hk, eq_comm] using hz
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [.refl, e_ced0, e_dia, e_gdi, e_rad, e_tr1, e_tr2a, e_tr2b, e_inna, e_innb]
  exact (key x hx).trans (reflTransGen_symm (linkAdj_symmetric hc v) (key y hy))

theorem conn_bedin_bed {w : κ} {i : Fin M} (hi : vc i = w) :
    ReflTransGen (LinkAdj (toS vc ec hc (vtx w))) (toS vc ec hc (bed (ec (fpred i))))
      (toS vc ec hc (bed (ec i))) := by
  subst hi
  set v : SCell vc ec hc := toS vc ec hc (vtx (vc i))
  have step (a b : Cell κ ι M)
      (ha : v < toS vc ec hc a := by simp [v])
      (hb : v < toS vc ec hc b := by simp [v])
      (h : toS vc ec hc a ≤ toS vc ec hc b ∨ toS vc ec hc b ≤ toS vc ec hc a := by
        first | (refine .inl (le_of_lt ?_); simp; done) | (refine .inr (le_of_lt ?_); simp; done)) :
      LinkAdj v (toS vc ec hc a) (toS vc ec hc b) := ⟨ha, hb, h⟩
  exact (((((ReflTransGen.single (step (bed (ec (fpred i))) (tr1 (fpred i)))).tail
    (step (tr1 (fpred i)) (dia i))).tail
    (step (dia i) (tr2 i))).tail
    (step (tr2 i) (gdi i))).tail
    (step (gdi i) (tr1 i))).tail
    (step (tr1 i) (bed (ec i)))

theorem conn_to_bed {w : κ} (z : Cell κ ι M) (hz : toS vc ec hc (vtx w) < toS vc ec hc z) :
    ∃ i : Fin M, vc i = w ∧ ReflTransGen (LinkAdj (toS vc ec hc (vtx w))) (toS vc ec hc z)
      (toS vc ec hc (bed (ec i))) := by
  have step (i : Fin M) (a b : Cell κ ι M)
      (ha : toS vc ec hc (vtx (vc i)) < toS vc ec hc a := by simp)
      (hb : toS vc ec hc (vtx (vc i)) < toS vc ec hc b := by simp)
      (h : toS vc ec hc a ≤ toS vc ec hc b ∨ toS vc ec hc b ≤ toS vc ec hc a := by
        first | (refine .inl (le_of_lt ?_); simp; done) | (refine .inr (le_of_lt ?_); simp; done)) :
      LinkAdj (toS vc ec hc (vtx (vc i))) (toS vc ec hc a) (toS vc ec hc b) := ⟨ha, hb, h⟩
  have c_tr1 (p : Fin M) := ReflTransGen.single (step p (tr1 p) (bed (ec p)))
  have c_gdi (p : Fin M) := (ReflTransGen.single (step p (gdi p) (tr1 p))).trans (c_tr1 p)
  have c_tr2 (p : Fin M) := (ReflTransGen.single (step p (tr2 p) (gdi p))).trans (c_gdi p)
  have c_dia (p : Fin M) := (ReflTransGen.single (step p (dia p) (tr2 p))).trans (c_tr2 p)
  rw [lt_iff_plt] at hz
  cases z with
  | bed e =>
      obtain ⟨j, rfl, rfl | rfl⟩ := hz
      · exact ⟨j, rfl, .refl⟩
      · exact ⟨j + 1, rfl, by simpa using conn_bedin_bed hc (i := j + 1) rfl⟩
  | dia p => subst hz; exact ⟨p, rfl, c_dia p⟩
  | gdi p => subst hz; exact ⟨p, rfl, c_gdi p⟩
  | tr2 p => subst hz; exact ⟨p, rfl, c_tr2 p⟩
  | tr1 p =>
      rcases hz with rfl | rfl
      · exact ⟨p, rfl, c_tr1 p⟩
      · refine ⟨p + 1, rfl, (ReflTransGen.single ?_).trans (c_dia (p + 1))⟩
        simpa using step (p + 1) (tr1 (fpred (p + 1))) (dia (p + 1))
  | _ => simp [plt] at hz

def CornerAdj (vc : Fin M → κ) (ec : Fin M → ι) (i j : Fin M) : Prop :=
  vc i = vc j ∧ (ec i = ec j ∨ ec i = ec (fpred j) ∨ ec (fpred i) = ec j ∨
    ec (fpred i) = ec (fpred j))

theorem cornerAdj_symm {i j : Fin M} (h : CornerAdj vc ec i j) : CornerAdj vc ec j i := by
  obtain ⟨hv, h | h | h | h⟩ := h <;> exact ⟨hv.symm, by tauto⟩

def CornersConnected (vc : Fin M → κ) (ec : Fin M → ι) : Prop :=
  ∀ i j : Fin M, vc i = vc j → ReflTransGen (CornerAdj vc ec) i j

def closedSurfacePoset_SCell (hd : PolygonData vc ec) (hcorners : CornersConnected vc ec) :
    ClosedSurfacePoset (SCell vc ec hc) where
  toSurfaceRank := surfaceRank_SCell hc hd
  link_connected v hv x y hx hy := by
    cases v with
    | vtx w =>
        obtain ⟨i, hi, hxi⟩ := conn_to_bed hc x hx
        obtain ⟨j, hj, hyj⟩ := conn_to_bed hc y hy
        have hcorn : ∀ {b c : Fin M}, vc b = w → ReflTransGen (CornerAdj vc ec) b c →
            vc c = w ∧ ReflTransGen (LinkAdj (toS vc ec hc (vtx w)))
              (toS vc ec hc (bed (ec b))) (toS vc ec hc (bed (ec c))) := by
          intro b c hb h
          induction h with
          | refl => exact ⟨hb, .refl⟩
          | @tail d e _ hde ih =>
              have hve := hde.1.symm.trans ih.1
              refine ⟨hve, ih.2.trans ?_⟩
              rcases hde.2 with h | h | h | h
              · rw [h]
              · rw [h]; exact conn_bedin_bed hc hve
              · have hb' := conn_bedin_bed hc ih.1; rw [h] at hb'
                exact reflTransGen_symm (linkAdj_symmetric hc _) hb'
              · have hb' := conn_bedin_bed hc ih.1; rw [h] at hb'
                exact (reflTransGen_symm (linkAdj_symmetric hc _) hb').trans (conn_bedin_bed hc hve)
        exact (hxi.trans (hcorn hi (hcorners i j (hi.trans hj.symm))).2).trans
          (reflTransGen_symm (linkAdj_symmetric hc _) hyj)
    | cvx p =>
        rw [← fpred_add_one p] at hx hy ⊢
        exact link_connected_cvx hc (fpred p) x y hx hy
    | ctr => exact link_connected_ctr hc x y hx hy
    | _ => simp [surfaceRank_SCell, Cell.rk] at hv
