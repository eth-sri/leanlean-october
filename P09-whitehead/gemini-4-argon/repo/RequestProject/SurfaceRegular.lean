module

public import RequestProject.OrderComplexSurface
public import RequestProject.SurfaceLabel

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis

open Cell ASC

universe u

section

variable {M : ℕ} [NeZero M]

theorem succ_mod_eq (n m : ℕ) (h : n < m) : (n + 1) % m = if n + 1 = m then 0 else n + 1 := by
  split
  · next he => rw [he, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

def fpred (p : Fin M) : Fin M := ⟨(p.val + (M - 1)) % M, Nat.mod_lt _ (Nat.pos_of_neZero M)⟩

theorem fpred_val (p : Fin M) : (fpred p).val = if p.val = 0 then M - 1 else p.val - 1 := by
  have hM := Nat.pos_of_neZero M; have h := p.isLt
  show (p.val + (M - 1)) % M = _
  split
  · next he => rw [he, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
  · rw [show p.val + (M - 1) = M + (p.val - 1) by omega, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

theorem fpred_add_one (p : Fin M) : fpred p + 1 = p := by
  have hM := Nat.pos_of_neZero M; have h := p.isLt
  apply Fin.ext
  rw [fin_succ_val, fpred_val]
  split <;> rw [succ_mod_eq _ _ (by omega)] <;> split <;> omega

theorem fpred_succ (p : Fin M) : fpred (p + 1) = p := by
  have := congrArg Fin.val (fpred_add_one (p + 1))
  rw [fin_succ_val, fin_succ_val, succ_mod_eq _ _ (fpred (p + 1)).isLt, succ_mod_eq _ _ p.isLt] at this
  have ha := (fpred (p + 1)).isLt; have hb := p.isLt
  apply Fin.ext; split at this <;> split at this <;> omega

theorem fin_succ_ne_self (hM : 2 ≤ M) (p : Fin M) : p + 1 ≠ p := by
  intro h
  have := congrArg Fin.val h
  rw [fin_succ_val, succ_mod_eq _ _ p.isLt] at this
  have hp := p.isLt
  split at this <;> omega

end

variable {κ ι : Type u} {M : ℕ} [NeZero M] {vc : Fin M → κ} {ec : Fin M → ι}

def EdgePairs (ec : Fin M → ι) : Prop :=
  ∀ i : Fin M, ∃ j : Fin M, j ≠ i ∧ ec j = ec i ∧ ∀ k : Fin M, ec k = ec i → k = i ∨ k = j

def NoLoopSide (vc : Fin M → κ) : Prop := ∀ i : Fin M, vc i ≠ vc (i + 1)

structure PolygonData (vc : Fin M → κ) (ec : Fin M → ι) : Prop where
  three_le : 3 ≤ M
  pairs : EdgePairs ec
  noLoop : NoLoopSide vc
  vc_surj : Function.Surjective vc
  ec_surj : Function.Surjective ec

variable (hc : Compat vc ec)

theorem lt_iff_plt {x y : Cell κ ι M} :
    (toS vc ec hc x < toS vc ec hc y) ↔ plt vc ec x y :=
  ⟨fun ⟨h, hnle⟩ => h.resolve_left fun he => hnle (Or.inl he.symm),
   fun h => lt_of_le_of_ne (Or.inr h) fun he => by have hxy : x = y := he; exact plt_irrefl y (hxy ▸ h)⟩

theorem lt_bed_iff {i : Fin M} {x : Cell κ ι M} :
    (toS vc ec hc x < toS vc ec hc (bed (ec i))) ↔ (x = vtx (vc i) ∨ x = vtx (vc (i + 1))) := by
  rw [lt_iff_plt]
  cases x with
  | vtx v =>
      simp only [Cell.vtx.injEq]
      exact ⟨by rintro ⟨j, hj, rfl | rfl⟩ <;> rcases hc j i hj with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> tauto,
        by rintro (rfl | rfl); exacts [⟨i, rfl, .inl rfl⟩, ⟨i, rfl, .inr rfl⟩]⟩
  | _ => simp [plt]

theorem lt_ced_iff {p : Fin M} {x : Cell κ ι M} :
    (toS vc ec hc x < toS vc ec hc (ced p)) ↔ (x = cvx p ∨ x = cvx (p + 1)) := by
  rw [lt_iff_plt]; cases x <;> simp [plt]

theorem lt_dia_iff {p : Fin M} {x : Cell κ ι M} :
    (toS vc ec hc x < toS vc ec hc (dia p)) ↔ (x = vtx (vc p) ∨ x = cvx p) := by
  rw [lt_iff_plt]; cases x <;> simp [plt, eq_comm]

theorem lt_gdi_iff {p : Fin M} {x : Cell κ ι M} :
    (toS vc ec hc x < toS vc ec hc (gdi p)) ↔ (x = vtx (vc p) ∨ x = cvx (p + 1)) := by
  rw [lt_iff_plt]; cases x <;> simp [plt, eq_comm]

theorem lt_rad_iff {p : Fin M} {x : Cell κ ι M} :
    (toS vc ec hc x < toS vc ec hc (rad p)) ↔ (x = ctr ∨ x = cvx p) := by
  rw [lt_iff_plt]; cases x <;> simp [plt]

theorem bed_lt_iff {i : Fin M} {y : Cell κ ι M} :
    (toS vc ec hc (bed (ec i)) < toS vc ec hc y) ↔ ∃ p : Fin M, ec p = ec i ∧ y = tr1 p := by
  rw [lt_iff_plt]
  cases y with
  | tr1 p => exact ⟨fun h => ⟨p, h.symm, rfl⟩, fun ⟨_, hp', hy⟩ => (Cell.tr1.inj hy ▸ hp').symm⟩
  | _ => simp [plt]

theorem ced_lt_iff {p : Fin M} {y : Cell κ ι M} :
    (toS vc ec hc (ced p) < toS vc ec hc y) ↔ (y = tr2 p ∨ y = inn p) := by
  rw [lt_iff_plt]; cases y <;> simp [plt, eq_comm]

theorem dia_lt_iff {p : Fin M} {y : Cell κ ι M} :
    (toS vc ec hc (dia p) < toS vc ec hc y) ↔ (y = tr2 p ∨ y = tr1 (fpred p)) := by
  rw [lt_iff_plt]
  cases y with
  | tr1 s =>
      simp only [plt, Cell.tr1.injEq, reduceCtorEq, false_or]
      exact ⟨fun h => by rw [h, fpred_succ], fun h => by rw [h, fpred_add_one]⟩
  | tr2 s => simp [plt, eq_comm]
  | _ => simp [plt]

theorem gdi_lt_iff {p : Fin M} {y : Cell κ ι M} :
    (toS vc ec hc (gdi p) < toS vc ec hc y) ↔ (y = tr1 p ∨ y = tr2 p) := by
  rw [lt_iff_plt]; cases y <;> simp [plt, eq_comm]

theorem rad_lt_iff {p : Fin M} {y : Cell κ ι M} :
    (toS vc ec hc (rad p) < toS vc ec hc y) ↔ (y = inn p ∨ y = inn (fpred p)) := by
  rw [lt_iff_plt]
  cases y with
  | inn s =>
      simp only [plt, Cell.inn.injEq]
      exact ⟨by rintro (rfl | rfl); exacts [.inl rfl, .inr (fpred_succ _).symm],
        by rintro (rfl | rfl); exacts [.inl rfl, .inr (fpred_add_one _).symm]⟩
  | _ => simp [plt]

theorem lt_tr1_iff {p : Fin M} {x : Cell κ ι M} :
    (toS vc ec hc x < toS vc ec hc (tr1 p)) ↔
      (x = bed (ec p) ∨ x = dia (p + 1) ∨ x = gdi p ∨
        x = vtx (vc p) ∨ x = vtx (vc (p + 1)) ∨ x = cvx (p + 1)) := by
  rw [lt_iff_plt]; cases x <;> simp [plt, eq_comm]

theorem lt_tr2_iff {p : Fin M} {x : Cell κ ι M} :
    (toS vc ec hc x < toS vc ec hc (tr2 p)) ↔
      (x = ced p ∨ x = dia p ∨ x = gdi p ∨
        x = vtx (vc p) ∨ x = cvx p ∨ x = cvx (p + 1)) := by
  rw [lt_iff_plt]; cases x <;> simp [plt, eq_comm]

theorem lt_inn_iff {p : Fin M} {x : Cell κ ι M} :
    (toS vc ec hc x < toS vc ec hc (inn p)) ↔
      (x = ced p ∨ x = rad p ∨ x = rad (p + 1) ∨
        x = ctr ∨ x = cvx p ∨ x = cvx (p + 1)) := by
  rw [lt_iff_plt]; cases x <;> simp [plt, eq_comm]

theorem not_lt_vtx {x : Cell κ ι M} {v : κ} : ¬ (toS vc ec hc x < toS vc ec hc (vtx v)) :=
  fun h => by have := (lt_iff_plt hc).1 h; cases x <;> simp [plt] at this

theorem not_lt_cvx {x : Cell κ ι M} {p : Fin M} : ¬ (toS vc ec hc x < toS vc ec hc (cvx p)) :=
  fun h => by have := (lt_iff_plt hc).1 h; cases x <;> simp [plt] at this

theorem not_lt_ctr {x : Cell κ ι M} : ¬ (toS vc ec hc x < toS vc ec hc ctr) :=
  fun h => by have := (lt_iff_plt hc).1 h; cases x <;> simp [plt] at this

theorem two_vertices_SCell (hd : PolygonData vc ec) :
    ∀ e : SCell vc ec hc, Cell.rk e = 1 → ExactlyTwo (fun v : SCell vc ec hc => v < e) := by
  have hM2 : 2 ≤ M := by have := hd.three_le; omega
  intro (e : Cell κ ι M) he
  have mk2 {a b : Cell κ ι M} (h : ∀ z : Cell κ ι M, toS vc ec hc z < toS vc ec hc e ↔ z = a ∨ z = b) (hne : a ≠ b) :
      ExactlyTwo (fun v : SCell vc ec hc => v < toS vc ec hc e) :=
    ⟨a, b, hne, (h a).2 (.inl rfl), (h b).2 (.inr rfl), fun z hz => (h z).1 hz⟩
  cases e with
  | bed e' =>
      obtain ⟨i, rfl⟩ := hd.ec_surj e'
      exact mk2 (fun _ => lt_bed_iff hc) fun h => hd.noLoop i (Cell.vtx.inj h)
  | ced p => exact mk2 (fun _ => lt_ced_iff hc) fun h => fin_succ_ne_self hM2 p (Cell.cvx.inj h).symm
  | dia p => exact mk2 (fun _ => lt_dia_iff hc) nofun
  | gdi p => exact mk2 (fun _ => lt_gdi_iff hc) nofun
  | rad p => exact mk2 (fun _ => lt_rad_iff hc) nofun
  | _ => simp [Cell.rk] at he

theorem two_faces_SCell (hd : PolygonData vc ec) :
    ∀ e : SCell vc ec hc, Cell.rk e = 1 → ExactlyTwo (fun f : SCell vc ec hc => e < f) := by
  have hM2 : 2 ≤ M := by have := hd.three_le; omega
  intro (e : Cell κ ι M) he
  have mk2 {a b : Cell κ ι M} (h : ∀ z : Cell κ ι M, toS vc ec hc e < toS vc ec hc z ↔ z = a ∨ z = b) (hne : a ≠ b) :
      ExactlyTwo (fun f : SCell vc ec hc => toS vc ec hc e < f) :=
    ⟨a, b, hne, (h a).2 (.inl rfl), (h b).2 (.inr rfl), fun z hz => (h z).1 hz⟩
  cases e with
  | bed e' =>
      obtain ⟨i, rfl⟩ := hd.ec_surj e'
      obtain ⟨j, hji, hecj, huniq⟩ := hd.pairs i
      refine ⟨tr1 i, tr1 j, fun h => hji (Cell.tr1.inj h).symm,
        (bed_lt_iff hc).2 ⟨i, rfl, rfl⟩, (bed_lt_iff hc).2 ⟨j, hecj, rfl⟩, fun (z : Cell κ ι M) hz => ?_⟩
      obtain ⟨p, hp, rfl⟩ := (bed_lt_iff hc).1 hz
      exact (huniq p hp).imp (congrArg tr1) (congrArg tr1)
  | ced p => exact mk2 (fun _ => ced_lt_iff hc) nofun
  | dia p => exact mk2 (fun _ => dia_lt_iff hc) nofun
  | gdi p => exact mk2 (fun _ => gdi_lt_iff hc) nofun
  | rad p =>
      exact mk2 (fun _ => rad_lt_iff hc) fun h => by
        have hp := fpred_add_one p; rw [(Cell.inn.inj h).symm] at hp; exact fin_succ_ne_self hM2 p hp
  | _ => simp [Cell.rk] at he

attribute [local simp] lt_bed_iff lt_ced_iff lt_dia_iff lt_gdi_iff lt_rad_iff
  lt_tr1_iff lt_tr2_iff lt_inn_iff not_lt_vtx not_lt_cvx not_lt_ctr

set_option maxHeartbeats 800000 in
theorem two_edges_SCell (hd : PolygonData vc ec) :
    ∀ v f : SCell vc ec hc, Cell.rk v = 0 → Cell.rk f = 2 → v < f →
      ExactlyTwo (fun e : SCell vc ec hc => v < e ∧ e < f) := by
  have hM2 : 2 ≤ M := by have := hd.three_le; omega
  have hsucc (p : Fin M) : cvx p ≠ (cvx (p + 1) : Cell κ ι M) :=
    fun h => fin_succ_ne_self hM2 p (Cell.cvx.inj h).symm
  have hloop (p : Fin M) : vtx (vc p) ≠ (vtx (vc (p + 1)) : Cell κ ι M) :=
    fun h => hd.noLoop p (Cell.vtx.inj h)
  have hrad (p : Fin M) : rad p ≠ (rad (p + 1) : Cell κ ι M) :=
    fun h => fin_succ_ne_self hM2 p (Cell.rad.inj h).symm
  have mkE {v f : Cell κ ι M} (e1 e2 : Cell κ ι M)
      (h3 : ∀ z : Cell κ ι M, toS vc ec hc v < toS vc ec hc z ∧ toS vc ec hc z < toS vc ec hc f → z = e1 ∨ z = e2)
      (hne : e1 ≠ e2 := by nofun)
      (h1 : toS vc ec hc v < toS vc ec hc e1 ∧ toS vc ec hc e1 < toS vc ec hc f := by simp)
      (h2 : toS vc ec hc v < toS vc ec hc e2 ∧ toS vc ec hc e2 < toS vc ec hc f := by simp) :
      ExactlyTwo (fun e : Cell κ ι M => toS vc ec hc v < toS vc ec hc e ∧ toS vc ec hc e < toS vc ec hc f) :=
    ⟨e1, e2, hne, h1, h2, h3⟩
  intro (v : Cell κ ι M) (f : Cell κ ι M) hv hf (hvf : toS vc ec hc v < toS vc ec hc f)
  change ExactlyTwo (fun e : Cell κ ι M => toS vc ec hc v < toS vc ec hc e ∧ toS vc ec hc e < toS vc ec hc f)
  cases f with
  | tr1 p =>
      rcases (lt_tr1_iff hc).1 hvf with rfl | rfl | rfl | rfl | rfl | rfl <;> try simp [Cell.rk] at hv
      · exact mkE (bed (ec p)) (gdi p) fun z ⟨hz1, hz2⟩ => by
          rcases (lt_tr1_iff hc).1 hz2 with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
      · exact mkE (bed (ec p)) (dia (p + 1)) fun z ⟨hz1, hz2⟩ => by
          rcases (lt_tr1_iff hc).1 hz2 with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [(hloop p).symm]
      · exact mkE (dia (p + 1)) (gdi p) fun z ⟨hz1, hz2⟩ => by
          rcases (lt_tr1_iff hc).1 hz2 with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  | tr2 p =>
      rcases (lt_tr2_iff hc).1 hvf with rfl | rfl | rfl | rfl | rfl | rfl <;> try simp [Cell.rk] at hv
      · exact mkE (dia p) (gdi p) fun z ⟨hz1, hz2⟩ => by
          rcases (lt_tr2_iff hc).1 hz2 with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
      · exact mkE (ced p) (dia p) fun z ⟨hz1, hz2⟩ => by
          rcases (lt_tr2_iff hc).1 hz2 with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
      · exact mkE (ced p) (gdi p) fun z ⟨hz1, hz2⟩ => by
          rcases (lt_tr2_iff hc).1 hz2 with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [(hsucc p).symm]
  | inn p =>
      rcases (lt_inn_iff hc).1 hvf with rfl | rfl | rfl | rfl | rfl | rfl <;> try simp [Cell.rk] at hv
      · exact mkE (rad p) (rad (p + 1)) (hne := hrad p) fun z ⟨hz1, hz2⟩ => by
          rcases (lt_inn_iff hc).1 hz2 with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
      · exact mkE (ced p) (rad p) fun z ⟨hz1, hz2⟩ => by
          rcases (lt_inn_iff hc).1 hz2 with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
      · exact mkE (ced p) (rad (p + 1)) fun z ⟨hz1, hz2⟩ => by
          rcases (lt_inn_iff hc).1 hz2 with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [(hsucc p).symm]
  | _ => simp [Cell.rk] at hf

def surfaceRank_SCell (hd : PolygonData vc ec) : SurfaceRank (SCell vc ec hc) where
  rk := Cell.rk
  rk_lt_of_lt {_ _} h := rk_lt_of_plt ((lt_iff_plt hc).1 h)
  rk_le_two := rk_le_two
  two_vertices := two_vertices_SCell hc hd
  two_faces := two_faces_SCell hc hd
  two_edges := two_edges_SCell hc hd
  exists_face := fun (x : Cell κ ι M) => by
    cases x with
    | vtx v => obtain ⟨i, rfl⟩ := hd.vc_surj v; exact ⟨tr1 i, rfl, le_of_lt ((lt_tr1_iff hc).2 (by simp))⟩
    | bed e => obtain ⟨i, rfl⟩ := hd.ec_surj e; exact ⟨tr1 i, rfl, le_of_lt ((lt_tr1_iff hc).2 (by simp))⟩
    | cvx p | ced p | dia p | gdi p => exact ⟨tr2 p, rfl, le_of_lt ((lt_tr2_iff hc).2 (by simp))⟩
    | tr1 p => exact ⟨tr1 p, rfl, le_rfl⟩
    | tr2 p => exact ⟨tr2 p, rfl, le_rfl⟩
    | ctr => exact ⟨inn 0, rfl, le_of_lt ((lt_inn_iff hc).2 (by simp))⟩
    | rad p => exact ⟨inn p, rfl, le_of_lt ((lt_inn_iff hc).2 (by simp))⟩
    | inn p => exact ⟨inn p, rfl, le_rfl⟩
  exists_vertex := fun (f : Cell κ ι M) hf => by
    cases f with
    | tr1 p => exact ⟨vtx (vc p), rfl, (lt_tr1_iff hc).2 (by simp)⟩
    | tr2 p => exact ⟨vtx (vc p), rfl, (lt_tr2_iff hc).2 (by simp)⟩
    | inn p => exact ⟨ctr, rfl, (lt_inn_iff hc).2 (by simp)⟩
    | _ => simp [Cell.rk] at hf

theorem edgeInTwoTriangles_SCell [DecidableEq κ] [DecidableEq ι] (hd : PolygonData vc ec) :
    EdgeInTwoTriangles (orderComplex (SCell vc ec hc)) :=
  (surfaceRank_SCell hc hd).edgeInTwoTriangles
