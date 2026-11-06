module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.RestoreTValid
public import Chazelle.Core.RestoreTDisp
public import Chazelle.Core.ShotListCut

/-!
# WP-E, the candidate test on the RAM: normalising a walk position

The shot wrapper needs **normalised** arc ends (`ShotList.NormPos`: height code `0` exactly when
the parameter is `0`).  `tNorm s` normalises the position in the registers `s`, `s + 1` of band
`bRestore`: a position `(e, h)` with `h > 0` and parameter `0` becomes `(e, 0)` (same point, same
key).  The parameter is tested with the key comparison `gKey` of `(e, 0)` and `(e, h)`; at the
box edges of a chain model (`e < 6`) no test is needed, since a point inside the height band of
the box has a positive parameter there (`SweepPrim.box_param_pos`).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim ShotList

variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ c : Config}

/-! ## Mathematics -/

theorem param_vtx (M : Model) (Q : Polygon) (e : ℕ) : M.param Q ⟨e, 0⟩ = 0 := rfl

theorem key_vtx' (M : Model) (Q : Polygon) (e : ℕ) : M.key Q ⟨e, 0⟩ = e := by
  simp [Model.key, param_vtx]

/-- A position with parameter `0` has the point and key of the start vertex of its edge. -/
theorem param_zero_same {M : Model} {Q : Polygon} {e h : ℕ} (hp : M.param Q ⟨e, h⟩ = 0) :
    M.pos Q ⟨e, h⟩ = M.pos Q ⟨e, 0⟩ ∧ M.key Q ⟨e, h⟩ = M.key Q ⟨e, 0⟩ := by
  simp_all [Model.pos, param_vtx, Model.key] 

/-- The key of `(e, 0)` is below that of `(e, h)` iff the parameter of `(e, h)` is positive. -/
theorem key_vtx_lt_iff {M : Model} {Q : Polygon} {e h : ℕ} :
    M.key Q ⟨e, 0⟩ < M.key Q ⟨e, h⟩ ↔ 0 < M.param Q ⟨e, h⟩ := by
  simp_all [Model.key, param_vtx] 

/-- **The normal form of a position**: `(e, 0)` if its parameter is `0`, else itself. -/
noncomputable def normOf (M : Model) (Q : Polygon) (u : WPos) : WPos :=
  if M.param Q u = 0 then ⟨u.edge, 0⟩ else u

theorem normOf_facts {M : Model} {Q : Polygon} {n : ℕ} {u : WPos} (hu : ProperPos M Q n u) :
    NormPos M Q n (normOf M Q u) ∧ (normOf M Q u).edge = u.edge ∧
      M.pos Q (normOf M Q u) = M.pos Q u ∧ M.key Q (normOf M Q u) = M.key Q u ∧
      ((normOf M Q u).hgt = 0 ∨ 0 < M.param Q (normOf M Q u)) := by
  obtain ⟨e, h⟩ := u
  unfold normOf
  by_cases hp : M.param Q ⟨e, h⟩ = 0
  · rw [ite_eq_left hp]
    obtain ⟨p1, k1⟩ := param_zero_same hp
    refine ⟨⟨⟨by aesop, by grind [param_vtx], by simp⟩, Or.inl rfl⟩, rfl,
      p1.symm, k1.symm, Or.inl rfl⟩
  ram_grind

/-! ## The machine -/

/-- The parameter test by the key comparison: `(e, h)` becomes `(e, 0)` if `key (e, 0)` is not
below `key (e, h)`. -/
def tNormK (s : ℕ) : Stmt :=
  .seq (.seq (gKey s 83022 s (s + 1)) (cp2 (s + 2) (s + 3)))
    (.ifLtN (s + 2) 83023 (.instr (.constN (s + 1) 0)) .skip)

/-- **Normalising the position in `s`, `s + 1`** (scratch `s + 2 … s + 4`). -/
def tNorm (s : ℕ) : Stmt :=
  .ifLtN 83022 (s + 1)
    (.seq (.instr (.constN (s + 4) 6))
      (.ifLtN 83021 83023 (.ifLtN s (s + 4) .skip (tNormK s)) (tNormK s)))
    .skip

/-- The cost bound of `tNorm`. -/
def normK : ℕ := 11010 + 20

section
variable {s : ℕ} (hs : Scr s ∧ Scr (s + 1) ∧ Scr (s + 2) ∧ Scr (s + 3) ∧ Scr (s + 4)) (hE : TGood P W M N c₀) (hI : TInv W c₀ c) (hp : ProperPos M (Qof P) P.n ⟨c.nreg s, c.nreg (s + 1)⟩) (he : c.nreg s < M.W.n)
include hs hE hI hp he
/-- The key-comparison branch. -/
theorem tNormK_rs
    (h0 : 0 < c.nreg (s + 1))
    (hbox : ∀ C : Chain, M = chainModel C → 6 ≤ c.nreg s) (hroom : c.nreg ALLOC + normK ≤ W) :
    RS P W c₀ (tNormK s) c (11010 + 6) (fun c' => c'.nreg s = c.nreg s ∧
      ⟨c'.nreg s, c'.nreg (s + 1)⟩ = normOf M (Qof P) ⟨c.nreg s, c.nreg (s + 1)⟩ ∧
      Agr c c' [s + 1, s + 2, s + 3]) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hs
  unfold Scr at h1 h2 h3 h4
  have i22 := hI.h22
  
  
  have hk := kcmp_rs (P := P) (W := W) gKey_ok (a := s) (b := 83022) (d := s) (e := s + 1)
    (u := s + 2) (v := s + 3) (by omega_nf) (by omega_nf) (by omega_nf)
    (by omega_nf) (by omega_nf) (by omega_nf) (by omega) hE hI
    ⟨by exact he, by grind [Chazelle.Core.ProperPos, param_vtx],
      fun C hM _ => hbox C hM⟩
    ⟨he, hp, fun C _ hh => by ram_simp⟩ (by omega_nf)
  rw [i22] at hk
  refine RS.mono (K := (11010 + 2) + (0 + 2 + 1)) ?_ (by norm_num) (fun _ h => h)
  unfold tNormK
  refine RS.seq hk fun c₁ hI₁ _ ⟨b1, _, a1⟩ => ?_
  have k1s : c₁.nreg s = c.nreg s := a1 _ (by omega) (by omega) (by simp)
  have k1h : c₁.nreg (s + 1) = c.nreg (s + 1) := a1 _ (by omega) (by omega) (by simp)
  have k23 : c₁.nreg 83023 = 1 := hI₁.h23
  rw [key_vtx_lt_iff] at b1
  rcases bit01 b1 with ⟨bz, hnp⟩ | ⟨bo, hpos⟩
  · -- parameter `0`
    have hp0 : M.param (Qof P) ⟨c.nreg s, c.nreg (s + 1)⟩ = 0 := le_antisymm (not_lt.1 hnp) hp.1
    refine RS.ifT (by omega) ((RS.const hI₁ (r := s + 1) (v := 0) (by omega_nf)
      (Nat.zero_le _)).mono (by norm_num) fun c₂ hc₂ => ?_)
    have e2s : c₂.nreg s = c.nreg s := by simp_all +zetaDelta 
    refine ⟨e2s, ?_, (a1.trans (Agr.of_upd hc₂)).mono (by simp)⟩
    rw [e2s, hc₂, upd_eq]; grind [normOf]
  · -- positive parameter
    refine RS.ifF (by omega) ((RS.skip hI₁ (K := 1) (Q := fun c' =>
      c'.nreg s = c.nreg s ∧ ⟨c'.nreg s, c'.nreg (s + 1)⟩ =
        normOf M (Qof P) ⟨c.nreg s, c.nreg (s + 1)⟩ ∧ Agr c c' [s + 1, s + 2, s + 3])
      ⟨k1s, ?_, a1.mono (by simp)⟩))
    grind [normOf]

/-- **Normalising a position.** -/
theorem tNorm_rs
    (hy : ∀ C : Chain, M = chainModel C →
      |(M.pos (Qof P) ⟨c.nreg s, c.nreg (s + 1)⟩).2| < C.radius)
    (hroom : c.nreg ALLOC + normK ≤ W) :
    RS P W c₀ (tNorm s) c normK (fun c' => c'.nreg s = c.nreg s ∧
      ⟨c'.nreg s, c'.nreg (s + 1)⟩ = normOf M (Qof P) ⟨c.nreg s, c.nreg (s + 1)⟩ ∧
      Agr c c' [s + 1, s + 2, s + 3, s + 4]) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  have hs' : Scr s ∧ Scr (s + 1) ∧ Scr (s + 2) ∧ Scr (s + 3) ∧ Scr (s + 4) :=
    ⟨h1, h2, h3, h4, h5⟩
  unfold Scr at h1 h2 h3 h4 h5
  have i22 := hI.h22
  unfold tNorm
  by_cases hh : c.nreg 83022 < c.nreg (s + 1)
  swap
  · -- a vertex: already normal
    have hz : c.nreg (s + 1) = 0 := by omega
    refine RS.ifF hh (RS.skip hI ⟨rfl, ?_, Agr.refl _ _⟩)
    simp_all [normOf] 
  
  refine RS.ifT hh ?_
  refine RS.mono (K := 1 + (11010 + 6 + 2 + 2)) ?_ (by norm_num) (fun _ h => h)
  refine RS.seq (RS.const hI (r := s + 4) (v := 6) (by omega_nf)
    (by omega_nf)) fun c₁ hI₁ hA₁ hc₁ => ?_
  have k1 : ∀ r, r ≠ s + 4 → c₁.nreg r = c.nreg r := fun r hr => by ram_simp
  have p1 : ProperPos M (Qof P) P.n ⟨c₁.nreg s, c₁.nreg (s + 1)⟩ := by
    ram_grind
  have e1 : c₁.nreg s < M.W.n := by ram_grind
  have z1 : 0 < c₁.nreg (s + 1) := by ram_grind
  have a1 : Agr c c₁ [s + 4] := Agr.of_upd hc₁
  have fin : ∀ c₂, (c₂.nreg s = c₁.nreg s ∧ ⟨c₂.nreg s, c₂.nreg (s + 1)⟩ =
      normOf M (Qof P) ⟨c₁.nreg s, c₁.nreg (s + 1)⟩ ∧ Agr c₁ c₂ [s + 1, s + 2, s + 3]) →
      (c₂.nreg s = c.nreg s ∧ ⟨c₂.nreg s, c₂.nreg (s + 1)⟩ =
        normOf M (Qof P) ⟨c.nreg s, c.nreg (s + 1)⟩ ∧ Agr c c₂ [s + 1, s + 2, s + 3, s + 4]) :=
    fun c₂ ⟨q1, q2, q3⟩ => by
      refine ⟨by ram_grind, by ram_grind,
        (a1.trans q3).mono (by simp)⟩
  have hroom1 : c₁.nreg ALLOC + normK ≤ W := by
    grind [ALLOC]
  have i21 := hI₁.h21
  have i23 := hI₁.h23
  rcases hE.kind with ⟨hz, C, hMC⟩ | ⟨h1', hMi, -⟩
  · -- a chain model
    refine RS.ifT (by omega) ?_
    by_cases hb : c₁.nreg s < c₁.nreg (s + 4)
    · -- a box edge: the parameter is positive
      have h6 : c.nreg s < 6 := by rw [k1 s (by omega), hc₁, upd_eq] at hb; exact hb
      have hpos : 0 < M.param (Qof P) ⟨c.nreg s, c.nreg (s + 1)⟩ := by
        subst hMC
        exact box_param_pos C (x := ⟨c.nreg s, c.nreg (s + 1)⟩) h6 hp.1 (hy C rfl)
      refine RS.ifT hb (RS.skip hI₁ (fin c₁ ⟨rfl, ?_, Agr.refl _ _⟩))
      grind [normOf]
    · refine RS.ifF hb ((tNormK_rs hs' hE hI₁ p1 e1 z1 (fun C' _ => ?_) hroom1).mono
        (by norm_num) fin)
      have v4 : c₁.nreg (s + 4) = 6 := by rw [hc₁, upd_eq]
      omega
  · -- the interior model
    refine RS.ifF (by omega) ((tNormK_rs hs' hE hI₁ p1 e1 z1
      (fun C' hC' => absurd (hC'.symm.trans hMi) (chainModel_ne_interior C' _)) hroom1).mono
      (by norm_num) fin)


end

end

end Restore

end Chazelle.Core
