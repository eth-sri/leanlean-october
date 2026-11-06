module

public import Chazelle.Golf

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
  Θ Model.key, param_vtx

/-- A position with parameter `0` has the point and key of the start vertex of its edge. -/
theorem param_zero_same {M : Model} {Q : Polygon} {e h : ℕ} (hp : M.param Q ⟨e, h⟩ = 0) :
    M.pos Q ⟨e, h⟩ = M.pos Q ⟨e, 0⟩ ∧ M.key Q ⟨e, h⟩ = M.key Q ⟨e, 0⟩ := by
  refine ⟨?_, ?_⟩
  · simp only [Model.pos]; rw [hp, param_vtx]
  · simp only [Model.key]; rw [hp, param_vtx]

/-- The key of `(e, 0)` is below that of `(e, h)` iff the parameter of `(e, h)` is positive. -/
theorem key_vtx_lt_iff {M : Model} {Q : Polygon} {e h : ℕ} :
    M.key Q ⟨e, 0⟩ < M.key Q ⟨e, h⟩ ↔ 0 < M.param Q ⟨e, h⟩ := by
  simp only [Model.key, param_vtx]; constructor <;> intro h <;> linarith

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
  · Ξ ite_eq_left hp
    obtain ⟨p1, k1⟩ := param_zero_same hp
    refine ⟨⟨⟨by rw [param_vtx], by rw [param_vtx]; norm_num, ✓⟩, Or.inl rfl⟩, rfl,
      p1.symm, k1.symm, Or.inl rfl⟩
  · Ξ ite_eq_right hp
    have h0 : 0 < M.param Q ⟨e, h⟩ := lt_of_le_of_ne hu.1 (Ne.symm hp)
    exact ⟨⟨hu, Or.inr h0⟩, rfl, rfl, rfl, Or.inr h0⟩

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

/-- The key-comparison branch. -/
theorem tNormK_rs {s : ℕ} (hs : Scr s ∧ Scr (s + 1) ∧ Scr (s + 2) ∧ Scr (s + 3) ∧ Scr (s + 4))
    (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
    (hp : ProperPos M (Qof P) P.n ⟨c.nreg s, c.nreg (s + 1)⟩) (he : c.nreg s < M.W.n)
    (h0 : 0 < c.nreg (s + 1))
    (hbox : ∀ C : Chain, M = chainModel C → 6 ≤ c.nreg s) (hroom : c.nreg ALLOC + normK ≤ W) :
    RS P W c₀ (tNormK s) c (11010 + 6) (fun c' => c'.nreg s = c.nreg s ∧
      ⟨c'.nreg s, c'.nreg (s + 1)⟩ = normOf M (Qof P) ⟨c.nreg s, c.nreg (s + 1)⟩ ∧
      Agr c c' [s + 1, s + 2, s + 3]) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hs
  unfold Scr at h1 h2 h3 h4
  have i22 := hI.h22
  have i23 := hI.h23
  have inR : ∀ r, Scr r → InR r := fun r hr => by unfold Scr at hr; unfold InR; omega
  have hk := kcmp_rs (P := P) (W := W) gKey_ok (a := s) (b := 83022) (d := s) (e := s + 1)
    (u := s + 2) (v := s + 3) (by unfold InR; omega) (by unfold InR; omega) (by unfold InR; omega)
    (by unfold InR; omega) (by unfold Scr; omega) (by unfold Scr; omega) (⋄) hE hI
    ⟨by exact he, by rw [i22]; exact ⟨le_rfl, ⊚ param_vtx, Nat.zero_le _⟩,
      fun C hM _ => hbox C hM⟩
    ⟨he, hp, fun C _ hh => by simp only at hh; omega⟩ (by unfold normK at hroom; omega)
  rw [i22] at hk
  refine RS.mono (K := (11010 + 2) + (0 + 2 + 1)) ?_ (⊛) (fun _ h => h)
  unfold tNormK
  refine RS.seq hk fun c₁ hI₁ _ ⟨b1, _, a1⟩ => ?_
  have k1s : c₁.nreg s = c.nreg s := a1 _ (⋄) (by omega) (by simp)
  have k1h : c₁.nreg (s + 1) = c.nreg (s + 1) := a1 _ (⋄) (by omega) (by simp)
  have k23 : c₁.nreg 83023 = 1 := hI₁.h23
  rw [key_vtx_lt_iff] at b1
  rcases bit01 b1 with ⟨bz, hnp⟩ | ⟨bo, hpos⟩
  · -- parameter `0`
    have hp0 : M.param (Qof P) ⟨c.nreg s, c.nreg (s + 1)⟩ = 0 := le_antisymm (not_lt.1 hnp) hp.1
    refine RS.ifT (by rw [bz, k23]; omega) ((RS.const hI₁ (r := s + 1) (v := 0) (by unfold Scr; omega)
      (Nat.zero_le _)).mono (⊛) fun c₂ hc₂ => ?_)
    have e2s : c₂.nreg s = c.nreg s := by rw [hc₂, upd_ne (⋄), k1s]
    refine ⟨e2s, ?_, (a1.trans (Agr.of_upd hc₂)).mono (✓)⟩
    rw [e2s, hc₂, upd_eq]; unfold normOf; rw [ite_eq_left hp0]
  · -- positive parameter
    refine RS.ifF (by rw [bo, k23]; omega) ((RS.skip hI₁ (K := 1) (Q := fun c' =>
      c'.nreg s = c.nreg s ∧ ⟨c'.nreg s, c'.nreg (s + 1)⟩ =
        normOf M (Qof P) ⟨c.nreg s, c.nreg (s + 1)⟩ ∧ Agr c c' [s + 1, s + 2, s + 3])
      ⟨k1s, ?_, a1.mono (✓)⟩))
    rw [k1s, k1h]; unfold normOf; rw [ite_eq_right (ne_of_gt hpos)]

/-- **Normalising a position.** -/
theorem tNorm_rs {s : ℕ} (hs : Scr s ∧ Scr (s + 1) ∧ Scr (s + 2) ∧ Scr (s + 3) ∧ Scr (s + 4))
    (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
    (hp : ProperPos M (Qof P) P.n ⟨c.nreg s, c.nreg (s + 1)⟩) (he : c.nreg s < M.W.n)
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
    have hz : c.nreg (s + 1) = 0 := by rw [i22] at hh; omega
    refine RS.ifF hh (RS.skip hI ⟨rfl, ?_, Agr.refl _ _⟩)
    unfold normOf; rw [ite_eq_left (by rw [hz]; rfl)]; rw [hz]
  have h0 : 0 < c.nreg (s + 1) := by rw [i22] at hh; exact hh
  refine RS.ifT hh ?_
  refine RS.mono (K := 1 + (11010 + 6 + 2 + 2)) ?_ (⊛) (fun _ h => h)
  refine RS.seq (RS.const hI (r := s + 4) (v := 6) (by unfold Scr; omega)
    (by have := hE.hW; unfold hostWords at this; omega)) fun c₁ hI₁ hA₁ hc₁ => ?_
  have k1 : ∀ r, r ≠ s + 4 → c₁.nreg r = c.nreg r := fun r hr => Ρ hc₁, upd_ne hr
  have p1 : ProperPos M (Qof P) P.n ⟨c₁.nreg s, c₁.nreg (s + 1)⟩ := by
    rw [k1 s (⋄), k1 (s + 1) (by omega)]; exact hp
  have e1 : c₁.nreg s < M.W.n := by rw [k1 s (⋄)]; exact he
  have z1 : 0 < c₁.nreg (s + 1) := by rw [k1 (s + 1) (⋄)]; exact h0
  have a1 : Agr c c₁ [s + 4] := Agr.of_upd hc₁
  have fin : ∀ c₂, (c₂.nreg s = c₁.nreg s ∧ ⟨c₂.nreg s, c₂.nreg (s + 1)⟩ =
      normOf M (Qof P) ⟨c₁.nreg s, c₁.nreg (s + 1)⟩ ∧ Agr c₁ c₂ [s + 1, s + 2, s + 3]) →
      (c₂.nreg s = c.nreg s ∧ ⟨c₂.nreg s, c₂.nreg (s + 1)⟩ =
        normOf M (Qof P) ⟨c.nreg s, c.nreg (s + 1)⟩ ∧ Agr c c₂ [s + 1, s + 2, s + 3, s + 4]) :=
    fun c₂ ⟨q1, q2, q3⟩ => by
      refine ⟨by rw [q1, k1 s (⋄)], by rw [q2, k1 s (by omega), k1 (s + 1) (by omega)],
        (a1.trans q3).mono (✓)⟩
  have hroom1 : c₁.nreg ALLOC + normK ≤ W := by
    have := hI₁.hA; rw [k1 _ (by unfold ALLOC; omega)]; exact hroom
  have i21 := hI₁.h21
  have i23 := hI₁.h23
  rcases hE.kind with ⟨hz, C, hMC⟩ | ⟨h1', hMi, -⟩
  · -- a chain model
    refine RS.ifT (by rw [i21, i23, hz]; omega) ?_
    by_cases hb : c₁.nreg s < c₁.nreg (s + 4)
    · -- a box edge: the parameter is positive
      have h6 : c.nreg s < 6 := by rw [k1 s (⋄), hc₁, upd_eq] at hb; exact hb
      have hpos : 0 < M.param (Qof P) ⟨c.nreg s, c.nreg (s + 1)⟩ := by
        subst hMC
        exact box_param_pos C (x := ⟨c.nreg s, c.nreg (s + 1)⟩) h6 hp.1 (hy C rfl)
      refine RS.ifT hb (RS.skip hI₁ (fin c₁ ⟨rfl, ?_, Agr.refl _ _⟩))
      rw [k1 s (⋄), k1 (s + 1) (by omega)]
      unfold normOf; rw [ite_eq_right (ne_of_gt hpos)]
    · refine RS.ifF hb ((tNormK_rs hs' hE hI₁ p1 e1 z1 (fun C' _ => ?_) hroom1).mono
        (⊛) fin)
      have v4 : c₁.nreg (s + 4) = 6 := Ρ hc₁, upd_eq
      omega
  · -- the interior model
    refine RS.ifF (by rw [i21, i23, h1']; omega) ((tNormK_rs hs' hE hI₁ p1 e1 z1
      (fun C' hC' => absurd (hC'.symm.trans hMi) (chainModel_ne_interior C' _)) hroom1).mono
      (⊛) fin)

end

end Restore

end Chazelle.Core
