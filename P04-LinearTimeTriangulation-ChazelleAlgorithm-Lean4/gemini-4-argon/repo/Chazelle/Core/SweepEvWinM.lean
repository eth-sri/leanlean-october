module

public import Chazelle.Core.SweepEvTasks
public import Chazelle.Core.OracleZipMath

/-!
# The sweep (WP-D), stage 3: the window of the event loop (mathematics)

* cyclic arcs in offsets (`sia_iff_off`, `cIn_of_off`, `cIn_of_U`);
* the key of the walk of `C` read in the walk of `C₁` (`kr`, `kd`, `ke₁`, `key_map`, `key₁_off`);
* monotonicity of the part offsets (`lex_lt`, `lex_le`, `lex_le_gap`);
* the arc after the key (`arc_of_loc`, `arc_of_loc'`), the window ends (`wend_map`, `wend_cut`,
  `wend_gap`, `gap_pt`) and the coverage by the gathered arcs (`mem_loSet`, `cover_arc`).
-/

namespace Chazelle.Core

namespace SweepEv

open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep ShotList
open Chazelle.Chain (sideInArc sidePt SideAttach)

@[expose] public section

theorem off_eq_sub {n g x y : ℝ} (hx0 : 0 ≤ x) (hyn : y < n) (h : off n g x ≤ off n g y) :
    off n x y = off n g y - off n g x := by
  unfold off at *; split_ifs at * <;> linarith

theorem off_eq_sub' {n g x y : ℝ} (hxn : x < n) (hy0 : 0 ≤ y) (h : off n g y < off n g x) :
    off n x y = off n g y - off n g x + n := by
  unfold off at *; split_ifs at * <;> linarith

theorem sia_iff_off {n a b z : ℝ} (hab : a ≠ b) (han : a < n) (hb0 : 0 ≤ b) (hbn : b < n)
    (hz0 : 0 ≤ z) (hzn : z < n) :
    sideInArc a b z ↔ 0 < off n a z ∧ off n a z < off n a b := by
  unfold sideInArc off
  by_cases hlt : a < b
  · rw [ite_eq_left hlt, ite_eq_left hlt.le]
    by_cases haz : a ≤ z
    · rw [ite_eq_left haz]; constructor
      · rintro ⟨h1, h2⟩; constructor <;> linarith
      · rintro ⟨h1, h2⟩; constructor <;> linarith
    · rw [ite_eq_right haz]; constructor
      · rintro ⟨h1, h2⟩; linarith
      · rintro ⟨h1, h2⟩; linarith
  · have hba : ¬ a ≤ b := fun h => hab (le_antisymm h (not_lt.1 hlt))
    rw [ite_eq_right hlt, ite_eq_right hba]
    by_cases haz : a ≤ z
    · rw [ite_eq_left haz]; constructor
      · rintro (h | h) <;> constructor <;> linarith
      · rintro ⟨h1, h2⟩; left; linarith
    · rw [ite_eq_right haz]; constructor
      · rintro (h | h) <;> constructor <;> linarith
      · rintro ⟨h1, h2⟩; right; linarith

/-- **The closed arc after a point of it.** -/
theorem cIn_of_off {n a b x y : ℝ} (han : a < n) (hb0 : 0 ≤ b) (hbn : b < n)
    (hx0 : 0 ≤ x) (hxn : x < n) (hy0 : 0 ≤ y) (hyn : y < n) (hab : a ≠ b)
    (hx : sideInArc a b x ∨ a = x) (hpos : 0 < off n x y) (hle : off n x y ≤ off n x b) :
    CIn a b y := by
  have hxb : off n a x < off n a b := by
    rcases hx with hx | rfl
    · exact ((sia_iff_off hab han hb0 hbn hx0 hxn).1 hx).2
    · rw [off_self n a]
      unfold off; split_ifs with h
      · rcases lt_or_eq_of_le h with h | h
        · linarith
        · exact absurd h hab
      · linarith
  have e1 : off n x b = off n a b - off n a x := off_eq_sub hx0 hbn hxb.le
  have hay : off n a y = off n a x + off n x y := by
    unfold off at *; split_ifs at * <;> linarith
  by_cases hyb : y = b
  · exact Or.inr (Or.inr hyb)
  · left
    rw [sia_iff_off hab han hb0 hbn hy0 hyn]
    have hax : 0 ≤ off n a x := off_nonneg hx0 han
    refine ⟨by linarith, lt_of_le_of_ne (by linarith) fun h => hyb ?_⟩
    unfold off at h; split_ifs at h <;> linarith

section Gap

variable {J : Merge.Junction}

theorem win_n_eq : (chainModel J.whole).W.n = 2 * J.whole.m + 7 := cm_n J.whole

theorem win_n₁_eq : (chainModel J.left).W.n = 2 * J.left.m + 7 := cm_n J.left

theorem win_lδ_cases : lδ J = 0 ∨ lδ J = 7 := by unfold lδ; split_ifs <;> simp

theorem win_Lst_lt : Lst J < (chainModel J.whole).W.n := by
  rw [Lst_rlen, win_n_eq]
  have hm : J.whole.m = J.m₁ + J.m₂ := rfl
  have := J.one_le_m₁
  unfold rlen; split_ifs <;> omega

theorem win_gW_lt : gW J < (chainModel J.whole).W.n := by
  have := tpos_lt J.whole J.m₁
  rw [win_n_eq]; unfold gW; omega

theorem win_E₁_eq : E₁ J = (chainModel J.whole).W.n - Lst J + lδ J := rfl

/-- **The facts of the left gap** (case G). -/
theorem gap_facts (hP : J.P.Simple) (hδ : 0 < lδ J) :
    VNotTop J ∧ lδ J = 7 ∧ lL1 J = 2 * J.m₁ - tpos J.left J.m₁ ∧ b₁ J = 6 + tpos J.left J.m₁ ∧
      0 < tpos J.left J.m₁ ∧ tpos J.left J.m₁ < 2 * J.m₁ ∧
      Lst J + lL1 J < (chainModel J.whole).W.n ∧
      (gW J + (Lst J + lL1 J)) % (chainModel J.whole).W.n =
        6 + tpos J.whole (J.m₁ + 2 * J.m₂) + lL1 J ∧
      6 + tpos J.whole (J.m₁ + 2 * J.m₂) + lL1 J < (chainModel J.whole).W.n := by
  have hv : VNotTop J := by
    by_contra h; have := (nvt_left J hP h).2.1; omega
  obtain ⟨h7, hl1, hl2, hτp, hτl⟩ := left_G hδ
  have hb : b₁ J = 6 + tpos J.left J.m₁ := by
    unfold b₁; rw [ite_eq_right (fun h => (caseB_facts J h).1 hv)]
  have hlOff : lOff J = Lst J := by rw [lOff_of_vnt J hv, Lst_rlen]
  have hlen : Lst J + llen J = (chainModel J.whole).W.n := by
    rw [Lst_rlen]; exact rlen_add_llen J hv
  have hL := lL1_add_lL2 J
  have hA : ¬ 2 * J.whole.m - tpos J.whole (J.m₁ + 2 * J.m₂) < 2 * J.m₁ := by
    intro h; unfold lδ at hδ; rw [ite_eq_left h] at hδ; omega
  have hτ := tpos_lt J.whole (J.m₁ + 2 * J.m₂)
  have hn := win_n_eq (J := J)
  have hlt : 6 + tpos J.whole (J.m₁ + 2 * J.m₂) + lL1 J < (chainModel J.whole).W.n := by
    rw [hn]; omega
  refine ⟨hv, h7, hl1, hb, hτp, hτl, by omega, ?_, hlt⟩
  rw [← add_assoc, ← Nat.mod_add_mod, ← hlOff, gL_eq, Nat.mod_eq_of_lt hlt]

/-- `Lst + ψ d < n` on the `C₁` part. -/
theorem Lst_ψ_lt (hP : J.P.Simple) {d : ℕ} (hd : d < E₁ J) :
    Lst J + ψ J d < (chainModel J.whole).W.n := by
  have hL := win_Lst_lt (J := J)
  rw [win_E₁_eq] at hd
  unfold ψ
  split_ifs with h1 h2
  · have := (gap_facts hP h1.1).2.2.2.2.2.2.1; omega
  · omega
  · rcases win_lδ_cases (J := J) with h | h
    · omega
    · have := (gap_facts hP (by omega)).2.2.2.2.2.2.1
      have : d ≤ lL1 J := by by_contra h'; exact h1 ⟨by omega, by omega⟩
      omega

end Gap

/-! ## The key read in the walk of `C₁` -/

section Key

variable {J : Merge.Junction}

theorem dOf_add_mod {n g d : ℕ} (hg : g < n) (hd : d < n) : dOf n g ((g + d) % n) = d :=
  add_mod_inj (dOf_lt (by omega) g _) hd (add_dOf hg (Nat.mod_lt _ (by omega)))

/-- The part offset `D - Lst` of the key edge `e` (as the RAM computes it). -/
noncomputable def kr (J : Merge.Junction) (e : ℕ) : ℕ :=
  dOf (chainModel J.whole).W.n ((gW J + Lst J) % (chainModel J.whole).W.n) e

/-- The `b₁`-offset of a part offset (beyond the gap if at or after its start). -/
noncomputable def d0Of (J : Merge.Junction) (r : ℕ) : ℕ := if lL1 J ≤ r then r + lδ J else r

/-- The `b₁`-offset of the key edge. -/
noncomputable def kd (J : Merge.Junction) (e : ℕ) : ℕ := d0Of J (kr J e)

/-- The edge of the walk of `C₁` of the key edge. -/
noncomputable def ke₁ (J : Merge.Junction) (e : ℕ) : ℕ := (b₁ J + kd J e) % (chainModel J.left).W.n

theorem win_offK_eq {P : Polygon} {e h : ℕ} (he : e < (chainModel J.whole).W.n)
    (hpp : ProperPos (chainModel J.whole) (Qof P) P.n ⟨e, h⟩) :
    offK P J e h = (dOf (chainModel J.whole).W.n (gW J) e : ℝ) +
      (chainModel J.whole).param (Qof P) ⟨e, h⟩ := by
  unfold offK
  exact off_key' win_gW_lt he hpp.1 hpp.2.1

/-- **The key in the walk of `C₁`.** -/
theorem key_map {P : Polygon} (hP : J.P.Simple) {e h : ℕ} (hpw : PosW P J e h)
    (hL : (Lst J : ℝ) ≤ offK P J e h) :
    offK P J e h = (Lst J : ℝ) + (kr J e : ℝ) + (chainModel J.whole).param (Qof P) ⟨e, h⟩ ∧
      kd J e < E₁ J ∧ (0 < lδ J → kd J e < lL1 J ∨ lL1 J + lδ J ≤ kd J e) ∧
      ψ J (kd J e) = kr J e ∧ mEdge J (kd J e) = e ∧ MValid J (kd J e) (1 / 2) ∧
      (chainModel J.left).param (Qof P) ⟨ke₁ J e, h⟩ = (chainModel J.whole).param (Qof P) ⟨e, h⟩ ∧
      (∀ s, sidePt (chainModel J.whole).W e s = sidePt (chainModel J.left).W (ke₁ J e) s) := by
  obtain ⟨he, hpp, -⟩ := hpw
  have hg := win_gW_lt (J := J)
  have hLn := win_Lst_lt (J := J)
  set n := (chainModel J.whole).W.n with hn
  set D := dOf n (gW J) e with hD
  have hDn : D < n := dOf_lt (by omega) _ _
  have hoff := win_offK_eq (J := J) he hpp
  rw [← hD] at hoff
  have hLD : Lst J ≤ D := by
    have h1 : (Lst J : ℝ) < D + 1 := by rw [hoff] at hL; linarith [hpp.2.1]
    exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast h1)
  have hr : kr J e = D - Lst J := by
    refine add_mod_inj (g := (gW J + Lst J) % n) (dOf_lt (by omega) _ _) (by omega) ?_
    unfold kr
    rw [← hn, add_dOf (Nat.mod_lt _ (by omega)) he, Nat.mod_add_mod,
      show gW J + Lst J + (D - Lst J) = gW J + D by omega, hD, add_dOf hg he]
  have hE : kd J e < E₁ J := by
    rw [win_E₁_eq]; unfold kd d0Of; rw [hr]; split_ifs <;> omega
  have hgap : 0 < lδ J → kd J e < lL1 J ∨ lL1 J + lδ J ≤ kd J e := by
    intro _; unfold kd d0Of; split_ifs <;> omega
  have hψ : ψ J (kd J e) = kr J e := by
    unfold kd d0Of ψ; split_ifs <;> omega
  have hm : mEdge J (kd J e) = e := by
    unfold mEdge; rw [hψ, hr, ← hn, show Lst J + (D - Lst J) = D by omega, hD, add_dOf hg he]
  have hv : MValid J (kd J e) (1 / 2) := by
    refine ⟨hE, fun h => ?_, fun h => ?_, fun h => absurd h (by norm_num)⟩
    · rcases hgap h.1 with h' | h' <;> omega
    · rcases hgap h.1 with h' | h' <;> omega
  refine ⟨?_, hE, hgap, hψ, hm, hv, ?_, fun s => ?_⟩
  · rw [hoff, hr]; push_cast [hLD]; ring
  · have := param_corr hP hv (by norm_num) (Qof P) h
    rw [hm] at this; exact this.symm
  · have := edge_corr hP hv (by norm_num) s
    rw [hm] at this; exact this

/-- The key of the key position in the walk of `C₁` has `b₁`-offset `kd + t₀`. -/
theorem key₁_off {P : Polygon} (hP : J.P.Simple) {e h : ℕ} (hpw : PosW P J e h)
    (hL : (Lst J : ℝ) ≤ offK P J e h) :
    off (chainModel J.left).W.n (b₁ J) ((chainModel J.left).key (Qof P) ⟨ke₁ J e, h⟩) =
      (kd J e : ℝ) + (chainModel J.whole).param (Qof P) ⟨e, h⟩ := by
  obtain ⟨-, hE, -, -, -, -, hpar, -⟩ := key_map hP hpw hL
  have hpp := hpw.2.1
  unfold Model.key
  simp only
  rw [hpar]
  exact off_key b₁_lt (lt_of_lt_of_le hE (E₁_le hP)) hpp.1 hpp.2.1

end Key

/-! ## Monotonicity of the part offsets -/

section Mono

variable {J : Merge.Junction}

/-- Gap property of a `b₁`-offset: not inside the gap and not at its start. -/
def GapOut (J : Merge.Junction) (d : ℕ) : Prop := 0 < lδ J → d < lL1 J ∨ lL1 J + lδ J ≤ d

theorem ψ_mono {d d' : ℕ} (h : d ≤ d') : ψ J d ≤ ψ J d' := by
  unfold ψ; split_ifs <;> omega

theorem ψ_step {d d' : ℕ} (h : d < d') (hd : GapOut J d) : ψ J d + 1 ≤ ψ J d' := by
  unfold GapOut at hd; unfold ψ; split_ifs <;> omega

/-- **Beyond the key**: a valid offset whose image is beyond the image of the key lies beyond it
in the walk of `C₁`. -/
theorem lex_lt {d₀ d : ℕ} {t₀ t : ℝ} (hd₀ : GapOut J d₀)
    (hv2 : ¬ (0 < lδ J ∧ lL1 J < d ∧ d < lL1 J + lδ J)) (hv3 : ¬ (0 < lδ J ∧ d = lL1 J ∧ t ≠ 0))
    (ht0 : 0 ≤ t) (ht1 : t < 1) (ht₀0 : 0 ≤ t₀) (ht₀1 : t₀ < 1)
    (h : (ψ J d₀ : ℝ) + t₀ < ψ J d + t) : (d₀ : ℝ) + t₀ < d + t := by
  by_contra hc
  push Not at hc
  have hdd : d ≤ d₀ := by
    have : (d : ℝ) < d₀ + 1 := by linarith
    exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)
  rcases eq_or_lt_of_le hdd with e | hlt
  · subst e; linarith
  · by_cases hs : 0 < lδ J ∧ d = lL1 J
    · have t0 : t = 0 := by by_contra h'; exact hv3 ⟨hs.1, hs.2, h'⟩
      have : ψ J d ≤ ψ J d₀ := ψ_mono hlt.le
      have : (ψ J d : ℝ) ≤ ψ J d₀ := by exact_mod_cast this
      subst t0; linarith
    · have hg : GapOut J d := fun hδ => by
        by_contra h'; push Not at h'
        rcases lt_or_eq_of_le h'.1 with h1 | h1
        · exact hv2 ⟨hδ, h1, h'.2⟩
        · exact hs ⟨hδ, h1.symm⟩
      have := ψ_step hlt hg
      have : (ψ J d : ℝ) + 1 ≤ ψ J d₀ := by exact_mod_cast this
      linarith

/-- **Up to the window end**: an offset whose image is at most the image of `dE + tE` lies at
most there in the walk of `C₁`. -/
theorem lex_le {d dE : ℕ} {t tE : ℝ} (hdE : GapOut J dE) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (htE0 : 0 ≤ tE) (htE1 : tE < 1) (h : (ψ J d : ℝ) + t ≤ ψ J dE + tE) :
    (d : ℝ) + t ≤ dE + tE := by
  by_contra hc
  push Not at hc
  have hdd : dE ≤ d := by
    have : (dE : ℝ) < d + 1 := by linarith
    exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)
  rcases eq_or_lt_of_le hdd with e | hlt
  · subst e; linarith
  · have := ψ_step hlt hdE
    have : (ψ J dE : ℝ) + 1 ≤ ψ J d := by exact_mod_cast this
    linarith

/-- **Up to the gap start.** -/
theorem lex_le_gap {d : ℕ} {t : ℝ} (hδ : 0 < lδ J)
    (hv2 : ¬ (0 < lδ J ∧ lL1 J < d ∧ d < lL1 J + lδ J)) (hv3 : ¬ (0 < lδ J ∧ d = lL1 J ∧ t ≠ 0))
    (ht0 : 0 ≤ t) (ht1 : t < 1) (h : (ψ J d : ℝ) + t ≤ lL1 J) :
    (d : ℝ) + t ≤ lL1 J ∨ (d = lL1 J + lδ J ∧ t = 0) := by
  by_cases h1 : d < lL1 J
  · left
    have : ((d + 1 : ℕ) : ℝ) ≤ lL1 J := by exact_mod_cast h1
    push_cast at this; linarith
  · by_cases h2 : d = lL1 J
    · left
      have t0 : t = 0 := by by_contra h'; exact hv3 ⟨hδ, h2, h'⟩
      rw [t0, h2]; simp
    · right
      have h3 : lL1 J + lδ J ≤ d := by
        by_contra h'; exact hv2 ⟨hδ, by omega, by omega⟩
      have hψ : ψ J d = d - lδ J := by
        unfold ψ; rw [ite_eq_left ⟨hδ, by omega⟩, ite_eq_right (by omega)]
      rw [hψ] at h
      have h4 : lL1 J ≤ d - lδ J := by omega
      have h5 : (lL1 J : ℝ) ≤ ((d - lδ J : ℕ) : ℝ) := by exact_mod_cast h4
      have t0 : t = 0 := by linarith
      refine ⟨?_, t0⟩
      subst t0
      have : ((d - lδ J : ℕ) : ℝ) ≤ lL1 J := by linarith
      have : d - lδ J ≤ lL1 J := by exact_mod_cast this
      omega

end Mono

/-- **The closed arc beyond a point of it**, in offsets from a base `g`: a point `y` beyond `x`
and not beyond the end `b` (or anywhere beyond `x` if the arc wraps past `g`). -/
theorem cIn_of_U {n g a b x y : ℝ} (hg0 : 0 ≤ g) (hgn : g < n) (han : a < n) (hb0 : 0 ≤ b)
    (hbn : b < n) (hx0 : 0 ≤ x) (hxn : x < n) (hy0 : 0 ≤ y) (hyn : y < n) (hab : a ≠ b)
    (hx : sideInArc a b x ∨ a = x) (hxy : off n g x < off n g y)
    (hyb : off n g y ≤ off n g b ∨ off n g b < off n g x) : CIn a b y := by
  have e1 := off_eq_sub (g := g) hx0 hyn hxy.le
  refine cIn_of_off han hb0 hbn hx0 hxn hy0 hyn hab hx (by linarith) ?_
  rcases hyb with h | h
  · rw [e1, off_eq_sub (g := g) hx0 hbn (by linarith)]; linarith
  · rw [e1, off_eq_sub' (g := g) hxn hb0 h]
    have := off_lt (g := g) hyn hg0
    have := off_nonneg (g := g) hb0 hgn
    linarith

/-! ## The arc after the key -/

section Arc

variable {C : Chain} {Q : Polygon} {N : NF}

theorem not_sia_end (a b : ℝ) : ¬ sideInArc a b b := by
  unfold sideInArc; split_ifs <;> intro h
  · linarith [h.2]
  · rcases h with h | h <;> linarith

/-- **The arc of a located key, if the key is not its end.** -/
theorem arc_of_loc {o : ℕ} {x : ℝ}
    (hne : (N.F (chainModel C) Q).Nonempty)
    (hl1 : ¬ (chainModel C).IsCut (N.F (chainModel C) Q) x →
      N.F (chainModel C) Q = ∅ ∨
        sideInArc (OracleQ.sk (chainModel C) Q N o) (OracleQ.ek (chainModel C) Q N o) x)
    (hl2 : (chainModel C).IsCut (N.F (chainModel C) Q) x →
      OracleQ.sk (chainModel C) Q N o = x ∨ OracleQ.ek (chainModel C) Q N o = x)
    (he : OracleQ.ek (chainModel C) Q N o ≠ x) :
    sideInArc (OracleQ.sk (chainModel C) Q N o) (OracleQ.ek (chainModel C) Q N o) x ∨
      OracleQ.sk (chainModel C) Q N o = x := by
  by_cases hc : (chainModel C).IsCut (N.F (chainModel C) Q) x
  · rcases hl2 hc with h | h
    · exact Or.inr h
    · exact absurd h he
  · rcases hl1 hc with h | h
    · exact absurd h hne.ne_empty
    · exact Or.inl h

/-- **The successor arc starts at the key** if the located arc ends there. -/
theorem arc_of_loc' (hP : C.P.Simple) (hN : IsNF (chainModel C) Q N) {o : ℕ}
    (ho : o < N.arcs.length) {x : ℝ} (hne : (N.F (chainModel C) Q).Nonempty)
    (he : OracleQ.ek (chainModel C) Q N o = x) :
    OracleQ.sk (chainModel C) Q N (OracleQ.succP N.arcs.length o) = x := by
  rw [← OracleQ.ek_eq_sk_succ hN hP hne ho, he]

end Arc

/-! ## The window ends -/

section End

variable {J : Merge.Junction} {P : Polygon}

theorem win_pos_eq_sidePt (M : Model) (Q : Polygon) (x : WPos) :
    M.pos Q x = sidePt M.W x.edge (M.param Q x) := rfl

theorem mvalid_half {d : ℕ} (hd : d < E₁ J) (hg : GapOut J d) : MValid J d (1 / 2) := by
  refine ⟨hd, fun h => ?_, fun h => ?_, fun h => absurd h (by norm_num)⟩
  · rcases hg h.1 with h' | h' <;> omega
  · rcases hg h.1 with h' | h' <;> omega

/-- **The window end at an arc end** of `N₁`: its image `(mEdge dE, hE)` in the walk of `C`. -/
theorem wend_map (hP : J.P.Simple) {dE eE hE : ℕ} (hdE : dE < E₁ J) (hg : GapOut J dE)
    (heE : (b₁ J + dE) % (chainModel J.left).W.n = eE)
    (hpp : ProperPos (chainModel J.left) (Qof P) P.n ⟨eE, hE⟩)
    (hy : |((chainModel J.left).pos (Qof P) ⟨eE, hE⟩).2| < J.left.radius) :
    PosW P J (mEdge J dE) hE ∧ offK P J (mEdge J dE) hE =
      (Lst J : ℝ) + ψ J dE + (chainModel J.left).param (Qof P) ⟨eE, hE⟩ := by
  have hv := mvalid_half hdE hg
  have hpar := param_corr hP hv (by norm_num) (Qof P) hE
  rw [heE] at hpar
  have hpt := edge_corr hP hv (by norm_num) ((chainModel J.left).param (Qof P) ⟨eE, hE⟩)
  rw [heE] at hpt
  have hm : mEdge J dE < (chainModel J.whole).W.n := by
    unfold mEdge; exact Nat.mod_lt _ (by have := win_gW_lt (J := J); omega)
  have hpp' : ProperPos (chainModel J.whole) (Qof P) P.n ⟨mEdge J dE, hE⟩ := by
    rw [ProperPos, hpar]; exact hpp
  refine ⟨posW_of_inner hm hpp' ?_, ?_⟩
  · rw [win_pos_eq_sidePt, hpar]
    simp only
    rw [hpt]
    exact hy
  · rw [win_offK_eq hm hpp', hpar]
    unfold mEdge
    rw [dOf_add_mod win_gW_lt (Lst_ψ_lt hP hdE)]
    push_cast; ring

theorem win_pred_mod {n b d e : ℕ} (hb : b < n) (hd : d < n) (h1 : 1 ≤ d) (he : (b + d) % n = e)
    (he0 : e ≠ 0) : (b + (d - 1)) % n + 1 = e := by
  by_cases h : b + d < n
  · rw [Nat.mod_eq_of_lt h] at he
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at he
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega

/-- **The cut witness of a window end at an arc end.** -/
theorem wend_cut {dE eE : ℕ} {tE : ℝ} {G : Set (Set Point)} (hdE : dE < E₁ J)
    (hheE : (b₁ J + dE) % (chainModel J.left).W.n = eE) (htE0 : 0 ≤ tE) (htE1 : tE ≤ 1)
    (hcut : (chainModel J.left).IsCut G ((eE : ℝ) + tE))
    (hg : GapOut J dE)
    (h0 : tE = 0 → 1 ≤ dE ∧ eE ≠ 0 ∧ (0 < lδ J → dE < lL1 J ∨ lL1 J + lδ J < dE))
    (hn₁ : dE < (chainModel J.left).W.n) :
    ∃ (d : ℕ) (t : ℝ), MValid J d t ∧ 0 ≤ t ∧ t ≤ 1 ∧
      (Lst J : ℝ) + ψ J dE + tE = (Lst J : ℝ) + ψ J d + t ∧
      (chainModel J.left).IsCut G (((b₁ J + d) % (chainModel J.left).W.n : ℕ) + t) := by
  rcases lt_or_eq_of_le htE0 with hpos | hz
  · refine ⟨dE, tE, ⟨hdE, fun h => ?_, fun h => ?_, fun h => absurd h hpos.ne'⟩, htE0, htE1,
      rfl, ?_⟩
    · rcases hg h.1 with h' | h' <;> omega
    · rcases hg h.1 with h' | h' <;> omega
    · rw [hheE]; exact hcut
  · obtain ⟨h1, he0, hg'⟩ := h0 hz.symm
    refine ⟨dE - 1, 1, ⟨by omega, fun h => ?_, fun h => ?_, fun h => absurd h one_ne_zero⟩,
      zero_le_one, le_rfl, ?_, ?_⟩
    · rcases hg' h.1 with h' | h' <;> omega
    · rcases hg' h.1 with h' | h' <;> omega
    · have : ψ J (dE - 1) + 1 = ψ J dE := by
        unfold ψ; split_ifs <;> omega
      rw [← hz, ← this]; push_cast; ring
    · rw [← hz, add_zero] at hcut
      have := win_pred_mod b₁_lt hn₁ h1 hheE he0
      rw [← this] at hcut; push_cast at hcut; exact hcut

/-- **The window end at the gap start.** -/
theorem wend_gap (hP : J.P.Simple) (hδ : 0 < lδ J) :
    PosW P J ((((gW J + Lst J) % (chainModel J.whole).W.n) + lL1 J) % (chainModel J.whole).W.n) 0 ∧
      offK P J ((((gW J + Lst J) % (chainModel J.whole).W.n) + lL1 J) %
        (chainModel J.whole).W.n) 0 = (Lst J : ℝ) + lL1 J := by
  obtain ⟨-, -, -, -, -, -, hlt, heq, hlt'⟩ := gap_facts hP hδ
  rw [Nat.mod_add_mod, add_assoc, heq]
  have hpp : ProperPos (chainModel J.whole) (Qof P) P.n
      ⟨6 + tpos J.whole (J.m₁ + 2 * J.m₂) + lL1 J, 0⟩ :=
    ⟨le_refl _, by simp [Model.param], Nat.zero_le _⟩
  refine ⟨⟨hlt', hpp, fun _ => by omega⟩, ?_⟩
  rw [win_offK_eq hlt' hpp, ← heq, dOf_add_mod win_gW_lt hlt]
  simp [Model.param]

/-- **The two ends of the gap are the same point** (the copies of the top of `C₁`). -/
theorem gap_pt (hP : J.P.Simple) (hδ : 0 < lδ J) :
    sidePt (chainModel J.left).W ((b₁ J + (lL1 J + lδ J)) % (chainModel J.left).W.n) 0 =
      sidePt (chainModel J.left).W ((b₁ J + lL1 J) % (chainModel J.left).W.n) 0 := by
  obtain ⟨-, h7, hl1, hb, hτp, hτl, -⟩ := gap_facts hP hδ
  have hn₁ := win_n₁_eq (J := J)
  have hm1 : J.left.m = J.m₁ := rfl
  rw [hb, hl1, h7, hn₁]
  rw [show 6 + tpos J.left J.m₁ + (2 * J.m₁ - tpos J.left J.m₁ + 7) = 6 + (2 * J.left.m + 7) by
      omega, Nat.add_mod_right, Nat.mod_eq_of_lt (show 6 < 2 * J.left.m + 7 by omega),
    show 6 + tpos J.left J.m₁ + (2 * J.m₁ - tpos J.left J.m₁) = 2 * J.left.m + 6 by omega,
    Nat.mod_eq_of_lt (show 2 * J.left.m + 6 < 2 * J.left.m + 7 by omega)]
  obtain ⟨a, b⟩ := sidePt_top_copies J.left
  rw [← hn₁] at *
  rw [a, b]

end End

/-! ## The gathered arcs -/

section Gath

/-- The arc list `l` is stored at `A` (normalised ends). -/
def Gath (M : Model) (Q : Polygon) (N : NF) (m : ℕ → ℕ) (A : ℕ) (l : List ℕ) : Prop :=
  ∀ k, k < l.length → ShotList.arcAt m A k = nArc M Q N (l.getD k 0)

theorem arc_mem_region {M : Model} {Q : Polygon} {N : NF} (hN : IsNF M Q N) {j : ℕ}
    (hj : j < N.arcs.length) : (N.arc j).reg < N.nRegions ∧ j ∈ (N.region (N.arc j).reg).arcs := by
  obtain ⟨-, -, -, reg, -, -, hA, -⟩ := hN
  have h1 := (hA.1 j hj).1
  exact ⟨h1, ((hA.2.2.2 _ h1 j).2 ⟨hj, rfl⟩)⟩

/-- **A point of a gathered arc is in `loSet`.** -/
theorem mem_loSet {M : Model} {Q : Polygon} {N : NF} {n' : ℕ} {m : ℕ → ℕ}
    {A : ℕ} {l : List ℕ} (hg : Gath M Q N m A l) (hl : ∀ a ∈ l, a < N.arcs.length)
    (hpp : ∀ j, j < N.arcs.length → ProperPos M Q n' (N.arc j).s ∧ ProperPos M Q n' (N.arc j).e)
    {a : ℕ} (ha : a ∈ l) {p : ℕ} {t : ℝ} (hp : p < M.W.n) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hc : CIn (M.key Q (N.arc a).s) (M.key Q (N.arc a).e) (p + t)) :
    sidePt M.W p t ∈ ShotList.loSet M Q m A l.length [] := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 ha
  have hkd : l.getD k 0 = l[k] := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl
  have hal := hl _ ha
  obtain ⟨hs, he⟩ := hpp _ hal
  refine ⟨p, t, hp, ht0, ht1, ⟨k, hk, ?_⟩, fun g hg' => absurd hg' (List.not_mem_nil), rfl⟩
  rw [hg k hk, hkd]
  unfold nArc
  simp only
  rw [(Restore.normOf_facts hs).2.2.2.1, (Restore.normOf_facts he).2.2.2.1]
  exact hc

end Gath

/-! ## Coverage -/

section Cover

variable {J : Merge.Junction} {P : Polygon} {N₁ : NF}

theorem key₁_range {M : Model} {Q : Polygon} {n' : ℕ} {x : WPos} (hx : x.edge < M.W.n)
    (hpp : ProperPos M Q n' x) : 0 ≤ M.key Q x ∧ M.key Q x < M.W.n := by
  unfold Model.key
  have h1 := hpp.1; have h2 := hpp.2.1
  have : ((x.edge + 1 : ℕ) : ℝ) ≤ M.W.n := by exact_mod_cast hx
  push_cast at this
  constructor <;> [positivity; linarith]

/-- **Coverage by the arc after the key.** -/
theorem cover_arc (hP : J.P.Simple) (hN : IsNF (chainModel J.left) (Qof P) N₁)
    {m : ℕ → ℕ} {A : ℕ} {l : List ℕ} (hg : Gath (chainModel J.left) (Qof P) N₁ m A l)
    (hl : ∀ a ∈ l, a < N₁.arcs.length) {o : ℕ} (ho : o < N₁.arcs.length)
    (hol : OracleQ.sj N₁ o ∈ l) {x : ℝ} (hx0 : 0 ≤ x) (hxn : x < (chainModel J.left).W.n)
    (hab : OracleQ.sk (chainModel J.left) (Qof P) N₁ o ≠ OracleQ.ek (chainModel J.left) (Qof P) N₁ o)
    (hin : sideInArc (OracleQ.sk (chainModel J.left) (Qof P) N₁ o)
        (OracleQ.ek (chainModel J.left) (Qof P) N₁ o) x ∨
      OracleQ.sk (chainModel J.left) (Qof P) N₁ o = x)
    {d : ℕ} {t : ℝ} (hd : d < E₁ J) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hlt : off (chainModel J.left).W.n (b₁ J) x < d + t)
    (hup : (d : ℝ) + t ≤ off (chainModel J.left).W.n (b₁ J)
        (OracleQ.ek (chainModel J.left) (Qof P) N₁ o) ∨
      off (chainModel J.left).W.n (b₁ J) (OracleQ.ek (chainModel J.left) (Qof P) N₁ o) <
        off (chainModel J.left).W.n (b₁ J) x) :
    sidePt (chainModel J.left).W ((b₁ J + d) % (chainModel J.left).W.n) t ∈
      ShotList.loSet (chainModel J.left) (Qof P) m A l.length [] := by
  set M := chainModel J.left with hM
  have hn₁ : 0 < M.W.n := by rw [hM, win_n₁_eq]; omega
  have hdn : d < M.W.n := lt_of_lt_of_le hd (E₁_le hP)
  have hpp : ∀ j, j < N₁.arcs.length → ProperPos M (Qof P) (Qof P).n (N₁.arc j).s ∧
      ProperPos M (Qof P) (Qof P).n (N₁.arc j).e := fun j hj => by
    obtain ⟨-, -, -, reg, -, -, -, -, -, -, h⟩ := hN; exact h j hj
  obtain ⟨reg, -, -, harc⟩ := OracleQ.isArc_sj hN ho
  obtain ⟨hs0, hsn, he0, hen, -⟩ := harc
  have hp := Nat.mod_lt (b₁ J + d) hn₁
  have hy : off M.W.n (b₁ J) (((b₁ J + d) % M.W.n : ℕ) + t) = d + t :=
    off_key b₁_lt hdn ht0 ht1
  have hyr : 0 ≤ (((b₁ J + d) % M.W.n : ℕ) : ℝ) + t ∧ (((b₁ J + d) % M.W.n : ℕ) : ℝ) + t < M.W.n := by
    have : (((b₁ J + d) % M.W.n + 1 : ℕ) : ℝ) ≤ M.W.n := by exact_mod_cast hp
    push_cast at this
    constructor <;> [positivity; linarith]
  have hb0 : (0 : ℝ) ≤ b₁ J := Nat.cast_nonneg _
  have hbn : (b₁ J : ℝ) < M.W.n := by exact_mod_cast b₁_lt
  refine mem_loSet hg hl hpp hol hp ht0 ht1.le ?_
  refine cIn_of_U hb0 hbn hsn he0 hen hx0 hxn hyr.1 hyr.2 hab hin (by rw [hy]; exact hlt) ?_
  rw [hy]; exact hup

end Cover

end

end SweepEv

end Chazelle.Core
