module

public import Chazelle.Core.SweepEvWinR3

/-!
# The sweep (WP-D), stage 3: the window of the event loop (mathematics of the post)

`win_math`: from the arc after the key (`BodyPost`) and the gathered arcs of its region, the
window facts of `WinOut`: the window end beyond the key (gap start or the image of a cut of `N₁`)
and the coverage of the valid offsets up to it by the gathered arcs.
-/

namespace Chazelle.Core

namespace SweepEv

open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep ShotList
open Chazelle.Chain (sideInArc sidePt SideAttach)

@[expose] public section

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c : Config} {J : Merge.Junction} {N₁ N₂ : NF}

theorem regArcs_single (N : NF) (r : ℕ) : regArcs N [r] = (N.region r).arcs := by
  simp [regArcs]

set_option maxHeartbeats 8000000 in
/-- **The mathematics of the window.** -/
theorem win_math (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) {e h : ℕ} (hpw : PosW P J e h)
    (hL : (Lst J : ℝ) ≤ offK P J e h) {o' : ℕ} (ho' : o' < N₁.arcs.length) {c' : Config}
    (hne : (N₁.F (chainModel J.left) (Qof P)).Nonempty →
      (sideInArc (OracleQ.sk (chainModel J.left) (Qof P) N₁ o')
          (OracleQ.ek (chainModel J.left) (Qof P) N₁ o') ((chainModel J.left).key (Qof P) ⟨ke₁ J e, h⟩) ∨
        OracleQ.sk (chainModel J.left) (Qof P) N₁ o' = (chainModel J.left).key (Qof P) ⟨ke₁ J e, h⟩) ∧
      DecOut J (U₁ P J (N₁.arc (OracleQ.sj N₁ o')).e < U₁ P J ⟨ke₁ J e, h⟩) (kd J e)
        (N₁.arc (OracleQ.sj N₁ o')).e.edge (N₁.arc (OracleQ.sj N₁ o')).e.hgt c')
    (hemp : N₁.F (chainModel J.left) (Qof P) = ∅ → c'.nreg wX = 1)
    (hg : Gath (chainModel J.left) (Qof P) N₁ c'.nmem (c'.nreg wGB)
      (regArcs N₁ [(N₁.arc (OracleQ.sj N₁ o')).reg])) :
    c'.nreg wX ≤ 1 ∧
    (c'.nreg wX = 0 → PosW P J (c'.nreg wE) (c'.nreg wH) ∧
      offK P J e h < offK P J (c'.nreg wE) (c'.nreg wH) ∧
      (offK P J (c'.nreg wE) (c'.nreg wH) = (Lst J : ℝ) + lL1 J ∨
        ∃ (d : ℕ) (t : ℝ), MValid J d t ∧ 0 ≤ t ∧ t ≤ 1 ∧
          offK P J (c'.nreg wE) (c'.nreg wH) = (Lst J : ℝ) + ψ J d + t ∧
          (chainModel J.left).IsCut (N₁.F (chainModel J.left) (Qof P))
            (((b₁ J + d) % (chainModel J.left).W.n : ℕ) + t))) ∧
    (∀ (d : ℕ) (t : ℝ), MValid J d t → 0 ≤ t → t < 1 →
      offK P J e h < (Lst J : ℝ) + ψ J d + t →
      (c'.nreg wX = 0 → (Lst J : ℝ) + ψ J d + t ≤ offK P J (c'.nreg wE) (c'.nreg wH)) →
      sidePt (chainModel J.left).W ((b₁ J + d) % (chainModel J.left).W.n) t ∈
        ShotList.loSet (chainModel J.left) (Qof P) c'.nmem (c'.nreg wGB)
          (regArcs N₁ [(N₁.arc (OracleQ.sj N₁ o')).reg]).length []) := by
  set M := chainModel J.left with hMd
  have hP : J.P.Simple := E.hP
  have hP₁ : J.left.P.Simple := E.hP
  have hNF := E.hNF₁
  set x₀ := M.key (Qof P) ⟨ke₁ J e, h⟩ with hx₀
  obtain ⟨hoff, hkdE, hgap0, hψ0, hm0, hv0, hpar, hpt⟩ := key_map hP hpw hL
  set t₀ := (chainModel J.whole).param (Qof P) ⟨e, h⟩ with ht₀
  have ht00 : 0 ≤ t₀ := hpw.2.1.1
  have ht01 : t₀ < 1 := hpw.2.1.2.1
  have hu0 : off M.W.n (b₁ J) x₀ = (kd J e : ℝ) + t₀ := key₁_off hP hpw hL
  have hoL : offK P J e h = (Lst J : ℝ) + ψ J (kd J e) + t₀ := by rw [hoff, hψ0]
  have hn₁ : 0 < M.W.n := by rw [hMd, win_n₁_eq]; omega
  have hke : ke₁ J e < M.W.n := Nat.mod_lt _ hn₁
  have hppx : ProperPos M (Qof P) P.n ⟨ke₁ J e, h⟩ := by
    refine ⟨?_, ?_, hpw.2.1.2.2⟩ <;> rw [hpar] <;> [exact ht00; exact ht01]
  have hxr := key₁_range (Q := Qof P) hke hppx
  set a := OracleQ.sj N₁ o' with ha
  have hal : a < N₁.arcs.length := NFLoc.seq_lt hNF ho'
  set l := regArcs N₁ [(N₁.arc a).reg] with hl
  obtain ⟨hreg, hmem⟩ := arc_mem_region hNF hal
  have hll : ∀ j ∈ l, j < N₁.arcs.length := by
    intro j hj
    rw [hl, regArcs_single] at hj
    obtain ⟨-, -, -, reg, -, -, hA, -⟩ := hNF
    exact ((hA.2.2.2 _ hreg j).1 hj).1
  have hol : a ∈ l := by rw [hl, regArcs_single]; exact hmem
  -- the valid offsets beyond the key are beyond it in the walk of `C₁`
  have hbeyond : ∀ (d : ℕ) (t : ℝ), MValid J d t → 0 ≤ t → t < 1 →
      offK P J e h < (Lst J : ℝ) + ψ J d + t → off M.W.n (b₁ J) x₀ < d + t := by
    intro d t hv ht0 ht1 hlt
    rw [hu0]
    rw [hoL] at hlt
    exact lex_lt hgap0 hv.2.1 hv.2.2.1 ht0 ht1 ht00 ht01 (by linarith)
  have hpp : ∀ j, j < N₁.arcs.length → ProperPos M (Qof P) (Qof P).n (N₁.arc j).s ∧
      ProperPos M (Qof P) (Qof P).n (N₁.arc j).e := fun j hj => by
    obtain ⟨-, -, -, reg, -, -, -, -, -, -, h⟩ := hNF; exact h j hj
  have hdn : ∀ d, d < E₁ J → d < M.W.n := fun d hd => lt_of_lt_of_le hd (E₁_le hP)
  by_cases hF : N₁.F M (Qof P) = ∅
  · -- the empty family: the arc covers the whole walk
    have hX := hemp hF
    refine ⟨by omega, fun h0 => by omega, fun d t hv ht0 ht1 _ _ => ?_⟩
    obtain ⟨reg, -, -, harc⟩ := OracleQ.isArc_sj hNF ho'
    have hab0 : OracleQ.sk M (Qof P) N₁ o' = 0 ∧ OracleQ.ek M (Qof P) N₁ o' = 0 := by
      rcases harc.2.2.2.2.1 with ⟨⟨c, hc, -⟩, -⟩ | ⟨-, h1, h2⟩
      · rw [hF] at hc; exact absurd hc (Set.notMem_empty c)
      · exact ⟨h1, h2⟩
    refine mem_loSet hg hll hpp hol (Nat.mod_lt _ hn₁) ht0 ht1.le ?_
    show CIn (OracleQ.sk M (Qof P) N₁ o') (OracleQ.ek M (Qof P) N₁ o') _
    rw [hab0.1, hab0.2]
    unfold CIn sideInArc
    rcases lt_trichotomy ((((b₁ J + d) % M.W.n : ℕ) : ℝ) + t) 0 with h' | h' | h'
    · left; rw [ite_eq_right (lt_irrefl 0)]; right; exact h'
    · right; left; exact h'
    · left; rw [ite_eq_right (lt_irrefl 0)]; left; exact h'
  have hFne : (N₁.F M (Qof P)).Nonempty := Set.nonempty_iff_ne_empty.2 hF
  obtain ⟨hin, hdec⟩ := hne hFne
  have hab := (OracleQ.arc_facts hNF hFne ho').2.2.1
  have hcutE := (OracleQ.arc_facts hNF hFne ho').2.1
  obtain ⟨-, ⟨hpe, hee, -⟩⟩ := arc_end_facts hP₁ hNF hal
  set eE := (N₁.arc a).e.edge with heEd
  set tE := M.param (Qof P) (N₁.arc a).e with htEd
  have htE0 : 0 ≤ tE := hpe.1
  have htE1 : tE < 1 := hpe.2.1
  set dE := dOf M.W.n (b₁ J) eE with hdEd
  have hUE : off M.W.n (b₁ J) (OracleQ.ek M (Qof P) N₁ o') = (dE : ℝ) + tE :=
    off_key' b₁_lt hee htE0 htE1
  have hUE' : U₁ P J (N₁.arc a).e = (dE : ℝ) + tE := hUE
  have hUx : U₁ P J ⟨ke₁ J e, h⟩ = (kd J e : ℝ) + t₀ := hu0
  have cov : ∀ (d : ℕ) (t : ℝ), d < E₁ J → 0 ≤ t → t < 1 → (kd J e : ℝ) + t₀ < d + t →
      ((d : ℝ) + t ≤ dE + tE ∨ (dE : ℝ) + tE < kd J e + t₀) →
      sidePt M.W ((b₁ J + d) % M.W.n) t ∈ ShotList.loSet M (Qof P) c'.nmem (c'.nreg wGB) l.length [] :=
    fun d t hd ht0 ht1 hlt hup => cover_arc hP hNF hg hll ho' hol hxr.1 hxr.2 hab hin hd ht0 ht1
      (by rw [hu0]; exact hlt) (by rw [hUE, hu0]; exact hup)
  rw [hUE', hUx] at hdec
  rcases hdec with ⟨hX, hc⟩ | ⟨hX, hnp, hδ, hd0, hl1d, hdE, hwE, hwH⟩ |
      ⟨hX, hnp, hncl, hdE, hwE, hwH⟩
  · -- part end
    rw [← hMd] at hc
    refine ⟨by omega, fun h0 => by omega, fun d t hv ht0 ht1 hlt _ => ?_⟩
    refine cov d t hv.1 ht0 ht1 (by rw [← hu0]; exact hbeyond d t hv ht0 ht1 hlt) ?_
    rcases hc with hp | hE
    · exact Or.inr hp
    · left
      have : d + 1 ≤ dE := by have := hv.1; omega
      have : ((d + 1 : ℕ) : ℝ) ≤ dE := by exact_mod_cast this
      push_cast at this; linarith
  · -- the gap start
    rw [← hMd] at hl1d hdE
    obtain ⟨hPW, hoffG⟩ := wend_gap (P := P) hP hδ
    have hψk : ψ J (kd J e) = kd J e := by unfold ψ; rw [ite_eq_right (by omega)]
    have hkl : (kd J e : ℝ) + t₀ < lL1 J := by
      have : ((kd J e + 1 : ℕ) : ℝ) ≤ lL1 J := by exact_mod_cast hd0
      push_cast at this; linarith
    have hlE : (lL1 J : ℝ) ≤ dE + tE := by
      have : (lL1 J : ℝ) ≤ dE := by exact_mod_cast hl1d
      linarith
    refine ⟨by omega, fun _ => ?_, fun d t hv ht0 ht1 hlt hle => ?_⟩
    · rw [hwE, hwH]
      refine ⟨hPW, ?_, Or.inl hoffG⟩
      rw [hoffG, hoL, hψk]; linarith
    · have hle' := hle hX
      rw [hwE, hwH, hoffG] at hle'
      have hb := hbeyond d t hv ht0 ht1 hlt
      rw [hu0] at hb
      rcases lex_le_gap hδ hv.2.1 hv.2.2.1 ht0 ht1 (by linarith) with h1 | ⟨h1, h2⟩
      · exact cov d t hv.1 ht0 ht1 hb (Or.inl (by linarith))
      · subst h1; subst h2
        rw [gap_pt hP hδ]
        exact cov (lL1 J) 0 (lt_of_le_of_lt hl1d hdE) le_rfl one_pos (by simpa using hkl)
          (Or.inl (by simpa using hlE))
  · -- an arc end
    rw [← hMd] at hncl hdE hwE
    have hne' : ¬ ((dE : ℝ) + tE = kd J e + t₀) := by
      intro heq
      have hk : M.key (Qof P) (N₁.arc a).e = x₀ := by
        have := key₁_range (Q := Qof P) hee hpe
        refine win_off_inj (g := (b₁ J : ℝ)) this.1 this.2 hxr.1 hxr.2 ?_
        rw [hu0]; exact hUE.trans heq
      rcases hin with h1 | h1
      · exact not_sia_end _ _ (show sideInArc _ (OracleQ.ek M (Qof P) N₁ o') (OracleQ.ek M (Qof P) N₁ o') by
          rw [show OracleQ.ek M (Qof P) N₁ o' = x₀ from hk] at h1 ⊢; exact h1)
      · exact hab (h1.trans hk.symm)
    have hlt0 : (kd J e : ℝ) + t₀ < dE + tE := lt_of_le_of_ne (not_lt.1 hnp) (Ne.symm hne')
    have hkdE : kd J e ≤ dE := by
      have : (kd J e : ℝ) < dE + 1 := by linarith
      exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)
    have hgE : GapOut J dE := by
      intro hδ
      by_cases h1 : dE < lL1 J
      · exact Or.inl h1
      · right
        have : ¬ kd J e < lL1 J := fun h2 => hncl ⟨hδ, h2, by omega⟩
        rcases hgap0 hδ with h3 | h3 <;> omega
    have hψE : (if dE < lL1 J + lδ J then dE else dE - lδ J) = ψ J dE := by
      unfold ψ
      rcases win_lδ_cases (J := J) with h7 | h7
      · split_ifs <;> omega
      · have := hgE (by omega)
        split_ifs <;> omega
    have hwE' : c'.nreg wE = mEdge J dE := by
      rw [hwE, hψE]; unfold mEdge; rw [Nat.mod_add_mod, add_assoc]
    have heE : (b₁ J + dE) % M.W.n = eE := add_dOf b₁_lt hee
    have hy := (Restore.arc_abs_lt hP₁ hNF hFne hal).2
    obtain ⟨hPW, hoffE⟩ := wend_map (P := P) hP hdE hgE heE hpe hy
    refine ⟨by omega, fun _ => ?_, fun d t hv ht0 ht1 hlt hle => ?_⟩
    · rw [hwE', hwH]
      refine ⟨hPW, ?_, Or.inr ?_⟩
      · rw [hoffE, hoL]
        rcases eq_or_lt_of_le hkdE with h1 | h1
        · rw [h1] at hlt0 ⊢; linarith
        · have := ψ_step h1 hgap0
          have : (ψ J (kd J e) : ℝ) + 1 ≤ ψ J dE := by exact_mod_cast this
          linarith
      · rw [hoffE]
        refine wend_cut hdE heE htE0 htE1.le hcutE hgE (fun h0' => have h0 : tE = 0 := h0'; ⟨?_, ?_, ?_⟩) (hdn _ hdE)
        · have : (kd J e : ℝ) + t₀ < dE := by rw [h0] at hlt0; simpa using hlt0
          have : (0 : ℝ) < dE := by have := (Nat.cast_nonneg (kd J e) : (0 : ℝ) ≤ _); linarith
          exact_mod_cast this
        · intro he0
          have hpos : M.pos (Qof P) (N₁.arc a).e = M.W.vtx eE := by
            rw [win_pos_eq_sidePt, ← htEd, h0]; exact Chazelle.Chain.sidePt_zero _ _
          rw [hpos, he0, Restore.chain_box_vtx_abs J.left (by norm_num)] at hy
          exact lt_irrefl _ hy
        · intro hδ
          by_cases h1 : dE < lL1 J
          · exact Or.inl h1
          · right
            have : ¬ kd J e < lL1 J := fun h2 => hncl ⟨hδ, h2, by omega⟩
            have h3 : lL1 J + lδ J ≤ kd J e := by rcases hgap0 hδ with h3 | h3 <;> omega
            have : (kd J e : ℝ) < dE := by rw [h0] at hlt0; linarith
            have : kd J e < dE := by exact_mod_cast this
            omega
    · have hle' := hle hX
      rw [hwE', hwH, hoffE] at hle'
      have hb := hbeyond d t hv ht0 ht1 hlt
      rw [hu0] at hb
      exact cov d t hv.1 ht0 ht1 hb (Or.inl (lex_le hgE ht0 ht1 htE0 htE1 (by linarith)))


end

end SweepEv

end Chazelle.Core
