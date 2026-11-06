module

public import Chazelle.Core.ClusterPhase2

/-!
# WP-I, part 70: the second phase up to the flags

`phase2a_exec`: `regsS; stkS; driverStmt; flagS` from `PostD`: the driver ends with an empty
stack, and the flags `DF` then mark exactly `D ∪ H`, where `D` is the separator of the driver
and `H` the light levels; `|D| + |H| ≤ 7 k²`.
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs Chazelle.Separator Chazelle.Separator.CombMap

@[expose] public section

/-- The first part of the second phase. -/
def phase2a : Stmt := .seq regsS (.seq stkS (.seq driverStmt flagS))

/-- Its cost bound. -/
def cost2a (g : GV) : ℕ := (5 * g.L + 50) + ((20 * g.μ + 5) +
  ((120 * (g.L * g.μ) + splitC g.L g.k' * (2 * g.μ / g.s) + 2) + (14 * g.μ + 3)))

section proofs

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 16000000 in
theorem phase2a_exec {g : GV} {c : Config} (hw : WordsBounded W c) (hG : GR g c)
    {F : Type} [Fintype F] [DecidableEq F] {M : CombMap (Fin g.μ) F (Fin g.N)} {T : SpanTree M}
    {a : F → Fin g.N} {ha : ∀ f, M.face (a f) = f} {C : CoTree (starTree T a ha)} {R : BTree}
    {first : Fin g.μ → Fin g.N} {preE slot : ℕ → ℕ} {ρ : ℕ}
    (hD : PostD g M T a ha C R first preE slot ρ W c.nmem)
    (hk : 1 ≤ g.k) (hμ : 0 < g.μ) (hμk : g.μ ≤ g.k ^ 3) (hEND : g.END ≤ W) :
    ∃ c' k, Exec P W phase2a c c' k ∧ k ≤ cost2a g ∧ WordsBounded W c' ∧ GR g c' ∧
      (∀ r, ¬ (130000 ≤ r ∧ r < 131000) → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧
      (∀ a, (a < g.base 43 ∨ g.base 49 ≤ a) → c'.nmem a = c.nmem a) ∧
      ((Finset.range g.μ).filter (fun v => c'.nmem (g.base 48 + v) = 1)).card ≤ 7 * g.k ^ 2 ∧
      ∃ (H D : Finset ℕ) (fin : Finset (ℕ × ℕ)) (nsp : ℕ),
        (∃ act, SInv g.μ g.k' g.s H (slabN T (g.k' - 1 - ρ) g.k') (AdjN M) act [] fin D nsp) ∧
        ∀ v, v < g.μ → (c'.nmem (g.base 48 + v) = 1 ↔ v ∈ D ∨ v ∈ H) := by
  have hU := g.U_ge; have hE := g.END_eq
  have b43 := g.base_eq 43; have b46 := g.base_eq 46; have b48 := g.base_eq 48
  have b49 := g.base_eq 49; have b3 := g.base_eq 3; have b36 := g.base_eq 36
  have b0 := g.base_eq 0; have b29 := g.base_eq 29; have b35 := g.base_eq 35
  have b37 := g.base_eq 37; have b38 := g.base_eq 38; have b44 := g.base_eq 44
  have hk' : 0 < g.k' := by show 0 < min g.k g.μ; omega
  have hkμ : g.k' ≤ g.μ := min_le_right _ _
  have hs : 0 < g.s := by
    show 0 < min (g.k' * g.k') g.μ; have := Nat.mul_pos hk' hk'; omega
  have hP := g.two_pow_L
  set cs := g.k' - 1 - ρ with hcs
  unfold phase2a
  -- registers
  obtain ⟨c1, k1, e1, hk1, hw1, hR1, h704, hr1, hm1, hrr1, hrm1, ho1⟩ :=
    regsS_exec (P := P) hw hG hEND
  have hG1 : GR g c1 := hG.frame (fun r hr => hr1 r (by unfold GRReg at hr; unfold RegRG; omega))
  -- stack
  obtain ⟨c2, k2, e2, hk2, hw2, hf2, htp2, hstk2⟩ := stkS_exec (P := P) hw1 hG1
    (s := g.s) (bo := boOf g c.nmem) hR1.rs hR1.rSTK
    (fun b hb => by rw [hm1]; exact hD.cnt b hb) hEND
  have hR2 : (ssOf g).Regs c2 := hR1.of_frameR (fun r hr => hf2.1 r (by
    unfold RegsR at hr; unfold StkRG; omega))
  have hG2 : GR g c2 := hG1.frame (fun r hr => hf2.1 r (by unfold GRReg at hr; unfold StkRG; omega))
  have hst2 : StaticEq g.A0 g.U c.nmem c2.nmem := fun x hx => by
    rw [hf2.2.2.2.2 x (by omega), hm1]
  have k2m : ∀ x, ¬ (g.base 46 ≤ x ∧ x < g.base 46 + 2 * g.μ) → c2.nmem x = c.nmem x :=
    fun x hx => by rw [hf2.2.2.2.2 x hx, hm1]
  have hSF2 := hD.sf.of_static hst2
  -- the initial invariant
  have hlevc : ∀ w (hw : w < g.μ), c.nmem (g.base 3 + w) = T.level ⟨w, hw⟩ :=
    fun w hw => hD.sf.lev ⟨w, hw⟩
  have hlevlt : ∀ w, w < g.μ → c.nmem (g.base 3 + w) < g.μ := fun w hw => by
    rw [hlevc w hw]; exact hD.sf.lev_lt ⟨w, hw⟩
  have hbo2 : ∀ w, w < g.μ → boOf g c2.nmem w = boOf g c.nmem w := fun w hw => by
    have := hlevlt w hw
    simp only [boOf, blkOf]
    rw [k2m (g.base 3 + w) (by omega), k2m (g.base 36 + c.nmem (g.base 3 + w)) (by omega),
      k2m (g.base 35 + c.nmem (g.base 3 + w)) (by omega)]
  have hkey2 : ∀ w, w < g.μ → keyOf' g c2.nmem w = keyOf' g c.nmem w := fun w hw => by
    have := (hD.firstF w hw).1
    simp only [keyOf']
    rw [k2m (g.base 0 + w) (by omega), k2m (g.base 29 + c.nmem (g.base 0 + w)) (by omega)]
  have hstk' : segL g.s g.μ (boOf g c2.nmem) g.μ = stkList c2.nmem (g.base 46)
      (segL g.s g.μ (boOf g c2.nmem) g.μ).length := by
    rw [segL_congr hbo2]; exact hstk2
  have hlv2 : ∀ l, l < g.μ → LvOK g c2.nmem cs l := fun l hl => by
    obtain ⟨h1, h2, h3, h4⟩ := hD.lv l hl
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [k2m _ (by omega)]; exact h1
    · rw [k2m _ (by omega)]; exact h2
    · rw [k2m _ (by omega)]; exact h3
    · rw [k2m _ (by omega)]; exact h4
  have hpc : ∀ v, v < g.μ → plPos g.μ (boOf g c2.nmem) (keyOf' g c2.nmem) v =
      plPos g.μ (boOf g c.nmem) (keyOf' g c.nmem) v := fun v hv => plPos_congr hbo2 hkey2 hv
  have hI := dinv_init (W := W) hSF2 hD.head hk' (by omega) hkμ hlv2
    (fun v hv => by
      show c2.nmem (g.base 44 + v) = if boOf g c2.nmem v < g.μ then
        plPos g.μ (boOf g c2.nmem) (keyOf' g c2.nmem) v else g.μ
      rw [k2m _ (by omega), hD.pos v hv, hbo2 v hv, hpc v hv])
    (fun v hv hb => by
      show c2.nmem (g.base 43 + plPos g.μ (boOf g c2.nmem) (keyOf' g c2.nmem) v) = v
      change boOf g c2.nmem v < g.μ at hb
      rw [hbo2 v hv] at hb
      have := plPos_lt_μ (key := keyOf' g c.nmem) hv hb
      rw [hpc v hv, k2m _ (by omega)]; exact hD.act v hv hb)
    (fun v hv => by rw [k2m _ (by omega)]; exact hD.df v hv) hstk'
  have htp2' : c2.nreg 130701 = 2 * (segL g.s g.μ (boOf g c2.nmem) g.μ).length := by
    rw [segL_congr hbo2]; exact htp2
  have hnsp2 : c2.nreg 130704 = 0 := by rw [hf2.1 _ (by unfold StkRG; omega)]; exact h704
  -- the driver
  obtain ⟨c3, K, e3, hK, hw3, hR3, ⟨fin, D, nsp, hI3⟩, htp3, hst3, hr3, hrr3, hrm3, ho3⟩ :=
    driver_exec (P := P) hw2 hR2 hSF2 hI htp2' hnsp2 hk' hs
  have hG3 : GR g c3 := hG2.frame (fun r hr => hr3 r (by unfold GRReg at hr; unfold SplitRG; omega)
    (by unfold GRReg at hr; omega) (by unfold GRReg at hr; omega))
  have hst03 : StaticEq g.A0 g.U c.nmem c3.nmem := hst2.trans hst3
  have hsp : segPot (segL g.s g.μ (boOf g c2.nmem) g.μ) ≤ g.L * g.μ := by
    have x1 := segPot_segL (s := g.s) (μ := g.μ) (L := g.L) (bo := boOf g c2.nmem)
      (fun b => by have := cntBelow_le (boOf g c2.nmem) g.μ b; omega) g.μ
    have x2 := cntLt_le (boOf g c2.nmem) g.μ g.μ
    calc _ ≤ g.L * cntLt (boOf g c2.nmem) g.μ g.μ := x1
      _ ≤ g.L * g.μ := Nat.mul_le_mul_left _ x2
  -- the flags
  obtain ⟨c4, k4, e4, hk4, hw4, hf4, hdf4⟩ := flagS_exec (P := P) hw3 hG3
    (fun v hv => by rw [hst03 _ (by omega)]; exact hlevlt v hv) hEND
  have hG4 : GR g c4 := hG3.frame (fun r hr => hf4.1 r (by unfold GRReg at hr; unfold FlRG; omega))
  set H := Hset T cs g.k' with hH
  have hflag : ∀ v, v < g.μ → (c4.nmem (g.base 48 + v) = 1 ↔ v ∈ D ∨ v ∈ H) := fun v hv => by
    rw [hdf4 v hv, hst03 (g.base 3 + v) (by omega), hlevc v hv]
    have hl := hD.sf.lev_lt ⟨v, hv⟩
    obtain ⟨-, -, -, h36⟩ := hD.lv _ hl
    rw [hst03 (g.base 36 + T.level ⟨v, hv⟩) (by omega), h36]
    have hdf := hI3.df v hv
    have hmod := Nat.mod_lt (T.level ⟨v, hv⟩ + cs) hk'
    have hHv : v ∈ H ↔ (T.level ⟨v, hv⟩ + cs) % g.k' = g.k' - 1 := by
      simp only [hH, Hset, Finset.mem_filter, Finset.mem_range]
      exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨hv, hv, h⟩⟩
    rw [hHv]
    rw [show (ssOf g).bDF = g.base 48 from rfl] at hdf
    by_cases hm : (T.level ⟨v, hv⟩ + cs) % g.k' < g.k' - 1
    · rw [ite_eq_left hm, ite_eq_left (show (0 : ℕ) < 1 by norm_num), hdf]
      constructor
      · intro h; exact Or.inl h
      · rintro (h | h)
        · exact h
        · omega
    · rw [ite_eq_right hm, ite_eq_right (show ¬ (1 : ℕ) < 1 by norm_num)]
      simp only [true_iff]; right; omega
  -- the size of `D*`
  have hHcard : g.k' * H.card ≤ g.μ := by
    have e : H.card = cntBelow (fun v => c.nmem (g.base 3 + v) % g.k') g.μ ρ := by
      simp only [hH, Hset, cntBelow]
      congr 1
      refine Finset.filter_congr (fun v hv => ?_)
      have hv' := Finset.mem_range.mp hv
      rw [hlevc v hv']
      constructor
      · rintro ⟨_, h⟩; exact (mod_light hk' hD.ρ_lt).mp h
      · intro h; exact ⟨hv', (mod_light hk' hD.ρ_lt).mpr h⟩
    rw [e]
    exact minres_card hk' (fun v _ => Nat.mod_lt _ hk') hD.rmin
  have hDcard : g.s * D.card ≤ 6 * g.k' * g.μ := by
    have := hI3.sinv.pot; simp at this; exact this
  have hsub : (Finset.range g.μ).filter (fun v => c4.nmem (g.base 48 + v) = 1) ⊆ D ∪ H :=
    fun v hv => by
      simp only [Finset.mem_filter, Finset.mem_range] at hv
      rcases (hflag v hv.1).mp hv.2 with h | h
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ h
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le D H)
  have hb := dstar_bound (k := g.k) (k' := g.k') (s := g.s) hk hμ hμk rfl rfl hDcard hHcard
  refine ⟨c4, k1 + (k2 + (K + k4)), .seq e1 (.seq e2 (.seq e3 e4)), ?_, hw4, hG4,
    fun r hr => ?_, by rw [hf4.2.1, hrr3, hf2.2.1, hrr1], by rw [hf4.2.2.1, hrm3, hf2.2.2.1, hrm1],
    by rw [hf4.2.2.2.1, ho3, hf2.2.2.2.1, ho1], fun x hx => ?_, by omega,
    H, D, fin, nsp, ⟨_, hI3.sinv⟩, hflag⟩
  · unfold cost2a
    have hK' : K ≤ 120 * (g.L * g.μ) + splitC g.L g.k' * (2 * g.μ / g.s) + 2 :=
      le_trans hK (Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 120 hsp)
        (le_of_eq (by rw [Nat.sub_zero]; rfl))) 2)
    omega
  · rw [hf4.1 r (by unfold FlRG; omega), hr3 r (by unfold SplitRG; omega) (by omega) (by omega),
      hf2.1 r (by unfold StkRG; omega), hr1 r (by unfold RegRG; omega)]
  · rw [hf4.2.2.2.2 x (by omega)]; exact hst03 x (by omega)

end proofs

end

end Chazelle.Core.Cluster
