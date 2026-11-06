module

public import Chazelle.Core.SweepEvStopFin6
public import Chazelle.Core.SweepEvStopFin7B
public import Chazelle.Core.SweepEvStopFinS2
public import Chazelle.Core.SweepEvStopPar

/-!
# The sweep (WP-D), stage 2, the finish of a stop origin: the composition (`FinTask`)

`slfFin ps sl = slfOffs ; slfParS ps ; slfLabS sl ; slfEmits`: the offsets of `A₀`, `A₁` and the
anchor flag, the parent, the labels, and the emission of the raw records.  `finTask_of` from the
stretch labels (`StrLabTask`) and the emission (`SlfEmitsSpec`); `finTask` with `strLabTask` and
`slfEmits_spec`.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt rayPt_snd)

@[expose] public section

/-- **The finish of a stop origin.** -/
def slfFin (ps sl : Stmt) : Stmt := .seq slfOffs (.seq (slfParS ps) (.seq (slfLabS sl) slfEmits))

variable {P : Polygon} {W : ℕ} {c₀ c : Config} {J : Merge.Junction} {N₁ N₂ : NF}

/-- The registers of the code, the attachments and the raw array. -/
def SlfSafe (r : ℕ) : Prop := sw 4000 ≤ r ∧ r ≤ sw 4053

theorem slf_keep {R : ℕ → Prop} {c c' : Config} (h : SlfFr R c c')
    (hR : ∀ r, R r → ¬ SlfSafe r) {r : ℕ} (hr : SlfSafe r) : c'.nreg r = c.nreg r :=
  h.1 r (band_sw_not ⟨by unfold SlfSafe sw at hr; omega, by unfold SlfSafe sw at hr; omega⟩)
    (fun h' => hR r h' hr) (by unfold SlfSafe sw at hr; unfold ALLOC; omega)

theorem slfOffR_safe : ∀ r, slfOffR r → ¬ SlfSafe r := by
  intro r h h'; unfold slfOffR SlfSafe sw at *; omega

/-- The registers of the finish before the emission. -/
def SlfFinR (r : ℕ) : Prop := slfOffR r ∨ ParR r ∨ slfLabR r

theorem slfFinR_sorg : ∀ r, SlfFinR r → SOrgR r := by
  intro r h
  unfold SlfFinR slfOffR ParR slfLabR StrR FRR frA frB slfN slfL0 slfL1 slfP slfY oPar SOrgR gRC
    sw at *
  omega

/-- **Transfer of the post** from the start of the emission. -/
theorem orgOut_transfer {R : ℕ → Prop} {N : NF} {kind k b : ℕ} {c₃ c' : Config}
    (hR : ∀ r, R r → SOrgR r) (fr : SlfFr R c c₃)
    (hRB : c₃.nreg gRB = c.nreg gRB) (hRC : c₃.nreg gRC = c.nreg gRC)
    (h : OrgOut P J N kind k b c₃ c') : OrgOut P J N kind k b c c' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  rw [hRB, hRC] at *
  exact ⟨h1, h2, h3, h4, fun a ha hs => (h5 a (lt_of_lt_of_le ha fr.2.1) hs).trans (fr.2.2 a ha),
    fr.2.1.trans h6, fun r hb hs ha => (h7 r hb hs ha).trans (fr.1 r hb (fun hr => hs (hR r hr)) ha)⟩

/-- The cost bound. -/
theorem slf_cost {A B T Kp Ks Pc : ℕ} (hA : 1 ≤ A) (hB : T + 1 ≤ B) (hP : Pc ≤ Kp * A + 5) :
    44037 + (Pc + ((Ks * (T + 1) + 40) + 100)) ≤ (44200 + Kp + Ks) * A * B := by
  have hB1 : 1 ≤ B := by omega
  have h1 : 1 ≤ A * B := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have h2 : Kp * A ≤ Kp * A * B := Nat.le_mul_of_pos_right _ (by omega)
  have h3 : Ks * (T + 1) ≤ Ks * A * B := by
    calc Ks * (T + 1) ≤ Ks * B := Nat.mul_le_mul_left _ hB
      _ ≤ Ks * A * B := by
        rw [mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
  have h4 : 44200 ≤ 44200 * A * B := by
    rw [mul_assoc]; exact Nat.le_mul_of_pos_right _ (by omega)
  have e : (44200 + Kp + Ks) * A * B = 44200 * A * B + Kp * A * B + Ks * A * B := by ring
  rw [e]; omega

set_option maxHeartbeats 32000000 in
/-- **Task Fin** from the stretch labels and the emission. -/
theorem finTask_of (hS : StrLabTask) (hEm : SlfEmitsSpec) : FinTask := by
  obtain ⟨ps, κp, hps⟩ := parTask
  obtain ⟨sl, κs, hsl⟩ := strLabSpec_of hS
  refine ⟨slfFin ps sl, fun D => 44200 + κp + κs D, ?_⟩
  intro sh Bs F X Ok P W c₀ c J N₁ N₂ E hI hD hpre hgA hraw hroom
  have hP := E.hP
  have hN := E.hNF₂
  generalize hkd : c.nreg oKd = kind at *
  generalize hkk : c.nreg oKk = k at *
  generalize hkb : c.nreg oB = b at *
  obtain ⟨he0, hpp0, hA0, he1, hpp1, hA1, hpre2⟩ := hpre
  obtain ⟨-, -, hy, -, -⟩ := stOrig_facts hP hN hD.ok
  obtain ⟨i1, i2, -⟩ := orig_attach hP hN hD
  have hat₀ : SlfAtt P J (stopSet J (Qof P) N₂ kind k b) c (oF0 + 1) (oF0 + 2) := by
    have hpos : |((chainModel J.whole).pos (Qof P) ⟨c.nreg (oF0 + 1), c.nreg (oF0 + 2)⟩).2| <
        J.whole.radius := by rwa [pos_eq_sidePt', hA0.2.2.2.1]
    exact ⟨⟨he0, hpp0, fun h0 => h6_of_abs J.whole (Qof P) hpos h0⟩, hpos, (i1 _ _ hA0).1⟩
  have hat₁ : SlfAtt P J (stopSet J (Qof P) N₂ kind k b) c (a1F + 1) (a1F + 2) := by
    have hpos : |((chainModel J.whole).pos (Qof P) ⟨c.nreg (a1F + 1), c.nreg (a1F + 2)⟩).2| <
        J.whole.radius := by
      rw [pos_eq_sidePt', hA1.2.2.2.1]; unfold farPt; rwa [rayPt_snd]
    exact ⟨⟨he1, hpp1, fun h0 => h6_of_abs J.whole (Qof P) hpos h0⟩, hpos, (i2 _ _ hA1).1⟩
  obtain ⟨hbrk, hpk⟩ := anc_pocket_iff hP hN hD hA0 hA1
  -- the cost
  have hcost := slf_cost (A := if kind = 1 then 1 else N₁.nChords + N₂.nChords + 1)
    (B := F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1) (T := c₀.nreg TLR) (Kp := κp)
    (Ks := κs (c₀.nreg (sw 6)))
    (Pc := if kind = 1 then 5 else κp * (N₂.nChords + 1) + 4) (by split_ifs <;> omega)
    (by omega) (by
      split_ifs with h
      · omega
      · have := Nat.mul_le_mul_left κp (show N₂.nChords + 1 ≤ N₁.nChords + N₂.nChords + 1 by omega)
        omega)
  refine (?_ : IRS P W c₀ (slfFin ps sl) c (44037 + ((if kind = 1 then 5 else
    κp * (N₂.nChords + 1) + 4) + ((κs (c₀.nreg (sw 6)) * (c₀.nreg TLR + 1) + 40) + 100))) _).mono
    (by beta_reduce; exact hcost) (fun _ h => h)
  beta_reduce at hroom
  have hroom' : c.nreg ALLOC + (44037 + ((if kind = 1 then 5 else κp * (N₂.nChords + 1) + 4) +
      ((κs (c₀.nreg (sw 6)) * (c₀.nreg TLR + 1) + 40) + 100))) ≤ W := by
    have := hcost; omega
  unfold slfFin
  -- 1. the offsets
  refine IRS.seq (K₁ := 44037) (slfOffs_irs E hI hat₀.1 hat₁.1 (by omega)) ?_
  rintro c₁ hI₁ hA₁ hA₁' ⟨b0, b3, b4, b7, ha1, ha, fr1⟩
  have s1 : ∀ r, SlfSafe r → c₁.nreg r = c.nreg r := fun r hr => slf_keep fr1 slfOffR_safe hr
  have e1kd : c₁.nreg oKd = kind := by rw [s1 _ (by unfold SlfSafe oKd sw; omega), hkd]
  have e1kk : c₁.nreg oKk = k := by rw [s1 _ (by unfold SlfSafe oKk sw; omega), hkk]
  have e1kb : c₁.nreg oB = b := by rw [s1 _ (by unfold SlfSafe oB sw; omega), hkb]
  have e1pe : c₁.nreg pE2 = c.nreg pE2 := s1 _ (by unfold SlfSafe pE2 sw; omega)
  have e1ph : c₁.nreg pH2 = c.nreg pH2 := s1 _ (by unfold SlfSafe pH2 sw; omega)
  -- 2. the parent
  refine IRS.seq (K₁ := if kind = 1 then 5 else κp * (N₂.nChords + 1) + 4)
    ((slfPar_irs E hI₁ (fun c' hI' => hps sh Bs F X Ok P W c₀ c' J N₁ N₂ E hI')
      (by rwa [e1kd, e1kk, e1kb])
      (by rwa [e1kd, e1kk, e1kb, e1pe, e1ph])
      (fun _ => by split_ifs at hroom' <;> omega)).mono (by rw [e1kd]) (fun _ h => h)) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨hpar, fr2⟩
  rw [e1kd, e1kk, e1kb] at hpar
  have fr12 : SlfFr SlfFinR c c₂ :=
    (fr1.mono fun r h => Or.inl h).trans (fr2.mono fun r h => Or.inr (Or.inl h))
  have g2 : ∀ r, 240000 ≤ r → r < 250000 → ¬ SlfFinR r → c₂.nreg r = c.nreg r :=
    fun r h1 h2 h3 => fr12.1 r (band_sw_not ⟨h1, h2⟩) h3 (by unfold ALLOC; omega)
  have r01 := g2 (oF0 + 1) (by unfold oF0 sw; omega) (by unfold oF0 sw; omega)
    (by unfold SlfFinR slfOffR ParR slfLabR StrR FRR frA frB slfN slfL0 slfL1 slfP slfY oPar oF0 sw; omega)
  have r02 := g2 (oF0 + 2) (by unfold oF0 sw; omega) (by unfold oF0 sw; omega)
    (by unfold SlfFinR slfOffR ParR slfLabR StrR FRR frA frB slfN slfL0 slfL1 slfP slfY oPar oF0 sw; omega)
  have r11 := g2 (a1F + 1) (by unfold a1F sw; omega) (by unfold a1F sw; omega)
    (by unfold SlfFinR slfOffR ParR slfLabR StrR FRR frA frB slfN slfL0 slfL1 slfP slfY oPar a1F sw; omega)
  have r12 := g2 (a1F + 2) (by unfold a1F sw; omega) (by unfold a1F sw; omega)
    (by unfold SlfFinR slfOffR ParR slfLabR StrR FRR frA frB slfN slfL0 slfL1 slfP slfY oPar a1F sw; omega)
  have o0 := slfOff_congr (P := P) (J := J) r01 r02
  have o1 := slfOff_congr (P := P) (J := J) r11 r12
  have k21 : ∀ r, 240000 ≤ r → r < 250000 → ¬ ParR r → c₂.nreg r = c₁.nreg r :=
    fun r h1 h2 h3 => fr2.1 r (band_sw_not ⟨h1, h2⟩) h3 (by unfold ALLOC; omega)
  have eO : ∀ i, i ≤ 8 → c₂.nreg (slfO + i) = c₁.nreg (slfO + i) := fun i hi =>
    k21 _ (by unfold slfO sw; omega) (by unfold slfO sw; omega) (by unfold ParR oPar slfO sw; omega)
  have eA2 : c₂.nreg slfA = c₁.nreg slfA :=
    k21 _ (by unfold slfA sw; omega) (by unfold slfA sw; omega) (by unfold ParR oPar slfA sw; omega)
  -- 3. the labels
  refine IRS.seq (K₁ := κs (c₀.nreg (sw 6)) * (c₀.nreg TLR + 1) + 40)
    (slfLab_irs E hI₂ hsl hD (hat₀.congr r01 r02) (hat₁.congr r11 r12)
      (by rw [o0]; exact b0.of_eq (eO 0 (by norm_num)))
      (by rw [o0]; exact b3.of_eq (eO 3 (by norm_num)))
      (by rw [o1]; exact b7.of_eq (eO 7 (by norm_num)))
      (by rwa [eA2]) (by rwa [o0, o1, eA2])
      (fun h => by rw [o0, o1]; exact hpk.1 h) hpar (by omega)) ?_
  rintro c₃ hI₃ hA₃ hA₃' ⟨hlab, fr3⟩
  have fr13 : SlfFr SlfFinR c c₃ := fr12.trans (fr3.mono fun r h => Or.inr (Or.inr h))
  have g3 : ∀ r, 240000 ≤ r → r < 250000 → ¬ SlfFinR r → c₃.nreg r = c.nreg r :=
    fun r h1 h2 h3 => fr13.1 r (band_sw_not ⟨h1, h2⟩) h3 (by unfold ALLOC; omega)
  have k32 : ∀ r, 240000 ≤ r → r < 250000 → ¬ slfLabR r → c₃.nreg r = c₂.nreg r :=
    fun r h1 h2 h3 => fr3.1 r (band_sw_not ⟨h1, h2⟩) h3 (by unfold ALLOC; omega)
  have safe : ∀ r, SlfSafe r → ¬ SlfFinR r := fun r hr h => by
    unfold SlfSafe SlfFinR slfOffR ParR slfLabR StrR FRR frA frB slfN slfL0 slfL1 slfP slfY oPar
      sw at *
    omega
  have g3s : ∀ r, SlfSafe r → c₃.nreg r = c.nreg r := fun r hr =>
    g3 r (by unfold SlfSafe sw at hr; omega) (by unfold SlfSafe sw at hr; omega) (safe r hr)
  have e3kd : c₃.nreg oKd = kind := by rw [g3s _ (by unfold SlfSafe oKd sw; omega), hkd]
  have e3kk : c₃.nreg oKk = k := by rw [g3s _ (by unfold SlfSafe oKk sw; omega), hkk]
  have e3kb : c₃.nreg oB = b := by rw [g3s _ (by unfold SlfSafe oB sw; omega), hkb]
  have e3a : c₃.nreg (oF0 + 1) = c.nreg (oF0 + 1) := g3s _ (by unfold SlfSafe oF0 sw; omega)
  have e3b : c₃.nreg (oF0 + 2) = c.nreg (oF0 + 2) := g3s _ (by unfold SlfSafe oF0 sw; omega)
  have e3c : c₃.nreg (a1F + 1) = c.nreg (a1F + 1) := g3s _ (by unfold SlfSafe a1F sw; omega)
  have e3d : c₃.nreg (a1F + 2) = c.nreg (a1F + 2) := g3s _ (by unfold SlfSafe a1F sw; omega)
  have e3RB : c₃.nreg gRB = c.nreg gRB := g3s _ (by unfold SlfSafe gRB sw; omega)
  have e3RC : c₃.nreg gRC = c.nreg gRC := g3s _ (by unfold SlfSafe gRC sw; omega)
  have q0 := slfOff_congr (P := P) (J := J) e3a e3b
  have q1 := slfOff_congr (P := P) (J := J) e3c e3d
  have eO3 : ∀ i, i ≤ 8 → c₃.nreg (slfO + i) = c₁.nreg (slfO + i) := fun i hi => by
    rw [k32 _ (by unfold slfO sw; omega) (by unfold slfO sw; omega)
      (by unfold slfLabR StrR FRR frA frB slfN slfL0 slfL1 slfP slfY slfO sw; omega), eO i hi]
  have eA3 : c₃.nreg slfA = c₂.nreg slfA :=
    k32 _ (by unfold slfA sw; omega) (by unfold slfA sw; omega)
      (by unfold slfLabR StrR FRR frA frB slfN slfL0 slfL1 slfP slfY slfA sw; omega)
  have eP3 : c₃.nreg oPar = c₂.nreg oPar :=
    k32 _ (by unfold oPar sw; omega) (by unfold oPar sw; omega)
      (by unfold slfLabR StrR FRR frA frB slfN slfL0 slfL1 slfP slfY oPar sw; omega)
  -- 4. the emission
  have haux : (∃ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W
      (stopSet J (Qof P) N₂ kind k b) q s ∧ (Lst J : ℝ) ≤ oW J (q + s)) →
      AuxOK P J N₂ (stopSet J (Qof P) N₂ kind k b)
        (c₃.nreg slfA, c₃.nreg slfN, c₃.nreg slfL0, c₃.nreg slfL1, c₃.nreg oPar) := by
    intro hC1
    obtain ⟨n1, n2, n3, n4⟩ := hlab
    obtain ⟨p1, p2, p3⟩ := hpar
    rw [eA3, eA2, eP3]
    refine ⟨ha1, ?_, n1, n2, n3, fun h hnp => n4 (by rwa [eA2]) hnp hC1, p1, p2, p3⟩
    rw [ha, hbrk]; rfl
  refine (hEm sh Bs F X Ok P W c₀ c₃ J N₁ N₂ E hI₃ (by rwa [e3kd, e3kk, e3kb])
    (by rwa [e3kd, e3kk, e3kb, e3a, e3b]) (by rw [e3a, e3b]; exact hat₀.1)
    (by rwa [e3kd, e3kk, e3kb, e3c, e3d]) (by rw [e3c, e3d]; exact hat₁.1)
    (by rw [q0]; exact b0.of_eq (eO3 0 (by norm_num)))
    (by rw [q1]; exact b4.of_eq (eO3 4 (by norm_num)))
    (by rwa [e3kd, e3kk, e3kb]) (by rwa [e3RB])
    (by rw [e3RB, e3RC]; omega) (by omega)).mono le_rfl ?_
  intro c' h
  rw [e3kd, e3kk, e3kb] at h
  exact orgOut_transfer slfFinR_sorg fr13 e3RB e3RC h

/-- **Task Fin: the finish of a stop origin.** -/
theorem finTask : FinTask := finTask_of strLabTask slfEmits_spec

end

end SweepEv

end Chazelle.Core
