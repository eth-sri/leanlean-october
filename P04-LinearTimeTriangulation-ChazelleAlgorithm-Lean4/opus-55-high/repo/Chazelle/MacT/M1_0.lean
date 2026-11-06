module

public import Chazelle.MacT.Base
public import Chazelle.MacT.M0_0
public import Chazelle.MacT.M0_1
public import Chazelle.MacT.M0_2
public import Chazelle.MacT.M0_3
public import Chazelle.MacT.M0_4
public import Chazelle.MacT.M0_5
public import Chazelle.MacT.M0_6
public import Chazelle.MacT.M0_7
public import Chazelle.MacT.M0_8
public import Chazelle.MacT.M0_9
public import Chazelle.MacT.M0_10
public import Chazelle.MacT.M0_11
public import Chazelle.MacT.M0_12
public import Chazelle.MacT.M0_13
public import Chazelle.MacT.M0_14
public import Chazelle.MacT.M0_15
public import Chazelle.MacT.M0_16
public import Chazelle.MacT.M0_17
public import Chazelle.MacT.M0_18
public import Chazelle.MacT.M0_19
public import Chazelle.MacT.M0_20
public import Chazelle.MacT.M0_21
public import Chazelle.MacT.M0_22
public import Chazelle.MacT.M0_23
public import Chazelle.MacT.M0_24
public import Chazelle.MacT.M0_25
public import Chazelle.MacT.M0_26
public import Chazelle.MacT.M0_27
public import Chazelle.MacT.M0_28
public import Chazelle.MacT.M0_29
public import Chazelle.MacT.M0_30

public section

set_option hygiene false

zn ztbh (Or.inr by_omega)
ztcv (Nat.mod_lt _ by_omega)
ztec (Or.inl by_omega)
zteh ⟨by_omega, ?_⟩
ztfm ⟨by_norm_num, by_norm_num⟩
ztgq ⟨fun r hr => ?_, by_simp_all, rfl, rfl, rfl⟩
ztgy ⟨by_omega, by_omega⟩
ztkp ⟨by_decide, by_decide⟩
ztmg (nk _ by_norm_num by_norm_num)
ztmr (not_oracle_sw by_decide by_decide)
ztnm (nk _ by_omega by_omega)
ztpy (ir _ by_omega by_omega)
ztpz (n1 _ by_decide by_decide)
ztqd ⟨by_omega, by rw [hl]; simp [addL, heq], fun _ _ => rfl, rfl⟩
ztrg ⟨fun r hr => ?_, rfl, rfl, rfl, by_simp_all⟩
ztsr ⟨by_grind, by_grind⟩
ztss ⟨by_omega, ?_, ?_⟩
ztwa (ir _ by_norm_num by_norm_num)
ztxl (fun a ha => by_grind)
ztzw ⟨by_omega, ?_, fun r hr => by simp [hr]⟩
ztzz (Or.inl by_grind)
ztbay (fun h => by_grind)
ztbbi ⟨DrvD.mem_drvBands by_omega by_omega, by unfold ALLOC; omega⟩
ztbbk ⟨by_grind, ?_⟩
ztbbp (Exec.constN hw _ _ by_omega)
ztbcd ⟨by_omega, ?_, rfl⟩
ztbci ⟨rfl, by_linarith, by_linarith⟩
ztbcx ⟨by_linarith, by_linarith⟩
ztbcz (Or.inr by_decide)
ztbdg (k1 _ by_omega by_omega)
ztbeo (fun i _ => by_omega)
ztbeq (keepR_of by_decide)
ztbet (not_oracle_sw by_omega by_omega)
ztbfj ⟨by_omega, ?_, ?_, ?_, ?_, ?_⟩
ztbfk ⟨by_omega, ?_, by_simp_all⟩
ztbgh ⟨mem_drvBands by_omega by_omega, by unfold ALLOC; omega⟩
ztbhe ⟨_, _, e, by_omega, 0, by_norm_num, rfl, zero ?_⟩
ztbhf ⟨by rw [hm _ by_omega]; exact h.1, fun i hi => ?_⟩
ztbif ⟨c', k, ex, hk, q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2, exec_frameB ex by_decide⟩
ztbjp (ne_of_mem_of_not_mem hr by_decide)
ztbjq (ne_of_wr hw (wr_sw by_norm_num by_norm_num))
ztbjx ⟨_, _, e, by_omega, 1, le_rfl, rfl, by_simp_all⟩
ztbjy ⟨by_simp_all, ?_⟩
ztbka ⟨c, 2, .whileLtN_false ht by_grind, hc, ht, by_omega, by_omega⟩
ztbkz ⟨c', k₁ + 2 + k₂, .whileLtN_true ht hb hl, hI', ht', by_omega, by_omega⟩
ztbls (Bgap_false by_omega)
ztbmd (Or.inr by_grind)
ztbmi (by rw [s8 _ by_decide]; omega)
ztbmx (fun i hi => by_grind)
ztbna (k2 _ by_omega)
ztbnx ⟨by_simp_all, ?_, ?_⟩
ztbny ⟨c', k, ex, hk, q.1, q.2.1, q.2.2.1, q.2.2.2, exec_frameB ex by_decide⟩
ztbod ⟨v50, v51, v52, v53, v54, fun h => by_tauto⟩
ztbot ⟨le_refl _, by_simp_all, fun r hr => ?_, rfl, rfl, rfl, ?_⟩
ztbpw (by rw [v₀, g₀ _ by_norm_num, hN]; omega)
ztbrc ⟨⟨2, 1, by_omega, by_omega, ?_, ?_⟩, ⟨1, 3, by_omega, by_omega, ?_, ?_⟩⟩
ztbsi (by rw [c75 _ by_decide (by unfold CovRG AscRG; decide)]; omega)
ztbtg ⟨p - 6, by_omega⟩
ztbua (iscr_sw by_decide by_decide)
ztbuo (Or.inl by_decide)
ztbur (band_sw_not by_decide)
ztbvq (by rw [g₇ _ by_omega, q03])
ztbvs (by rw [r₁ _ by_decide by_decide by_decide])
ztbxn (.ifLtN_true by_omega e₂)
ztbyj (IRS.ifF by_omega ?_)
ztcbn ⟨by_omega, ?_, ?_, ?_⟩
ztcbo ⟨by_omega, ?_, rfl, rfl, rfl, rfl⟩
ztcdi (k4 _ by_omega by_omega)
ztcfo ⟨by rw [hp0], by_simp, Nat.zero_le _⟩
ztcfp ⟨by_omega, ?_, fun r hr => by simp [hr], rfl, rfl, rfl, rfl⟩
ztcgp (BZB_keep (Or.inr by_norm_num))
ztcgx (Or.inl ⟨by_norm_num, by_norm_num⟩)
ztcgy (Or.inr by_simp_all)
ztcid (fun u hu => by_simp_all)
ztcil (hS _ by_decide r hr)
ztcis (kr _ by_decide by_decide by_decide)
ztcjq ⟨c', _, by_omega, .ifLtN_false h e, by_simp_all, o⟩
ztclp (IRS.ifF by_omega (IRS.skip hI₁ rfl))
ztclu (RS.ifT by_omega (leaf_skip hI ?_))
ztcmg (by rw [k4' _ by_omega]; omega)
ztcns (keep₂ _ by_norm_num by_norm_num)
ztcot ⟨by_omega, ?_, ?_, ?_, rfl⟩
ztcou ⟨c', k + 1, .ifLtN_true ht ex, by_omega, hI, hrf.mono subset_rfl by_omega, hq⟩
ztcov ⟨c', k + 2, .ifLtN_false ht ex, by_omega, hI, hrf.mono subset_rfl by_omega, hq⟩
ztcox ⟨e', k, ex, ⟨j + 1, hI'⟩, RF', by_omega, by_omega⟩
ztcpl (by rw [Y.gn]; exact sig_lt li by_omega _ _)
ztcqb (s3.mono by_simp)
ztcqk ⟨by_omega, ?_, ?_, fun r h1 h2 => ?_⟩
ztcqx ⟨c', k₁ + k₂, .seq e₁ e₂, by_omega, hI', hrf₁.trans hrf₂, hq⟩
ztcry (.ifLtN_false by_omega e₂)
ztcrz (.ifLtN_true by_omega ex)
ztcta (Exec.constN w₁ _ _ by_omega)
ztcvp (fun r hr => by_simp_all)
ztcvx (k3 _ by_omega)
ztcwa (ne _ by_trivial)
ztcxm ⟨by_omega, ?_, fun r hr => ?_, rfl⟩
ztcxo ⟨by_omega, fun a ha => ?_, ?_, by_omega⟩
ztcxp ⟨by_omega, fun q hq => ?_, ?_, ?_⟩
ztcxq ⟨c', k1 + k, .seq e1 e, by_omega, hw', hf', hm'⟩
ztcxy ⟨h - 1, by_omega⟩
ztcyb ⟨hc, z, hz, hzD, hzU, by_grind⟩
ztczk (fun h => by_omega)
ztczq (g₁ _ by_omega by_omega)
ztdby (Or.inr (Or.inl ⟨le_refl _, by_omega⟩))
ztdce (by rw [cr' _ by_omega by_omega]; omega)
ztdcf (by rw [cr'' _ by_omega by_omega]; omega)
ztdda (fun r h1 h2 => r₁ r by_omega by_omega by_omega)
ztddf (not_pairRG by_omega)
ztddg (s2.mono by_simp)
ztddt ⟨_, rfl, by_grind, hpp _, by_grind⟩
ztdfp (IRS.ifT by_omega ?_)
ztdfv (Nat.mul_le_mul_left _ by_omega)
ztdgs (by intro h; rw [h] at hr; exact absurd hr by_decide)
ztdhk (hI.hin _ by_trivial)
ztdiv ⟨?_, by_omega⟩
ztdix ⟨by_omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
ztdiy ⟨by_omega, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
ztdiz ⟨c, 2, .whileLtN_false by_omega hI.wb, by_omega, by_omega, hI, by_omega⟩
ztdjb ⟨d', k, e, by_omega, exec_frameB e by_decide, v1, v2⟩
ztdjc ⟨d', k, e, hw', hI', by_omega, ?_, ?_⟩
ztdjd ⟨d', k, ex, hk, h1, hm, exec_frameM ex by_decide⟩
ztdje ⟨e₁ + 1, 2 * C.m + 5, ?_, ?_, ?_, by_omega, by_omega, ?_, fun _ => ?_, fun h => ?_⟩
ztdjf ⟨le_of_eq rfl, by_simp, Nat.zero_le _⟩
ztdjl ⟨c', _, .seq e₀ e, by_omega, I'.env, I'.vbG, I'.vbn, fun v h1 h2 => I'.cov v ?_, f', y', m'⟩
ztdls (by rw [cmA _ by_omega]; grind)
ztdlu (by rw [g₇ _ by_omega, d₂])
ztdly (by rw [h]; exact getD_mem_of_lt by_omega)
ztdma (by rw [kEq _ by_decide, kXq _ by_decide by_decide]; omega)
ztdod (fun r a b => hr r a by_simp_all)
ztdop (g₂ 50201 by_norm_num by_norm_num)
ztdox (lerp_mem_segment _ _ by_norm_num by_norm_num)
ztdoy (nO _ by_decide by_decide)
ztdqe ⟨6, 2 * C.m + 5, ?_, ?_, ?_, by_omega, by_omega, ?_, fun _ => ?_, fun h => ?_⟩
ztdqf ⟨?_, by_omega, rfl⟩
ztdqh ⟨_, _, .seq e₁ (.seq e₂ (.ifLtN_true hb e₃)), by_omega, ?_, fun r h1 h2 h3 => ?_, ?_⟩
ztdqi ⟨by_omega, ?_, ?_, fun x hx1 hx2 => ?_, rfl⟩
ztdqj ⟨by_omega, ?_, ?_, rfl, fun r h1 h2 => ?_⟩
ztdqr ⟨hc - 1, by_omega⟩
ztdqt ⟨p + n, by_simp, by rw [Nat.add_mod_right, Nat.mod_eq_of_lt hp]⟩
ztdqx ⟨rfl, ?_, ?_, by_simp_all, rfl⟩
ztdrb ⟨by_omega, ?_, ?_, fun r hr => ?_, fun r h1 h2 => ?_, ?_, rfl, rfl, rfl, rfl⟩
ztdrc ⟨by_omega, ?_, fun v hv => ?_, fun r h1 h2 => ?_, hfr, fun t ht' => ?_, hrm, hout⟩
ztdrw (.ifLtN_false by_omega ex)
ztdrx (.ifLtN_true by_omega e)
ztdtu (bandOK_l41 by_omega by_omega)
ztdtz (by rw [f₂.1 _ by_decide, q20, hE₂.r32]; omega)
ztduj (exec_frameB e₁ by_decide)
ztduk (exec_frameB e₃ by_decide)
ztduz (iB _ by_omega)
ztdvl (mq _ by_omega)
ztdwy ⟨?_, by_simp_all⟩
ztdwz ⟨_, _, ex, by_omega, exec_frameB ex by_decide, ?_⟩
ztdxc ⟨by_omega, ?_, fun r h1 h2 h3 => ?_, rfl⟩
ztdxd ⟨c', _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e')))), by_omega, s'⟩
ztdxe ⟨c', k, ex, by_omega, ?_, hI.prim ex.wb_right hf'⟩
ztdxh ⟨fun r hr => ?_, by_simp_all, by_simp_all, rfl, rfl⟩
zteah (kW by_omega)
ztear (s4.mono by_simp)
zteba ⟨cT, _, by_omega, ex, t09, ?_, ?_, ?_, ?_, t1415, (o113.trans oT).mono ?_⟩
ztecb (by rw [c4c _ by_decide by_decide by_decide by_decide]; omega)
ztedo ⟨by_omega, ?_, rfl, fun r h1 h2 => ?_⟩
ztedp ⟨c', k1 + (1 + k), .seq x1 (.seq e2 e), by_omega, hw', hf', hm'⟩
ztedq ⟨c₃, _, .seq e₁ (.seq e₂ (.ifLtN_false g1 (.ifLtN_false g2 e₃))), by_omega, best₃, ?_⟩
ztedy ⟨r₁, rr₁, fun a ha => m₁ a by_omega, fun a ha => rm₁ a by_omega, o₁, a₁, b₁⟩
ztefd (f₁ _ by_decide by_decide)
ztejp (.ifLtN_false by_omega e)
ztejy (.seq e₂ (.ifLtN_false by_omega e₃))
ztemn (Exec.constN ‹_› _ _ by_omega)
ztenq (Or.inr ⟨k, hk, rfl, a', b', harc, hsub k (Nat.cast_nonneg k) by_simp_all hkin⟩)
zteod (Same.upd1 by_simp)
ztepf (band_ne by_norm_num by_norm_num)
zteps (by rintro rfl; exact ho by_decide)
ztept (by rintro rfl; exact hr by_decide)
ztepv (by rw [fr3 _ by_decide by_decide by_decide]; omega)
ztepw (by rw [h, band8 by_norm_num by_norm_num]; decide)
ztesd (fun _ => x_mono (x_skipR d1 hw1 dst) by_omega)
ztese (fun a ha => by_simp_all)
ztesm (fun h => band9_not by_omega by_omega hr)
ztetf (hr _ by_tauto)
ztevi (scr_out by_norm_num by_norm_num)
ztevs (spec_skip hw by_simp_all)
ztexr ⟨by_grind, fun i hi => ?_⟩
ztexs ⟨by_norm_num, hb, by_omega, by_omega⟩
ztext ⟨by_omega, ?_, by_simp_all, rfl⟩
ztexu ⟨by_omega, ?_, fun r' h1' h2' h3' => ?_⟩
ztexv ⟨by_omega, hlax, fun i hi => ?_, fun i hi => ?_, h5, h6, h7, h8⟩
ztexz ⟨c, hcF, p, t, by_simp_all, rfl⟩
zteye ⟨c₁₃, _, by_omega, .ifLtN_true g1 (.skip hW13), ?_, fun h => ?_, Out.refl _ _⟩
zteyt ⟨p, t, hp, h0, h1, ⟨X, by_linarith, hX2, j, hj⟩, rfl⟩
ztezr (by rw [v₁, r₁ _ by_decide, hq.twoM, hv.m]; rw [hv.m] at hE; omega)
ztfag ⟨_, _, .ifLtN_false a0 (.ifLtN_false a2 (.ifLtN_true b0 ex)), by_norm_num, bt, fr 0⟩
ztfbo (by rw [o₈.1 _ by_simp, o₇.1 _ by_simp, q113, o18.1 _ by_simp, h23]; omega)
ztfdc ⟨c', k, e, by_grind, RF', hk, by rw [I.r10, I'.r10]; omega⟩
ztfde ⟨d - 1, by_omega, 1 - s, ⟨by_linarith, by_grind⟩, ?_, ?_, ?_⟩
ztfdg ⟨e₂, k₂, ex₂, hk₂, w40, w41, w42, w43, m₂, exec_frameM ex₂ by_decide⟩
ztfdi ⟨hu, by_omega, by rw [ch_m]; omega, ch_P, hD, hn, by_omega, hA⟩
ztffg (Bpass_false by_omega)
ztfhh (fun _ => x_ifR (fun _ => s0 5 by_omega) (fun _ => s1 5 by_omega))
ztfhi (fun i a b => by_simp_all)
ztfij (rs[i]' by_omega)
ztfjs ⟨?_, ?_, fun a ha => ?_, by_omega, fun r h1 h2 h3 h4 => ?_⟩
ztfjw ⟨c'', k + 2 + k₂, .whileLtN_true by_omega e e₂, by_omega, by_omega, hI'', hK⟩
ztfjy ⟨gR' _ by_omega by_omega, z3⟩
ztfkf ⟨⟨Qof P, _, _, gradeLen_pos hn by_omega, by_omega⟩, rfl, rfl, rfl⟩
ztfph (by rw [K₂ _ by_decide]; omega)
ztfps (by rw [show fb 4 = 60104 from rfl, hR1.b 4 by_norm_num, r40]; omega)
ztfpt (by rw [show fb 6 = 60106 from rfl, hR.b 6 by_norm_num, h20]; omega)
ztfrh (fun _ => by_grind)
ztfrw (f₆.1 _ by_decide)
ztfsw (k1 _ by_omega)
ztfvu ⟨(hsf x by_grind hxl).1, hxF⟩
ztfvy ⟨by_omega, hgap r, hsplit r, ?_⟩
ztfvz ⟨c', k, ex, by_nlinarith, r', rr', mm, rm, o, J'⟩
ztfwb ⟨c, 2, .whileLtN_false ht hI.hw, by_omega, hI, IFr.refl c 2, hc, ht⟩
ztfwc ⟨c, 2, .whileLtN_false ht hI.hw, by_omega, hI, RF.refl c 2, hc, ht⟩
ztfwd ⟨c₃, _, ex, by_omega, v₃, exec_frameB ex wr_gamS, fun r hr => ?_⟩
ztfwf ⟨c₈, _, by_omega, ex, ?_, ?_, ?_, ?_, ?_, ?_⟩
ztfwg ⟨d, hd, t + s, ⟨by_grind, hs3⟩, ?_, by_simp_all, by_simp_all⟩
ztfws ⟨iscrT, by_omega⟩
ztfyg (fun r h1 h2 => (k₁' r by_omega by_omega).trans (hk0 r h1 h2))
ztfza ⟨_, _, .ifLtN_false a0 (.ifLtN_true a2 ex), by_norm_num, bt, fr 0⟩
ztfzb ⟨_, _, .ifLtN_true a0 (.ifLtN_false b0 ex), by_norm_num, bt, fr 1⟩
ztfzc ⟨_, _, .ifLtN_true a0 (.ifLtN_true b0 ex), by_norm_num, bt, fr 0⟩
ztfzd ⟨by_omega, ?_, ?_, ?_, rfl, fun r h1 h2 h3 h4 => ?_⟩
ztfze ⟨by_omega, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
ztfzg ⟨c₄, _, ex, by_omega, ?_, hI.prim ex.wb_right (frame_of_frameB hfr Bturn_band _)⟩
ztgbl ((param_eq_zero_iff _ _ _).2 by_grind)
ztgdg (Bkb_bedge by_decide)
ztgew (X.local_ _ _ _ _ _ by_simp_all hX)
ztgfp (by rw [bandSet F _ by_decide])
ztgfq (by rw [f₃ _ by_omega, f₃ _ by_omega, w31, w7]; omega)
ztgfr (by rw [g3 _ by_omega, g2 _ by_omega, g1 _ by_omega]; omega)
ztgfx (by rw [n2' fEE by_simp, n2' fEH by_simp, vEE, vEH]; tauto)
ztgfy (by rw [p₁.1 _ by_simp, p₁.1 _ by_simp, b100, b101]; omega)
ztgga (by rw [v₁, o₁.1 jr by_grind, hm, hs, hj]; omega)
ztgjg (fun i hi => by_simp_all)
ztgjh (fun i i' h1 h2 h3 h4 h => hinj i i' h1 h2 h3 h4 by_grind)
ztgjp (fun r h1 h2 => (kk r by_omega).trans (hk0 r h1 h2))
ztgjq (fun u hu => by_grind)
ztgmd (simple_vtx_inj hP hk by_omega h')
ztgob ⟨by_omega, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
ztgoc ⟨by_omega, ?_, fun r' hr' => ?_, rfl, rfl, rfl, rfl⟩
ztgoe ⟨by_omega, fun H' C' hC' => ?_⟩
ztgof ⟨by_omega, fun _ => ?_, fun d t hv ht0 ht1 hlt hle => ?_⟩
ztgog ⟨by_tauto, ?_, ?_⟩
ztgoh ⟨c', _, .seq (.ifLtN_false by_omega e₁) e, by_omega, hm, hr⟩
ztgoi ⟨c', _, .seq e₁ (.ifLtN_true hf ex), by_omega, hb, fr⟩
ztgoj ⟨c', _, by_omega, .ifLtN_false g1 (.ifLtN_false g2 e), ?_, o⟩
ztgok ⟨c', _, by_omega, .ifLtN_false g1 (.ifLtN_true g2 e), ?_, o⟩
ztgos ⟨c₃, _, ex, by_omega, v.2.2, v.1, v.2.1, exec_frameB ex wr_recS⟩
ztgou ⟨e, ?_, h6, by_omega, rfl, fun r hr => ?_, rfl⟩
ztgoy ⟨fun r hr => ?_, by_grind, fun a ha => ?_, rfl, rfl⟩
ztgoz ⟨h.stk _ by_omega, hl⟩
ztgpa ⟨iscr_sw by_norm_num by_norm_num, by_omega⟩
ztgpb ⟨j, hj, by_grind⟩
ztgpg ⟨q - 6, by_omega⟩
ztgpk ⟨rfl, by_grind, by_grind⟩
ztgpo ⟨t - 1, by_omega⟩
ztgpq ⟨t, by_omega, by rw [hsd t by_omega, NFLoc.getD_of_lt 0 ht, e]⟩
ztgpr ⟨u, by_omega, ?_⟩
ztgpw ⟨⟨h, rfl, hh, by_simp_all, ?_, by_simp_all⟩, epos, epar⟩
ztgpx ⟨⟨hmem _ by_omega, hmem _ by_omega⟩, hmem _ by_omega, hmem _ by_omega⟩
ztgrc (by simp [Src.pt, SymPt.Lt, k₁' 212070 by_norm_num by_norm_num, hi, hin])
ztgsx ⟨by_omega, ?_, fun r h1 h2 => by simp [h1, h2]⟩
ztgsy ⟨c', k₁ + 2 + k₂, .whileLtN_true by_omega e₁ e₂, hI', ?_⟩
ztgvg ((Exec.whileLtN_false by_omega hw).cast_end ?_)
ztgvs ((chainModel C).key Q (ps[i]' by_omega).e)
ztgvt ((chainModel C).key Q (ps[i]' by_omega).s)
ztgvv ((f2.1 _ by_decide).trans p11)
ztgvw ((f2.2.1 _ by_decide).trans p1z)
ztgxc (.seq e₂ (.ifLtN_true by_omega e₃))
zthat (IRS.ifT by_omega (IRS.skip hI₂ rfl))
zthbt (Nat.mul_ne_zero by_omega by_omega)
zthdw (band8 by_omega by_omega)
zthee (boundary_subset_filled P (vtx_mem_boundary P by_omega))
zthei (by rintro rfl; exact h3 by_decide)
zthen (by rw [F.1 _ by_decide])
zthfa (by rw [s2.1 _ by_simp, s1.1 _ by_simp, h20]; omega)
zthgt (fun a ha => hI.hm a by_omega)
zthgy (fun h => hNL 0 by_norm_num by_omega)
zthgz (fun i hi => (hpr i by_omega).1 (hpre₃ i hi))
zthha (fun i' b c d => by_omega)
zthhq (hne _ by_simp)
zthih (k2 (k1 bxb by_omega) by_omega)
zthis (nS _ by_norm_num)
zthiv (nob by_decide by_decide)
zthlz ⟨?_, ?_, ?_, Or.inr by_tauto, Or.inr by_tauto, ?_, ?_⟩
zthma ⟨?_, by_grind⟩
zthmf ⟨_, _, e', by_omega, ?_, fun r hr => ?_⟩
zthmg ⟨_, _, ex', by_omega, ?_, ?_, exec_frameB ex' wr_ldRange⟩
zthmh ⟨_, _, ex, by_omega, by_simp_all, ?_, exec_frameB ex by_decide⟩
zthmj ⟨_, rfl, by_grind, ⟨h0, h1, by_grind⟩, hp⟩
zthmk ⟨by_omega, ?_, ?_, rfl⟩
zthml ⟨by_simp, ?_⟩
zthmo ⟨c', k, ex, by_omega, hI, hrf, hQ c' hq⟩
zthmu ⟨d', k', e', by_omega, exec_frameB e' by_decide, v1, v2⟩
zthmw ⟨d7, _, ex, by_omega, ?_, ?_, FrameB.refl _ _⟩
zthmx ⟨d₇, _, X', e₇.wb_right, ?_, v7, by_omega, by_omega⟩
zthnc ⟨hl, hHW, by_omega, ?_⟩
zthnl ⟨pa, pb, ta, tb, hAa, hAb, hpt, by_tauto⟩
zthqa ((sideInArc_iff_off hg0 hgn kP0 kP1 kZ0 kZ1 kx0 kx1 hPZ).2 by_grind)
zthqr (BZB_keep by_omega)
zthsa (RS.const hI by_trivial by_omega)
zthse (band_sw_not by_omega)
zthwt (frame_test_bit by_omega)
zthwu (fun _ => ⟨c₁, k₁, ex₁, by_omega, h₁⟩)
zthxi (f₁ _ by_norm_num by_norm_num)
zthxj (g _ by_norm_num by_norm_num)
zthym (k2 _ by_omega by_omega)
zthyn (kp _ by_norm_num by_norm_num)
zthyx (m₄ (by rw [G07 _ le_rfl by_norm_num]; exact h))
zthyz (nk q by_omega by_omega)
ztiam (rot_index_inj hj by_omega h)
zticf ⟨by_omega, ?_, by_simp_all, fun r hr hr2 => ?_, by_simp_all⟩
zticg ⟨c', _, .ifLtN_false hs ex, by_omega, bt.congr ?_, f⟩
ztich ⟨c', _, .ifLtN_true hs ex, by_omega, bt.congr ?_, f⟩
ztick ⟨e'.wb_right, hfd.trans hf'', by_omega, fun f u hf hu => ?_⟩
zticl ⟨fun h => absurd h by_norm_num, fun _ t ht hS => ?_⟩
ztico ⟨p - s, by_omega, by rw [Nat.mod_eq_of_lt by_omega]; omega⟩
zticp ⟨q.1 + s, by_linarith, hout, fun x h1 h2 => ?_⟩
ztihd (FrameN.mono (Frame.toN F₅) by_decide)
ztihm (Or.inl ⟨by_rfl, by_decide⟩)
ztiie (by rw [a110, o14.1 _ by_simp, h103]; omega)
ztiif (by rw [a112, o15.1 _ by_simp, h103]; omega)
ztiim (by rw [rg 81140 by_omega, rg 81141 by_omega]; omega)
ztiin (by rw [s2.1 60023 by_simp, s1.1 60023 by_simp]; omega)
ztiji (fun a ha => by rw [m₆ a by_omega, m₅])
ztijo (fun i h1 h2 => by_grind)
ztijp (fun j hj => by rw [m₆ _ by_omega, m₅])
ztilg (inDrv_of fun q h => by_grind)
ztilh (inK _ hdn p₀ t₀ hp₀ ht₀ ht₀1 hf₀ K₁ c₁ hK₁ by_grind)
ztili (iw_edge_ne hQ T hD hli by_omega)
zting ⟨N.chord k, by_simp_all, rfl⟩
ztink ⟨_, _, ex, by_omega, ?_, ?_, ?_⟩
ztinl ⟨_, _, wpos_exec ea eb, le_rfl, by_simp_all, by_simp⟩
ztinm ⟨by rw [f6.2.2.1, o1], by_omega, by_omega, by_omega⟩
ztino ⟨by_omega, ?_, by simp [h], by_simp, by_simp_all⟩
ztinp ⟨by_omega, ?_, fun x hx => by simp [hx]⟩
ztinq ⟨by_omega, by_grind, fun _ => fun t _ h => ?_⟩
ztinr ⟨c', _, by_omega, .ifLtN_false g e, ?_, o⟩
ztins ⟨c', _, by_omega, .ifLtN_false h e, ?_, o⟩
ztint ⟨c', _, by_omega, .ifLtN_true g e, ?_, o⟩
ztinu ⟨c', _, by_omega, .ifLtN_true g1 e, ?_, o⟩
ztinv ⟨c', _, by_omega, .ifLtN_true h e, ?_, o⟩
ztinw ⟨c', _, by_omega, .ifLtN_true h e, by_simp_all, o⟩
ztinx ⟨c', j, e, by_simp_all, v, Bidx_frame fr _⟩
ztioa ⟨c', k, ex, hk, q, exec_frameB ex by_decide⟩
ztioe ⟨c₁, _, by_omega, .ifLtN_false h e₁, ?_, o₁⟩
ztiof ⟨c₃, _, .ifLtN_false by_omega e₃, by_omega, ?_, r₃⟩
ztioh ⟨d, t, h0, h1, by_linarith, h3, rfl⟩
ztioj ⟨j, by_omega, by simp only [↓reduceIte]; omega⟩
ztiop ⟨s 4820 by_norm_num by_norm_num, ?_⟩
ztirp (by rw [hGn]; exact sig_lt li by_omega _ _)
ztisj (fun _ => ⟨0, exec_skip_upd hw r, by_omega⟩)
ztist (fun r h1 h2 => r₂ r (bpt_lo h1 by_omega))
ztitd (ih _ _ ((List.length_filter_le _ _).trans by_omega))
ztiwe ⟨by_omega, by rw [h40003]; exact hNFW, hNF⟩
ztiwf ⟨by_omega, fun hf => ?_, fun hf => h2 by_omega⟩
ztiwh ⟨hlt, by_omega, by_simp_all, fun x hx1 hx2 => ?_⟩
ztiwi ⟨hlt, by_simp_all, by_omega, fun x hx1 hx2 => ?_⟩
ztiwj ⟨hxD, fun ⟨c, hc, hxc'⟩ => by_grind⟩
ztiwo ⟨ε₀, mem_Ioi.1 hε₀, fun ε h1 h2 => hsub by_grind⟩
ztjdl (.ifLtN_true by_omega e₁)
ztjim (Exec.constN w₆ _ _ by_omega)
ztjkq (Or.inl by_norm_num)
ztjoj (band12_oracle by_norm_num by_norm_num)
ztjok (band5_oracle by_norm_num by_norm_num)
ztjpz (by rw [Fa.1 _ by_decide, dA]; omega)
ztjqc (by rw [hnW, Nat.mod_eq_of_lt by_omega]; exact eb)
ztjqf (by rw [o₂.1 _ by_decide, v104, h05])
ztjuw (exec_frameB e₄ by_decide)
ztjux (exec_frameM x by_decide)
ztjvh (fun _ => x_mono (x_skipR d12 hw12 217064) by_omega)
ztjvi (fun _ => x_mono (x_skipR d13 hw13 217064) by_omega)
ztjvv (fun h => absurd h (hDne _ by_omega hjL))
ztjvw (fun ht => ⟨fun h0 => ?_, by_omega⟩)
ztjwa (fun j hj => by_grind)
ztjwk (fun r hr => by_omega)
ztjwq (fun x hx => by_grind)
ztjwr (fun x hx => by_omega)
ztjwu (f₃.1 _ by_decide)
ztjxd (g₀ _ by_norm_num)
ztjxz (hne _ by_decide)
ztjzh (k3 (k2 (k1 bax by_omega) by_omega) by_omega)
ztjzp (kk₂ _ by_decide by_decide by_decide)
ztkbf (nD _ by_simp)
ztkbh (ne_of_Bl hr by_simp)
ztker (sc_of_bt by_omega F₂)
ztkfj (spec_ifLtN_false by_omega ?_)
ztkfy (tr a2 _ by_simp by_simp)
ztkfz (tr a3 _ by_simp by_simp)
ztkga (tr a4 _ by_simp by_simp)
ztkgb (tr a5 _ by_simp by_simp)
ztkij ⟨0, by_omega, by_omega⟩
ztkiv ⟨_, _, _, by_simp_all, C.chordSet_eq_hseg k σ⟩
ztkix ⟨by_linarith, ?_⟩
ztkiy ⟨by_nlinarith, by_nlinarith, by_nlinarith⟩
ztkiz ⟨by_norm_num, ?_⟩
ztkjb ⟨by_simp_all, by_simp_all⟩
ztkje ⟨c, 2, .whileLtN_false by_omega hw, hc, by_omega⟩
ztkkb ⟨cB, k', e', by_omega, ?_, rB⟩
ztkkj ⟨c₁₀, _, eAll, by_omega, ?_, ?_⟩
ztkkk ⟨c₂, _, .seq e₁ e₂, by_omega, ?_⟩
ztkkn ⟨c₄, _, ex, by_omega, ?_, ho⟩
ztkko ⟨d', k', ex, hU, hk', by_omega⟩
ztkkq ⟨d', k, e, by_simp_all, ?_, ?_⟩
ztklc ⟨fun hf1 => absurd hf1 by_omega, fun _ => hnh⟩
ztklr ⟨hsX, by_omega⟩
ztklx ⟨h₁ - 1, by_omega⟩
ztkly ⟨i, by_simp_all⟩
ztklz ⟨i, ⟨hi, by_simp_all⟩, hi.1, rfl⟩
ztkma ⟨iscr_sw by_decide by_decide, by_omega⟩
ztkmb ⟨iscr_sw' by_norm_num by_norm_num, by_omega⟩
ztkmc ⟨k - 1, by_omega⟩
ztkme ⟨k, rfl, hkl, by_grind, ?_, by_grind⟩
ztkmg ⟨le_antisymm ?_ ?_, by_simp_all⟩
ztkmh ⟨p - pa, by_omega, ?_, ?_, ?_⟩
ztkml ⟨q' - se + 1, by_omega, by_omega, ?_⟩
ztknd ⟨w - 6, by_omega⟩
ztknf ⟨x, by_omega⟩
ztkpm ((shared_iff₁ hA.hP _ q.he q.hP0 q.hP1).2 by_grind)
ztkqh (Or.inr (Or.inr ⟨le_refl _, by_omega⟩))
ztksr (by rw [R₂ _ by_decide by_decide]; omega)
ztksv (by rw [g' _ by_omega by_omega, h40])
ztksw (by rw [g' _ by_omega by_omega, h90])
ztksx (by rw [g' _ by_omega by_omega, h91])
ztktb (by rw [hL, Nat.mod_eq_of_lt by_omega]; omega)
ztkua (by rw [k2 _ by_omega by_omega]; omega)
ztkub (by rw [k3 _ by_simp]; exact hB)
ztkuc (by rw [k3 _ by_simp]; exact hK)
ztkup (by rw [r₂ _ by_omega by_omega, q54])
ztkuq (by rw [r₂ _ by_omega by_omega, q55])
ztkwx (seg_subset_obs hs ((mem_seg_flat hf).2 by_grind))
ztkyf ⟨?_, by_omega, fun _ => notset _ ?_⟩
ztkyg ⟨Up, hUp, fun z hz hzD => by_simp_all⟩
ztkyh ⟨_, rfl, by_grind, hpp _, ?_⟩
ztkyl ⟨fun h => ⟨h.1, h⟩, by_simp_all⟩
ztkyq ⟨rfl, rfl, (hholes j by_omega).2.2⟩
ztlfm (RS.ifF by_omega (leaf_set hI hf le_rfl ?_))
ztlfn (RS.ifF by_omega (leaf_set hI hs le_rfl ?_))
ztlfo (RS.skip hI₉ ⟨by_omega, ?_, a19⟩)
ztlgd (b21 _ by_norm_num by_norm_num)
ztlgi (bprim_R' hR by_omega by_omega)
ztlgo (by rw [F₁.1 _ by_decide, h35])
ztlgs (by rw [a₃ _ by_norm_num by_norm_num by_simp])
ztlgu (by rw [band8 by_omega by_omega]; decide)
ztlgv (by rw [band8 h1 by_omega]; omega)
ztlgw (by rw [bandOf_l41 by_omega by_omega]; decide)
ztlgz (by rw [fr1 F₆ by_decide]; omega)
ztlha (by rw [fr1 R₁ by_decide, h12])
ztlhb (by rw [fr7 _ by_decide]; omega)
ztlhc (by rw [f₁ _ by_decide]; tauto)
ztlhd (by rw [g _ by_decide, c0])
ztlhe (by rw [g _ by_decide, c1])
ztlhf (by rw [g _ by_decide, c2])
ztlhg (by rw [g _ by_decide, hn])
ztlhh (by rw [g₂ _ by_decide]; omega)
ztlhi (by rw [g₂ _ by_omega]; omega)
ztlhx (by rw [hm12 _ by_omega]; rfl)
ztlib (by rw [hr2 _ by_decide by_decide by_decide])
ztlie (by rw [o13.1 _ by_simp, h100])
ztlif (by rw [o13.1 _ by_simp, h102])
ztlig (by rw [o₂.1 _ by_decide, v100])
ztlim (by rw [r4 _ by_decide]; omega)
ztlir (by rw [r₂ _ by_decide by_decide by_decide])
ztlis (by rw [r₂ _ by_decide, o05])
ztlit (by rw [r₂ _ by_decide, o08])
ztljj (by rwa [g _ by_decide] at hK)
ztlod (fun h0 => by_grind)
ztlot (fun r h => r₃ r by_omega by_omega by_omega)
ztlpk (g₂ 50202 by_norm_num by_norm_num)
ztlpp (hb₂ _ by_norm_num by_norm_num)
ztlux ⟨(Nat.pow_dvd_pow 2 by_omega).trans hd, ?_⟩
ztluz ⟨-1, by_simp⟩
ztlva ⟨1 - t, by_linarith, by_linarith, ?_⟩
ztlve ⟨False, h.mono by_grind⟩
ztlvf ⟨Or.inr by_simp_all, by_omega, fun h => ?_⟩
ztlvg ⟨_, _, e', by_omega, by_simp_all⟩
ztlvh ⟨by rw [this]; decide, by_grind⟩
ztlvi ⟨by_nlinarith, Or.inl by_nlinarith⟩
ztlvj ⟨by_omega, ?_, ?_, ?_, ?_⟩
ztlvk ⟨by_omega, ?_, ?_, ?_, by_simp_all⟩
ztlvl ⟨c', k, e, by_grind, ?_⟩
ztlvm ⟨c', k, e, by_omega, by_simp_all⟩
ztlvn ⟨c', k, ex, by_omega, hr⟩
ztlvq ⟨c₂, k₂, e₂, by_omega, ?_⟩
ztlvr ⟨d2, k2, e2, by_omega, ?_⟩
ztlvu ⟨fun _ => ?_, fun h => by_grind⟩
ztlvv ⟨fun h => by_grind, fun _ => ?_⟩
ztlwb ⟨gR' _ by_omega by_omega, gR' _ by_omega by_omega⟩
ztlwh ⟨hg', d, hvd, hmd, by_grind⟩
ztlwr ⟨y, a, b, by_simp_all, rfl⟩
ztlzn ((param_eq_zero_iff _ _ _).2 by_simp_all)
ztmaj (BL_keep by_omega)
ztmbc (Finset.range_subset_range.mpr by_omega)
ztmbl (List.mem_flatten.2 by_grind)
ztmbv (Or.inl by_simp_all)
ztmcj (Set.disjoint_left.2 by_grind)
ztmdy (by rw [r₁ _ by_decide by_decide])
ztmdz (by rw [r₃ _ by_decide by_decide])
ztmea (by rw [r₅ _ by_decide by_decide])
ztmhk (cmp _ _ by_omega (hfneg hs))
ztmjc (er_of by_omega)
ztmjs (fun i hi => k1 _ by_omega by_omega)
ztmjx (fun q a b => f' q by_omega)
ztmks (hK.subset by_simp_all)
ztmlb (hc.2 by_norm_num)
ztmlh (hl_loc by_simp)
ztmmg (lt_of_lt_of_le ht (cntF_mono key by_omega r'))
ztmmj (m2cS_irs E hI hM hD hpos by_omega hr')
ztmmm (mem_events.2 ⟨i, hi, by_tauto⟩)
ztmmo (no by_grind)
ztmnl (s6.mono by_simp)
ztmqc ⟨abs_lt.2 ⟨by_nlinarith, by_nlinarith⟩, by_simp⟩
ztmqe ⟨by_omega, Nat.mod_lt _ by_omega, vtx_hole_ne ha⟩
ztmqf ⟨by_omega, Nat.mod_lt _ by_omega, vtx_hole_ne hb⟩
ztmqh ⟨by_omega, by_simp_all, fun h1 => ?_⟩
ztmqi ⟨by_omega, fun H C' hC' => ?_⟩
ztmqs ⟨lerp u v t, by_grind, ?_⟩
ztmqt ⟨slitSeg C, Or.inr by_simp, Or.inl this⟩
ztmto N.chord i.1 = N.chords[i.1]' by_grind
ztmtp N.chord j.1 = N.chords[j.1]' by_grind
ztmye ((Nat.pow_dvd_pow 2 by_omega).trans hd)
ztmyu ((f2.1 _ by_decide).trans p1n)
ztmyz ((g₁ _ by_decide).trans h60)
ztnac (.ifLtN_false by_omega e₁)
ztnci (.seq e2 (.ifLtN_true by_omega e3))
ztnkk (D.mem_closedTrap_bot by_linarith by_linarith)
ztnnp (Or.inl ⟨Or.inl by_grind, a3⟩)
ztnnq (Or.inl ⟨Or.inr by_grind, a3⟩)
ztnsw (by rw [F₁.1 _ by_decide])
ztnth (by rw [fn1 _ by_omega])
ztnti (by rw [f₁ _ by_decide])
ztntj (by rw [g₁ _ by_decide])
ztntn (by rw [hR2 6 by_omega])
ztnwz (chordSet_adm hok by_omega)
ztnxa (closure_mono by_grind hcl)
ztnya (exec_frameB ex₂ by_decide)
ztnyb (exec_frameB e₆ by_decide)
ztnyc (exec_frameM X by_decide)
ztnyv (fun h => hNL 1 by_norm_num h.symm)
ztnyw (fun h' hm => hh h' by_grind)
ztnyx (fun i hi => hR2 i by_omega)
ztnyy (fun i hi => hreg' i by_omega)
ztnyz (fun i hi => k2 _ by_omega)
ztnza (fun i hi => reg4 i by_omega)
ztnze (fun j hj => he _ by_omega)
ztnzf (fun j hj => seg_getD hE by_omega)
ztnzg (fun k hk => hPv k by_grind)
ztnzt (g _ by_decide)
ztoae (hGs.rbase 11 by_omega)
ztoaf (hGs.rbase 14 by_omega)
ztoag (hGs.rbase 17 by_omega)
ztoah (hGs.rbase 21 by_omega)
ztoap (hb21 q by_omega)
ztoat (hh g by_simp)
ztoax (hmem e₁ by_simp)
ztoay (hmem f₁ by_simp)
ztoaz (hnoPOS _ by_omega)
ztocc (k1 byb by_omega)
ztocg (kg _ by_simp)
ztocv (leaf_skip hI by_omega)
ztohd (r₄ _ by_omega)
ztoia (spec_ifLtN_true by_omega ?_)
ztojr (vtx_mem_boundary _ by_simp_all)
ztolh ⟨0, by_linarith, by_linarith, ?_⟩
ztolk ⟨0, le_rfl, zero_le_one, by_simp⟩
ztoll ⟨1, h.1, by_norm_num, h.2⟩
ztolq ⟨2, h.1, by_norm_num, h.2⟩
ztolr ⟨3, h.1, by_norm_num, h.2⟩
ztolv ⟨?_, ?_, ?_, by_simp_all⟩
ztomh ⟨_, by_linarith, by_linarith, zt⟩
ztoml ⟨by rw [hp0], by_simp_all⟩
ztomm ⟨by_decide, by_rfl⟩
ztomn ⟨by_grind, fr3 c' k₃ ha₃ hm₃⟩
ztomo ⟨by_grind, fun m hm => ?_⟩
ztomp ⟨by_grind, hfin c' h1 h2 h3⟩
ztomq ⟨by_linarith, by_grind⟩
ztomr ⟨by_linarith, hs1⟩
ztoms ⟨by_omega, by_simp_all, ?_, ?_⟩
ztomt ⟨by_omega, by_simp_all, by_simp_all, by_grind⟩
ztomu ⟨by_omega, by_simp_all⟩
ztomv ⟨by_positivity, by_linarith⟩
ztomw ⟨by_simp, ?_, ?_, ?_⟩
ztomx ⟨by_simp_all, by_simp_all, by_simp_all, ?_⟩
ztomy ⟨by_tauto, fun i hi => ?_⟩
ztonb ⟨c, by_simp_all, hfree, rfl⟩
ztong ⟨d, hd, by_simp_all, ?_⟩
ztonm ⟨fun h0 => hnv ?_, by_omega⟩
ztonu ⟨hEi, by_omega⟩
ztooj ⟨hj, hjL, hjd, by_simp_all⟩
ztook ⟨hmem₄ _ by_omega, hmem₄ _ by_omega⟩
ztool ⟨hp.1, fun hm => hp.2 by_grind⟩
ztoon ⟨hpD, by_grind⟩
ztooo ⟨hs, hs0, hps, by_positivity⟩
ztoov ⟨j - i - 1, by_omega⟩
ztopi ⟨rfl, ?_, by_simp_all, ?_⟩
ztopk ⟨s - ε, by_grind, rfl⟩
ztopr ⟨v, by_simp_all⟩
ztopw ⟨δ₂, hδ₂, by_grind, by_grind⟩
ztosp ((div_le_one by_linarith).2 by_linarith)
ztosq ((div_le_one hpos).2 by_linarith)
ztosr ((div_le_one_of_neg by_linarith).2 by_linarith)
ztosy ((mem_triangle_iff_bary hdet).2 by_grind)
ztosz ((regionOfDiag_injOn hP).mono by_simp_all)
ztota ((vtxChords_finite hP).subset by_grind)
ztowt (Exec.addN hw _ _ _ by_omega)
ztowv (Exec.addN hwd _ _ _ by_omega)
ztoxb (IRS.ifT by_omega (hzero by_omega))
ztoxc (IRS.ifT h2 (hs by_omega))
ztoxf (Machine.Exec.addN hw _ _ _ by_omega)
ztoxy (afterFaces_mono (hFV.1 by_norm_num) hUV)
ztoyb (beforeFaces_mono (hFV.2 by_norm_num) hUV)
ztpbe (fun a b h => by_omega)
ztpbg (fun c' hc hlt => by_simp_all)
ztpbi (fun d _ hlt => by_omega)
ztpbm (fun h => absurd h by_omega)
ztpbp (fun h0 => absurd h0 by_omega)
ztpeh (sv 0 by_norm_num by_omega 1 le_rfl)
ztpfa ⟨by_omega, fun _ => ReflTransGen.refl⟩
ztpfb ⟨by_omega, fun h => ?_⟩
ztpfc ⟨by_simp, by_simp, Nat.zero_le _⟩
ztpfd ⟨c.nreg 170050 / 2, by_omega⟩
ztpfe ⟨c.nreg 170051 / 2, by_omega⟩
ztpfi ⟨fun hz => ?_, by_omega⟩
ztpfr ⟨s 1101 by_norm_num by_norm_num, ?_⟩
ztpfs ⟨s 1107 by_norm_num le_rfl, ht⟩
ztpft ⟨s _ by_omega by_omega, trivial⟩
ztpge ⟨x, mem_dropWalls.2 by_grind, rfl⟩
ztpwi (Bin_false by_omega)
ztpxr (Exec.constN by_omega _ _ by_omega)
ztpxs (Exec.constN hE.wb _ _ by_omega)
ztpxx (Exec.constN w₁ 170014 0 by_omega)
ztpxz (Exec.constN w₂ _ _ by_omega)
ztpya (Exec.subN by_omega _ _ _)
ztqel (bt_cs by_norm_num)
ztqnd (fun _ _ => by_omega)
ztqnf (fun _ h => by_simp_all)
ztqnh (fun a _ => by_grind)
ztqni (fun a h => by_omega)
ztqnq (fun e => hb by_simp_all)
ztqnr (fun e => hx1 by_grind)
ztqns (fun h => g3 by_linarith)
ztqoc (fun r h => by_omega)
ztqog (fun v hv => by_omega)
ztqoj (fun x hx => by_simp_all)
ztqol (fun y hy => by_grind)
ztqov (h.chord₁ (h.meet by_simp_all))
ztqqd (hfinA.subset by_grind)
ztqqs (hs ▸ hopen s by_simp_all)
ztqrx (iterate_ne_of_lt_per hf hx by_omega by_omega)
ztqso (kp _ by_norm_num by_norm_num by_norm_num)
ztqsp (kp₂ _ by_norm_num by_norm_num by_norm_num)
ztqsq (kp₄ _ by_norm_num by_norm_num by_norm_num)
ztqtx (nl r lX by_trivial hrl)
ztqvr (r₁ _ by_decide by_decide by_decide)
ztqvs (r₃ _ by_decide by_decide by_decide)
ztqwj (sig_lt li by_omega _ _)
ztqws (ssBit_exec hw₃ 0 by_omega hW1)
ztqzg (yes by_grind)
ztqzt ⟨0, by_grind, by_simp⟩
ztqzu ⟨0, by_omega, rfl⟩
ztqzv ⟨1, by_omega, ?_⟩
ztqzw ⟨1, by_omega, hj⟩
ztrad ⟨H, by_simp_all, hA.hreg⟩
ztrak ⟨by_grind, ?_, by_grind⟩
ztram ⟨by_omega, by_grind, ?_⟩
ztran ⟨by_omega, by_linarith, by_linarith⟩
ztrao ⟨by_omega, by_omega, ?_⟩
ztrap ⟨by_omega, by_simp_all, rfl⟩
ztraq ⟨by_omega, by_tauto, by_simp_all⟩
ztrar ⟨by_omega, hq.2, ?_⟩
ztras ⟨by_omega, rfl, ?_⟩
ztrat ⟨by_ring, by_nlinarith, by_nlinarith⟩
ztrau ⟨by_simp, ?_, ?_⟩
ztrav ⟨by_simp_all, by_nlinarith, by_nlinarith⟩
ztraw ⟨by_simp_all, hexc.1, ?_⟩
ztrbe ⟨c, by_simp_all, rfl⟩
ztrcc ⟨e - 6, by_omega⟩
ztrck ⟨g - 1, by_omega⟩
ztrco ⟨h0, h1, by_tauto⟩
ztrcr ⟨hA.2.1, hA.2.2.1, by_tauto⟩
