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

zn ztbaiv (vert ztmlv)
ztbaiw (ztkhx z)
ztbaix (ztkhz x.1)
zg zuc have hQn : ztx := shear_n _ _
zuk have hAl : ztmi := rfl
zul rw [Nat.mod_eq_sub_mod by_omega, Nat.mod_eq_of_lt by_omega]
zuo refine h.mono by_simp ?_
    rintro c' ⟨c₁, c₂, hm, e1, e2, hpost, f1, hk, hA, hm'⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at e1 f1
zubc rw [Machine.upd_other _ _ _ by_omega]
zubn have hN : ztgai := by rw [hP]; simp [Host.poly, Polygon.n]
     have hsucc := NFLoc.preLen_succ Q.n H hr
     have hlen := NFLoc.preLen_mono Q.n H zteas
     rw [NFLoc.preLen_length] at hlen
     rw [hrun] at hsucc
     simp only [NFLoc.itemCnt] at hsucc
zubp have hn : ztx := shear_n _ _
zubr rw [v32 _ by_decide by_decide by_decide, g₂ _ by_decide]; omega
zubv refine spec_ifLtN_false by_omega ?_
zubw rw [r₄ _ by_decide, f₃.1 _ by_decide, k₂ _ by_decide by_decide]
zubx have e1 : ztwc := hk1
zubz obtain ⟨a1, a2, a3, a4, a5⟩ := ha j hj
     obtain ⟨b1, b2, b3, b4, b5⟩ := ha' j by_omega
     change N.arc j = N'.arc j
     rcases hx : N.arc j with ⟨x1, ⟨x2, x3⟩, ⟨x4, x5⟩⟩
     rcases hy : N'.arc j with ⟨y1, ⟨y2, y3⟩, ⟨y4, y5⟩⟩
     rw [hx] at a1 a2 a3 a4 a5; rw [hy] at b1 b2 b3 b4 b5
     simp only at a1 a2 a3 a4 a5 b1 b2 b3 b4 b5
     simp only [ARec.mk.injEq, WPos.mk.injEq]; omega
zucb have hW1 : ztehs := by have := hE.hWh; unfold hostWords at this; omega
zuck have hsd : ztmwq := by rw [hs]; linarith [min_le_left d k]
     have hsk : ztppx := by rw [hs]; linarith [min_le_right d k]
     have hmem : zteig := by rw [← hwv]; exact hcD s hs0 hsd
     apply hM.trace p hp ztkek ztjub ztfed
zucl obtain ⟨a1, a2, a3, a4, a5⟩ := hc i hi
     obtain ⟨b1, b2, b3, b4, b5⟩ := hc' i by_omega
     change N.chord i = N'.chord i
     rcases hx : N.chord i with ⟨x1, x2, x3, x4, x5⟩
     rcases hy : N'.chord i with ⟨y1, y2, y3, y4, y5⟩
     rw [hx] at a1 a2 a3 a4 a5; rw [hy] at b1 b2 b3 b4 b5
     simp only at a1 a2 a3 a4 a5 b1 b2 b3 b4 b5
     simp only [CRec.mk.injEq]; omega
zucm have hQ : ztxw := (shearInvariance ztbhs P).1 hG.1
zucn have hW : ztkf := rfl
zucp set hc := c₀.nreg 50202 with hc_def
     set σ := c₀.nreg 50203 with hσ_def
     set M := chainModel C with hM
     set x : WPos := ztev with hx
     have hn : ztcri := C.sideWalk_n _
     have hlen := hE.hlen
     have hW := hE.hW
     have e₁ := Exec.copyN (P := P) hE.wb 50002 50201
zucs obtain ⟨s, hs, hseg, p, hp, t, ht, hq, hup⟩ := hM.reach z hzD hzv
     set q : Point := ztbfb with hqdef
     set L := (fun s' : ℝ => (ztbtb : Point)) '' Ico 0 s with hL
zucw rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega]
zucx set ε := min ztcal s / 2 with hε
     have hε0 : ztbad := by_positivity
     have hεr : ztmxl := by rw [hε]; have := min_le_left ztcal s; linarith
     have hεs : ztjaz := by rw [hε]; have := min_le_right ztcal s; linarith
zucz have hm : zttd := rfl
zudd refine spec_ifLtN_true by_omega ?_
zudk have hW1 : ztbla := by_omega
zudp by_cases hnb : c.nreg bF ≠ 1 ∨ offK P J e h < offK P J ztvo ztvp
zudq have hQ : ztx := qn'
zuds obtain ⟨a, b, hab, -, -, -, ⟨⟨pa, ta, hA, hAa⟩, -⟩, ⟨⟨pb, tb, hB, hBb⟩, -⟩⟩ := hM.ends c ztlz
zudx refine spec_ifLtN_false by_simp_all ?_
zudz have hE : ztgaa := by rw [B.hperm.length_eq, List.length_range]; have := B.hK; omega
zueb have : ztlbf := by show edgeSel _ _ _ _ _ _ _ _ = _; unfold edgeSel; simp_all
zued have hg0 : ztee := Nat.cast_nonneg _
zuee have hwv : ztbrq := Chazelle.Chain.sidePt_zero _ _
     set v := M.W.vtx p with hv
     set a := M.W.vtx ztcm with ha
zueh obtain ⟨d', -, hpts, -, -⟩ := attached_opposite hM ztesy hA'' hτ ztoao
     obtain ⟨s', hs'0, -, hxs'⟩ := hpts x hxc'
     refine ztkmu
     rw [hxs', hwv, rayPt_sub]
zuek refine spec_ifLtN_true by_simp_all ?_
zuem have hlt : ztgun := by_omega
     obtain ⟨c₁, k₁, e₁, hI₁, hk₁⟩ := hbody j c hlt hc
     obtain ⟨c', k₂, e₂, hI', hk₂⟩ := ih hI₁ by_omega by_omega
zuet have hn : ztdh := C.sideWalk_n _
zuew obtain ⟨c₀, hc₀, z₀, hz₀, hz₀D, hz₀U, h0, hq0⟩ := hA
     have hz₀T := hmid z₀ hz₀D zthxx h0 ztqqo
     have hU0 := habove c₀ hc₀.1 z₀ hz₀ hz₀T hq0
zuex obtain ⟨c₀, hc₀, z₀, hz₀, hz₀D, hz₀U, hq0, h0⟩ := hA
     have hz₀T := hmid z₀ hz₀D zthxx ztqqq h0
     have hU0 := hbelow c₀ hc₀.1 z₀ hz₀ hz₀T hq0
zuey rw [Nat.mod_eq_of_lt by_omega]
zuez rw [a4] at s4; rw [a5] at s5; rw [a6] at s6; rw [a7] at s7
     have b0 : ztjah := by_omega
     have b1 : ztjai := by_omega
     have b2 : ztjaj := by_omega
     have c1 : ztjak := by_omega
     have c2 : ztjal := by_omega
     have c3 : ztjam := by_omega
     rw [b0, b1, b2, c1, c2, c3]
zufa rw [ite_eq_right by_omega]
zufd have hm1 : ztcql := rfl
zufe obtain ⟨hmd, hmwf⟩ := E.md₂ hI
     have hNT := E.nt₂ hI
     have hNA : zthog := hNT.nfAt
     obtain ⟨htab, hbig, hTB, eL⟩ := E.tab hI
     have hA0 := arcs_pos hP₂ hNF
     obtain ⟨b7, b4A, b6A⟩ := NFLoc.nfWithin_bounds hNT hNF hA0
     obtain ⟨-, -, b3, -, -, -⟩ := Restore.nf_bounds hNT
     have hAW : ztcga := hI.hw.1 _
zufk obtain ⟨hR, hk⟩ := h
     refine ztfwn
     rcases hk with ⟨k, hx⟩ | ⟨k, hx⟩ | ⟨k, hx, s, hs, hl, he⟩
zufo have heq : ztlbn := by_grind
     have hz₀c := hslice c hc z hz hzT z₀ hz₀T heq
     exact eq_of_common by_grind ztfsh hz₀c hz₀ hz₀D
zufp have m1 : ztwh := by rw [hc1]
zufq intro h; simp only at h ⊢
     rw [he _ by_omega, he _ by_omega, he _ by_omega]; exact h
zuft rintro c₃ hI₃ hA₃ hA₃' ⟨⟨s, hs, hsl, hse⟩, q3, hA₃'', qm3⟩
     rw [q23, hH₂, hpe] at hse
     obtain ⟨hkl, hkh⟩ := symHgt hs hsl
     rw [hse] at hkh
     set k := if c₃.nreg ztibh = 0 then c₃.nreg ztibf else c₃.nreg ztibg with hkd
     have k1₃ := (Consts.fix hK hI₃).2.1
zugd have q01 := g₂ 50201 by_norm_num by_norm_num
     have q02 := g₂ 50202 by_norm_num by_norm_num
     have q03 := g₂ 50203 by_norm_num by_norm_num
     have hd2 : ztpnb := by rw [d₂]; exact dirCode_le_two _ _
zugo rw [g₃ _ by_norm_num by_norm_num by_decide, bandSet Fs _ by_omega]; omega
zugs obtain ⟨c₁, k₁, x₁, hk₁, v₁⟩ := setupA_exec (P := P) c hw hB' hK hA by_omega by_omega
     obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, fr₁, rr₁, m₁, rm₁, out₁⟩ := v₁
     have w₁ := x₁.wb_right
zugv have B := hE.ctx hK
     have hr' : ztjaf := by rw [hE.nRegions]; exact hr
zugy rw [g30, List.length_range, hm₄, mm₃]
     unfold SortL.seg
     apply List.ext_getElem by_simp
     intro t h1 h2
     simp only [List.getElem_map, List.getElem_range]
     simp only [List.length_map, List.length_range] at h1
zugz rw [← NFLoc.getD_of_lt 0 by_omega, ← NFLoc.getD_of_lt 0 by_omega] at this
     unfold lexLe at this
     rw [ite_eq_left hA, ite_eq_left hB] at this
     simp only [decide_eq_true_eq] at this
     rw [(hc4 _ hA).1, (hc4 _ hB).1, (hc4 _ hA).2, (hc4 _ hB).2] at this
     exact this
zuha set ε := min ε₀ r₀ / 2 with hε
     have hε0 : ztbad := by_positivity
     have hε1 : ztmxm := by rw [hε]; linarith [min_le_left ε₀ r₀]
     have hε2 : ε < r₀ := by rw [hε]; linarith [min_le_right ε₀ r₀]
     obtain ⟨-, -, hdiff⟩ := hsep ε hε0 hε1
     intro heq
     apply hdiff
zuhb obtain ⟨c, hcF, p', t', hA', hk⟩ := hcut
     obtain ⟨hpp, htt⟩ := sideKey_inj ht ht1 hA'.2.1 hA'.2.2.1 hk
     rw [← hpp, ← htt] at hA'
     obtain ⟨d, hd, -, hcD, hcmem⟩ := attached_opposite hM ztgjz hA' hτ by_simp_all
     obtain ⟨r₃, hr₃, hcl⟩ := hA'.2.2.2.2
zuhc set Bp := sidePt W pb tb with hBpdef
     obtain ⟨-, hyf, -⟩ := hM.attach_seg ztvtc hfA hfF hNF
     obtain ⟨-, hyf', -⟩ := hM.attach_seg zteae hA' hB ztbsb
     have hPn1 : Pn.1 ≠ Pf.1 := by_grind
     have hB1 : Bp.1 ≠ Pf.1 := by_grind
     have hopp := tie_opposite hM hFs hf hf' hne hfF hA' hfA.2.2.2.1 hB.2.2.2.1 hPn1 hB1
zuhf have hn : ztlh := cm_n J.whole
zuhh obtain ⟨-, hlo, hτs, hLst⟩ := caseB_facts J hbox
     have hb : ztidu := by unfold b₁; grind
     have hE₁ : ztcyk := by unfold E₁; omega
zuhp have hAL : ztmi := rfl
zuhq have i01 := hinp 50201 by_norm_num by_norm_num
     have i02 := hinp 50202 by_norm_num by_norm_num
zuhr have k1 : ztgar := by rw [hI.hin _ ztbc, hE.k1]
zuhy have hd0 : ztphr := by_grind
     set ε := min T d / 2 with hε
     have hε0 : ztbad := by_positivity
     have hεT : ztmxk := by rw [hε]; linarith [min_le_left T d]
     have hεd : ε < d := by rw [hε]; linarith [min_le_right T d]
     have hin := hdom ztbpt by_linarith by_linarith
zuhz obtain ⟨hτs, hlo, hLst⟩ := caseC_facts J hVNT hbox
     have hb : ztcfz := by unfold b₁; grind
     have hE₁ : ztcyk := by unfold E₁; omega
zuia refine Or.inr ztdfx
     have e1 : ztgur := by_omega
     have e2 : ztguo := by_omega
     have e3 : ztgus := by_omega
     have e4 : ztgup := by_omega
     exact NFLoc.symPtIn_copy hs h1 by_omega by_omega
zuid set E := (2 : ℝ) ^ ztbxl with hE
     have hE1 := one_le_E lam
zuig have hτlt := tpos_lt C J₀
     have hτ'lt := tpos_lt C' J₀'
     set g := 6 + τ with hg_def
     set g' := 6 + τ' with hg'_def
     have hg : g < W.n := by_grind
     have hg' : g' < W'.n := by_grind
     set s := 2 * C.m - τ with hs_def
     set s' := 2 * C'.m - τ' with hs'_def
zuih obtain ⟨-, -, h3, h4⟩ := hcl hzU
     rw [hzy] at h3 h4
     exact ztcbw
zuiv have hGM : ztebh := Or.inl ztiv
zuix have hmn := T.hm
     have hle := i0_le hQ T hD hli
     have hr := mod_i0 (C := C) li
     have hs := sA_lt' (C := C)
     obtain ⟨hL1, hL2⟩ := Trans.sA_inner hQ T hD
     have hv : ztcee := fun k hk => T.vertex_eq by_omega
     have htop : ztpiy := hv _ C.topIdx_le
zuiy have hn : ztbiy := by_omega
zuiz have hn : ztbof := by_omega
zujc intro h; subst h; exact hr (iscr_sw by_norm_num by_norm_num)
zujo rw [keep5 _ by_decide by_decide by_decide by_decide]; omega
zujr set u := P.vtx ztch with hu
     set v := P.vtx 0 with hv
     set w := P.vtx 1 with hw
zujt simp only [hqdef, sub_self, abs_zero]
     rw [max_lt_iff, show z.1 + ztdig - ztkhm = -ε by ring, abs_neg, abs_of_pos hε0]
     grind
zujx refine ztcp
zukb have hxW' : x ∈ Wg := ztuin
     obtain ⟨hxD, hxc⟩ := hsf x by_grind zttmx
     apply hxS
     refine ztfwr
     rintro ⟨c', hc', hxc'⟩
     have hA' := hxc c' hc' hxc'
     have hvc' : v ∈ c' := by have := hA'.2.2.2.1; grind
     have hy := hsys.snd_eq hc' hxc' hvc'
zuku have hWn : ztmd := by unfold hostWords at hWh; omega
zukv have hnσ : ztjh := by_grind
zukw obtain ⟨pb, tb, hB, hBne⟩ := hM.other_attach ztcik heA
     obtain ⟨pb', tb', hB', hBne'⟩ := hM.other_attach zteae hA'
     obtain ⟨-, hy, -⟩ := hM.attach_seg ztcik heA hB ztbsb
     obtain ⟨-, hy', -⟩ := hM.attach_seg zteae hA' hB' zthrn
zuld rw [show c₃.nmem ztdpj = ps.length from hq] at hi
zulh have e : ztixk := by_linarith
     have e' : ztehg := by_linarith
     have e1 : ztskq := by exact_mod_cast e
     have e2 : ztiye := by exact_mod_cast e'
zuli have h1 : ztfzq := by_decide
     have h5 : ztfzs := by_decide
     have h14 : ztixa := by_decide
     have h15 : ztfzr := by_decide
     unfold bandOf at hr
zulk have hM : ztlxj := walkAx_interiorModel hQ
zull have hm1 : ztwh := by rw [hc1]
zulo have k : zthpi := by_simp_all
     have k46 := k 170046 by_norm_num by_norm_num
     have k50 := k 170050 by_norm_num by_norm_num
     have k51 := k 170051 by_norm_num by_norm_num
     have k52 := k 170052 by_norm_num by_norm_num
     have k53 := k 170053 by_norm_num by_norm_num
     have k54 := k 170054 by_norm_num by_norm_num
     have k55 := k 170055 by_norm_num by_norm_num
zulp have m₁ : ztwh := by rw [h₁]
zulu obtain ⟨r, hr, hloc⟩ := FactsInterior.edge_local hW hL hp ht
     set δ := min r δ₀ / 2 with hδ
     have hδ0 : ztcfy := by_simp_all
     have hδr : ztsod := by rw [hδ]; linarith [min_le_left r δ₀]
     have hδδ : δ < δ₀ := by_grind
zumc all_goals try rw [k2' 170050 by_norm_num by_norm_num]
     all_goals try rw [k2' 170051 by_norm_num by_norm_num]
     all_goals try rw [k2' 170052 by_norm_num by_norm_num]
     all_goals try rw [k2' 170053 by_norm_num by_norm_num]
     all_goals try rw [k2' 170054 by_norm_num by_norm_num]
     all_goals try rw [k2' 170055 by_norm_num by_norm_num]
zumd have b34 : ztuqa := by rw [g₁ _ by_norm_num by_norm_num by_decide]; omega
     have b35 : ztuqb := by rw [g₁ _ by_norm_num by_norm_num by_decide]; omega
     have b36 : ztuqc := by rw [g₁ _ by_norm_num by_norm_num by_decide]; omega
     have hτ : ztlyw := tau_lt
zumf obtain ⟨r, hr, hsf⟩ := sector_free hM hFam.2.1 hFam.1 hp le_rfl one_pos
     filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hr] with s hs hsr
     have hs0 := hs
     rw [hUD]
     refine (hsf _ ?_ ztjcq).1
     rw [mem_ball, dist_rayPt _ hτ hs0.le]; simp_all
zumg have hht := hI.inv.hlt
     have hun : ztlxp := by rw [hI.u]; exact hI.inv.inv.qlt _ hht
     have hfirst : ztdrd := hp.ok.first_lt _ hun
zumi have hzT := hmid z hzD ztetb hmz.1 ztqqi
     have hUz := habove c hc z hz hzT hmz.2
     have hz0' := hclge _ hUz z₀ hz₀U
zumj have hzT := hmid z hzD ztetb ztqqp hmz.2
     have hUz := hbelow c hc z hz hzT hmz.1
     have hz0' := hclle _ hUz z₀ hz₀U
zumk intro pa ta c h
     have : ztehp := by exact_mod_cast h.1
     exact ⟨by have := h.2.1; positivity, by linarith [h.2.2.1]⟩
zumm obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hC
     have c0 := hc 0 by_omega
     have c1 := hc 1 by_omega
     have c2 := hc 2 by_omega
     have c3 := hc 3 by_omega
     have c4 := hc 4 by_omega
     simp only [add_zero] at c0
zumq obtain ⟨-, hc, -, -⟩ := arc_facts hN hne hp
     obtain ⟨U, hU, b, hab⟩ := (arcCover M Q ztdu hGM hN.1).2 _ hc
     obtain ⟨j, hj, hjs, -⟩ := NFLoc.listed_of_isArc hN hU hab
zumr obtain ⟨c', k, ex, hk, a, b⟩ := H
     exact ztbjz
zumz have hE₁ := hE.step e₁ by_decide
zuna have hL : ztiyk := by have := hd.2.1; omega
zunb have hm : ztcrl := fun a ha => hI.hm a ha
     obtain ⟨hC, hw⟩ := chainDesc_keep hwf' hcd hm hI.hA
     obtain ⟨mwfc, m0c, mdc⟩ := ShotList.modelDesc_keep hmwf h0 hcd hm hI.hA
     have hTB := fixr hI ztddj
     have hTL := fixr hI ztkxm
zunc have hm2 : ztdjs := rfl
zune have hσ : ztim := by_grind
zunj obtain ⟨y, hyI, hyB⟩ := ((Ioo_infinite ztoda).sdiff hBfin).nonempty
     set z : Point := ztkhp with hz
zunn refine regB_other _ _ _ ztdp
zuno refine ztdan
     unfold NF.chord
     rw [NFLoc.getD_of_lt _ hk]
     grind
zunw have hM : ztezg := FactsChain.walkAx J.whole hP
zunx have hQn : ztcfw := shear_n _ _
zuoa obtain ⟨reg, -, -, harc⟩ := isArc_sj hN ztfhw
     obtain ⟨reg', -, -, harc'⟩ := isArc_sj hN hq
     have hfree := harc.2.2.2.2.2.1
     have hcq := (WalkAx.arc_cuts hne harc').1
     have hlt := starts_lt hN hGM hne hpq hq
zuoe rw [k2 _ by_omega]; omega
zuog set W := (chainModel J.whole).W with hW
     set W' := (chainModel C').W with hW'
     have hn : ztmsm := by rw [hW, WalkEmbed.cm_n]; omega
     have hn' : 0 < W'.n := by rw [hW', WalkEmbed.cm_n]; omega
zuom have hb : ztcfz := by unfold b₁; grind
     have hE₁ : ztidn := by unfold E₁; omega
     have hL := lL1_add_lL2 J
zuon have hhi := hI.hi
     have hp1 : ztpia := by_grind
     have hqlo : ztguf := by rw [hlo]; exact Nat.le_mul_of_pos_right _ hp1
zuoq have t3 : ztlbr := by rw [hE₂.r32]; omega
     have e₃ := Exec.subN (P := P) w₂ 50120 50201 50081
zuos intro j e hj ⟨hw, h1, h2, h3, h4, hf, _⟩
     have h4' : ztgum := h4
zupb refine spec_ifLtR_false by_simp_all ?_
zupd rw [Nat.mod_eq_of_lt by_omega]; omega
zupj unfold Prot at hr; rw [Machine.upd_other _ _ _ by_omega]
zupk all_goals try rw [c51]
     all_goals try rw [c55]
     all_goals try rw [k0 170050 by_decide by_decide]
     all_goals try rw [k0 170052 by_decide by_decide]
     all_goals try rw [k0 170053 by_decide by_decide]
     all_goals try rw [k0 170054 by_decide by_decide]
zupm have hc := cntS_le (sel := sel) (lo := lo) ztsf
     have hcm := cntS_succ (sel := sel) (lo := lo) ztglz
     rw [show lo + j + 1 = lo + ztl by omega] at hcm
zupn have hm2 : ztpnc := by rw [R₂ _ by_decide, hq.m, hv.m]
     by_cases hlt : tj C ztvu < C.m
zupo have hn := hC.n_pos
     set n := (chainModel J.whole).W.n with hndef
     set g := 6 + tpos J.whole J.m₁ with hgdef
     have hg : g < n := hC.hg
     have hg0 : ztcjx := Nat.cast_nonneg _
     have hgn : ztcrg := by exact_mod_cast hg
zups obtain ⟨t0, t1, t2, t3, tS0, tS1, tS1lt, tpow, thalf, tent⟩ := tab_lt hR by_omega hΛ
     obtain ⟨S, hS⟩ : ztlcd := zths
     obtain ⟨T, hT⟩ : ztlce := zths
zupv rintro ⟨d, hd, hp⟩
     refine ztkkr
     obtain ⟨hU, hV⟩ := pc0_pts (Q := Q) hxn hyn (d := d) by_omega
     obtain ⟨a0, ab, b1⟩ := pc0_ab hx hy hxn hyn hwt d
zupx rw [q70] at hx
     rw [qm₃, m₂ _ by_omega, vm, qm]
     by_cases hxr : x = r
zupy rw [va, show e - 6 + 6 = e by omega] at b70 b71
     have hwa : ztmtn := rfl
zuqa simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false]
     have e1 : ztoqt := (cst 41 ztp).trans g1
     have e2 : ztsgz := (cst 42 by_omega).trans g2
     have e4 : ztsha := (cst 44 by_omega).trans g4
zuqd unfold tw
     rw [show ztdkn % 3 = s by omega, show ztdkn / 3 = j by omega, hg]
zuqh have hkm : k < C.m := by rcases h with h | h <;> [exact h.1; linarith [h.2]]
     have hτ1 : ztsoh := by rcases h with h | h <;> [exact h.2.2; linarith [h.2]]
zuqi have hn : ztcka := by_omega
zuql have x₀ := Exec.constN (P := P) hw 43250 0 ztbg
     set c₀ : Config := { c with nreg := upd c.nreg 43250 0 } with hc₀
     have w₀ := x₀.wb_right
     have g₀ : ztkos := by_simp_all
     by_cases hK : 0 < K
zuqs obtain ⟨hC6, hCW⟩ := hwf.2 h0
     obtain ⟨hl, hwfH, hHE, hs⟩ := hCW H C hC
     obtain ⟨hH, hP, h2, h3, h4, h5⟩ := hC
     have e1 := hm ztef by_omega
zuqt obtain ⟨hn0, -⟩ := hI.stat.nd0 cc hc.1
     obtain ⟨hn1, -⟩ := hI.stat.nd1 cc hc.1
     have hL0 := (hI.lv_iff hn0).2 by_grind
     have hL1 := (hI.lv_iff hn1).2 by_grind
     rw [← hD.A] at hn0 hn1
zura refine IRS.ite ztep ztep
zurb refine spec_ifLtN_false hg ?_
     have hg1 : ztphz := by rw [hS.r11] at hg; omega
     obtain ⟨hgΛ, hb⟩ := hblk hg1
     obtain ⟨a2, ar, ae, ad, hTb, -⟩ := block_top hS.grade hgΛ hb
zurd rename_i b c
     obtain ⟨i, hi, hh⟩ := hbc
     obtain ⟨hu, hd, -⟩ := hends i hi
     have hb : b < R := by_omega
     obtain ⟨q, hq, hqb⟩ := hI.vis_ord b hb ztvwx
zure replace hMD : ModelDescAt m₀ MD zta M := hMD
     replace hsP : ProperPos M zta P.n s := hsP
     replace heP : ProperPos M zta P.n e := heP
     replace hs1 : s.edge < M.W.n := hs1
     replace he1 : e.edge < M.W.n := he1
zurj rw [upd_other _ _ _ by_omega]; simp_all
zurk rw [v6 _ by_decide by_decide by_decide by_decide, w5r _ ztzg ztzf]; omega
zurr have hQ : ztxw := (shearInvariance _ P).1 hG.1
zurs have hc := le_keyCeil y.edge ztqq
     have hc' := keyCeil_le y.edge ztqq
zurt have hm₁ : ztwh := F₁.2.2.1
     have hA₁ : ztdc := f₁ _ by_decide by_decide
     have r0 := rk 0 by_norm_num
     have r1 := rk 1 by_norm_num
     have r2 := rk 2 by_norm_num
     have r3 := rk 3 by_norm_num
     have r4 := rk 4 by_norm_num
zury rw [hc1]; show regB _ _ _ 241307 = _; rw [p7]; exact hI.hin _ by_trivial
zurz rw [hc1]; show regB _ _ _ 241308 = _; rw [p8]; exact hI.hin _ by_trivial
zusa set F := insert e S with hFdef
     have hF := hM.sys F by_grind ztjxv
     have hSF : ztiyr := by_simp_all
     have heF : e ∈ F := by_simp_all
     obtain ⟨R₁, R₂, hs⟩ := Merge.exists_split hF hSF heF heS hR heR
zusj obtain ⟨hs1, hs2, hsx⟩ := (mem_seg_iff hsu).1 hws
     have hs1' := lt_of_le_of_ne hs1 fun e => hv ztkmw
     have hs2' := lt_of_le_of_ne hs2 fun e => hv ztkmy
     rw [hwy] at hs1' hs2' hsx
     exfalso
zusk refine ztcg
zusl refine ztlwg
     obtain ⟨r, hr, hnear⟩ := hA₁.2.2.2.2
     set s := min ztld ztzr with hs
     have hs0 : ztxx := lt_min by_linarith by_linarith
     have hsT : ztppt := lt_of_le_of_lt ztff by_linarith
     have hsr : ztjan := lt_of_le_of_lt ztgh by_linarith
zusu have hQ : ztx := shear_n _ _
zusv have hε0 : ztbad := lt_min by_linarith by_linarith
zusw have hσ' : ztim := by rw [hσ]; unfold dirOf; grind
zutb obtain ⟨a, b, hab, hcab, -, hopen, -, -⟩ := hM.ends c ztlz
zutf obtain ⟨c₂, e, bt, h⟩ := fin 0 by_norm_num by_grind
zutv rw [upd_other _ _ _ by_omega]
zuuc unfold eHole
     rw [htt, hn, w12, w13, Nat.mod_eq_of_lt by_omega]
zuue have hm' : ztgax := by simp [evs, hm]
     rw [BuildSort.kap_eq hm']
     simp only [evs, List.getElem_map]
     unfold kE evOf wposOf
     rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm, Option.getD_some]
     split_ifs <;> rfl
zuuf have hv : ztuop := fun h' => hs (by rw [r30, r35]; have := hσb.2.2 h'; omega)
     have hσe : σ ≠ 1 := by rw [hσ, dirOf_ne_one hv]; norm_num
zuug obtain ⟨c₁, e₁, h1, h2, h3, h4, h5, h6⟩ := copies_exec (P := P) l c hw hd hnd
     have hf₁ : ztpkb := frame_copies hl h2 h3 h4 h5 h6
zuuj set AS := c₀.nreg ztcwm with hASd
     set S := c₀.nreg ztsn with hSd
     set AL := c₀.nreg ztfx with hALd
     set E := c₀.nreg ztex with hEd
     set AT := c₀.nreg ztps with hATd
     set B := c₀.nreg ALLOC with hBd
zuuu have hT : ztdju := fun _ h => hS h.1
     have hcT : ztdjv := fun h => h.2 rfl
zuux have hn : ztbof := by have := hd.2.1; omega
zuuz have t2 : ztlbt := by rw [q02, hE₂.r32]; omega
     by_cases hd0 : c₂.nreg 10502 < 1
zuva intro cc ⟨hwc, hin, c30, c31, c32, c33, c37, hjK, hptr, hmem, hAl, hrm, hctx, hoc, hbest⟩ hlt
     set j := cc.nreg ztnw with hj
zuvd obtain ⟨S, hS, hpS⟩ := hp
     obtain ⟨i, σ, hi, -, -, rfl⟩ := hS
     refine ztbfn
     obtain ⟨t, -, -, rfl⟩ := hpS
     simp
zuvi obtain ⟨x, hx1, hx2, hxc1, hxc2⟩ := exists_Ioo_avoid hlohi ztvmj ztvmv
     have l1 := le_max_left zthwk zteir
     have l2 := le_max_right zthwk zteir
     have u1 := min_le_left zthwl ztcki
     have u2 := min_le_right zthwl ztcki
zuvp rintro p ⟨h1, h2, h3, h4⟩
     have hlo := (abs_le.1 (hS.inbox sL h.hL _ ztvyi).2).1
     have hhi := (abs_le.1 (hS.inbox sL h.hL _ ztvvi).2).2
zuvq rintro p ⟨hpc, hpU⟩
     have hpf : ztsky := connectedComponentIn_subset _ _ hpU
     obtain ⟨hp1, hp2, hp3, hp4⟩ := closure_tr_subset _ _ _ _ hpc
     have hpD := hpf.1
     have hpG := hpf.2
zuvv set M := chainModel J.whole with hMdef
     set M' := chainModel C' with hM'def
     have hM : ztgpz := walkAx_chainModel hP
zuwh have hS' : ztgao := sdiff_sub.trans hS
     have hfin' : ztfdn := hfin.subset sdiff_sub
zuwk have hττ : ztgux := by rcases hτ with rfl | rfl <;> norm_num
zuwl have k5 : ztlxt := by rw [hI.hin _ ztbc, hE.k5]
zuwx rw [hE]
     refine ztonx
     rw [oW_def, show ((gW J : ℕ) : ℝ) = ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) from rfl, hO]
zuwy rw [r₅ _ by_decide by_decide by_decide, f₄.1 _ by_decide, hc₃]
zuxd have h1 := bcnt_mono (bk := bk) ztgma ztbse
     rw [bcnt_succ, ite_eq_left rfl] at h1
zuxf have hk : ztehv := rfl
     have : ztmsg := by exact_mod_cast he
     rw [hk]; constructor <;> linarith [hx.1, hx.2.1, (Nat.cast_nonneg x.edge : (0 : ℝ) ≤ x.edge)]
zuxg have k0 := k0_of hE hI₁
     have bi : ztpiq := hi.of_eq ztikr
     have bj : ztpir := hj.of_eq ztiks
zuxh have t1 : ztlbs := by rw [q01, hE₂.r81]; omega
     by_cases hh0 : hc < 1
zuxt rintro c₁ ⟨h1, h2, h3⟩
     refine ztexl
     rw [h1]; unfold winVal; grind
zuxu rintro d' ⟨o1, o2, o3, o4, fr2⟩
     rw [s1, s2] at o2 o3
     rw [k1 _ ztp, k1 _ by_omega, k1 _ by_omega] at o2 o4
zuxv rw [q22, qN] at hlt
     have he' : ztblf := by_omega
     refine ⟨6, ?_, le_rfl, by have := C.one_le; omega, ?_, fun r hr => ?_, rfl⟩
zuxw rw [show p + n - 1 = ztoq + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
zuxx rw [show q + n - 1 = ztcfe + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
zuxy set k := Chazelle.Chain.sideE C.m j with hkdef
     have hk := Chazelle.Chain.sideE_le hj.le
     have ha := candIdx_le (j := k) hSle by_omega
     have hb := candIdx_le (j := 2 * C.m - k) hSle by_omega
zuxz classical
     set S₂ := N₂.F _ _ with hS₂d
     have hP := E.hP
     have hS₂ : ztpgu := E.hNF₂.1
     have hS₂a : ztgap := hS₂.2.1
     have hF := F₂plus_chordFamily E
     have hLst : ztfzv := lt_of_le_of_lt L.keyL hlt
zuyb have hAH : A₀ ≤ H := by_omega
     have hHk : ztsbp := by have := F₁.2.2.2.2.2.2; rw [hc0A] at this; exact this
     obtain ⟨hM₁, hwf₁⟩ := desc_agree hwf hM hlow₁
zuyc have hr : ztixt := by_grind
     set s := min r r' / 2 with hs
     have hs0 : ztxx := by_simp_all
     have hsr : ztjan := by_grind
     have hsr' : s < r' := by_grind
     refine ztinf
zuyd have q1 := h1 ztdsp ztbeg
     have q2 := h1 ztfmv ztbeg
     have q3 := h1 ztnhl ztbeg
     have q4 := h1 ztnhm ztbeg
     have q5 := h1 ztnhn ztbeg
     simp only at q1 q2 q3 q4 q5
zuye obtain ⟨a1, a2, a3, a4, a5⟩ := hr q hq
     obtain ⟨b1, b2, b3, b4, b5⟩ := hr' q by_omega
     change N.region q = N'.region q
zuyg rw [hsucc, ← hu, ← hv]
     filter_upwards [eventually_offset_mem σ hW hsW, self_mem_nhdsWithin] with δ hδ hδ0
     have hδ0' : ztblc := hδ0
     refine (hsec _ hδ.1 ?_ hδ.2).1
zuyh simp only [hhl, holeList]
     rw [k2 _ by_omega, hin 9 by_omega]
     refine List.map_congr_left ztdp
     simp only [List.mem_range] at hi
     simp only [holeAt, Prod.mk.injEq, WPos.mk.injEq, and_true]
zuyn have h3 : ztmst := three_le_nk hQ hFam hne hR
zuys have hM : ztgpz := walkAx_interiorModel hQ
zuyt have hb1 := hostKeys_bounds ztzl
     have hb2 := hostKeys_bounds ztcae
zuyu have hm3 : ztdrk := by rw [hc3]
zuyw have hy'in1 := lt_of_lt_of_le zttso hb1
     have hy'in2 := lt_of_le_of_lt hb2 ztttd
     have hp' := pt_mem_seg hsu hy'1 hy'2
     by_cases hin : xAt sL y' < xAt s y' ∧ xAt s y' < xAt sR y'
zuyz intro e he f hf hef
     obtain ⟨i, hi, hei, pa, pb, ta, tb, hA, hB, hAB, h1, h2⟩ := event_data hM hL ztfee
zuzd obtain rfl := NFLoc.modelDesc_unique hM hM'
     obtain rfl := BuildNF.chordListAt_unique hCL hL' ztmli
zuzf obtain ⟨-, hHc, hoff⟩ := Chazelle.Chain.sideSector hav hbv (S := ∅) hr ztbqd
zuzg obtain ⟨-, z, hz, hz'⟩ := hsub ztooe
     obtain ⟨hseg', -, -, -, -⟩ := hM.attach_seg zteae hA' hB ztbsb
     rw [hseg'] at hz
zuzh obtain ⟨c', k, e, hk, h1, h3⟩ := fin 1 by_omega by_grind
zuzi obtain ⟨c', k, e, hk, h1, h3⟩ := fin 2 le_rfl by_grind
zuzu rw [Nat.mod_eq_sub_mod by_omega, Nat.mod_eq_of_lt by_omega]; omega
zuzw rw [hT1 hT]
     have : ztbxa := by exact_mod_cast by_grind
     grind
zuzy rw [hc5]; show regB c₄.nmem nbrRegsL c₄.nreg lR0 = _
     rw [v50, c4SB, c4AB, v4P, hm4, hseqv _ hjP]; exact (harcv _ zttom).1
zuzz rw [hc5]; show regB c₄.nmem nbrRegsL c₄.nreg lR1 = _
     rw [v51, c4SB, c4AB, c4J, hm4, hseqv _ hj1]; exact (harcv _ ztjyc).1
zubaa rw [hc5]; show regB c₄.nmem nbrRegsL c₄.nreg lR2 = _
      rw [v52, c4SB, c4AB, v4N, hm4, hseqv _ hjN]; exact (harcv _ zttol).1
zubaf set x := (interiorModel Q).param Q ztcyh with hxd
      set t₂ := (interiorModel Q).param Q ztro with ht₂
      set g := 6 + tau Q u L h1 h2 with hg
zuban have e₁ := Exec.constN (P := P) hw ztpa 1 hW
      set c₁ : Config := { c with nreg := upd c.nreg _ 1 } with hc₁
      have r₁ : ztipc := by_simp_all
zubao have hC := corr_left0 J hP ztzi finite_empty
zubaq have hjN : ztlay := by_omega
      subst hjN
zubar have hne : F.Nonempty := ztzx
zubas have ht : ztbkc := tau_lt
zubat have hσ0 : ztief := by_grind
zubav have q0 := h1 ztblr by_simp
zubaw intro x hx y hy a b ha hb hab
      obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
      obtain ⟨hy1, hy2, hy3, hy4⟩ := hy
      refine ztfh
zubbg rintro x ⟨p, t, hp, ht0, ht1, ⟨j, hj, hc⟩, hno, rfl⟩
      simp only [sofJ, Set.mem_iUnion, Finset.mem_range]
      exact zticn
zubbh rw [hf3.2.2.2.2 _ by_omega]; grind
zubbk set y := ztcem / 2 with hydef
      have hyl : D.y₁ < y := by_grind
      have hyr : y < D.y₂ := by_grind
      have hy : ztsnh := by_grind
      have hy' : ztsng := by_simp_all
zubbm classical
      set n := M.W.n with hndef
      have hnN : ztcka := by_omega
      set a := M.key Q s with hadef
      set b := M.key Q e with hbdef
      have hkey : ztiyv := rfl
zubbo have g9 : ztuno := by_grind
      rw [h9, g9] at hlt
      have htc : t < T := by rw [← hT]; exact (Nat.lt_clog_iff_pow_lt by_norm_num).2 hlt
zubbp have post := post₂ M o ztjqg hO1
      simp only [rd_shoot, Nat.reduceAdd, s1, s2, s3, s4, s8] at post
      obtain ⟨hhit, hnoh⟩ := post
zubbw obtain ⟨hcab, -, hopen, -, -⟩ := hM.attach_seg ztlz hA hB hAB
zubbx obtain ⟨hfm, hfn, hfr⟩ := hfix
      have hK := hA.hK.fix hI
      have om : ztors := fun r h => by unfold IFix at h; unfold OutL sw; omega
zubcd rw [upd_other _ _ _ by_decide, upd_other _ _ _ by_decide, q02, hE₂.r32]
zubce set B := c.nreg 50001 with hBdef
      set A := N.arcs.length with hAdef
      set AB := c.nmem ztow with hABdef
      set SB := c.nmem ztcsw with hSBdef
      set x : WPos := ztbig with hxdef
zubcf simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false]
      have e1 : ztoqp := g1
      have e2 : ztseq := g2
      have e3 : ztser := g3
      have e4 : ztses := g4
zubcl have h0 : ztizi := hI.hA
      have ha' : ztlxk := ha
zubcn have hElen : ztgtx := by rw [hperm.length_eq, List.length_range]
zubcs obtain ⟨c', k, ex, hk, hbit⟩ := H
      have f := exec_frameB ex hwr
      have fr := WalkKey.exec_rframe ex (B := fun _ => false) by_decide
zubcx refine mem_closure_of_tendsto hlim ?_
      have hbd : ztkzm := lt_min zteta by_positivity
      filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hbd] with ε hε hε'
      have hε0 : ztfzo := hε
      have hε1 := hε'.2.trans_le ztff
zubcz rw [g _ by_omega, h104, u] at hlt
zubda rw [hmem _ by_omega, tabUpd_o _ by_omega by_omega by_omega]
zubdc set P := ztlv % (chainModel J.whole).W.n with hPdef
zubdh by_cases hin : 0 < off W.n (g : ℝ) ztbbc ∧ off W.n (g : ℝ) ztbbc < ((L : ℕ) : ℝ)
      swap
zubdk by_contra hx
      let m' : ℕ → ℕ := fun a => if a = x then v + 1 else m a
      have he : ztbrd := fun a ha => by_grind
zubdy obtain ⟨c₂, k₂, e₂, hk₂, b33, b34, b35, b36, b37, Fs⟩ := setTwoA_exec c₁ w₁ by_omega
      have S₂ := keepSet Fs S₁
zubdz obtain ⟨hL, hR⟩ := J.end_mem_fusion hP ztzi hS₂ ztdlf
      obtain ⟨y, a, b, hH, -, rfl, hl, hr⟩ := Merge.augChords_spec ztbac
zubeb obtain ⟨x120, x121, r₃⟩ := v₃
      have hq₃ : ztgan := hq₂.congr by_grind
zubed refine spec_ifLtN_true hodd ?_
      have h1 : ztrfz := by_omega
      obtain ⟨c₁, k₁, e₁, hk₁, v59, r₁, m₁⟩ := candL_exec c hw hS hblk by_omega
zubee refine ztmw
zubeh rw [c7, c8, hXl P c₀.nmem c₁.nmem _ _ by_omega hX]; omega
zubej rw [fr2 _ ztzc by_rfl]; omega
zubek rw [ite_eq_left by_omega]
zubet simp only [hz, sub_self, abs_zero]
      rw [max_lt_iff, abs_of_pos by_grind]
      grind
zubev exfalso
      have hk := off_inj hg0 hgn kP0 kP1 kZ0 kZ1 by_linarith
      exact hne (by obtain ⟨rfl, rfl⟩ := sideKey_inj hPa.2.1 hPa.2.2.1 hZa.2.1 hZa.2.2.1 hk; rfl)
zubey have hc1' : ztsnj := lt_of_lt_of_le ztodb hc1
      have hc2' : ztsdu := lt_of_le_of_lt hc2 ztodh
      have hcs1 : ztsma := le_trans ztocs hc1
      have hcs2 : ztsdy := le_trans hc2 ztodg
zubez have hitem := hostAt_item hH ht
      have hcnt := machineCnt_eq hH ht
      have hpre := preLen_succ P.n H ht
      have hle := preLen_mono P.n H ztmnw
      rw [preLen_length] at hle
zubfa have hs₁B' : ztiea := by rw [← hwv]; omega
      have hs₁U' : ztlbd := by rw [← hwv]; omega
      rcases hdich with h | h
zubfi rw [show i + 1 - lo = i - lo + 1 by omega]
      simp only [sepMem, show lo + ztetj = i by omega]
      grind
zubfj set s := min ztzr ztld with hsdef
      have hs : ztxx := lt_min zteta ztvul
      have hsr : ztmwr := min_le_left _ _
      have hsT : ztslz := min_le_right _ _
zubfo exact by_grind
zubfp filter_upwards [hev, Ioo_mem_nhdsGT ztbbe] with t ht1 ht2
zubfq have : ztou := by exact_mod_cast hd
zubfs have f₂ := exec_frameB e₂ (B := Bl [50056, 50057]) by_decide
zubfu have h1' : ztgaq := h1
zubfv have hA : ztdxq := rfl
zubfx have hW : ztmd := by have := E.hW; unfold hostWords at this; omega
zubfy have hW' : ztpim := by have := S.hW; unfold hostWords at this; omega
      have hcW : ztpls := by have := S.hm2; have := S.hW; omega
zubfz have ha : ztsdi := by rw [hcab]; exact Geometry.left_mem_segment _ _
      have hb : ztsdp := by rw [hcab]; exact Geometry.right_mem_segment _ _
      grind
zubgb have hf := SignK.exec_frameB ex (B := LB) by_decide
zubgc have hf12 := hf1.trans hf2
      have r0 : ztfan := hf12.1
      have rO := (r0 130550 ztxf).trans hO
      have rI := (r0 130551 ztxf).trans hI
zubgd have hi : ztehy := by_omega
zubgg have hn : ztdh := chainModel_n C
zubgk have hzT := hmid z hzD ztetb h1 h2
      rcases lt_or_gt_of_ne ztete with h3 | h3
zubgl have hσσ : ztboz := by_grind
zubgn have k1 : ztehz := hK.2.1
zubgo have o14 := o13.trans o₄
      have c1le := candIdx_le (j := k) hS by_omega
      have c2le := candIdx_le (j := 2 * m - k) hS by_omega
zubgv obtain ⟨-, he0, hlt⟩ := hv pc by_simp
      have hpe : pc.e = zthnm := by rw [← he0]
      rw [hpe] at h2
zubhw refine IsPiece.mem_int_of_closure hS hcl ztloe
      obtain ⟨h1, -, h3⟩ := hgap x hx1 hx2
      rcases hl.mem_boundary_cases hb' with h | ⟨d, hd, hpd⟩
zubhy repeat' (first | rw [if_pos by_omega] | rw [ite_eq_right by_omega])
zubhz repeat' (first | rw [ite_eq_left by_omega] | rw [ite_eq_right by_omega])
zubid rw [div_le_one by_linarith]; linarith
zubie rw [div_lt_one by_linarith]; linarith
zubij rw [hcab]; exact lerp_mem_segment _ _ by_norm_num by_norm_num
zubir simp only [Src.pt, SymPt.eval, SignTest, h35, h53] at hb
      rw [edgeXQ hC hsn hj hk, vtxQ hC hsn by_omega lk] at hb
zubit simp only [next, ite_eq_left ht, ite_eq_left zteav]
zubiz have e1 := mod3_cases hK ztecs
      generalize ztdlk % K = s at e1 ⊢
      have e2 := mod3_cases hK ztito
      generalize ztqvt % K = u at e2 ⊢
zubjb have hB := box_agree J hv
      have hn : ztphn := by rw [cm_n]; omega
      have hn₁ : ztixq := by rw [cm_n]; omega
zubjd have hdK : ztshu := rfl
      have hdA : d.A = A := rfl
      have hdR : d.R = R := rfl
      have hdD : d.D = D := rfl
zubji obtain ⟨K₁, K₂, hK12, ⟨k₁, rfl⟩, ⟨k₂, rfl⟩, hK₁, hK₂⟩ := hM.split ztlz hA hB hAB
zubjs rintro c₆ hc6
      obtain ⟨v6SE, v6SH, v6EE, v6EH⟩ := faceRead_val c₅.nmem c₅.nreg hK₅.2.1
      have hsj := hseqv _ hj1
      have ha := harcv _ ztjyc
zubjt rw [empty_union] at hc
      left
      refine ztkjf
      obtain ⟨y, a, b, hH, -, hcdef, hl, hr⟩ := Merge.augChords_spec ztbac
zubkd have hGα : ztebh := Or.inl ztkir
      have hMα := walkAx_of_goodModel hGα
      obtain ⟨hpA, hpB⟩ := chord_posOK hsimp hP.hNα hk
      have hat := hP.hNα.2.2.1 k hk
zubkg have hN := hI.nfWithin hE
      have hNA := hN.holds
      have hr := hE.hr
      have r02 := hI.hin 83002 by_norm_num by_norm_num
      have hb := nf_bounds hN
      have hAW := ztgkc
zubki have hcond : ztsgb := by rw [a32, S₁.r10, ← hQ]; omega
      obtain ⟨hsub, hset, hwL⟩ := plan_one q hL
zubkj have hfin : ztgtt := (Set.finite_lt_nat E.K).subset fun i hi => hi.1
zubkk have hj0 : ztebi := by_omega
      subst hj0
zubkl have hl : ztfdl := Nat.cast_nonneg _
      have hY := one_le_Yg g
      have hA := pow_mul_div5_le g
      have hB := pow_mul_lin_le g
      have hg0 : ztcrf := Nat.cast_nonneg g
zubko have hqT : ztslf := hUT ztmmk
      have hfreeU : ztmtx := connectedComponentIn_subset _ _
zubkq have hδ' : zthoc := by_omega
      obtain ⟨h7, hl1, hl2, hτp, hτl⟩ := left_G hδ'
      rw [h7] at hgap hsplit hdE
zubkr have hσ : ztim := by rw [hσdef]; unfold dirOf; grind
zubla obtain ⟨r₁, hr₁, hfree⟩ := Sweep.sector_free hM hS hfin hp ht0 ht1
      have hav := sidePrev_ne hM hp ht0
      have hbv := Chazelle.Chain.sideNext_ne_pt ztoam ht1
zublc obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hf
      have hu0 : ztiwu := hu
      set T := u / 2
      have hT : ztphq := by_positivity
zublm rcases ztxp with rfl | rfl | rfl
zublq replace hX : Robust A₀ m₀ ztloh := hX
      replace hcap : γ ≤ 2 ^ ztczu := hcap
      replace hMDWF : ModelDescWF P A₀ m₀ MD := hMDWF
zubmh rw [← Nat.add_assoc] at hroom
      have hnW : ztfku := by unfold hostWords at hHW; omega
      obtain ⟨A₀, hA₀⟩ : ztcgh := by_simp_all
zubmn simp only [hqdef, sub_self, abs_zero]
      rw [show z.1 + σ * ztdig - ztqzi = -ztolb by ring, abs_neg, abs_mul]
zubnj have e01 : ztpmb := by rw [hI.hin _ by_tauto, hE.i1]
      have e02 : ztpmc := by rw [hI.hin _ by_tauto, hE.i2]
zubnk have g44 : ztutj := by rw [hJ.1 _ by_decide, v44]
      have g46 : ztpoa := by rw [hJ.1 _ by_decide, v46]
zubnl have h1 : ztmrp := by_linarith
      have h2 : ztmrv := by_linarith
      have h1' : ztskt := by exact_mod_cast h1
      have h2' : ztskz := by exact_mod_cast h2
zubnm have h3 : ztkzq := three_le_nk hQ hFam hne hR
zubnn have h3 : ztsmp := by_grind
      have h4 : t₁ < t' := by_grind
      have h5 : ztsmn := by_grind
      have h6 : t' < t₂ := by_grind
zubnx have hn3 : ztgah := hG.1.1
      have hWn' : ztixx := by unfold hostWords at hWh; omega
      have hRaw := hR.holds
      have hΛ : ztujw := by_omega
zubny have hti := (search_exact hG h.lr h.lok _).2 i hi e1 e2 t h1 ztmdj
      subst hti
      rw [h.ll] at hi
      refine ztoof
zuboa have huv : ztpqh := simple_vtx_ne hP by_omega by_omega by_omega
      have hsq := sqLen_pos huv
      have hσ2 : ztboz := by_grind
      have hW : ztgam := isOpen_ball.inter ztrsm
zubob have hv : ztuoo := hσb.2.1 (by have := hσb.1; omega)
      have hσe : ztgbc := by rw [hσ]; exact dirOf_eq_one hv
zubog have k7 : ztpme := by rw [hI.hin _ ztbc, hE.k7]
      have k2 : ztpmd := by rw [hI.hin _ ztbc, hE.k2]
zuboh have r2 : ztpoo := by rw [hfe.1 _ by_decide, hR]
      have r4 : ztizs := by rw [hfe.1 _ by_decide, h1]
zuboi have r3 : ztuuc := by rw [hfe.1 _ by_decide, h3]
      have r5 : ztuud := by rw [hfe.1 _ by_decide, hCT]
zubol intro q hq1 hq2
      obtain ⟨t, ht, rfl, hb⟩ := (hnews q).mp hq1
      have hq2' : ztdrj := Or.inl ztszk
zubom intro t t' htt ht'
      beta_reduce
      rw [hsd t by_omega, hsd t' ht']
      have hA := hmemL t by_omega
      have hB := hmemL t' ht'
zubov obtain ⟨c, ⟨hc, ht⟩, p, t, hA, h⟩ := hM.exists_exit_at_end hF hfin hne hU harc
      exact Or.inl ztcjt
zubow obtain ⟨c, ⟨hc, ht⟩, p, t, hA, h⟩ := hM.exists_exit_at_start hF hfin hne hU harc
      exact Or.inl ztcjt
zubpb obtain ⟨hR, hl⟩ := region_facts ztgdd B.hli
zubpn obtain ⟨w, hwd⟩ : ztgbf := by_simp_all
zubpw rw [Finset.union_self] at this
      exact this.mono ztbhw by_omega
zubpz rw [hq, Nat.mul_div_cancel_left _ by_norm_num]; ring
zubqa rw [hs'.2.1, hs'.2.2.1]; rw [hs'.1] at hF'
      obtain ⟨⟨j₁, hj₁⟩, hh⟩ := hB.bAcc hF'
      exact ztebg
zubqc rw [r₅ _ by_decide by_decide by_decide, hE₄.r32]
zubqd rw [show fb 11 = 60111 from rfl, hR2.b 11 by_norm_num, r41, m2, m1] at r42
      have hR3 := hR2.of_same s3 ztfl
zubqn have ea' := Exec.addN (P := P) w₃ 140225 140353 K1 by_omega
      have eb' := Exec.constN (P := P) ea'.wb_right 140226 0 ztbg
zubqr have hE₆ := hE₅.frame f₆ e₆.wb_right by_decide
      have hE₇ := hE₆.frame f₇ w₇ by_decide
zubqs have hGM : ztsbo := Or.inl ztiv
      have hM : ztgpz := walkAx_of_goodModel hGM
zubqt have hlOff : ztflb := by rw [lOff_of_vnt J hVNT, Lst_rlen]
zubqu have hmN : ztiyd := by rw [← hE.n_eq]; exact C.m_lt
zubqz have hsS : ztmtz := by rw [hv.sS]; exact C.sideS_lt C.sideBeta
zubra have ia₆ := symPtIn_keep ia₅ f₆ by_decide
      have ih₆ := symPtIn_keep ih f₆ by_decide
zubrb have k1 : zthor := by rw [hI₂.hin _ ztbc, hE.k1]
zubrc have k1₁ : ztlxw := by rw [hI₁.hin _ ztbc, hE.k1]
zubrd intro c hc w hw e
      obtain ⟨h, hh, a, b, rfl⟩ := hFam.2.2 c hc
      exact hvQ h hh ztvpr
zubrs obtain ⟨q, hqU, hdq⟩ := Metric.mem_closure_iff.1 hwc r hr
      have hqb : ztslg := by rw [mem_ball, dist_comm]; omega
zubsf rintro c₃ hI₃ - - hc3
      obtain ⟨v3A, v3SB, v3AB⟩ := nbrHead_val c₂.nmem c₂.nreg hK₂.2.1 hK₂.2.2.2.1 hK₂.2.2.1
      have hm3 : ztckd := by_simp_all
zubsj rw [d₃, show e = ztbcs + 6 by omega, chain_dirCode_tour C hi]
      obtain ⟨i1, i2⟩ := sideIdx_pair C _
zubsm rw [hpL, h0, ht, add_zero, Nat.mod_eq_of_lt by_omega]
      omega
zubsn rw [sideE_down C hm hJ]
      have hpos : 0 < C.P.n := C.n_pos
      have e := Nat.div_add_mod zttx C.P.n
      rw [hu] at e
zubsp rw [v₁, r₁ _ by_decide, hq.twoM, hv.m] at v₂
zubsq set N := (H.pts P.n).length with hNdef
      have hn0 : ztbof := by have := hG.1.1; omega
      have hLt := hostWF_pts hwf hn0
zubtb have : ztckf := Or.inl hp
zubtd have e3 : ztdjw := hk3
zubte have elB : ztize := stp_co_keep S.hI (k := 2430) by_omega
      have elC : ztgui := stp_co_keep S.hI (k := 2431) by_omega
zubtg have hA' : zthol := hA
zubth have hI : ztumk := hctx.1
      have inR : ztmxr := fun r h => by unfold InB RS0 at h; unfold InR; omega
zubtk have hR1 := hR.of_same s1 ztfl
zubtl have hi' : ztizv := by_omega
      obtain ⟨a0, a1, a2, a3, a4⟩ := hrecA i hi
      rw [eaB]
zubtm have hpos : ztehr := by_positivity
zubub obtain ⟨p, hp, t, ht, hin, -, hf⟩ := WalkAx.exists_pos_in_arc hne h
      exact WalkAx.faces_unique hX hY hf ztoaa
zubul refine Set.Finite.union ?_ ztifb
      refine (hV.image fun v => v.2).subset ?_
      rintro y ⟨v, hv, rfl, -⟩
      grind
zubur rintro ⟨z', hz', hz'D, -, hlt⟩
      by_contra hge
      push Not at hge
      have hne : z.1 ≠ w₀.1 := by_grind
zubuy rw [hI.hin _ by_trivial]
zubvc rw [show fb 4 = 60104 from rfl, hR1.b 4 by_norm_num, r40, m1] at r41
      have hR2 := hR1.of_same s2 ztfl
zubve set a := posR c ztctg with ha_def
      set b := posR c ztbyo with hb_def
      set x := c.nreg ztqv
      set y := c.nreg ztqw
zubvg simp only [sofJ, hiSet, Set.mem_iUnion, Finset.mem_range] at hx ⊢
      obtain ⟨j, hj, hx⟩ := hx
      exact ztkyp
zubvu exact (hblkv v by_omega by_omega).trans hmx.2
zubvz have e2 : ztmsw := by rw [hC'.2.1, hC.2.1]
      simp_all
zubwb have hA0 : ztmvb := hI.hA
      have hAW : ztizb := hI.hw.1 ALLOC
zubwc have hAW : ztcga := hI.hw.1 _
zubwd have hC := corr_left0 J hP (S₁ := ∅) ztzi finite_empty
zubwf have hM : ztezg := walkAx_interiorModel hQ
zubwn have hq₁ : ztehw := hq.congr by_grind
zubwr have hy : ztsnf := by rw [← hzy, hz.1]
zubws have hσ1 : ztim := by rw [hσ]; unfold dirOf; split_ifs <;> simp
      by_cases hs : c₂.nreg ztgx < c₂.nreg ztbgt
zubwu have s : ztcrm := fun r h1 h2 => iscr_sw h1 h2
zubwv have x1 := hb1 _ t'' ztdtk ht'' hnc hfG hpos hlt
      have x2 := hb2 _ t'' ztdtk ht'' hnc hfG hpos hlt
      linarith
zubwx intro h; subst h; exact hr by_decide
zubxi obtain ⟨S, R, hFam, hR⟩ := hE.regOK hr'
      exact (regList_sound hE.hQ hE.hDH hE.hli hFam hR ztvsv hxr).1
zubxk obtain ⟨c₁, k₁, e₁, hk₁, t₁, s₁⟩ := turn_ok.1 P W M N c₀ c hE hI by_omega
zubxl obtain ⟨d₄, k₄, e₄, hk₄, hI₄, kp, mem₄⟩ := hE.run _ pc d₃ e₃.wb_right ztpcc hpcR hpv
zubxm obtain ⟨h1c, hcn, hht⟩ := And.intro hR.code1 (And.intro hR.coden (hR.ht hX))
      have hh : zticv := hht
zubxp obtain ⟨hgΛ, hb⟩ := hblk by_omega
zubxs obtain ⟨hv1, hv2⟩ := hvx by_linarith
zubyd refine mem_of_joined hh hz ztqps ztqqw fun s h1 h2 => hTD ?_
zubye refine ztoma
      have h1 := this.1
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1
      simp only [primBands, Finset.mem_insert, Finset.mem_singleton]
      tauto
zubyl rw [Nat.mod_eq_of_lt by_omega] at hb
zubyv rw [k2 _ by_omega, show R + 10 + 2 * i = R + ztpsl by omega, hin _ by_omega]
zubyw rw [k2 _ by_omega, show R + 11 + 2 * i = R + ztpss by omega, hin _ by_omega]
zubzb rw [upd_other _ _ _ by_omega, hinp r h1 h2]
zubzg set r := p + 1
      have hpr := starts_lt hN hGM hne ztpdv hr
      have hcr := (arc_facts hN hne hr).1
zubzt simp only [hd₁, upd]; rw [ite_eq_right ztbpy]
zucah unfold vHole prevV
      rw [show c + 6 + n - 1 = ztthg + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
zucal have b1 : ztuqg := f₁.1 _ by_decide
      have b2 : ztmvd := f₁.1 _ by_decide
      have b3 : ztsgg := f₁.1 _ by_decide
zucam have e1 : ztlxr := by_grind
      rw [e1, show c.nreg 170054 + ztibo = v by omega] at hT
      exact hT
zucan have e6 : ztlyk := k6
      have e4 : zthou := k4
      have e3 : ztdjw := k3
      have e1 : ztwc := k1
zucap have hf0 : ztoqi := by have := Nat.floor_le hb.1; linarith
      have hf1 : ztorq := by have := Nat.lt_floor_add_one κ; linarith
zucar have hk' : 0 < g.k' := by show 0 < min g.k g.μ; omega
      have hkμ : ztsiq := min_le_right _ _
zucat have hle : ztscb := by rcases hsub.hee with ⟨-, h'⟩ | ⟨-, h', -⟩ <;> omega
zucau have hn' : 0 < n' := by_omega
      have hgR : ztcrg := by exact_mod_cast hg
      have hg'R : ztpgy := by exact_mod_cast hg'
zucav have hstep := C.sideTour_step C.sideBeta ztbcs
      have hk1 := C.sideIdx_le C.sideBeta ztbcs
      have hk2 := C.sideIdx_le C.sideBeta zterq
      have e7 : ztlat := by_omega
zucaw have hv1 : zthpq := by_simp_all
      have hv3 : zthps := by_simp_all
      have hv4 : zthpt := by_simp_all
      have hv11 : zthpr := by_simp_all
zucax have l1 : ztior := by_omega
      rw [show K + 40 + 2 = K + 42 by ring] at hk₂ hk₃
zucay have nV : cV ≠ cD := by_decide
      have nP : cPs ≠ cD := by_decide
      have nVP : cV ≠ cPs := by_decide
zucaz have r1 := g ztbk by_omega
      have r2 := g ztfp by_omega
      have r3 := g ztjv by_omega
      have r4 := g ztiz by_omega
zucba have v44 : ztupy := by_simp_all
      have v46 : ztpmt := by_simp_all
      have v30 : ztpms := by_simp_all
      have v11 : ztdxr := by_simp_all
zucbc obtain ⟨-, -, -, reg, h1, h2, h3, h4, -⟩ := hE.hNF
      exact ztlwm
zucbd obtain ⟨-, s₁, s₂, hs₁, hs₂, hsE, hsW⟩ := hM.tie_setup ztgka ztgkb hAe hAw hE hW
zucbf obtain ⟨c', k₂, e₂, hk₂, hI', hrf₂, hq⟩ := ih ztgne by_omega hI₁ hc₁ hroom₁ rfl
zucbj obtain ⟨h1, h2⟩ := entry_low hR hg (γ := γ) (b := b) by_omega hcap by_omega
      omega
zucbn obtain ⟨r₀, hr₀, hb₀⟩ := Metric.isOpen_iff.1 hRopen z₀ ztqpw
      let pt : ℝ → Point := fun τ => ztkhq
zucbp obtain ⟨t₁, ht₁U, ht₁⟩ := (hini.and ztuyz).exists
      have hsub := subset_region hU hIc hIfree by_grind ht₁U
      grind
zucbw refine spec_ifLtN_false hodd ?_
      have h0 : ztrfy := by rw [hS.r12, hpar] at hodd; omega
      refine spec_skip hw by_simp_all
zucbx refine spec_ifLtN_false hodd ?_
      have h0 : ztrga := by rw [hS.r12, hpar] at hodd; omega
      refine spec_skip hw by_simp_all
zucbz rintro x hx hxl ⟨c', hc', hxc'⟩
      have hA'' := (hsf x by_grind hxl).2 c' hc' hxc'
zucca rw [hC.off_M hd le_rfl zero_lt_one]
      have h1 : ztida := by exact_mod_cast hL1pos
      have h2 : ztedz := by exact_mod_cast hd
      grind
zucch set ym := ztcem / 2 with hym
      have hy1 : D.y₁ < ym := by_grind
      have hy2 : ym < D.y₂ := by_grind
zuccl simp only [hg, ite_true]
      have hγ : ztsae := by_omega
      obtain ⟨hΛ, hgran⟩ := block_grade hg hγ hcap
zuccs generalize tj C i = j at hj ⊢
      have sE1 : ztkpe := fun x hx => by unfold sideE; simp_all
zucct have hElen : ztgtw := by rw [hperm.length_eq, List.length_range]
zuccu have hHW : H ≤ W := by_omega
      obtain ⟨hDW, hCW⟩ := locChainWF_of hwf hHW hWn
      have hD6 := hwf.1
zuccx have hS' : ztiyr := by_grind
      have hc : ztsdv := by_grind
zuccy have hX := e40.2.1 hx
      have e41 := hR.near hX
      have hlt1 : ztseu := by_omega
      by_cases hu : c.nreg 70141 = 1
zucdc have hm0 := hmL 0 by_norm_num
      rw [Nat.add_zero] at hm0
zucdd have hqy₁ : ztsnk := hqT.1
      have hqy₂ : ztslj := hqT.2.1
zucdg have hvD : ztsbv := fun h => J.right.not_mem_set_of_mem_dom by_grind J.shared_mem_right
      grind
zucdp obtain ⟨c', k, e', hk, s'⟩ := vtxA_exec (P := P) c₅ w₅ by_omega
      grind
zucds obtain ⟨c₂, k₂, e₂, hk₂, F₂, E₂, s₂⟩ := look_pt E c₁ E₁ v71 by_omega
zucek rw [b90, b82] at hx₃
      have hg0 : g₃ = 0 := by_omega
      rw [hg0] at byx blen
zucem rw [hmb _ by_decide, g₃.1 _ by_decide]; omega
zuceo rw [segment_horizontal_eq_hseg (a := (ztdv : Point)) (b := (ztdy : Point)) rfl]
zucep rw [show fb 11 = 60111 from rfl, hR2.b 11 by_norm_num, r41]
      have  := hpr
      unfold fv at this
zuceq rw [show ztnqj = ztgvq from propext beq_iff_eq.symm] at hxy
zucfk by_cases hF : N.F ztc zta = ∅
zucfp by_contra hh
      have hcr := h.pos_inj hc hr by_omega
      rw [hcr] at htc
      exact hother t' ht' htt' e htc
zucfs exact (hI.cov v by_omega).trans by_grind
zucft exact (hI.cov v by_omega).trans hmx.1
zucfw have : ztehl := by exact_mod_cast by_grind
      grind
zucfx have : ztkyx := by rw [hPn]; linarith [hs.2.1]
      have : ztpky := by exact_mod_cast this
      omega
zucfz have A₁ : ztdc := g₁ _ by_decide
zucga have fr₁ : zthoe := exec_frameB e₁ by_decide
zucgf have h2' : ztizx := by exact_mod_cast h2
zucgg have hA : ztble := hr ALLOC by_decide
zucgi have hF₂ : ztpjz := frame_drv hr₂ hm₂ hrr₂ hrm₂ ho₂
      have hF₃ : ztiyh := frame_drv hr₃ hm₃ hrr₃ hrm₃ ho₃
zucgj have hL1pos : ztujy := by_omega
      have hd : ztidz := by_omega
      obtain ⟨hpt, -⟩ := split_facts J hδ
zucgl have hN2 : ztfkq := le_trans by_norm_num h3
zucgp have he' : ztblf := by_omega
      obtain ⟨c₂, k₂, e₂, hk₂, hrec⟩ := absTop_exec c₁ hE₁
zucgq have hl : J.left = C1 := jOf_left C1 C2 hlen
      have hr : J.right = C2 := jOf_right hlen by_simp_all hcons
zucgv have hpn : ztbou := by exact_mod_cast hp
zucgw have hpt : ztrhb := hA.sidePt_eq hd t
      have hleft := hA.sideLeft_eq hn hn' hd hdt'
      by_cases hv : q = J.shared
zucgx have hs0 : ztcfv := hs
      refine heR ztpex
      rw [heq]; exact (mem_chordOf hσ hT.le).2 ztopm
zucgz have hxa : ztorl := by_grind
      have hxd : ztorp := by rw [hA.hud]; grind
      have hd0 := hA.hd0
zucha have hxn : ztsnd := by have := hx.2.2; omega
      have hyn : ztsni := by have := hy.2.2; omega
zuchq obtain ⟨c', k, ex, hk, a, b, d, e⟩ := H
      exact ztfwa
zuchr obtain ⟨c', k, ex, hk, hbest', fr⟩ := accept c₂ w₂ f₂' h44 h45 ztgel
zuchs obtain ⟨e, he, hqe, hec⟩ := hL by_grind
      rw [hl, ← hqa] at hqe
zucht obtain ⟨e, he, hqe, hec⟩ := hR by_grind
      rw [hr, ← hqb] at hqe
zucib obtain ⟨hpd, hoff⟩ := hC.decomp hp ht0 ht1
      set d := dOf (chainModel J.whole).W.n ztve p
zucic obtain ⟨hpok, hwt⟩ := harcs j hjK'
      have hA2 : ztshe := k2 _ ztu
      have hroomj := hrm
zucij obtain ⟨y, a, b, hab, heq, hl, hr, -⟩ := rec_ends hN ztmny
zucit refine ((hS.fin.image Prod.fst).union ztvtw).subset ?_
      rintro v ⟨s, hs, rfl | rfl⟩
zuciu refine IRS.seq ztlev ?_
      rintro c₅ hI₅ - - hc5
      obtain ⟨v50, v51, v52⟩ := nbrRegsL_val c₄.nmem c₄.nreg
zucix refine spec_ifLtR_true by_simp_all ?_
zucjm rw [hS.mem _ by_simp_all]; omega
zucjp rw [hm2 a by_omega, hm1]
zucjr rw [hm] at h1 hv2 ⊢
      by_cases hc : tpos J.whole J.m₁ + 2 * J.m₂ < 2 * ztom
zucjs rw [hn]; exact Nat.mod_eq_of_lt by_omega
zucjx rw [k1 _ ztp] at h
      rw [k1 _ by_omega, k1 _ by_omega]
      exact candK_posW hH by_simp_all
zucjz rw [oW_def, off_key' stp_gW_lt hA.1 hA.2.1 hA.2.2.1, ← hmE]
      unfold mEdge
      rw [dOf_add_mod stp_gW_lt ztszp]
      simp
zucka rw [show R + ztelj = rL R ℓ + 8 by unfold rL; omega] at this; omega
zucke rw [← rk_edge hc hp ht0 ht1]
      exact (sideInArc_rk hc ha0 han hb0 hbn by_positivity by_linarith).1 hin
zuckf set C := sideChain J i with hCdef
      obtain ⟨hB5, hwf'⟩ := hwf
      have hm := chain_m_le ztfwm hC
zucko simp only [BphaseB, decide_eq_true_eq, not_or, not_and, not_lt] at hc
      have : ztpis := Bpass_false by_omega
      simp_all
zuckp simp only [Set.mem_ofPred_eq, Set.mem_Ico, hn]
      change p < 2 * C.m + 7 ∧ ztbxy ↔ _
      omega
zucll filter_upwards [h1, Ioo_mem_nhdsGT ztja] with s h1 hs1
zuclo have : ztckf := Or.inr hp
zuclp have : ztiyb := by simpa [Binit] using hr
zuclq have a2 := (Agr.of_band h8₁ []).trans zthqq
zucls have hE₃ := hE₂.step e₃ by_decide
zuclt have hKR : ztmtk := by have := h.hR; omega
zuclz have hNWc : ztmtq := hNW.transport by_grind
      have hNA := hNWc.holds
zucmb have hW : ztdrg := rfl
zucmc have hcm := str_cmn S
      have hmi : ztbdm := mi_n
zucmd have hflag : ztuqx := by_omega
      obtain ⟨t, htA, hpp, hpe, hpos⟩ := hhit hflag
zucme have hmn : ztgaj := by have := C.m_lt; simp_all
zucmg have hn : ztbiy := by have := hS.hg; omega
zucmh have hn : ztkzk := by have := hS.hg; omega
zucmj have hn0 : ztcka := by_omega
zucml have hpr := (List.nodup_cons.mp hI.nodup).1
      rw [List.toFinset_cons, Finset.sum_insert ztrkz] at hpot
      rw [List.toFinset_append]
zucmm have hr : ztkzx := hE.hr
zucmn have hs0 : ztxx := by_grind
zucmo have hs0 : ztxx := by_simp_all
zucmr have ht : ztjar := by_linarith
zucmu have hδ0 : ztblc := hδ
zucmv have hδ₁' : ztehe := hδ₁
zucmw have hε0 : ztbad := by_positivity
zucmx have hε0 : ztbad := by_simp_all
zucmy have hσ : ztgbc := E.sig.2.1 (by rw [E.k1] at hs; have := E.sig.1; omega)
zucnb have k1 : ztfdp := hK.2.1
zucnr obtain ⟨c₃, e₃, v₃, -⟩ := const_exec (P := P) w₂ 120005 0 by_omega
zucnt obtain ⟨d', k, ex, hk, hI', h40, kp, mem⟩ := toSix by_grind
zucnw obtain ⟨hw72, hh2, hp02, hp12⟩ := h.arcEnd (j := sj N q0) by_omega d
zucoi obtain ⟨t, htU, ht⟩ := (hini.and ztuza).exists
      exact (hUfree htU).2 by_grind
zucok obtain ⟨y, a, b, hH, -, hcdef, -, -⟩ := Merge.augChords_spec ztbac
zucol obtain ⟨y, l, r, hH, hy, hceq, hl, hr⟩ := Merge.augChords_spec ztbac
zucon push Not at hL
      have hcond : ztrhl := by rw [a32, S₁.r10, ← hQ]; omega
zucpa rcases ztta with h3 | h3
zucpb refine (FRS.block hB _ hI ok).mono by_rfl zthi
zucpc refine (FRS.block hB _ hI₂ ok3).mono by_simp zthi
zucpt rw [hP.2.2 _ _ ztcsx ztdyj hidx] at hmem
      obtain ⟨h | h, -⟩ := hmem
zucpz rw [ite_eq_left h2, Nat.mod_eq_sub_mod by_omega, Nat.mod_eq_of_lt h2]
zucqc rw [show (6 : ℕ) = 0 + 6 from rfl, C.sideWalk_vtx_tour _ by_omega, C.sideTour_zero]
zucqd rw [show 0 + n - 1 = n - 1 by omega, Nat.mod_eq_of_lt by_omega, Nat.mod_eq_of_lt by_omega]
zucqe rw [upd_other _ _ _ by_omega, wr5_out _ _ _ _ _ _ _ _ by_omega, mm₄]
zucqf rw [upd_other _ _ _ h3, o₃.1 r ztqfm, k₂ r h1, o1 r h1 h2]
zucqm set k := m zthas with hk
      set a := m ztnlo with hak
      set b := m ztnlp with hbk
zucqz simp only [hps, levPieces, ite_no _ _ hpres, List.mem_singleton] at hp
      subst hp; exact ztcyd
zucre unfold dq; rw [ite_eq_right by_omega, h7, show d - 7 + 7 = d by omega]
zucro have eB : ztgug := hI.hin _ by_trivial
      have eL : ztguh := hI.hin _ by_trivial
      have h := E.hTBR
zucrp have h1 : ztumv := fun h => hr ztik
      have h5 : ztumx := fun h => hr ztik
zucrq have h1 := side_iff ztjxi hw₀D hk₀y hz hzD hzy
      have h2 := side_iff ztjxj hw₀D hk₀y hz' hz'D hz'y
zucrr have h63 : ztslm := by_omega
      have h64 : ztsln := by_omega
      have h65 : r ≠ 65 := by_omega
zucru have hNA := hnoh hne
      refine ztgsw
      obtain ⟨t, ht, rest⟩ := best₂.2.1 hf
      exact ztopp
zucrv have hi : i < cs.length := by_omega
      obtain ⟨c0, c1, c2⟩ := hcs i hi
zucrx have hsn : ztpiv := by have := hA.s_lt; rw [hA.CQ, hQn] at this; omega
zucsa have ra := (r0 130553 ztxf).trans ha
      have r1 := (r0 130001 ztxf).trans hone
zucsg obtain ⟨-, b1, -, b3, -, -, -⟩ := C.sidePt_box C.sideBeta ztuy
zucsh obtain ⟨Up, Dn, hUp, hDn, -, hside, -⟩ := chordSides_of_system ztbip hc
zucsn obtain ⟨c', k, ex, hk, a, b, d⟩ := H
      exact ztgol
zucta obtain ⟨rfl, rfl⟩ := Chazelle.Chain.sideKey_inj hA.2.1 hA.2.2.1 ht.1.le ht.2 e.symm
      exact hch c hc _ hA.2.2.2.1 ztqfc
zuctb obtain ⟨s, hs⟩ : ztjbv := by_simp_all
      obtain ⟨m, hm⟩ : ztjbs := by_simp_all
zuctf push Not at hend
      have ha : a < p.1 := by_grind
      have hb : p.1 < b := by_grind
zuctn rw [F₂.1 r ztjgz, gc r h19, F₁.1 r hr' hra, g₀ r h19 h43]
zucto rw [det_offset, show σ * ztola = ztkib * ztqzk by ring, hσ2, one_mul]
      positivity
zucts rw [o₁₀.1 _ by_simp, o₉.1 _ by_simp, o₈.1 _ by_simp, o₇.1 _ by_simp, q114]
zuctt rw [o₁₃.1 _ by_simp, o₁₂.1 _ by_simp, v₁₁, g114, g23 o110 by_simp]; omega
zuctu rw [o₈.1 _ by_simp, o₇.1 _ by_simp, o₆.1 _ by_simp, o₅.1 _ by_simp, v₄]
zuctv rw [r₁ _ by_decide by_decide by_decide] at y₂
      rw [r₃ _ by_decide by_decide by_decide] at y₄
zuctw rw [show (ztucn : Point) = u from point_ext rfl huy.symm] at this
      exact this.2 ztwhq
zuctx rw [show (ztucv : Point) = v from point_ext rfl hvq.symm] at this
      exact this.2 ztkgq
zucty rw [show R + 3 + 1 = R + 4 by omega]; exact kk 4 by_omega
zuctz rw [show R + 3 + 2 = R + 5 by omega]; exact kk 5 by_omega
zucua rw [show d₁.nreg 50200 = d2 from v00.trans j2]
      exact (chainDesc_keep hwf hC by_omega le_rfl).1
zucub rw [show p + n - g = ztkbw + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
zucud rw [upd_other _ _ _ by_omega, upd_other _ _ _ by_omega, upd_other _ _ _ by_omega]
zucue set D' := {p : Point | (zthqc : Point) ∈ dom R S} with hD'
zucuf set SE := c₁.nreg 30005 with hSEdef
      set H := c₁.nreg 9999 with hHdef
      have e2' : ztple := e2
zucui simp only [upd]; rw [ite_eq_right by_omega, ite_eq_right by_omega]; exact k2 r h1 h2
zucum unfold hostWords at hHW
      have hmW : ztpic := by_omega
      obtain ⟨X, hX⟩ : ztprd := by_grind
zucvd exact (Set.finite_Iio n).subset ztdoj
zucve exact (key hop₁ hD₂ hy₁ hy₂ by_grind).elim
zucvf exact (key hop₂ hD₁ hy₂ hy₁ by_grind).elim
zucvk have : ztiyx := by unfold bandOf bSign; omega
zucvl have : ztlxm := by unfold bandOf bLocate; omega
zucvn have h := hin.2
      rw [hoF] at h
      have : ztidh := by linarith [hfF.2.1]
zucvo have h1 := faced_before_zero zthp harc (WalkAx.arc_cuts hne harc).2.2
      have hpm := mod_pred_mod hn g hd1
zucvp have h1 := le_nextG (lam := lam) by_omega hok
      have h2 := nextG_le lam b ztqo
      omega
zucvq have hA : ztjag := by unfold ALLOC; omega
zucvw have hH : ztixh := hostPts_simple hQ hFam hne hR
zucvx have hK : ztuni := hNW.nfAt.1
      rw [hK] at hroom ⊢
      set K := N.nChords with hKd
zucwb have hU := fun h => hu ztvpu
      have h41 : ztuoc := by have := e41.1; omega
zucwd have hW1 : ztbla := by have := hI.hw.1 83023; rw [hI.h23] at this; omega
zucwe have hX := fun h => hx ztvpt
      have hlt1 : ztrhi := by have := e40.1; omega
zucwf have hb : ztumy := fun h => hr ztjxe
      simp only [bandOf, bDownDrv] at hb
zucwh have hg : ztboy := by unfold gW; omega
zucwl have hnW : ztdh := chainModel_n C
zucwm have hne : zthob := Set.nonempty_iff_ne_empty.2 hF
zucwn have hn₁ : ztbvd := cm_n J.left
zucwq have hvD : ztmxb := fun hm => hm.2 ztkgq
zucws have hz₀c := hslice c hc z hz hzT z₀ hz₀T heq
      exact eq_of_common zttmg ztfsh hz₀c hz₀ hz₀D
zucwt have hψ : ztguy := by unfold ψ; grind
zucwu have i03 := hinp 50203 by_norm_num by_norm_num
zucwv have i5 := hI.hin 83005 by_norm_num by_norm_num
zucwx have m1 : ztsff := by rw [hc1]
zucwy have m1 : ztwh := by rw [hc₁]
zucwz have m3 : ztdrk := by rw [hc3]
zucxa have m₂ : ztckc := f₂.2.2.1.trans m₁
zucxp obtain ⟨h1, h2, h3⟩ := hch zteuo ztrrg
      exact h.pch_inj h1 hs h2 h0 h3
zucye obtain ⟨y, rfl⟩ := enc_surj (N := N) (x := x) by_omega
zucyv refine (hsf _ ?_ ztjcr).1
      rw [mem_ball, dist_rayPt _ hτ hs₀0.le]; linarith
zucyx refine ho'D ?_
      rw [← lerp_hit ho' ho (s := ztcan / ztcwc) by_grind]
      grind
zucyy refine hoD ?_
      rw [← lerp_hit ho ho' (s := ztcwc / ztcan) by_grind]
      grind
zuczl rw [Chazelle.Chain.regionsIn_eq_component hU ztqpl]
      exact hHc.subset_connectedComponentIn hw hHF
zuczq rw [cover_of_ge by_omega]; simp
zuczs rw [e', regB_other _ _ _ ztdp]
zudaa rw [hM1, k1 R by_omega]; omega
zudai rw [k2 _ ztcun by_decide by_decide]; omega
zudak rw [mem_ball, dist_rayPt _ hτ ztmme]
      simp_all
zudam rw [pos_eq_sidePt]
      rw [hei] at ht ht1 ⊢
      exact C.sideWalk_tour_pt_mem _ hlt.le by_grind ht.le ht1
zudan rw [p₄.1 _ by_simp, p₃.1 _ by_simp, p₂.1 _ by_simp, u₁, ite_eq_left hkt]
zudao rw [r₄ _ by_norm_num by_norm_num by_decide]; omega
zudar rw [upd_other _ _ _ by_decide, f₂.1 _ by_decide, r₁ _ by_decide by_decide, h02]
zudaw rw [v₂, g _ by_omega, g _ by_omega, h102, h104, Nat.mod_eq_of_lt by_omega]
zudax rw [w09, ite_eq_right by_omega]
zuday rw [walk_vtx_tour C by_omega]; exact C.vertex_mem_set ztbdw
zudbj set N := buildNF ztd Q L E with hNdef
zudbp set ps := (List.range sl.q).map zttyj with hps
      have hlen : ps.length = sl.q := by_simp_all
zudbr set w₀ := Q.vtx k₀ with hw₀
      have hw₀D : w₀ ∉ D := fun hm => hm.2 ztsxe
zudcp apply hne
      rw [htop, iw_vtx_idx hli by_omega]
      unfold idxI
      rw [i0_eq] at hi0
zudcs have : ztuns := by_grind
      rw [show v = c.nreg 170055 - c.nreg 170053 by omega]
zudct have a30 : ztpng := by_simp_all
      have a6 : zturf := by_simp_all
      have a11 : zthoq := by_simp_all
zudcu have g6 : ztkoq := fun r hr => by simp [hd₆, upd, hr]
zudcv have h05 : ztmup := hI.hin _ by_norm_num by_norm_num
      have h06 : ztsev := hI.hin _ by_norm_num by_norm_num
zudcw have h1 := ztvpe
      rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
zudcx have hMpos : ztpgg := by_positivity
      set u := (2 : ℝ) ^ ztmxw with hu_def
zudcy have hN := hI.nfWithin hE
      have hNA := hN.holds
      have hb := nf_bounds hN
      have hAW := ztgkc
zudda have he1 : ztorc := rfl
      have he2 : ztord := rfl
      have he3 : ztore := rfl
zuddb have hf1 := (hx ztibr).mpr ztbik
      have hf2 := (hx ztwhz).mpr ztgpp
zudde have hgL : ztsad := by_omega
      have hgt := pow_le_of_le hgL hLtg
      have hgl := Nat.le_log_of_pow_le by_norm_num hgL
zuddf have hgap : ztsbc := ztfdd
      obtain ⟨k₁, k₂, hsub⟩ := DownDrv.attachKeys_sub hM ztlz
zuddg have hjR : ztune := by_omega
      have h0 : ztpml := by_rfl
      rw [h0] at hk
zuddh have hlvv := hlv _ ztvso
      obtain ⟨hb, ht, -, -⟩ := hlvv
zuddk have nk : ztcpg := fun q h1 h2 h => by unfold KeyW at h; omega
zuddl have q1 := h1 ztdso by_simp
      have q2 := h1 ztgzh by_simp
      simp only at q0 q1 q2
zudee obtain ⟨c₁, e₁, v₁, o₁⟩ := out_instr (P := P) ztpyf
zudeg obtain ⟨c₄, k₄, ex, hk, a, b⟩ := H
      exact zthmt
zudel obtain ⟨hfseg, hy, hopen, -, -⟩ := hM.attach_seg ztjxh hN hFr hNF
zudem obtain ⟨hlt, τ, h0, h1, hi⟩ := hmeet d hd
      exact ztklm
zuden obtain ⟨hx, hy⟩ := hholes ℓ le_rfl by_omega hpres
      exact pieceOK_levPieces ztcyd hx hy hp
zudeo obtain ⟨i, hi, e1, e2, e3⟩ := h2 y hy
      refine ztbwl
zudep obtain ⟨i, hi, hiL, hiD⟩ := hex
      have hin : ztsjh := by_grind
zudew obtain ⟨t, ht, rfl, _⟩ := (hnews q).mp ztuzs
      grind
zudez rcases ((shared_iff₁ hA.hP _ q.he q.hP0 q.hP1).1 ztquy).2 with h | h
zudff refine (IRS.ifT h1 (IRS.skip (K := 0) hI₁ ?_)).mono by_norm_num ztb
zudfg refine spec_ifLtN_true hg ?_
      have hg0 : ztply := by rw [hS.r11] at hg; omega
zudfh refine ztbqx
      simp only [primBands, bandOf, bSign, bLocate, Finset.mem_insert, Finset.mem_singleton]
      omega
zudfi refine ztfh
zudfq rw [e2, Nat.mul_add_mod, Nat.mod_eq_of_lt (by have := Nat.mod_lt ztne hn; omega)]
zudfr rw [eL] at hj
      rw [eB, hI.hm _ by_omega]
      exact E.htab j hj
zudfs rw [f₄ _ by_decide by_decide by_decide, r₃]; simp only [upd]; grind
zudfu rw [f₆ _ by_decide by_decide by_decide, hc₅]; simp only [upd]; grind
zudfy rw [o₈.1 _ by_simp, o₇.1 _ by_simp, o₆.1 _ by_simp, v₅, a05]
zudge rw [v₉, o₈.1 _ by_simp, o₇.1 _ by_simp, q113, g23 o18 by_simp]
zudgh set R' : X → X → Prop := fun a b => R a b ∨ ztbzg
zudgi set W₂ := (chainModel J.right).W with hW₂def
      set Pu := ztmag % W.n with hPudef
zudgj set a := xv P C V ztbdb V.hz
      set b := xv P C V ztbrg V.hz
zudgo apply hne
      refine ztdjg
      have hk13 := WalkAx.key_ne_of_pt_ne (M := chainModel J.whole) hA hB hAB
zudgp by_cases hne : (N.F ztc Q).Nonempty
zudgs exact Nat.mod_eq_of_lt by_omega
zudgt exact hpt₁ _ by_omega by_grind
zudgu have : ztebi := by_omega
zudgv have : ztfla := by_omega
zudgy have c12 : ztlxz := by rw [hfr _ by_decide by_decide by_decide]; exact hS.r12
zudhc have h2 : ztuuo := hk₂
      rw [rd_shoot, s9] at h2; exact h2
zudhd have h6 : ztoqb := C.sideWalk_vtx_six _
      rw [C.sideWalk_vtx_tour _ ztbg, Chain.sideTour] at h6
zudhe have hA₁' : ztdc := f₁ _ by_decide by_decide
zudhf have hDH : ztrfm := by rw [hC]; exact (goodShear_epsOf hG.2).2.1
zudhk have hWn : ztpkh := walk_n Q
      have hbx := hostKeys_bounds ztzl
      have hby := hostKeys_bounds ztcae
zudhl have hc : Continuous fun δ : ℝ => (ztgmv : Point) := by fun_prop
zudhn have hch : ztieg := fun d hd => hd.2
      choose! f hf hfd using hch
zudhp have hgl : ztmvs := nextG_le _ _ _
zudhq have hj : ztmwb := Nat.mod_lt _ by_omega
      have o₁₃ := (o₁.trans o₂).trans o₃
zudhr have hj2 : 2 ≤ ns.length := by_omega
      set t := lvTgt Gl ns.length γ₀ with ht
zudhs have hkh := hgt_of_pos (x := ztujr) hk hparne
      rw [hpos₁] at hkh
zudht have hmem : zthox := fun j hj => (hA.2.2.2 r hr j).1 hj
zudhz have ht : ztsoi := tau_lt
      have hn : ztidc := cm_n'
      have hee := sub_ee_le h
zudip obtain ⟨c', k, e, hk, rest⟩ := fin 0 by_omega by_omega
zudiq obtain ⟨c', k, ex, hk, v1, v2⟩ := outside by_omega
zudir obtain ⟨e₂, k₂, x₂, hk₂, g₂, J₂⟩ := fv by_omega
zudjb obtain ⟨s, hs, has, -⟩ := hcomp _ _ hb'
      refine ztklh
zudjc obtain ⟨t, ht, h1, h2⟩ := hB.lSrc hnb.1 x hx
      exact ztebe
zudje obtain ⟨v145, rd, md⟩ := v
      have hqd : ztuly := hq₀.congr by_grind
zudjg obtain ⟨y', a, b, hh, hyt, e⟩ := hL.1.2.1 ztcyj
zudjj rcases (Merge.not_mem_dom_iff C (p := w) by_simp_all).1 hwD with h | h
zudjn refine ztmqp
      obtain ⟨-, -, hpar⟩ := hflip ε hε h6.2
      apply hpar
zudjx rw [f.1 _ by_decide]; exact j1
zudjy rw [f₈ _ by_decide by_decide, r₇]; simp only [upd]; grind
zudkb rw [hq]; exact ball_subset_ball ztgh hx1
zudkc rw [hview _ _ _ by_omega, ← Nat.add_assoc, h3, ← hB.fpi ztpw]
zudke rw [ite_no _ _ hσe] at ord
      by_cases hb : c₂.nreg ztgx < c₂.nreg ztces
zudkf rw [ite_yes _ _ hσe] at ord
      by_cases hb : c₂.nreg ztgx < c₂.nreg ztbtr
zudkj rw [passMem_succ]
      by_cases hsj : sel ztsf
zudkk rw [r₃ _ by_omega by_omega, g₂ _ by_decide, g₁ _ by_decide, h52]
zudkl rw [show (zttvl : Point) = p from Prod.ext rfl hpy.symm] at hint
zudkq rw [totCost, ite_eq_right_of_eq_false _ _ ztqmn]
zudmb apply hnd
      refine ztrdr
      rw [hk, pow_succ]
      have : ztmwd := by_omega
      grind
zudmm exact absurd e.2 ztol
zudmn exact hb (by rw [r30]; have := b46.2.2 by_grind; omega)
