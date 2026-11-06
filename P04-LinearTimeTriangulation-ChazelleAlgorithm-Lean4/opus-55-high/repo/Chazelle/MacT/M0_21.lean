module

public import Chazelle.MacT.Base

public section

set_option hygiene false

zg zubcv rcases hE.kind with ⟨C, -, hM⟩ | hM
zubcw rcases hs with ⟨k, hk, rfl⟩ | hs
zubcy rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
zubdb rw [hn]
zubdd simp only [Machine.upd_apply]; unfold ArrRG at hr; grind
zubde simp only [Machine.upd_apply]; unfold ERG at hr; grind
zubdf simp only [nbrRegs, List.mem_cons, List.not_mem_nil, or_false]
      simp_all
zubdg simp only [regB, regI, upd, ite_eq_right hr]
zubdi by_contra h; push Not at h; nlinarith
zubdj by_contra hc; push Not at hc; nlinarith
zubdn have g₂ := fun r (hr : Bhost r = false) => f₂.1 r hr
zubdo have hM := walkAx_interiorModel hQ
zubdp have hR' := hR; unfold RegsOK at hR'
zubdq have hRd := hR.frame hfd
zubdr have hUfree := Chazelle.Chain.regionsIn_subset hU
zubds have hkN := (((H.regs ri hr).1 k).1 hk).1
zubdt have hp := Nat.two_pow_pos g
zubdv intro p t h1 h2 h3 h4 h5 h6
zubdx obtain ⟨c₁, k₁, e₁, hk₁, p₁, r₁, m₁⟩ := parL_exec c hw hS (by have := hI.hiy; have := hI.yn; omega)
zubea obtain ⟨t1, t2, t3, t4, t5, t6, t7, c1, c2, c3, c4⟩ := chosen_facts h hch hT hB hI he hc
zubec rcases hlt c hc hpc with h2 | h2
zubef right; right; right
zubeg rw [List.length_range] at hseg s₂ hk₅
      rw [show ALLOC = 9999 from rfl, g9] at s₁
      have e₆ := Exec.copyN (P := P) e₅.wb_right 60007 30005
zubei rw [e₁]; simp [regB, regI, upd, a, b]
zubel rw [ite_eq_left h1]
zubem rw [mEdge_def, hψ, ← hpD]
zubep set Q := Qof P
zubeq simp only [Src.pt, SymPt.eval, SignTest, h35, h53, h55] at hb'
      rw [edgeXQ hC hsn hj hk, edgeXQ hC hsn hb hk] at hb'
zuber simp only [hd₄, upd]; grind
zubes simp only [holeL, chainHL, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
zubeu simp only [mem_insert_iff, mem_singleton_iff] at hs
      rcases hs with rfl | rfl | rfl
zubex have hK₀ := E.hK.fix hI
      obtain ⟨g1, g2, g3, g4, g34⟩ := cst_regs E hI
      obtain ⟨hg', hL2, hW2⟩ := corr_bounds E
zubfb have o0 := slfOff_congr (P := P) (J := J) r01 r02
      have o1 := slfOff_congr (P := P) (J := J) r11 r12
zubfc obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h40, -⟩ := hA.hst
zubfd obtain ⟨-, hex, -⟩ := hT.2.2 reg₀ hreg₀
      obtain ⟨T, -, -, -, hfe, hfp, -⟩ := hex b10 b11
zubfe obtain ⟨bab, bax, bxa, bay, byb, bxb, bxy, byx⟩ := mem
      rw [hz] at bax bxa bay byb bxb bxy byx
zubff obtain ⟨c₂, k₂, e₂, hk₂, b33, b34, b35, b36, b37, Fs⟩ := setOne_exec c₁ w₁
      have S₂ := keepSet Fs S₁
zubfg obtain ⟨hr, hp1, hp2, h66, h67, h68, h69⟩ := found
      set r := d₁.nreg 150065 with hrdef
      set u := d₁.nreg 150064 with hudef
zubfh rintro (⟨h1, h2, h3⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
zubfn by_cases hx : x < b
zubfr have H := shift_c0 hQ T hD hli
      have hle := i0_le hQ T hD hli
zubft have h1 := J.one_le_m₁
      have hτ₁ := tpos_lt J.left J.m₁
      have hτw := tpos_lt J.whole J.m₁
zubfw have hS₂a := hS₂.2.1
      have hS₂f := hS₂.1
      have hC := corr_right0 J hP hS₂a hS₂f
zubga have hb := hD.base
zubge have hkab := WalkAx.key_ne_of_pt_ne hQA hQB hQAB
      have hsep' := (sep_iff_btw hg0 hgn a0 a1 b0 b1 x0 x1 y0 y1 hkab hxy hxa hxb hya hyb).1 hsep
zubgf have hlen := hE.hlen
zubgh have hw3 := e3.wb_right
zubgi have hw4 := e4.wb_right
zubgj have hx0 := hx.1
      have hx1 := hx.2.1
      have hy0 := hy.1
      have hy1 := hy.2.1
zubgm have k0 := k0_of hE hI
zubgp have w₇ := e₇.wb_right
zubgq intro P W c hw hpre hroom
zubgr intro c hc z hz hzT hqz
zubgs intro i hi j hj hij
zubgt intro u hu
zubgu obtain ⟨-, -, -, -, b5⟩ := envRegs_band2 q hq
zubgw obtain ⟨L, ma, mb, mx, my, mk, ra, rb, rx, ry, rk⟩ := ranks5 a b x y k
zubgx obtain ⟨U, hU, hS⟩ := side_region_exists hM hFam.2.1 hFam.1 he hρ
      have hfac := (faced_or_middle hGM hFam he hA hρ hU hS hdir).1 huniq
zubgy obtain ⟨c', k, e, h1, h2, h3⟩ := h
zubgz obtain ⟨c', k, e, h1, h2, h3⟩ := hh
zubha obtain ⟨c', k, ex, hk, v⟩ := qk0_exec c hw
zubhb obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
zubhc obtain ⟨hHost, hP, hs', hm', hT', hb'⟩ := hC
zubhd obtain ⟨hna, -, -, hlist, -⟩ := hm.nf.2.2.2.2.2.2.2.1 _ hrR
zubhe obtain ⟨hq2, hqa, hqb⟩ := hq
      rcases hqa.lt_or_eq with h1 | h1
zubhf obtain ⟨i, hi, h1, h2, hse⟩ := S.stop_idx he heK hst
      obtain ⟨hi', hia, hfl, hok⟩ := S.skip_aux h1 h2
zubhg obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
zubhh obtain ⟨i, σ, hi, hσ, hdir, rfl⟩ := hc
zubhi obtain ⟨j, hj, hjr, hja, hjb⟩ := hA.2.2.1 r hr a b harc
      obtain ⟨p, hp, hpj⟩ := NFLoc.seq_surj hN hj
zubhj obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
zubhk obtain ⟨p, hpn, hp1, hp2, hv0, hv1, -⟩ := piece (g := g) (h3 := h3) X hA hjd
zubhl obtain ⟨s, hs, hps⟩ := mem_iUnion₂.1 hp
zubhm obtain ⟨x0, x1⟩ := Corr.key_mem hp ht.1.le ht.2
zubhn obtain ⟨z, hz, hzD, hzU, hzy⟩ := hbot c hc
zubho obtain ⟨z, hz, hzD, hzU, hzy⟩ := htop c hc
zubhp obtain ⟨δ, hδ, h⟩ := sideInArc_nhds hin
zubhq push Not at hA
zubhr rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with rfl | rfl
zubhs rcases h.2 with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, hx, -⟩ <;> [omega; omega; exact hx]
zubht rcases hq with hq | hq
zubhu rcases ht.lt_or_eq with ht0 | ht0
zubhv rcases k with _ | k
zubhx refine spec_name fun c₃ hc₃ => ?_
zubia rintro c' ⟨v1, v2, v3, v4⟩
zubib rintro c₂ hI₂ - - hc2
zubic rw [List.range_succ, List.filter_append]
      grind
zubif rw [eTL] at h
      refine h.mono le_rfl ?_
      rintro c' ⟨⟨L', a', s', g', geo'⟩, fr, hA', hm'⟩
zubig rw [h150, h151, h152] at hfill
      rw [h151] at hk2
zubih rw [hI.d, hI.d0]; exact hp.ok.injOn.iterate_lt _ hfirst
zubii rw [hPm]; exact h1b rfl s hs.1 hs1
zubik rw [hin] at hx
zubil rw [hpt]
zubim rw [hr]
zubin rwa [hwv, rayPt_sub, sideCcw_smul hs₂0] at this
zubio set M := chainModel C with hM
zubip simp only [Geometry.add_snd, Geometry.smul_snd, Geometry.add_fst, Geometry.smul_fst]
zubiq simp only [NFLoc.itemCnt] at hsucc
zubis simp only [ZKeep, Bool.or_eq_true, decide_eq_true_eq] at h
zubiu simp only [rayPt, neg_one_mul, neg_sub, add_sub_cancel]
zubiv simp only [regI, upd_same]
zubiw unfold nodeArc nodeLs; rw [hr, ← hm.RB, ← hm.LB]; simp_all
zubix unfold sideInArc at hin
zubje have hst := e.hA.hstops
      have hlog := e.hA.hlog
      have htw := e.hA.htabw
      simp only [rd_sw] at hst hlog htw
      have hAc := hI.hA
      have hWc := hI.hw.1 ALLOC
zubjg intro r hr hrr
      have n1 := fun q (h1 : sw 1102 ≤ q) (h2 : q ≤ sw 1203) => out_ne hrr h1 h2
zubjh obtain ⟨K₁, K₂, hK, ⟨c₁, rfl⟩, ⟨c₂, rfl⟩, hsec₁, hsec₂⟩ := hM.split he hA hB hAB
zubjj obtain ⟨hA, hB⟩ := hr
      have h1 := hA.2.2.2.1
      obtain ⟨a, b, hab, hcab, hy, -⟩ := hM.ends _ hadm
zubjk obtain ⟨hjr, harc⟩ := hArcs.1 j hj
      have hU := hRC.1 _ hjr
      obtain ⟨-, ha, -, hb, -⟩ := harc
zubjl obtain ⟨δ, hδ, h1a, h1b⟩ := hW
      obtain ⟨δ₂, hδ₂, h2a, h2b⟩ := hW₂
      rcases ht0.lt_or_eq with htpos | ht00
zubjm rcases he with ((⟨c', hc', hfree, rfl⟩ | ⟨c', hc', hfree, rfl⟩) | hsh) | htop
zubjp rintro (⟨-, -, h⟩ | ⟨h1, h2 | h2⟩ | ⟨h1, -⟩ | ⟨h1, -⟩)
zubjq rintro (⟨-, h, -⟩ | ⟨h1, h2 | h2⟩ | ⟨h1, -⟩ | ⟨h1, -⟩)
zubjr rintro (⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, -, h3⟩ | ⟨-, h2, -⟩)
zubjv simp only [slfLdL, regB, regI, upd, slfP, slfY, slfL0, slfL1, slfN, oPar, K1, K3, sw]
      grind
zubjw apply point_ext
zubjx by_cases a2 : c₁.nreg 81011 < c₁.nreg j
zubjy by_cases h : c.nreg a < c.nreg b
zubjz by_cases h2 : c.nreg b < c.nreg a
zubka by_contra hfr
      rw [Filter.not_eventually] at hfr
      simp only [not_not] at hfr
zubkc exact ⟨by have := hA.2.1; positivity, by linarith [hA.2.2.1]⟩
zubke have hK₁ := E.hK.fix hI₁
zubkh have hP₂ := E.hP
      have hNF := E.hNF₂
zubkm have hn := h.walk.n_pos
      have hc := h.walk.c_lt
zubkn have hne := ne_of_param_pos ht
zubkp have hy' := sig_band hy (C := C) (C' := C')
zubks obtain ⟨-, -, hEb, -⟩ := hcw.2 H C hC
zubkt obtain ⟨P, s, m, a, b⟩ := C
      obtain ⟨P', s', m', a', b'⟩ := C'
      simp_all
zubku obtain ⟨b1, b2, -, -, -, -, -, -⟩ := cut_chosen h hch hT hB hI ht htop hact hbt
zubkv obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := cut_chosen h hch hT hB hI ht htop hact hbt
zubkw obtain ⟨e, h⟩ := x
zubkx obtain ⟨h1, h2⟩ := h
zubky obtain ⟨hjA, hjr⟩ := (B.hregs.2.2.1.2.2.2 r hr j).1 hj
zubkz obtain ⟨hs1, hs2⟩ := hs
zublb obtain ⟨t, hFH, hpp2, he2, hpos2⟩ := hyes h1
zubld obtain ⟨z, hz, rfl⟩ := hU
      obtain ⟨sL, sR, y₁, y₂, hT, hsub⟩ := region_trap hP hDH hz
zuble obtain ⟨σ, hσ, hdir, hend, hseg⟩ := vtxChords_spec hd
zublf rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
zublg rcases hA with ⟨_, h⟩ | ⟨h', _⟩ | ⟨h', _⟩ <;> [exact h; omega; omega]
zublh rcases hA with ⟨h', _⟩ | ⟨_, h⟩ | ⟨h', _⟩ <;> [omega; exact h; omega]
zubli rcases hB with ⟨h', _⟩ | ⟨_, h⟩ | ⟨h', _⟩ <;> [omega; exact h; omega]
zublj rcases hB.2 with ⟨_, h⟩ | ⟨h', _⟩ | ⟨h', _⟩ <;> [exact h; omega; omega]
zublk rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [ipT, ipB, ipM6, ipM5, ipJ, ipKc, sw]
zubll rcases hτ with rfl | rfl <;> linarith
zubln refine IRS.seq (K₂ := 31009) hstep2 ?_
      rintro c₂ hI₂ hA₂ hA₂' ⟨e', q23, he6, he', hpe, q2, qm2⟩
zublr rw [e']; simp [regB, regI, upd, h]
zubls rw [e']; simp [regB, regI, upd, hq]
zublt rw [e0, e1] at hb
zublu rw [e₃]; simp [regB, regI, upd, h]
zublv rw [hQ] at b70 b71
      by_cases hlt : c₇.nreg 50170 < c₇.nreg 50032
zublw rw [hc6]; show regB c₅.nmem faceRead c₅.nreg fEE = _
      rw [v6EE, c5AB, c5SB, c5J, hm5, hsj]; omega
zublx rw [hc6]; show regB c₅.nmem faceRead c₅.nreg fEH = _
      rw [v6EH, c5AB, c5SB, c5J, hm5, hsj]; omega
zubly rw [hc6]; show regB c₅.nmem faceRead c₅.nreg fSE = _
      rw [v6SE, c5AB, c5SB, c5J, hm5, hsj]; omega
zublz rw [hc6]; show regB c₅.nmem faceRead c₅.nreg fSH = _
      rw [v6SH, c5AB, c5SB, c5J, hm5, hsj]; omega
zubma rw [hch] at hcnt
      simp only [Bool.true_eq_false, false_or] at hcnt
zubmb rw [hpos] at hz
      rw [hW] at he
      rcases C.sideWalk_pos_cases C.sideBeta he hx.1 with hbox | ⟨i, hi, hie, hit⟩
zubmc rw [hwv] at this
      exact (sideLeft_zero _ _ _).1 this
zubmd rw [ite_eq_right h1]
zubme rw [ite_eq_right h]
zubmg rw [v₂]; unfold tj; rw [← hv.sS, Nat.add_comm]
zubmi rw [← a1, ← a2]
zubmj set M := interiorModel Q
zubmk simp [h1, h2, h3]
zubml simp only [Bpos, Binit, Bpz, NFLoc.Bdir, Bool.or_eq_false_iff, decide_eq_false_iff_not]
zubmm simp only [List.mem_append] at hq
      rcases hq with h | ((((h | h) | h) | h) | h)
zubmo simp only [ht, ↓reduceIte]
zubmp simp only [rd, bandReg, bBuild, Nat.reduceMul, Nat.reduceAdd] at h
zubmq unfold transL at hx'
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hx'
zubmr beta_reduce at hroom ⊢
zubms by_cases hlt : oL < offK P J e h
zubmv exact h.cnt j hj
zubmw exact h.deg x hx
zubmx exact h.eg j hj
zubmy exact h.exb x hx
zubmz exact h.live i hi
zubna exact h.nd0 i hi
zubnb exact h.nd1 i hi
zubnc exact h.nxt j hj
zubnd exact h.prv j hj
zubne exact h.pz j hj
zubnf exact h.s0 i hi
zubng exact h.s1 i hi
zubnh exact h.stk t ht
zubni exact h.wt x hx
zubno have hA := agree_Sh hT hR.symm hℓ.le hℓ' hss hsl
zubnp have hA0 := hI.hA
zubnq have hB : gRB ≠ slfX := by unfold gRB slfX sw; omega
      have hC : gRC ≠ slfX := by unfold gRC slfX sw; omega
zubnr have hM₂ := walkAx_chainModel (C := J.right) hP
zubns have hP := E.hP
zubnt have hag := hI.agree hE
      have hA := hI.allocA hE
zubnu have hl : N'.arcs.length = N.arcs.length := h'.2.1.symm.trans h.2.1
      apply List.ext_getElem hl
      intro j hj hj'
      have e := h.2.2.2.2.2.2.1 j hj'
      have e' := h'.2.2.2.2.2.2.1 j hj
zubnv have hl : N'.chords.length = N.chords.length := h'.1.symm.trans h.1
      apply List.ext_getElem hl
      intro j hj hj'
      have e := h.2.2.2.2.2.1 j hj'
      have e' := h'.2.2.2.2.2.1 j hj
zubnw have hmN := C.m_lt
zubnz have htop := C.top_snd_lt_radius
zuboc have hw := (AncX.pos_le h hwv hv).1
zubod have hw := hI.hw
zuboe have hw₃ := e₃.wb_right
zubof have k1 := hK.2.1
zuboj have w₂ := x₂.wb_right
zubok intro p h1 h2
zuboo obtain ⟨-, -, d, hMV, hmE, hArr⟩ := cand_prep hP hS₂a hch ha haR hav ha₁ hA hpt hLst hnv hlt'
zubop obtain ⟨-, V', l, r, -, hV', -, -, harcV, -⟩ := hM.attach_face hF hfin hc hA
zuboq obtain ⟨-, harc⟩ := arc_regOf hN hj
zubor obtain ⟨D, hD, rfl⟩ := hd
zubos obtain ⟨H, -, hst⟩ := E.hst
zubot obtain ⟨U', V', l, r, hU', -, -, harcU, -, -⟩ := hM.attach_face hF hfin hc hA
zubou obtain ⟨U, V, l, r, hU, hV, -, harcU, harcV, -⟩ := hM.attach_face hF hfin hc hAc
zubox obtain ⟨d, rfl⟩ := h.eD_surj e he
zuboy obtain ⟨h0, h1, h2⟩ := h
zuboz obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
zubpa obtain ⟨h1, h2, h3⟩ := h
zubpc obtain ⟨he1, hne1, hne2⟩ := T.mem_Sd.mp he
      obtain ⟨x', hx'0, rfl | rfl⟩ := (C.mem_coDarts_iff hM).mp he1
zubpd obtain ⟨htmem, htmin⟩ := D.isTrap.topVtx_spec hP D.free
zubpe obtain ⟨hzy, hza, hzb⟩ := hz
zubpg obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
      clear h
zubph obtain ⟨rs, ls, -, -, -, -, hlsl, hls, -, hlsW, -, -⟩ := hA.hout
zubpi obtain ⟨rs₁, -, -, -, -, -, -, -, -, -, hmW, hregW⟩ := hW
zubpj obtain ⟨t, ht, rfl⟩ := h
zubpk obtain ⟨t1, t2, t3⟩ := t
zubpl obtain ⟨u', hu', heq⟩ := hother _ hUmem hUR
      have hu'' := heq ▸ mem_connectedComponentIn huA
      rw [connectedComponentIn_eq hu''] at heq
      grind
zubpm obtain ⟨u, hu, rfl⟩ := hU
zubpo push Not at h
zubpp rcases h with h | ⟨h, -⟩
zubpq rcases hc with (⟨j, hj, hφ⟩ | ⟨j, hj, hφ⟩) | ⟨o, ho, ho'⟩
zubpr rcases hr with (h | h) | h
zubpu rintro _ ⟨s, hs, rfl⟩ hp
zubpv rintro c₂ hI₂ hA₂ hA₂' ⟨-, -, -, -, vE, vC, -, -, fr₂, hAl₂, hm₂⟩
zubpx rw [List.mem_append, List.mem_map, List.mem_map] at ht
      rcases ht with ⟨t', ht', rfl⟩ | ⟨t', ht', rfl⟩
zubpy rw [h3, Nat.mod_self] at hc; omega
zubqb rw [hs]
zubqe set W := (chainModel C).W with hW
zubqf set W := (interiorModel Q).W with hW
zubqh unfold bestOf; simp_all
zubqi unfold dirOf; grind
zubqj all_goals try omega
zubqk by_contra hcon
zubql exact Nat.mod_eq_of_lt h
zubqo have fr := hM.2.2.2
      have eE := candFr_qE fr
      have eH := candFr_qH fr
zubqp have h1 := sum_segL (s := s) (μ := μ) (bo := bo) μ
      have h2 := cntLt_le bo μ μ
zubqq have h4 := h.pos_prg c hc.1 hc.2.1
      rw [hc.2.2.1] at h4
      omega
zubre intro e he
zubrf intro g hg
zubrg obtain ⟨-, -, -, -, -, -, -, -, -, -, hpp⟩ := id hN
zubrh obtain ⟨c₁, k₁, e₁, hk₁, f₁, hd₁⟩ := locDir_ok P W c hw hD
      have d₁ := hd₁ M hM
zubri obtain ⟨dw, df, dm, dle, dd⟩ := hd
zubrj obtain ⟨h1, h2, h3, -⟩ := triples_props hN hxm
zubrk obtain ⟨h1, h2, h3, h4, h5⟩ := h
zubrl obtain ⟨hNF, -, -⟩ := BuildNF.isNF_goodModel hGM hok hperm hsort
zubrm obtain ⟨hT, -, -⟩ := Merge.hit_of_freeAt C ha hσ hf
zubrn obtain ⟨hT, -, -⟩ := Merge.hit_of_freeAt J.whole ha hσ hf
zubro obtain ⟨hW, -, hR, hB, hK⟩ := hI
zubrp obtain ⟨hk, h1, h2⟩ := seg_spec h hN hx0 hxN
zubrq obtain ⟨hkp, -, -, -⟩ := stp_pre_frame hW hR
zubrr obtain ⟨hn, p₀, hp₀, hc₀⟩ := goodModel_walk M hM
zubrt obtain ⟨s₁, hs₁, hs₁0⟩ := (hev.and self_mem_nhdsWithin).exists
zubru obtain ⟨y, a, b, h, hy, -, hl, hr⟩ := augChords_spec hc
      rw [hl, hr]
zubrv obtain ⟨y, l, r, hH, hy, -, hl, hr⟩ := Merge.augChords_spec hc
      rw [hl, hr]
zubrw obtain ⟨δ, hδ1, hδ2⟩ := (hs1.and h2).exists
zubrx obtain ⟨δ, hδU, hδ⟩ := (hf.and hs1).exists
zubry rcases hbtw with ⟨h1, h2⟩ | ⟨h1, h2⟩
zubrz rcases hcl with (h | h) | ⟨-, h⟩ | ⟨h, -⟩ <;> simp only at h <;> omega
zubsa rcases hzend with ⟨hσ1, hz1⟩ | ⟨hσ1, hz1⟩
zubsb refine (convex_ball w r).inter ?_
      intro p hp q hq a b ha hb hab
      simp only [mem_ofPred_eq] at hp hq ⊢
zubsd rintro _ ⟨y, hy, rfl⟩ hmem
      rw [← LinearMap.image_convexHull] at hmem
      obtain ⟨z, hz, hzy⟩ := hmem
zubse rintro c₂ hI₂ - hAb ⟨hpost, k2, hA2, hm2⟩
zubsg rintro ⟨r, ⟨i, hi, rfl⟩, rfl⟩
zubsh rintro ⟨y, hy, h⟩
      rcases y with v | g
zubsi rw [Nat.sub_add_cancel hp1, Nat.mod_eq_of_lt hp, ← prev_mod hp hp1]
      omega
zubsk rw [hTL] at hj; rw [hTB, hm _ (by have := hA.hTW; omega)]; exact hA.htab j hj
zubsl rw [hl, h0] at hA
      obtain ⟨d, -, hall, -, -⟩ := attached_opposite hM hadm hA hσ hav
zubso rw [upd_same, hval]
      have h6' := h6; simp only [hc5] at h6'; rw [v5D, v5T] at h6'
zubsr set T := J.whole.hitParam a σ with hT
      have hz' := ha₁.trans J.left_top_le
      obtain ⟨hT0, -, hdom⟩ := Merge.hit_of_freeAt J.whole hz' hσ hfree
zubss simp [okB, okI, ipE, ipH, sw, IScr]
zubst subst h
zubsu unfold NF.chord
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
      grind
zubsv unfold sideCross; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
zubsx by_cases h1 : kind = 1
zubsy by_cases hK : L.length = 0
zubsz by_cases hji : j = i
zubta by_cases hsm : e < 6
zubtj have hNF' := hNF
      obtain ⟨-, -, -, reg, hRC, hCS, hAO, hRO, -⟩ := hNF'
zubtn have hτ' := tpos_lt J.right 0
zubto intro a b ha hb h
zubtp intro a ha b hb hab
zubtq intro k hk hmem
      simp only [Finset.mem_erase, Finset.mem_range] at hk
      rcases (simple_vtx_mem_edge_iff hP hi hk.2.2).1 hmem with h | h
zubtr obtain ⟨-, -, -, -, -, -, -, -, -, -, hpp⟩ := hNF
zubts obtain ⟨-, -, -, -, -, -, -, -, -, hh, -⟩ := hE.hNF
zubtt obtain ⟨-, -, -, -, -, -, -, -, -, h⟩ := newL_mem B hx
zubtu obtain ⟨-, -, -, reg, -, -, -, -, -, -, hpp⟩ := hN
zubtv obtain ⟨-, -, -, reg, -, -, -, -, -, hh, -⟩ := hE.hNF
zubtw obtain ⟨c', k, ex, hk, h1, h2, h3, h4, h5, h6, h7⟩ := ex
zubtx obtain ⟨c1, c2⟩ := hI.closed q hq i hmem
      rcases hh with ⟨-, e⟩ | ⟨e, -⟩
zubty obtain ⟨c₂, k₂, e₂, hk₂, I₂, hd, f₂, y₂, m₂⟩ := topBody_exec c₁ w₁ I₁ hlt
zubtz obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
zubua obtain ⟨hFam, -, -, reg, -, -, harcs, -, -, -, hpp⟩ := hNF
zubuc obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s13⟩ := v₁
zubud obtain ⟨s₁, ⟨hs₁U, hs₁B⟩, hs₁pos⟩ := ((happ.and hball).and self_mem_nhdsWithin).exists
      have hs₁pos' := hs₁pos
zubue obtain ⟨v07, v11, v12, v13, v14, v15, v16, v24, v20, v23, v22⟩ := vals
zubuf rcases h.lt_or_eq with h | h
zubug rcases hle.lt_or_eq with h | h
zubuh rcases hok with rfl | rfl
zubui rcases hqb.lt_or_eq with h2 | h2
zubuj rcases hr with h | h
zubuk rcases i with _ | i
zubun rintro c₁ hI₁ hA₁ hA₁' hc₁
zubuo rintro c₂ hI₂ - - rfl
zubup rintro c₃ hI₃ hA₃ hA₃' rfl
zubuq rintro ⟨hv, hav⟩
zubus rw [List.length_map] at this
zubut rw [Merge.Junction.whole_vertex_add]; rfl
zubuu rw [e]; omega
zubuv rw [h0] at this
zubuw rw [h1, h2]
zubux rw [hE₁] at hdE
zubuz rw [hc1]; rfl
zubva rw [hlo, hhi]
zubvb rw [neg_neg] at hsec
zubvd rwa [one_mul] at this
zubvf simp [rayPt, sub_eq_add_neg]
zubvh simp only [↓reduceIte]
zubvi subst h0
zubvj apply Geometry.point_ext <;> simp [Geometry.lerp] <;> ring
zubvk apply point_ext <;> simp [lerp, rayPt, hw]; ring
zubvl apply point_ext <;> simp [lerp] <;> ring
zubvm by_contra hne'
      rcases Nat.lt_or_gt_of_ne hne' with h | h
zubvs congr 1; unfold sideE; grind
zubvt dsimp only
zubvv exact h1
zubvx exfalso
      have hk := off_inj hg0 hgn kB0 kB1 kA0 kA1 h
      obtain ⟨rfl, rfl⟩ := sideKey_inj hB.2.1 hB.2.2.1 hbA.2.1 hbA.2.2.1 hk
zubwa have h := hR; unfold RegsOK at h
zubwe have hHU := subset_region hU hHc hHfree hs₁H hs₁U'
zubwg have hP : C.P.Simple := by rw [T.hP]; exact hQ
zubwh have hR := rT_lt C
zubwi have hRc := Regs_of_pfr hR0 hf
      set R := L.tree c0.nmem with hRdef
zubwj have hfin := hF.finite.subset hS
zubwk have hlr := hH.lt
zubwl have hlt' := whole_lt_right hP hS₂a hch ha haR hav hfree hst hA hLst
      have hpt := attach_far hP hσ haR hav hfree hA hLst.le
zubwm have hq' := hq
zubwo have hs' := o6 hlt hnb.1 hlt2
zubwp have hv0 := Chazelle.Chain.sidePt_zero M.W p
      rw [hv0] at hBe' hBw'
      have hin := hord pe pw te tw hBe hBe' hBw hBw'
zubwq have hw₄ := e₄.wb_right
zubwt have q := q0_of hQ
zubww intro h0
zubwy intro hF; unfold FoundC at hF; grind
zubwz intro j hj0 hj s' hs'
      unfold grpLen at hj; rw [hJt] at hj
      rcases Nat.lt_or_ge j _ with hjd | hjd
zubxa intro m' hm'
zubxb intro r hr j; rw [← harcsN]; exact hlast r (by rw [nRegions]; exact hr) j
zubxc intro r hr; simp only [regB, regI]; simp_all
zubxd obtain ⟨-, -, hC, -, EL, ER⟩ := h.facts hi
      rw [hH] at hC EL ER
zubxe obtain ⟨-, harc⟩ := arc_regOf hN hq
      obtain ⟨-, -, hne', -⟩ := OracleQ.arc_facts hN hne hq
zubxg obtain ⟨D, -, rfl, hD⟩ := regionOfDiag_spec hd
zubxh obtain ⟨Hs, Cα, N, γ', hK, J, hV, ht, hs1, hs2⟩ := h1 hk
zubxj obtain ⟨a1, a2, a3⟩ := hCL i hi
      grind
zubxn obtain ⟨hL1, hLn, hsL⟩ := diagLen_spec hd.1 hd.2.1 hd.2.2.1
zubxo obtain ⟨hMD, hwf⟩ := hI.modelDesc hE
zubxq obtain ⟨htK, hk⟩ := mem_kl.1 ht
zubxr obtain ⟨hu0, hun⟩ := WalkAx.cut_bounds hu
zubxt obtain ⟨ii, hii, hir⟩ := List.mem_iff_getElem.1 hr
      have hii3 : ii < 3 := by simpa [Sweep.nbrRegs] using hii
zubxu obtain ⟨reg, -, hA, -⟩ := NFLoc.isNF_arcs hN
zubxv obtain ⟨s, hs0, hs1, rfl⟩ := Chazelle.Geometry.mem_segment_iff_lerp.1 hz
zubxw obtain ⟨ε₀, hε₀, hε⟩ := hside z hzc hzD
zubxx rcases Nat.lt_or_gt_of_ne hne with h | h
zubxy rcases hA with ⟨h', _⟩ | ⟨h', _⟩ | h <;> [omega; omega; exact h]
zubxz rcases hB with ⟨h', _⟩ | ⟨h', _⟩ | h <;> [omega; omega; exact h]
zubya rcases hg h.1 with h' | h' <;> omega
zubyb rcases hp with h | h | h <;> rw [h]
zubyc rcases wv_inp (b := revOf Q) hp with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
zubyf right
      have hel : ee < L := by rcases sub_he' h with h' | ⟨-, h'⟩; exact h'; omega
zubyg rintro _ ⟨s, hs, rfl⟩
zubyh rintro c (hc | hc)
zubyi rintro c' ⟨a, b, d⟩
zubyj rintro c₁ hI₁ - - ⟨hj1, hl1, hl2, k1', hA1, hm1⟩
      set j := c₁.nreg lJ with hjd
zubyk rw [Lst_rlen]; exact rlen_add_llen J hVNT
zubym rw [Nat.mod_eq_of_lt h3] at hc; omega
zubyn rw [div_mul_eq_mul_div, div_eq_iff hk0.ne', hk]
zubyo rw [e2, hθρ, one_mul]
      linarith
zubyp rw [h.param'_eq hk hy, param_eq _ Q x k hk]
zubyq rw [hb, hostPt_eq M.W hB.2.1 hB.2.2.1]
zubyr rw [hm a]
zubys rw [ht]
zubyt rw [ite_eq_left rfl]
zubyu rw [ite_eq_right h2, show S + i = 2 * m + 2 * m by omega, Nat.add_mod_right, Nat.mod_self]
      omega
zubyx rw [mem_sideSet' hK hRR h hch hisdn hI hna] at hh
zubyy rw [show p + 1 = n by omega, Nat.mod_self]
zubyz rw [sideCross_neg_dir, sideDot_neg_dir, h4]
      grind
zubza rw [this]; simpa [selX, hA] using hc
zubzd set M := chainModel C
zubze set M := interiorModel Q with hMdef
zubzf set k := sideE m j with hkd
      have hkm : k ≤ m := by rw [hkd]; unfold sideE; grind
zubzh set w := sidePt M.W p t with hw
zubzi simp only [Binit, decide_eq_false_iff_not] at hr
zubzj simp only [Bool.or_eq_true, decide_eq_true_eq] at h
zubzk simp only [Chain.slitTop] at hpy
zubzl simp only [Config.nreg_mk, Machine.upd_same]
zubzm simp only [Geometry.lerp_fst, Geometry.lerp_snd]
zubzn simp only [M]
zubzo simp only [Model.wa, Model.wb, chainModel]
zubzp simp only [SignTest, SymPt.eval] at t₂
zubzq simp only [decide_eq_false_iff_not] at hr
zubzr simp only [dstI] <;> intro he <;> subst he <;> simp_all
zubzs simp only [dstI] <;> omega
zubzu simp only [hqdef, det]; ring
zubzv simp only [lerp_snd]
zubzw simp only [mul_zero, add_zero] at this
zubzx simp only [okB, okI, FScr, FOut]; grind
zubzy simp only [rayPt, one_mul, add_sub_cancel]
zubzz simp only [regI, upd_same]; omega
zucaa simp only [slfLdL, List.mem_cons, List.not_mem_nil, or_false] at hi
zucab simp only [upd, h2, ite_false, ite_true]; grind
zucac simp only [upd_same]; omega
zucad simp only; unfold StCRG at hr
zucaf unfold det; ring
zucag unfold nodeReg rgi; rw [hj0, ← hm.AB]; omega
zucai unfold xv; simp_all
zucaj have : sel = 1 := by show edgeSel _ _ _ _ _ _ _ _ = _; unfold edgeSel; simp_all
zucak have : sel = 2 := by show edgeSel _ _ _ _ _ _ _ _ = _; unfold edgeSel; simp_all
zucas have hk'm : k' < C.m := by rcases h' with h | h <;> [exact h.1; linarith [h.2]]
zucbb intro q h1 h2 h3 h4 h5 h6; rw [hc6]; exact faceRead_other _ _ h1 h2 h3 h4 h5 h6
zucbe obtain ⟨c', k, e, h1, h2, h3, h4, h5, h6, h7⟩ := h
zucbg obtain ⟨d20', w20'⟩ := chainDesc_keep w20 d20 hm hA
      obtain ⟨d21', w21'⟩ := chainDesc_keep w21 d21 hm hA
zucbh obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
zucbi obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
zucbk obtain ⟨hA, hlast⟩ := gs_last (M := M) (Q := Q) (L := L) hE
zucbl obtain ⟨hA0, hlast⟩ := DrvD.gs_last (M := I) (Q := Q) (L := L) hE
zucbq obtain ⟨δ, hδ, -, h1b⟩ := hW
      obtain ⟨δ₂, hδ₂, -, h2b⟩ := hW₂
zucbr rcases hst with ⟨-, hp0, -⟩ | ⟨-, -, -, -, -, hj⟩
zucbs rcases hst with ⟨-, hp0, -⟩ | ⟨hi0, hp0, A, h1, h2, -⟩
zucbt rcases vertex_index_cases P s L hL hn hi with ⟨k, hk, hki⟩ | ⟨k, hk, hki⟩
zucby rintro c' ⟨k, hk1, hkl, hkh, hk2, hk3, hk4⟩
      rw [← hposv] at hkh
zuccb rw [hc3]; show regB c₂.nmem nbrHead c₂.nreg lA = _
      rw [v3A, c2NF, hm2]; exact hNA.2.1
zuccd rw [s2MD]
      rcases hM.hmd with ⟨h0, H, C', hC', hMC⟩ | ⟨h1, -⟩
zucce rw [show v.1 + -1 * s₀ - v.1 = -s₀ by ring, abs_neg, abs_of_pos hs₀0]; linarith
zuccf rw [t50, t51, s50, s51, f50, f51, q50, q51, e50, e51]; omega
zuccg rw [view_lt hi]
      refine hf.2.2.2.2 _ ?_
      obtain ⟨h1, h2, h3, h4⟩ := hY.d1 b n hb
zucci simp only [cAddr, regB, regI, upd, kA, kE, kH, lsI, K1, sw]
      grind
zuccj simp only [cRead, regB, regI, upd, kS, kF, kPe, kPh, K1, sw]
      simp_all
zucck simp only [eIn, regB, regI, upd, eR0, eR1, eR2, S0C.lsI, K1, sw]
      simp_all
zuccm simp only [sw, K1, kqX, Nat.reduceAdd] at hK1 hW
      refine (IRS.block _ hI ?_).mono le_rfl ?_
zucco apply point_ext <;> simp only [lerp_fst, lerp_snd] <;> ring
zuccp by_cases h3 : a = B' + 3 * j + 2
zuccq by_cases h4 : a = B' + 3 * j + 1
zuccr by_contra h0
zuccv have hS := hI.env
      have hpw := hI.pw
      have hlo := hI.lo
zuccw have hS := hostKeys_finite (U := U) hM hF hfin
zucde have hs := bary_sum h x
      have hr := bary_reconstruct h x
zucdf have hu := h.hu
      have h1 := h.h1
      have h2 := h.h2
      set τ := tau Q u L h.h1 h.h2 with hτ
zucdi have hxlo := hI.xlo
      have hhiy := hI.hiy
      have hyn := hI.yn
zucdj intro a b harc
      obtain ⟨i₀, hi₀, hir, his, hie⟩ := hArcs.2.2.1 r hr a b harc
zucdk intro w hw
zucdl obtain ⟨-, -, -, reg, hRC, -, -, hRO, -⟩ := id hN
zucdm obtain ⟨-, -, hArcs, -⟩ := hregs
zucdn obtain ⟨-, -, hEb, -⟩ := hwfw.2 Hs J.whole hJ.2.2
      have hCd7 := chainDescAt_copy hJ.2.2 hEb mem7c hcopy7
zucdo obtain ⟨a1, a2, a3⟩ := hag u hu
zucdq obtain ⟨c', k, ex, hk, v37, v38, v39, v34⟩ := oBox_exec c hw hW
zucdr obtain ⟨c1, c2, c3⟩ := hch e he
zucdt obtain ⟨c₂, k₂, e₂, hk₂, hM₂, -, -⟩ := hM₁.pop (P := P)
zucdu obtain ⟨c₃, k₃, e₃, hk₃, v64, v65⟩ := fb c₂ e₂.wb_right hm₂ b7 b61 b67 b64
zucdv obtain ⟨h0, h1, h11, h35⟩ := hS
zucdw obtain ⟨h1, h2, h3, h4⟩ := h
zucdx obtain ⟨haR, hav, hat⟩ := S.hval t ht
zucdy obtain ⟨hoff, hkdE, hgap0, hψ0, hm0, hv0, hpar, hpt⟩ := key_map hP hpw hL
zucea obtain ⟨t', ht', rfl⟩ := h.surj f hf
zuceb obtain ⟨t, -, -, rfl⟩ := hp
zucec obtain ⟨σ, hσ, hfree, rfl⟩ := htop
zucee rcases g' τ hτ with h | ⟨h1, h2⟩
zucef rcases ho with rfl | rfl | rfl | rfl | rfl
zuceg rcases hx with h0 | ⟨k, hk, hy⟩
zuceh rintro (h' | ⟨h1, h2⟩) <;> rcases h with h | ⟨h3, h4⟩ <;> linarith
zucei rintro c₄ hI₄ - - ⟨v4, o4, m4⟩
zucej rintro d ⟨σ, hσ, -, rfl⟩
      grind
zucel rw [e']; simp [kidL, regB, regI, upd, k7, k1, e8]; grind
zucen rw [hnc] at hk
      rw [hlohi k hk]
zucer rw [stMem_apply]; split_ifs <;> first | omega | rfl
zuces rw [this]; exact (finite_Iio _).image _
zucet set Am : ℕ → Prop := fun a => g.base 42 ≤ a ∧ a < g.base 42 + g.μ with hAm
zuceu set I := interiorModel Q
      set N := nk I S R
zucev set c := (N.chord k).toSet M Q with hc
zucew set t := (chainModel C).param Q x with ht
zucex simp [regB, regI, upd, oE, oFE, oD, oL, oR, sw, ite_eq_left hs0]
zucey simp [regB, regI, upd, oE, oFE, oD, oL, oR, sw, ite_eq_right hs1]
zucez simp only [Set.mem_Iio] at hx hy
      simp only at hxy
zucfa simp only [hRc.rQ, hRc.rPar, hRc.rVert, hRc.rSz, hi, hRc.one, Nat.add_sub_cancel, r1, r2, r3]
zucfb subst ht
zucfc unfold FreeAt at h ⊢
      filter_upwards [h] with t ht
zucfd unfold Model.wa at hy
      rw [hW] at hy
      rcases he with h' | h' <;> rw [h'] at hy
zucfe unfold cVtx
      rw [show 2 * C.m + 6 - 6 = 2 * C.m by omega, C.sideIdx_two_m]; rfl
zucff unfold nodeNa; rw [hr, ← hm.RB]; omega
zucfg unfold sideLeftOf
zucfh apply List.map_congr_left
zucfi by_cases b0 : c.nreg b < c.nreg K1
zucfj by_cases h : c.nreg r < c.nreg nr
zucfl by_cases hbox : Lst J < lOff J
zucfm by_cases hg : c.nreg 170052 < c.nreg 170011
zucfn by_cases hh : ((chainModel C).wa x.edge).2 = ((chainModel C).wb x.edge).2
zucfo by_cases hodd : c.nreg 170012 < c.nreg 170058
zucfu exact_mod_cast hC.hg
zucfv filter_upwards [nhdsWithin_le_nhds hc] with ε hε
zucgb have g₂ := f₂.1
zucgc have h := hW.lemma23_walk hAdm hfin hdeg hgran
zucgd have h1 := hsub.h1
      have h2 := hsub.h2
      have hu := hsub.hu
      have hee := sub_ee_le hsub
      have hcap := hLγ.trans hS.cap
zucgh have hA' := hA
zucgk have hN := S.hN
      have hNn := S.hNn
zucgm have hQn := hE.hQn
zucgn have hW := hHW
      unfold hostWords at hW
zucgo have ha := interior_wa hbit he
      have hb := interior_wb hbit he
      have hi := iIdx_lt (bit := bit) he
zucgr have hle := Chazelle.Chain.sideE_le (m := C.m) (j := tJ C i) (tJ_lt C i).le
zucgs have hlt := D.isTrap.edgeX_lt hQ D.free hy1 hy2
zucgt have hn := hS.n3
zucgu have hn3 := hG.1.1
zuchd have w₃ := x₃.wb_right
zuche intro O c hI he ha hinv hroom
zuchf intro e
zuchg intro hc
zuchh intro r h1 h2 h3 h4 h5; rw [hc5]; exact nbrRegsL_other _ _ h1 h2 h3 h4 h5
zuchi intro x h1 h2
zuchj obtain ⟨-, -, -, reg, -, -, -, hregs, -⟩ := hE.hNF
zuchk obtain ⟨-, g2, -, -, -, -, -, v7⟩ := gap_walk J hδ
zuchl obtain ⟨H, C, hC, hM, hwf, hsimp, -⟩ := hI.chainS hE hM₀
      subst hM
zuchm obtain ⟨a, b, hab, hcab, -, hopen, hEa, hEb⟩ := hM.ends c hc
zuchn obtain ⟨a, b, hab, hcab, hy, hopen, ha, hb⟩ := hM.ends c hc
zucho obtain ⟨a0, a1⟩ := Corr.key_mem hQA.1 hQA.2.1 hQA.2.2.1
      obtain ⟨b0, b1⟩ := Corr.key_mem hQB.1 hQB.2.1 hQB.2.2.1
zuchp obtain ⟨c', k, ex, hk, a, a'⟩ := hrev c₂ w₂ s30 s32 s02 s31
zuchu obtain ⟨ea, eb, heab, heq, -, heopen, -, -⟩ := hM.ends e he
zuchv obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩ := e1
zuchw obtain ⟨h1, h2, h3, h4, h5, h6, N, hN, hc⟩ := h
zuchx obtain ⟨h1, h2⟩ := hmem
zuchy obtain ⟨hR, h⟩ := h
zuchz obtain ⟨hT, hwD, hdom⟩ := Merge.hit_of_freeAt J.whole hz' hσ hfree
      set T := J.whole.hitParam z σ with hTdef
zucid obtain ⟨k0, k1, k6, -, -, -, -⟩ := hKc
      have hW2 := hctx.2.2.2.2.2
zucie obtain ⟨q10, q11⟩ := q
zucif obtain ⟨s, hs, hws⟩ := mem_iUnion₂.1 hw
      rcases (hS.le s hs).lt_or_eq with hsu | hf
zucig obtain ⟨w1, w2, -, w4, -, w6, w7, w8, w9⟩ := hBW
zucih obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
      obtain ⟨x', hx', hxx⟩ := List.mem_map.1 hc'
zucik obtain ⟨z, hz⟩ := hne
zucil obtain ⟨ε₀, hε₀, hε⟩ := h z hz hzD
      filter_upwards [Ioo_mem_nhdsGT hε₀] with δ hδ
      grind
zucim rcases h with ⟨h0, H, C', hC, hM'⟩ | ⟨-, -, hI⟩
zucin rcases h.2 with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
zucio rcases hM.attach_endpoint hopen hA' with h | h
zucip rcases hMD with ⟨h0, H, C, hC, hM⟩ | ⟨h1, hbit, hM⟩
zuciq rcases hMD with ⟨h0, H, C, hC, rfl⟩ | ⟨h1, hbit, rfl⟩
zucir rcases harc0.2.2.2.2.1 with ⟨⟨c, hc, -⟩, -⟩ | ⟨-, ha, hb⟩
zucis rcases hd with ⟨h0, H, C, hC, rfl⟩ | ⟨h1, hL, hM⟩
zuciz rintro (h | h | h)
zucja rintro c₂ hI₂ - - ⟨⟨n2s, n2s1, k2, -, -⟩, hA2, hm2⟩
zucjb rintro c₃ hI₃ - - ⟨⟨n3e, n3e1, k3, -, -⟩, hA3, hm3⟩
zucjc rintro x ⟨⟨p', t', hA'', rfl⟩, -⟩
      exact hM.trace p' hA''.1 t' hA''.2.1 hA''.2.2.1.le
zucjd rintro ⟨i, hi, hp⟩
zucje rintro ⟨k, hk, hp⟩
zucjf rintro ⟨t, ht, hp⟩
zucjg rw [Finset.mem_insert, not_or] at hr
zucjh rw [List.length_append, List.length_singleton] at hi
zucji rw [Metric.mem_ball, Prod.dist_eq]
      simp only [z', Real.dist_eq, sub_self, abs_zero, add_sub_cancel_left, abs_of_pos hη0]
zucjj rw [e2]
zucjk rw [h.vE, h.vy] at e'
zucjl rw [h.vj, h.vk] at hj
zucjo rw [he]
zucjq rw [hm]
zucjt rw [hr4 r h1 h2 h3, hfr3 r h1, hr2 r h1, hfr1 r h1 h2 h3]
zucju rw [hset]
zucjv rw [hx]
zucjw rw [ite_eq_right]
zucjy rw [mem_ball_iff_abs]
zuckb rw [show c - 6 + d + 6 = c + d by omega, hq] at this
      omega
zuckc rw [v₃, w6, w100]
      by_cases h2 : S + i - 2 * m < 2 * m
zuckd rw [← DrvD.arc_s B.hK hjA'] at sn s0 s1
      rw [← DrvD.arc_e B.hK hjA'] at en e0 e1
zuckg set K1 : ℝ := (κM * κ ^ 2 * 14704 * 3 * 19368 : ℝ) with hK1
zuckh set L := rL R ℓ with hL
zucki set Q := subPoly P l with hQdef
zuckj set T := C.hitParam z σ with hTdef
zuckk set i := e - 6 with hi
zuckl simp [chainModel, interiorModel] at this
zuckm simp [lR0, lR1, lR2, lX, lY, fSE, fSH, fEE, fEH, sw]
zuckn simp [step, h, ht]
zuckq simp only [h1, ↓reduceIte]
zuckr simp only [hL, ↓reduceIte]
zucks simp only [regB, regI]; rw [upd_other _ _ _ h2, upd_other _ _ _ h1]
zuckt simpa [rayPt, hy] using this
zucku unfold BestOK
zuckv unfold Model.key at hk
zuckw unfold Model.pos; simp_all
zuckx unfold addL; grind
zucky unfold sidePt
zuckz by_cases h0 : d = 0
zucla by_cases hL : Mountain.LeftInside Q
zuclb by_cases hd : d = 0
zuclc by_cases hi0 : i = 0
zucld by_cases hup : fv c.nmem A R 10 T < v
zuclg exact (Nat.mod_eq_of_lt h).symm
zuclh exact h'
zucli exact label_right3 J hP hS₂.2.1 hS₂.1 hG hV' hV hL hRL
zuclj exact upd_other _ _ _ hr
zuclk ext v
      simp only [Finset.mem_filter, Finset.mem_inter, mem_sideSet h hch hT hB hI, mem_sub]
      unfold OnSide
      simp_all
zuclm filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hr] with s hs hs'
zuclu have hM := hM₀.fix hI
zuclv have hM := walkAx_of_goodModel hE.hGM
zuclw have hN := hNW.holds
      obtain ⟨aB, aCh, aRg, aLst, aArc, aSeq⟩ := nf_areas hNW
zuclx have hNA := hN'.nfAt
      obtain ⟨hB7, -, hab, hrb, hlb, -⟩ := nf_bounds hN'
zucly have hNF := hE.hNF
      rw [hM'] at hNF hne
zucma have hU := g.U_ge; have hE := g.END_eq; have b3 := g.base_eq 3; have b36 := g.base_eq 36
zucmf have hmx := Y_max_le (P := P) (a := c.nreg 170046) (b := c₁.nreg 170059)
zucmi have hn := chainModel_n C
zucmk have hne := h.nd_ne hE hc
zucmp have hsa := (side_arc hC.hM hC.hF hh hPa hZa hne hρ hG hS hori hp₀ ht₀ hfG₀).1 rfl
zucmq have hsa := (side_arc hC.hM hC.hF hh hPa hZa hne hρ hG hS hori hp₀ ht₀ hfG₀).2 rfl
zucmt have hxi := hint δ hδ0 hδδ
      set a := W.vtx p with ha
      set b := W.vtx _ with hb
zucmz have hτ := tpos_lt J.left J.m₁
zucna have k0 := k0_of hE hI₁
zucnd intro G hG ρ hρ hS
zucne intro U hU
zucnf intro j hj hmem
      rw [ea, ev, eb] at hmem
      rw [hQn] at hj ⊢
zucng intro m hm
zucnh intro q hq; simp only [buildL, List.mem_cons, List.not_mem_nil, or_false] at hq
      unfold Scr; omega
zucni intro r hr; rw [hc2]; show regB c₁.nmem [.copyN lNF _] c₁.nreg r = _
zucnj intro sh Bs F X Ok P W c₀ J N₁ N₂ c cw cs co c' E hL hIt hd
zucnk left; rw [this]; unfold arcA; grind
zucnl left; unfold sideInArc; simp_all
zucnm let Wr : ℕ → Prop := fun r => R + 16 ≤ r ∧ r < R + 300
zucnn obtain ⟨b, hb, rfl⟩ := code_of_dir hσ
zucno obtain ⟨b, hb, rfl⟩ := lv_iff.mp hp
zucnp obtain ⟨b1, b2⟩ := hF.best x hx htx
zucnq obtain ⟨b1, hb2, -⟩ := Restore.nf_bounds hNW
zucns obtain ⟨d', k, ex, hk, hI', h40, kp, mem⟩ := toNext hnd
zucnv obtain ⟨hpS, hxy, hmod, heen, hee, hL1, hwtL, hwtn⟩ := qplan q
zucnx obtain ⟨hy, ha, hb⟩ := hxc
      simp only [rayPt_fst, rayPt_snd] at hy ha hb
zucny obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
zucoa obtain ⟨kB0, kB1⟩ := Corr.key_mem hB.1 hB.2.1 hB.2.2.1
zucob obtain ⟨n1, n2, n3, n4, n5, n6, n7, -⟩ := ne_of_bgap hr
zucoc obtain ⟨q, hq, hq'⟩ := List.mem_map.1 h
zucod obtain ⟨r, hr, hreq⟩ := List.mem_map.1 hmem
zucoe obtain ⟨r, hr, hxr⟩ := List.mem_flatMap.1 hx
zucof obtain ⟨r, hr, hxr⟩ := mem_flat.1 hx
zucog obtain ⟨r, hr, rfl⟩ := mem_map.1 hx
zucoh obtain ⟨t, ht, e⟩ := List.getElem_of_mem this
zucoj obtain ⟨u1, u2, -⟩ := bp h1
zucom obtain ⟨ε₀, hε₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hall
zucoo push Not at hab
      have hq1' := abs_lt.1 hq1
      have hq2' := abs_lt.1 hq2
      rcases le_abs'.1 hab with ha | ha
zucop rcases h1.lt_or_eq with h | h
zucoq rcases ha.lt_or_eq with ha' | ha'
zucor rcases hb with hb | hb
zucos rcases hdir with rfl | rfl
zucot rcases hk with hk | hk
zucou rcases hmd with ⟨-, H, C', hC', hMC⟩ | ⟨h1, -⟩
      swap
zucov rcases hmem with h | h
zucow rcases hr with hr | rfl
zucox rcases ht0.lt_or_eq with ht0' | ht0'
zucoy rcases sA_top (C := C) with ⟨h, -⟩ | ⟨h, h0⟩ <;> omega
zucoz rcases z with x | t
zucpg rintro (rfl | rfl)
zucph rintro c' ⟨f1, f2, f3, f4⟩
zucpi rintro c'' ⟨⟨L', a', s', g', geo'⟩, fr, hA', hm'⟩
zucpj rintro k ⟨c, ⟨x, hx, rfl⟩, p, t, hA, rfl⟩
zucpk rw [Finset.mem_range] at hi
zucpl rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
zucpm rw [List.mem_range] at hi
zucpn rw [c1] at s5; rw [c2] at s6; rw [c3] at s7
      omega
zucpp rw [e0, e1]
zucpq rw [ek, ek'] at hk
      obtain ⟨he, hp⟩ := key_inj hA.2.1 hA.2.2.1 hA'.2.1 hA'.2.2.1 hk
zucpr rw [h, add_zero] at hdt; exact_mod_cast hdt
zucps rw [hI₂.mem, h30]; unfold memT; grind
zucpu rw [ha, hb]
zucpv rw [hb] at hH'
      obtain ⟨-, -, hEb, -⟩ := ww.2 H J.whole hJ.2.2
zucpw rw [hl] at h5 ⊢
      simp only [List.length_cons] at h3
      simp only [degCount] at h4
zucpx rw [hlen] at hi
zucpy rw [hwa, hwb]
zucqa rw [ite_eq_right h0]
zucqb rw [one_mul] at this
zucqg rw [vtx_arc P s L h.1, vtx_arc P s L h.2.1, vtx_arc P s L h.2.2]
      rfl
zucqh rw [← Real.rpow_natCast, ← Real.rpow_mul h0]; norm_num
zucqi rw [← heq]
zucqj rw [← hq]; exact Geometry.det_lerp_self _ _ _
zucqk set C := ch _ u L h1 h2 with hCd
zucql set C := hostChain Q S R g h3 with hC
zucqn set kind := c.nreg oKd with hkind
      set k := c.nreg oKk with hkk
      set b := c.nreg oB with hbb
zucqo set n := M.W.n with hn_def
zucqq simp only [BSQ, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
zucqr simp only [BregPhase, Bool.or_eq_true, decide_eq_true_eq] at hr
zucqt simp only [Bside, Bool.or_eq_false_iff] at h; simp_all
zucqv simp only [List.mem_append] at hq
      rcases hq with h | ((h | h) | h)
zucqw simp only [Set.mem_iUnion]
zucqx simp only [ZKeep, Bool.or_eq_true, decide_eq_true_eq] at hr
zucqy simp only [det, hx, sidePt, lerp_fst, lerp_snd, ← ha, ← hb]; ring
zucra simp only [ite_true, zero_add, one_ne_zero, ite_false]
zucrb simp only [normRep, h1, h2, h3, h4, ↓reduceIte, RepAt, Nat.reduceAdd]
      simp_all
