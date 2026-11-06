module

public import Chazelle.MacT.Base

public section

set_option hygiene false

zg zuixf have hU' := hU
zuixh have hWh := hW
zuixk have ha := F₂plus_subset J hS₂.2.1 hm
zuixl have haddr := hH.addr
zuixm have harc := chainArcs_one hsub hs hLγ
zuixn have hb' := hb
zuixo have hc := h.walk.c_lt
zuixp have hcp' := hcp
zuixq have hctx2 := hctx.transport cd2 hm2' hA2'
zuixs have hcx := subset_S₂x J S₂ hc
zuixt have hc₂ := hC.not_cut₂ hd ht hcut
zuixv have hd0 := hD.hd0
zuixw have he := shoot_end_mem hc ha hfree
zuixx have hfin := hL.1.1
zuixy have hfree := harc.2.2.2.2.2.1
zuiyc have hgL := hS.hgL
zuiyd have hk := DrvD.key_s_lt_e B.hK hE hlt
zuiyh have hlow := hI₁.hm
zuiyi have hm := h.nodeMem
zuiyj have hm := hf.2.2.1
zuiyk have hmn := h.m_lt
zuiyo have hn := S.hn
zuiyp have hn3 := hE.hG.1.1
zuiyq have hnd : E.Nodup := hperm.nodup_iff.2 List.nodup_range
zuiyr have ho := hC.off_M hd'' ht''.1.le ht''.2
zuiys have hoA := hC.off_M hd le_rfl zero_lt_one
zuiyt have hp := prod_nonneg_of_cross_zero h
      unfold sideDot
zuiyu have hpR := h.prg_lt _ c1 c2
zuiyv have hpos := C.chordParam_pos hk hσ h
zuiyw have hpos := Visibility.chordParam_pos hQ hi hdir
zuiyx have hps := innerSeg_subset _ _ hp
zuiza have hr := C.radius_pos
zuizd have hr := hI.i0 e he hp
zuizg have hs0 := hs3
zuizh have hst' := hst
zuizi have hsucc := NFLoc.preLen_succ P.n H hr
zuizj have hsucc := NFLoc.preLen_succ n H hr
zuizk have hsys := hM.sys S hFam.2.1 hFam.1
zuizl have hsys := hM.sys _ hN.1.2.1 hN.1.1
zuizn have hw7 := e7.wb_right
zuizo have hw8 := e8.wb_right
zuizr have hw₆ := e₆.wb_right
zuizt have hzb := Visibility.chordEnd_mem_boundary hQ hi hdir
zuizu have hzn := hv.hz_lt
zuizv have hε0' := hε0
zujab have k := hf.1
zujac have k1 := E.k1
zujad have k2 := hKc.2.2.2.2.2.1
zujaf have o := hR.one
zujag have w₂ := ex₂.wb_right
zujah have w₄ := x₄.wb_right
zujai have w₈ := e₈.wb_right
zujaj have w₉ := e₉.wb_right
zujap intro H' hH'
zujaq intro P W c hw h _
zujar intro P W c hw hPre hroom
zujas intro P hP hPR
zujat intro a b hab
zujau intro a h1 h2
zujav intro b0 b1 _ _ h0 h1
zujaw intro c hc q hq hqD hqv
zujax intro c' hc' hA'
zujay intro h1 h2
zujba intro hh
zujbb intro hm
zujbc intro ht; by_contra h0
      apply hnv
zujbd intro i a b
zujbe intro it hit
zujbf intro j
zujbg intro j hj h
zujbh intro k hk h
zujbi intro p t hp ht0 ht1 _
zujbj intro p t hp ht0 ht1 hpt
zujbk intro pc hpc
zujbl intro r hr hra
zujbm intro s hs hs0
zujbn intro t
zujbo intro t ht hmem
zujbp intro t ht1 ht2
zujbq intro v
zujbr intro w hw hk
zujbs intro w hw hwm hw' y hy
zujbt intro x y hxy
zujbu intro x; unfold sideInArc; grind
zujbv intro x; unfold sideInArc; simp_all
zujbw intro y h1 h2
zujby left; grind
zujca linarith [C.top_snd_lt_radius]
zujcb linarith [hA.2.2.1]
zujcc linarith [ht.2]
zujce push Not at hpock
zujcf push Not at h₁
zujcg push_cast at hj
zujci rcases Finset.mem_union.mp hq with hq | hq
zujcj rcases Finset.mem_union.mp hqf with h | h
zujck rcases List.mem_append.1 hd' with h | h
zujcl rcases List.mem_append.1 hpc with hpc | hpc
zujcm rcases List.mem_append.1 hy with hy | hy
zujcn rcases List.mem_cons.1 hc' with rfl | hc'
zujco rcases List.mem_cons.1 hi' with rfl | hi'
zujcp rcases List.mem_cons.1 hz' with rfl | h
zujcq rcases List.mem_cons.mp hq with rfl | hq
zujcr rcases Nat.eq_or_lt_of_le hii with rfl | hlt
zujcs rcases Nat.eq_zero_or_pos K with h0 | hpos
zujct rcases Nat.eq_zero_or_pos L with hL | hL
zujcu rcases Nat.eq_zero_or_pos L.length with hK | hK
zujcv rcases Nat.eq_zero_or_pos d with rfl | hd
zujcw rcases Nat.eq_zero_or_pos i with rfl | hi'
zujcx rcases Nat.eq_zero_or_pos i with rfl | hpos
zujcy rcases Nat.eq_zero_or_pos j with hj | hj
zujcz rcases Nat.eq_zero_or_pos k with h0 | hpos
zujda rcases Nat.eq_zero_or_pos p with hp0 | hp0
zujdb rcases Nat.eq_zero_or_pos p with rfl | h0
zujdc rcases Nat.eq_zero_or_pos q with h0 | h0
zujdd rcases Nat.eq_zero_or_pos x with rfl | hpos
zujde rcases Nat.eq_zero_or_pos γ with h0' | hpos
zujdf rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hB.hi with h0 | h0
zujdg rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hw.1 with hz | ho
zujdh rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h' | rfl
zujdi rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
zujdj rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
zujdk rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | rfl
zujdl rcases Nat.lt_succ_iff_lt_or_eq.mp hxi with hxi | hxi
zujdn rcases eq_or_lt_of_le h2 with e | e
zujdo rcases eq_or_lt_of_le hdd with e | hlt
zujdp rcases eq_or_lt_of_le htt with h | h
zujds rcases hl2 hc with h | h
zujdt rcases hl2 hc with hs | he
zujdv rcases loc1 hc' with h0 | h0
zujdw rcases lt_abs.1 hgt with h1 | h1
zujdx rcases lt_or_eq_of_le hj' with h2 | h2
zujdy rcases lt_or_eq_of_le hp with hp' | hp'
zujea rcases lt_or_gt_of_ne hN with hN' | hN'
zujeb rcases lt_or_gt_of_ne hNFo with h | h
zujec rcases lt_or_gt_of_ne hab with hlt | hgt
zujed rcases lt_or_gt_of_ne hcb with hlt | hgt
zujee rcases lt_or_gt_of_ne hdu with hn | hp
zujef rcases lt_or_gt_of_ne hdw with hn | hp
zujeg rcases lt_or_gt_of_ne he with h | h
zujeh rcases lt_or_gt_of_ne heq with h | h
zujei rcases lt_or_gt_of_ne hhor with hdown | hup
zujej rcases lt_or_gt_of_ne hlr with h | h
zujek rcases lt_or_gt_of_ne hne with hlt | hlt
zujel rcases lt_or_gt_of_ne hne12 with h12 | h12
zujem rcases lt_or_gt_of_ne hq2 with hlt | hlt
zujen rcases lt_or_gt_of_ne huw1 with h | h
zujeo rcases lt_or_gt_of_ne hxy with h | h
zujep rcases mem_addL hx with hx | hx
zujeq rcases mul_eq_zero.1 h with h | h
zujer rcases mul_eq_zero.1 h3 with h | h
zujes rcases mul_eq_zero.1 this with h' | h'
zujet rcases orient_eq P with ho | ho
zujev refine Prod.ext ?_ ?_
zujew refine Prod.ext rfl ?_
zujex refine absRec_transport hrec ?_ ?_ ?_ ?_
zujez refine h.pop_keep htop fun hr => ?_
zujfa refine hfree j j' hj hj' ?_
zujfb refine key _ hwc r hb ?_
zujfc refine lt_of_le_of_ne hle fun heq => ?_
zujfg refine spec_ifLtN_true c2 ?_
zujfh refine spec_ifLtN_true h0 ?_
zujfz right; nlinarith
zujga right; simp_all
zujgb rintro (x | t) hz
zujgc rintro c' hc'
zujgd rintro e (he | he)
zujge rintro p ⟨hp, hc⟩
zujgf rintro p ⟨hp, hp'⟩
zujgg rintro rfl ⟨h1, h2⟩
zujgh rintro rfl; simp_all
zujgi rintro x ⟨hx, hxD⟩
zujgj rintro x ⟨hxA, hxB⟩
zujgk rw [C.mem_dom_iff] at hnd
      tauto
zujgl rw [C.sideWalk_next_last β]; rfl
zujgm rw [Function.iterate_succ_apply]
zujgn rw [Geometry.lerp_one]
zujgo rw [Gran.ncard_F hnf] at h
zujgq rw [List.getD_eq_getElem _ _ hi']
zujgr rw [List.length_append]
zujgs rw [List.length_map]
zujgt rw [List.map_append]
zujgu rw [List.mem_cons, hcop]
      constructor
zujgv rw [List.mem_filter] at ha hb
zujgw rw [List.nodup_flatMap]
zujgx rw [List.nodup_iff_injective_get]
zujgy rw [Machine.upd_apply]
zujgz rw [Metric.isOpen_iff]
zujha rw [Metric.mem_closure_iff]
zujhb rw [Model.arcWt_eq]
zujhd rw [Nat.div_lt_iff_lt_mul hpos]; omega
zujhf rw [Nat.mod_eq_of_lt h] at he
zujhg rw [Nat.mod_eq_of_lt hgN] at his
zujhh rw [Visibility.segment_horizontal_eq_hseg hy] at h
zujhj rw [abs_lt] at h1 h2
zujhk rw [abs_lt] at hb1 hb2
zujhn rw [arcList_pos hK, length_map]
zujho rw [arcWt_eq']
zujhq rw [cover_of_lt hx, List.length_cons]
zujhr rw [cw_getElem hm] at this
zujhs rw [det_offset]
zujht rw [dirCode_eq]
zujhv rw [e0]
zujhw rw [e4]
zujhx rw [e5]
zujhy rw [eBX, eXA]
      constructor
zujhz rw [e]; exact h2
zujia rw [filled_sdiff_boundary_eq hP]; simp_all
zujib rw [h.n_eq]
zujic rw [h4]
zujid rw [hC.off_M₂ hdL ht0 ht1]
zujie rw [hC] at hcls ⊢
zujif rw [hP, ← hQn]
zujig rw [hP]
zujih rw [hQn]
zujii rw [hT1 hT, hkeq]
zujij rw [hT2 hT, hkeq]
zujik rw [hT]
zujil rw [hW] at heq hp
zujim rw [hW] at hy ⊢
zujin rw [hX]; simp only
zujip rw [hb] at hW ⊢
zujiq rw [hb] at viaGen ⊢
zujir rw [hce]
zujis rw [hc₆]; exact this
zujit rw [hd']
zujiu rw [he'd] at h1 h2
zujiv rw [hev] at hyes hno
zujiw rw [he₁] at hns ⊢
zujix rw [hf]
zujiy rw [hget]
zujiz rw [hidx]
zujja rw [hk]
zujjb rw [hk] at hl1 hl2
zujjc rw [hk] at hroom' ⊢
zujjd rw [hke.1 hj1] at hx
zujjf rw [hl1] at hlen ⊢
zujjg rw [hl] at hne ⊢
zujjh rw [hlen]
zujji rw [hmem']; unfold ssWM
zujjj rw [hmem]
zujjk rw [hmin] at hp hc
zujjl rw [hm₁]; unfold mem1
zujjm rw [hnW] at hs1 he1
zujjn rw [hn] at hi hj
zujjq rw [hoffp]
zujjr rw [holeAt_eq]; unfold eHole
zujjs rw [hp'] at hA hend
zujjt rw [hpos] at hmem hedge
zujju rw [hq] at s1 s2
zujjv rw [hr] at hne ⊢
zujjw rw [hvq] at hfree hAt
zujjx rw [hvy]
zujjy rw [hw]
zujjz rw [hx] at hsp hwf
zujka rw [hy]
zujkb rw [hμ]
zujkc rw [hψz z h1 h2]
zujkd rw [ite_eq_left hd]; omega
zujkh rw [ite_eq_right hup]; grind
zujkj rw [max_eq_left h]; nlinarith
zujkk rw [max_eq_left hgt.le] at h2
zujkl rw [max_eq_left hgt.le]; nlinarith
zujkm rw [max_eq_right h]; nlinarith
zujkn rw [max_eq_right hlt.le] at h2
zujko rw [max_eq_right hlt.le]; nlinarith
zujks rw [mem_ball_iff_abs] at hp ⊢
zujkt rw [mem_sub, Finset.mem_singleton]
      constructor
zujku rw [mem_sub, mem_sub]
      constructor
zujkv rw [min_eq_left h]; nlinarith
zujkw rw [min_eq_left hlt.le] at h1
zujkx rw [min_eq_right h]; nlinarith
zujky rw [min_eq_right hgt.le] at h1
zujkz rw [min_eq_right hgt.le]; nlinarith
zujla rw [mir_n] at hi hj
zujlb rw [n_arc] at hi hj
zujlc rw [n_rotate] at hi hj
zujld rw [param_eq hQ hdh hp]
zujle rw [point_ext_iff]
zujlf rw [popLoop_singleton]
zujlg rw [pow_add]
zujlh rw [qm]
zujli rw [rm_F hE h hc]
zujlj rw [segL_congr hbo2]; omega
zujlk rw [selectLast_cons]
zujll rw [shear_vtx, shear_vtx]
      grind
zujlm rw [sideIdx_eq]; congr 1
zujln rw [this, mul_left_comm]
      simp_all
zujlo rw [this]; exact h.left_not
zujlp rw [this]; exact h.right_not
zujlq rw [this]; exact hch.left_mem
zujlr rw [this]; exact hch.right_mem
zujls rw [this]; exact hh
zujlt rw [transpose_n] at hi hj
zujlw rw [← Nat.add_assoc] at this
zujlx rw [← Nat.mul_succ]; simp_all
zujly rw [← Nat.succ_mul]; grind
zujlz rw [← fam_diff hE hc]
zujma rw [← hD.R] at hX
zujmb rw [← h] at hu'
zujmc rw [← h]; omega
zujmd rw [← hb] at hArr
zujme rw [← hk] at e
zujmf rw [← hpt] at hl
zujmg rw [← hpy]; nlinarith
zujmh rw [← hrUe] at harc
zujmi rw [← pow_succ']; simp_all
zujmj set A := c.nreg ALLOC with hAdef
zujml set B₀ := c.nreg ALLOC with hB₀
zujmm set D := c₀.nreg _ with hD
zujmo set Fg := F _ with hFg
zujmp set M := chainModel J.left with hMd
zujmq set N := nk M S R
zujms set Q := P.rotate i with hQdef
zujmt set T := c₀.nreg TLR with hTd
zujmu set W := C.sideWalk C.sideBeta with hW
zujmw set e := c.nreg 50002 with he'
zujmx set g := gOf c with hg
zujmy set j := c.nreg 207 with hjdef
zujmz set j := c₁.nreg lJ with hjd
zujna set l := E.pts r with hl
zujnb set r := st.ord h with hrdef
zujnc set t := c₃.nreg 50105 with htdef
zujnd set σ := dirOf _ with hσd
zujne set σ := dirOf d with hσdef
zujnh simp [Host.pts]
zujni simp only [Bool.not_eq_false] at hc
zujnj simp only [Bool.not_eq_true] at hcon
zujnk simp only [Chain.chordEnd_fst] <;> linarith
zujnl simp only [Chain.slitTop] at hy
zujnm simp only [Config.nreg_mk, upd]
zujnn simp only [Finset.union_self] at F
zujno simp only [Function.iterate_zero, id]
zujnp simp only [Geometry.add_fst, Geometry.smul_fst]
zujnq simp only [Geometry.lerp_fst] at hz'
zujnr simp only [List.length_cons] at hi
zujns simp only [Model.wa, Model.wb]
zujnt simp only [Nat.add_zero] at q0
zujnu simp only [Nat.sub_zero] at h
zujnv simp only [Prod.snd_sub]; linarith
zujnw simp only [QRel] at hrel
zujnx simp only [Rd] at hq
zujny simp only [Set.mem_ofPred_eq, Set.mem_union]
zujnz simp only [Set.mem_ofPred_eq] at hy
zujoa simp only [ShotList.arcAt, upd]
zujob simp only [Src.pt, SymPtIn]
zujoc simp only [View.key] at hlt
zujod simp only [View.tail] at hwt
zujoe simp only [ViewOK] at hv
zujof simp only [add_zero] at he
zujog simp only [boOf, blkOf]
zujoh simp only [chordEnd_fst] at this
zujoi simp only [decide_eq_false_iff_not]; omega
zujoj simp only [det]; nlinarith
zujok simp only [eHole, key_hole]
zujom simp only [interiorModel] at he
zujon simp only [lerp_fst, lerp_snd]
zujoo simp only [lerp_snd] at hmid
zujop simp only [lerp_snd]; grind
zujoq simp only [ne_eq] at hxy
zujor simp only [param_hgt0, add_zero]
zujos simp only [phi, stretchPt]
zujot simp only [qvx] at h
zujou simp only [rayPt]; ring
zujov simp only [rayPt_fst, Geometry.lerp_fst]
zujow simp only [shear, List.map_map]
zujox simp only [sideL]; linarith
zujoy simp only [sideR]; linarith
zujoz simp only [sub_zero] at this
zujpa simp only [t3Of] at this
zujpb simp only [vHole, key_hole]
zujpc simp only at e
zujpd simp only at h0
zujpe simp only at hit
zujpf simp only; unfold ARG at hr
zujpg simp only; unfold FlRG at hr
zujph simp only; unfold StDRG at hr
zujpi simp only; unfold StkRG at hr
zujpj simpa using hS1 hx
zujpk simpa using this
zujpl split_ifs <;> rfl
zujpm split_ifs <;> simp
zujpn split_ifs with h0
zujpo split_ifs with ht
zujpp subst h; simp_all
zujpq subst hk'
zujpr subst hue
      by_cases hcf : CPF f
zujps unfold Bbd at hr; unfold Bco
zujpt unfold IFix at hq
zujpu unfold IniW at hq
zujpv unfold LdW₀ at hq
zujpw unfold ModB; simp_all
zujpx unfold Model.param Model.wa Model.wb
zujpy unfold Model.size
zujpz unfold Model.wa
zujqa unfold Model.wa Model.wb
zujqb unfold NF.F; rw [h]
zujqc unfold NF.region buildNF
      simp_all
zujqd unfold NFLoc.dirOf; grind
zujqe unfold SlfAtt SlfPos at *; simp_all
zujqf unfold St.pop; simp_all
zujqg unfold St.step; simp_all
zujqh unfold bestOf; grind
zujqi unfold cntBelow
zujqj unfold dOf
zujqk unfold det; fun_prop
zujql unfold dq
zujqm unfold initS
zujqn unfold ivB; grind
zujqo unfold lblOf
zujqp unfold midR; linarith [C.coordBound_lt_radius]
zujqq unfold midT; grind
zujqr unfold nArc
zujqs unfold p1; grind
zujqt unfold rY1; grind
zujqu unfold regMem
      grind
zujqw unfold sideCross sideDot at *; grind
zujqx unfold sideCross; ring
zujqy unfold sideInArc at h
zujqz unfold sideInArc at hqk hx ⊢
      grind
zujra unfold sideLeftOf; rw [rayPt_sub_one]
zujrb unfold sidePt; simp_all
zujrd unfold ssWM
      rw [upd_apply]
      grind
zujre unfold stopE stopH
zujrf unfold tabUpd; simp
zujrg unfold wrapK; grind
zujrq all_goals first | omega | skip
zujru all_goals try rw [S₂.r11]
zujrv apply Prod.ext
zujrw apply seg_congr; intro i hi
zujrx apply two_rpow_le_two_rpow
zujry by_cases a : e < B.N
zujrz by_cases a0 : kd = 0
zujsa by_cases a1 : kd = 1
zujsb by_cases h : L ≤ C
zujsc by_cases h : d = 0
zujsd by_cases h : j < S
zujse by_cases h : r = j
zujsf by_cases h' : r' = r
zujsg by_cases h0 : 0 < t
zujsh by_cases h0 : L = 0
zujsi by_cases h0 : eh = 0
zujsj by_cases h0 : j = 0
zujsk by_cases h0 : r = 0
zujsl by_cases h0 : z = 0
zujsm by_cases h1 : L = lim
zujsn by_cases h1 : a₁ = 1
zujso by_cases h1 : st.nlive = 1
zujsp by_cases h2 : 1 < b
zujsq by_cases h2 : e < 2
zujss by_cases h4 : e < 4
zujst by_cases h5 : p ≤ 5
zujsu by_cases h6 : e < 6
zujsv by_cases h9 : r = 9999
zujsw by_cases hB : b < K
zujsx by_cases hT0 : C.topIdx = 0
zujsy by_cases hac : a ∈ c
zujsz by_cases ham : a < C.m
zujta by_cases hba : b < a
zujtb by_cases hc : h < 1
zujte by_cases hd7 : d < 7
zujtf by_cases hdc : d = c
zujtg by_cases hdd : d = d'
zujth by_cases heK : e < K
zujti by_cases hes : e = X''
zujtj by_cases hfc : f < c
zujtk by_cases hic : i = c
zujtl by_cases hij : j = i
zujtm by_cases hk : k < P.n
zujtn by_cases hkind : k < 1
zujto by_cases hle : L ≤ C
zujtp by_cases hlen : ns.length ≤ 1
zujtq by_cases hlt : ps.length < Nmax
zujtr by_cases hq : x = k
zujts by_cases hqs : q ∈ C.slit
zujtt by_cases hqt : q = st.tl
zujtu by_cases hra : r = ALLOC
zujtv by_cases hs : σb < 1
zujtw by_cases hs1 : σ = 1
zujtx by_cases hsd : s ≤ d
zujty by_cases hthr : Thr J f
zujtz by_cases hui : u = i
zujua by_cases hv : IsVert S w
zujub by_cases hwv : w = v
zujuc by_cases hx0 : h = x0
zujud by_cases hxb : x = b
zujue by_cases hz : h = 0
zujuf by_cases hzP : z ∈ P.boundary
zujug by_cases hzU : z.2 = U.2
zujuh by_cases hz₁ : z ∈ Q₁.boundary
zujui by_cases hz₂ : z ∈ Q₂.boundary
zujuj by_contra hpos
      push Not at hpos
zujuk by_contra hxD
zujum change u < d.cap at hu
zujun classical
      set j := Nat.find hex
zujuo clear hcb
      have hcb := hcb'
zujup clear hroom hγW hm hA h09
zujuq clear hw
zujuv exact hp.2.2.2 i hi hiL h
zujuw exact hp.2.2.2 i hi hiL h1
zujux exact hs
zujuy exact hs.2.2.2 i hi hiL h
zujuz exact hs.2.2.2 i hi hiL h1
zujva exact innerPt_of_mi ch_P hu h.hs this.symm
zujve exact lerp_mem_segment _ _ ht0 ht1
zujvh exact proper_vtx _ _ _ _
zujvj exact sideLeftOf_mir _ _ _ _
zujvo exfalso
      unfold rgNode at hab
      grind
zujvp exfalso; linarith [ht'.1]
zujwb have E₁ := E.frame fe₁ Bedge_env
zujwg have S₄ := keepSet Ft S₃
zujwh have T₂ := keepSetT Fs T₁
zujwi have X := Exec.seq x₁ x₂
zujwj have X₂ := ctx_of_bbd X₁ K₂
zujwr have b1 := hrb _ hr
zujws have b3 := hab _ hj
zujxq have f₂ := exec_frameB e₂ wr_locSetup
zujxw have h := mountain_orient_det P hM
zujyc have h0N := hil 0 hk1
zujyh have h1 := arcs_le_regions hsimp hcan
zujyr have h2i := two_mul_lt_gradeCount hg1 hi
zujyz have hAi := hE.arcOK hch ht
zujzh have hFf := F₂plus_finite J hS₂f
zujzi have hHC := FullDegInt.hc_full hQ hc
zujzs have hNT := win_nt E hI
zujzt have hNWc := hI.nfWithin hE le_rfl
zujzu have hP : J.P.Simple := E.hP
zujzv have hP0 := off_nonneg kP0 hgn
zukae have hS := ChainObs.good hP hDH
zukaf have hS := sideConvR J hP
zukaj have hSM := star_planar M hM
zukaw have ha := Nat.mod_lt U₀ hn
zukay have hadm := Y.adm_G hc hk
zukaz have haq := simple_vtx_succ_ne hQ hk
zukba have hat := hNF.2.2.1 i hi
zukbd have hb := hT.botVtx_lt hP hq
zukbl have hcf := hM.finite_cuts hF hfin
zukbm have hct := htmin c hcS
zukbn have hcut := hnocut _ hx
zukbo have hcyc := hR.cyc c List.mem_cons_self
zukbp have hd := d₂ M hMD
zukbq have hd := h.diag d List.mem_cons_self
zukbu have hdw := hI.deg_word hE hr
zukbx have hf := h.first_lt u hu
zukbz have hfin : F.Finite := hFam.1
zukcj have hhi := hD.rng _ hlv
zukcq have hinc := brkInc X hA
zukdd have hlog := Nat.log_le_clog 2 γ
zukde have hlog := log_le_clog_succ hL1 hLγ
zukdf have hlog' := Nat.mul_le_mul_left 2100 hlog
zukdg have hlogB := log_le_clog_succ hsubB.h1 hLB
zukdi have hlt := tJ_lt C i
zukdp have hm := h ▸ hA.2.2.2.1
zukdz have hn := n_subPoly P l
zukec have hnd := hM.nd p hp
zukee have hne := C.sideVertex_succ_ne hP k
zukef have hne := hd'.vtx_ne P hQ
zukeh have hnw := piece0_nowrap hx hy
zukei have ho'' := originIn_unique ho' ho
zukel have hp := h.n_eq.symm ▸ hA.1
zukem have hp := hreg r hr
zukfe have hr := h.ord_lt _ hp
zukfk have hs := C.sideTour_step C.sideBeta i
zukfq have hsi := hsucc i hi
zukfs have hsome := stp_key_some hI hd
zukgc have ht := tpos_lt J.right 0
zukge have ht' := tpos_lt C' J'
zukgj have hu2 := snd_le_of_lexLE_of_fst_eq hu hu1
zukgl have huv := simple_vtx_succ_ne hP hi
zukgo have hvμ := hlt v hv
zukgp have hw2 := snd_le_of_lexLE_of_fst_eq hw hw1
zukgy have hxA := hbk j hj
zukhf have hy := congrArg Prod.snd he
zukhm have hzfree := Chazelle.Chain.regionsIn_subset hR hzR
zukhy have k0₁ := k0_of hE hI₁
zukhz have k0₅ := k0_of hE hI₅
zukiz intro a ha b hb e
zukja intro c hc c' hc' hcc
zukjb intro c hc c' hc' hdd
zukjc intro c hc c' hc' hne
zukjd intro c' hI' hc hlt hroom'
zukje intro d₁ h₁ d₂ h₂ e
zukjf intro d₁ k₁ d₂ w₂ k₂
zukjg intro g hg g' hg' h
zukjh intro h1 h2; apply h1
zukji intro h2
zukjj intro hs x₁ x₂ h₁ h₂
zukjk intro i hi i' hi' h
zukjl intro i i' h1 h2 h3
zukjm intro j hj j' hj' he
zukjn intro j hj j' hj' hjj
zukjo intro j j' hj hj' hjj
zukjp intro k hk hky hk1 hk2
zukjq intro p
zukjr intro p hp t ht0 ht1
zukjs intro q q' hq hq' e
zukjt intro r a1 a2 a3 a4
zukju intro t ht i hi hmem
zukjv intro t' ht' x₀ hx hcov
zukjw intro v hv hvq h1 h2
zukjx intro w hw hwy h1 h2
zukjy intro x hx hv k hk
zukka nlinarith [hs.2, hmS.2]
zukkc nlinarith [mul_nonneg hs0 hτ''.le]
zukkd nlinarith [mul_pos hσ2 this]
zukkh rcases dC' with h' | h'
zukki rcases dC'' with h3 | h3
zukkj rcases e1 with e | e
zukkk rcases e2 with e | e
zukkl rcases h with _ | k
zukkm rcases h0.lt_or_eq with h | h
zukkn rcases h0.lt_or_eq with h0 | h0
zukko rcases h1 with h1 | h1
zukkp rcases h1.lt_or_eq with h1 | rfl
zukkq rcases h2 with h2 | h2
zukkr rcases hA.lt_or_eq with h2 | h2
zukks rcases hB.lt_or_eq with h2 | h2
zukkt rcases hD with h0 | h1
zukku rcases hU2 with h | h
zukkv rcases ha1.lt_or_eq with h | h
zukkw rcases hb.lt_or_eq with hb' | hb'
zukkx rcases hb1.lt_or_eq with h | h
zukky rcases hbp.lt_or_eq with hbp | hbp
zukkz rcases hc with rfl | hcT
zukla rcases hc0 with rfl | rfl
zuklb rcases hcase with h | h
zuklc rcases hcase with h0 | hp
zukld rcases hcases with e | e
zukle rcases hcr with hcr | hcr
zuklf rcases hend with he | he
zuklg rcases hend with hoe' | hoe'
zuklh rcases hf with rfl | rfl
zukli rcases hf.1 with h | h
zuklj rcases hge with hge | heq
zuklk rcases hin with h' | h'
zukll rcases hin with hin | hin
zuklm rcases hjj with rfl | rfl
zukln rcases hk.lt_or_eq with hk | hk
zuklo rcases hle.lt_or_eq with hlt | heq
zuklp rcases hle.lt_or_eq with hlt' | heq
zuklq rcases hlo.lt_or_eq with hlt | heq
zuklr rcases hloc with h | h
zukls rcases hlt with hlt | hpz
zuklt rcases hnot with hlt | hlt
zuklu rcases hoZ with h | h
zuklv rcases hon with h | h
zuklw rcases hp.lt_or_eq with h | h
zuklx rcases hp3 with rfl | rfl
zukly rcases hpa'.lt_or_eq with h1 | h1
zuklz rcases hpb'.lt_or_eq with h1 | h1
zukma rcases hpos with hE | hval
zukmb rcases hq' with rfl | rfl
zukmc rcases hqa.lt_or_eq with h | h
zukmd rcases hs with rfl | rfl
zukme rcases hs0.lt_or_eq with hs | hs
zukmf rcases hs1.lt_or_eq with h | h
zukmg rcases hs1.lt_or_eq with hs1 | rfl
zukmh rcases hstop with h | h
zukmi rcases ht.lt_or_eq with h | h
zukmj rcases ht0.lt_or_eq with h0 | h0
zukmk rcases ht0.lt_or_eq with htp | ht00
zukml rcases ht0.lt_or_eq with htp | htp
zukmm rcases ht1.lt_or_eq with h1 | h1
zukmn rcases hv with hv | hv
zukmo rcases hw with rfl | rfl
zukmp rcases hwa.lt_or_eq with h1 | h1
zukmq rcases hwb.lt_or_eq with h2 | h2
zukmr rcases hy with rfl | rfl
zukms rcases hz with hz | hz
zukmu rcases hza.lt_or_eq with h | h
zukmv rcases hzb.lt_or_eq with h | h
zukmw rcases hκ with h1 | h1
zukmx rcases hρd with h | h
zukmy rcases hσ with hσ1 | hσ1
zukmz rcases hτ' with rfl | rfl
zukna rcases i with _ | j
zuknb rcases this.1 with e | e
zukno refine param_of_lerp _ Q hne ?_
zuknw rintro (a | b)
