module

public import Chazelle.MacT.Base

public section

set_option hygiene false

zg zuknx rintro (h'' | h'')
zukny rintro c₁ hI₁ - - hc₁
zuknz rintro c₁ hI₁ hA1 hA1' hc1
zukoa rintro c₃ hI₃ hA3 hA3' hc3
zukob rintro c₃ hI₃ hA₃ hA₃' hc3
zukoc rintro c₄ hI₄ - - rfl
zukod rintro c₅ hI₅ - - hc5
zukoe rintro d₁ hI₁ hA₁ hA₁' hd₁
zukof rintro d₄ hI₄ - - rfl
zukoh rintro ⟨a, b⟩
zukoi rintro ⟨hc, ht⟩
zukoj rintro ⟨he, hh⟩
zukok rintro ⟨hi, hc⟩
zukol rintro ⟨hw1, hw2⟩
zukom rintro ⟨hz, hp⟩
zukon rintro ⟨m, hm⟩
zukoo rw [C.chainEdge_eq] at hmem
zukop rw [C.edgeIdx_succ] at h2
zukoq rw [C.mem_slit_iff] at h
zukor rw [C.sidePt_tour β hi]
zukos rw [C.sideWalk_vtx_four]; grind
zukot rw [C.sideWalk_vtx_tour _ hi]
zukov rw [C.sideWalk_vtx_two]; grind
zukow rw [Chazelle.Chain.sidePt_zero, Geometry.lerp_one]
zukoy rw [Chazelle.Geometry.segment_comm]; omega
zukoz rw [Cost.beta_eq] at this
zukpa rw [E.h61] at ht
zukpb rw [Existence.n_rotate, hostPoly_n]
zukpc rw [E₂.h61] at hx₂
zukpd rw [F_buildNF]; omega
zukpg rw [Function.onFun, Finset.disjoint_left]
zukph rw [Function.update_self, Function.update_self]
zukpi rw [F₂.2.2.1, m₁]
zukpj rw [F₂.2.2.2, F₁.2.2.2.2.1]
zukpk rw [J.whole_set] at h
zukpm rw [List.getElem_map, List.getElem_map]
zukpn rw [List.length_append]; omega
zukpo rw [List.map_append, List.map_singleton]
zukpp rw [List.map_append, List.nodup_append]
zukpq rw [List.mem_range] at hj
zukpr rw [List.mem_range] at hr
zukps rw [List.mem_singleton] at ht
zukpt rw [Metric.mem_ball, Prod.dist_eq]
zukpu rw [NFLoc.getD_of_lt _ hk]
zukpv rw [Nat.sub_mul, Nat.one_mul]
zukpw rw [Set.not_nonempty_iff_eq_empty] at hF
zukpx rw [SimpleGraph.reachable_iff_reflTransGen] at h
zukpz rw [T.hP] at this
zukqa rw [a1, a2]
zukqb rw [a1, hiff]
zukqc rw [a2] at h1
zukqd rw [add_zero] at this
zukqe rw [arcPoly_n] at hk
zukqf rw [arc_eq hK hj]
zukqg rw [band8 h1 h2]
zukqh rw [beta_eq] at hc
zukqi rw [beta_eq]; norm_num
zukqj rw [chPr_iff] at this
zukqk rw [cp_zero] at heq
zukql rw [d32] at hlt
zukqm rw [d70] at hu
zukqn rw [det_lerp, det_self_right]
zukqo rw [det_lerp]; simp
zukqp rw [det_rayPt_right]; linarith
zukqq rw [e']; tauto
zukqr rw [e, hinj.ncard_image]
zukqs rw [e0] at hg'
zukqt rw [e0] at ht
zukqu rw [e0] at hx₂
zukqv rw [e2] at htest
zukqw rw [e301] at hj
zukqx rw [e5]; tauto
zukqy rw [e6]; tauto
zukqz rw [eBF] at h1
zukra rw [eTL] at hj
zukrb rw [e] at D
zukrc rw [e] at hArr
zukrd rw [e] at hh
zukre rw [e] at hz
zukrg rw [ev, ev]
zukrh rw [exl_length] at ht
zukri rw [e₄]; tauto
zukrk rw [h.head] at hhe
zukrl rw [h.nlive] at h1
zukrm rw [h.open_iff hy hj]
zukrn rw [h.vert] at hve
zukro rw [h.wa_eq, h.wb_eq]
zukrp rw [h0']; simp
zukrq rw [h10] at hb
zukrr rw [h117] at hD
zukrs rw [h1]; grind
zukrt rw [h22] at h64
zukru rw [h3, h4]
zukrv rw [h301] at ht
zukrw rw [h32] at h2
zukrx rw [h32] at hs
zukry rw [h3] at hi
zukrz rw [h4] at h3
zuksa rw [h88] at hj
zuksc rw [hA1, i28]
zuksd rw [hAL] at ha
zukse rw [hA] at hb2
zuksf rw [hA] at hj
zuksg rw [hAl] at hA
zuksh rw [hA₀] at ha
zuksi rw [hE, he]
zuksj rw [hE2] at hX
zuksk rw [hEs t ht]
zuksl rw [hGnv] at htn
zuksm rw [hI.hin _ hfm]
zuksn rw [hK.2.1] at h0
zukso rw [hK.2.2.2.2.2.1] at h1
zuksp rw [hK1.1] at h1
zuksq rw [hK1] at hfl
zuksr rw [hK2.1] at h1
zukss rw [hK2] at hlt
zukst rw [hK] at hlt
zuksu rw [hK₂.1] at h3
zuksv rw [hK₂] at hi
zuksw rw [hL'] at hi
zuksx rw [hM] at hc
zuksy rw [hP9]; omega
zuksz rw [hQj] at hmem
zukta rw [hQn] at hx
zuktb rw [hR'] at hrw
zuktc rw [hRd.rK] at htest
zuktd rw [hRd.rR] at ht
zukte rw [hS.1.length_eq, List.length_range]
zuktf rw [hU', List.length_append]
zuktg rw [hVeq] at hxV
zukth rw [hW2] at hX
zukti rw [hWn] at hp
zuktj rw [hX2] at heq
zuktk rw [hX2] at hne
zuktl rw [hXR] at harc
zuktm rw [hYnz] at this
zuktn rw [h] at e2
zukto rw [hb, hτ0]
zuktp rw [hc, Geometry.mem_segment_iff_lerp]
zuktq rw [hc, h0]
zuktr rw [hc3]; tauto
zukts rw [hceq] at this
zuktt rw [hcq] at hmem
zuktv rw [hc₃]; tauto
zuktw rw [hc₅]; simp
zukty rw [hdv]; rfl
zukua rw [he', pos_top_copies]
zukub rw [he1] at hcode
zukuc rw [he] at hA
zukud rw [he] at hmem
zukue rw [heq] at h
zukuf rw [hfr, hfl]
zukug rw [hgetD] at hrd
zukuh rw [hht] at hI
zukui rw [hhy] at hch
zukuj rw [hj] at hH
zukuk rw [hj] at ht
zukul rw [hk04] at ha4
zukum rw [hk0₂] at hc1
zukun rw [hk0₂] at hc2
zukuo rw [hk1] at hf
zukup rw [hk] at f5
zukuq rw [hk] at hflag
zukur rw [hk] at hsucc
zukus rw [hkx] at hI
zukut rw [hkx] at hk
zukuu rw [hl, hceq]
zukuv rw [hl, hr]
zukuw rw [hlast, chain_dirCode_last]
zukux rw [hlen] at ht
zukuz rw [hm, e]
zukva rw [hmin] at hp
zukvb rw [hmod] at hl
zukvc rw [hmod] at hpy
zukvd rw [hnW] at this
zukve rw [hn] at h
zukvf rw [hn] at hi
zukvg rw [hn]; rfl
zukvh rw [hnc, hnr]
zukvi rw [holeAt_eq, e2]
zukvj rw [ho₁', ho₂']
zukvk rw [hp'] at harc
zukvl rw [hp.1, hq.1]
zukvm rw [hp1, ht1]
zukvn rw [hpm] at h1
zukvo rw [hpos₂] at this
zukvp rw [hpt, bary₂_lerp]
zukvq rw [hpt, rayPt_back]
zukvr rw [hpt0] at hray
zukvs rw [hpt] at h
zukvt rw [hpt] at hc
zukvu rw [hq] at e
zukvv rw [hr, hceq]
zukvw rw [hr] at h
zukvx rw [hs'] at hx
zukvy rw [hs, hsL]
zukvz rw [hs] at e3
zukwa rw [hs] at h
zukwb rw [hs] at this
zukwc rw [hsc] at hE
zukwd rw [hseg, Geometry.segment_comm]
zukwe rw [hsel] at pc₄
zukwf rw [hset]; simp
zukwg rw [hsj] at hE
zukwh rw [ht, Nat.succ_mul]
zukwi rw [htop]
      exact C.slit_subset_dom_compl'
zukwj rw [hv0, hpe]
zukwk rw [hv0, hpw]
zukwl rw [hx]; omega
zukwm rw [hz', rayPt_rayPt]
zukwn rw [hz', rayPt_rayPt_neg]
zukwo rw [hzpos] at hzC
zukwp rw [hΓn] at hk
zukwq rw [hκ]; omega
zukwr rw [k0, k1]
zukws rw [k01] at hAr
zukwt rw [k01] at hF
zukwu rw [k01] at hv
zukwv rw [k02] at h4
zukww rw [k02] at h5
zukwx rw [k02] at hGb
zukwy rw [k03] at hFr
zukwz rw [k0] at h4
zukxa rw [k0₂] at h
zukxb rw [k0₂] at hc
zukxc rw [k5] at hgt5
zukxd rw [k5] at hlt5
zukxe rw [ka, kb]
zukxf rw [key00, key10]
zukxg rw [key_eq, hpe]
zukxh rw [lerp_zero] at this
zukxi rw [mEdge_def, hidx]
zukxj rw [mem_Enc, mem_SSup]
zukxk rw [mem_Enc, mem_Sup]
zukxl rw [mem_Ioi] at hε₀
zukxm rw [mem_SSup, mem_Enc]
zukxn rw [mem_ball, Prod.dist_eq]
zukxo rw [mem_ball_iff_abs] at hp
zukxp rw [mem_singleton_iff] at hdc
zukxq rw [mem_sub] at hmem
zukxr rw [mir_n] at hi
zukxs rw [mod_add_one_mod] at h
zukxt rw [mpass]; simp
zukxu rw [nRegions] at hr
zukxv rw [n_subPoly] at hb
zukxw rw [n_subPoly] at hlen
zukxx rw [neg_neg] at this
zukxy rw [newLB_eq_flatMap] at hx
zukxz rw [not_nonempty_iff_eq_empty] at he
zukya rw [o5] at hf
zukyb rw [one_mul] at h1
zukyc rw [one_mul] at hδ
zukyd rw [p1, p2]
zukye rw [p32] at h0
zukyf rw [pairSeg_swap] at hp
zukyg rw [prevIdx_eq P hi]
zukyh rw [prev_mod hp hp1]
zukyi rw [ptsLen_run]; omega
zukyj rw [q82, F₃'.2.2]
zukyk rw [r2]; rfl
zukyl rw [r3]; tauto
zukym rw [radius_mir]; rfl
zukyn rw [rayPt_sub_self, slitTop_sub_top]
zukyo rw [ray_one]; tauto
zukyp rw [sideLeftOf_iff, add_sub_cancel_left]
zukyq rw [starFperm_inl]; simp
zukys rw [t4] at this
zukyt rw [this, C.sideWalk_vtx_zero]
zukyu rw [this, Geometry.segment_comm]
zukyv rw [this] at h
zukyw rw [this]; fun_prop
zukyx rw [this]; rfl
zukyy rw [this]; simp
zukyz rw [va]; nlinarith
zukza rw [vd]; split_ifs
zukzd rw [walkPoly_n] at hk
zukze rw [whole_set]; simp
zukzf rw [← List.toFinset_card_of_nodup hnd]
zukzg rw [← hD.D]
      omega
zukzh set A := N.arcs.length with hAdef
zukzi set C := sideChain J i
zukzj set K := L.length with hK
zukzk set K := N.nChords with hKd
zukzl set K := N.nChords with hKdef
zukzm set N := E.length with hNdef
zukzo set j := ns.length with hjdef
zukzq set ks := M.key Q s
zukzs set m := l.length with hm
zukzt set n := E.M.W.n with hn
zukzu set n := M.W.n with hndef
zukzv set n' := M'.W.n with hn'_def
zukzw set q := M.key Q x
zukzy set u := J.right.top with hu_def
zulaa set y₂ := D.y₂ with hy₂
zulac set μ := st.mu E c
zulad simp [Host.poly, Polygon.n]
zulae simp [Model.param, h0]
zulaf simp [e1, e2]
zulag simp [ha, hb]
zulah simp [upd] at hu
zulaj simp only [HostItem.pts]
      simp_all
zulak simp only [List.length_singleton]
      omega
zulal simp only [SymPtIn]
      simp_all
zulam simp only at h1 h2 h3
zulan simp only at q1 q2 q3
zulao simp only; field_simp; ring
zulap split_ifs at hin ⊢ with hse
zulaq subst h; right; omega
zular subst hHH
zulas subst hM
zulat subst hcc
zulau subst hyy
zulav try simp
zulaw unfold Bbit at hr; grind
zulax unfold Bm Bk at hr
      grind
zulay unfold BorgR at hr; simp_all
zulba unfold Bt at hr; simp_all
zulbb unfold Chain.slitTop; ext <;> simp
zulbc unfold Merge.shoot
      rw [hhit]
zulbd unfold Model.key at *; linarith
zulbe unfold Model.param Model.wa Model.wb; simp_all
zulbf unfold Model.pos Model.wa Model.wb; simp_all
zulbg unfold along sqLen lerp; grind
zulbh unfold bandOf bLocate bSign ALLOC
      grind
zulbi unfold bestOf
zulbj unfold cVtx
      rw [e7]
zulbk unfold chainPre
      have hB' := hB
zulbl unfold chordAt
zulbm unfold crossSum
zulbn unfold det
zulbo unfold det; simp only
      nlinarith
zulbp unfold dirCode at h4 h6
      grind
zulbr unfold endOrigin
zulbs unfold farPt
      rw [Sweep.rayPt_back]
zulbt unfold gradeCount
zulbu unfold idxI
zulbv unfold keepW at hk; grind
zulbw unfold keyOf at this; simp_all
zulbx unfold localK lh1K shotOfferK ShotList.shotCost
      ring
zulby unfold mem1
zulbz unfold mem2
zulca unfold off at h1 h2
      grind
zulcb unfold prevIdx
zulcc unfold runItems; split_ifs <;> simp
zulcd unfold sideChain; split_ifs <;> rfl
zulce unfold sideLeft sidePrev sideNext sidePt
      simp_all
zulcf unfold sidePrev
zulcg unfold slotVal
zulch unfold tourV
zulci unfold wposOf
zulcj unfold zipRaw zipSp zipSpO at hc
zulcy all_goals try tauto
zulcz apply Finset.card_le_card
zuldc apply Set.Subset.antisymm
zuldd apply filter_congr
zulde apply hfree _ _ hcq
zuldf apply hfree c _ hc
zuldg apply hne s hs0.ne'
      grind
zuldi apply hxv
zuldj apply mul_le_mul_of_nonneg_left _ hl
      linarith
zuldk by_cases hLI : Mountain.LeftInside Q
zuldl by_cases hc : RPF f
zuldn by_cases hw : WallRec x
zuldo by_cases hx : U x
zuldp by_contra hL
zuldq by_contra hb
zuldv classical
      simp [sideSet]
zuldw classical
      unfold emIdx
zulea constructor <;> linarith
zuled exact FactsInterior.rev_vtx Q k hk
zulee exact List.getElem_mem _
zuleh exact Or.inl hRL
zulei exact Or.inl hr
zulej exact Or.inl rfl
zulep exact SweepStop.not_mem_set_of_abs C h hm
zules exact bpt_of_bk hk
zulew exact dirOf_self _
zuley exact drvBands_subset hx
zulez exact e
zulfb exact firstHit_union_le htb hA hle
zulfc exact firstHit_union_le' htb hA hle
zulfi exact hb
zulfm exact hneg h i' h'
zulfn exact hy
zulfr exact not_sideInArc_left _ _ h'
zulfs exact not_sideInArc_right _ _ h'
zulfz exact_mod_cast lvGr_clog_le h
zulgd exfalso
      apply heD
zulge ext U
zulgy have F02 := F01.trans F12
zulgz have F04 := F02.trans F24
zulhb have a2 := E.hD.1.1
      grind
zulhc have e := Nat.mod_eq_of_lt hx1
zulhd have eJ := candFr_qJ fr
zulhe have fT := f₁'.trans fL
zulhf have gm := f₁.2.2.1.trans E.mem
zulhg have h := gradeGran_le_real g
zulhh have h := lvNch_mul μ
zulhi have h' := h.trans i3
zulhj have h1 := Gran.ncard_F hnf
zulhk have h1v := hsp1.resolve_left h1
zulhl have h2 := C.vertex_snd_le_top hj
zulhm have h2 := hF.dualTree_card_edgeSet_le hS
zulhn have hB := hbk hK
zulhp have hC' := hC.of_frame hf'.1
zulhq have hC2 := hC.of_frame hr2
zulhr have hC2 := hC1.of_frame h2r
zulhs have hC5 := hC4.of_frame h5r
zulht have hCap := cap_ncard J
zulhu have hD := distinct_Qof hG
zulhv have hF := h.fam_empty hK
zulhw have hG' := hG hδp
zulhx have hH := cutGran_le_E lam
zulhy have hH := cutGran_lvGr_le μ
zulhz have hK := e.hA.hK.fix hI
zulia have hK := hK₀.fix hId
zulib have hK1 := E.hK.fix hI₁
zulic have hK60 := leaves_length_le hF
zulid have hKd := E.hK.fix hId
zulie have hKd := hK₀.fix hId
zulif have hKn := hK.isOpen_compl.mem_nhds hzK
zulig have hK₀ := E.hK.fix hI
zulih have hK₁ := e.hA.hK.fix hI₁
zulii have hK₁ := hA.hK.fix hI₁
zulij have hK₁ := hK.fix hI₁
zulik have hK₂ := e.hA.hK.fix hI₂
zulil have hK₃ := hA.hK.fix hI₃
zulim have hK₃ := hK₀.fix hI₃
zulin have hL0 := Lst_pos J
zulip have hM := walkAx_interiorModel B.hQ
zulir have hMC := walkAx_chainModel hP
zulis have hM₃ := hM₀.fix hI₃
zulit have hNW := E.nw₂' hI
zuliu have hR := abs_lt.1 hyR
zuliv have hR := hR0.fr hI.fr
zuliw have hR' := hR hg1
zulix have hR' := hR0.fr hf'
zuliy have hR1 := hR.of_frame hr1
zuliz have hR2 := hR1.of_frame hr2
zulja have hR3 := hR2.frame hf3
zuljb have hR4 := hR3.frame hf4
zuljc have hR5 := hR4.frame hf5
zuljd have hS := C.sideS_lt β
zulje have hS := sideD₂ hA
zuljf have hT := rT_def C
zuljg have hTfin := hfin.subset hTF
zuljh have hU := e41.2.1 hu
zulji have hWn := DownMath.walk_n Q
zuljj have hacc2 := hacc.transport a2
zuljk have hareas := Gran.nf_areas hNW
zuljl have hax := hzc.2.1
      grind
zuljm have hb := C.abs_le_coordBound_of_mem_set hmem
zuljo have hb := J.whole.dom_subset_box hd
zuljp have hb := bS_le J.whole
zuljq have hb := bm_false_of_band hr
zuljs have hb2 := D.bot_snd hP
zuljt have hbx := hzc.2.2
      grind
zulju have hc := Finset.card_le_card himg
zuljv have hcc := chain_counted C
zuljw have hcm := str_cmn S
zuljx have hctx := E.ctx2' hI
zuljy have hdisj := components_disjoint hK
zuljz have henv3 := hf3.env hY
zulka have hev1 := htend.eventually hnear
zulkb have hf12 := hf1.trans hf2
zulkc have hgw₁ := E.gw' hI₁
zulkd have hh0 := Nat.pos_of_ne_zero hh
zulke have hhy := hzc'.1.symm.trans hz2
zulkf have hin := hl1 hc
zulkg have hj := List.mem_toFinset.1 hj
zulkh have hk := sideDot_key h1
zulki have hle' := hle hX
zulkj have hlen := List.length_pos_iff.2 hne
zulkk have hlh := h.lo_lt_hi hi'
zulkl have hll := lL1_add_lL2 J
zulkm have hlow := ShootCut.grade_low hX
zulkn have hmin := min_eq_left hlt.le
zulko have hm₂ := F₂.2.2.1.trans F₁.2.2.1
zulkp have hn := C.sideWalk_n C.sideBeta
zulkq have hn := C.sideWalk_n β
zulkr have hn := Chazelle.Jordan.simple_three_le hP
zulks have hn' := hn hch
zulkt have hnW := chainModel_n C
zulku have hne := last_arc_edges B
zulkv have hnear := h2 hf
zulkx have hn₂ := cm_n C₂
zulky have hopen := isOpen_filled_sdiff_boundary hl.simple
zulkz have hout := h0 hz
zullb have hp2 := pow_topGrade_le hn
zullc have hr' := ge_of_band hr
zulld have hrun := ih hqe
zulle have hrun := ih₁ hqb
zullf have hsc := sortCost_le K
zullg have hsh := shooterOKE_of hsh'
zullh have hsl := NFLoc.seq_length hNF
zulli have hsm := hσ.resolve_left hs1
zullj have hsq := sqLen_pos hav
zullk have hsq := sqLen_pos huv
zulll have htop := C.snd_le_top_of_mem_set hmem
zullm have hub := unwrap_b h
zulln have hvert := vert_le_zero_of_none hnone
zullo have hx := abs_lt.1 hD
zullq have hy := C.vertex_snd_le_top hk
zullr have hyL := sub_y_le hsub
zulls have hzR := hnp.1 hσ
zullt have hzR := hnp.2 hσ
zullu have hσ := Sweep.dirOf_cases q.2.2
zullv have hσ := SweepStop.dirOf_cases' b
zullx have hσ := hpos.1 rfl
zully have hσh := one_le_card_sub hh
zullz have hτ := dirOf_pm σb
zulma have o12 := o₁.trans o₂
zulmb have o13 := o12.trans o₃
zulmc have o15 := o14.trans o₅
zulmd have o16 := o15.trans o₆
zulme have od := e.odc hI.hm
zulmh intro C hP hs0 hm
zulmi intro S hST hk hS
zulmj intro U hU V hV
zulmk intro V hV
zulml intro W hW
zulmm intro a _
zulmn intro c3 h3 r hr
zulmo intro e _; simp
zulmp intro g b hlo hhi
zulmq intro h hh hd hb
zulmr intro h' i hi hic
zulms intro h; by_contra h'
zulmt intro hU
zulmu intro hi
zulmv intro hin
zulmw intro hp
zulmx intro hpos
zulmy intro i h1 h2 hs
zulmz intro i ins hi
      grind
zulna intro i j hij hj
zulnb intro j d hI hj
zulnc intro j hj hj0 hjΔ
zulnd intro k hk hkm hzk
zulne intro k hk r hkr
zulnf intro k s hs h
zulng intro m' hm' i hi
zulnh intro q hq hg hqa
zulni intro q q' hqq hq'
zulnj intro r hr t ht
zulnk intro s hs0 hsd hb
zulnl intro u
zulnm intro w' hw'
zulnn intro x hl hd hb
zulno intro x hx hxS hxW
zulnp intro x hx hxS hxl
zulnq intro x hx y hy
zulnr intro ℓ hℓ
zulnv nlinarith [not_lt.1 h]
zulnw push_cast
      rw [div_eq_mul_one_div]
zulnx push_cast at h1
zulny refine IRS.ite ?_ ?_
      swap
zulog refine hI.par _ hi ?_
zuloj refine hdisj.imp_of_mem ?_
zuloz right
      intro G hG hf
zulpa right
      intro j hj hin
zulpc rw [Finset.sum_union hdn]
zulpd rw [List.getElem_append_left hlt]
zulpg rw [Model.pos_snd hne]
zulph rw [Nat.div_lt_iff_lt_mul hk]
zulpi rw [Nat.mod_eq_of_lt hc]
zulpj rw [Nat.mod_eq_of_lt hlast]
zulpk rw [SpanTree.mem_coDarts]
      grind
zulpl rw [chord_eq hi]
zulpm rw [connectedComponentIn_eq hxc]
zulpp rw [dite_eq_left h]
zulpq rw [dite_eq_left hex]
zulpr rw [h.faces hp]
zulps rw [hT2 hT]
zulpt rw [hU]
      push_cast
zulpu rw [hspike]
      left
zulpv rw [ite_eq_left hB]
zulpw rw [ite_eq_left hc]
zulpx rw [ite_eq_left hh]
zulpy rw [ite_eq_left hin]
zulpz rw [ite_eq_left hpos]
zulqa rw [ite_eq_right a]
zulqb rw [ite_eq_right h2]
zulqc rw [ite_eq_right hB]
zulqd rw [ite_eq_right hK]
zulqe rw [ite_eq_right hb]
zulqf rw [ite_eq_right he]
zulqg rw [ite_eq_right hhe]
zulqh rw [ite_eq_right hj]
zulqi rw [ite_eq_right hpos]
zulqj rw [ite_eq_right hs]
zulqk rw [ite_eq_right ht]
zulql rw [ite_eq_right hv]
zulqm rw [mem_emitted]
      constructor
zulqo rw [nd_map_of_lt hk]
zulqp rw [prev_succ hp]
zulqq rw [pts_pos hK]
zulqr rw [rayPt_fst]
      grind
zulqs rw [region_buildNF hr]
zulqt rw [← Finset.mul_sum]
zulqu rw [← Nat.add_assoc]
zulqv rw [← e2]
zulqw rw [← e]
zulqx rw [← hRM]
zulqy rw [← hReq]
zulqz rw [← hc]
zulra rw [← hdom]
zulrb rw [← hk]
zulrc rw [← hkk]
zulrd rw [← hn]
zulre rw [← hpos]
zulrf rw [← hv0]
zulrg rw [← hx]
zulrh rw [← sum_range_nd]
zulrk set e := c.nreg 50002
zulrl set v := M.W.vtx p
zulrm simp at this; omega
zulrn simp only [BuildRegions.crec]
zulro simp only [Config.nreg_mk]
zulrp simp only [Int.cast_natCast]
zulrq simp only [List.getD_cons_zero]
zulrr simp only [List.getElem_cons_succ]
zulrs simp only [List.getElem_cons_zero]
zulrt simp only [Model.param]
zulru simp only [Model.pos]
zulrv simp only [Nat.reduceAdd]
zulrw simp only [Polygon.vtx]
zulrx simp only [Set.mem_ofPred_eq]
zulry simp only [ShootCut.edgeOf]
zulrz simp only [chainAnchor]
zulsa simp only [c₆]
zulsb simp only [fIA]
zulsc simp only [hc₃]
zulsd simp only [hσ]
zulse simp only [keyOf']
zulsf simp only [passMem]
zulsg simp only [posK]
zulsh simp only [qvx]
zulsi simp only [scat]
zulsj simp only [stkList]
zulsk simp only [xAt]
zulsl simp only at hA hB
zulsm simpa using hA ℓ le_rfl
zulsn split_ifs at h
zulso split_ifs at hX2 with hab
zulsp split_ifs at hv with hh
zulsq split_ifs at hx with e
zulsr split_ifs with h'
zulss split_ifs with hk
zulst split_ifs with hl hdeg hmu
zulsu split_ifs with hr
zulsv split_ifs with hs
zulsw subst hH
zulsx subst hXU
zulsy subst hb
zulsz subst he
zulta subst he'
zultb subst hji
zultc subst hk1
zultd subst hp0 ht0
zulte subst hp; subst ht
zultf subst ht0 ht0'
zultg subst ht0'
zulth subst hui
zulti subst huj
zultj subst hur
zultk subst hx
zultl unfold BEnv.stF BEnv.arcR; grind
zultm unfold Bco at hr
      grind
zultn unfold Bsc at hr
      grind
zulto unfold Btw at hb
      grind
zultp unfold Chain.sideBeta Chain.slitTop Chain.top Chain.radius
zultq unfold Chain.top
zultr unfold DirInterior
zults unfold ELay.WR at ha
      grind
zultt unfold Host.pts
zultu unfold Model.arcWt Model.size
