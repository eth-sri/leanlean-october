module

public import Chazelle.MacT.Base

public section

set_option hygiene false

zg zufxk intro c' hc'
zufxl intro h; exact huR (h ▸ mem_connectedComponentIn huA)
zufxm intro i hi h1 h2 _ o τ _ _ _
zufxn intro it hit; exact hwf it (List.mem_reverse.1 hit)
zufxo intro p hp hpΓ
      rcases hΓ hpΓ with hb | hcc
zufxp intro r h1 h2 h3 h4
zufxq intro r hr; simp only [upd]; grind
zufxr left; rw [hs, ← hs0, Geometry.lerp_zero]
zufxs let J : Config → Prop := JK c₁ K A₀
zufxt obtain ⟨a, b, c⟩ := hS.scls_in ht
zufxu obtain ⟨c, hc, rfl⟩ := mem_map.1 hx
zufxv obtain ⟨e, he, rfl⟩ := h.isCut_iff.1 hcut
zufxw obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp h
zufxx obtain ⟨h, hh, he⟩ := List.mem_iff_getElem.1 hmem
zufxy obtain ⟨h1, h2, -⟩ := C.mem_slit_iff.1 hs
zufxz obtain ⟨h1, h2, h3⟩ := mem_starList.1 hc
zufya obtain ⟨hB0, hBA⟩ := cyc_zero hA0 hAB hi
zufyb obtain ⟨hEO, -⟩ := endOrigin_eq J hN hj
zufyc obtain ⟨hMD', hwf'⟩ := Gran.desc_agree' hE.hwf hE.hMD hag
zufyd obtain ⟨harcA, harcB⟩ := chainArcs_two hsub hs hLγ
zufye obtain ⟨hfin, hcard⟩ := hM.arcs_bound hF.2.1 hF.1 hU
zufyf obtain ⟨hi2, hτ, hτ1⟩ := hedge hh0
zufyg obtain ⟨hp₃e, ho₃⟩ := hC.decomp hA₃.1 hA₃.2.1 hA₃.2.2.1
zufyh obtain ⟨hwb, hwp⟩ := hw
      ext z
      constructor
zufyi obtain ⟨hxD, hxc⟩ := hfree x hx.1 hx.2
zufyj obtain ⟨i, hi, he⟩ := mem_events.1 he
zufyk obtain ⟨i, hi, hqi⟩ := Finset.mem_image.mp this
zufyl obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hr
zufym obtain ⟨j, hj, hjx⟩ := mem_arc.mp h
zufyn obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
zufyo obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
zufyp obtain ⟨j, hj, rfl⟩ := h.fam_cases hc
zufyq obtain ⟨k, hk, hka⟩ := index_of_mem ha
zufyr obtain ⟨k, hk, hke⟩ := gsX_of_mem hmem
zufys obtain ⟨k, hk, rfl⟩ := gs_of_mem hm
zufyt obtain ⟨k0, k1⟩ := Corr.key_mem hp ht0 ht1
zufyu obtain ⟨kA0, kA1⟩ := Corr.key_mem hbA.1 hbA.2.1 hbA.2.2.1
zufyv obtain ⟨o1, o2, o3⟩ := hI.i8 hj
zufyw obtain ⟨p, hp, hpa⟩ := List.mem_map.1 h
zufyx obtain ⟨r, hr, har⟩ := List.mem_flatMap.1 ha
zufyy obtain ⟨r, hr, hyr⟩ := mem_flat.1 hy
zufyz obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
zufza obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hy
zufzb obtain ⟨sB, κB, hB⟩ := DrvR.sortedMeets_of buildNFSorted
zufzc obtain ⟨t, ht, htj⟩ := List.mem_iff_getElem.1 hjm
zufzd obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq1
zufze obtain ⟨u1, u2, -⟩ := bp a
zufzf obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
zufzg obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
zufzh obtain ⟨y0, y1⟩ := Corr.key_mem hp' ht'.1.le ht'.2
zufzi obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h
zufzj obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
zufzm push Not at h₁ h₂
      by_cases hL : a₂ = 0
zufzn rcases D.segment_cases hP hD hp with e | e | e
zufzo rcases E.hσ with h | h
zufzp rcases h1 with rfl | rfl
zufzq rcases hE.hxc with h | h
zufzr rcases hU with hU | hU
zufzs rcases hW with hW | hW
zufzt rcases ha with ha | ha
zufzu rcases hab with rfl | rfl
zufzv rcases hdir with hu | hd
zufzw rcases heab with rfl | rfl
zufzx rcases hi with rfl | rfl
zufzy rcases hj.lt_or_eq with hj | rfl
zufzz rcases hl1 with hF | hin
zugaa rcases hp with rfl | rfl
zugab rcases hqa.lt_or_eq with h1 | h1
zugac rcases hs0.lt_or_eq with hs0 | rfl
zugad rcases ht'.lt_or_eq with ht'0 | ht'0
zugae rcases ht1.lt_or_eq with h | h
zugaf rcases hθ with rfl | rfl
zugag rcases key q hq heq with h' | h' | h'
zugah rcases le_total x (-B) with h | h
zugai rcases n with _ | n
zugaj rcases x with v | g
zugam refine Chazelle.Chain.sideCcw_not_ray_left hdm0 ?_ ?_ h5
zugan refine Chazelle.Chain.sideCcw_not_ray_right hdm0 ?_ ?_ h5
zugap refine Prod.ext ?_ ?_ <;> simp only [shearPt]
      ring
zugaq refine hE₂.keep e₃.wb_right h3m fun r hr => h3' r ?_
zugaw right; left; rw [← h0, rayPt_zero]
zugax rintro (h0 | h1)
zugay rintro c' ⟨e1, e2, e3, fr2⟩
zugaz rintro c' ⟨hb, k₃, ha₃, hm₃⟩
zugba rintro c₂ ⟨vd, fr2, hA2, hm2⟩
zugbb rintro c₃ hI₃ - - hc3
zugbc rintro c₅ hI₅ - - rfl
zugbd rintro d ⟨σ, hσ, hfree, rfl⟩
zugbe rintro d' hd'
zugbf rintro d' rfl
zugbg rintro x ⟨p, t, hA, rfl⟩
zugbi rintro ⟨hT0, hTm⟩ ⟨h1, h2⟩
zugbj rintro ⟨hc, hd⟩
zugbk rintro ⟨rfl, h2⟩
zugbl rw [(C.sidePt_box C.sideBeta t').2.1] at hpt'
zugbm rw [(C.sidePt_box C.sideBeta t').2.2.2.1] at hpt'
zugbn rw [A₁] at A₂
zugbo rw [C.mem_slit_iff] at h2
      have hle := C.snd_le_top_of_mem_set h1
zugbp rw [C.sideIdx_one, C.sideIdx_last]
zugbq rw [C.sideWalk_vtx_one]; grind
zugbr rw [C.sideWalk_vtx_three]; grind
zugbs rw [Chain.chordSet_eq_hseg] at hz
zugbt rw [Chain.sideIdx_eq, hmod]; unfold Chain.sideE; grind
zugbv rw [Cα.chainEdge_eq] at hx
zugbx rw [Finset.card_image_of_injOn, Finset.card_range]
zugby rw [Finset.mem_image] at hi
zugcb rw [Geometry.lerp_zero] at this
zugcc rw [Geometry.point_ext_iff]; simp [hky]; ring
zugce rw [List.mem_singleton] at h
zugcf rw [List.pairwise_cons] at hrest
zugcg rw [NFLoc.hostAt_unique hH' hH]
zugcj rw [OutWalk.walk_n]; have := Jordan.simple_three_le hQ; omega
zugck rw [abs_le]; constructor <;> simp only <;> nlinarith
zugcm rw [d1, d2, d3]; exact h
zugcn rw [d1, d4, d5]; exact h
zugcr rw [e, Set.ncard_eq_toFinset_card', Set.toFinset_Ico, Nat.card_Ico]
      rfl
zugcs rw [e] at hy
zugcv rw [h1i, hone1] at hin
      unfold ClassTest
      grind
zugcw rw [h1i, hzero1] at hin
      unfold ClassTest
      grind
zugcy rw [h8 _ hu]; exact hF.topR u hu
zugcz rw [h87] at ht
zugda rw [hA1 s' le_rfl]
zugdd rw [hE₇.r32] at hlt
zugde rw [hE₇.r32] at hlt2
zugdh rw [hP'def, hPdef, mod_pred_mod hn0 _ hd1]
zugdi rw [hRd.rR] at htest
zugdj rw [hS, hinj.ncard_image, Set.ncard_eq_toFinset_card', Set.toFinset_Iio]
      simp
zugdk rw [hS] at v102
      have hSle := C.sideS_lt C.sideBeta
zugdl rw [hT] at hroom
zugdm rw [hTj] at hm
zugdo rw [hbo, v₃]
zugdp rw [hc1]; tauto
zugdq rw [hcab] at hA'
zugdr rw [hcab] at hx
zugds rw [hc₃]; simp
zugdt rw [hdq, hdq'] at hbtw
      push_cast at hbtw
zugdu rw [he] at this
zugdx rw [hit] at hH; unfold NFLoc.itemOf at hH
zugdy rw [hjr] at harc
zugdz rw [hk] at hr
zugea rw [hkl, hkr', ht0, add_zero]
      tauto
zugec rw [hm', Machine.upd_apply]
zugeh rw [hn] at hk
zugei rw [hn] at hp
zugej rw [hna'] at ht
zugel rw [hs] at hf hfpos hfA hvA hpos ⊢
zugem rw [hseqv v hv]
zugen rw [hu1] at htu
zugeo rw [hx]; decide
zugep rw [hz] at h
zuger rw [ite_eq_left hsl, ite_eq_left hsl, ite_eq_left hsl]
zugew rw [k0] at h1
zugex rw [k0₂] at hflag
zugez rw [mem_ball, dist_rayPt _ hτ hs.le]; omega
zugfa rw [mem_ball_iff_abs]; simp_all
zugfb rw [mem_image_mir, mir_pt, neg_neg]; exact hm
zugfc rw [nChords] at hi
zugfe rw [r1]; tauto
zugff rw [rayPt_fst]; grind
zugfi rw [sideDot_comm] at hd
zugfj rw [sideLeftOf_iff, add_sub_cancel_left, rayPt_sub, sideCcw_smul hs]
zugfk rw [stMem_apply]; grind
zugfl rw [this, Set.ncard_eq_toFinset_card', Set.toFinset_Ico, Nat.card_Ico]
      omega
zugfm rw [this]; simp only [↓reduceIte]
zugfo rw [← Finset.card_map Fin.valEmbedding]
zugfs rw [← isHChordIn_mir, neg_neg, neg_neg]; omega
zugft set C := J.whole with hC
zugfu set F := J.fusion S₁ S₂ ∪ glueChords J with hFdef
zugfv set K₀ := N.chords.length with hK₀
zugfw set S' := J.fusion S₁ S₂ ∪ glueChords J with hS'
zugfy set τ := tau _ u L h1 h2 with hτd
zugfz simp [Bapp, h]
zugga simp [Model.key, Model.param]
zuggb simp [NF.nRegions, buildNF]
zuggc simp [Polygon.edge, h3]
zuggd simp [h1, h2]
zugge simp [sweepEndQ, NF.nChords]
zuggf simp only [BEm, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
zuggg simp only [BFR, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
zuggh simp only [BIS, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
zuggi simp only [BMD, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
zuggj simp only [BPT, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
zuggk simp only [BR, Bool.or_eq_false_iff] at h; simp_all
zuggl simp only [BSQC, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
zuggm simp only [BTB, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
zuggn simp only [BZS, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
zuggo simp only [BcmpG, Bool.or_eq_true, decide_eq_true_eq] at hr
zuggp simp only [Bcp, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
zuggq simp only [BhitG, Bool.or_eq_true, decide_eq_true_eq] at hr
zuggr simp only [Bkb, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hr
zuggs simp only [Bld, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
zuggt simp only [Bouts, List.contains_eq_mem, decide_eq_false_iff_not]; tauto
zuggu simp only [Bs56, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
zuggv simp only [BsA, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
zuggw simp only [Finset.mem_singleton, bandOf, bDownDrv] at hq
zuggx simp only [Int.cast_zero, zero_mul, add_zero] at hj
zuggy simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact b₂
zuggz simp only [List.flatMap_nil, pcSet_nil, Set.union_empty]
      exact best₁'
zugha simp only [List.map_cons, List.mem_cons, not_or] at hr
zughb simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
zughc simp only [Machine.upd_apply, h1, h2, ite_false]
zughd simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
zughe simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
zughf simp only [SignTest, hV] at this; omega
zughh simp only [bandOf, bDownDrv] at h21; omega
zughi simp only [cfgRen, σ_σ] at this ⊢
      omega
zughj simp only [cfgRen_nreg, σ_σ] at this ⊢
      omega
zughk simp only [ch, Finset.mem_filter, Finset.mem_range] at hc
zughl simp only [chainModel, not_and, not_lt] at hc
zughm simp only [copy2List, List.mem_cons, List.not_mem_nil, or_false]
zughn simp only [dBands, Finset.mem_insert, Finset.mem_singleton] at h
zughp simp only [h, ite_true, zero_add, Nat.mod_mod]
zughq simp only [hS', surgery, upd]; grind
zughr simp only [halfDisk, mem_inter_iff, mem_ofPred_eq, mem_ball_iff_abs]
zughs simp only [mem_iUnion]
      grind
zught simp only [mem_ofPred_eq, abs_neg_midR, abs_midR] <;> linarith
zughu simp only [phi, stretchPt, hR, hRn]
zughv simp only [posR, ha_def, WPos.mk.injEq]; omega
zughw simp only [posR, hb_def, WPos.mk.injEq]; omega
zughx simp only [primalEnv, view_lt a.2]; exact ha
zughy simp only [primalEnv, view_lt b.2]; exact hb
zughz simp only [rowE, hR', e6] at hNL
zugia simp only [topIdxs, Finset.mem_insert, Finset.mem_singleton] at hk
zugid simpa [rayPt] using this
zugie simpa [rayPt] using this.2
zugif split_ifs with hc
zugig subst e
zugih subst hMi
      have hn := interior_n (P := P)
zugii subst hkj
      left
      rw [← edge_prevIdx P hi]
      omega
zugij subst ht00
      obtain ⟨hd0, -⟩ := hsec rfl
zugik unfold ALLOC at hb; omega
zugil unfold Chain.vertex Chain.edgeIdx
zugim unfold Model.wa; rw [hW, DownMath.walk_vtx hli hq]
zugin unfold PLt at this; omega
zugio unfold copyF
      grind
zugip unfold dq; split_ifs <;> omega
zugiq unfold interiorWalk
      split_ifs
zugir unfold off at *; grind
zugis unfold off at h; grind
zugit unfold sw at *; omega
zugja apply C.sideNot_mem_set_of_abs; grind
zugjb apply Subset.antisymm
zugjd beta_reduce at hk₂ ⊢
      rw [r9] at hk₂
zugje by_cases h2 : a = X + 2 * i
zugjg by_cases hB : g + 1 ≤ lam - 1
zugjh by_cases hE : w < 2 * V.m + 6
zugji by_cases hb : 0 < βb ∧ βb < L
zugjk by_cases hc : i < 2 * m - S
zugjm by_cases hit : i = t ∧ s' = s
zugjn by_cases hl : p = 2 * C.m + 6
zugjo by_cases hlt : e - 6 < 2 * C.m
zugjp by_cases hsw : 240000 ≤ r ∧ r < 250000
zugjy congr 1; omega
zugjz congr 2
zugkb exact (sideLeft_congr ht ha hb _).1 hsec
zugkf exact gapPair_label J hP hS₂.2.1 hS₂.1 hG hV' hL hgp
zugkh exact hW
zugkj exact pos_of_mul_pos_right hprod hori.le
zugkk exfalso; apply hBdm
zugkl exfalso; apply hzD.2
zugkm ext k
      simp only [sideVtxSet, mem_ofPred_eq]
      simp_all
zugkn filter_upwards [hside z hz hzD] with δ hδ
zugko filter_upwards [hsideE z hz hzD] with δ hδ
zugkp filter_upwards [hsideW z hz hzD] with δ hδ
zugkr have C₄ := keepArc Fb C₃
      have hA₃ := F₃.2.2.2.2.2.2
zugkv have e1 := h.2.1.symm.trans h'.2.1
      have e2 := h.2.2.symm.trans h'.2.2
zugkx have e23 := hI₃.h23
zugky have eD := candFr_qD fr
      have hK := hA.hK.fix hI₂
zugla have g := hf.1
zuglc have h1 := hI.h23
zugld have h1 := hori
      nlinarith [mul_pos h1 h1]
zugle have h1 := sub_ne_zero.2 h.symm
      have h2 := sub_ne_zero.2 h
zuglf have h1' := h1
      rw [k01] at h1'
zuglh have h2 := congrArg Prod.snd hpt'
      simp only at h2
zugli have h2' := h2
      rw [k01] at h2'
zugll have hA₂ := F₂.2.2.2.2.2.1
zugln have hE := E₁_le (J := J) hP
zuglo have hF := hFam.2.1
zuglp have hL := hSF.lay
zuglq have hM₂ := hC.hM₂
zuglr have hNA := hN'.nfAt
zugls have hNF' := hNF
zuglt have hP := S.E.hP
zuglu have hS := hP.hS
zuglv have hW := hR.hW
zugma have hcb := C.coordBound_lt_radius
zugmc have hdN := hA.hdN
zugmi have hhn := (regOf_spec hNF).2.2.2.2.2.1 k hk
zugmj have hi := hidx.1
      rcases hti with hti | hti
zugmp have hlist := hI.list
      rw [hj] at hlist
zugmq have hm := h.m_eq
zugmr have hm := hI.hm
zugmw have hm₁ := f₁.2.2.1
zugmx have hn := hC.n_pos
zugnb have hr := hE.hr
zugnc have hroom := hI.room
zugne have htR := C.top_snd_lt_radius
zugng have hvw := (hL.rvert _ hqn hqr').2
zugnh have hw := E.wb
zugnr have k₁' := r₁
zugnw have w₀ := x₀.wb_right
zugnx have w₁ := ex₁.wb_right
zugoa intro S W R hS hW hR hn hΔ hdeg
zugob intro U hU ⟨u, huU, huR⟩
zugoc intro h; by_contra h'; push Not at h'
zugod intro hc; by_contra hc'; push Not at hc'
zugoe intro hnd d' k ex hk hI' h40 kp mem
zugof intro ht; rw [ht] at hf₁ hns
zugog intro hv; rw [hv] at hf₁ hns
zugoh intro i hi hi'
zugoi intro k
zugoj intro k hk hkin
zugok intro n
zugol intro pa₁ pb₁ ta₁ tb₁ hA₁ hB₁ hAB₁ hin₁ hout₁
zugom intro reg hr hch v hv hvs σb hσb hg
zugon intro v hv hv'
zugoo intro v hv1 hv2
zugop intro x
zugoq left; simp [dBands, bDecomp, h]
zugor nlinarith [mul_lt_mul_of_pos_left h1 hs, mul_le_mul_of_nonneg_left h2.le hs']
zugos obtain ⟨-, rfl⟩ := hx'; grind
zugov obtain ⟨D', hD', rfl⟩ := hd
zugow obtain ⟨H₀, -, hst⟩ := E.hst
zugox obtain ⟨c, hc, rfl⟩ := hx
zugoy obtain ⟨d', rfl⟩ := h.eD_surj e' he'
zugoz obtain ⟨g1, g2, g3⟩ := hgen
zugpb obtain ⟨h1, h2, h3⟩ := hI
zugpc obtain ⟨h1, h2, h3⟩ := hb
zugpd obtain ⟨h12, h15, -⟩ := hF
zugpe obtain ⟨h2, hn, hch⟩ := hd
zugpf obtain ⟨hCl, hCr, hCw⟩ := hJ
zugph obtain ⟨hX, hY⟩ := h.cl_mem hE hc
zugpi obtain ⟨hb1, hb2, hb3⟩ := hB
zugpk obtain ⟨hdisj, hWb, hWs⟩ := hL
zugpl obtain ⟨hl, hr⟩ := hL.2.2.1 x hx
zugpm obtain ⟨hpA, hpj⟩ := hm.pos j hj
zugpn obtain ⟨hpA, hpj⟩ := hm.pos j hjA'
zugpo obtain ⟨hpa, hpb⟩ := ne_of_mem_innerSeg hne hp
zugpp obtain ⟨hpn, hpp⟩ := hR.par_spec hh hr
zugpq obtain ⟨hpt, hsec⟩ := split_facts J hδ
zugpr obtain ⟨hr, e1, e2⟩ := h
zugpt obtain ⟨ht, hpre, hpost⟩ := hpart
zugpu obtain ⟨hwy, hwa, hwb⟩ := hwc
zugpv obtain ⟨hx0, hx1, -⟩ := hx
zugpw obtain ⟨hx1, hx2⟩ := bot_x_mem hQ D
zugpx obtain ⟨hx1, hx2⟩ := top_x_mem hQ D
zugpy obtain ⟨hxy, hxl, hxr⟩ := hx
zugpz obtain ⟨hzy, hza, hzb⟩ := hzc
zugqa obtain ⟨i, hi, hqi⟩ := hqB
zugqc obtain ⟨i0, g, Y⟩ := X.ctx
zugqd obtain ⟨i0, i1, i2⟩ := hit
zugqf obtain ⟨j, hj, rfl⟩ := hv
zugqh obtain ⟨k0, k1, k2⟩ := f1
zugqi obtain ⟨o1, o2, o3⟩ := ho
zugqj obtain ⟨p, hp⟩ := regionsIn_nonempty hR₁
      grind
zugqk obtain ⟨p, hp⟩ := regionsIn_nonempty hR₂
      grind
zugql obtain ⟨p1, p2⟩ := pairsZ i hi
zugqm obtain ⟨q, hqT, hqU⟩ := hne
zugqn obtain ⟨q10, q11, q12⟩ := q
zugqo obtain ⟨q102, qr, qm⟩ := q
zugqp obtain ⟨q3a, q3b, q3c⟩ := q3
zugqq obtain ⟨r, hr, rfl⟩ := hc
zugqr obtain ⟨rfl, rfl⟩ := this
      exact hA
zugqs obtain ⟨s, h | h⟩ := hmount
zugqt obtain ⟨sG, κG, hGr⟩ := granularize
zugqu obtain ⟨v, rfl⟩ := h.eV_surj u hu
zugqv obtain ⟨w, hw, hwc⟩ := hex
zugqw obtain ⟨x, hx, rfl⟩ := hX
zugqx obtain ⟨x₁, c₁', r₁⟩ := hB.cand
zugqy obtain ⟨z, -, rfl⟩ := hC
zugqz obtain ⟨z, hz, rfl⟩ := hU
zugrb obtain ⟨δ, hδ, hW'⟩ := hW
zugrd push Not at h'
      rcases h'.lt_or_eq with h'' | h''
zugre push Not at h0
zugrf push Not at hB
zugrg push Not at hall
zugrh push Not at hge
zugri push Not at hlt
      rcases hlt.lt_or_eq with h1 | h1
zugrj push Not at hv
zugrk rcases Chazelle.Existence.eq_endpoint_of_vtx_mem_edge hQ hv he hmem with h | h
zugrl rcases Nat.lt_succ_iff.1 hi |>.lt_or_eq with h | h
zugrm rcases S with _ | ⟨y, S⟩
zugro rcases h with h | ⟨-, h⟩
zugrp rcases h.eq_of_subset hP hPR with rfl | rfl <;> omega
zugrq rcases hMD with ⟨h0, -⟩ | h
zugrr rcases he with he | ⟨-, rfl⟩
zugrs rcases he with he | ⟨he, h0⟩
zugrt rcases hfe with hz | ⟨hLz, hz⟩
zugru rcases hg with hg | ⟨hg1, -⟩
zugrv rcases hr with (hr | hr) | hr
zugrw rcases hs.zo with e | ⟨e, hz1⟩
zugrx rcases ht' with h | ⟨h, h0⟩
zugry rcases hz with e | ⟨e, hz1⟩
zugrz rcases hτ with rfl | rfl <;> simp <;> linarith
zugsa rcases ls with _ | ⟨a, ls⟩
zugsc rcases lt_trichotomy e.1 e'.1 with h | h | h
zugsd rcases lt_trichotomy e₁.1 e₂.1 with h | h | h
zugse rcases lt_trichotomy s.edge e.edge with hlt | heq | hgt
zugsg rcases rest with _ | ⟨a, rest'⟩
zugsh rcases s' with _ | ⟨b, rest⟩
zugsi rcases sideInArc_split h1 hmid with h2 | h2 | h2
zugsl refine List.disjoint_left.2 fun x hx hx' => hab ?_
      grind
zugsp refine spec_ifLtN_false c2 ?_
zugsq refine spec_ifLtN_false hb ?_
zugsr refine spec_ifLtN_true c1 ?_
zugss refine spec_ifLtN_true h ?_
zugst refine spec_ifLtN_true hb ?_
zugtc right
      have hu := (hRT.ends_lt 0 hpos).1
zugtd rintro (h | ⟨h1, h2⟩)
zugte rintro Z hZ ⟨δ, hδ, hf⟩
zugtf rintro _ ⟨t, ht, rfl⟩ hxb
zugtg rintro c'' rfl
      simp only [I, upd_same]
zugth rintro s ⟨k, hk, rfl⟩
      grind
zugti rintro z ⟨-, hz1, hz2⟩
      linarith
zugtj rintro ⟨s, hs0, hsT, rfl⟩
zugtk rintro ⟨u, h0, h1, he⟩
zugtl rintro ⟨⟨h1, h2⟩, hx⟩
zugtm rw [C.sideIdx_eq, C.sideIdx_eq, Nat.add_mod_right, Nat.add_zero]
zugto rw [C.sideWalk_vtx_wrap, C.sideWalk_vtx_tour _ le_rfl, C.sideTour_two_m]
zugtp rw [Chain.sideIdx_eq] at hidx
      unfold Chain.sideE at hidx
zugtq rw [Chazelle.Chain.sideLeft_zero]
zugtt rw [List.length_flatMap]
zugtu rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
zugtw rw [Nat.card_Ico, Nat.sub_zero, smul_eq_mul] at this
zugtz rw [Prod.dist_eq]
zugua rw [Set.disjoint_left]
zugub rw [abs_lt] at this
      linarith [h.lt]
zuguc rw [arcWt_chain C Q hx hy] at hwt
zugue rw [cm_W]
zuguf rw [e0, e1, e2, e3]
zuguj rw [h', neg_mul] at hpos; linarith
zuguk rw [h3, Nat.mod_self] at hc2; omega
zugul rw [h3]
zugum rw [hA]
zugun rw [hE]
zuguo rw [hF]
zuguq rw [hPdef, hx, unwrapK_self]; grind
zugur rw [hS.r18]
zugus rw [hW]
zugut rw [hWf, hWb, hz', hzt]
zuguu rw [hc1, hc2, hc3, hd1]
zuguv rw [hg]
zuguy rw [hk, he _ hcnt] at hlt
zugva rw [hlerp]
zugvb rw [hlv] at hp
      rw [g7]
zugvc rw [hm5, hI.mem a, ← hi]
zugvd rw [hmod]
zugvg rw [hout x hx hr] at hne ⊢
zugvh rw [hp]
zugvi rw [hpc', hl, e6] at hb
zugvl rw [hq]
zugvm rw [hs'.1, hs'.2.1, hs'.2.2.1]; grind
zugvn rw [hsP, heP, key_hgt0, key_hgt0]
zugvo rw [hv' f u hf hu, hjR]
zugvp rw [hwv]
zugvq rw [hx, zero_mul, add_zero] at D1
zugvs rw [hz, Visibility.rayPt_fst, Visibility.rayPt_fst]; ring
zugwa rw [lerp_rayPt]
zugwb rw [m']
zugwd rw [map_map]
zugwn rw [m₄, hm₃, h.rsrc, h.rdst]
zugwo rw [n_subPoly, List.length_reverse] at h1 h2 h3
zugwp rw [not_or, not_le, not_le] at hcon
zugwq rw [not_or, not_lt, not_lt] at hcon
zugwr rw [n₅, Machine.upd_other _ _ _ hr]
zugws rw [o3 k hk, eN] at hlt'
zugwu rw [one_mul]
zugwx rw [pow_succ]
zugxa rw [rayPt_sub_one]
zugxb rw [r₄]; simp only [upd_same]
zugxc rw [se1, sh1, se2, sh2]
zugxd rw [sideE_eq]
      by_cases hc : m < j
zugxf rw [tB i' b c]; intro h
zugxg rw [this]; exact highList_length_le _ _ _
zugxi rw [v54, h82, hpc]; rfl
zugxj rw [v₃, d₂, v₁, v₂]
zugxk rw [x51, x120, x121] at g₄
zugxl rw [z₁, hcnt', hcase]; simp
zugxn rw [← Nat.succ_mul]; congr 1; omega
zugxo rw [← chordSet_eq_hseg, ← hS]; rfl
zugxq rw [← hI.u, ← hI.d0]; tauto
zugxr rw [← hWb]
      exact sidePt_mem_boundary hp ht0 ht1.le
zugxt rw [← hh]
      exact vert_mem_halfDisk hτ hs0 hsr'
zugxu rw [← hpp, ← htt] at hA
zugxv rw [← hpre] at a₁ n₁ L₁ ⊢
zugxw rw [← hseg_mir, ← hc, image_mir_image_mir]
zugxx rw [← hv']; exact Geometry.left_mem_segment _ _
zugxz rw [← sum_cntBelow, ← sum_cntBelow, Finset.sum_range_succ]
zugya rwa [mem_image_mir, mir_pt, neg_neg] at hm
zugyb set A := N.arcs.length
zugye set L := rL1 J + rL2 J with hLdef
zugyf set L₁ := 2 * L - τ with hL₁
zugyg set N := (H.pts P.n).length with hN
zugyi set N := BuildNF.buildNF _ Q L E with hN
zugyk set T := tr sL sR y₁ y₂ with hTdef
zugyl set W' := (chainModel C').W with hW'
zugym set X := 2 * E + μ + 1
zugyo set bo := blkOf g.μ lev hl blk with hbo
zugyp set g := 6 + tpos J.whole J.m₁ with hgdef
zugyq set j := 2 * k + s with hjd
zugyr set n : ℝ := (M.W.n : ℝ)
zugys set n := M.W.n
zugyt set pc := pcB κP _ κs _ with hpc
zugyu set s := 2 * C.m - τ with hs_def
zugyw simp [Geometry.lerp, Chain.slitTop] at hy; linarith
zugyx simp [h]
zugyy simp [lerp, rayPt, hzy, hwy]
zugyz simp [rayPt]
zugza simp only [Chain.slitTop, Chazelle.Geometry.lerp_snd] at hb
      grind
zugzb simp only [Chain] at h h'; omega
zugzc simp only [Finset.coe_Ico, Set.mem_Ico] at hx hy
zugzd simp only [List.length_cons]
      rw [Nat.add_comm]
      tauto
zugze simp only [SortL.seg_getD _ hq] at this
      omega
zugzg simp only [Visibility.hseg, rayPt, mem_ofPred_eq]
      grind
zugzh simp only [e1, e2] at le1 le2
zugzi simp only [hL, hR, ↓reduceIte]
zugzj simp only [hL, ↓reduceIte, ShootCut.edgeOf]
zugzk simp only [label, Enc, f]
      grind
zugzl simp only [levLeaves, pcSet_single]; exact hb
zugzm simp only [mem_insert_iff, mem_singleton_iff] at h
      grind
zugzo simp only [regB, regI, upd]
      simp_all
zugzp simp only [segL, optSeg]
      split_ifs with hs
zugzq simp only [upd, h1, ↓reduceIte]
zugzr simp only [upd, ite_eq_right h1]; grind
zugzt simp only [upd, ite_true, chainModel]
      constructor
zugzu simp only at this
zugzw subst hq hs
      exact attach_disj hAB hat hG hpt' hsec
zugzx subst hy
      by_cases h : x + c < n
zugzy unfold ALLOC at hra
zugzz unfold Btop at hr
zuhaa unfold DegC nearC at hdeg
      unfold farC at h1 h0
zuhab unfold DirInterior
      filter_upwards [Ioo_mem_nhdsGT hd] with t ht
zuhac unfold Model.key; grind
zuhae unfold Prot at hr
zuhaf unfold RegsOK at hR
zuhag unfold StBRG at hr
zuhah unfold arcList; simp_all
zuhai unfold bandOf ALLOC
      omega
zuhaj unfold candS
      by_cases h : c.nreg jr < c.nreg sr
zuhak unfold det; simp only [lerp]; grind
zuhal unfold dirCode; grind
zuhan unfold endPos; split_ifs
zuhao unfold i0F; grind
zuhap unfold ifNe1
      by_cases h1 : c.nreg x < c.nreg 130001
zuhaq unfold len; grind
zuhar unfold logPos; grind
zuhas unfold mu
      by_cases hU : BrkU C nQ H U
zuhat unfold normOf at hp; split_ifs at hp with hz
zuhau unfold rpv; simp_all
zuhav unfold seg
zuhaw unfold selOf; simp_all
zuhax unfold sideCross
      simp only [Prod.fst_sub, Prod.snd_sub]
      grind
zuhay unfold sideE; simp_all
zuhaz unfold sideInArc at hc
zuhba unfold sideInArc at hx
zuhbb unfold sidePt at hpy
      rw [Geometry.lerp_snd] at hpy
zuhbc unfold sidePt; grind
zuhbe apply Geometry.point_ext <;> simp [lerp] <;> ring
zuhbf apply hnv ht
zuhbg apply hr
zuhbh apply point_ext <;> simp [rayPt]; ring
zuhbi by_cases a1 : c₁.nreg 81011 < c₁.nreg s
      swap
zuhbj by_cases h : d.nreg src + 1 < n
zuhbk by_cases h0 : nz C w hc = 0
zuhbn by_cases hD : dOf W.n g p < s'
zuhbo by_cases hb : d.nreg 30001 < 2 * L.length
zuhbq by_cases hlt : c.nreg s + 1 < n
zuhbs by_cases hv : VNotTop J
zuhbt by_contra hA
zuhbu by_contra hdd
      simp only [Bool.not_eq_false] at hdd
zuhbv by_contra hle; push Not at hle; nlinarith
zuhbw by_contra hn
zuhbx by_contra hn; push Not at hn; nlinarith
zuhch classical
      unfold cntS
zuhcp exact FactsInterior.rev_n Q
zuhcq exact Or.inr h
zuhcy exfalso
      rw [hposv, pos_eq_sidePt'] at hy
zuhcz ext p; simp [box, abs_lt]
zuhda filter_upwards [Ioo_mem_nhdsGT hT] with t ht
      simp_all
zuhdb filter_upwards [Ioo_mem_nhdsGT hδ0] with x hx
      grind
zuhdf filter_upwards [hopen.mem_nhds hmem] with p' hp' hpos
zuhdu have e1 := (hafter p).2 hl
zuhdx have f2 := simple_vtx_inj hP hb hsucc e2
      simp_all
zuhdz have h3 := (h2.pos_le h hu).2.1
zuhea have hA := hw.1 ALLOC
zuheb have hAA := sideDot_self_pos hA
zuhec have hE := dmOf_oEnd K A R D b0
zuhee have hK := hA.hK.fix hI
zuhef have hK2 := E.hK.fix hI₂
zuheg have hK₂ := hA.hK.fix hI₂
zuheh have hK₂ := hK₀.fix hI₂
zuhei have hK₃ := E.hK.fix hI₃
zuhek have hM' := walkAx_chainModel hS.simple
zuhel have hMα := walkAx_of_goodModel hGα
zuheo have hS := hI.env
      have hlow := ShootCut.grade_low hS.grade
zuheq have hb := b₁_lt (J := J)
zuhes have hd := sub_ne_zero.2 hne.symm
zuhet have hd := sub_pos.2 huv
zuheu have hdom := T.interior_sub_dom hQ
zuhev have he := Merge.shoot_mem_augChords C ha haD hσ hf
zuhew have hfac := (h hdn).2 rfl
zuhex have hfac := (h hup).2 rfl
zuhey have hgw := E.gw' hI
zuhez have hi' := Finset.mem_range.1 hi
zuhfa have hil := (chordAt_lt hE ht).1
zuhfc have hl : li = true := hli.2 hLI
zuhfd have hl := NFLoc.seq_length hN
zuhfe have hl := lam_le_E lam
zuhff have hl := seq_length h
zuhfg have hlen := newEx_le hE h hc hs hlow
zuhfh have hn := Chazelle.Jordan.simple_three_le hQ
zuhfi have hn := cm_n J.left
zuhfj have hn' := cm_n C'
zuhfk have hnd' := List.nodup_cons.1 hnd
zuhfl have hp := (b1 bi).1 a1
zuhfm have hqD₀ := hC.hM₂.trace _ hA₁.1 _ hA₁.2.1 hA₁.2.2.1.le
zuhfp have hs := sA_lt' (C := C)
zuhfq have hsub := subset_region hU hHc hfree hδ.1 hδU'
zuhfr have hv0 := walk_vtx Y.X.hCs Y.X.hCm C.sideBeta h6 hp
zuhfs have hvc := hec hv
zuhfu have hw₂ := (hC.sidePt_eq hd t).symm
zuhfx have hμ := hSF.hμ; have hN := hSF.hN
zuhfy have hσ2 := sigma_sq hσ
zuhfz have h₂ := hsame.1 h₁
zuhga have o110 := (o18.trans o₉).trans o₁₀
zuhgb have o18 := (o16.trans o₇).trans o₈
zuhgd intro F hF U hU
zuhge intro _
zuhgf intro c c' h hr _ hm _ _
zuhgg intro c hc hZ
      simp only [lexStmt]
zuhgh intro f hf
zuhgi intro g hg p' τ' hp' h0 h1 hkk
zuhgj intro h'
zuhgl intro h; unfold chordSel at h; grind
zuhgm intro h; unfold xpClass at h; simp_all
zuhgn intro hb
zuhgo intro hf
zuhgp intro hmem
zuhgq intro ht h
zuhgt intro i _
zuhgu intro p hp hp1 hp2
zuhgv intro s hs s' hs' hne p hp hp'
zuhgw intro t ht htop' hact'
zuhgx intro x h1 h2 hx
zuhgz left; nlinarith
zuhha left; rw [← h0, Geometry.lerp_zero]
zuhhb left; rw [← hs0, Geometry.lerp_zero]
zuhhc let C0 := gChain P g i hn hi
zuhhe obtain ⟨-, he⟩ := h1 hc1
zuhhf obtain ⟨a, b⟩ := inA.1 h1
zuhhg obtain ⟨a, b⟩ := inB.1 h1
zuhhh obtain ⟨b1, -⟩ := Restore.nf_bounds hNW
zuhhi obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
zuhhj obtain ⟨e0, h1⟩ := hn2 hu
zuhhk obtain ⟨ea, eb⟩ := tour_ends hi2
zuhhl obtain ⟨h0, e1⟩ := hn1 hu
zuhhm obtain ⟨h1, h2⟩ := this
      grind
zuhhn obtain ⟨h6, h2m⟩ := sidePt_top_copies J.left
zuhho obtain ⟨hRC, -⟩ := regOf_spec hNF
zuhhp obtain ⟨ha, hb⟩ := hchord_end_mem_boundary h
zuhhq obtain ⟨hc, ha⟩ := query_chord hj
zuhhr obtain ⟨hfin', hcard⟩ := ih hS'
zuhhs obtain ⟨hkN, h6⟩ := hw rfl
zuhhv obtain ⟨hr1, hr2⟩ := bandOf_not_l41 hr
zuhhw obtain ⟨k0, k1⟩ := attach_key_mem hB
zuhhx obtain ⟨p, hp⟩ := regionsIn_nonempty hP
zuhhy obtain ⟨reg, hregs⟩ := nfregs_of hE
zuhhz obtain ⟨reg₀, hreg₀⟩ := nfregs_of hE
zuhia obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 h
zuhib obtain ⟨z, hz⟩ := Chazelle.Chain.regionsIn_nonempty hR
zuhic obtain ⟨z, hz⟩ := regionsIn_nonempty hP
zuhid obtain ⟨z, hz⟩ := regionsIn_nonempty hQ
zuhie rcases C.chordEnd_cases hk hσ hf with hset | hwall
zuhif rcases C.sideGood_sideBeta hP with h' | h' | h'
zuhig rcases cover hT hk hr with h | h
zuhih rcases cyc_two hkk hxa hxa' with h2 | h2
zuhii rcases h.innerSeg_cases hQ hd' hnc with hs | hs
zuhij rcases hball x hxb hxB with h | h
zuhik rcases hlt u hu hpu with h1 | e
zuhil rcases hnot v hv2 hvD with hfv | hfv
