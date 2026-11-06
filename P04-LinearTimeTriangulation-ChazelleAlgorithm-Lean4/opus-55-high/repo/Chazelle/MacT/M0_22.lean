module

public import Chazelle.MacT.Base

public section

set_option hygiene false

zg zucrc simp only at q0 q1
zucrd unfold Polygon.edge
zucrf unfold nodeArc0 sj; rw [← hm.SB]; omega
zucrg unfold sideInArc at hc; grind
zucrh unfold sideInArc at hin ⊢
zucri unfold sideInArc at hκ ⊢
      grind
zucrl ext R
      simp only [mem_empty_iff_false, iff_false]
      rintro ⟨D, -, hD⟩
      exact hk hD.1
zucrm filter_upwards [ih h2, self_mem_nhdsWithin] with ε hε hε0
      simp only [pe, h1, zero_add]
zucrn have d1 := hL.dSz; have d2 := hL.dSl; have d3 := hL.dPS
      unfold Disj at d1 d2 d3
zucrs have hA := DrvD.arcs_length (M := I) (Q := Q) (E := E) B.hK
zucry have ord := ray_lt_iff (p := z) (t := t) (t' := tb) hσ1
zucsb have w := ‹WordsBounded W { c with nreg := upd c.nreg 170095 (c.nreg 170072) }›
zucsc intro r h1 h2 h3 h4; rw [hc3]; exact nbrHead_other _ _ h1 h2 h3 h4
zucsd intro v hv w hw h
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv hw
zucse intro x hx hcut
      obtain ⟨c, hc, p, t, hA, hk⟩ := hcut
zucsf obtain ⟨-, -, -, reg, -, -, hArcs, -⟩ := hNF
zucsi obtain ⟨X, hX, a, b, harc, hin⟩ := hM.arc_around hF hfin hne hncut
zucsj obtain ⟨X, hX, l, r, harc, hin⟩ := WalkEmbed.exists_arc_around hGM hFam hpos hcut
zucso obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := e1
zucsp obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
zucsq obtain ⟨h60, h61, h62, h65, h68, h70, hr70, hr72⟩ := hC
zucss obtain ⟨hT0, -, -⟩ := Merge.hit_of_freeAt C hzt hσ' hf
      exact hno hne _ hT0 hTA
zucst obtain ⟨hc, ha⟩ := query_chord (J := J) (Q := Qof P) hj
zucsv obtain ⟨hpf, hoF⟩ := hC.decomp hfF.1 hfF.2.1 hfF.2.2.1
      set d' := dOf W.n g pf with hd'def
zucsw obtain ⟨hw, hi, hz, hfn, hfr, hnm, hrm, hout⟩ := hI
zucsy obtain ⟨q00, q26, q01, qr₁, qm₁, qrr₁, qrm₁, qo₁⟩ := q
zucsz obtain ⟨q500, q501, q502, q503, q504, q505, q103, q104⟩ := q
zuctc obtain ⟨x, hx⟩ := hne r hr
      obtain ⟨y, hy⟩ := hne _ hdn
zucte obtain ⟨δ, hδ, h1⟩ := hW
      obtain ⟨δ₂, hδ₂, h2⟩ := hW₂
zuctg rcases attach_two hP hN hD h₀ h₁ hA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
zucth rcases hlive q' hq' with ⟨h1', h2'⟩ | ⟨t', ht', rfl, _⟩
zucti rcases hpart with ⟨c', hc', hfc', V', hV', hVs', hgV'⟩ | hoff
zuctj rcases hsplit i hi with ⟨h1, e⟩ | ⟨t, ht, rfl, e⟩
zuctk rcases hst with ⟨-, hp0, h22⟩ | ⟨-, hp0, A, -⟩
zuctm rintro c hc ⟨pa', pb', ta', tb', hA, hB, hAB, hiff⟩
zuctp rw [hIW] at hA hps
      obtain ⟨hp, hs0, hs1, -⟩ := id hA
zucuc rw [show v.1 + 1 * s₀ - v.1 = s₀ by ring, abs_of_pos hs₀0]; linarith
zucug set w2 := (endPos N d q0).edge
      set hc2 := (endPos N d q0).hgt
zucuh simp only [okB, okI, oE, oFE, oD, sw]
      simp only [Nat.reduceAdd]
zucuj subst h1
zucuk unfold EvBrk at hZb
      push Not at hZb
      obtain ⟨pz, tz, hZz, hzL⟩ := hZb
zucul unfold LblR at hq
      simp only [kN, kL, aF, sP, sw] at hq
      omega
zucun unfold phaseBands at h1; simp only [Finset.mem_Icc, not_and_or, not_le] at h1
      unfold OutB; omega
zucuo by_cases h : D.NonAdj
zucup by_cases h5 : a = B' + 3 * j
zucuq by_cases hT : C.topIdx = 0 ∨ C.topIdx = C.m
zucur by_cases hb : c.nreg 30001 < K
zucus by_cases hg : e - 6 - C.m < C.m
zucut by_cases htop : IsTop pch σ.rem t
zucuu by_cases hv1 : v ≤ c.nreg 170054
zucuv by_cases hv2 : c.nreg 170055 ≤ v
zucuw by_contra hA
      set Z := A + P.n + 1
zucux by_contra hge
zucuy by_contra hh; push Not at hh
zucuz by_contra hp
      let V := p + A + 1
zucvb classical
      set D := dom R S with hD
      obtain ⟨q, hqf, rfl⟩ := hU
zucvg exact Geometry.left_mem_segment _ _
zucvh exact Nat.ModEq.eq_of_lt_of_lt h2 (by have := C.m_lt; omega) (by have := C.m_lt; omega)
zucvi exact h2
zucvr have hA := agree_N hT hsl hsl'
zucvs have hA := agree_pre hu h1 h2
zucvt have hA0 := arcs_pos hP₁ hNF
      obtain ⟨b7, b4A, b6A⟩ := NFLoc.nfWithin_bounds hNT hNF hA0
zucvu have hG := hE.hG
zucvv have hGcap := gradeGran_cap (g := lam) h7
zucvy have hM := walkAx_chainModel (C := C) hP
zucvz have hM := walkAx_chainModel (C := J.whole) hP
zucwa have hP₁ : J.left.P.Simple := E.hP
      have hNF := E.hNF₁
zucwc have hW := hS.nW
zucwg have hfit := gradeLen_fit hn hi
      have hl1 := gradeLen_pos hn hi
      have hl2 := gradeLen_le P.n g i
zucwi have hhn := (regOf_spec hN).2.2.2.2.2.1 k hk
zucwk have hmn := T.hm
zucwo have hsN := S.hs
      rw [hN] at hmN hsN
      have hHA := S.hHA
      have hAW := S.hAW
zucwp have hsys := hM.sys S hF hfin
zucwr have hxu := (cyc_unwrap hlb hlb hrb hxb hab').1 hin
      rw [unwrapK_self] at hxu
zucww have k1 := hKc.2.1
zucxb intro a b d e ha hb hd he c hw hctx hp1 he1 hp2 he2 hyy hY hroom
zucxc intro a b d e ha hb hd he c hw hctx hx hxe hx0 hy hye hy0 hroom
zucxd intro f f' hop hD hf hf' hbtw
      apply hD
zucxe intro k' hk'
zucxf intro r h1 h2
zucxg intro t ht i i1 i2 h
zucxh obtain ⟨-, hA, ek, eh, hh, hy⟩ := chordPos_attach hN hi hxi
zucxi obtain ⟨A₀, hA₀, h⟩ := h
zucxj obtain ⟨_, ⟨_, _⟩, ⟨_, _⟩⟩ := a
      simp_all
zucxk obtain ⟨c', k, e, I', RF', hk⟩ := round_step hE I ht
zucxl obtain ⟨c, hc, hxc⟩ := hx
zucxn obtain ⟨c₃, k, ex, hk, ca, -⟩ := cand0_exec c₂ w₂ hN
zucxo obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hgood s d hdx
zucxq obtain ⟨h3, hinj, hedge⟩ := hP
zucxr obtain ⟨hL1, hLn, -⟩ := diagLen_spec hd.1 hd.2.1 hd.2.2.1
      have hsp := splitPair_split hQ hd
zucxs obtain ⟨hl, hHW, -, -⟩ := hwf.2 H C hC
      have h1 := C.add_one_le
zucxt obtain ⟨hmS, hmmin⟩ := leftmostVtx_spec P hSfin hSne
      set w := leftmostVtx P S with hwdef
zucxu obtain ⟨hwy, hwa, hwb⟩ := hw
zucxv obtain ⟨i, hi, hxi⟩ := hx
zucxx obtain ⟨q20, q43, r₁⟩ := q
zucxy obtain ⟨q60, q61, r₅⟩ := q
zucxz obtain ⟨rs, ax, hD⟩ := L.stops
zucya obtain ⟨s1, s2, s3, s4⟩ := hsnd hflag
      rw [a2] at s4
zucyc obtain ⟨x, hx, rfl⟩ := hc
zucyg push Not at hsl
      by_cases hsl' : ℓ ≤ s'
zucyh push Not at htie
zucyi rcases (AncX.back_iff h).1 h1 with e | ⟨-, -, -, h2⟩
zucyj rcases List.mem_append.1 hx with h | h
zucyk rcases List.mem_append.mp hq with hq | hq
zucyl rcases List.mem_cons.1 hpc with rfl | hpc
zucym rcases Nat.eq_zero_or_pos p with rfl | hp0
zucyn rcases Nat.eq_zero_or_pos p with rfl | hp1
zucyo rcases Nat.eq_zero_or_pos γ with rfl | hγ
zucyp rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
zucyq rcases eq_or_lt_of_le ht1 with h1 | h1
zucyr rcases hl with h | h | h | h
zucys rcases hle with hlt | ⟨hh, -⟩
zucyu rcases pos_on_chain C hp ht ht1 hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
zucyz refine mem_closure_of_tendsto htend ?_
zuczb rintro (h | ⟨h, h'⟩)
zuczc rintro (h1 | ⟨h1, h2⟩)
zuczd rintro _ ⟨j, hj, rfl⟩
      obtain ⟨h1, h2⟩ := hmem j hj
zuczf rintro c' ⟨hres, hfr⟩
zuczg rintro p ⟨hp1, hp2⟩
zuczh rintro x hx ⟨k, hk, hxk⟩
zuczi rintro ⟨a, b, hab, rfl⟩
zuczj rintro ⟨u, hu0, hu1, rfl⟩
zuczk rw [Chazelle.Chain.regionsIn_eq_component hU hzU]
      exact hLc.subset_connectedComponentIn hzL hLF
zuczm rw [List.map_map]
zuczn rw [List.pairwise_map]
zuczo rw [Nat.mod_eq_of_lt h]; omega
zuczp rw [b2, SignTest, heb, hen, hd]; simp only [Visibility.rayPt_fst]
      grind
zuczr rw [dist_rayPt _ (by rcases hτ with rfl | rfl <;> norm_num) hs₂0.le]; omega
zuczt rw [e] at ht1 ⊢
zuczu rw [h']
zuczv rw [h1] <;> rcases hv with ⟨rfl, h⟩ | ⟨rfl, h⟩
zuczw rw [h2]
zuczx rw [h2] <;> rcases hv with ⟨rfl, h⟩ | ⟨rfl, h⟩
zuczy rw [hF, Set.ncard_empty, zero_add] at hcard
      obtain ⟨U, hU⟩ := Set.ncard_eq_one.1 hcard
zuczz rw [hK₁, hK₂]; rw [hK₁, hK₂] at hK; exact components_disjoint hK
zudab rw [heq]
zudac rw [heq] at hue'
      obtain ⟨s, hs0, hs1, hs⟩ := Geometry.mem_segment_iff_lerp.1 hue'
zudad rw [hk, hk']; push_cast; linarith
zudae rw [hmem₇]; unfold recRMem
zudaf rw [hv.CQ, hv.s, show (Qof P).n = P.n from shear_n _ _]
zudah rw [ite_eq_left hact] at hact'
zudaj rw [mem_ball, dist_comm, Prod.dist_eq]
      simp only [hx, Real.dist_eq, sub_self, abs_zero]
zudal rw [mem_image_mir]
zudap rw [show c + 7 = 2 * m + 7 by omega, Nat.mod_self]; omega
zudaq rw [this]; exact C.top_mem_set
zudas rw [v46]; exact hI.vbG
zudat rw [v46]; exact hI.vbn
zudau rw [v59]
      split_ifs with hg0
zudav rw [vsp, h00, show e - 6 + 6 = e by omega]; rfl
zudaz rw [x100, x101] at rest₆
      obtain ⟨-, z₆, -⟩ := rest₆ hY7
zudba rw [← ha', zero_add] at hab
      positivity
zudbb rw [← hpp, ← htt] at hA'
zudbc rw [← o0] at this
zudbd rw [← oW_eq, ← Lst_eq] at this
zudbe rwa [lt_div_iff₀ hK0] at this
zudbf rwa [prev_succ_mod hp] at this
zudbg set A := c.nreg ALLOC with hAd
zudbh set M := chainModel C with hMdef
zudbi set M := chainModel J.whole with hMdef
zudbk set cnt := gradeCount P.n g with hcnt
      set K := stepB κB κL κG O.κ g with hK
zudbl set d₁ := ({ d with nreg := upd d.nreg 150075 _ } : Config) with hd₁
zudbn set n := (chainModel J.whole).W.n with hn
zudbo set n := (chainModel J.whole).W.n with hndef
zudbq set t := (chainModel C).param Q x
zudbs set ε := min r s / 2 with hε
zudbt simp only [Chain.slitTop] at this
zudbu simp only [Enc] at hE
zudbv simp only [Finset.coe_range, Set.mem_Iio] at hi hj
zudbw simp only [Geometry.add_snd, Geometry.smul_snd] at this
      grind
zudbx simp only [Geometry.lerp_snd]; grind
zudby simp only [HostEdgeOK] at hok
zudbz simp only [Machine.upd_same]; omega
zudca simp only [Nat.add_zero] at h0
zudcb simp only [Polygon.triVertices, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl | rfl
zudcc simp only [SignTest, testPoly]
zudcd simp only [decide_eq_true_eq] at h
zudce simp only [leaves, List.mem_flatMap] at h
      obtain ⟨q, hq, hq'⟩ := h
zudcf simp only [lerp_fst, rayPt_fst]
zudcg simp only [outList, List.mem_map] at hx
      obtain ⟨u, hu, rfl⟩ := hx
zudch simp only [rayPt_fst]; grind
zudci simp only [sub_self, mul_zero, zero_sub]
      nlinarith
zudcj simp only [upd, show R + 246 ≠ R + 247 by omega, ↓reduceIte]
zudck split_ifs <;> first | rfl | omega
zudcl unfold Model.param; simp_all
zudcm unfold dq; grind
zudcn unfold sideInArc; simp
zudco all_goals simp only [k46, k50, k51, k52, k53, k54, k55]
zudcz have hW8 : 8 ≤ W := by unfold hostWords at hHW; omega
      have hD6 := hmwf.1
zuddc have hfX := harc.2.2.2.2.2.2 p s hp hs3.1 hs3.2 hs2
      have hXU := WalkAx.faces_unique hX hU hfX hs1
zuddd have hfX := harc.2.2.2.2.2.2 p t hp ht.1 ht.2 hin
      have hXU := WalkAx.faces_unique hX hU hfX hf
zuddm have r1 := (h.param_mem_iff hx).2 hm
      have r2 := (h.param_mem_iff hx').2 hm'
zuddp intro x hx hxS hxl
      apply hxS
      obtain ⟨hxD, hxc⟩ := hfree x hx hxl
zuddq obtain ⟨-, -, -, -, -, hfree, hfac⟩ := harc
zuddr obtain ⟨-, -, -, -, hJ, hJW, -⟩ := hA.hst
zudds obtain ⟨-, -, -, -, r, hr, hleft⟩ := hA
zuddt obtain ⟨-, -, -, -, r, hr, hl⟩ := hA
zuddu obtain ⟨-, -, esC', -, -⟩ := stp_arrays_c' S.E S.L S.hI S.hd
zuddv obtain ⟨-, -, hmem, -, -, hA, -⟩ := hf
zuddw obtain ⟨-, -, hp1, hp2, -, -⟩ := copy_facts J hδ
zuddx obtain ⟨a, b, d, e, f, g, i⟩ := KA
zuddy obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h
zuddz obtain ⟨b10, hiv, b11, b14, i11, i14, h5⟩ := hTF
zudea obtain ⟨b3, -⟩ := Restore.nf_bounds hNW₁
      obtain ⟨b4, -⟩ := Restore.nf_bounds hNW₂
zudeb obtain ⟨c', a', r', s', d', ro', l'⟩ := N'
zudec obtain ⟨c', k, e, h1, h2, h3, h4⟩ := hh
zuded obtain ⟨c, a, g, s, d, o, l⟩ := N
zudef obtain ⟨c₂, k₂, e₂, I₂, RF₂, hk₂⟩ := rounds_exec hE hI0
zudeh obtain ⟨e, he, heK, q, s, hQ, hQ0⟩ := hpock
zudei obtain ⟨e, h⟩ := x; simp only at h0; subst h0; rfl
zudej obtain ⟨hB1, hB2⟩ := hB t' ht' htt' h1
      by_cases e : t' = t
zudek obtain ⟨ha0, han, hb0, hbn, -, hfree, hfac⟩ := h
zudeq obtain ⟨j, hj⟩ := KPath.last hk hne
      obtain ⟨j', hj'⟩ := he
zuder obtain ⟨k, hk, t, ht0, ht1, e⟩ := mem_set_lerp C hz
zudes obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' h.le).1 (Nat.ModEq.add_left_cancel' _ hxy).symm
zudet obtain ⟨k0, k1, k6, k4, k5, k2, k3⟩ := hK₀
zudeu obtain ⟨n1, -, -⟩ := new_top_facts h hch hT hB hI hpk hc
      simp_all
zudev obtain ⟨r₁, rr₁, m₁, rm₁, o₁, a₁, b₁⟩ := fT
zudex obtain ⟨y1, y2, y3, y4, y5, y6, -⟩ := d.lay
zudey obtain ⟨σ, T, hσ, hT, hray, hseg⟩ := seg_ray hwu hwy
zudfa rcases h with ⟨C, hC, rfl⟩ | ⟨Q, hQ, rfl⟩
zudfb rcases hG with ⟨C, -, rfl⟩ | ⟨Q, hQ, rfl⟩
zudfd rcases hy₁C with ⟨v, hv, hvy, -, h3, h4⟩ | h
zudfe rcases hy₂C with ⟨v, hv, hvy, -, h3, h4⟩ | h
zudfj rintro c₁ k₁ hk₁ hw₁ ⟨hdet, hfr, hn, hnm, hrm, hout⟩
zudfk rintro c₂ hI₂ hA₂ hA₂' hc₂
      have hm₂ : c₂.nmem = c'.nmem := by rw [hc₂]
zudfl rintro c₄ hI₄ - - ⟨hA4, k4, hm4, -, -, -⟩
zudfm rintro ⟨w₁, w₂, w₃, hw₁, hw₂, hw₃, hw, rfl⟩
zudfn rw [c2'] at hj
      rw [c1', hm1, harcs j hj, c7]
zudfo rw [e1, e2, WalkAx.wa_eq, v0, v25, v26, slitTop_sub_top] at hsE
zudfp rw [e1, e2, WalkAx.wa_eq, v7, v5, v6, slitTop_sub_top] at hsW
zudfv rw [hArr.2.2.2.1, ← hgk] at hin
      rw [hR.1, eGB, eGK]
      omega
zudfw rw [hW, C.sideWalk_vtx_tour _ le_rfl, Chain.sideTour, e2m, h6, ht]; rfl
zudfz rw [show (Qof P).n = P.n from shear_n _ _, hE.n_eq]
      omega
zudga rw [show xAt sL c = xAt s c by linarith]
      exact pt_mem_seg hsu hcs1 hcs2
zudgb rw [show xAt sR c = xAt s c by linarith]
      exact pt_mem_seg hsu hcs1 hcs2
zudgc rw [unwrapK_self, ← hA.hud, ← hu0]
      exact ukey_mono hM hF hfin hA.hil hA.hd0 hA.hdN
zudgd rw [vtx_rotate P s h.1, vtx_rotate P s h.2.1, vtx_rotate P s h.2.2]
      rfl
zudgf rwa [show sw _ = gR + u by unfold gR sw; omega] at this
zudgg rwa [show sw _ = kL + u by unfold kL sw; omega] at this
zudgl simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, pcSet_append]
      rw [← Set.union_assoc]
      exact b₄
zudgm simp only [List.getElem_map, List.getElem_range, Function.comp]
      simp only [List.length_map, List.length_range] at h1
zudgn unfold Host.poly Host.whole Host.pts HostItem.pts
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map, zero_add]
zudgx have b35 := g.base_eq 35; have b36 := g.base_eq 36; have b37 := g.base_eq 37
zudha have g₄ := fun r (hr : Bhost r = false) => f₄.1 r hr
zudhb have h := hsys.dualGraph_reachable hW.preconn hW.nonempty subset_rfl U hU V hV
      rw [SimpleGraph.reachable_iff_reflTransGen] at h
zudhg have hHU := subset_region hU hHc hHfree hs₁H hs₁U
zudhh have hK₂ := E.hK.fix hI₂
zudhi have hRa''s := haft'' Ra'' hRa'' hWa''
      rw [hdY''e, neg_neg, hY''s] at hRa''s
zudhj have hUc := (isPreconnected_connectedComponentIn : IsPreconnected U)
zudhm have hc := chord_mem (M := chainModel J.right) (Q := Qof P) hkN
zudho have hdom := ChainObs.dom_eq (C := C)
zudhu have hn := cm_n J.right
zudhv have hn := walk_n (C := C)
zudhw have hn3 := Chazelle.Jordan.simple_three_le hQ
zudhx have hnd := (hRs r hr).2.2.1
      set L := (N.region r).arcs
zudhy have hne := sub_ne_zero.2 h.symm
zudia have hσ := dirOf_cases' b
zudib intro M Q F hM hF c hc p t hA hsole
      have hW := walkAx_of_goodModel hM
zudic intro V hV
      obtain ⟨U, hU, hVU⟩ := exists_chain_region hQ T hF₀.2.1 hV
zudid intro c c' ⟨h1, h2, h3, h4⟩ hr _ hm _ _
zudie intro e; rw [e] at h; exact lt_irrefl _ (h.lt_q.trans h.q_lt)
zudif intro g hg p' τ hp' h0 h1 hkk
zudig intro h; have := congrArg Prod.fst h; simp [rayPt] at this; linarith
zudih intro h; rw [← h] at hin; unfold sideInArc at hin; simp_all
zudii intro heq
zudij intro v hv h1 h2 h3 h4
      rcases lt_trichotomy v.2 q.2 with hlt | heq | hgt
zudik intro ε hε
zudim obtain ⟨-, -, hy, -, -⟩ := stOrig_facts hP hN hD.ok
zudin obtain ⟨a0, a1, a2, a3, a4⟩ := h i h1
      grind
zudio obtain ⟨a1, a2⟩ := hE.areas hr
zudis obtain ⟨hpA, hsA, hgap, hin⟩ := h.dead_gap hE hc hne' hn hcnt
zudit obtain ⟨hpae, hoae⟩ := hC.decomp₂ hA₁.1 hA₁.2.1 hA₁.2.2.1
      rcases hoaL.lt_or_eq with hlt | heq
zudiu obtain ⟨hq1, hq2⟩ := box_of_dom hq
      by_cases hab : |a| < R
zudiv obtain ⟨hreg, -⟩ := regOf_spec hN
zudiw obtain ⟨hs, hint, hbd, hvx⟩ := polyFacts_rotate hQ hFam hne hR i0
zudix obtain ⟨ht0, hhor, -⟩ := hM.tie_shape hF hce hcw hAe hAw hE hW
zudiy obtain ⟨hxm, hk⟩ := List.mem_filter.1 hx
zudiz obtain ⟨i, h1, h2, hx'⟩ := (mem_vs x).1 hx
zudja obtain ⟨k0, k1⟩ := attach_key_mem hA
zudjh obtain ⟨y, a, b, h, -, rfl⟩ := hF hc
zudji obtain ⟨y, a, b, hch, -, rfl⟩ := hF₀ hc
zudjk rcases C.sideS_mod C.sideBeta with ⟨hs, hc⟩ | ⟨hs, hT0, -⟩
zudjl rcases C.sideWalk_pos_cases C.sideBeta hp ht with hbox | ⟨i, hi, rfl, hit⟩
zudjm rcases hs with ⟨hacc, hpi, ha⟩ | ⟨hdone, -⟩
      swap
zudjo rintro V ⟨d, hd, t, ht, hc, hf, -⟩
zudjp rintro c' ⟨v, o, m⟩
zudjq rintro y (⟨v, -, rfl, h, -⟩ | h)
zudjr rw [D.det_bot_top hP]
zudjs rw [List.length_map, show (Qof P).n = P.n from shear_n _ _]
zudjt rw [Nat.mod_eq_of_lt h1]
zudjv rw [det_eq_zero_of_mem_segment hx1] at hx'; simp_all
zudjw rw [e₄]; simp [cutL, regB, regI, upd]; omega
zudjz rw [ha, hostPt_eq M.W hA.2.1 hA.2.2.1]
zudka rw [hm₄, Machine.upd_other _ _ _ (by have := h.dA; omega)]
zudkd rw [i5, i6]; exact hE.xPosG
zudkg rw [lbl c', v2, hl]
zudkh rw [mpass_eq hw hne]
      have hB := merge_block_length (le := le) w l
zudki rw [newLB_zero _ _ _ hK]; exact (newL0_ok hE.hQ hE.hDH hE.hli).2.1
zudkn rw [show c.nreg 70142 - 1 + 1 = c.nreg 70142 by omega] at hgeo
zudko rw [show p + 1 = Q.n by omega, Nat.mod_self] at this; omega
zudkp rw [show x.edge + 1 = Q.n by omega, Nat.mod_self] at this; omega
zudkr rw [v₃]; unfold tci; grind
zudks rw [← sig_le_iff (C := C) (C' := C')]; grind
zudku set C := hostChain Q S R g h3
zudkv set K := nk I S R with hK
zudkw set c₁ : Config := { c with nreg := upd c.nreg 50002 _ } with hc₁
zudkx set c₁ : Config := { c with nreg := upd c.nreg 50058 _ } with hc₁
zudky set c₁ : Config := { c with nreg := upd c.nreg 50120 _ } with hc₁
zudkz set c₃ : Config := { c₂ with nreg := upd c₂.nreg _ _ } with hc₃
zudla set t := Pn - s.edge with htdef
      have hub := (unwrapK_bounds ha hke).2
zudlb simp only [Bprim, Bool.or_eq_false_iff, decide_eq_false_iff_not]
zudlc simp only [Config.nreg_mk, Machine.upd_same]; omega
zudld simp only [Finset.mem_filter, Finset.mem_range] at hi
zudle simp only [Finset.mem_insert, Finset.mem_singleton, bandOf, bBuild, bSort, bSign] at hr
zudlf simp only [Finset.mem_insert, Finset.mem_singleton, bandOf, bSort, bSign, bBuild]; omega
zudlg simp only [Geometry.add_fst, Geometry.smul_fst] at this
zudlh simp only [Geometry.lerp_fst]
zudli simp only [Nat.add_sub_cancel]
zudlj simp only [Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl, rfl⟩ := hq
zudlk simp only [Prod.mk.injEq] at hreq
      obtain ⟨h1, h2, h3⟩ := hreq
zudlm simp only [not_or] at hcon
      obtain ⟨hj0, hj1, hjn⟩ := hcon
zudln simp only [rayPt]
zudlo simp only [rayPt_fst]
zudlp simp only [regB, regI, upd_same]
zudlq simp only [sub_self, abs_zero, add_sub_cancel_left]
zudlr simp only [upd_apply]
zudls simp only [upd_same, e1011, e1201]
zudlt simp only [zero_smul, add_zero] at this
zudlu split_ifs with h1
zudlv split_ifs with h1 h2 h2
zudlw subst ht0
zudlx unfold Merge.shoot
      rw [← hT, rayPt_back]
      have hT' : T ≠ 0 := hT0.ne'
zudly unfold NF.chord
zudlz unfold chordSet Chazelle.segment
      simp only [mem_ofPred_eq, mem_image, mem_Icc, chordEnd_fst, chordEnd_snd]
      constructor
zudma unfold sideE
      grind
zudmc apply le_antisymm
zudmd apply polygon_ext
      rw [vertices_subPoly]
zudme by_cases hqp : q = p
zudmf by_cases hs0 : s = 0
zudmg by_cases hsl : s < ℓ
zudmh by_cases ht : t' = 0
zudmi by_cases hxa : x = a
zudmj by_cases hσ : V.σb < 1
zudmq exfalso
      rcases pos_and_pos_or_neg_and_neg_of_mul_pos hsame with ⟨h1, h2⟩ | ⟨h1, h2⟩
zudms filter_upwards [hq1, hq2, hf1, hg2] with ε h1 h2 h3 h4
zudmu have C₂ := keepArc Fa C₁
zudna have g₄ := f₄.1
zudnb have h := DownDrv.buildNF_arc hK hj
zudnc have h0 := hS.r0
      have h1 := hS.r1
      have hl := hS.rli
      have hp := hS.ptr
zudnh have h1 := J.one_le_m₁
zudni have hAc := hI.hA
zudnj have hC := h.ctx
zudnk have hFs := F₂plus_subset J hS₂
zudnl have hFs := hC.hF
zudnn have hK := hA.hK
zudnq have hN := h.isNF
zudnv have hR := B.hregs.1.1 r hr
zudnw have hR := radius_of_P J hC'P
zudnz have hRo := hsys.regionsIn_open subset_rfl hR
zudoe have hW3 := hD.W1
      obtain ⟨y1, y2, y3, -⟩ := d.lay
zudog have hX := normPos_vtx M Q P.n x
      have hY := normPos_vtx M Q P.n y
zudoh have hab := hH.lt
zudoi have hb := hbeyond d t hv ht0 ht1 hlt
      rw [hu0] at hb
zudoj have hb1 := bL_one hq hK fr hb
      have h₁ := (hq.hbL.2).1 hb1
zudoo have hj := tj_lt C i
zudoq have hlt' := hch'.lt
      obtain ⟨hzbA, hzbB⟩ := piece_ends_bd hQ T hD hch'
zudov have hn3 := hQ.1
zudox have hn₂ := hC.n₂_pos
zudoz have hoe : o ∈ e := by rw [heo]; exact origin_mem J
zudpc have hr' := hr
zudpd have hregH := hreg H hC.1
zudpe have hs := sA_lt (C := C) (β := β)
      unfold tourA
zudpg have hsome := stp_key_some S.hI S.hd
zudpi have ht := tpos_lt C J
zudpl have hv := hT.hv
zudpm have hw := hI.wb
zudpn have hw5 := e5.wb_right
zudpp have hw₅ := e₅.wb_right
zudpu have hτw := tpos_lt J.whole J.m₁
zudpx have k0 := hK.1
zudpy have k02 := (E.hK.fix hI₂).1
      by_cases h2 : d₂.nreg K0 < d₂.nreg kqO
zudpz have k0₂ := k0_of hE hI₂
zudqb have r1 := hG2.one
zudqc intro h' i hi hic
      obtain ⟨a, b⟩ := h' i hi.1 hic
zudqd intro h1
zudqe intro hd
zudqg intro r hr; rw [hc6]; exact regB_out _ _ _ faceRead_dst hr
zudqh intro r v hR hb
      obtain ⟨r0, r1⟩ := Corr.key_mem hR.1 hR.2.1 hR.2.2.1
zudqi intro x hx hnv hnv'
      simp only [NonVtx, not_forall, not_not] at hnv
zudql obtain ⟨-, -, -, hS⟩ := NFLoc.isNF_arcs hN
      exact hS.1.nodup_iff.2 List.nodup_range
zudqm obtain ⟨-, -, -, hl, -⟩ := hNA.2.2.2.2.2.2.2.1 _ hrl
zudqo obtain ⟨-, -, hs1, hs2, hs3, hs4⟩ := hC
zudqp obtain ⟨-, hky, hk1, hk2⟩ := hk
      rw [hky]
zudqq obtain ⟨-, i1⟩ := h1
      obtain ⟨-, i2⟩ := h2
zudqr obtain ⟨-, w2, w3, w4, -⟩ := o4 hlt hnb
zudqs obtain ⟨a1, a2, a3, a4, a5⟩ := h i hi
zudqt obtain ⟨a1, a2, a3, a4, a5⟩ := h.rr x hx'
zudqu obtain ⟨a4, a5, a7, a11, a12, hM⟩ := hJ
zudqv obtain ⟨b, hb, rfl, hi⟩ := hit p hp; grind
zudqy obtain ⟨c', k, ex, hk, h1, h2⟩ := H
zudqz obtain ⟨c, hc, p', t', hAc, hkey⟩ := hcut
zudra obtain ⟨d', k, x', hk, h2, h3⟩ := push
zudrb obtain ⟨e', k, x, hk, hj', hm'⟩ := X
zudrc obtain ⟨g0, g1, g2, g3, g4, g5⟩ := e1
zudrd obtain ⟨h, hxh, hhn, hyz, hsec, -⟩ := hg
zudre obtain ⟨h5, h6⟩ := cyc_zero_out hBA hui
      have h7 := cyc_zero_closed hBA hx
zudrf obtain ⟨hL, hR⟩ := hend _ hcS
      rcases hqe with hqa | hqb
zudrg obtain ⟨hL1, -, hL2, -, hlt⟩ := caseG_consts J hδ
zudrh obtain ⟨hMD, hwf⟩ := Gran.desc_agree' hE.hwf hE.hMD hag
      have hwfc := hwf.mono hA
zudri obtain ⟨hSB, hj0, hRB, hLB, hlist⟩ := hm.node v hvA
zudrj obtain ⟨hi, hmF, -, hat, -⟩ := S.skip_at h1 h2
zudrk obtain ⟨hjm, ht0, ht1, hfl, hfr⟩ := hpos x hx
zudrl obtain ⟨hr, -⟩ := final_cut hK hRR h hch hisdn hI hna hk
zudrm obtain ⟨hz, H, C', hC, hM'⟩ := chainDesc_of hMD hM
zudrn obtain ⟨i_l, d, hD⟩ := arc_keys hM hFam.2.1 hFam.1 hne hR harc
zudro obtain ⟨na, nb, ea, eb, ia, ib⟩ := hpc
zudrq obtain ⟨r50, r51, r52, r53, r54, r55⟩ := hR
zudrr obtain ⟨v1, v2, v3⟩ := valid_next h hch hT hB hI o1
zudrs obtain ⟨y, a, b, h, hy, rfl⟩ := hc
zudrt obtain ⟨y, a, b, hch, -, hcab⟩ := h2
zudru obtain ⟨σ'', hσ'', hfr, he⟩ := chord_eq_shoot_of_end J.whole hAdm hbmem hbD
zudrw push Not at hnot
zudrx rcases ag1 with h | h
zudry rcases hB.slot j' hj' with h' | ⟨e', h'', hm, w⟩
zudrz rcases hM' with ⟨h0, -⟩ | ⟨-, -, h⟩
zudsa rcases hZ0.lt_or_eq with hpos | hzero
zudsb rcases hcl with h | ⟨h6, hlt⟩ | ⟨hend, -⟩
zudsc rcases hd with hd | hd
zudsd rcases he with rfl | rfl
zudse rcases hg q hq with ⟨hl, he⟩ | ⟨he, hq'⟩
zudsf rcases hj with rfl | rfl
zudsg rcases hle.lt_or_eq with hq | hq
zudsh rcases hp with hp | hp
zudsi rcases ht0.lt_or_eq with htp | rfl
zudsj rcases hvl.lt_or_eq with h1 | h1
zudsk rcases hvr.lt_or_eq with h2 | h2
zudsl rcases hx with rfl | rfl
zudsn rcases o2 with ⟨hF', e1, e2⟩ | ⟨e1, e2⟩
zudso rcases q.hcls with h | ⟨h6, -⟩ | ⟨h6, -⟩
zudsp refine (Chain.isOpen_box R).sdiff ?_
      refine hS.fin.isClosed_biUnion fun s _ => Geometry.isClosed_segment _ _
zudsq refine (hsort.and hnd).imp_of_mem fun {a b} ha hb hab => ?_
zudss refine originIn_copy ho ?_ ?_ ?_ <;> simp only [bandReg, bShoot] <;> norm_num
zudst rintro (h1 | h1)
zudsu rintro c₁ hI₁ - hA1 hc1
zudsv rintro c₃ hI₃ - - rfl
zudsw rintro c₄ hI₄ - - hc4
zudsx rintro d₂ hI₂ hA₂ hA₂' ⟨b1, -, k₂, ha₂, hm₂⟩
zudsz rintro rfl; tauto
zudta rintro x hx ⟨c, hc, p₁, t₁, hA₁, he⟩
zudtb rintro ⟨R, hR⟩
zudtc rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩; tauto
zudte rintro ⟨⟨h1, -⟩, ⟨h2, -⟩⟩; grind
zudtg rw [C.mem_slit_iff] at h1
zudti rw [Chazelle.Chain.sidePt_zero]
zudtj rw [Chazelle.Chain.sidePt_zero]; rfl
zudtk rw [Finset.mem_range] at hr
zudtl rw [Function.iterate_succ_apply']
zudtm rw [Geometry.point_ext_iff]
zudtn rw [Geometry.point_ext_iff]; simp_all
zudto rw [Geometry.segment_comm] at h
zudtp rw [List.mem_range] at ht
zudtq rw [det_rayPt_left]; linarith
zudts rw [eD] at a' g' geo'
      rw [eE, eH] at geo'
zudtt rw [e] at h
zudtu rw [e] at this
zudtv rw [e]; tauto
zudtw rw [e₃]; tauto
zudty rw [h0]
zudtz rw [hF']
zudua rw [hc2]; tauto
zudub rw [hc3]; rfl
zuduc rw [hc₁]; simp only [regB, regI, upd_same]; omega
zudue rw [hd] at pc₄
zuduf rw [hk, Nat.sub_self]
      simp only [HostItem.pts, List.getD_cons_zero, Enc]
      omega
zudug rw [hl]
zuduh rw [hmem5]
      unfold mem4
zuduk rw [hpA] at h1
      obtain ⟨-, h1a, h1b⟩ := h1
zudul rw [hpos]
zudum rw [hpt] at hray
zudup rw [hset]; tauto
zuduq rw [htake, List.mem_append, List.mem_singleton] at hin'
      rcases hin' with h' | h'
zudur rw [hz]
zudus rw [k01] at h2
zudut rw [k02] at h2
zuduv rw [k6] at hbox
zuduw rw [mem_Ioi] at hu
zudux rw [mem_mirF]
zuduy rw [neg_neg]
zuduz rw [not_and_or, not_lt, not_lt] at hin
      rcases hin with hle | hge
zudva rw [not_or] at hcon
zudvj rw [v3s, v3s1, n2s1, n2s, v1s, v1s1]
      unfold nhgt
zudvk rw [vb]; nlinarith
zudvn rw [zero_mul] at this
zudvo rw [← innerE_iff hQ T hD hli hx]
      unfold keepT at hk; simp_all
zudvp rw [← v46, ← v46'] at hmx
      rw [v46] at hmx
zudvs set m₀ := c.nmem with hm₀
zudvu set τ := tpos C J₀ with hτ
      set τ' := tpos C' J₀' with hτ'
zudvv simp (disch := omega) only [Machine.upd_other, hA', hbw, ALLOC]
zudvw simp (disch := omega) only [Machine.upd_same, Machine.upd_other, hA', ALLOC]
zudvx simp [NF.nRegions, BuildNF.buildNF]
zudvy simp [xAt, haR]
zudvz simp only [Bpt, Bprim, ALLOC, Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
      omega
zudwa simp only [chainHL, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp_all
zudwb simp only [mem_ofPred_eq, one_mul]; rw [← hcrossB]; exact h1
zudwd split_ifs at h ⊢ with hab
zudwe unfold Bsc at hr; grind
zudwf unfold det; simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; ring
zudwg unfold fpN
      rw [dite_eq_left hex]
      obtain ⟨a, b⟩ := Nat.find_spec hex
zudwh unfold hostWords at hWh
zudwi unfold kN at this; simp only at this; rwa [hfv] at this
zudwj unfold sideCross; simp only [Prod.fst_sub, Prod.snd_sub, lerp_fst, lerp_snd]; ring
zudwk unfold ψ; grind
zudwq apply Nat.clog_le_of_le_pow
zudwr apply csSup_le'
      rintro _ ⟨⟨a, b⟩, hab, rfl⟩
zudws apply csSup_le'
      rintro _ ⟨⟨a, b⟩, harc, rfl⟩
zudwt apply hseg
      rw [Visibility.segment_horizontal_eq_hseg hwz.symm]
      tauto
zudwu by_cases a1 : c₁.nreg 81011 < c₁.nreg i
zudwv by_cases h : c.nreg 170014 < c.nreg 170011
zudww by_cases h : j % 2 = 0
zudwx by_cases hin : i = P.n - 1
zudwy by_cases hlt2 : c₇.nreg 50171 < c₇.nreg 50032
zudwz by_cases hodd : d.nreg 150083 / 2 + d.nreg 150083 / 2 < d.nreg 150083
zudxb by_cases hs : c.nreg 140241 < c.nreg K1
zudxc by_contra h'
zudxk exact lt_of_le_of_lt (J.right.abs_le_coordBound_of_mem_set haR).2 J.right.coordBound_lt_radius
zudxm ext <;> simp [Geometry.lerp] <;> ring
zudxs have e1 := wrapK_unwrapK (n := n) (l := a) hx
zudxt have eD := candFr_qD fr
      have eL := candFr_bL fr
      have eR := candFr_bR fr
zudxx have h1 := Cα.one_le
      have ht := WalkEmbed.tpos_lt Cα J
      have hn' := WalkEmbed.cm_n Cα
zudxy have h1 := hI.room
      have h2 := RFall.2.2.2.2.2.2
zudyb have hA := agree_post hu h1 h2 hs
zudye have hC' := chainDescAt_copy hC hEb he hc
zudyf have hD := (goodShear_epsOf hG.2).2.1
zudyg have hFA := fuse_adm J hgen hS₁.2.1 hS₂.2.1
      have hfin := fuse_fin J hS₁.1 hS₂.1
zudyh have hG := hF.good
      have hHW := hF.hw
zudyi have hL'len : L'.length = n := by rw [← hseg, SortL.seg_length]
zudym have hNW := hE.NW
      have hNn := hE.n_eq
zudyn have hPC : C.P.Simple := by rw [hCdef, sideChain_P]; exact hP
zudyp have hT6 := κT_ge C
      have hT7 := κT_lt C
      have hTdef := rT_def C
zudyr have hWs := (FactsInterior.interiorWalk_spec hQ).1
zudys have hab := vtx_prev_ne_vtx_succ P i hP hi
zudyv have hcK : cc < d.K := by rw [hD.K]; exact hc.1
zudyx have hend := S.hend
      have h6 := S.h6
zudzb have hiμ : i.1 < V.μ := by rw [← X.μ]; omega
zudzd have hk1 := (hK.fix hI).2.1
zudze have hlt := ord.2 (b46.2.1 (by have := b46.1; omega))
zudzf have hlt := ord.2 (b47.2.1 (by have := b47.1; omega))
zudzr have ht0 := hA.2.1
      have ht1 := hA.2.2.1
zudzs have hx' : x < rs.length := by rw [h.rl]; exact hx
zudzt have hz0 := hclge _ hU0 z hzU
zudzu have hz0 := hclle _ hU0 z hzU
zudzv have k0₂ := (hK.fix hI₂).1
zudzw have kA := hA.kind
      have kB := hB.kind
zudzx intro U hU hUR
      rcases id hU with ⟨u, hu, rfl⟩
zudzz intro hb
      rcases hl.mem_boundary_cases hb with h | ⟨d, hd, hpd⟩
zueaa intro p hp hpR
      rw [hR, connectedComponentIn_eq hpR]
      exact connectedComponentIn_mono p hA'A
zueac intro x hx hxf
      have hi := List.idxOf_lt_length_of_mem hx
      have hxv := vtx_idxOf P hx
zuead intro σ; unfold det; simp only [lerp, rayPt]; ring
zueae obtain ⟨-, -, h3⟩ := (mem_seg_iff hs).1 hp
zueaf obtain ⟨-, -, hEb, -⟩ := hwf' H C hC
zueag obtain ⟨-, -, hne', -⟩ := OracleQ.arc_facts hN hne hj
zueah obtain ⟨-, -, hne', hfree⟩ := arc_facts hN hne hp
zueai obtain ⟨-, w2, w3, w4⟩ := o5 hlt hnb.1 heq.symm
zueaj obtain ⟨R', hR', hne, hsub⟩ := hK c hc hcG
zueak obtain ⟨_, _, _, _, _⟩ := a
      simp_all
zuean obtain ⟨c₂, e₂, v₂, -⟩ := copy_exec e₁.wb_right 120066 10010
zueao obtain ⟨c₂, e₂, v₂, r₂⟩ := copy_exec e₁.wb_right 120067 10010
zueap obtain ⟨c₃, e₃, v₃, -⟩ := copy_exec e₂.wb_right 120128 10010
zuear obtain ⟨e1, e2⟩ := h
zueas obtain ⟨h0, h1⟩ := h
zueat obtain ⟨h1, h2, h3, h4⟩ := hall H C hD
zueau obtain ⟨h7, hl1, hl2, hτp, hτl⟩ := left_G hδ
zueav obtain ⟨hDA, hall⟩ := hwf
zueaw obtain ⟨ha, hℓ⟩ := hwf
zueax obtain ⟨haN, har⟩ := (hArcs.2.2.2 r hr a).1 ha
zueay obtain ⟨hg, -⟩ := prep p t h1 h2 h3 h4 h5
zueaz obtain ⟨hi₁, -, hs, -⟩ := S.skip_at f1 f2
      simp_all
zueba obtain ⟨hjl, hjr⟩ := (hArcs.2.2.2 r hr j).1 hj
zuebb obtain ⟨hp1, hp2, hpx⟩ := (mem_seg_iff hsu).1 hps
zuebc obtain ⟨hv1, hv2⟩ := hv
zuebd obtain ⟨hy, hmin, hmax⟩ := (mem_seg_flat hf).1 hps
zuebe obtain ⟨hy, hmin, hmax⟩ := (mem_seg_flat hf).1 hws
zuebf obtain ⟨hτ0, hτ1, hnear, hnf⟩ := cap_param J hgen hext
zuebg obtain ⟨i, hi, his, -⟩ := NFLoc.listed_of_isArc hN hU hab
zuebh obtain ⟨j, hj, ha, hb⟩ := listed a b hab
zuebi obtain ⟨rC, hrC, hclean⟩ := FactsInterior.clean hWs hWo hp ht0 ht1
zuebj obtain ⟨r₁, hr₁, hcl⟩ := hM.clean p hp 0 le_rfl one_pos
zuebk obtain ⟨u, v⟩ := p
zuebl obtain ⟨w, hw⟩ := filled_sdiff_boundary_nonempty hP
      rw [filled_sdiff_boundary_eq_component hP hw]
zuebm obtain ⟨w1, w2, w3⟩ := ShotList.modelDesc_keep hmwf hm0 hC' hm hA
zuebn obtain ⟨xe, xh⟩ := x
zuebo rcases F₂plus_kind J hS₂.2.1 hf' with ⟨c₀, hc₀, hfc₀⟩ | hkind
zuebp rcases Nat.lt_or_ge p.1 u with hl | hl
zuebq rcases Nat.lt_or_ge v p.2 with hv | hv
zuebr rcases hI.rdisj q p hq hLp hqp with h | h | h | h
zuebs rcases hM.attach_endpoint hopen hA with h | h
zuebt rcases hp with rfl | rfl | rfl
zuebu rcases hx with hx | hx | hx
zuebv rcases lt_or_ge j L.length with hj | hj
zuebw rcases mul_neg_iff.1 hopp with ⟨h1, h2⟩ | ⟨h1, h2⟩
zueby refine Gran.ChordListAt.congr hL₂ fun a h1 h2 => ?_
      rw [hlen₂] at h2
zuebz refine afterFaces_of_arc harc hfe le_rfl ?_
      filter_upwards [WalkAx.eventually_after_start hne'] with s hs
      simp_all
zuecd rintro U hU hUR ⟨hUS, hUne⟩
      rw [mem_singleton_iff] at hUne
zuece rintro _ ⟨l, hl, rfl⟩
      apply toΛ
      rw [hlist]
zuecf rintro c' ⟨a1, a2, a3, a4, a5, a6⟩
zuecg rintro p ⟨hp, -, t, ht0, ht1, hx⟩
zuecj rintro x ⟨c, hc, p, t, hA, rfl⟩
zueck rintro ⟨c, hc, hzc⟩
zuecl rintro ⟨e, he, rfl⟩
zuecm rintro ⟨hy, h1, h2⟩
zuecn rintro ⟨i, hi, hie⟩
zueco rintro ⟨j, hj, hp⟩
zuecp rintro ⟨j, hj, rfl⟩
zuecq rintro ⟨k, hk, hx⟩
zuecr rintro ⟨q, hq, rfl⟩
zuecs rintro ⟨z, hz, rfl⟩
zuect rw [J.left_inter_right hP] at this
      simp_all
zuecu rw [band_sw h1 h2]; decide
zuecv rw [dist_comm, dist_eq_norm, dist_eq_norm]
zuecw rw [endM_param hS hd, endM_pos hS hd]
      unfold endCode
      split_ifs with hk
zuecx rw [fm]
      change c₇.nmem _ < A ∧ _ at this
      exact this
zuecz rw [hE, E_pow]; grind
zuedb rw [hTn, hTdef, transpose_vtx, transpose_vtx, transpose_vtx, det_swap_swap_swap]
      linarith
zuedc rw [hc1]; simp (disch := omega) only [Machine.upd_other]
zuedd rw [hd₄]; simp [regB, regI, upd, hr]
zuedf rw [hm4, hm3, Machine.upd_apply]
zuedg rw [hpos, hp0, Chazelle.Chain.sidePt_zero, hie, C.sideWalk_vtx_tour _ hi]
      rfl
zuedj rw [leafShp_length] at hk
      unfold leafShp
zuedo rw [mEdge_def, left_edge_eq, hoff]
zuedp rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at hy
      grind
zuedq rw [mem_newEx hE h hc hs]
zuedr rw [one_mul]; unfold sidePt sideNext
      exact Chazelle.Chain.offset_lerp_left _ _ _ _ _
zueds rw [q103, m₂] at hprj ⊢
      rw [q104] at hj
zuedt rw [rank_eq_iff mx my] at hxy
zuedx rw [show q + 1 = n by omega, Nat.mod_self]; omega
zuedy rw [sideLeft_edge hne ht]; omega
zuedz rw [this, Set.ncard_empty]; omega
zueea rw [transpose_n, transpose_vtx, transpose_vtx, transpose_vtx, det_swap_swap_swap] at this
      simp_all
zueec rw [v₂] at g'
      exact g' reg hr hch hs σb hσb hg
zueee set K : Set Point := lerp u v '' Icc t₁ t₂ with hK
zueeg set Z := E + b₁ + m p₂ + t + 1 with hZ
zueei set c₆ : Config := { c₅ with nreg := upd c₅.nreg 50032 1 }
zueej set l := A ++ b :: c :: k :: B with hl
zueel simp only [Bool.false_eq_true, ↓reduceIte]
      rcases Nat.eq_zero_or_pos C.topIdx with h0 | h0
zueem simp only [Brute.Bt, Bvt, Bool.or_eq_true, decide_eq_true_eq] at hr ⊢
      grind
zueeo simp only [Machine.upd_apply, h1, h2, h3, h4, ite_false]
zueep simp only [Machine.upd_other _ _ _ h1, Machine.upd_other _ _ _ h2]
zueeq simp only [SymPt.Lt] at hl₁ hl₂
zueer simp only [regB, regI, upd_same, upd_other _ _ _ nE.symm]
zuees simp only [sideCross, Prod.fst_sub, Prod.snd_sub, hx1, hx2]; ring
zueet unfold B19 at hr
      simp only [decide_eq_false_iff_not, not_and, not_lt] at hr
zueeu unfold Chain.sideS
      by_cases hb : C.sideBeta = true
zueev unfold Chain.sideTour
zueew unfold Model.pos
zueey unfold OutL at _hmd
      simp only [setL, okB, okI, regI]
zueez unfold sideLeftOf sideCcw
zuefa unfold view
zuefe all_goals first | (split_ifs <;> first | rfl | omega) | skip
zueff apply C.sideNot_mem_dom_of_abs; right; simp [lerp, slitTop, abs_of_pos hR]
zuefg apply point_ext <;> simp only [lerp_fst, lerp_snd] <;> field_simp <;> ring
zuefh by_cases hh : (M.wa p).2 = (M.wb p).2
zuefi by_cases hq : ∃ i, i < t ∧ q i = x
zuefj by_contra hne; rw [w9, ite_eq_right hne] at hq'; omega
zuefr ext U
      simp only [mem_union, Set.mem_sdiff, mem_singleton_iff, mem_insert_iff]
      constructor
zuefs filter_upwards [hoff] with s hs
      filter_upwards [hs] with δ hδ
zueft first | exact hN _ h | exact hR _ h | exact h
zuegf have h := hF.touches_iff hS hc
      unfold edgeOfIn
      rw [dite_eq_left h]
      grind
zuegg have h' := congrArg Prod.fst h
      simp only [rayPt] at h'
      grind
zuegh have h0 := hIok _ hv; simp only [ChordOK] at h0
zuegi have h0 := hOok _ hv; simp only [ChordOK] at h0
zuego have hKA' := hkey hA'.1 hA'.2.1 hA'.2.2.1
      have hKB' := hkey hB'.1 hB'.2.1 hB'.2.2.1
zuegq have hU := g.U_ge; have hE := g.END_eq; have hLU := g.L_le_U
zuegr have hUaX := hafter Ua hUa hfa
      have hVbY := hbefore Vb hVb hfb
zuegt have harc := arcOf j hj
      rw [hk, hkx] at harc
