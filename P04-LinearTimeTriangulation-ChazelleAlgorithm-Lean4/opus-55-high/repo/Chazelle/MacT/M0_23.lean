module

public import Chazelle.MacT.Base

public section

set_option hygiene false

zg zuegv have hcorr := h.regionCorr
         rw [RegionCorr, h.F_eq, nRegions] at hcorr
zuegw have hin1 := hin.1
      rw [hoF] at hin1
      clear_value d'
      subst hpf
zuegx have hjA' : j < V.A := by rw [hm.A]; omega
zuehd have hp0m : p₀ ∈ ps := by rw [hcase]; simp
zuehe have htop := (top_iff h hch hT hB hI ht).1 htt
zuehg have hw := walk_left hQ D
      rw [← nxt_eq D.isTrap.hi] at hv
zuehh have hw := walk_right hQ D
      rw [← nxt_eq D.isTrap.hj] at hv
zuehm have hτ' := tpos_lt C₂ 0
      set ℓ := 2 * J.m₂ with hℓ_def
zueid obtain ⟨-, -, -, htouch⟩ := h.sides c hc
zueie obtain ⟨U, hU, a, b, hab⟩ := hcov1
zueif obtain ⟨c', k, e, h1, h2⟩ := hh
zueig obtain ⟨c', k, e, hk, hr⟩ := h
zueih obtain ⟨c₃, k₃, e₃, hk₃, v₃⟩ := e₃
zueii obtain ⟨e1, e2⟩ := Prod.mk.inj h
      subst e1; subst e2
zueik obtain ⟨fr2, frr2, hm2, hrm2, ho2⟩ := fb2
zueil obtain ⟨h1, h2, h3, -⟩ := hvalid t ht
zueim obtain ⟨hT, -, hin⟩ := Merge.hit_of_freeAt C ha hσ hf
zuein obtain ⟨hT, hTD, hTdom⟩ := Merge.hit_of_freeAt C ha hσ hfree
zueio obtain ⟨hW, hAl, hR, hB, -⟩ := hI
zueip obtain ⟨hX, hY, -, -⟩ := hI.sides cc hc
zueiq obtain ⟨hkp, hmem, -, -⟩ := stp_pre_frame hW hR
zueir obtain ⟨hlt, -, -⟩ := stp_next_key S.E S.L S.hI S.hd
zueis obtain ⟨hlt, hpw, -⟩ := stp_next_key S.E S.L S.hI S.hd
zueit obtain ⟨hn1, hn2⟩ := hc1 hx
      by_cases hu : NearU J
zueiu obtain ⟨hp, ht0, ht1, hmem, -⟩ := hA
zueiv obtain ⟨hp, ht0, ht1, hpt, hsec⟩ := harr
zueix obtain ⟨hsq', hjl', hwv', hhv'⟩ := h.endPos_mem hq0A d
zueiy obtain ⟨hvalid, hcount, hunion, hdisj, hvert⟩ := hT
zueiz obtain ⟨hw', ht', henc', hr', hm'⟩ := I'
zueja obtain ⟨k5, k7, k3, k1⟩ := fx c hI
zuejb obtain ⟨or₂, -, om₂, -, -⟩ := o₂
zuejd obtain ⟨pos, γ, hpos, hgap, hst⟩ := hI.st
zueje obtain ⟨q, s, h1, h2⟩ := hEa.1; grind
zuejf obtain ⟨q, s, h1, h2⟩ := hEb.1; grind
zuejg obtain ⟨q00, q02, qm, qA, q08⟩ := q
zueji obtain ⟨reg, -, -, harc⟩ := isArc_sj hN hp
zuejj obtain ⟨rfl, rfl⟩ := sideKey_inj hA'.2.1 hA'.2.2.1 hA.2.1 hA.2.2.1 hk'.symm
      grind
zuejk obtain ⟨s, h1, h2⟩ := (hev.and hrayR).exists
zuejl obtain ⟨sh, cu, κs, hsh, hcu⟩ := hSC
zuejm obtain ⟨y₀, a, b, hab, rfl⟩ := hc
zuejp obtain ⟨δ, h1, h2⟩ := (h.and h').exists
zuejq rcases hI with ⟨h1, h2⟩ | ⟨h1, h2⟩
zuejr rcases hL' with rfl | ⟨τ', rfl, hτ0, hon⟩
zuejs rcases hadj with ⟨r, harc⟩ | ⟨l, harc⟩
zuejt rcases hb with ⟨-, rfl⟩ | ⟨-, rfl⟩
zueju rcases hcase with ⟨rfl, h⟩ | ⟨rfl, h⟩
zuejv rcases hdir with ⟨h1, h2⟩ | ⟨h1, h2⟩
zuejw rcases hfin with ⟨rfl, _⟩ | ⟨rfl, _⟩
zuejx rcases hmem c hc with hcS | ⟨R, hR, hcR⟩
zuejy rcases hmid with ⟨h1, h2⟩ | ⟨h1, h2⟩
zuejz rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
zuekn rintro (⟨a, b⟩ | ⟨a, b⟩)
zueko rintro (⟨t, ht, rfl⟩ | rfl | rfl)
zuekp rintro d₁ hI₁ hA₁ hA₁' ⟨s1, s2, s3, s4⟩
zuekq rintro ⟨_, ⟨t, ht, rfl⟩, hp⟩
zuekr rintro ⟨c, hc, p', t', hA', hk⟩
zueks rintro ⟨hp, hc, t, ht0, ht1, hin⟩
zueku rintro ⟨x, hx, hlt⟩
      rw [hce] at hx
zuekv rintro ⟨y, hy, hyz⟩
      by_cases hyz' : y < z
zuekw rw [C.sideWalk_vtx_tour β hi.le]; unfold sideTour; rw [k1]
zuekx rw [Geometry.det_lerp, Geometry.det_self_outer, det_cyclic]
      nlinarith [mul_pos hs01.1 hpos]
zueky rw [Geometry.point_ext_iff]; simp only [lerp_fst, lerp_snd]; grind
zuekz rw [Geometry.point_ext_iff]; simp only [rayPt_fst, rayPt_snd]; grind
zuela rw [List.getD_append _ _ _ _ h]; exact h₁ i h
zuelb rw [List.length_append] at hi
      rcases Nat.lt_or_ge i L.length with h | h
zuelc rw [Nat.add_mul, Nat.one_mul, ← hlo, ← hhi] at this
zuelf rw [WalkEmbed.mod_succ_mod, WalkEmbed.mod_succ_mod, hA d hd.le, hA _ hd]
zuelh rw [bary₁_combination h hw, bary₂_combination h hw, bary₃_combination h hw]
zuelj rw [count_eq_zero, mem_map]
      rintro ⟨f, hf, rfl⟩
zuelk rw [e1] at hNW hroom
      rw [e2] at hdeg hroom
zuell rw [eP3] at h
      rcases Nat.lt_or_ge i' i with h' | h'
zuelm rw [ec]; by_contra hc; push Not at hc; nlinarith
zuels rw [hN1] at hj
      rw [w1, w7 j hj]
zuelv rw [hc₁]; simp only [regB, regI]; simp_all
zuema rw [hjE] at hbest
      rw [i28, Nat.sub_zero] at hkL
zuemb rw [hlen'] at hq
      rcases Nat.lt_or_ge q np with hq1 | hq1
zuemd rw [hlv, g6] at b₃
      rw [g7] at hk₃
zuemf rw [hm2', fv_store heR htR, fv_store heR htR]; simp
zuemg rw [hnW] at hv
      rcases Nat.lt_or_ge _ _ with h2 | h2
zuemr rw [t8, t9, t10]; exact hw.2 ho reg hregs
zuemt rw [v₄, j3]; simp only [hostEdgeIdx]; grind
zuemu rw [← e] at s2
      rw [hcab] at s1 s2
zuemv rw [← hxv]; exact (T.isAnc_parent_self x).trans T h
zuemw set A := c.nreg 50103 with hAdef
      set n := c.nreg 50104 with hndef
zuemy set T := transpose P with hTdef
      have hT : T.Simple := transpose_simple hP
zuena set a := Q.vtx k with ha
      set q := Q.vtx _ with hq
zuenb set a := c.nreg 30000 with ha
      set b := c.nreg 30001 with hb
zuene set t := c.nreg lsI with htdef
      set d := c.nreg qD with hddef
zueng set y := ((Qof P).vtx V.hz).2 with hydef
zuenh set ρ : ℕ → ℕ := fun q => rg _ with hρ
zueni simp [SignTest, Src.pt, SymPt.eval, hq, hbq, hi]
zuenj simp [wposOf, e0, d0, BuildRegions.crec, CRec.lpos, recOf]
zuenk simp [wposOf, e1, d1, BuildRegions.crec, CRec.rpos, recOf]
zuenl simp only [Enc] at henc
      simp only [SymPt.Lt] at hs
zuenm simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
      omega
zuenn simp only [List.mem_cons, hnc _ _ hz.le, or_false]; omega
zueno simp only [decide_eq_true_eq] at hr; simp [BCa, hr]
zuenp simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hm hmin
zuenq simp only [hp, hq, ite_true, ite_false]
      split_ifs <;> rfl
zuenr simp only [rayPt, neg_one_mul, neg_sub, add_sub_cancel] at this
      omega
zuens simp only [sub_self, abs_zero, sub_sub_cancel_left, abs_neg, abs_of_pos hε0]
zuent suffices hVV : V = V'' by rw [hVV]; exact hfV''
zuenu unfold Model.Faces
      filter_upwards [Ioo_mem_nhdsGT hpos] with δ hδ
      have hδ0 := hδ.1
zuenw unfold sideDot; simp only [Prod.fst_sub, Prod.snd_sub, lerp_fst, lerp_snd]
zuenx unfold sideDot; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
zueny unfold wedgeTest
      rw [e1, e2, mul_zero]
      split_ifs with h h'
zuenz apply point_ext <;> simp [lerp]
zueoa apply point_ext <;> simp [offset, nrm, lerp, hy]
zueob apply point_ext <;> simp [rayPt]
zueoc by_cases hL2 : 0 < c.rreg 116
zueod by_cases hVNT : VNotTop J
zueoe by_cases hne : l = []
zueof by_cases hp : σ.pend e = 1
zueoi by_cases hδ : lδ J = 0
zueop constructor <;> nlinarith
zueos exact (hUall x hx).trans (hUall y hy).symm
zueou exact Or.inl h
zueow exact hB1 c hc htc hct h2
zueox exact hI.good _ hcand.2.1 hcand.2.2
zuepb ext v
zuepd filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
zuepu have e₃ := Exec.subN (P := P) w₂ 50089 50058 50059
zuepx have g₁ := f₁.1
zuepy have g₃ := f₃.1
zuepz have h := modelMir_interior hQ
zueqa have h1 := C.one_le
zueqd have h23 := hI.h23
zueqf have h3 : 3 ≤ m := by have := hM.1.1; omega
zueqh have hAW := hw.1 ALLOC
zueqi have hBW : E.B₂ ≤ E.W := by have := hE.hBW; omega
zueqk have hK₁ := hK₀.fix hI₁
zueqm have hN := E.hNF₂
zueqn have hNF := E.hNF₂
zueqo have hQ := hl.simple
zueqp have hQn := S.hQn
zueqq have hR := C.top_snd_lt_radius
zueqr have hT := J.whole.topIdx_le
zueqs have hU := g.U_ge
zueqv have haD : a ∉ J.right.dom := fun hd => J.right.not_mem_set_of_mem_dom hd haR
zueqx have hdet := det_ne_zero_of_simple_three P hP h3
zuerf have hlog := hA.hlog
zueri have hm := J.right.one_le
zuerk have hm2 := S.hm2'
zuerp have hn := simple_three_le hQ
zuerq have hn := simple_three_le hW
zueru have hn3 := simple_three_le hQ
zuerw have hnα := Stretch.nα Cα
zuerx have hn₁ := cm_n J.left
zuerz have hp := hA.1
zuesa have hpos := chordParam_pos hP hi h
zuesd have hres := hpost H C hC₁
zuese have hrl := hr
zuesf have hs' := o3 hlt
zuesg have hs0 := hs
zuesh have hsys := h.walk.sys _ h.adm h.finite
zuesj have ht2 := D.top_snd hP
zuesl have hv := hit i h1 h2
zuesm have hv := hs.hv
zuesn have hw := h.wb
zueso have hw6 := e6.wb_right
zuesp have hy := h.key_ne_of_not_cut hcut
zuesr have hσ' : V.σb = 1 := by have := hv.σb_le; omega
zuesu have m₁ := f₁.2.2.1
zuesv have o113 := ((o110.trans o₁₁).trans o₁₂).trans o₁₃
zuesx intro P W c hw pre hroom
zuesz intro h; have := hR.q_inj i hin 0 hR.n_pos h; omega
zueta intro h; subst h; tauto
zuetb intro hx
zuetc intro p t hp ht0 ht1 hz
zuetd intro q h1 h2 hq
zuete intro r h1 h2 h3
zuetf intro r h1 h2 h3 h4 h5
zuetg intro s hs0 hs1
zueth intro x hx hx'
zueti intro x hx hxF hxs
      rw [sideLeftOf_iff, add_sub_cancel_left] at hxs
zuetj intro x hx hxb
      rcases hSr x hx hxb with h | h
zuetl intro x hx1 hx2
zuetm intro x hx; split_ifs with h
zuetn left; right; omega
zueto obtain ⟨-, hWb, -, -⟩ := FactsInterior.interiorWalk_spec hQ
zuetp obtain ⟨a1, a2, a3⟩ := convL_val hst hP hcls
zuetq obtain ⟨a1, a2, a3⟩ := convR_val hst hP hcls
zuetr obtain ⟨a1, a2, a3⟩ := hF.chOf e' he'
      grind
zuetx obtain ⟨f1, t8, t9, t10⟩ := h1 ho
zuety obtain ⟨h0, h1, h2⟩ := h i hi
      grind
zuetz obtain ⟨h0, h1, h2⟩ := vtx_earArc P i hi
zueua obtain ⟨hWs, hWb, hWf, hWo⟩ := FactsInterior.interiorWalk_spec X.hQ
zueub obtain ⟨hc1, hc2⟩ := hP.cap
      by_cases hx : SharedExtremum J
zueuc obtain ⟨hf, hfo⟩ := farW_spec hQ hDH li hi hdir
zueud obtain ⟨hf, hfo⟩ := farW_spec hQ hDH li hin hdir
zueue obtain ⟨hi', ht⟩ := (hmem i).1 hi
zueuf obtain ⟨hs, hb, hf, ho⟩ := FactsInterior.interiorWalk_spec hQ
zueug obtain ⟨hup, hdn, hA, hB⟩ := h.sides_rec hi
zueui obtain ⟨hzpos, hx, hp0, hp1⟩ := tree_pos h
zueuj obtain ⟨i1, i2, -⟩ := orig_attach hP hN hD
zueuk obtain ⟨k', e', hk'⟩ := ifNe1_run hone1 hX1' eU
zueun obtain ⟨r, hr, hball⟩ := exists_ball_disjoint_edges P _ hother
zueuo obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.1 hR w hwR
zueuq obtain ⟨r, hr, hloc⟩ := vertex_local hW hL hp
zueut obtain ⟨s, hs0, hs1, he⟩ := Geometry.mem_segment_iff_lerp.1 hmem
zueuu obtain ⟨t, ht0, ht1, rfl⟩ := mem_segment_iff_lerp.1 hq
zueuv obtain ⟨t, ht0, ht1, rfl⟩ := mem_segment_iff_lerp.1 hx
zueuw obtain ⟨u, hu0, hu1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hx
zueux obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hRo z hzR
zueuy push Not at hc h1
      obtain ⟨hc1, hc2⟩ := hc
zueuz rcases List.mem_cons.1 hp with rfl | hp
zueva rcases Nat.eq_zero_or_pos g with h0 | h0
zuevb rcases Nat.eq_zero_or_pos g with rfl | hg
zuevc rcases Nat.eq_zero_or_pos k with rfl | hk0
zuevd rcases Nat.eq_zero_or_pos p with h0 | h0
zueve rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hi with rfl | rfl
zuevf rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hji
zuevh rcases eq_or_lt_of_le hs with rfl | hs
zuevj rcases h with h | h <;> rw [h] at hy
zuevk rcases he with rfl | rfl <;> rcases he' with rfl | rfl
zuevl rcases hl1 hc with h | h
zuevm rcases lt_or_gt_of_ne hA0 with ha | ha
zuevn rcases lt_or_gt_of_ne hne with hlt | hgt
zuevo rcases lt_or_gt_of_ne hpq with hlt | hlt
zuevp rcases lt_or_gt_of_ne hx₁ with h₁ | h₁
zuevq rcases mem_addL h with h | h
zuevr rcases ylexLE_zero P hM hi with h | ⟨h1, h2⟩
zuevt refine BitIs.of_bf v₇ ?_
      simp only [BF.eval, Bool.and_eq_true, Bool.not_eq_true']
zuevu refine h.mono le_rfl ?_
zuevv refine spec_ifLtN_false c1 ?_
zuewc right; grind
zuewd rintro _ ⟨D, rfl, hD⟩ r hr c₁ c₂
zuewf rintro c' ⟨w1, w2⟩
zuewg rintro d ⟨hd, rfl⟩
zuewh rintro p (hp | hp)
zuewi rintro x y ⟨e, he, rfl, rfl⟩ hx
zuewj rintro ⟨r, hr, rfl⟩; exact hRC.1 r hr
zuewk rw [C.edgeIdx_succ] at this
      tauto
zuewl rw [Chain.sideIdx_eq]
zuewm rw [DownDrv.buildNF_arcs hK, List.length_map]
zuewn rw [Finset.range_add_one, Finset.filter_insert]
      grind
zuewo rw [Function.update_self]
zuewp rw [Geometry.mem_segment_iff_lerp]
zuewq rw [Geometry.point_ext_iff]; simp only [rayPt_fst, rayPt_snd]
      grind
zuewr rw [I₄.pw, s52, g3, ← hpw]; omega
zuews rw [List.getD_eq_getElem _ _ hi]
zuewt rw [List.toFinset_card_of_nodup hnd, List.length_map]
zuewu rw [Nat.mul_succ]
      omega
zuewv rw [Nat.zero_add] at cnt₂
      simp only [Nat.add_zero] at pr₂
zueww rw [Prod.dist_eq]; simp [rayPt, abs_of_pos hs]
      grind
zuewx rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]
zuewy rw [Set.not_nonempty_iff_eq_empty] at hne
      have h1 := arcs_le_one_of_empty hN hGM hne
zuewz rw [beta_eq] at this
      linarith
zuexc rw [chordSet_eq_image hP hi h]
zuexd rw [cr_old h hch hT hB hI hrp]; exact a2
zuexe rw [cwa_tour hi.le]; unfold vPt; rw [e1]
zuexf rw [cwb_tour hi]; unfold vPt; rw [e2]
zuexg rw [d1, d4, d6, d2]; exact h
zuexh rw [e, hq0]
      positivity
zuexi rw [e3, e2]
      simp only [BuildRegions.crec, hg]
zuexj rw [e]; rcases hσ with rfl | rfl <;> linarith
zuexk rw [eventually_all_finite hI]
zuexl rw [e₃]; simp [regB, regI, upd]
zuexo rw [gc_old h hch hT hB hI hrp]; exact a3
zuexp rw [h40003]; exact hNF
zuexq rw [h5v, hC5.rN, hI4 d htest] at hvis
      grind
zuexr rw [hA, hB]
      rcases lt_or_gt_of_ne hA0 with h1 | h1
zuext rw [hQ]
zuexu rw [hQn] at hps hpe
zuexv rw [hX]
zuexw rw [hcost] at hroom ⊢
zuexx rw [hkdef] at ht; unfold kOf at ht; grind
zuexz rw [hme]; unfold recRMem
zueya rw [hm₆, v7, ← hseg, SortL.seg_getD t ht]
zueyb rw [hn] at hp ⊢
zueyc rw [ho']
zueyd rw [hoA]
zueye rw [hoff] at h0 hL
zueyf rw [hpar]
zueyh rw [hqdef]; unfold adjN
zueyj rw [hsub, Finset.mem_inter, mem_sideSet h hch hT hB hI]
zueyk rw [hv]
zueyl rw [h₅]
zueym rw [interior_filled h.simple₁] at hp
zueyn rw [ite_eq_left h]
zueyo rw [ite_eq_left hk] at hr
zueys rw [ite_eq_right hex, ite_eq_right]
zueyw rw [key]
zueyx rw [key]; simp only [add_sub_cancel_right]; exact ht'.2.1
zueyy rw [lerp_one] at e1
      rw [lerp_zero] at e2
      grind
zueyz rw [mem_halfDisk_iff]
zuezc rw [q00, qm]; exact (hI.modelDesc hE).1
zueze rw [rayPt_snd] at this
      linarith
zuezf rw [r₄]; simp only [upd, ite_eq_right h15]
zuezg rw [shear_n] at hi hj
zuezh rw [show r / 10000 = 1 by omega]; decide
zuezi rw [show r / 10000 = 14 by omega]; decide
zuezj rw [show r / 10000 = 17 by omega]; decide
zuezk rw [show xAt sL c = xAt sR c by linarith]
zuezl rw [sortPair_eq_iff (allDiagonals_lt hP he).2.2] at hed
      grind
zuezm rw [stopSet_eq]
zuezn rw [tpos_second J]
zuezo rw [w4] at hx; rw [w2, w3]
zuezp rw [w4]; rw [w2, w3] at hto
zuezq rw [← Nat.mul_succ]; grind
zuezr rw [← Set.ncard_coe_finset]
zuezs rw [← h, upd_eq_self]
zuezt rw [← h2, t0, add_zero, offU u hu]
zuezu rw [← h]
zuezv rw [← h]; exact (C.sideVertex_succ_ne hP _).symm
zuezw rw [← hj] at hg
zuezx rw [← hm', ← hm, ← Function.iterate_add_apply]; simp_all
zuezy rw [← hpos1]
zuezz rw [← hpt]
zufaa rw [← hv]; rfl
zufab rw [← hv]; tauto
zufac rw [← pow_succ']; grind
zufag set N := sideNext W k
      set Pp := sidePrev W k 0
zufai set e := c₀.nreg 50201 with he_def
zufak set p := topGrade n with hp
zufam set σ := dirOf _ with hσ
zufan simp [Polygon.n]
zufao simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hd
zufap simp only [BcutG, BoffG, Bool.or_eq_true, beq_iff_eq] at hr
zufaq simp only [Bend, ALLOC, Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
zufar simp only [Bool.or_eq_false_iff] at hr
zufas simp only [Config.nreg_mk, upd_same]
zufat simp only [Finset.mem_singleton] at hb
      unfold bandOf bSign at hb
      grind
zufau simp only [Geometry.lerp_fst]; grind
zufav simp only [Geometry.lerp_snd] at hy
zufaw simp only [LblR, kN, kL, sw] at h
zufax simp only [List.getD_cons_succ]
zufay simp only [List.getElem_map, List.getElem_range]
zufaz simp only [List.length_append]; omega
zufba simp only [Nat.add_zero] at e0
zufbb simp only [Option.some.injEq] at h
zufbc simp only [S, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
zufbd simp only [Sweep.nbrRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
zufbe simp only [SymSrc.Holds] at hp
zufbf simp only [add_sub_cancel_left]
zufbg simp only [add_zero] at this
zufbh simp only [addrL, List.mem_cons, List.not_mem_nil, or_false] at hi
zufbi simp only [arcL2, List.mem_cons, List.not_mem_nil, or_false] at hi
zufbj simp only [bRead, List.mem_cons, List.not_mem_nil, or_false] at hi
zufbk simp only [c0, Machine.upd_apply]
zufbl simp only [eval]
zufbm simp only [hRc.rQ, hRc.rPre, hRc.rSlot, r1, Machine.upd_apply]
zufbn simp only [hc₁]
zufbo simp only [hvChainL, List.mem_cons, List.not_mem_nil, or_false] at hi
zufbp simp only [ite_true] at hr
zufbq simp only [lerp_fst]; grind
zufbr simp only [mem_ofPred_eq, one_mul]
zufbs simp only [natOnly, Bool.and_eq_true] at hs; exact ih hs.1
zufbt simp only [natOnly, Bool.and_eq_true] at hs; exact ih hs.2
zufbu simp only [ne_eq, Nat.add_one_ne_zero, not_false_eq_true, true_and, Nat.add_sub_cancel]
zufbv simp only [pEdge]
zufbw simp only [rayPt]; grind
zufbx simp only [rayPt_fst] at hx
zufby simp only [rd, bandReg, bBuild, Nat.reduceMul, Nat.reduceAdd]
zufbz simp only [rd_sw] at od
zufca simp only [sideCross, Chazelle.Chain.sideDot, rayPt, Prod.fst_sub, Prod.snd_sub]
zufcb simp only [upd]; split_ifs <;> first | rfl | omega
zufcc simp only [upd_eq, true_iff]
zufce simp only [wr, Bool.and_eq_true] at hs; exact ih hs.1
zufcf simp only [wr, Bool.and_eq_true] at hs; exact ih hs.2
zufcg simp only [wr2, Bool.and_eq_true] at hs; exact ih hs.1
zufch simp only [wr2, Bool.and_eq_true] at hs; exact ih hs.2
zufci simp only [wrM, Bool.and_eq_true] at hs; exact ih hs.1
zufcj simp only [wrM, Bool.and_eq_true] at hs; exact ih hs.2
zufck simp only [wrM2, Bool.and_eq_true] at hs; exact ih hs.1
zufcl simp only [wrM2, Bool.and_eq_true] at hs; exact ih hs.2
zufcm simp only [wrR, Bool.and_eq_true] at hs; exact ih hs.1
zufcn simp only [wrR, Bool.and_eq_true] at hs; exact ih hs.2
zufco simp only [wrRS, Bool.and_eq_true] at hs; exact ih hs.1
zufcp simp only [wrRS, Bool.and_eq_true] at hs; exact ih hs.2
zufcq simp only [wrS, Bool.and_eq_true] at hs; exact ih hs.1
zufcr simp only [wrS, Bool.and_eq_true] at hs; exact ih hs.2
zufcs simp only [← hAdef, ← hKdef] at ht hr ⊢
zufct simp only at h1 h2
zufcu simp only at hch hzc hc ⊢
zufcx simp only; unfold PLRG at hr
zufcy split_ifs <;> first | omega | rfl
zufcz subst h1; subst h2
zufda subst hne; simp [mpass_nil]
zufdb unfold CRec.toSet recOf CRec.lpos CRec.rpos
zufdd unfold FixP FixB at hq; simp only [decide_eq_false_iff_not]; omega
zufde unfold Model.param
zufdf unfold OutB bandOf at h1; omega
zufdg unfold envR at h
zufdh unfold farEdge; simp_all
zufdi unfold interiorWalk; split_ifs
zufdj unfold keyCeil; grind
zufdk unfold oppN; grind
zufdl unfold posOf; simp only [ite_true, posK, ite_eq_left he]
zufdm unfold recAt; simp_all
zufdn unfold sideCcw sideCross at hX
zufdo unfold sideCross sideDot; simp only [Prod.fst_sub, Prod.snd_sub]; grind
zufdp unfold sideDot sideCross; simp only [Prod.fst_sub, Prod.snd_sub]; ring
zufdq unfold sideInArc
zufdr unfold sidePt; simp
zufds unfold tK sideE; grind
zufdz apply C.sideNot_mem_dom_of_abs; left; simp [lerp, abs_of_pos hR]
zufea by_cases h1 : a = X + 2 * i + 1
zufek exact ((genuine_iff C hzt hσ).1 hg).2
zufel exact (rot hka'0 hka'n hka0 hkan hu0 hun).2 this
zufem exact (rot hka0 hkan hka'0 hka'n hu0 hun).2 this
zufep exact this
zufeq exfalso; rw [← hty] at h1 h2; nlinarith
zufer ext w
      simp only [mem_image, mem_ofPred_eq, Prod.exists]
      constructor
zufes filter_upwards [eventually_before_end hVne, Ioo_mem_nhdsGT one_pos] with s h1 h2
zufet have : Finite _ := (hF.regionsIn_finite hD hne hS).to_subtype
zufev have a := h ▸ hu0
      have b := h ▸ huL
zufey have b1 := hlow.2.2 _ hql
      have b2 := hlow.2.2 _ hqr
zuffe have e2 := Exec.copyN (P := P) e1.wb_right 110106 110101
zuffh have ea' := Exec.copyN (P := P) w₃ 140225 140353
zuffi have ec := Exec.copyN (P := P) hw3 130535 130001
zuffj have ew := ea.wb_right
      clear hroom hγW hm hA h09 ea ra
zuffk have e₃ := Exec.copyN (P := P) e₂.wb_right 150048 150089
zuffl have e₄ := Exec.copyN (P := P) w₃ 150040 150085
zuffm have e₇ := Exec.loadN (P := P) e₆.wb_right 50210 50101
zuffs have h1 := hsize r hr
      have h2 := hm r hr
zufft have h3 := Set.ncard_inter_add_ncard_sdiff_eq_ncard S {p | M.counted p} hSf
zuffz have hJ₄ := hJs c c₄ h.hJ hsl.1 hsl.2.1 hsl.2.2.1 hsl.2.2.2.1 hsl.2.2.2.2
zufga have hP : C0.P.Simple := (shearInvariance _ P).1 hG.1
zufgd have hW := walkAx_of_goodModel hM
      have hsys := hW.sys F hF.2.1 hF.1
zufgo have hdisj := hG.disj
      rw [List.map_cons, List.pairwise_cons] at hdisj
zufgu have hl := b₁.2.1 (by have := b₁.1; omega)
zufgv have hlay := L.lay1
      have hlay2 := L.lay2
      have hlay4 := L.lay4
zufgx have hlt := b1.2.1 (by have := b1.1; omega)
zufgz have hodd' := hodd
      rw [o87, o88] at hodd'
zufhc have hs := DrvD.arc_s B.hK hj
      have he := DrvD.arc_e B.hK hj
zufhn have kS := key_range hs hs1
      have kE := key_range he he1
zufho have l1 := S.L.lay1
      have l2 := S.L.lay2
      have l4 := S.L.lay4
zufht have t1 := tpos_lt J.right 0
      have t2 := tpos_lt J.whole J.m₁
zufhw intro c e' hce
      simp only [dir, decide_eq_true_eq]
      constructor
zufhx intro c hc c' hc' ⟨h1, h2, h3⟩
zufhy intro c hw ⟨j1, j2, j3, j4⟩
zufhz intro he
zufia intro hlt
zufic left; simp [dBands, bDecomp, bandOf]; omega
zufid left; simp [dBands, bOPrep, bandOf]; omega
zufie left; simp [dBands, bSort, bandOf]; omega
zufif obtain ⟨-, -, -, hK4⟩ := hK
zufig obtain ⟨-, -, -, hRg⟩ := hregs
zufih obtain ⟨-, -, A, hBA⟩ := hB
zufii obtain ⟨-, -, hak⟩ := WalkAx.arc_cuts hne harc
zufij obtain ⟨-, -, hkr⟩ := WalkAx.arc_cuts hne harcU
zufik obtain ⟨-, -, hlk⟩ := WalkAx.arc_cuts hne harcV
zufil obtain ⟨-, a1, a2⟩ := tour_twin C hi2'
zufim obtain ⟨D, heq, hS, hc'⟩ := hst
zufin obtain ⟨a', b', harc, hsub⟩ := hA
zufio obtain ⟨a, b⟩ := inArcIdx_spec C Q N hin
zufip obtain ⟨a0, a1, a2, a3⟩ := v₅
zufiq obtain ⟨a1, a2, a3, a4⟩ := ha
zufir obtain ⟨b0, b1, b2⟩ := hlist i hi
zufis obtain ⟨c'', hc'', hne'', hA''⟩ := htie₂
zufit obtain ⟨c', k, ex, q⟩ := h
zufiu obtain ⟨c, hc, hA⟩ := attach_of_cut hM hk
zufiv obtain ⟨c1, c2, c3, -⟩ := hc
zufiw obtain ⟨c1, c2, c3⟩ := hch k hk
zufix obtain ⟨d1, d2, d3, d4⟩ := dr_m1
zufiy obtain ⟨e', he', hne, hA'⟩ := htie
zufiz obtain ⟨fr, hF, hiff, hmin⟩ := hS
zufja obtain ⟨g0, g1, g2, g3⟩ := e1
zufjc obtain ⟨h1, h2, h3⟩ := h i hi
zufjd obtain ⟨hA1, hA2⟩ := C.sideWalk_box_pt β hA hta hta1
zufje obtain ⟨hC', hwf'⟩ := chain_keep hwf hC hI.hm hI.hA
zufjf obtain ⟨hI, h40, h11, h12⟩ := hB
zufjg obtain ⟨hI0, hht, _, hcur⟩ := hI
zufjh obtain ⟨hRC, -, -, -⟩ := hregs
zufji obtain ⟨hRC, -, -, hRO⟩ := hregs
zufjj obtain ⟨hXe, -, -⟩ := seg_pt hne hX
zufjk obtain ⟨ha, hA'⟩ := aftArc_spec C Q N hex
zufjl obtain ⟨ha, hb, hab⟩ := WalkAx.arc_cuts hne h
zufjm obtain ⟨ha, hb, hab⟩ := WalkAx.arc_cuts hne' h
zufjn obtain ⟨haR', hav', hat'⟩ := S.hval t' ht'
zufjo obtain ⟨hb, hB'⟩ := befArc_spec C Q N e2
zufjp obtain ⟨hb, hB⟩ := befArc_spec C Q N e2
zufjq obtain ⟨hca, hcb, hab⟩ := WalkAx.arc_cuts hne harc
zufjr obtain ⟨hcnt, hlen, hp0, hp1⟩ := pc₁
zufjs obtain ⟨hcs, hce, -⟩ := WalkAx.arc_cuts hne harc
zufjt obtain ⟨hcuta, hcutb, hab⟩ := arc_cuts hne harc
zufju obtain ⟨hk2, hb, hw, -⟩ := hok
zufjv obtain ⟨hm, hst⟩ := stop_mem hP hN hD.ok hD.free
zufjw obtain ⟨hnf, hdeg, hgr, -⟩ := hN
zufjx obtain ⟨hp, hq⟩ := param_pos_of_wab ha hb Q h
zufjy obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
zufjz obtain ⟨hreg, hAc, A, hB⟩ := hInv
zufka obtain ⟨htf0, hdL⟩ := hsplit
      subst htf0
      subst hdL
zufkb obtain ⟨hy1, hy2⟩ := heights_eq_of_region_eq hP D D' h
zufkc obtain ⟨i, hi, rfl⟩ := seq_surj h hj
zufkd obtain ⟨j, hj, rfl⟩ := vert_eq_vertex hv hvR
zufke obtain ⟨j0, j1, j2, j3⟩ := hJ
zufkf obtain ⟨k, hk, e⟩ := hvert i hi
zufkg obtain ⟨k, hk, hks⟩ := chordUnion_snd hc
      grind
zufkh obtain ⟨k0, k1, k2, k3⟩ := f1
zufki obtain ⟨l1, l2, l3⟩ := hR i ht
zufkj obtain ⟨m1, m2, -⟩ := hls i hi
zufkk obtain ⟨m1, m2, m3⟩ := hmono i hi
zufkl obtain ⟨q, hq, hqi⟩ := NFLoc.seq_surj hN hi
zufkm obtain ⟨r, hr, hrj⟩ := NFLoc.seq_surj hN hj
zufkn obtain ⟨r, hr, rfl⟩ := hC.2.2 U hU
zufko obtain ⟨r, hr, rfl⟩ := hRC.2.2 U hU
zufkr obtain ⟨s, hs0, hs1, rfl⟩ := hp
zufks obtain ⟨s, hs0, hs1, rfl⟩ := hx
zufkt obtain ⟨t, h0, h1, rfl⟩ := hX
zufku obtain ⟨t, ht0, ht1, hzt⟩ := hmem
zufkv obtain ⟨t, ht0, ht1, rfl⟩ := hp
zufkw obtain ⟨t, ht0, ht1, rfl⟩ := hz
zufkx obtain ⟨u, -, -, rfl⟩ := hx
zufky obtain ⟨v, hv, hvy, hvx⟩ := h.bot_vertex
zufkz obtain ⟨v, hv, hvy, hvx⟩ := h.top_vertex
zufla obtain ⟨v0, v1, v2, v3⟩ := v₃
zuflb obtain ⟨wl, wr', ww, hreg⟩ := hwf
zuflc obtain ⟨z₀, hz₀⟩ := (hF.chord_inter_nonempty_isPreconnected hc).1
zufld obtain ⟨δ', hδ', hthick⟩ := hKc.exists_thickening_subset_open hOo hKO
zufle obtain ⟨σ, -, -, rfl⟩ := hsh
zuflf rcases (hiffE R hR).1 h with rfl | rfl
zuflg rcases (hiffW R hR).1 h with rfl | rfl
zuflh rcases (htouche U hU).1 ht₀ with h | h
zufli rcases (htouchw U hU).1 ht₀ with h | h
zuflj rcases hL' with rfl | ⟨τ, rfl, -⟩
zuflk rcases hNx with hNu | hNw | ⟨hNs, hvT⟩
zufll rcases hS : S with _ | ⟨f, v⟩
zuflm rcases hVΛ with ⟨l, hl, hlV⟩ | hg
zufln rcases hpartner with ⟨c', hc', hfc'⟩ | hsh
zuflo rcases hr with ⟨h, -, -⟩ | h
zufls refine csSup_le' ?_
      rintro w ⟨ab, hab, rfl⟩
zuflt refine hsort.imp_of_mem fun {a b} ha hb hab => ?_
zuflu refine this.mono fun δ' h' => ?_
      rw [offset_mid_ab hy]
zuflz rintro (⟨hU, hUR⟩ | rfl | rfl)
zufma rintro _ ⟨D, rfl, -⟩
      exact D.region_mem_regions hP
zufmb rintro c₁ hI₁ - - ⟨a1, a2, a3⟩
zufmc rintro c₄ hI₄ - - ⟨v4, k4, m4⟩
zufmd rintro v hv hiff c' ⟨a1, a2, a3⟩
zufme rintro x y ⟨k, hk, rfl, rfl⟩
zufmg rintro ⟨i, a, b, c, d⟩
zufmh rintro ⟨s, ⟨hs0, hs1⟩, rfl⟩
zufmj rw [C.head x' hx'0, C.isDesc_parent_iff hx'g, C.parent_of_ne hx'0]
zufml rw [Function.update_of_ne h1]
      by_cases h0 : j = st.nd0 c
zufmm rw [Function.update_of_ne hr]
      by_cases hr' : r = u i
zufmp rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at h; omega
zufmq rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this; omega
zufms rw [c4J]; have := hb1 _ hj1; omega
zufmt rw [closure_Ioo (hT.bot_lt.trans hT.lt_top).ne] at hcl
      grind
zufnb rw [hC.bPrv, hC.bNxt, hj, ep, en]
zufnh rw [hW, C.sideWalk_vtx_tour _ cv.1.1, Chain.sideTour, cv.1.2]
zufni rw [hW, C.sideWalk_vtx_tour _ cv.2.1, Chain.sideTour, cv.2.2]
zufnk rw [hbot] at h1
      rw [htop] at h2
zufnl rw [hc₆]; show c₅.nreg ALLOC ≤ _; omega
zufno rw [hp1, ht1, Chazelle.Chain.sidePt_zero, Chazelle.Chain.sidePt_zero, hvtx]
zufnp rw [hpD]; congr 1; unfold gW; omega
zufnr rw [hμ] at hx ⊢; exact hSF.upT_lt x hx
zufns rw [ite_eq_left hsj]
      rw [ite_eq_left hsj] at hcm
zufnt rw [ite_eq_left hup]; simp [Function.update_apply, hup]
zufnx rw [leftEnd_fst] at h1
      rw [rightEnd_fst] at h2
zufnz rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff]
zufoa rw [n3e1, n3e, v2e, v2e1]
      unfold nhgt
zufob rw [n₄]; simp only [upd]; grind
zufoi rw [sideInArc_rot hg0 hgn ha0 han hb0 hbn hx0 hxn]
zufoj rw [transpose_n] at hi
      rw [transpose_vtx, transpose_vtx]
zufol rw [upd_same, n2, hn, k1₁] at hb1
zufom rw [upd_same, n2, hn, k1₁] at hb2
zufon rw [v4N]; have := hb1 _ hjN; omega
zufoo rw [v4P]; have := hb1 _ hjP; omega
zufop rw [v62, hM, pos_vtx0, interior_wa hbit he]
zufor rw [whole_set] at h'
      rcases h' with h' | h'
zufos rw [x212, x210, z₆', x211] at v₇
zufot rw [← FuseMath.radius_of_P J (C' := J.left) rfl]
zufow rw [← hseg]; exact Geometry.lerp_mem_segment _ _ hs0.le hs1.le
zufox rwa [walk_succ Q hp, walk_vtx Q hp] at this
zufoz set K := L.length with hKd
      set K₂ := L₂.length with hK₂d
zufpf set j := (E.N.region E.r).arcs.getD t 0 with hjdef
zufph set sel := SelP m0 bTMP bDF bFIRST bFPRE mode a b
zufpj simp (disch := omega) only [Machine.upd_other]; simp_all
zufpk simp [SignTest, Src.pt, SymPt.eval, r70', r95']
zufpl simp only [BEnv.pts, ptsB, this, ↓reduceIte]
zufpm simp only [Machine.upd_apply]; unfold TeRG at hr; grind
zufpn simp only [S, Finset.mem_filter, mem_Sd] at he ⊢
zufpo simp only [add_sub_cancel_left, ← hvy, sub_self, abs_zero]
zufpp simp only [c₁, upd_eq, zero_ne_one, false_iff]
      grind
zufpq simp only [decide_eq_true_eq] at hq; subst hq; decide
zufpr simp only [hw, rayPt_snd, Chain.slitTop] at this
      grind
zufps simp only [rayPt, one_mul, add_sub_cancel] at this
      omega
zufpt simp only [regB, regI, upd, ite_true]
      grind
zufpu simp only [sub_self, abs_zero, add_sub_cancel_left, abs_of_pos hε0]
zufpv simp only at hl
      rw [vi, vm] at hl
zufpx subst heq
zufpy subst hi0
zufpz unfold BEnv.recs at hx; rwa [pts_pos hK] at hx
zufqa unfold Bc0 at hr; simp only [Bool.or_eq_false_iff] at hr
zufqb unfold cntIn bB; simp only [Bool.false_eq_true, ite_false]
      omega
zufqe unfold sideCcw
zufqf unfold sideLeftOf at hsl
      rw [rayPt_sub_self, slitTop_sub_top] at hsl
zufqh unfold tpos
      rcases this with h | ⟨h1, h2⟩
zufqk apply C.sideNot_mem_set_of_abs; right
      simp only [slitTop]; grind
zufql apply Finset.sum_congr rfl
zufqm apply Geometry.point_ext
zufqn apply h1
      rw [FuseMath.radius_of_P J rfl]
      exact J.whole.dom_subset_box hx
zufqo apply hne
zufqp apply point_ext <;> simp [rayPt, lerp]; field_simp
zufqq beta_reduce at hroom
zufqr by_cases h : r = r₀
zufqs by_cases h0 : b < 1
zufqt by_cases h0 : i = 0
zufqu by_cases h0 : kind = 0
zufqv by_cases h6 : w < 6
zufqw by_cases hZP : Z = P
zufqx by_cases hab : a = b
zufqy by_cases hb : b.2 = v.2
zufqz by_cases hc : 0 < s * det p a q
zufra by_cases hki : k = i
zufrb by_cases hkj : k = j
zufrc by_cases hl : li = true
zufrd by_cases hlt : a < b
zufre by_cases hlt : z'.1 < z.1
zufrf by_cases hp6 : p < 6
zufrg by_cases hq : i = k
zufrh by_cases hq : j = k
zufri by_cases hr : G.Reach v x
zufrj by_cases hr : h = R.root
zufrk by_cases hr : r < R
zufrl by_cases hs : tau _ u L h1 h2 ≤ L
zufrm by_cases hsplit : tf = 0 ∧ d' = rL1 J
zufrn by_cases hue : u = e
zufro by_cases hv : v = T.root
zufrp by_cases h₁ : a.2 ≤ J.left.top.2
zufru classical
      obtain ⟨-, hinj, -⟩ := hN
zufry constructor <;> intro h <;> linarith
zufrz exact (hostChain Q S R g h3).vertex_mem_set hk
zufsc exact absurd hz (C.sideWalk_box_pt C.sideBeta hbox hx.1 hx.2.1).1
zufsd exact h.touch_within hU hp ht hcut hf hi' hj hji htouch
zufse exact hcl0 x hx0 hxD0 hxl
zufsg exact hx
zufsm ext d
zufsn ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
zufso ext t
zufsp field_simp <;> ring
zufsq filter_upwards [hev, self_mem_nhdsWithin] with η hη hη0
      simp_all
zufsr filter_upwards [hfe, hp] with ε h1 h3
      simp_all
zufss filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT one_pos] with s hs hs'
zufsu have F₁ := frame_chainI hk₁' dA dm dr drr drm dout
zufsz have e40 := hR.ext
      by_cases hx : c.nreg 70140 = 1
zufta have h := Quot.eqvGen_exact hqq
      rw [eqvGen_or_pair_iff] at h
zuftb have h1 := congrArg Prod.fst h
zuftc have h2 := Nat.ModEq.add_left_cancel' C.s h1
zuftf have hA := hN.2.2.1 k hk
zuftg have hA := hNF.2.2.1 k hk
zuftk have hB' := hB
      rw [hcab] at hA' hB'
zufto have hK₅ := E.hK.fix hI₅
      have hb6 := hb1 _ hj1
zuftr have hN := NFLoc.chain_n_le hC hl hHW
      have hm := C'.m_lt
zufts have hP := hs.mem
      rw [he] at hP ⊢
zuftv have hR' := hR.frame hf'
      rw [hR'.rK] at htest
zufty have hSf : S.Finite := (Set.finite_Iio t).image _
zufud have hU := hRC.1 r hr
zufue have hUo := hsys.regionsIn_open subset_rfl hU
zufuw have hj := final_j hK hRR h hch hisdn hI hna
zufuz have hk := C.sideIdx_le C.sideBeta i
zufva have hk := keyb hAe
      rw [add_zero] at hk
zufvd have hk6 := (vkey_nbrs J hP hk hv).1
zufvf have hl := (corner_iff hDH hi hσ).2 he
zufvh have hlen0 := hD.sinv.length_le
      simp only [List.length_cons] at hlen0
zufvi have hlj := hlt j hj
zufvk have hm := (stop_mem hP hN hok hf).1
zufvo have hmin := lt_min hd hk0
zufvz have hne := hT.topVtx_ne_botVtx hP hq
zufwd have hq' := hT.q_mem hP hq.1
zufwj have hsu := hS.up s hs
zufwn have htake := List.take_of_length_le hlt.le
      rw [htake] at hrec
zufwq have huA := hA'A hu
      by_cases huR : u ∈ R
zufwx have hτ := tpos_lt C k
zufxa have k0₃ := k0_of hE hI₃
zufxg intro L hL p hp t ht ht1 hpos hlt heq
zufxh intro M Q F hM hF
zufxi intro X hX
zufxj intro c hc c' hc' hff
