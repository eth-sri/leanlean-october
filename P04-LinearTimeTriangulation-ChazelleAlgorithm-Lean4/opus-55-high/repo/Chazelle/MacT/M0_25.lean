module

public import Chazelle.MacT.Base

public section

set_option hygiene false

zg zuhim rcases lex_trichotomy L with h' | h' | h'
zuhit refine (Restore.highList_length_le _ _ _).trans ?_
zuhiw refine f.1 r ?_
      unfold Brute.Bt Bk; grind
zuhje rename_i x c
zuhjf right
      filter_upwards [self_mem_nhdsWithin] with s hs hm
zuhjh right; unfold rL at hr ⊢; omega
zuhji rintro _ ⟨ab, hab, rfl⟩
zuhjj rintro c' ⟨b1, b2, b3⟩
zuhjk rintro c' ⟨h1, h2, h3⟩
zuhjl rintro c' ⟨hacc', hk, hm⟩
zuhjm rintro c' ⟨hres, hk', hm'⟩
zuhjn rintro c' ⟨hv, hr, hm⟩
zuhjo rintro c' ⟨inv', he', ha'⟩
zuhjp rintro c' ⟨v1, v2, v3⟩
zuhjq rintro c' ⟨z1, z2, z3⟩
zuhjr rintro c₁ ⟨h1, h2, h3⟩
zuhjs rintro c₁ ⟨w1, w2, w3⟩
zuhjt rintro p ⟨k, hk, hp⟩
zuhju rw [Bbody_imp hh] at hr; omega
zuhjw rw [List.getD_append _ _ _ _ h]
zuhjy rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
zuhjz rw [List.getD_eq_getElem?_getD]
zuhka rw [List.mem_singleton] at hrun; subst hrun
zuhke rw [Nat.card_coe_set_eq, hF.ncard_regionsIn hD hne hS]
zuhkh rw [Nat.mod_eq_of_lt h1] at h; omega
zuhki rw [Nat.mod_eq_of_lt h2] at hsucc; omega
zuhkj rw [Nat.mod_eq_of_lt h3] at hc2; omega
zuhkk rw [Nat.zero_mod, Nat.zero_add, Nat.mod_eq_of_lt hk]
zuhkl rw [Prod.dist_eq, Real.dist_eq] at hzd
      grind
zuhkm rw [Prod.dist_eq, Real.dist_eq] at this
      simp_all
zuhkn rw [a1]; unfold chordSel; grind
zuhkp rw [add_zero, Nat.mod_eq_of_lt hg] at this
zuhkr rw [c0]
      exact hostAt_agree h0 hE he
zuhks rw [chordSet_eq_openChordSet_union hP hi h] at hp
zuhkt rw [chords_ncard hC.1, walk_n] at this
zuhkv rw [cover_of_lt hx, List.map_cons, List.sum_cons]
zuhkw rw [crosses_iff_of_lt huv]
zuhkx rw [dist_rayPt _ hnσ hs0.le]; omega
zuhla rw [div_le_iff₀ hpos]
zuhlb rw [dot_neg_iff_of_cross_zero hz, dot_pos_iff_of_cross_zero hz]
      simp_all
zuhle rw [eventually_all_finite hS]
zuhlf rw [f']; unfold FoundC; grind
zuhlh rw [h1]; unfold sideE; grind
zuhli rw [h1]; unfold winVal; simp_all
zuhlj rw [hA'eq] at this; exact this.2
zuhlk rw [hI.mem]; unfold mem2; grind
zuhll rw [hS g hg, hR.card_sub hg]
zuhlm rw [h]; exact C.sideVertex_succ_ne hP _
zuhln rw [hb] at hA hnv viaGen viaSplit
zuhlo rw [hdq1, mod_pred_mod hn₂ _ hdq0]
zuhlp rw [heq]; exact Geometry.right_mem_segment _ _
zuhlq rw [hlbot, hltop, hlev0]
      omega
zuhlr rw [hmem']; unfold ssWM; grind
zuhly rw [htr, this, ← hxe']
zuhlz rw [hwe2] at hw72 hh2 hp02 hp12
zuhma rw [hwe] at hw7 hh hp0 hp1
zuhmb rw [hx] at hx''; cases hx''
zuhmc rw [hx]; unfold xAt; ring
zuhmd rw [ite_eq_left h0]
zuhme rw [ite_eq_left ha]
zuhmf rw [ite_eq_left hj]
zuhmg rw [ite_eq_left hp]
zuhmm rw [ite_eq_right ha]
zuhmn rw [ite_eq_right hd]
zuhmq rw [ite_eq_right hp]
zuhmr rw [ite_no _ _ hp]
      exact pc₄
zuhms rw [ite_yes _ _ hp]
      unfold cut1
zuhmx rw [key] at hdet
      split_ifs with hlt
zuhmz rw [mem_filter, mem_sub, mem_sub]
      constructor
zuhna rw [mem_segment_iff_of_lt huv]
zuhnd rw [prev_succ_mod hp]
zuhng rw [q103, m₂] at hpre₃ hpost₃
zuhni rw [rL_succ]; exact hp0 p hp
zuhnk rw [sgnOf_ne hσ]
zuhnl rw [sgnOf_one hσ, one_mul, one_mul]
zuhnm rw [this, Set.union_empty]; exact hS
zuhnn rw [this, one_mul, abs_of_pos hε0]
zuhno rw [tv_lt hkR]
zuhnq rw [vK, vS] at vE vC
zuhnr rw [v₀]; unfold FoundC; grind
zuhns rw [← Bool.not_eq_true, chPr_iff] at hnot
zuhnt rw [← Gran.deg_region hN hRC hRO hr]
zuhnu rw [← hT]
zuhnv rw [← hik, h, C.sideIdx_two_m]
zuhnw rw [← hpt, Chazelle.Chain.sidePt_zero]; rfl
zuhnx rw [← hpw, hhi]; omega
zuhny rw [← hs0, Geometry.lerp_zero] at hs
zuhnz rw [← this]
zuhoa set E := L.foldl ins [] with hE
zuhoc set J := jOf C1 C2 hlen with hJ
zuhoe set N := nk I S R with hN
zuhof set S := C.sideS C.sideBeta
zuhog set a := M.W.vtx p
zuhoh set j := rankF keepW L₀ i with hj
zuhoj set p := ⌊a⌋₊ with hpdef
zuhok set q := sidePt M.W p t with hq
zuhol set r := c₀.nreg 83002
zuhom set w := rayPt z σ T with hw
zuhon simp [chordPoly, Polygon.vtx, List.getD_eq_getElem?_getD]
zuhoo simp [withDec, List.getD_eq_getElem?_getD, hr]
zuhop simp only [BQ, Bool.or_eq_false_iff] at hr
zuhoq simp only [BSP, Bool.or_eq_false_iff] at hr
zuhor simp only [Binit, decide_eq_false_iff_not] at hr'
zuhos simp only [Bool.and_eq_true]
zuhot simp only [Bool.false_eq_true, ite_false, ite_true]
zuhov simp only [Chain.slitTop, Chazelle.Geometry.lerp_snd] at htop
zuhow simp only [Chain.slitTop] at hpy; linarith
zuhox simp only [Chain.slitTop] at hy; linarith
zuhoy simp only [Config.nmem_mk, upd]; grind
zuhoz simp only [Config.nreg_mk, upd]; simp_all
zuhpa simp only [Finset.mem_filter, Finset.mem_range] at hv
zuhpb simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
zuhpc simp only [Geometry.lerp, Chain.slitTop] at hy
zuhpd simp only [Geometry.lerp_fst, rayPt_fst]; ring
zuhpe simp only [LB, decide_eq_false_iff_not]; omega
zuhpf simp only [List.foldl_cons]
zuhpg simp only [List.length_append, List.length_singleton] at hk
zuhph simp only [List.length_cons, List.length_nil] at hA₁
zuhpi simp only [List.mem_append, not_or] at hr
zuhpj simp only [List.mem_singleton] at hx
      subst hx
zuhpk simp only [Machine.upd_apply, hr, ite_false]
zuhpl simp only [View.tail, View.head] at this
zuhpm simp only [add_fst, smul_fst]; grind
zuhpn simp only [add_snd, smul_snd]; grind
zuhpo simp only [det, Chain.slitTop]; ring
zuhpp simp only [dist_self, Real.dist_eq, add_sub_cancel_left]
zuhpq simp only [h, Bool.false_eq_true, ite_false]
zuhpr simp only [ite_eq_left hab] at hnot hpt
zuhps simp only [ite_eq_right hab] at hnot hpt
zuhpt simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
zuhpu simp only [mul_zero, offset_zero] at this
zuhpv simp only [posR] at this ⊢
      simp_all
zuhpw simp only [pow_zero, lt_irrefl, ite_false]
zuhpx simp only [rayPt_fst, rayPt_snd] <;> linarith
zuhpy simp only [rayPt_snd, Geometry.lerp_snd]; grind
zuhpz simp only [shearPt]
zuhqa simp only [surgery, upd]; simp
zuhqb simp only [takeL, okB, okI]
zuhqc simp only [true_iff]
zuhqd simp only [upd, ite_true]; grind
zuhqe simp only at q1 q2
zuhqf simp only; rw [hm5, hm4]
zuhqg simpa only [Finset.coe_insert, Finset.coe_singleton] using h
zuhqh split_ifs at * with h1
zuhqi subst h2
zuhqj subst hji
      rw [h.count_prefix_self hsplit hi']
      simp_all
zuhqk subst htf
      rw [h] at hin1
      grind
zuhqm unfold Model.deg
zuhqn unfold Model.key
zuhqo unfold NF.arc; rw [h]; rfl
zuhqp unfold arcCnt
zuhqq unfold cycDist at h
      grind
zuhqr unfold det lerp; grind
zuhqs unfold dirCode at hdir
      grind
zuhqt unfold gradeGran fuseLoss
zuhqu unfold hstep
      rcases Nat.eq_zero_or_pos D with rfl | hD
zuhqx unfold off at h
      grind
zuhqy unfold prevV
      rcases Nat.eq_zero_or_pos q with rfl | h0
zuhqz unfold ratio
      rcases lt_or_gt_of_ne hab with h | h
zuhra unfold scan at h
      split_ifs at h with hc
zuhrb unfold sideCross sideDot; ring
zuhrc unfold sideInArc at hκ
      split_ifs at hκ with h
zuhrd unfold sideLeft sideLeftOf
zuhre unfold stk
      rw [run_succ hm]
      unfold BuildStack.step
zuhrf unfold topGrade
zuhrr apply List.ext_getElem
zuhrs apply h
zuhrv apply hsa
      rcases hP0.lt_or_eq with hP0' | hP0'
zuhrw by_cases a : c₁.nreg 81071 < c₁.nreg 81017
zuhrx by_cases a0 : c.nreg a < c.nreg K1
zuhry by_cases a2 : c.nreg K1 < c.nreg a
zuhrz by_cases a3 : c₁.nreg 81011 < c₁.nreg k
zuhsa by_cases b : e < B.N + B.I.length
zuhsb by_cases b2 : c.nreg K1 < c.nreg b
zuhsc by_cases c1 : d.nreg 217090 < d.nreg 217093
zuhse by_cases g2 : c.nreg 170012 < c.nreg 170085
zuhsg by_cases g3 : c.nreg 170012 < c.nreg 170086
zuhsh by_cases h : b + d < n
zuhsi by_cases h : p + 1 < n
zuhsj by_cases h0 : c.nreg oKd < c.nreg K1
zuhsk by_cases h0 : c₁.nreg 50210 < c₁.nreg 50032
zuhsm by_cases h1 : e + 1 < Q.n
zuhsn by_cases h1 : i + 1 < N
zuhso by_cases h1 : p + 1 < Q.n
zuhsp by_cases h1 : x.edge + 1 < Q.n
zuhsq by_cases h2 : c.nreg K1 < c.nreg oKd
zuhss by_cases h2 : v + 1 < P.n
zuhst by_cases h59 : d₁.nreg 150059 < d₁.nreg 150091
zuhsv by_cases hb : c₂.nreg 170012 < c₂.nreg 170066
zuhsw by_cases hb : d.nreg 30001 < d.nreg gRC
zuhsx by_cases hbox : c.nreg pe < c.nreg K6
zuhsy by_cases hc : c.nreg 30001 < c.nreg 30000
zuhsz by_cases hd2 : d < 2 * J.m₁
zuhta by_cases hflag : c₂.nreg K0 < c₂.nreg 241320
zuhtc by_cases hl : i + 1 < q
zuhtd by_cases hlen : 2 * w ≤ l.length
zuhte by_cases hlt : Lst J < lOff J
zuhtf by_cases hlt : c.nreg a < c.nreg b
zuhtg by_cases hm1 : m + 1 = E.length
zuhth by_cases hodd : d₁.nreg 150087 < d₁.nreg 150088
zuhtj by_cases htt : t = st.top - 1
zuhtk by_cases hw : s + m < n
zuhtl by_cases hx : x ∈ M.arc a k
zuhtm by_cases hz : sideCross B A = 0
zuhtn by_contra hnd
zuhtu constructor <;> linarith [this.1, this.2]
zuhtv exact (D.region_subset_interior hP hp.1).2 h
zuhtx exact (caseC_facts J hv hlt).2.1
zuhtz exact Or.inr (innerPt_bounds C h').1
zuhua exact absurd (basm_io hB).1 hr
zuhug exact hl.mem_boundary_of_closure hS hcS.1 hmS.1.1 hpe hseg hcl
zuhuj exact lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set hmem).2 C.coordBound_lt_radius
zuhun ext <;> simp [lerp] <;> ring
zuhuo filter_upwards [Ioo_mem_nhdsGT hr] with s hs
zuhup filter_upwards [Ioo_mem_nhdsGT hδ₀] with δ hδ
zuhuu filter_upwards [hLt.eventually_const_lt hLpos] with z' hz'
zuhvn have P1 := side_plucker B X Y A
zuhvx have f1 := simple_vtx_inj hP ht hsucc e1
zuhvz have h1 := (C'.mem_slit_iff.1 hys).2.1
zuhwa have h12 := (hT.bot_lt.trans hT.lt_top).le
zuhwd have h4 := (abs_le.1 C.abs_top_snd_le).2
zuhwo have hBout := hoff pb tb hB hBne
zuhwq have hD := (goodShear_epsOf hS.good.2).2.1
zuhws have hFam : I.ChordFamily Q S := hN.1
zuhwt have hFam : M.ChordFamily Q F := hN.1
zuhwu have hH := hostPts_simple hQ hFam hne hR
zuhww have hK : Consts c := e.hA.hK.fix hI
zuhwx have hK := h.rK
      have hbW := h.bW
zuhwy have hK1₄ := (hK.fix hI₄).2.1
zuhxa have hLx := E.hLx
      have hBk := E.hBk
zuhxc have hNn := hE.n_eq
      have hNW := hE.NW
zuhxd have hQ := X.hQ
      have hdh := X.hdh
zuhxe have hQ := h.CQ
      have hD := h.hD
zuhxf have hR : J.left.P = J.right.P := rfl
zuhxg have hR := hX.repr
      have hcnt := hX.cnt
zuhxi have hRO := (regOf_spec E.hNF₂).2.2.2.1
zuhxj have hReq := DownDrv.region_eq_intHost Y.X.hQ Y.X.hFam Y.X.hne Y.X.hR
zuhxl have hS := hC.env
      have hG := hS.good
zuhxm have hS := hFam.2.1
      have hfin := hFam.1
zuhxn have hS₂ := hN.1.2.1
      have hS₂f := hN.1.1
zuhxo have hS₂a := hS₂.2.1
      have hS₂f := hS₂.1
zuhxp have hT2 := hT.2
      unfold Sweep.tabOf at hT2
zuhxq have hTB := hL.TB_le
      have hPW := h.hW
zuhxs have hVV := WalkAx.faces_unique hV' hU hfV' hs1
zuhxt have hW := hin.work
      have h83 := hin.len
zuhxy have ha0 := harc.1
      have han := harc.2.1
zuhyb have hbL := h.botL
      have htL := h.topL
zuhyj have hd := TrapData.diag_eq_of_region_eq hP D D' h
zuhyo have hf : Continuous f := by fun_prop
zuhyp have hfree := whole_free_end hP haR hav hfr
zuhys have hij := D.isTrap.edgeX_lt hP D.free hh.1 hh.2
zuhyw have hk := hd.1
      have hm := hd.2.1
zuhyz have hl0 := harcV.1
      have hln := harcV.2.1
zuhzb have hl3 := hX.lay3
      have hl4 := hX.lay4
zuhze have hle := i0_le hQ T hD hli
zuhzg have hlt := D.isTrap.edgeX_lt hP D.free hyl hyr
zuhzh have hmj := h.mid_j
      have hbs := h.bsrc
zuhzi have hnE : E.n = E.M.W.n := rfl
zuhzl have hne := walk_nonhoriz C hD h6 h7
zuhzn have hone2 := (hR0.fr hf2).one
zuhzw have hps := param_start hu h.h1 h.h2 sh
zuhzy have hpts := regHost_pts li Q.n N r
zuiam have ht0 := hat.2.1
      have ht1 := hat.2.2.1
zuian have ht0 := hpp.1
      have ht1 := hpp.2.1
zuiat have hw := hS.wb
      have h0 := hS.r0
zuiau have hwb := hS.wb
      have hW := hS.hW
zuiaz have k := fr.1
      have hmm := fr.2.2.1
zuiba have k0 := (E.hK.fix hI).1
zuibb have k0 := (hK.fix hI₁).1
zuibc have k02 := (hK₀.fix hI₂).1
zuibd have k0₁ := (hK.fix hI₁).1
zuibe have k1 := (hK.fix hI).2.1
zuibf have k1₁ := (hK.fix hI₁).2.1
zuibi have nN1 := hNW1.nfAt
      have nN2 := hNW2.nfAt
zuibp intro e he hsc p t hA hL
zuibq intro h; unfold chordSel at h
      grind
zuibr intro hex
      unfold st at hex
      unfold keyBkt
zuibt intro hk
zuibu intro hr
zuibv intro ht
zuibw intro i
zuibx intro l d D ih₁ ih₂ h hT
zuiby intro q hq h
      unfold SlotW at h
zuibz intro r hr h0 h1 h2 h3 h4
zuicb linarith [(abs_lt.1 h1.1).2]
zuicc linarith [(abs_lt.1 h2.1).1]
zuicd obtain ⟨R, hR⟩ := h
zuice obtain ⟨c, hc⟩ := hne
zuicf obtain ⟨dd, hDec⟩ := hP.hDec
zuicg obtain ⟨e, hgt⟩ := x
zuich obtain ⟨e, hh⟩ := x
zuici obtain ⟨h0, h1⟩ := hs
zuicj obtain ⟨hA1, hA2⟩ := hAg
zuick obtain ⟨hI, hex⟩ := h
zuicl obtain ⟨hK, hH⟩ := hf
zuicm obtain ⟨hch, -⟩ := hNA.2.2.2.2.2
zuicn obtain ⟨hctx, hcap⟩ := S₁.ctx
zuico obtain ⟨he, hchain'⟩ := hchain
zuicp obtain ⟨hf, hb⟩ := hE
zuicq obtain ⟨hi, hl⟩ := hok
zuicr obtain ⟨hlabR, hinv⟩ := S.labels
zuics obtain ⟨hok, hf⟩ := hD
zuict obtain ⟨hp1, hp2⟩ := hp
zuicu obtain ⟨hs1', hs2⟩ := hs
zuicv obtain ⟨hz0, hzK⟩ := hnot
zuicw obtain ⟨k, hk⟩ := h2
zuicx obtain ⟨k, hk⟩ := hs.1
zuicy obtain ⟨m, rfl⟩ := hgh
zuicz obtain ⟨n, hn⟩ := hsc.exists_nat_pow_eq
zuida obtain ⟨n, rfl⟩ := h
zuidb obtain ⟨o1, o2⟩ := ho
zuidc obtain ⟨q, q0⟩ := q
zuidd obtain ⟨rfl, rfl⟩ := hab
zuide obtain ⟨v1, v2⟩ := v
zuidf obtain ⟨z, hz⟩ := hM.nonempty
zuidg rcases C.sideTour_step C.sideBeta i with h | h
zuidh rcases Chazelle.Chain.regionsIn_eq_or_disjoint hV hU with h | h
zuidi rcases D.vtx_mem_closure_region hk hv with h | h
zuidj rcases Nat.lt_or_ge _ A with hj1 | hj1
zuidk rcases Nat.lt_or_ge _ n with h | h
zuidl rcases Nat.lt_or_ge g' g with h1 | h1
zuidm rcases Nat.lt_or_ge i L with h | h
zuidn rcases Nat.lt_or_ge i' i with hlt | hge
zuidp rcases Nat.lt_or_ge p 6 with h6 | h6
zuidr rcases Nat.lt_or_ge t j with h | h
zuidw rcases c with ⟨a, b⟩
zuidy rcases hD.sound _ h with h' | h'
zuidz rcases hX with hX | hX | hX
zuiea rcases hc with hb | hT | hT
zuieb rcases hcases with he | he | he
zuiec rcases hi with rfl | rfl | rfl
zuied rcases hon with h | h | h
zuiee rcases hr with rfl | rfl | rfl
zuief rcases hx with rfl | rfl | hx
zuieg rcases hσ with rfl | rfl <;> nlinarith
zuieh rcases le_or_gt x y with hy | hy
zuiei rcases le_or_gt y x with hy | hy
zuiej rcases le_total U.2 V.2 with hh | hh
zuiek rcases le_total a.1 b.1 with h | h
zuiel rcases le_total m m' with hle | hle
zuiem rcases le_total s.1.1 s.2.1 with h | h
zuien rcases le_total x B with h' | h'
zuiep rcases le_total z₁.1 m.1 with h | h
zuieq rcases mem_segment_or_far ht.2 h with h' | h'
zuier rcases mem_segment_or_far ht.2 hx with h | h
zuieu refine (Set.ncard_union_le _ _).trans ?_
zuiev refine (ncard_union_le _ _).trans ?_
zuiey refine rejQ c₁ frR1 hA₁ fr1.2.2 best1 ?_
zuifb refine weight_le fun a b h => ?_
zuifh replace hk₅ : k₅ ≤ 260 := hk₅
zuifi rintro x ⟨hxb, hx⟩ hxB
zuifj rintro z (hz | hz) hzD
zuifk rintro ⟨c, hc, hwc⟩
zuifl rintro ⟨c, hc, hxc⟩
zuifm rintro ⟨c, hc, rfl⟩
zuifn rintro ⟨d, hd, e⟩
zuifo rintro ⟨d, hd, hx⟩
zuifp rintro ⟨e1, e2, e3⟩
zuifq rintro ⟨hzy, hzl, hzr⟩
zuifr rintro ⟨i, hi, hx⟩
zuifs rintro ⟨i, hi, hz⟩
zuift rintro ⟨j, hjn, hjm⟩
zuifu rintro ⟨s, hs, hys⟩
zuifv rintro ⟨t, ht, rfl⟩
zuifw rintro ⟨y, hy, rfl⟩
zuifx rintro ⟨z, hz, hzU⟩
zuify rw [C.sideWalk_vtx_five, C.sideWalk_vtx_six] at hpy
zuifz rw [C.sideWalk_vtx_four, C.sideWalk_vtx_five] at hpy
zuiga rw [C.sideWalk_vtx_one] at hy; grind
zuigb rw [C.sideWalk_vtx_three] at hy; grind
zuigc rw [C.sideWalk_vtx_tour β le_rfl, sideTour_two_m]
zuigd rw [C.sideWalk_vtx_two, C.sideWalk_vtx_three] at hpy
zuige rw [C.sideWalk_vtx_wrap, walk_last] at hpy
zuigf rw [C.sideWalk_vtx_zero, C.sideWalk_vtx_one] at hpy
zuigg rw [Chain.sidePt_zero]; exact walk_vtx_tour hi
zuigh rw [Chazelle.Chain.sideLeft_zero, cm_W, C.sideWalk_n]
zuigi rw [Chazelle.Chain.sidePt_zero, Chazelle.Chain.sidePt_zero] at this
zuigm rw [List.mem_toFinset, List.mem_map] at hx
zuign rw [List.mem_toFinset, hlists v hv]
zuigo rw [List.nodup_iff_injective_getElem]
      intro i j hij
zuigq rw [Merge.Junction.left_inter_right J hP] at this
zuigr rw [Merge.insert_sdiff_self hc]; exact hX
zuigt rw [R₁.r79] at s₂
      exact s₂
zuigu rw [Set.ncard_coe_finset, h1] at h3
zuigv rw [a16, a03] at hlt
zuigw rw [a87, a88] at hx₂
zuigx rw [abs_lt]; constructor <;> nlinarith
zuigy rw [add_zero, add_zero] at this
zuigz rw [arcWt_chain C Q hx hy]
zuiha rw [c4SB, c4AB, hm4]
zuihc rw [chain_dirCode_small C he] at hdir
zuihd rw [chordSet_eq_openChordSet_union hP hi h]
      simp_all
zuihe rw [cm_W, h6, hz]
zuihf rw [compl_arc_index, Nat.add_assoc] at he₂
zuihg rw [connectedComponentIn_eq h1, connectedComponentIn_eq h2]
zuihh rw [d42, d44] at hd1
zuihi rw [d42, d44] at hd2
zuihj rw [da, db] at t3
zuihk rw [det_lerp, det_self_right]; ring
zuihl rw [e1, e2, Merge.Junction.whole_vertex_add]
zuihm rw [e1, e2, e3]
zuihn rw [e1, e2]; rfl
zuiho rw [e1, e2]; tauto
zuihq rw [eE, hK₁.2.1] at e
zuihr rw [eE, hK₁.2.2.2.2.2.2] at e'
zuihs rw [eE3, e46] at h2
zuiht rw [eE3, e46] at h3
zuihu rw [eSP, eSC] at hs
zuihw rw [ex, ey] at h
zuihy rw [fm, f302, eTB]
zuihz rw [fr_key, ht, add_zero]
zuiia rw [h.v41, k6] at e''
zuiib rw [h.vE, h.v41] at e
zuiic rw [h.vE, h.vt] at e''
zuiid rw [h.vE, k6] at e
zuiie rw [h0, h1, h2]
zuiif rw [h05, c03] at htest
zuiig rw [h1, mul_zero] at e1
zuiih rw [h22, h1] at hp
zuiii rw [h49, h24] at hf
zuiij rw [h53, r1'] at hp
zuiik rw [h5] at hD; nlinarith
zuiil rw [h8 _ hx] at htx
zuiim rw [h87, h88] at ht
zuiin rw [hA, length_singleton] at hj
zuiio rw [hA₂, hA₁, sγ]
zuiip rw [hBX, hXA, hdBX]
zuiiq rw [hBi, hlc, Nat.sub_zero]
zuiir rw [hE₅.r32, d₅] at hd0
zuiit rw [hK1, hK2] at hroom
zuiiu rw [hK₁.1, a3] at h0
zuiiv rw [hK₁.2.1, eR] at h1
zuiiw rw [hK₁.2.2.2.1, eE] at h2
zuiix rw [hK₂.2.2.1, e46] at h2
zuiiy rw [hK₃.1, n3H] at h1
zuiiz rw [hK₃.2.1, eY3] at h1
zuija rw [hL, one_mul] at hδ1
zuijb rw [hM'', chainDesc_unique hC' hD]
zuijc rw [hM, cm_n] at we
zuijd rw [hM.le, hd] at h2
zuije rw [hM.ll, hd] at h1
zuijf rw [hM.ll, hd] at h3
zuijg rw [hM] at hpp he hpos
zuijh rw [hPdef]; unfold unwrapK
      split_ifs
zuiji rw [hV, Finset.mem_filter, Finset.mem_range]
zuijj rw [hW, walk_n] at hb
zuijk rw [hX2, hR2.rn] at hv
zuijl rw [hc0A] at d2 hrec e1
zuijm rw [hcl, hdeg, hexl]
zuijq rw [hdet] at h; nlinarith
zuijr rw [hedge, hshift] at hx
zuijs rw [hf4.2.2.2.2 _ id]; grind
zuiju rw [hfound] at e52 e53 e54
zuijv rw [hget] at m1 m2 m3
zuijw rw [hi, esC] at hlt
zuijx rw [hje, r7] at htest
zuijy rw [hk0, v3] at hf
zuika rw [hleft, hpt]; omega
zuikb rw [hm', Machine.upd_apply, Machine.upd_apply]
zuikc rw [hmd₁] at a2 a3 a4
zuike rw [hn, hwm]; omega
zuikg rw [hone, hi] at htest
zuikh rw [hopen] at hcR hex ⊢
zuikj rw [hpc', hl] at hp'
zuikk rw [hpj, H.pt_eq T hjm]
zuikl rw [hpos1, hz2] at habove
zuikm rw [hposf]; exact ray_ne hT
zuikn rw [hq0d] at hq₂ loc1 loc2
zuiko rw [hqv, hGN] at this
zuikp rw [hs1, Geometry.lerp_one] at hs
zuikq rw [hset, ncard_coe_finset, Nat.card_Ico]
zuikr rw [htq', e33] at h1
zuiks rw [hwdef] at h6 hE ⊢
zuikt rw [hμ] at hleaf hroom ⊢
zuikw rw [i5, i6]; rfl
zuikx rw [ite_eq_left h] at hi0 ⊢
zuilb rw [i₃, k58] at hlt
zuilc rw [k0, vH] at hp
zuild rw [k01, bF1] at h3
zuile rw [k02, eD] at hd
zuilf rw [k0₂, h2] at hb3
zuilh rw [key_pz] at hk; grind
zuili rw [key_pz] at hk; simp_all
zuilj rw [lOff_of_vnt J hv, Lst_rlen]
zuill rw [m10, m9, m8]
zuilm rw [mem_bfilt] at hq hq'
      simp_all
zuilo rw [mem_union, not_or] at hcon
zuils rw [n2.1, n1.1, Machine.upd_upd_same]
zuilt rw [newLB_pos _ _ _ hK]
zuilu rw [not_or, not_not] at hcon
zuima rw [p32, p10502] at hd2'
zuimb rw [pa, pb] at kab
zuimd rw [prevIdx_eq P hi]; grind
zuime rw [r0, r1, r2]
zuimf rw [r11', h19] at hB
zuimj rw [radius_mir, mir_pt, neg_neg]
zuimk rw [rayPt_fst, rayPt_fst] at h1
zuiml rw [s28, d28, sofJ_succ]
zuimm rw [s36, s06] at he
zuimn rw [s36, s54] at he
zuimo rw [stackList_last P hn]; simp
zuimp rw [subPoly_shear, rotate_shear] at h
zuimq rw [this, hI.q0] at hqi
zuimr rw [this] at h; tauto
zuims rw [topIdx_mir, vertex_mir]; rfl
zuimt rw [tv_lt hr] at h8 ⊢
zuimu rw [unwrapK_self] at this; grind
zuimw rw [upd_other _ _ _ hne]
zuimx rw [v1, v2] at hlt
zuimy rw [v1s, v1s1]; omega
zuimz rw [v2e, v2e1]; omega
zuina rw [v58, h84]; rfl
zuinb rw [vd, hM₃.e1] at hb2
zuinc rw [view_lt d.2, h.rot d.2]
zuind rw [v₃, g₂, hzo]
zuine rw [v₆, q5]; rfl
zuinf rw [z1, h1g] at hg0
zuing rw [z2, f2] at hf0
zuinh rw [z91, v93] at a
zuini rw [← ecA, ← ecC]
zuinj rw [← h.2.1] at this
      linarith
zuink rw [← hD.R] at hX hY
zuinl rw [← hb, ← hb']
zuinm rw [← hki] at hpi ⊢
zuinn rw [← hn] at hroom ⊢
zuinp rw [← hty] at h1 h2
zuins set D := D₀ \ c with hD
zuint set D := Q.filled \ Q.boundary with hD
zuinu set F := N.F M Q with hFdef
zuinv set K1 := E.K₀ + 1 with hK1
zuinw set L := min _ lim with hL
zuinx set R := L.length + 1 with hR
zuiny set S := N.F I Q with hS
zuinz set S₂ := N₂.F _ _ with hS₂d
zuioa set U := connectedComponentIn _ q with hUdef
zuiod set c := E.getD m 0 with hc
zuioe set d := dirCode M x.edge with hd
zuiof set j := prevIdx P i with hj
zuiog set j := prevIdx W p with hj
zuioi set t₂ := x - p with ht₂
zuiom set x := hk _ S R i
zuion set x := offset _ _ t' δ
zuior simp [Geometry.lerp, xv, hx]
zuios simp [phi, stretchPt, hk]
zuiot simp only [Chazelle.Geometry.lerp_fst] at hb
      grind
zuiou simp only [Finset.mem_filter, Finset.mem_range]
      constructor
zuiov simp only [Geometry.lerp] at this
      grind
zuiow simp only [Host.whole, List.getD_cons_zero]
      simp_all
zuiox simp only [List.length_cons] at hW ⊢
zuioy simp only [Machine.upd_same, hone3]
      grind
zuioz simp only [Polygon.vtx, List.getD_eq_getElem?_getD]
zuipa simp only [Prod.snd_sub] at this
      linarith
zuipb simp only [Set.mem_ofPred_eq, List.mem_map]
      constructor
zuipc simp only [SignTest] at this
      grind
zuipd simp only [SymPt.eval, Polygon.vtx]
      simp_all
zuipe simp only [SymPtIn] at h ⊢
zuipf simp only [SymPtIn] at hin ⊢
zuipg simp only [SymPtIn] at hp ⊢
zuiph simp only [SymPtIn] at hq ⊢
zuipi simp only [h2, ↓reduceIte]
zuipj simp only [h3, ↓reduceIte]
zuipk simp only [h4, ↓reduceIte]
zuipl simp only [hd₁, upd]
      grind
zuipm simp only [hlt, ↓reduceIte]
zuipn simp only [hv, ↓reduceIte]
zuipo simp only [mem_ofPred_eq, mem_Ico]
      constructor
zuipp simp only [mem_ofPred_eq, mem_image]
      constructor
zuipq simp only [min_def, max_def]
      grind
zuipr simp only [rayPt_fst, rayPt_snd]
      grind
zuips simp only [rayPt_fst] at h
      linarith
zuipt simp only [rayPt_fst] at h1
      linarith
zuipu simp only [rayPt_snd] at h
      linarith
zuipv subst ha2
      rcases hAw with h' | h'
zuipw subst hb2
      rcases hBw with h' | h'
zuipx subst hi
zuipy subst hrest
      rw [List.append_nil] at hsplit
zuipz unfold Merge.shoot
      rw [hTeq]
      ext z
zuiqa unfold Model.arcWt
zuiqb unfold dq; rw [ite_eq_left hdl]
zuiqc unfold endPos
zuiqd unfold slfOffR slfO sw at *; omega
zuiqh unfold wrapK
zuiqi unfold κT at *; push_cast; linarith
zuiqs all_goals first | omega
zuiqu apply List.ext_getElem hl
zuiqw apply point_ext <;> simp [ho]
zuiqx beta_reduce
      rw [r9, hA₁]
zuiqy beta_reduce
      rw [sγ] at hk₃
zuiqz beta_reduce at hcost
zuira beta_reduce at hk₂
zuirc by_cases b0 : c.nreg 50205 < 1
zuird by_cases h : c₄.nreg aF = 1
zuire by_cases h : r = key j
zuirf by_cases h1 : c.nreg b = 1
zuirg by_cases h1 : j = st.nd1 c
zuirh by_cases h1 : sideInArc a b b'
zuiri by_cases h2 : 1 < c.nreg 10502
zuirj by_cases hD : c.nreg 120050 = 1
zuirk by_cases hL1 : 0 < c.rreg 115
zuirl by_cases ha : c.nreg 30000 < K
zuirm by_cases hact : σ.act t = 1
zuirn by_cases hcap : f ∈ capChords J
zuirq by_cases hdl : d < lL1 J
zuirs by_cases hna : D.NonAdj
zuirt by_cases hr : r = u i
zuiru by_cases hr : r = v i
zuirv by_cases q2 : c.nreg c2 = 1
zuirw by_cases q2 : sideInArc ka kb ky
zuirx by_contra h0; push Not at h0
zuiry by_contra hc'; push Not at hc'
zuirz by_contra hne'
zuisa by_contra hne; tauto
zuisb by_contra hxa; push Not at hxa
zuisc by_contra hxb; push Not at hxb
zuisg change c₅.nmem _ = _ at l2
zuish exact (FuseMath.sideLeft_rayPt hs).2 hsl
zuisi exact (FuseMath.sideLeft_rayPt hε0).1 hz
zuisj exact (List.finite_toSet _).image _
zuisk exact (arc_regOf hNF hj).1
zuisl exact (h.stat.nd0 c hc.1).1
zuism exact (h.stat.nd1 c hc.1).1
zuiso exact (lerp_ne_right hne ht1).symm
zuisp exact Geometry.right_mem_segment _ _
zuisq exact I.chords x' hx' h' f hf
zuiss exact Nat.mod_lt _ hn
zuisu exact Sweep.arcSet_subset_compl_dom C hP _ _ hj
zuisw exact ccw_half_left h
zuisx exact ccw_half_right h
zuisy exact combo_gt hx hy hs hs' h
zuisz exact combo_lt hx hy hs hs' h
zuita exact combo_lt_combo hx3 hy3 ha hb hab
zuitb exact combo_lt_combo hx4 hy4 ha hb hab
zuitc exact connectedComponentIn_subset _ _
zuitd exact convex_trapSet P D.i D.j D.y₁ D.y₂
zuitk exact hM₁.trace _ hA₁.1 t hA₁.2.1 hA₁.2.2.1.le
zuitm exact hnot_in j hj0 hjd s' hs'
zuitn exact hp
zuito exact hq
zuitq exact left_mem_segment _ _
zuits exact ok_ptAns J Q pt₀ q h
zuitt exact ok_ptAns J Q pt₁ q h
zuity ext <;> simp
zuitz ext c; constructor
zuiua ext c; simp [famOf]
zuiub ext d; simp [fam]
zuiuc filter_upwards [hf] with t ht
zuiud filter_upwards [hfree] with t ht
zuiur have cv := cand_vertex C C.sideBeta hk
zuiuw have f₁ := F₁.1
zuiux have g₅ := f₅.1
zuiuz have h := hT.no_vertex i hT.hi
      grind
zuiva have h := hcost
      beta_reduce at h
zuivb have h' := h
zuive have h1 := hvalid.1 V₀ hV₀ hR
zuivf have h2 := J.right.one_le
zuivg have h2 := Nat.log_le_clog 2 n
      omega
zuivh have h2 := Set.ncard_le_ncard hsub hfin
      omega
zuivj have h21 := hI.h21
zuivl have h5 := hwf.1
zuivm have hA := agree_pre hu h.h1 h.h2
zuivp have hA := hL.A
zuivt have hC := h.canon
zuivv have hE₁ := hE.frame hX hF₁ bCore_notin_drvBands
zuivx have hF := hC.1.1
zuiwe have hK := I'.rK
zuiwg have hL := h.lay
zuiwh have hL' := List.length_eq_zero_iff.1 hL
      subst hL'
zuiwj have hL1 := hR.hL
zuiwk have hLU := g.L_le_U
zuiwm have hLn := hR.hLn
zuiwo have hN := hNW.holds
zuiwp have hN := hcan.1
zuiwq have hNA := hNW.holds
zuiwr have hP := g.two_pow_L
zuiws have hP := h.simple
zuiwt have hP := hA.hP
zuiwu have hP := hM.1
zuiwv have hQ := H.simple
zuiww have hR' := hR
zuiwx have hRaY := haft Ra hRa hWa
zuiwy have hS₂ := hN.1
zuiwz have hT := hE.hT
zuixa have hTA := E.hTBR
