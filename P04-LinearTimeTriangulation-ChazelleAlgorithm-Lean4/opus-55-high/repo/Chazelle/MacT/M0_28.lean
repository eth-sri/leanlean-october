module

public import Chazelle.MacT.Base

public section

set_option hygiene false

zg zultv unfold Model.key Model.param Model.wa Model.wb
zultw unfold St.cntOf
zultx unfold WCand GAt
zulty unfold WalkKey.KeyPred at h
      grind
zultz unfold WrLev rL; omega
zulua unfold Yg
zulub unfold arcAt
      simp_all
zuluc unfold arcWtNat keyCeil
zulud unfold bandOf bL41; omega
zulue unfold bandOf bLocate; omega
zuluf unfold bcnt bfilt
zulug unfold clampR
      grind
zuluh unfold cntIn
zului unfold codeLe
zuluk unfold cyc sideInArc
zulul unfold delFace
      grind
zulum unfold dropE
zulun unfold gradeGran fuseLoss; ring
zuluo unfold len scls; omega
zulup unfold markMem
zulur unfold nhgt Restore.normOf
zulus unfold ord
      grind
zulut unfold rX2 rY2; grind
zuluu unfold rawRec rawDc rawAux
      simp_all
zuluv unfold rpowCeil
      apply Nat.one_le_iff_ne_zero.2
      positivity
zulux unfold sideInArc at hkey
      grind
zuluy unfold sideInArc at hnot hpt
zuluz unfold sideLeft
zulva unfold sideLeftOf at h ⊢
zulvb unfold sidePrev at this
      grind
zulvc unfold sqLen at hsq
      nlinarith
zulvd unfold upd1 HitC
zulve unfold xAt
zulvn apply Fin.ext
zulvs apply hnot
zulvu apply hnv _ hk
zulvw apply seg_arg <;> omega
zulvx apply this
zulwa by_cases hAn : An
zulwc by_cases hs : sel
zulwd by_contra h6
zulwe by_contra hlt
zulwf by_contra hno
zulwq congr 1; grind
zulwx exact C.not_mem_set_of_mem_dom hd h
zulwy exact Chazelle.Geometry.left_mem_segment _ _
zulwz exact Chazelle.Geometry.right_mem_segment _ _
zulxb exact Geometry.segment_comm _ _
zulxe exact Nat.le_of_mul_le_mul_left this hμ
zulxg exact Prod.ext h1 h2
zulxh exact Prod.ext rfl hm.1
zulxj exact WalkEmbed.slitTop_not_mem_box C hvbox
zulxm exact absurd h ha
zulxz exact boundary_subset_closure_component hP hL
zulya exact boundary_subset_closure_component hP hR
zulyd exact closure_mono hsub this
zulyf exact connectedComponentIn_mono u hA'A
zulyi exact h0
zulyj exact h4
zulyk exact hAR i hi
zulyl exact hB y hy
zulym exact hI.cov
zulyn exact hI.hgood p hp
zulyo exact hI.vbG
zulyp exact hI.vbn
zulyq exact hJW.2.2.2 H hJ.2.2.1
zulys exact hSR i hi
zulyt exact hT.subset_connectedComponentIn hqT hTS
zulyu exact hdisj.notMem_of_mem_left hp hpR
zulyv exact he
zulyw exact hf1.1 r hr
zulyy exact hreg H hJ.2.2.1
zulyz exact hsec _ hx
zulza exact hst.2 τ h
zulzb exact hw
zulzc exact isPreconnected_connectedComponentIn
zulzd exact kph r hb
zulzg exact max_lt hmε hε
zulzh exact mem_closure_of_tendsto hlim hev
zulzj exact pairs₁ t ht
zulzl exact piece_set_sub hdir' hc
zulzo exact right_mem_segment _ _
zulzp exact right_split_top J hδ
zulzr exact sReg v hv
zulzt exact slitTop_not_mem_box C h1
zulzx exact walkMir_sideWalk_not C _
zumae exfalso; apply hTD
zumaf exfalso; apply hn
zumag ext j
zumah ext p; constructor
zumai ext z
zumaj ext z; constructor
zuman have  := Nat.floor_le hbx.1
zumao have E := hI.env
zumap have R := hS.regs
zumaq have R₂ := f₂.1
zumar have fr := hM.2.2.2
zumas have g1 := f1.1
zumat have g1 := fr1
zumau have g₂ := r₂
zumav have g₆ := F₆.1
zumaw have h := E.hTBR
zumax have h1 := Cα.one_le
zumay have h1 := J.right.one_le
zumaz have h1 := h
zumba have h1 := hI.room
zumbb have h1 := hI₃.h23
zumbc have h1 := he'A'.2.2.2.1
zumbd have h1' := hI₄.h23
zumbe have h1m := Cα.one_le
zumbf have h2 := M.two_mul_euler
zumbg have h2 := hA.2.2.1
zumbh have hA := env.aW
zumbi have hA0 := E.hA0
zumbj have hA2' := hA2
zumbk have hA5 := hE.F.hA
zumbl have hA₁ := hF₁.2.2.2.2.2.2
zumbm have hA₁ := hfr₁.2.2.2.2
zumbn have hA₁ := hrf₁.2.2.2.2.2.2
zumbo have hD5 := hwf.1
zumbp have hFam := B.fam
zumbq have hFam := hN.1
zumbr have hG := hR.holds
zumbs have hG := hctx.1
zumbt have hGn := Y.gn
zumbu have hK := E.hK
zumbv have hK' := hK
zumbw have hKR := hF.hKR
zumbx have hL' := hL
zumby have hLm := hB.hLm
zumbz have hM1 := f₁.2.2.1
zumca have hN0 := hNW.nfAt
zumcb have hNA := hN.holds
zumcc have hNAt := hNW.nfAt
zumcd have hNF := hE.hNF
zumce have hP := hctx.2.2.2.2.1
zumcf have hP₁ := E.hP
zumch have hR := C.coordBound_lt_radius
zumci have hR := h₁.1
zumcj have hRt := J.right.top_snd_lt_radius
zumck have hSA := hS₁.2.2.2
zumcl have hS₁ := hE₁.setup
zumcm have hT := C.top_snd_lt_radius
zumcn have hT := X.ch.hT
zumco have hTR := C.top_snd_lt_radius
zumcp have hTm := C.topIdx_le
zumcq have hW := hI.wb
zumcr have hW13 := e₁₃.wb_right
zumcs have hW3 := hD.W1
zumct have hWh := hE.hWh
zumcu have hWn := E.nW
zumcv have ha' := ha
zumcw have hab := hch.lt
zumcx have hab := hh.lt
zumcy have hadm := hL.1.2.1
zumcz have hal := h.alloc
zumda have harr := h.arr
zumdb have hb0 := harc.2.2.1
zumdc have hc := h.ctx
zumdd have hconv' := hconv
zumde have hcp := hSF.cpMem
zumdf have hcs := hR.hcs
zumdg have hctx0 := hctx
zumdh have hd1 := hA.hd0
zumdi have hdN := hD.hdN
zumdj have hdir' := hdir
zumdk have hend := S.hend
zumdl have hfy' := hfy
zumdm have hi := D.isTrap.hi
zumdn have hil := hD.hil
zumdo have hin := h.y₁_lt_y₂.le
zumdp have hj := D.isTrap.hj
zumdq have hj' := hj
zumdr have hjK' := hlt
zumds have hl := C.coordBound_lt_radius
zumdu have hlen := hH.1
zumdv have hlev := h.length_evs
zumdw have hli := h.lo_i
zumdx have hlo := hI.lo
zumdy have hm := C.m_lt
zumdz have hm := J.left.two_m_pos
zumea have hm1 := Cα.one_le
zumeb have hm1 := J.one_le_m₁
zumec have hmn := C.m_lt
zumed have hn := hE.hn
zumee have hn := hS.nW
zumef have hn0 := hC.n_pos
zumeg have hn3 := hE.hn3
zumeh have hn3 := hF.hG.1.1
zumei have hnW := X.hnW
zumej have hnW := hctx.2.2.2.2.2
zumek have hout := h.out
zumel have hp' := hp
zumem have hpc := hxc.2.2.1
zumen have hpc' := hpc
zumeo have hpre' := hpre
zumep have hq' := hq.1
zumeq have hreg := hI.regs
zumer have hroom := hG.room
zumes have hroom' := hroom
zumet have hs0 := hs1.1
zumeu have hs0 := hs2
zumev have ht := C.top_snd_lt_radius
zumew have ht1 := hA.2.2.1
zumex have htl := C.topIdx_le
zumey have htw := hA.htabw
zumez have hvk := hv
zumfa have hx' := hx
zumfb have hz' := hz
zumfc have hzy := hz.1
zumfd have hδ := hδ0
zumfe have hε := h5
zumff have hσ := hE.hσ
zumfg have hσ := q.hσ
zumfh have i22 := hI.h22
zumfi have k := hr
zumfj have k3 := hK.2.2.2.2.2.2
zumfk have k6 := h.hK.2.2.1
zumfl have k6 := hK.2.2.1
zumfm have k₁' := f₁.1
zumfn have r0 := hf4.1
zumfo have r1 := hG.one
zumfp have r1 := hG3.one
zumfq have r3 := h3r
zumfr have reg8 := hI.regs
zumfs have w1 := e1.wb_right
zumft have w₀ := e₀.wb_right
zumfu have w₁ := X1.wb_right
zumfv have w₁' := e₁'.wb_right
zumfw have w₁₀ := e₁₀.wb_right
zumfx have w₂ := I₂.wb
zumfy have w₂ := e₂'.wb_right
zumfz have w₃ := ex₃.wb_right
zumga have w₅ := x₅.wb_right
zumgb have z := hR.zero
zumgf intro H j hj
zumgg intro L
zumgh intro X Y Z
zumgi intro X h1 h2
zumgj intro a
zumgk intro c hn hc
zumgl intro c hw hJ
zumgm intro c' hc' _
zumgn intro d e hde
zumgo intro d hd hpd
zumgp intro d' hd' hn
zumgq intro e he hA
zumgr intro h; positivity
zumgs intro hL
zumgt intro hs
zumgu intro hθ1
      subst hθ1
zumgv intro hτ1
      subst hτ1
zumgw intro i hi hno
zumgx intro i hi0 hi
zumgy intro j h1 h2
zumgz intro j hj hj'
zumha intro j hj hjk
zumhb intro j hj0 hjd
zumhc intro k hk hkz
zumhd intro l D hD
zumhe intro l hl hlV
zumhf intro q h1 h2
zumhg intro q hq hqp
zumhh intro r a b
zumhi intro s
zumhj intro s hs hm
zumhk intro s hs1 hs2
zumhl intro t h1 h2
zumhm intro t ht hm
zumhn intro u hu hpu
zumho intro v t ht
zumhp intro w hw hwz
zumhq intro x hx _
zumhr intro x hx hcut
zumhs intro z h1 h2
zumht intro z hz hzD
zumhu intro z hz hzy
zumia linarith [h.2]
zumib linarith [hB.2.2.1]
zumic linarith [hC.lt]
zumie push Not at h1
zumif push Not at hD
zumig push Not at hL
zumih push Not at hT
zumii push Not at ham
zumij push Not at hb
zumik push Not at hc
zumil push Not at hd
zumim push Not at hex
zumin push Not at hh
zumio push Not at hk
zumip push Not at hne
zumiq push Not at hq
zumir push Not at hqt
zumis push Not at hs
zumit push Not at hsd
zumiu push Not at hsole
zumiv push Not at huniq
zumiw push Not at hw
zumix push Not at hx
zumjb refine convexHull_min ?_ ?_
zumjd refine le_antisymm ?_ hge
zumje refine le_trans Nat.cast_div_le ?_
zumji refine max_lt ?_ ?_
zumjk refine spec_ifLtN_false g ?_
zumjl refine spec_ifLtN_false g1 ?_
zumjm refine spec_ifLtN_false h ?_
zumjo refine spec_ifLtN_false ha ?_
zumjp refine spec_ifLtN_false hk ?_
zumjr refine spec_ifLtN_true g ?_
zumjs refine spec_ifLtN_true g1 ?_
zumjt refine spec_ifLtN_true g2 ?_
zumju refine spec_ifLtN_true hc ?_
zumla rintro rfl; simp
zumlb rw [C.chainEdge_eq]
zumlc rw [C.sideBeta_eq_true_iff]
zumld rw [DownMath.regHost_pts]
zumle rw [Finset.card_map]
zumlf rw [Fintype.card_eq_zero_iff]
zumlg rw [Geometry.lerp_symm]
zumlh rw [Geometry.lerp_zero]
zumli rw [Geometry.segment_comm]
zumlj rw [List.foldl_cons]
zumlk rw [List.map_flatMap]
zumll rw [List.map_pmap]
zumlm rw [List.pairwise_append]
zumln rw [List.pairwise_flatMap]
zumlo rw [List.pairwise_iff_getElem]
zumlp rw [List.range_succ]
zumlq rw [M.opp_opp]
zumlr rw [Machine.upd_other]
zumls rw [Machine.upd_same]
zumlt rw [Merge.contractionCondIn_iff]
zumlu rw [Nat.ceil_le]
zumlv rw [Nat.mod_add_mod]
zumlw rw [abs_lt]
zumlx rw [arcWt_eq]
zumly rw [bary₂_lerp]
zumlz rw [bcnt_eq]
zumma rw [cntLt_succ]
zummb rw [combineTri]
zummc rw [countP_eq_zero]
zummd rw [decide_eq_true_iff]
zumme rw [downOverhead_eq]
zummf rw [e10]
zummg rw [e6]
zummh rw [edgeIdx_succ]
zummi rw [filter_eq_nil_iff]
zummj rw [foldr_cons]
zummk rw [g6]
zumml rw [hA6]
zummm rw [hAL]
zummn rw [hH]
zummo rw [hK]
zummp rw [hKc]
zummq rw [hNF]
zummr rw [hPe]
zumms rw [hR]
zummt rw [hR₁]
zummu rw [hUT]
zummv rw [harc0]
zummw rw [hc']
zummx rw [hc1]
zummy rw [hc]
zummz rw [hcab]
zumna rw [hcnt]
zumnb rw [hcode]
zumnc rw [hc₁]
zumnd rw [hc₃]
zumne rw [hd]
zumnf rw [hfe]
zumng rw [hfl]
zumnh rw [hh]
zumni rw [hi]
zumnj rw [hins]
zumnk rw [hje]
zumnl rw [hlast]
zumnm rw [hleaves]
zumnn rw [hm']
zumno rw [hm1]
zumnp rw [hm2]
zumnq rw [hm4]
zumnr rw [hnext]
zumns rw [hn₁]
zumnt rw [hoF0]
zumnu rw [hoN]
zumnv rw [hoW]
zumnw rw [hoff]
zumnx rw [hpar.1]
zumny rw [hpd]
zumnz rw [hper]
zumoa rw [hpq]
zumob rw [hq']
zumoc rw [hrec]
zumod rw [hreg]
zumof rw [hseg]
zumog rw [hsl]
zumoh rw [hsn]
zumoi rw [hwdef]
zumoj rw [hx2]
zumok rw [h₄]
zumol rw [i0_eq]
zumom rw [lo₅]
zumon rw [m13]
zumoo rw [m1]
zumop rw [m2]
zumoq rw [mem_F_iff]
zumor rw [mem_cross_opp_iff]
zumos rw [mi_n]
zumot rw [oW_def]
zumou rw [off_lerp]
zumov rw [r1]
zumow rw [slf_labSet2]
zumox rw [splitAll]
zumoy rw [ss_getD_snoc]
zumoz rw [subPoly_range]
zumpa rw [two_rpow_mul_two_rpow]
zumpb rw [v30]
zumpc rw [v44]
zumpd rw [v₇]
zumpe rw [w1]
zumpf rw [word_eq]
zumpg rwa [image_mir_image_mir]
zumph set m0 := c.nmem
zumpi set n := E.M.W.n
zumpk simp [HostItem.pts]
zumpl simp [M.vert_rot]
zumpm simp [eq_comm]
zumpn simp [slotPcs]
zumpo simp [stopsOf]
zumpp simp [xAt]
zumpq simp only at hb
zumpr simp only at hf
zumps simp only at hlt
zumpt simp only at ht
zumpu simp only at hxy
zumpv simp only at hy
zumpw split_ifs with h0 h1
zumpx subst e0
zumpy subst e1
zumpz subst e1 e2 e3
zumqa subst h'
zumqb subst hab
zumqc subst hk1 hk3 hk5
zumqd subst hki; tauto
zumqe subst hs0
zumqf subst htt; tauto
zumqg unfold ArrAt at harr
zumqh unfold Bd; grind
zumqi unfold BinitR at hb
zumqj unfold CRec.toSet CRec.lpos CRec.rpos
zumqk unfold Chain.sideTour at h
zumql unfold Chazelle.Chain.sideCross; simp_all
zumqm unfold Chazelle.Chain.sideE; grind
zumqn unfold Chazelle.Chain.sideTour Chazelle.Chain.sideIdx Chazelle.Chain.sideS
zumqp unfold Cost.ceilBeta
zumqq unfold CpRG at hr
zumqr unfold D0RG at h1
zumqs unfold DR at h
zumqt unfold FWin
zumqu unfold Fb
zumqv unfold Final.cut; simp_all
zumqw unfold FixB at hq
zumqx unfold FixR at hq
zumqy unfold GK at h
zumqz unfold HeadW at hq
zumra unfold Host.poly Polygon.vtx
      simp_all
zumrb unfold Keep at hr
zumrc unfold Lay.Written at ha
zumrd unfold LoopR at h
zumre unfold LvRG at h2
zumrf unfold Model.wb
zumrg unfold Mountain.orient; simp_all
zumrh unfold Nat.ModEq at h2
zumri unfold Polygon.commonEndpoints
zumrj unfold Scr; omega
zumrk unfold SetRG at hr
zumrl unfold SlotOK
zumrm unfold SlotW at hq
zumrn unfold WcW at hq
zumro unfold addLs; simp
zumrp unfold arcItems
zumrq unfold arcWtNat at hwt
zumrr unfold bary₁ bary₂ bary₃
zumrs unfold bary₁; simp
zumrt unfold bary₂; simp
zumru unfold bary₃; simp
zumrv unfold bary₃; simp_all
zumrw unfold bnd; grind
zumrx unfold brk
zumry unfold brk; simp_all
zumrz unfold b₁; grind
zumsa unfold candIdx
zumsb unfold candIdx; grind
zumsc unfold capDir; grind
zumsd unfold capOrigin; simp_all
zumse unfold cntInit
zumsf unfold cut; simp_all
zumsg unfold cutGran gradeGran
      grind
zumsh unfold det at h
zumsi unfold det at hx
zumsj unfold det; grind
zumsk unfold dirCode at h4
zumsl unfold dq; simp
zumsm unfold edgeIdx at h
zumsn unfold endDir; simp
zumso unfold eqT
zumsp unfold evOf; simp_all
zumsq unfold faceLocK; omega
zumsr unfold fv
zumss unfold gapLabel at hf
zumst unfold gapStarts
zumsu unfold hostWords at hW
zumsv unfold iIdx; grind
zumsw unfold idxI; grind
zumsx unfold inArcIdx; grind
zumsy unfold inp; grind
zumsz unfold interiorWalk
zumta unfold iv; grind
zumtb unfold jCOf; grind
zumtc unfold jCOf; simp_all
zumtd unfold kap; simp_all
zumte unfold keptC; grind
zumtf unfold keyCeil; simp
zumtg unfold keyOff; simp_all
zumth unfold lL1; grind
zumti unfold lerp; fun_prop
zumtj unfold loOf; simp_all
zumtk unfold locCost searchCost
      omega
zumtl unfold lsPr
zumtm unfold mk at e
zumtn unfold mk; grind
zumto unfold nfVal
zumtp unfold nh; grind
zumtq unfold normP; grind
zumtr unfold off
zumts unfold off; grind
zumtt unfold openList
zumtu unfold outE
zumtv unfold outS
zumtw unfold pcEdge pcA pcB
zumtx unfold posMir
zumty unfold posOf; grind
zumtz unfold ptK; omega
zumua unfold ptSym; grind
zumub unfold ratio; simp_all
zumuc unfold rayPt; fun_prop
zumud unfold regFree at hr
zumue unfold reorient
zumuf unfold revEdge; grind
zumug unfold rho; grind
zumuh unfold rho; simp_all
zumui unfold rk
zumuk unfold sOf Chain.sideS
      simp_all
zumul unfold scanLenR arcLenM lenOf
zumum unfold seg; simp_all
zumun unfold sideCcw sideCross sideDot
zumuo unfold sideChain; split_ifs
zumup unfold sideDot at hd
zumuq unfold sideDot; simp
zumur unfold sideDot; simp_all
zumus unfold sideInArc at hti
zumut unfold sideLeft sidePrev sideNext
zumuu unfold sideNext
zumuv unfold sidePt at hm
zumuw unfold sidePt at hx
zumux unfold sig; grind
zumuy unfold slotE; grind
zumuz unfold slotW; simp
zumva unfold stackS
zumvb unfold stopLabs
zumvc unfold stopPos; simp_all
zumvd unfold sw; omega
zumve unfold tJ; grind
zumvf unfold tourB
zumvg unfold trapPairs
zumvh unfold trapPairs; grind
zumvi unfold tw; simp
zumvj unfold upTf; simp_all
zumvk unfold wposOf; simp_all
zumvl unfold wupd; simp_all
zumvm unfold wv; grind
zumvn unfold xL at hy
zumvo unfold κBuild at hcost'
zumvp unfold σ; grind
zumwj simp only [Machine.upd_apply]
zumwr rw [hc₃]
zumwv simp only [upd_same]
zumwx rw [e₁]
zumwy simp [hr]
zumxd simp [regB, regI, upd]
zumxi simp only [regB, regI]
zumxk simp [h]
zumxp rw [hc₂]
zumxt simp only [regB, regI, upd, ite_true]
zumyf simp [regB, regI, upd, hq]
zumyg rw [hc']
zumym simp [wr, wrOK, Bone]
zumyp simp only [Config.nreg_mk, upd]
zumys rw [hc₆]
zumyt simp [chordL, regB, regI, upd, h3, h1, a]
zumyv rw [hc4]
zumyw rw [hc2]
zumyy simp [lMD, lCD, lNF, TBR, TLR, sw]
zumzd simp [regI, upd_other _ _ _ hq]
zumzf simp only [h, ↓reduceIte]
zumzh rw [s1, s2]
zumzk rw [hd']
zumzl simp [rpv, RPF, ht, ha, hs]
zumzm simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
zumzo simp only [Machine.upd_same]
zumzp rw [m₃]
zumzr simp only [Bchain, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]
zumzu simp only [okB, okI]
zumzv rw [e₃]
zumzy simp only [Config.nreg_mk]
zunac rw [g r hr, hI.fr r hr]
zunad rw [hc₀]
zunaf simp [h1, h2, h3, h4]
zunag rw [e₂]
zunah rw [rd_shoot, rd_shoot, s1, s2]
zunai rw [rd_shoot, rd_shoot, s3, s4]
zunaw simp [upd, hr]
zunaz rw [pow_succ', Perm.mul_apply]
zunba rw [hOut.1 ALLOC (fun h => by have := hHL _ h; unfold HSet ALLOC lO sw at this; omega)]
zunbb rw [hε]
macro "zvmwc" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [h] $[$l]?)
macro "zvmwd" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [dstI] $[$l]?)
macro "zvmwe" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [e] $[$l]?)
macro "zvmwf" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [upd] $[$l]?)
macro "zvmwg" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [e'] $[$l]?)
macro "zvmwh" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [View.key] $[$l]?)
macro "zvmwi" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [hm] $[$l]?)
macro "zvmwk" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [this] $[$l]?)
macro "zvmwl" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [hc1] $[$l]?)
macro "zvmwo" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [decide_eq_true_eq] $[$l]?)
macro "zvmwp" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [h1] $[$l]?)
macro "zvmwq" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [ZKeep, Bool.or_eq_true, decide_eq_true_eq] $[$l]?)
macro "zvmws" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [e1, e2] $[$l]?)
macro "zvmwt" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] $[$l]?)
macro "zvmxc" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [ChordOK] $[$l]?)
macro "zvmxe" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [hpt] $[$l]?)
macro "zvmxf" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp [rayPt] $[$l]?)
macro "zvmxg" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [hQn] $[$l]?)
macro "zvmxh" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [List.mem_cons, List.not_mem_nil, or_false] $[$l]?)
macro "zvmxj" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [hc₁] $[$l]?)
macro "zvmxl" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [h'] $[$l]?)
macro "zvmxm" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [he] $[$l]?)
macro "zvmxn" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [m₁] $[$l]?)
macro "zvmxo" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [bandOf, bDownDrv] $[$l]?)
macro "zvmxq" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [hn] $[$l]?)
macro "zvmxv" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [Nat.reduceAdd] $[$l]?)
macro "zvmxw" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [hv.CQ, show (Qof P).n = P.n from shear_n _ _] $[$l]?)
macro "zvmxx" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [h2] $[$l]?)
macro "zvmxy" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [e1] $[$l]?)
macro "zvmxz" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [hm1] $[$l]?)
macro "zvmyh" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [hcab] $[$l]?)
macro "zvmyi" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [rd, bandReg, bDownDrv, Nat.reduceMul, Nat.reduceAdd] $[$l]?)
macro "zvmyk" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [sw, Nat.reduceAdd] $[$l]?)
macro "zvmyq" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [hv] $[$l]?)
macro "zvmyr" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [← e] $[$l]?)
macro "zvmyz" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [hs] $[$l]?)
macro "zvmza" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [h1, h2] $[$l]?)
macro "zvmze" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [hA] $[$l]?)
macro "zvmzi" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [← h] $[$l]?)
macro "zvmzj" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [regB, regI, upd_same] $[$l]?)
macro "zvmzn" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [h0] $[$l]?)
macro "zvmzx" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [hM] $[$l]?)
macro "zvnak" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [e3] $[$l]?)
macro "zvnal" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [r1] $[$l]?)
macro "zvnam" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] $[$l]?)
macro "zvnan" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [decide_eq_false_iff_not] $[$l]?)
macro "zvnao" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [hQ] $[$l]?)
macro "zvnap" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [rayPt] $[$l]?)
macro "zvnar" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [hc3] $[$l]?)
