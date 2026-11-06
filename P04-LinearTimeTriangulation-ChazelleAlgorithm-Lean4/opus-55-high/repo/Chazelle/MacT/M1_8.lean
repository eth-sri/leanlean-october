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

zg zuknv refine ztkw
zukog rintro rfl; exact hr by_decide
zukou rw [C.sideWalk_vtx_tour β by_omega]
zukpe rw [Fb.1 _ by_decide]
zukpl rw [List.getElem?_rotate by_omega]
zukpy rw [SweepPrim.walk_vtx_tour C by_omega]
zukrf rw [edge_eq _ by_omega]
zukrj rw [fB.1 _ by_decide]
zuksb rw [hA'eq]
      refine ztlvp
zuktz rw [he _ by_omega]
zukuy rw [hm _ by_omega]
zukyr rw [t4 _ by_simp]
zukzb rw [w2 _ by_decide]
zukzn set hi := min ztmyt ztr
zukzp set k := ztkem / ztken
zukzr set lo := max ztmys p
zukzx set q := ztoh % M.W.n
zukzz set u := ztuet / ztdgh
zulab set z' : Point := ztkho
zulbq unfold emitted
      refine List.Nodup.filterMap ztmjh List.nodup_range
zulda apply List.ext_getElem by_simp
zuldb apply Real.rpow_le_rpow_of_exponent_le by_norm_num
zuldh apply ht2 t le_rfl by_omega
zuldm by_cases hs : sel ztsf
zuldr by_contra hobs
      exact hnot ztopx
zulec exact C.vertex_segment_subset by_omega
zulef exact Or.inl by_grind
zuleg exact Or.inl by_omega
zulek exact Or.inl ztedt
zulel exact Or.inl ztjjc
zulem exact Or.inl ztlwc
zulen exact Or.inr by_simp_all
zuleo exact Or.inr zteds
zuleq exact WalkEmbed.corner_not_mem_box C ztbt hvbox
zuler exact WalkEmbed.corner_not_mem_box C ztp hvbox
zulet exact bpt_of_range by_omega
zuleu exact corner_not_mem_box C ztbt h1
zulev exact corner_not_mem_box C ztp h1
zulex exact dom_left J ht by_simp_all
zulfa exact fin1 hq hM' by_simp_all
zulfd exact h.open_mem _ by_linarith by_linarith
zulfe exact h.open_mem _ ztnss ztnst
zulff exact hH.open_mem _ by_grind by_grind
zulfg exact hH.open_mem _ by_linarith by_linarith
zulfh exact hR.2.2.2 _ by_decide by_decide
zulfj exact hch'.open_mem _ by_grind by_linarith
zulfk exact hch'.open_mem _ by_linarith by_grind
zulfl exact hch.open_mem _ by_linarith by_linarith
zulfp exact mem_dom_of_region C hV by_grind
zulfq exact mem_segment_iff_weights.2 by_grind
zulft exact selectLast_self by_grind
zulfu exact slb_evVal zthco hVb zttrr
zulfy exact_mod_cast Nat.lt_succ_iff.1 ztjps
zulgl have  := by_omega
zulgm have : ztcrc := by_simp_all
zulgn have : ztfki := by_grind
zulgo have : ztgpy := by_decide
zulgp have : ztgub := by_omega
zulgq have : ztguw := by_nlinarith
zulgr have : ztiwt := by_linarith
zulgs have : ztpgw := by_linarith
zulgt have : ztsdb := by_simp_all
zulgu have : ztsje := by_omega
zulgv have : ztsjf := by_grind
zulgw have : ztskx := by_simp_all
zulgx have : ztsld := by_omega
zulha have RFall := RF₁.trans zthrz
zulho have hBB := sideDot_self_pos ztqxb
zulio have hLr' := hLr by_omega
zuliq have hM' := walkAx_interiorModel ztttm
zuljn have hb := C.set_subset_box ztowl
zuljr have hb := hostKeys_bounds ztqqh
zulkw have hno := best₁.2.2 by_omega
zulla have hp := Nat.two_pow_pos ztbs
zullp have hx := abs_lt.1 ztjxr
zullw have hσ := SweepStop.dirOf_cases' ztfb
zulnu nlinarith [norm_nonneg ztcod]
zuloa refine Or.inl ztexp
zulob refine PFr.of_eq hf ztez ztts
zuloc refine PFr.of_eq hf2 ztez ztts
zulof refine chainModel_congr ?_ ztrql ?_
zuloi refine hcut 1 ztp ?_
zulon refine spec_seq ztcow
zuloo refine spec_seq zthmr
zulop refine spec_use ztlrs ?_
      grind
zuloq refine tendsto_nhdsWithin_iff.2 ztgnx
zulor refine ylexTest_exec c ztep ztep
zulot refine ztboa
zulov refine ztcxz
zulow refine ztcyc
zuloy refine ztzy
zulpe rw [List.getLast_cons ztjjq]
zulpf rw [List.take_of_length_le by_grind]
zulqn rw [min_eq_left by_omega]
zulrj set M := chainModel ztgi
zulvo apply Geometry.point_ext _ ztqqx
zulvq apply hhalfR 1 ztp
zulvr apply hhalfR _ ztbt
zulvt apply hnv 0 by_omega
zulvv apply hnv ztr hk
zulwr exact .seq e1 ztdsh
zulws exact BitIs.const_zero by_grind ztggd
zulwt exact BitIs.const_zero by_simp by_omega
zulwu exact BitIs.const_zero by_simp_all ztggd
zulwv exact C'.sideWalk_vtx_tour _ by_omega
zulww exact C.not_mem_set_of_mem_dom by_grind hset
zulxa exact C₂.sideWalk_vtx_tour _ by_omega
zulxc exact IRS.ifF h2 by_grind
zulxd exact IRS.ifT h2 by_grind
zulxk exact absurd by_simp_all h.left_not
zulxl exact absurd by_simp_all h.right_not
zulxn exact absurd hC.symm ztnou
zulxo exact absurd hM zttbw
zulxs exact absurd ztfdh hnc₀
zulxt exact absurd ztfzj hnc₀
zulxu exact absurd ztnyd ztwag
zulxv exact absurd ztrjz by_omega
zulxy exact band9_gran by_omega by_omega
zulyc exact by_omega
zulye exact closure_mono hsub ztswl
zulyg exact div_pos by_nlinarith hp
zulyh exact div_pos_of_neg_of_neg by_nlinarith hn
zulzi exact nk1 q zteo
zulzk exact pcEdge_lt by_omega _
zulzm exact point_ext zteqe by_simp
zulzn exact q1 r zthft
zulzq exact s13.1 x ztbaw
zulzs exact scat_at h1 by_grind
zulzw exact st_addL_self by_omega x
zulzy exact wr_sw by_norm_num by_norm_num
zumdt have hl := ztuxi
zumhx left
      refine ztopo
      simp_all
zumhy left; exact ztooi
zumiy refine IRS.ite ztefa ztefa
zumja refine Set.Finite.union ?_ ztvqm
zumjc refine ifEqN_ne ztdmc ?_
zumjf refine le_trans ztjmu hunc
zumjg refine le_trans ztjmu hwt
zumjh refine le_trans ztuyt ?_
zumjq refine spec_ifLtN_false ztdcg ?_
zumjv refine spec_ifLtN_true ztdlw ?_
zumjw refine spec_ifLtN_true ztlhn ?_
zumjx refine spec_ifLtN_true ztlhv ?_
zumjy refine spec_instr ztrjd by_simp_all
zumka refine spec_skip by_omega ?_
zumkc refine spec_step ztqaf ztczm
zumkd refine ztbfi
zumkh refine ztbqx
zumki refine ztbwk
zumkj refine ztbwl
zumkm refine ztddu
zumkn refine ztddv
zumkq refine ztexh
zumkr refine zteyo
zumks refine zthnd
zumku refine ztkli
zumkx right
      refine ztkmz
      simp_all
zumky right; refine ztboa
zumkz right; refine ztuhw
zumwm rw [v6 _ by_decide by_decide by_decide by_decide, w5r _ ztzg ztzf]
zumwn rw [hr _ by_decide]
zumwu rw [g _ by_norm_num by_norm_num]
zumxa rw [he _ by_omega]
zumxb rw [g _ by_decide]
zumxr rw [c5c _ by_decide by_decide by_decide by_decide by_decide by_decide]
zumxs rw [hr _ by_decide by_decide]
zumxu rw [kk _ by_omega]
zumya rw [upd_other _ _ _ by_omega]
zumyb rw [k _ by_tauto]
zumye rw [k _ by_tauto by_decide]
zumyj rw [hfx _ ztbc]
zumyl rw [Machine.upd_other _ _ _ by_omega]
zumyo rw [keep _ by_norm_num by_norm_num]
zumyu rw [k _ by_decide]
zumyx rw [fm _ by_omega]
zumzg rw [hk _ by_decide]
zumzq rw [hk _ by_omega]
zumzs rw [q _ ztbeh]
zumzt rw [p52 _ by_decide]
zumzw rw [hfx _ by_tauto]
zunaa rw [r₁ _ by_decide by_decide by_decide]
zunab rw [ite_eq_left by_omega]
zunaj rw [qr _ by_decide by_decide by_decide by_decide by_decide]
zunaq rw [R₄ _ by_decide, R₃ _ by_decide by_decide by_decide, n₂]
zunas rw [k56 _ ztxg]
zunat rw [kk6 _ by_omega]
zunau rw [he _ ztbei]
zunav rw [g _ by_norm_num]
zunax rw [hr _ by_omega]
zunay rw [hr _ ztnf]
zunbc rw [he _ by_omega by_omega]
zunbd rw [hkeep _ by_omega by_omega by_omega by_omega]
zunbi rw [kk _ by_omega by_omega]
zunbw rw [upd_other _ _ _ by_decide]
zunbx rw [r₂ _ by_decide by_decide by_decide]
zunby rw [k21 _ by_norm_num by_norm_num by_decide]
zuncd rw [hJ.2 _ by_omega, m₁]
zunci rw [keep2 _ by_omega by_omega by_omega]
zunco rw [k2m _ by_omega]
zunct rw [g₁ _ by_decide]
zuncu rw [d09, hmm, keep _ by_norm_num by_norm_num]
zuncy rw [F₇.1 _ by_decide]
zundd rw [fr₂.1 _ by_simp_all]
zunde rw [r₆ _ by_omega]
zundf rw [r₂ _ by_omega]
zundj rw [a1, a2, hr _ by_omega by_omega, hr _ by_omega by_omega, p44, p45]
zundr rw [hlow3 _ by_omega, dlow _ by_omega]
zunds rw [M₅ _ by_omega, M₄ _ zteem]
zundt rw [he _ by_omega, he _ by_omega]
zunea rw [a₃ _ by_norm_num by_norm_num by_simp, q2]
zuneb rw [h8 _ by_norm_num by_norm_num]
zunef rw [hmem _ by_omega by_omega]
zuneo rw [m₂, f₁.2.2.1, upd_other _ _ _ by_omega, upd_other _ _ _ by_omega]
zunep rw [upd_other _ _ _ ztvbn, upd_other _ _ _ hrn, hA, hn]
zuner rw [Machine.upd_apply, show dst + lo + ztfqf = dst + c.nreg 30015 by omega]
zunfa rw [d09, keep _ by_norm_num by_norm_num]
zunfb rw [x02, kRq _ by_decide by_decide by_decide, kHq _ by_decide by_decide, f08]
zunfj rw [R _ by_decide by_decide by_decide by_decide]
zunfk rw [R₃ _ by_decide by_decide by_decide by_decide]
zunfl rw [f₉ _ by_norm_num by_norm_num by_norm_num by_norm_num]
zunfs rw [g6 _ by_omega]
zunfu rw [hreg _ by_decide]
zunfv rw [hf.1 _ by_decide]
zunfw rw [g₂ _ by_decide, g₁ _ by_decide, h4, f₂.2.2.1, hm₁]
zunfx rw [rd_drv, rd_drv, hr₃' _ by_omega by_omega, hr₂' _ by_omega by_omega]
zunfy rw [hlow5 _ by_omega]
zunga rw [hlow3 _ by_omega]
zungc rw [ite_eq_left by_omega, show A₀ + q - A₀ = q by omega]
zungg rw [hr _ by_norm_num]
zungm rw [s4.1 _ by_simp, s3.1 _ by_simp, s2.1 _ by_simp, r53]
zungo rw [agE _ by_omega]
zungs rw [R₁ _ by_decide]
zungu rw [hpc _ by_omega]
zungy rw [mem5 _ by_omega]
zunha rw [r3 _ by_decide]
zunhe rw [h4r _ by_omega by_omega by_omega]
zunhi rw [g _ by_norm_num, hI.rK]
zunho rw [g₅ _ by_decide, bA]
zunhq rw [r₄ _ by_decide, r₃ _ by_decide by_decide, f₂ _ by_decide]
zunhv rw [hfe.1 _ by_decide, h1]
zunhw rw [hfe.1 _ by_decide, hA]
zunhx rw [s2.1 _ by_simp, r20]
zunhz rw [f₆.1 _ by_decide, n₅]
zunic rw [hI.hin _ ztbc, hE.wn]
zunik rw [h4.1, hf4.1 _ ztjqo, h3 _ by_omega, r1]
zunin rw [g₆ _ by_decide, K5 _ by_simp, g₁ _ by_omega]
zunio rw [k₂' _ by_norm_num, k₂' _ by_norm_num, hm, h21]
zuniq rw [s4.1 _ by_simp, s13.1 _ by_simp, h21, hR4.one]
zunis rw [r20, s2.1 _ by_simp, s1.1 _ by_simp, h20]
zunit rw [r₅ _ by_omega, r₅ _ by_omega, j4, u32]
zuniu rw [r₃ 120050 by_decide, r₃ 120051 by_decide, r₃ 120052 by_decide]
zuniv rw [r₁ 120050 by_decide, r₁ 120051 by_decide, r₁ 120052 by_decide]
zunix rw [g1 83012 by_simp, g1 83013 by_simp, f12, f13]
zunjd rw [ite_eq_right by_omega, ite_eq_right by_omega, ite_eq_right by_omega, ite_eq_right by_omega]
zunjf rw [r₁ _ by_decide, r₁ _ by_decide, h01, hE.r85]
zunjg rw [g 50200 by_decide, g 50202 by_decide, m₁, v₁]
zunjm rw [kk3 _ by_omega by_omega by_omega by_omega, g1 _ by_omega]
zunjn rw [hm _ by_omega by_omega]
zunjo rw [hE2, ← hc2 i by_omega, he2, he1]
zunjs rw [kc _ by_norm_num by_norm_num]
zunjt rw [k₂' _ by_norm_num by_decide]
zunju rw [K4 210001 by_norm_num by_norm_num]
zunjv rw [K4 210002 by_norm_num by_norm_num]
zunjz rw [show d₃.nreg ALLOC = d₂.nreg ALLOC from g₃ _ by_decide]
zunkb rw [band_of_range (lo := 19) by_omega by_omega, mem_drvBands]
zunkm rw [r₂ r by_grind by_omega]
zunko rw [rayPt_rayPt, show d + ztkej = s by ring]
zunku rw [o₄.1 _ by_simp, g3 _ by_omega by_omega, h05]
zunkx rw [show e = ztugk by rw [← he0]]
zunli rw [r1 _ by_decide by_decide]
zunma rw [← a4 t ht, ← b4 t by_omega]
zunmb rw [← a5 t ht, ← b5 t by_omega]
zunmg rw [M5 _ by_omega, Machine.upd_other _ _ _ by_omega]
zunmh rw [qm _ by_omega by_omega, qm _ by_omega by_omega]
zunmk rw [Machine.upd_other _ _ _ ztvat, hxr1, hR1.one]
zunmm rw [hAL, K3 _ by_decide by_decide by_decide by_decide by_decide]
zunmr rw [o₂.1 _ by_simp, g _ by_omega, h100]
zunms rw [o₄.1 _ by_simp, o₃.1 _ by_simp, v₂]
zunmt rw [(o18.trans o₉).1 _ by_simp, h90]
zunmu rw [o₃.1 _ by_decide, o₂.1 _ by_decide, v100]
zunmv rw [o₃.1 _ by_decide, o₂.1 _ by_decide, v103]
zunmw rw [o₃.1 _ by_decide, o₂.1 _ by_decide, v97]
zunmx rw [o₃.1 _ by_decide, o₂.1 _ by_decide, v98]
zunmy rw [o₃.1 _ by_decide, o₂.1 _ by_decide, v101]
zunmz rw [o₃.1 _ by_decide, o₂.1 _ by_decide, v96]
zunna rw [o₃.1 _ by_decide, o₂.1 _ by_decide, v90]
zunnj rw [r₄ _ by_decide, f₃.1 _ by_decide, hc₂]
zunnv rw [h _ by_omega]
zunnw rw [hf5.2.2.2.2 _ by_omega]
zunnx rw [hf3.1 _ ztjqx]
zunny rw [h4r _ ztcuh]
zunnz rw [rd5.1 _ by_omega]
zunoa rw [hE1, ← hc1 i by_omega, he1]
zunol rw [h.low _ by_omega]
zunon rw [tlow _ by_omega]
zunor rw [r₄ _ by_decide, r₃ _ by_decide by_decide]
zunos rw [g₂ _ by_norm_num by_norm_num, k₁ _ by_norm_num]
zunou rw [kc _ by_decide by_decide, kb _ by_decide]
zunox rw [g₄' _ by_norm_num by_norm_num, r₃ _ by_decide]
zunpa rw [m4 _ by_omega]
zunpb rw [hmem6 _ by_omega]
zunpd rw [r₅ _ by_omega by_omega by_omega by_omega, E₄.h60]
zunpe rw [r₅ _ by_omega by_omega by_omega by_omega, E₄.h61]
zunpf rw [r₅ _ by_omega by_omega by_omega by_omega, E₄.h67]
zunpg rw [r₅ _ by_omega by_omega by_omega by_omega, E₄.h68]
zunph rw [r₅ _ by_omega by_omega by_omega by_omega, E₄.h69]
zunpi rw [F₄.1 _ by_decide]
zunpj rw [k2r _ by_omega by_omega, k1 _ by_omega]
zunpk rw [k4r _ by_omega]
zunpt rw [r₃ _ by_decide by_decide, g₂ _ by_decide]
zunpu rw [mPA _ by_omega]
zunqe nlinarith [mul_nonneg hs'0 ztqts]
zunqh rw [hI.hm _ by_omega]
zunql rw [k3 _ by_omega, kp2 i by_omega ztpq]
zunqm rw [show w = zthla from Prod.ext rfl hwy]
zunqw simp only [upd_same, upd_other _ _ _ ztvau]
zunqx rw [f₂.1 _ by_decide]
zunqz rw [e207, R 205 by_decide by_omega, h205]
zunrf rw [q20, R₃.1 _ by_decide, c11]
zunrj rw [h590, h5r _ ztcul, r1']
zunrl rw [hf6.2.2.2.2 _ by_omega, hf5.2.2.2.2 _ by_omega]
zunrm rw [hfr2.1 _ ztggo, hf1.1 _ ztggp]
zunrn rw [h50', hf5.1 _ ztcuh, r1']
zunro rw [hf3 _ ztbsl, hf2.1 _ ztbsl]
zunrp rw [he zttcm by_omega, he zttco by_omega]
zunrw rw [g₁ _ by_decide, h4, hm₁]
zunsi rw [upd_other _ _ _ by_omega, upd_same]
zunsv rw [upd_other _ _ _ by_norm_num, hA₁₁]
zunsw rw [s13.1 _ by_simp, h21, hR3.one]
zuntb rw [ite_eq_right by_omega, ite_eq_right by_omega, hsym]
zuntg rw [r₄ _ by_decide, v84, hq₄.one]
zunti rw [R₁ _ by_decide, R₁ _ by_decide]
zuntl rw [hfx 81021 ztbc, hfx 81019 ztbc]
zuntm rw [hfx 81021 ztbc, hfx 81025 ztbc]
zuntn rw [a₅ _ by_norm_num by_norm_num by_simp, q4]
zuntv rw [reg4 i by_omega, hin i hi]
zunua rw [k2 pE2 ztp, k2 pH2 ztbt]
zunub rw [w2 _ by_decide, k3 _ by_simp]
zunug rw [em6, s3 _ by_omega, em4]
zunuv rw [hE0, ← hc0 i by_omega]
zunvb rw [m₂, K2 210001 by_norm_num by_norm_num]
zunvp rw [r₃ _ by_omega by_omega, E₂.h60]
zunvq rw [r₃ _ by_omega by_omega, E₂.h61]
zunvr rw [r₃ _ by_omega by_omega, E₂.h67]
zunvs rw [r₃ _ by_omega by_omega, E₂.h68]
zunvt rw [r₃ _ by_omega by_omega, E₂.h69]
zunvu simp only [upd_other _ _ _ ztkxa]
zunvz rw [g₆ _ by_norm_num by_norm_num, p1]
zunwa rw [Function.update_self, cnt2F_succ, ite_eq_left ztp]
zunwc rw [Function.update_self, lst2F_succ, ite_eq_left ztp]
zunwf rw [hr _ by_decide by_decide by_decide by_decide]
zunwh rw [v65, hrot, ite_eq_right by_omega]
zunwl rw [R₄ _ by_decide by_decide, a140]
zunwn rw [g1, g _ by_norm_num by_norm_num]
zunwp rw [f₇ _ by_norm_num by_norm_num by_norm_num by_norm_num]
zunwx rw [div_le_one by_linarith]
zunxm rw [R₂.1 _ by_decide, q30]
zunxo rw [(hmap ztpw).1]
zunxu rw [g _ by_norm_num, hI.r101]
zunya rw [hf'.1 _ by_decide, h2]
zunye rw [F₂.2.2.1 a by_omega, m₁]
zunyj rw [r₂ r by_omega by_omega by_omega]
zunys rw [r₄ _ by_decide by_decide by_decide]
zunyt rw [Fa.1 _ by_decide, dA]
zunyw rw [tourV_left J by_omega, tourV_left_zero]
zunyx rw [tourV_right J by_omega, tourV_right_zero]
zunyy rw [e1, hmem5 _ by_omega]
zunyz rw [hr _ by_decide, h20]
zunzb rw [g₂ _ by_decide, q104]
zunzg rw [hfe.1 _ by_decide, hCA]
zunzh rw [hfe.1 _ by_decide, hK]
zunzi rw [s13.1 _ by_simp, h26]
zunzj rw [s1.1 _ by_simp, h20]
zunzk rw [s23.1 _ by_simp, r40]
zunzl rw [s1.1 60020 by_simp, h20]
zunzo rw [R₄ _ by_omega, i₃]
zunzp rw [F₁.1 _ by_decide, hAl]
zunzq rw [F₁.1 _ by_decide, h1]
zunzr rw [F₁.1 _ by_decide, hμ]
zunzt rw [hAL, F₄.1 _ by_decide]
zunzu rw [hJ.1 _ by_decide, v60]
zunzv rw [R₁ _ by_decide by_decide by_decide]
zuoaa rw [hI.hin _ ztbc, hE.k0]
zuoab rw [hI'.hin _ ztbc, hE.wn]
zuoac rw [hI'.hin _ ztbc, hE.k0]
zuoad rw [hI'.hin _ ztbc, hE.pn]
zuoae rw [hI'.hin _ ztbc, hE.k1]
zuoaf rw [h.hin _ ztbc, hE.k5]
zuoag rw [h.hin _ ztbc, hE.k7]
zuoah rw [h.hin _ ztbc, hE.k3]
zuoai rw [h.hin _ ztbc, hE.k1]
zuoaj rw [af' _ by_norm_num, x33]
zuoam rw [o₇.1 _ by_simp, a23]
zuoan rw [o₅.1 _ by_simp, a05]
zuoao rw [o₅.1 _ by_simp, v₄]
zuoaq rw [o113.1 _ by_simp, h98]
zuoar rw [o113.1 _ by_simp, h100]
zuoas rw [o113.1 _ by_simp, h101]
zuoat rw [o113.1 _ by_simp, h96]
zuoau rw [o₁₃.1 _ by_decide, h05]
zuoav rw [o₁₃.1 _ by_decide, h06]
zuoaw rw [o₃.1 _ by_decide, v102]
zuoax rw [g₁ _ by_omega, R.h91]
zuobc rw [wv _ by_omega, hb]
zuobd rw [hmem₅ a by_omega, mem₂]
zuobe rw [r₇ _ by_decide by_decide by_decide]
zuobf rw [reg4 30 by_omega, c30]
zuobg rw [reg4 31 by_omega, c31]
zuobh rw [reg4 32 by_omega, c32]
zuobi rw [reg4 33 by_omega, c33]
zuobj rw [reg4 37 by_omega, c37]
zuobo rw [hR _ ztp, c5R0]
zuobp rw [hR _ by_omega, c5R1]
zuobq rw [hR _ by_omega, c5R2]
zuoby rw [upd_other _ _ _ ztu]
zuocc rw [hM1, k1 R by_omega]
zuocf rw [hnm₂ t by_omega, hc₁]
zuocp rw [hr4 _ by_omega by_omega]
zuocv rw [rd5.2 _ by_omega by_omega]
zuodh rw [K4 210003 by_norm_num by_norm_num]
zuodi rw [K4 210004 by_norm_num by_norm_num]
zuoej rw [hr _ by_omega by_omega]
zuoel rw [lr _ by_decide by_decide]
zuoeo rw [g _ by_omega zteqg]
zuoeq rw [k _ by_omega by_omega]
zuoet rw [g _ ztbeh zteqg]
zuofi rw [fr2 _ ztksz by_rfl]
zuofj rw [fr2 _ ztzc by_rfl]
zuofn rw [tv_lt by_omega, m3]
zuofr rw [k12₂ _ by_norm_num by_norm_num]
zuoga rw [h₉, upd_ne by_norm_num]
zuogb rw [keep q h1 by_omega]
zuogg rw [k2 _ by_omega by_omega]
zuogm rw [List.getD_eq_getElem _ _ by_omega]
zuogs rw [ko _ by_decide by_decide]
zuoho rw [fr1 F₆ by_decide]
zuohw rw [h3r r ztnvd]
zuoia rw [h4r _ ztcul]
zuoid rw [hr5 _ by_omega]
zuoie rw [r1 _ zteqi]
zuoig rw [hf1.2.2.2.2 _ by_omega]
zuoii rw [k67 _ by_omega]
zuojc rw [← Real.rpow_add by_norm_num]
zuojv rw [f₂ _ by_decide]
zuojw rw [r₄ _ by_decide]
zuojx rw [v _ by_decide]
zuokd rw [k₁ r ztcmk]
zuokh rw [kb _ by_decide]
zuokj rw [f₁ _ by_decide]
zuokn rw [tr _ by_decide]
zuoli rw [fr2 _ ztnf]
zuolj rw [r1 _ ztcuo]
zuolv rw [s3.1 _ by_simp]
zuome rw [f.1 _ by_decide]
zuomh rw [f₁.1 _ by_decide]
zuomj rw [g₂ _ by_decide]
zuomn rw [ag0 _ by_omega]
zuomv rw [hI₁.hin _ ztbc]
zuonf rw [o₁.1 _ by_decide]
zuonj rw [k ALLOC by_decide]
zuonv rw [k₁' _ by_decide]
zuooh rw [q1 _ by_decide]
zuooj rw [m3 a by_omega]
zuool rw [hg67 _ ztqfx]
zuoor rw [e _ by_decide]
zuoos rw [w2 ALLOC by_decide]
zuoov rw [hk r by_omega]
zuoox rw [r2 4 by_simp]
zuopa rw [hm3 a by_omega]
zuope rw [f ALLOC by_decide]
zuopf rw [fr₃ _ by_decide]
zuopi rw [key _ by_omega]
zuopw rw [hstate _ by_simp]
zuopx rw [g5 9992 by_omega]
zuoqs rw [Function.update_of_ne by_omega]
zuoqz rw [ite_eq_right ztkal]
zuorn rw [Nat.floor_eq_iff by_positivity]
zuosm rw [div_lt_one_of_neg by_linarith]
zuosn rw [div_lt_one by_linarith]
zuosp rw [Nat.clog_le_iff_le_pow by_norm_num]
zuosu rw [ite_eq_left ztqeq]
macro "zvmww" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [r₁ _ by_decide] $[$l]?)
macro "zvmyc" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [Nat.mod_eq_of_lt by_omega] $[$l]?)
macro "zvmyd" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [ite_eq_right by_omega] $[$l]?)
macro "zvmyn" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [ite_eq_right by_omega, ite_eq_right by_omega] $[$l]?)
macro "zvmzz" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [hm _ by_omega] $[$l]?)
macro "zvnae" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [Nat.mod_eq_sub_mod by_omega, Nat.mod_eq_of_lt by_omega] $[$l]?)
macro "zvnee" l:(Lean.Parser.Tactic.location)? : tactic => `(tactic| rw [ite_eq_right (by norm_num : ¬ ztekg)] $[$l]?)
