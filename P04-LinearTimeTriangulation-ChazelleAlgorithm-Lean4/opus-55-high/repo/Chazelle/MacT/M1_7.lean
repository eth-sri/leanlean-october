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

zg zuhdi have : ztixn := by_linarith
zuhdj have : ztmwt := hx.2
zuhdk have : ztpph := by_grind
zuhdl have : ztsmt := fun h => hx ztbzk
zuhdm have : ztumt := by unfold bandOf; omega
zuhdp have A₁ : ztdc := R₁ _ by_decide by_decide
zuhdq have Fr₁ : ztsbl := frameIO_of_frameB ztpbu F₁ k₁
zuhds have e1 : ztkzw := Chain.sideIdx_eq C C.sideBeta i
zuhdt have e1 : ztorj := Chain.sideCross_corner a v b
zuhdv have e2 := walk_next hs hm β ztpds ztkxj
zuhdy have h1 := hle i _ hi hj1 by_grind
zuhed have hHU := subset_region hU hHc hHfree hs₁H by_grind
zuhej have hL : ztulj := List.length_eq_zero_iff.1 hK
      subst hL
zuhem have hN1 : ztpgk := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
zuher have hcls := posClass_of he h0 h1 hy ztqbe
zuhfb have hkne := hk_succ_ne hM hF hfin by_grind hj
zuhfn have hrd := hI.rdisj _ p hL' hLp by_grind
zuhfo have hrd := hI.rdisj _ p hq2' hLp by_grind
zuhft have hwnbr := D.bot_top_nbr hP hl hml hmb ztvbx
zuhfv have hy : ztkpa := fun t => rfl
zuhfw have hδ : ztiwv := Nat.cast_nonneg _
      unfold psi
zuhgc have s : IScr kS := iscr_sw by_decide by_decide
zuhgk intro h; subst h; exact hr' by_decide
zuhgr intro ht; exact ⟨by_grind, ht.2⟩
zuhgs intro ht; exact ⟨by_simp_all, ht.2⟩
zuhht obtain ⟨hma, hmb⟩ := hmx by_grind
zuhhu obtain ⟨hr, hrU⟩ := rOf_spec ztnql
zuhin rcases xpClass_cases zteeu with h0 | h1 | h2
zuhio refine (FRS.ifF a ztpyn).mono by_simp zthi
zuhip refine (FRS.ifF a1 ?_).mono le_rfl ztb
zuhiq refine (FRS.ifF a2 ?_).mono le_rfl ztb
zuhir refine (FRS.ifF a3 ?_).mono le_rfl ztb
zuhis refine (IRS.ifT b0 cp).mono by_norm_num ?_
zuhiv refine FRS.seq (K₂ := 16) ztbbr ztiy
zuhix refine harc.2.2.2.2.2.2 p _ hp ztnsu ztlgl ?_
      grind
zuhiz refine ztgnz
      have : ztgth := by exact_mod_cast hp
zuhja refine ztkjd
      rw [hI.r10] at hk
      omega
zuhjb refine ztoob
      simp only [mem_ofPred_eq] at hp2
zuhjc refine ztoow
      rw [Chain.chainEdge_eq] at hp ⊢
zuhjd refine ztui
zuhjg right; refine ztooh; unfold sideE; grind
zuhjv rw [F₁.1 _ by_rfl]; exact hS.r12
zuhjx rw [List.getD_eq_getElem _ _ by_simp_all, List.getElem_map]
zuhkb rw [Nat.add_assoc, hwalk _ by_omega]
      grind
zuhkc rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt by_omega]; omega
zuhkd rw [Nat.add_zero, Nat.mod_eq_of_lt by_omega] at this
zuhkf rw [Nat.le_div_iff_mul_le by_omega]
zuhkg rw [Nat.mod_eq_of_lt by_omega] at hi0; omega
zuhko rw [abs_clampR_eq hr'0 zteue] at hcoord
      grind
zuhkq rw [bandSet Fs _ by_decide, hA₁]
zuhku rw [cover_of_ge by_omega] at hk; simp_all
zuhky rw [dist_rayPt _ ztbt hε0.le]; omega
zuhkz rw [dist_rayPt _ ztp hε0.le]; omega
zuhlc rw [e2, Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
zuhld rw [e2, Nat.mul_add_mod, Nat.mod_eq_of_lt by_omega]
zuhlg rw [f.1 _ by_decide]; exact j2
zuhlt rw [hn, vHole_six by_omega, Nat.mod_self]
zuhlu rw [hn₁, Nat.mod_eq_of_lt by_omega]; omega
zuhlv rw [hr _ by_decide by_decide, h1]
zuhlw rw [hr _ by_decide by_decide, h2]
zuhlx rw [hr _ by_decide by_decide, h3]
zuhmh rw [ite_eq_left ztffu]; exact Nat.mod_eq_of_lt by_omega
zuhmi rw [ite_eq_left zthrr]; exact Nat.mod_eq_of_lt by_omega
zuhmj rw [ite_eq_left ztjku, Nat.add_mod_right]; rfl
zuhmk rw [ite_eq_right by_omega]; exact Nat.mod_eq_of_lt by_omega
zuhml rw [ite_eq_right by_simp_all]
zuhmo rw [ite_eq_right hnU1]; exact Nat.mod_eq_of_lt by_omega
zuhmp rw [ite_eq_right hnU]; exact Nat.mod_eq_of_lt by_omega
zuhmt rw [k2 _ by_omega by_omega]; omega
zuhmu rw [k4' _ by_decide by_decide, c3AB]
zuhmv rw [k4' _ by_decide by_decide, c3J]
zuhmw rw [k4' _ by_decide by_decide, c3SB]
zuhmy rw [kp2 31 by_omega ztpq, o₁]
zuhnb rw [mul_comm]; exact Nat.log_mul_base by_norm_num by_omega
zuhnc rw [n_subPoly, Nat.sub_add_cancel by_omega, Nat.mod_self]
zuhne rw [q1 _ by_decide]; exact hE
zuhnf rw [q1 _ by_decide]; exact k6
zuhnh rw [qm _ by_omega by_omega]; grind
zuhnj rw [rd3.2 _ by_omega by_omega]; grind
zuhnp rw [upd_other _ _ _ ztkfa]
      omega
zuhob set Fg := F ztkx
zuhod set K := nk ztd S ztcz with hKdef
zuhoi set j := rankF ztse L i with hj
zuhou simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
      refine ztpfm
zuhql unfold DEnv.Kc
      have : ztixy := Nat.pow_le_pow_right by_norm_num ht.le
zuhqw unfold numComp
      rw [card_quot_eq_of_eqvGen_iff _ _ ztnzq]
zuhrg unfold tourV
      rw [Nat.add_zero, Nat.mod_eq_of_lt by_omega]
zuhrt apply hbad
      refine countOK_mono hfin ztfhn ztfhn hgood
zuhru apply hright hmb by_grind
      intro ε hε hεle
zuhsd by_cases g1 : c₂.nreg zthl < c₂.nreg 140010
zuhsf by_cases g2 : c₂.nreg 140010 < c₂.nreg zthl
zuhsl by_cases h1 : c.nreg L < c.nreg zttz
zuhsr by_cases h2 : c.nreg zttz < c.nreg L
zuhsu by_cases hA : 0 < σ * ztdgg
zuhtb by_cases hj : j = ztg % Q.n
zuhti by_cases hpres : c.nreg ztkt < c.nreg ztnx
zuhty exact (e5 _ h1).trans zttjn
zuhub exact h.no_vertex _ ztkmv hy'in1 hy'in2 hin.1.le hin.2.le
zuhuc exact h.no_vertex _ ztkmx hy'in1 hy'in2 hin.1.le hin.2.le
zuhud exact hA.2.1 j j' h1 h1' ztqpb zttib
zuhue exact hM.region_subset_of_sector hc hU hp ht hf by_grind
zuhuf exact hM.region_subset_of_sector hc hU' hp' ht' hf' by_grind
zuhuh exact hreg' r hra by_omega by_omega by_omega by_omega
zuhui exact left_stretch_pt J hP by_omega ht0 ht1 hx
zuhuk exact_mod_cast by_grind
zuhul exfalso
      refine Chazelle.Jordan.simple_openEdge_ne_vtx hQ he ht ztjhw ?_
zuhum exfalso
      refine Chazelle.Jordan.simple_openEdge_ne_vtx hQ he ht ztjhy ?_
zuhuq filter_upwards [Ioo_mem_nhdsGT ztbbe] with t ht
zuhur filter_upwards [Ioo_mem_nhdsGT ztcjf] with s hs
zuhus filter_upwards [Ioo_mem_nhdsGT ztja] with s hs
zuhut filter_upwards [Ioo_mem_nhdsGT ztto] with s hs
zuhuw have : ztcjz := by exact_mod_cast hp
      grind
zuhux have : ztddy := by exact_mod_cast h
      linarith
zuhuy have : ztehm := by exact_mod_cast by_grind
      grind
zuhuz have : ztehm := by exact_mod_cast hlt
      grind
zuhva have : ztfzy := by exact_mod_cast by_grind
      grind
zuhvb have : ztgtl := by exact_mod_cast h
      linarith
zuhvc have : ztgtp := by exact_mod_cast hp'
      linarith
zuhvd have : ztknl := by exact_mod_cast by_grind
      grind
zuhve have : ztmrf := by exact_mod_cast hd
      linarith
zuhvf have : ztsas := Nat.le_mul_of_pos_right _ by_omega
      omega
zuhvg have : ztsik := by exact_mod_cast this
      omega
zuhvh have : ztsof := Nat.le_mul_of_pos_right _ hR
      grind
zuhvl have A₆ : ztfkx := g₆ _ by_decide
zuhvm have F₀ : ztuky := exec_frameM x₀ by_decide
zuhvo have aA : ztdc := ar _ by_decide
zuhvp have b2 : ztizr := by exact_mod_cast a2
zuhvq have e1 : x.1 < C.top.1 := by_nlinarith
zuhvr have e1 : zticw := Nat.cast_sub hle
      grind
zuhvu have eTL : ztguk := hI₁.hin _ by_trivial
zuhvv have eXA : ztfdr := sideCross_swap _ _
zuhvw have elC : ztgui := stp_co_keep hI by_omega
zuhvy have h1 : ztmrz := by exact_mod_cast hv.1
zuhwb have h2 : ztmse := by exact_mod_cast hv.2
zuhwc have h3 : ztizy := Nat.le_pow_clog by_norm_num m
zuhwe have h72 : r ≠ 72 := by_omega
zuhwf have hA : ztlxc := by_omega
      refine ztugw
zuhwg have hA1 : ztdc := f₁.1 _ by_rfl
zuhwh have hA1 : ztdc := q1 _ by_decide
zuhwi have hAW : A₀ ≤ W := by_omega
zuhwj have hA₁ : ztdc := f₁ _ by_decide
zuhwk have hA₁ : ztdc := k₁' _ by_decide
zuhwl have hA₁ : ztdc := r₁ _ by_decide
zuhwm have hA₁' : ztdc := f₁ _ by_decide
zuhwn have hB0' : ztujv := lt_of_le_of_ne zttuv ztvar
zuhwr have hF : ztgty := F₂plus_subset J hS₂
zuhwv have hHb : H ⊆ W.boundaryᶜ := by_grind
zuhwz have hL2 : 0 < L₂ := by_omega
zuhxb have hN2 : 2 ≤ N := by_omega
zuhxh have hR1 : 1 ≤ R := by_omega
zuhxk have hRo : ztrfp := hsys.regionsIn_open subset_rfl hR
zuhxr have hVU : V ⊆ U := by_grind
zuhxu have hW6 : 6 ≤ W := by_omega
zuhxv have hWn : ztcjy := Chain.sideWalk_n _ _
zuhxw have hZ1 : 1 ≤ Z := by_omega
zuhxz have hamem : a ∈ J.right.set := by_grind
zuhya have hb1 : bit = 1 := by_omega
zuhyc have hbig : ztscm := hD.sinv.big _ List.mem_cons_self
zuhyd have hc : E.M.counted _ := hcnt.2 ztvbz
zuhye have hc : ztizf := F_adm hN ztmhu
zuhyg have hc0A : ztpmq := g₀ 9999 by_norm_num
zuhyh have hcut : ztuvd := harc.2.2.2.2.2.1 _ hin
zuhyi have hc₁S : c₁ ∈ S₂ := by_simp_all
zuhyk have hd' : ztmsp := Nat.dvd_add hs.1 dvd_rfl
zuhyl have he0 : e.hgt = 0 := by_omega
zuhym have hee2 : 2 ≤ ee := by_omega
zuhyn have hen : ztmvo := Nat.mod_lt _ by_omega
zuhyq have hgpos : 0 < g := by_linarith
zuhyr have hi2 : ztdrl := Nat.mod_lt _ by_omega
zuhyt have hj0A : ztsmj := NFLoc.seq_lt hN hvA
zuhyv have hk : ztidw := C.sideIdx_le _ _
zuhyx have hkt : k = top := by_omega
zuhyy have hl := hnear _ hmem by_grind by_grind
zuhza have hl1 : ztpgm := by exact_mod_cast by_grind
zuhzc have hle : ztmrh := by exact_mod_cast hgt
zuhzd have hle : ztmry := by exact_mod_cast hlt
zuhzj have hna : a ∉ J.right.set := by_grind
zuhzk have hne : u ≠ r := by_grind
zuhzm have hnγ : P.n ≤ s.γ := by_omega
zuhzo have hp : ztbou := by exact_mod_cast hA.1
zuhzp have hp1 : p.1 ≠ v := by_grind
zuhzq have hp1 : pa ≤ p := by_grind
zuhzs have hp2 : p ≤ pb := by_grind
zuhzt have hp2 : p.2 ≠ u := by_grind
zuhzu have hp2 : p.2 ≠ v := by_grind
zuhzv have hpl : ztmrt := by exact_mod_cast hp
zuhzx have hpt : ztrgz := Chazelle.Chain.sidePt_zero _ _
zuhzz have hq : ps.length ≤ Nmax := by_linarith
zuiab have hq' : q < st.tl := by_omega
zuiad have hqN : q < N.arcs.length := by_omega
zuiaf have hqn : ztumb := hR.q_lt i hin
zuiag have hqn : ztx := shear_n _ _
zuiah have hs : ztxx := lt_min by_linarith by_linarith
zuiai have hs1 : ztdrm := lt_of_le_of_lt ztgh by_norm_num
zuiak have hsl := hsec _ hmem hne by_grind
zuial have hs₂r : ztsmm := lt_of_le_of_lt ztgh by_linarith
zuiap have hun : ztrgx := hI.inv.qlt _ hht
zuiaq have hv : ztmuo := hI.hin _ ztbc
zuiar have hvn : v ≠ G.nv := by_omega
zuias have hw : ztmtr := simple_vtx_succ_ne hP hj
zuiav have hwv : ztbrq := Chazelle.Chain.sidePt_zero _ _
zuiaw have hy : ztsci := Nat.le_mul_of_pos_right _ hΛ
zuiax have hρ' : ztuvf := by_linarith
      subst hρ'
zuiay have hℓ : ℓ ≤ 2 := by_omega
zuibh have n1 : K1 ≠ ALLOC := by_decide
zuibj have o70 : Src.Out ztboh := Or.inr by_norm_num
zuibk have r1 : ztsei := hf.2.2.2.2 _ zttmm
zuibl have w₀ : ztsdd := ‹_›
zuibs intro hj
      have : ztskw := by_omega
      grind
zuido rcases Nat.lt_or_ge n zts with h' | h'
zuidq rcases Nat.lt_or_ge p ztcc with h' | h'
zuids rcases Nat.lt_or_ge ztbs N with h2 | h2
zuidt rcases Nat.lt_or_ge ztda n with h1 | h1
zuidu rcases Nat.lt_or_ge ztfqb ztfk with h | h
zuidv rcases Nat.lt_or_ge zts m with h | h
zuidx rcases glue_thr J zteg with h' | h'
zuieo rcases le_total ztciq ztcir with h | h
zuies rcases sign_eq_or_eq_neg hσ ztquj with h' | h'
zuiet rcases ztiaw with rfl | rfl | rfl
zuiew refine RS.out hI holeL_scr ex by_omega ho ztufs
zuiex refine harc.2.2.2.2.2.2 _ _ by_omega by_linarith by_linarith ?_
zuiez refine spec_ifLtN_false ztdlw ?_
      refine spec_step ztlfh ztczm
zuifc refine ztbfn
zuife refine ztgw
zuiff refine ztiwc
      dsimp only [Rep.neg]
      grind
zuigj rw [F₁.2.2.1 a by_omega, hm₀]
zuigk rw [F₂.2.2.1, F₁.2.2.2.1 a by_omega]
zuigl rw [K5 _ by_simp]; omega
zuigp rw [Machine.upd_other _ _ _ by_grind]
zuigs rw [Nat.mod_eq_sub_mod hpn, Nat.mod_eq_of_lt by_omega]
zuihb rw [capDir_eq J ztvtp] at hans
zuihp rw [eE, eH]
      exact ztfvx
zuihv rw [edge_zero P by_omega] at hqi
zuihx rw [fix1 301 by_norm_num] at hj
zuiis rw [hI.hin _ by_trivial]; grind
zuijt rw [hf57.2.2.2.2 _ by_omega]; grind
zuijz rw [hk₀, hA2 1 by_omega]
zuikd rw [hmem _ by_omega, tabUpd_0]
zuikf rw [hn]; exact J.whole.vertex_snd_le_top by_omega
zuiki rw [hostChain_vertex, add_steps_mod ztjkk hi]
zuikv rw [i34, k1 R by_omega]
zuikz rw [ite_eq_left ztvuo, ite_eq_left hb]
zuila rw [ite_t by_omega, ite_t by_omega]
zuilg rw [k1 _ by_omega]; omega
zuilk rw [logPt_congr hm by_omega] at hv
zuilp rw [min_eq_left by_linarith, max_eq_right by_linarith]
zuilq rw [min_eq_right by_linarith, max_eq_left by_linarith]
zuilr rw [mod_pred_mod hn₂ _ by_omega]
      rfl
zuilv rw [oT.1 _ by_simp, w10]
zuilw rw [oT.1 _ by_simp, w11]
zuilx rw [oT.1 _ by_simp, w12]
zuily rw [oT.1 _ by_simp, w13]
zuilz rw [o₈.1 _ by_simp, b12]
zuimc rw [pad_ge by_omega] at this
      omega
zuimg rw [r2 5 by_simp]; omega
zuimh rw [r2 6 by_simp]; omega
zuimi rw [radius_eq_of_model ztqpm, hM']
      simp_all
zuimv rw [upd_other _ _ _ by_grind]
zuino rw [← hoff _ le_rfl by_omega]
zuinq set A := ztbe % W.n with hAdef
zuinr set A := ztlv % W.n with hAdef
zuiob set VT := connectedComponentIn zttkf v with hVT
zuioc set Y := F * G * ztbhm
zuioh set p := ztbe % M.W.n with hp
zuioj set x : WPos := zthj with hx
zuiok set x : WPos := ztxt with hxdef
zuiol set x := L₀.getD i ztt with hx
zuioo set xs : WPos := ztcjw with hxs
zuiop set ε := min ztzr T with hε
zuiqe unfold subInnerPot; rw [ite_eq_right by_omega]
zuiqf unfold unwrapK; rw [ite_eq_right ztjpx]
zuiqg unfold unwrapK; rw [ite_eq_right ztqep]
zuiro by_cases hd : DirFwd P l ztdnf
zuirp by_cases hd : isdn ztjk = 1
zuirr by_cases hk : kR P v ztctl
zuisn exact (h1 ztdlz).2 hρ1
zuisr exact Nat.mod_lt _ by_omega
zuist exact Or.inr zthvx
zuite exact core hA' hB' hAB' h ztqqt
zuitf exact core hB' hA' ztvaq by_grind h
zuitg exact div_nonneg_of_nonpos by_linarith by_linarith
zuith exact h1.inter ztgjy
zuitj exact hI.hm _ by_omega
zuitl exact hNC _ hp _ hc' by_omega
zuitp exact hr by_decide
zuitr exact not_mem_set_of_abs by_grind
zuitu exact ok_ptAns J Q zttwf q h
zuitv exact spec_nil hw₁ zteyr
zuitw exact stp_mem_full ztvdb h by_grind hUc hxU
zuitx exact wrap_succ by_omega
zuiuf have  := chain_eq ztvsr ztvst ztvss
      grind
zuiug have : i = L := by_omega
zuiuh have : p = ztdv := by_grind
zuiui have : p = ztdy := by_grind
zuiuj have : ztfzw := by exact_mod_cast hle
zuiuk have : ztgtj := by exact_mod_cast hJ
zuiul have : ztphh := by exact_mod_cast hℓ
zuium have : ztscn := Subset.antisymm ztwdj hST
zuiuo have Fa' := frameIO_of_frameB ztiki Fa k₂
zuiup have Fa' := frameIO_of_frameB ztikj Fa k₂
zuiuq have G₁ := sc_of_two by_omega by_omega R₁
zuiuu have e2 := mul_pos hs0 ztwfv
      linarith
zuiuv have e244 := r1 244 by_decide by_decide
zuiuy have h := hT.no_vertex _ ztubj
      grind
zuivd have h1 := hinner 1 one_pos by_omega
zuivk have h3 : ztpgv := List.length_map _
zuivn have hA := arcs_le_one_of_empty hN hGM ztqcq
zuivo have hA := endPos_attach hN hk ztlp
zuivq have hAW : ztcga := hI.hw.1 ALLOC
zuivr have hAW : ztizb := hI.hw.1 ALLOC
zuivs have hAW : ztpnj := hI₂.hw.1 ALLOC
zuivu have hE74 : ztrzv := one_le_pow₀ hE1
zuivw have hE₇ := hE₆.frame f₇ e₇.wb_right by_decide
zuivy have hF := hM.sys _ ztobr ztjxv
zuivz have hFT := hM.sys _ zttpm ztvuf
zuiwa have hG1 : ztido := hG.frame ztfyh
zuiwc have hGM : ztebh := Or.inl ztexm
zuiwd have hGα : ztebh := Or.inl ztrac
zuiwf have hK₁ : ztukh := hK.fix hI₁
zuiwi have hL0 : ztopz := Nat.cast_nonneg _
zuiwl have hLU0 : ztixv := Nat.zero_le _
zuiwn have hM : ztgpz := walkAx_chainModel hP
zuixb have hTA := hlo hlo'
      refine zticd
zuixe have hU' : ztsct := hU
      simp_all
zuixg have hWA : ztcga := hw.1 ALLOC
zuixi have hWn : ztbdm := walk_n Q
zuixr have hctx₁ := hctx.transport g0 by_simp_all ztchd
zuixu have hd : ztrzo := sub_pos.2 huv
zuixz have hg'0 : ztehf := Nat.cast_nonneg _
zuiya have hg0 : ztcrf := Nat.cast_nonneg _
zuiyb have hg0 : ztehf := Nat.cast_nonneg _
zuiyg have hk₁ : ztpkz := hk.congr by_grind
zuiyl have hn : ztbdm := DownMath.walk_n Q
zuiym have hn : ztbld := cm_n J.right
zuiyn have hn : ztdh := C.sideWalk_n C.sideBeta
zuiyy have hpv : Pv pc := by_grind
zuiyz have hq₃ : ztgan := hq₂.congr by_grind
zuizb have hr := DownBase.rankF_succ keepW ztt hi
zuizc have hr := DownBase.rankF_succ ztbdh ztt hi
zuize have hr := rankF_succ ztse ztt hi
zuizm have huA' := hUA' ztmml
      refine ztreu
zuizp have hw₁ : ztmtb := hw.congr' by_grind
zuizq have hw₂ : ztsbh := hw.congr' by_grind
zuizs have hxD := hin x by_grind by_grind
zuizw have hκ : ztiww := Nat.cast_nonneg _
zuizx have hμ0 : ztfzp := Nat.cast_nonneg μ
zuizy have hσ : ztim := dirOf_cases _
zuizz have i0 := hI.hin 83000 by_norm_num by_norm_num
zujaa have iv₈ := symPtIn_keep iv₇ f₈ by_decide
zujaz intro h; exact absurd h by_omega
zujdm rcases Nat.lt_succ_iff_lt_or_eq.mp ztkxo with hi | hi
zujdq rcases eq_or_lt_of_le ztgmb with e | e
zujdr rcases hcov ztvtk with h | h
zujdu rcases hloc2 by_simp_all with h' | h'
zujdz rcases lt_or_eq_of_le ztitn with h | h
zujeu refine (mem_triangle_iff_bary hdet).2 ztrdf
zujey refine frame_of_frameM ztuyu R' by_omega ?_ ?_
zujfd refine region_below hQ hFam hne hR ztdp
zujff refine spec_ifLtN_false ztbvr ?_
zujfi refine spec_ifLtN_true ztbvr ?_
zujfk refine spec_instr ztoxg fun _ => ?_
zujfp refine spec_seq ztdja
zujfq refine spec_seq zteyf
zujfr refine spec_step ztjkd zthxf
zujfs refine spec_step ztowu fun hw1 => ?_
zujfu refine ztbqx
      unfold bandOf ioBands oracleBands kernelBands
zujfv refine ztcya
zujfx refine zteyl
zujgp rw [List.getD_eq_getElem _ _ by_omega]
zujhc rw [Nat.clog_le_iff_le_pow by_norm_num, pow_add]
zujhe rw [Nat.mod_eq_of_lt by_omega] at this
zujhl rw [abs_of_nonneg by_linarith] at hd
zujhm rw [abs_of_nonpos by_linarith] at hd
zujhp rw [bandSet Ft _ by_decide]
zujhu rw [div_le_one_of_neg by_linarith]; linarith
zujio rw [h]; exact ztgny
zujje rw [hke.2 by_omega] at hx
zujjo rw [hn]; exact_mod_cast by_grind
zujjp rw [hng, cover_of_ge by_omega]
zujkf rw [ite_eq_right by_decide] at h1
zujkg rw [ite_eq_right by_omega]; omega
zujki rw [ite_eq_right ztqud]; linarith
zujlu rw [vd, ite_eq_left by_grind]
zujlv rw [vd, ite_eq_right by_omega]
zujmn set D := c₀.nreg ztbey with hD
zujmr set N := nk ztd S R
zujnf set σ := dirOf ztql with hσdef
zujng set σ := dirOf ztvjj with hσ
zujtc by_cases hcut : M.IsCut F ztdj
zujtd by_cases hcut : M.IsCut F ztk
zujus exact Geometry.lerp_mem_segment _ _ by_norm_num by_norm_num
zujut exact eq_endpoint_of_vtx_mem_edge hP zthp zthp hp1
zujuu exact h m hm x ztvyw
zujvc exact iterate_le_iterate hA B _ ztbg
zujvd exact key _ ztmmv hr ztkwa
zujvi exact sideCcw_asymm hn0 ztjhl h3 h2
zujvk exact sideSectorIn_of_faces by_grind ztuik hclp hf
zujvm exact ztbwm
zujvq have : ztiot := q9999
      omega
zujvr have : ztixm := by_grind
      simp_all
zujvs have : ztixv := Nat.zero_le _
zujvt have : ztmqx := Nat.cast_nonneg _
zujvu have : ztmtl := by_grind
      grind
zujvv have : ztpgx := by_linarith
      simp_all
zujvw have : ztphb := by_linarith
      simp_all
zujvx have : ztupw := hu
      omega
zujwa have A1 := f1 ALLOC by_decide
zujwc have K₁ := hK.frame f₁ by_decide
zujwd have K₃ := K₂.frame f₃ by_decide
zujwe have K₄ := K₃.frame f₄ by_decide
zujwf have R₃ : ztcqm := by_simp_all
zujwk have a' : ztmxc := by_omega
zujwl have a0 : ztsgi := by_grind
zujwm have a15 : ztmwl := by_grind
zujwn have a2 : ztehk := by_linarith
zujwo have a4' : zteif := a4
zujwp have a9 : zteif := ha
zujwq have a9 : ztlxy := by_simp_all
zujwt have b32 : ztizk := by_simp_all
zujwu have b6 : ztusi := by_simp_all
zujwv have c55 : ztoqr := by_rfl
zujwy have e : ztids := by_simp_all
zujwz have e : ztiwr := by_simp
zujxa have e := hm' zter by_omega
zujxb have e0 := mod3_cases hK ztkxn
zujxc have e1 : ztehz := k1
zujxd have e1 : ztlxu := by_omega
zujxe have e1 : ztphi := by_nlinarith
zujxf have e1 := mul_pos ztwfz zteau
zujxg have e2 : ztphj := by_nlinarith
zujxh have e2 : ztsna := by_nlinarith
zujxi have e3 : ztusu := k4T
zujxj have e3 := mod3_cases hK ztiav
zujxk have e30 := hreg' ztssz by_omega
zujxl have e4 : ztlan := by_ring
zujxm have e40 : ztlyd := by_omega
zujxn have e6 : ztlyk := hk6
zujxo have eA3 : ztbox := by_grind
zujxr have g1 : ztdxr := by_simp_all
zujxs have g1 := hfx.r40 1 by_norm_num
zujxx have h' : ztidm := by_tauto
zujxy have h0 : ztsiy := by_omega
zujxz have h0 := h 0 by_norm_num
zujya have h0 := hk 0 by_norm_num
zujyb have h0' : ztuup := by_grind
zujyd have h1 : ztcfy := by_positivity
zujye have h1 : ztpne := by_omega
zujyf have h1 : ztslo := by_omega
zujyi have h1' := lt_of_lt_of_le h1 ztff
zujyj have h2 : zteho := by_grind
zujyk have h2 : zteho := by_linarith
zujyl have h2 : ztpgs := by_grind
zujym have h2' : zteif := h2
zujyn have h2' : ztsby := by_omega
zujyp have h201 : ztset := by_simp_all
zujyq have h2g : ztiws := by_positivity
zujys have h2m : ztmsi := by_omega
zujyt have h3x : ztupj := by_grind
zujyu have h9 : zteif := hra
zujyw have hA' : ztdxq := hA₀
zujyx have hA4' : ztpnt := by_omega
zujyy have hAW : ztsfi := by_omega
zujza have hA₁ := f₁.1 ALLOC by_decide
zujzb have hA₂ := f₂.1 ALLOC by_decide
zujzc have hB : ztlwx := rfl
zujzd have hE0 : ztgaa := by_omega
zujze have hE₅ := hE₄.step e₅ by_decide
zujzf have hF1 : ztutu := by_simp_all
zujzg have hFam : ztpgz := hN.1
zujzj have hHn : ztknj := hostPoly_n
zujzk have hL0 : ztrze := by_positivity
zujzl have hLL : ztfkk := List.length_append
zujzm have hLpos : ztujs := by_simp_all
zujzn have hM1 : ztrzw := by_grind
zujzo have hMR : ztpgq := by_simp_all
zujzp have hM₁ : ztezg := hC.hM₂
zujzr have hN' : ztpih := by_decide
zujzw have hQ : ztgqf := hB.reach_iff
zujzy have hR : ztpkk := rfl
zujzz have hR4 := hR3.of_same s4 ztfl
zukaa have hR5 := hR4.of_same s5 ztfl
zukab have hR6 := hR5.of_same s6 ztfl
zukac have hR7 := hR6.of_same s7 ztfl
zukad have hR₁ : ztpkk := rfl
zukag have hS' : ztmvz := by_grind
zukah have hS' : ztrgs := by_grind
zukai have hS' : ztsjk := by_grind
zukal have hT' : ztsaz := by_omega
zukam have hTu : ztsco := rfl
zukan have hW : ztoqd := rfl
zukao have hW' : ztsal := by_omega
zukap have hW1 : zteht := by_omega
zukaq have hW3 : ztpik := by_omega
zukar have hW4 : ztpil := by_omega
zukas have hWn : ztixz := hWh
zukat have hX : ztmub := by_omega
zukav have hX1 : ztphy := by_omega
zukax have haK : ztsdg := by_grind
zukbb have hatt := hL.2.2.1 _ ztdoo
zukbc have hay' : ztsnu := hay
zukbe have hb1 : ztplm := by_omega
zukbf have hbW : ztshv := by_omega
zukbh have hc : ztpmo := zteyq
zukbi have hc' : ztmxd := hc
zukbj have hc' : ztmxe := hc
zukbk have hce : ztsdx := by_grind
zukbr have hd0 : ztpnz := by_simp_all
zukbt have hdir : ztmvm := by_grind
zukbv have he8 := h8 e by_simp
zukbw have heq := Finset.eq_of_subset_of_card_le hsub by_simp_all
zukca have hfl' : ztpnf := hfl
zukcb have hg : ztsai := by_omega
zukcc have hg' : ztlaw := by_omega
zukcd have hg1 : ztiwz := by_simp_all
zukce have hg2 : ztpig := by_omega
zukcf have hge : ztrhn := by_omega
zukcg have hge : ztsio := by_omega
zukch have hgg : ztpot := by_omega
zukci have hgm : ztrgr := by_omega
zukck have hhn : ztmra := by_simp_all
zukcl have hi : ztdrl := by_omega
zukcm have hi : ztmvy := by_omega
zukcn have hi : ztsji := by_omega
zukco have hi0 : ztfla := by_omega
zukcp have hi2 : ztsja := by_omega
zukcr have hj := Nat.mod_lt ztty hm2
zukcs have hj := Nat.mod_lt ztwz ztcdw
zukcu have hjL : ztsjn := by_omega
zukcv have hjS : ztsjt := ztfxc
zukcw have hk : zteie := by_omega
zukcx have hk1 : ztpmi := by_omega
zukcy have hk2 : ztuot := by_omega
zukcz have hkj : ztska := by_grind
zukdc have hlo : ztmth := by_omega
zukdh have hlt : ztsjm := by_omega
zukdk have hm : ztcrl := hI.hm
zukdl have hm : ztdjm := by_grind
zukdm have hm : ztlam := hC.2.2.2.1
zukdn have hm : ztlyn := hC.2.2.2.1
zukdr have hmem₃ : ztckd := by_grind
zukds have hmem₄ : zteid := by_grind
zukdt have hmid := hopen ztcn by_grind
zukdu have hmin : ztskl := by_omega
zukdv have hmn : ztsat := T.hm
zukdw have hm₁ : ztwh := rfl
zukdx have hn : ztfku := by_omega
zukdy have hn : ztfzz := by_omega
zukea have hn' : ztrzf := by_omega
zukeb have hn3 : ztpij := by_omega
zuked have hne : C.Nonempty := by_simp_all
zukej have hone2 : zthoo := by_simp_all
zukek have hp : ztplb := by_omega
zuken have hp0 : ztidy := by_omega
zukeo have hp1' : ztgva := hp1
zukep have hpos : ztehd := by_grind
zukeq have hpos : ztfzn := by_simp_all
zuker have hpos : ztmsj := by_positivity
zukes have hpos : ztmso := by_omega
zukeu have hpt' : ztlyr := hpt
zukev have hpt' : ztlys := hpt
zukex have hptU : ztuus := by_grind
zukey have hpv : ztshz := hp
zukez have hq := Nat.mod_lt ztpd hn
zukfa have hq' : ztknh := by_simp_all
zukfb have hq' : ztunl := hprg
zukfc have hqF : ztmwj := by_grind
zukff have hr' : ztplw := rfl
zukfg have hrn : ztppo := by_omega
zukfh have hroom' : ztrgd := hroom
zukfi have hroom' : ztrge := hroom
zukfl have hs := hstat d by_grind
zukfm have hs' : ztkzo := by_grind
zukfn have hs'1 : ztsaa := by_omega
zukfo have hs0' : ztcfv := hs0
zukfp have hs1 : ztdrm := by_simp_all
zukft have hsq : ztixi := by_nlinarith
zukfu have hsr : ztjan := by_grind
zukfv have hss : ztppv := by_omega
zukfw have hss : ztslt := by_grind
zukfx have hsum' : ztym := hsum
zukfy have hsε₀ := lt_of_lt_of_le hsε ztff
zukfz have ht : ztbhh := by_grind
zukga have ht : ztrhk := by_omega
zukgb have ht : ztsfe := by_omega
zukgd have ht' : ztkzp := by_simp_all
zukgf have ht0 : ztbhh := by_grind
zukgg have htl : ztjaq := by_omega
zukgh have htp : ztfkp := by_grind
zukgk have huv : ztpqh := by_grind
zukgm have hvpt : ztlab := by_grind
zukgn have hvpt : ztlac := by_grind
zukgr have hwaq : ztulr := rfl
zukgs have hwf := S.hwf _ ztpzp
zukgt have hw₁ : ztidr := by_grind
zukgu have hw₃ : ztlaj := by_simp_all
zukgv have hx0 : ztmqw := by_positivity
zukgw have hx0 : ztrzu := by_positivity
zukgx have hx0 : ztsmx := by_linarith
zukgz have hxK : ztpql := by_omega
zukha have hxe2 : ztjau := by_omega
zukhg have hz : ztuon := hctx.2.2.2.2.2.1
zukhh have hz'2 : ztsnp := by_simp_all
zukhi have hz2 : ztpqs := rfl
zukhj have hzD : ztmxg := by_grind
zukhk have hzD := hopen ztcn by_grind
zukhn have hβ : ztpiw := by_grind
zukho have hδ' : ztblc := hδ
zukhp have hδ0 : ztcfy := by_grind
zukhq have hδ0 : ztcfy := by_linarith
zukhr have hδ0 : ztcfy := by_positivity
zukhs have hε1 : ztpqx := by_grind
zukht have hμ : ztphw := by_grind
zukhu have hτw := tpos_lt J.whole ztbv
zukhv have hℓ : ztsoj := by_omega
zukhw have hℓ' : ztsok := by_omega
zukia have k4 : ztlxs := hK.2.2.2.1
zukib have ka : ztgto := rfl
zukic have kb : ztgtn := rfl
zukid have keep1 : ztgvb := by_grind
zukie have k₂ : ztkov := by_simp_all
zukif have lj : ztsax := by_omega
zukig have lk : ztsay := by_omega
zukih have m12 : ztsfg := by_simp_all
zukii have m13 : ztmut := by_simp_all
zukij have mem : ztlca := b₁
zukik have m₂ : ztckc := by_grind
zukil have nA : ztpip := by_decide
zukim have q1 := h1 ztdso by_simp
zukin have q1 := h1 ztjfz by_simp
zukio have q1 := h1 ztjga by_simp
zukip have q5 := g ztfz by_omega
zukiq have r72 := hG2.rbase 42 by_omega
zukir have s36 : zturv := by_grind
zukis have t : ztrhg := by_omega
zukit have t1 : ztrhp := by_omega
zukiu have t1 : ztsia := by_omega
zukiv have v46 : ztizj := by_grind
zukkb nlinarith [mul_nonneg hYd ztqsu]
zukke obtain rfl : ztpol := by_omega
zukkf obtain rfl : ztsie := by_omega
zukkg obtain rfl : ztsif := by_omega
zuknc rcases ztfcl with hj | rfl
zuknd rcases ztfyl with h2 | h2
zukne rcases ztfym with hpe | hpe
zuknf rcases ztfyn with h2 | h2
zukng rcases ztkxp with hlt | rfl
zuknh rcases ztkxs with h | h
zukni rcases ztta with h' | h'
zuknj refine Set.ncard_lt_ncard ?_ ztpcd
      refine ztebc
zuknk refine chordListAt_append ztdp ?_ ?_ ?_
zuknl refine hpost _ ?_ ztez rfl
zuknm refine kqIsOne_irs hI₁ hK₁ ztyq ztyq
zuknp refine regB_other m _ f ztdp
zukns refine viaGen d by_omega ?_ by_omega
zuknt refine viaGen ztfqv by_omega ?_ by_omega
zuknu refine ztfwo
