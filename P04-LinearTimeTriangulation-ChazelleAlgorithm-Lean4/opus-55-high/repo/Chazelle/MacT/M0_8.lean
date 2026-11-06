module

public import Chazelle.MacT.Base

public section

set_option hygiene false

zn ztivb (∀ r, r ≠ 160034 → c'.nreg r = c.nreg r)
ztivc (∀ r, r ≠ 170017 → c2.nreg r = c1.nreg r)
ztivd (∀ r, r ≠ 170030 → c2.nreg r = c1.nreg r)
ztive (∀ r, r ≠ 170031 → c3.nreg r = c2.nreg r)
ztivf (∀ r, r ≠ 190037 → c'.nreg r = c.nreg r)
ztivg (∀ r, r ≠ 70228 → c'.nreg r = c.nreg r)
ztivh (∀ r, r ≠ a → c'.nreg r = c.nreg r)
ztivi (∀ r, r ≠ d → c'.nreg r = c.nreg r)
ztivj (∀ r, r ≠ fR → c'.nreg r = c.nreg r)
ztivk (∀ r, r ≠ ipT → c'.nreg r = c.nreg r)
ztivl (∀ r, r ≠ x → c'.nreg r = c.nreg r)
ztivm (∀ r, ¬ ClimbRG r → c'.nreg r = c.nreg r)
ztivn (∀ r, ¬ CpRG r → c1.nreg r = c.nreg r)
ztivo (∀ r, ¬ CpRG r → c4.nreg r = c.nreg r)
ztivp (∀ r, ¬ GoodRG r → c'.nreg r = c.nreg r)
ztivq (∀ r, ¬ LbRG r → c1.nreg r = c.nreg r)
ztivr (∀ r, ¬ MarkRG r → c'.nreg r = c.nreg r)
ztivs (∀ r, ¬ PassRG r → c'.nreg r = c.nreg r)
ztivt (∀ r, ¬ SetRG r → c'.nreg r = c.nreg r)
ztivu (∀ r, ¬ SplitRG r → c1.nreg r = c.nreg r)
ztivv (∀ x, sideInArc a b x → ¬ M.IsCut F x)
ztivw (∀ x, x ≠ 140000 → c'.nreg x = c.nreg x)
ztivx (∀ x, x ≠ 150071 → d'.nreg x = d.nreg x)
ztivy ⟨.box _, ⟨v38, v39⟩, h36, ?_⟩
ztivz ⟨6 + tau Q u L h1 h2 + e, h₂⟩
ztiwa ⟨D, rfl, hSR, Or.inr (D.isTrap.topVtx_mem hP D.free)⟩
ztiwb ⟨N, q, fun g => G.vert (par g)⟩
ztiwc ⟨by dsimp only [Rep.neg]; linarith, ?_, rfl⟩
ztiwd ⟨by rw [hwbq] at hx; exact hx, ?_⟩
ztiwg ⟨fun x hx' => ?_, fun x hx' hf => ?_⟩
ztiwk ⟨lt_of_lt_of_le ht₀ h1, h2, fun t ht0 ht1 => ?_⟩
ztiwl ⟨r, hr, hb, key w hwc r hb ?_⟩
ztiwm ⟨rayPt _ τ s₀, ⟨hs₀c, ?_⟩, ?_⟩
ztiwn ⟨rfl, fun i h1 h2 => ?_, rfl, rfl⟩
ztiwp ((p + 1 : ℕ) : ℝ) < n
ztiwq ((p + 1 : ℕ) : ℝ) = M.W.n
ztiwr (0 + N - 1) % N = N - 1
ztiws (0 : ℝ) < (2 : ℝ) ^ g
ztiwt (0 : ℝ) < d
ztiwu (0 : ℝ) < u
ztiwv (0 : ℝ) ≤ δ
ztiww (0 : ℝ) ≤ κo
ztiwx (1 : ℝ) ≤ (2 : ℝ) ^ g
ztiwy (1 : ℝ) ≤ L₁
ztiwz (1 : ℝ) ≤ g
ztixa (14 : ℕ) ∈ oracleBands
ztixb (2 : ℝ) ^ (13 : ℝ) = 8192
ztixc (N.region r).arcs.getD 0 0 ∈ (N.region r).arcs
ztixd (chainModel C).param _ ⟨x.edge, h₁⟩ ≠ 0
ztixe (e : ℝ) = (y.edge : ℝ) - x.edge
ztixf (f : ℕ) < N
ztixg (g' : ℝ) < M₂.W.n
ztixh (hostPoly Q S R).Simple
ztixi (lam : ℝ) ≤ (lam : ℝ) ^ 2
ztixj (p : ℝ) + 1 ≤ 2 * C.m + 6
ztixk (p : ℝ) < C.m
ztixl (p : ℝ) < k
ztixm (p : ℝ) < n
ztixn (p : ℝ) ≤ 0
ztixo (st.F E \ {cs E.M E.Q E.N c}).Nonempty
ztixp 0 < (chainModel C).W.n
ztixq 0 < (chainModel J.left).W.n
ztixr 0 < (interiorModel Q).W.n
ztixs 0 < C.radius - C.top.2
ztixt 0 < r
ztixu 0 < rδ J
ztixv 0 ≤ S.L * U
ztixw 1 ≤ hc
ztixx 128 * P.n + 3 ≤ W
ztixy 2 ^ t ≤ 2 ^ E.d0
ztixz 256 * P.n + 16 ≤ W
ztiya 8 * P.n + 32 ≤ W
ztiyb 90070 ≤ r ∧ r < 90100
ztiyc BestOK P.n V.s V.m c₁
ztiyd C.m < (H.pts P.n).length
ztiye C.m < p + 1
ztiyf Exec P W _ c c₄ _
ztiyg Frame DrvR.drvBands c₁ c₂ k₂
ztiyh Frame {bDownDrv} c₂ c₃ k₃
ztiyi H' = H
ztiyj HostAt m' (m bw) H
ztiyk L ≤ P.n
ztiyl N.chord k = N.chords[k]
ztiym N.chords[i] = N.chord i
ztiyn NFWithin c.nmem _ _ N
ztiyo R + 30 + j = R + (30 + j)
ztiyp R₁ ⊆ R
ztiyq R₂ ⊆ R
ztiyr S ⊆ F
ztiys ShotList.ShotPre X Ok RS P W c₁
ztiyt W.n = 2 * C.m + 7
ztiyu a = 0 ∧ b = 0
ztiyv a = s.edge + M.param Q s
ztiyw a ≠ v
ztiyx bandOf r = bSign
ztiyy c'.nreg ALLOC ≤ c1.nreg ALLOC + k
ztiyz c'.nreg sB = c.nreg sB
ztiza c.nmem _ = s.m₀ _
ztizb c.nreg ALLOC ≤ E.W
ztizc c2.nreg 160024 = 1
ztizd c4.nreg 130001 = 1
ztize co.nreg lB = c.nreg lB
ztizf cs M Q N i ∈ M.Adm
ztizg cs.nreg kE = c.nreg kE
ztizh cs.nreg kH = c.nreg kH
ztizi c₀.nreg 9999 ≤ c.nreg 9999
ztizj c₁.nreg 170046 = c.nreg 170046
ztizk c₁.nreg 50032 = 1
ztizl c₁.nreg ALLOC = A
ztizm c₁.nreg qD = c.nreg qD
ztizn c₂.nreg 90019 = 1
ztizo c₃.nreg K1 = 1
ztizp c₅.nreg ALLOC = c.nreg ALLOC
ztizq d < rL1 J + rL2 J
ztizr e < p + 1
ztizs e.nreg 43011 = 1
ztizt f * R ≤ 18 * R
ztizu g.L * g.N ≤ g.L * g.U
ztizv i < c.nreg sC
ztizw j ∈ (E.N.region E.r).arcs
ztizx k < p + 1
ztizy m ≤ 2 ^ Nat.clog 2 m
ztizz m' D = m D
ztjaa p < 2 * C.m + 6
ztjab p = 2 * C.m + 6
ztjac q.2 < z.2 ∧ z.2 < y₂
ztjad q[base + 1 + codeSize e]? = some _
ztjae q[base + 2 + codeSize body]? = some _
ztjaf r < E.N.nRegions
ztjag r ≠ ALLOC
ztjah rL R ℓ + 10 + 1 = rL R ℓ + 11
ztjai rL R ℓ + 10 + 2 = rL R ℓ + 12
ztjaj rL R ℓ + 10 + 3 = rL R ℓ + 13
ztjak rL R ℓ + 4 + 1 = rL R ℓ + 5
ztjal rL R ℓ + 4 + 2 = rL R ℓ + 6
ztjam rL R ℓ + 4 + 3 = rL R ℓ + 7
ztjan s < r
ztjao sideLeftOf a v _ x
ztjap st.cur ∈ st.L E
ztjaq t < (N.region r).arcs.length
ztjar t = 1
ztjas x < 2 * ((interiorModel Q).W.n : ℝ)
ztjat x = rayPt z (-1) (r - x.1)
ztjau x.edge < (chainModel C).W.n
ztjav y₁ < z.2 ∧ z.2 < q.2
ztjaw z < S.cnt + 2
ztjax ¬ (o _ = 0 ∨ o _ < o _)
ztjay ¬ ks < ke
ztjaz ε < s
ztjba ∀ Q : Set Point, (exitsIn M.D S Q).Finite
ztjbb ∀ a, a < c.nreg ALLOC → c₁.nmem a = c.nmem a
ztjbc ∀ a, a < c.nreg ALLOC → c₄.nmem a = c.nmem a
ztjbd ∀ a, a < c.nreg ALLOC → c₅.nmem a = c.nmem a
ztjbe ∀ p, p < N₂.arcs.length → c.nmem _ = sj N₂ p
ztjbf ∀ q, 81000 ≤ q → q < 82000 → InR q
ztjbg ∀ r, BFR r = false → c₁.nreg r = c.nreg r
ztjbh ∀ r, Bcp r = false → c₂.nreg r = c₁.nreg r
ztjbi ∀ r, Bcp r = false → c₄.nreg r = c₃.nreg r
ztjbj ∀ r, r ≠ sw 722 → c₁.nreg r = c.nreg r
ztjbk ∀ r, r ≠ sw 96 → c₂.nreg r = c.nreg r
ztjbl ∀ u : Fin μ, (u : ℕ) < S.μ
ztjbm ∀ x : Point, sideCross B _ = det v _ x
ztjbn ∀ x : Point, sideCross _ A = det a v x
ztjbo ∀ x, sideLeft M.W p 0 x ↔ sideCcw _ _ _
ztjbp ∀ x, x < c.nreg ALLOC → c₂.nmem x = c.nmem x
ztjbr ∃ j, d.nreg 60020 = j
ztjbs ∃ m, c.nreg 218002 = m
ztjbt ∃ p', p' < N.arcs.length ∧ After C Q N p' _
ztjbu ∃ q', q' < N.arcs.length ∧ Before C Q N q' _
ztjbv ∃ s, c.nreg 218001 = s
ztjbw ∃ x', L[i - 1]? = some x'
ztjbx ∃ μ, c.nreg 218005 = μ
ztjby (((g' + dX : ℕ) : ℝ))
ztjbz (((k - 1 : ℕ) : ℝ))
ztjca (((μ + 65 : ℕ) : ℝ))
ztjcb ((C.vertex _).2 - (C.vertex k).2)
ztjcc ((M.wb x.edge).2 - (M.wa x.edge).2)
ztjcd ((M.wb y.edge).2 - (M.wa y.edge).2)
ztjce ((P.vtx k).1 - (P.vtx m).1)
ztjcf ((chainModel C).key Q (N.arc j).e)
ztjcg ((chainModel C).key Q (N.arc j).s)
ztjch ((crot haj0 hajn hbj0 hbjn hkx'0 hkx'n).1 hkx')
ztjci ((g + (x₀ - g')) % E.M.W.n)
ztjcj ((g' + (L1 + δ)) % M₂.W.n)
ztjck ((g' + d₀) % (chainModel C').W.n)
ztjcl ((interiorModel Q).key Q (N.arc j').s)
ztjcm ((interiorModel Q).param Q ⟨u, sh⟩)
ztjcn ((pa : ℝ) + (ta + s))
ztjco ((rot haj0 hajn hbj0 hbjn hka'0 hka'n).1 ha')
ztjcp ((s.edge + d) % (chainModel C).W.n)
ztjcq ((sideLeft_rayPt_iff _ p 0 τ one_pos hs0).1 hsec)
ztjcr ((sideLeft_rayPt_iff _ p 0 τ one_pos hs₀0).1 hsec)
ztjct (-C.radius + 2 * t * C.radius, -C.radius)
ztjcu (.constN oKk 0)
ztjcv (.e 180053 180035)
ztjcw (.ifLtN 120120 120028 xpVtx (.ifLtN 120120 120029 xpEdge xpVtx))
ztjcx (.ifLtN 130864 130862 .skip (.ifLtN 130862 130864 .skip lightB))
ztjcy (.ifLtN 140319 K1 cand0 (.ifLtN 140320 K1 cand0 xTree))
ztjcz (.ifLtN 217094 217027 lookRun lookPt)
ztjda (.ifLtN 43203 43204 incV (.ifLtN 43204 43203 incV .skip))
ztjdb (.ifLtN 43221 43225 fillV (.ifLtN 43225 43221 fillV .skip))
ztjdc (.ifLtN 50121 50032 secFirst (.ifLtN 50121 50123 secGen secLast))
ztjdd (.ifLtN 90010 90019 emptyS mainStmt)
ztjde (.ifLtN 90073 90019 .skip writeT)
ztjdf (.ifLtN K1 oKd (m2cS sh) (m2cW sh))
ztjdg (.ifLtN b a e t)
ztjdh (.ifLtN_false a2 (.ifLtN_false b0 (.ifLtN_false b2 ex)))
ztjdi (.ifLtN_false a2 (.ifLtN_false b0 (.ifLtN_true b2 ex)))
ztjdj (.ifLtN_false h2 e)
ztjdk (.ifLtN_false t2 ex)
ztjdm (.ifLtR 117 116 setFlag .skip)
ztjdn (.instr (.subN cDd cT (b + 4)))
ztjdo (.not (.var 50143))
ztjdp (.not (.var 50144))
ztjdq (.not (.var 50147))
ztjdr (.not (.var 50148))
ztjds (.seq e₂ (.seq e₃ (.ifLtN_false g06 e₄)))
ztjdt (.seq e₂ (.seq e₃ (.ifLtN_true g06 e₄)))
ztjdu (.seq e₇ e₈)
ztjdw (.seq x₂ x₃)
ztjdx (.skip e₃.wb_right)
ztjdy (.skip w₀)
ztjdz (.v 180062)
ztjea (0 + 6 + (C.sideWalk β).n - 1)
ztjeb (0, 1)
ztjec (1 + 6)
ztjed (1 - a)
ztjee (10001, a + 1)
ztjef (10002, a + 2)
ztjeg (10004, b + 1)
ztjeh (10005, b + 2)
ztjei (10007, d + 1)
ztjej (10008, d + 2)
ztjek (120160 + k)
ztjel (14700 * t + 14700)
ztjem (16 * Fg)
ztjen (180041 + d)
ztjeo (18900 * t + 18900)
ztjep (190000 + r)
ztjeq (1950481 * X)
ztjer (2 * (L.length + (newL.map Prod.snd).length))
ztjes (2 * C'.m + 7)
ztjet (2 * C.m - i)
ztjeu (2 * Cc + 2)
ztjev (2 * J.left.m + 6)
ztjew (2 * J.whole.m + 6)
ztjex (2 * J.whole.m)
ztjey (2 * Kod + 10)
ztjez (2 * Kod + 4)
ztjfa (2 * K₂)
ztjfb (2 * N - 2 - a + 1 + q)
ztjfc (2 * T * (E.d0 + 3) + 1)
ztjfd (2 * TLk.length)
ztjfe (2 * a.2.1 + 7)
ztjff (2 * dist b a)
ztjfg (2 * g.N + d)
ztjfh (2 * i + s)
ztjfi (2 * l₁.length + q)
ztjfj (2 * γ)
ztjfk (2 * μ / S.s - (nsp1 + 1))
ztjfl (2 + offerFK)
ztjfm (2 ^ μ)
ztjfn (210000 + i)
ztjfo (240000 + j)
ztjfp (3 * (c₂.nreg 9999 - c₂.nreg 219003) + 4)
ztjfq (3 + 1)
ztjfr (32 * SY + 1)
ztjfs (4 * c + k)
ztjft (4900 * E ^ 11)
ztjfu (5 * M.W.n)
ztjfv (5 * i + 4)
ztjfw (5 * r + 4)
ztjfx (5 * Γ + 9)
ztjfy (5 + (5 + (offerFK + 2)))
ztjfz (50201, ir)
ztjga (50201, jr)
ztjgb (6 + i)
ztjgc (6 + r2)
ztjgd (6 + tpos C J)
ztjge (6 + tpos C' J')
ztjgf (8192 * E ^ 14)
ztjgg (9 * D + 24)
ztjgh (A * B * K)
ztjgi (A + 10)
ztjgj (A + 5 * i)
ztjgk (A + 6)
ztjgl (A + v + 1)
ztjgm (Agr.of_upd h₄)
ztjgn (A₀ + 10 * K)
ztjgo (A₁ + 1)
ztjgp (B + 8)
ztjgq (B + i)
ztjgr (B + z)
ztjgs (B.N + i)
ztjgt (BB + j)
ztjgu (BK + 2 * t)
ztjgv (BhalfS dd dst)
ztjgw (BhitG R Bx)
ztjgx (Bn + 3)
ztjgy (BoffG R Bk)
ztjgz (BphaseB_false hr' hra)
ztjha (Bq.1 - Pa.1)
ztjhb (Bt d)
ztjhc (BuildNF.buildNF E.M E.Q L Ev)
ztjhd (B₀ + 3)
ztjhe (C R)
ztjhf (C'.topIdx + 1)
ztjhg (C.chordSet k σ)
ztjhh (C.m - sA C C.sideBeta)
ztjhi (C.radius + t * (C.top.1 - C.radius), C.radius)
ztjhj (C.s + j)
ztjhk (C.sideIdx β i)
ztjhl (C.sideTop_nonSpike hP β hT0 hTm)
ztjhm (C.sideTour C.sideBeta 1)
ztjhn (C.slitTop - v)
ztjho (C.top.1, C.radius + t * (C.top.2 - C.radius))
ztjhp (CA + R + r)
ztjhq (CA + R + v)
ztjhr (ChainObs.segs C)
ztjhs (Cα.s + Cα.m)
ztjht (D + 1 + j)
ztjhu (D \ c)
ztjhv (D ⊕ D ⊕ D)
ztjhw (D.bot_lt hQ)
ztjhx (D.j + 1)
ztjhy (D.top_lt hQ)
ztjhz (D.y₂ - D.y₁)
ztjia (DB + L + L)
ztjib (DrvD.endPos x s)
ztjic (DrvD.scanK + 2)
ztjid (E.Cm + 1)
ztjie (E.K + newL.length)
ztjif (E.N.F E.M E.Q)
ztjig (E.d0 + E.D)
ztjih (E.hK.fix hI₃)
ztjii (E.length + 1)
ztjij (End × End)
ztjik (Exec.constN hI.hw r v hv)
ztjil (Exec.constN w₆ 30002 1 hW1)
ztjin (Exec.subN hI.hw r a b)
ztjio (Exec.subN w₆ _ _ _)
ztjip (E₁_le hP)
ztjiq (F + 2)
ztjir (F + T + 1)
ztjis (F.ncard * γ)
ztjit (FA + r)
ztjiu (FRS.block hB _ hI₁ ok2)
ztjiv (Fin N)
ztjiw (Finset.Ico lo hi)
ztjix (Finset.mem_range.1 hr)
ztjiy (H + 3)
ztjiz (H + f)
ztjja (Host.whole n)
ztjjb (J - 1 - t)
ztjjc (J.right_set_subset h)
ztjjd (K * (Nat.clog 2 m + 1) + 1)
ztjje (K + 40)
ztjjf (K i)
ztjjg (K' * Z)
ztjjh (Kd * (Nat.clog 2 Kd + 1) + 1)
ztjji (Kod + κO)
ztjjj (K₀ + t)
ztjjk (K₂ + 2)
ztjjl (L.bPar + g)
ztjjm (L.bQ + i)
ztjjn (L.getD i d)
ztjjo (L41.scF κs)
ztjjp (L41.scG κs)
ztjjq (List.cons_ne_nil q qs)
ztjjr (M - 1 - t₀)
ztjjs (M.D \ j)
ztjjt (M.face e)
ztjju (M.fperm d)
ztjjv (M.head e)
ztjjw (M.head f)
ztjjx (M.key Q q.1)
ztjjy (M.key Q q.2)
ztjjz (M.pos Q X)
ztjka (M.vert f)
ztjkb (M.wb p - M.wa p)
ztjkc (M1Post P J N₂ c)
ztjkd (Machine.Exec.subN hw₁ _ _ _)
ztjke (N - 2 - p)
ztjkf (NB + y)
ztjkg (NFLoc.seq_lt hN hq)
ztjkh (Nat.clog 2 (c2.nmem (c2.nreg 90001)) + 1)
ztjki (Nat.clog 2 L.length + 1)
ztjkj (Nat.floor_le hb.1)
ztjkk (Nat.mod_lt _ hN)
ztjkl (Nat.mod_lt _ hn0)
ztjkm (Nat.sub_le _ _)
ztjkn (Ne.symm h1)
ztjko (Ne.symm hij)
ztjkp (Or.inl (D.diag_mem_trapDiagonals hna))
ztjkr (Or.inl hc)
ztjks (Or.inl hq)
ztjkt (Or.inr (Or.inr ⟨hbA, hdA, ?_⟩))
ztjku (Or.inr h1)
ztjkv (OracleQ.sj N₁ o)
ztjkw (P - v)
ztjkx (P.n - 1 + 1)
ztjky (P.n - q - 1)
ztjkz (P.vtx b)
ztjla (P.vtx d.1)
ztjlb (P.vtx d.2)
ztjlc (P.vtx x)
ztjld (P.vtx y)
ztjle (POS + j)
ztjlf (PW + i)
ztjlg (ParOut P J N₂ c)
ztjlh (Pr + Nx - v)
ztjli (Q.n + 4 * L.length)
ztjlj (Q.n - 1 - j)
ztjlk (Q.n - 1 - u + (Q.n - L))
ztjll (Quot R)
ztjlm (R + 100 < r ∧ r < R + 300)
ztjln (R + 104)
ztjlo (R + 105)
ztjlp (R + 120)
ztjlq (R + 140)
ztjlr (R + 160)
ztjls (R + 180)
ztjlt (R + 200)
ztjlu (R + 220)
ztjlv (R + 246 ≤ r ∧ r < R + 248)
ztjlw (R + 32)
ztjlx (R + 33)
ztjly (R + 38 ≤ r ∧ r < R + 44)
ztjlz (R - ys)
ztjma (R' + 3 * i)
ztjmb (S + 2 + i)
ztjmc (S ∪ A)
ztjmd (S ∪ Extract.kept R F₁)
ztjme (S.bACT + i')
ztjmf (S.bACT + lo ≤ x ∧ x < S.bACT + e3)
ztjmg (S.bACT ≤ x ∧ x < S.bACT + 2 * S.μ)
ztjmh (S.bDF + x)
ztjmi (S.bDF + y)
ztjmj (S.bFPAR + x)
ztjmk (S.bFPRE + g)
ztjml (S.bFPRE + x)
ztjmm (S.bFSZ + x)
ztjmn (S.bLEV + y)
ztjmo (S.bPOS + y)
ztjmp (S.bSF + x)
ztjmq (S.bSO + x)
ztjmr (SE + j)
ztjms (SelI c.nmem S X f)
ztjmt (Set.empty_subset _)
ztjmu (Set.ncard_le_ncard ?_ ?_)
ztjmv (ShootCut.shootCutSpec O hV)
ztjmw (ShotList.shotList sh RS)
ztjmx (Sp ∪ A)
ztjmy (St.F_finite hE)
ztjmz (T + 3 * a)
ztjna (T + 3 * p)
ztjnb (T + 3 * r)
ztjnc (T + 3 * x)
ztjnd (T + 3 * xs.length)
ztjne (T + 4 * c)
ztjnf (T + i)
ztjng (T m)
ztjnh (TB + j)
ztjni (TD + 1)
ztjnj (U + 7)
ztjnk (U - U₀)
ztjnl (V.A + V.K)
ztjnm (V.CH + q)
ztjnn (V.ORD + i)
ztjno (V.SB + x)
ztjnp (W.filled \ W.boundary)
ztjnq (WT + j)
ztjnr (WalkAx.open_rev hopen)
ztjns (X + 4)
ztjnt (a + C)
ztjnu (a + t, y)
ztjnv (a - B')
ztjnw (a < d.b0 + d.oCnt ∨ d.b0 + d.oStk ≤ a)
ztjnx (a < d.b0 + d.oNd0 ∨ d.b0 + d.oDeg ≤ a)
ztjny (a.x0 + ε * a.x1)
ztjnz (aO + 1)
ztjoa (act i)
ztjob (adjS d)
ztjoc (b + b + (b + b) + b)
ztjod (b - t, y)
ztjoe (b r₀ + c r₀)
ztjof (b' - v)
ztjog (b', y')
ztjoh (bS + q.2 + 1)
ztjoi (bT + d)
ztjol (block [.addN 110067 110060 110065, .copyN 110066 110063])
ztjom (block [.addN 120099 120097 120098, .loadN 120080 120099])
ztjon (block [.addN 120101 120034 120100, .loadN 120090 120101])
ztjoo (block [.addN 130141 130105 130140, .loadN 130142 130141])
ztjop (block [.addN 130141 130106 130140, .loadN 130142 130141])
ztjoq (block [.addN 130536 130531 130533, .loadN 130537 130536])
ztjor (block [.addN 130618 130606 130616, .loadN 130618 130618])
ztjos (block [.addN 130641 130634 130640, .loadN 130641 130641])
ztjot (block [.addN 130823 130069 130820, .storeN 130823 130821])
ztjou (block [.addN 130837 130064 130834, .loadN 130837 130837])
ztjov (block [.addN 170034 170014 170035, .loadN 160035 170034])
ztjow (block [.addN 170034 170034 170022, .loadN 160036 170034])
ztjox (block [.addN 60107 130004 60103, .loadN 60107 60107])
ztjoy (block [.addN 90072 90030 90070, .loadN 90073 90072])
ztjoz (block [.addN 90072 90039 90070, .storeN 90072 90085])
ztjpa (block [.addN kqX kqX K1, .loadN kqV kqX])
ztjpb (block [.constN 120085 0, .addN 120088 120084 120011])
ztjpc (block [.constN 150063 0, .subN 150062 150029 150061])
ztjpd (block [.constN 170133 6, .addN 170135 170089 170133])
ztjpe (block [.constN 217070 1, .addN 217071 217095 217097])
ztjpf (block [.constN 50112 6, .addN 50201 50111 50112])
ztjpg (block [.constN 90112 0, .subN 90115 90111 90019])
ztjph (block [.constN K1 1, .addN 140403 140000 K1])
ztjpi (block [.copyN 150049 150001, .subN 150076 150004 150091])
ztjpj (block [.copyN 150049 150003, .subN 150076 150004 150091])
ztjpk (block [.copyN 170137 170136, .addN 170134 170134 170011])
ztjpl (block [.copyN 180045 180016, .subN 180046 180010 180011])
ztjpm (block [.copyN 212084 212073, .subN 212085 212000 212073])
ztjpn (block [.storeN 110005 r, .addN 110005 110005 120011])
ztjpo (bpt_of_side hr)
ztjpp (br_prim hr)
ztjps (by exact_mod_cast this)
ztjpt (by linarith [(open_of_mem h hz hzD).1])
ztjpu (by linarith [(open_of_mem h hz' hz'D).2])
ztjpv (by linarith [hc₁.lt])
ztjpw (by linarith [hc₂.lt])
ztjpx (by linarith [hs.1])
ztjqa (by rw [h1, h2]; left; grind)
ztjqb (by rw [hA₁])
ztjqd (by rw [hoT, ekE, ekH]; tauto)
ztjqe (by rw [hp0])
ztjqg (by rw [rd_shoot, s0, hM1]; omega)
ztjqh (by rw [t2, hMod, d2]; tauto)
ztjqi (by show c'.nreg 9999 ≤ c.nreg 9999 + k; omega)
ztjqj (by simp [Bl, h1, h2', h3'])
ztjqk (by simp [Src.pt, SymPt.Lt, r70, hin])
ztjql (by simp [Sweep.nbrRegs])
ztjqm (by simp [copyBit, setB, wr, wrOK])
ztjqn (by simp only [decide_eq_false_iff_not]; unfold ALLOC; omega)
ztjqo (by unfold ARG; omega)
ztjqp (by unfold Alw sw at b; unfold sw; omega)
ztjqq (by unfold AttRG; omega)
ztjqr (by unfold BDV; simp only [decide_eq_false_iff_not]; omega)
ztjqs (by unfold BEd; simp only [decide_eq_false_iff_not]; omega)
ztjqt (by unfold FillScr; omega)
ztjqu (by unfold FirstRG; omega)
ztjqv (by unfold InR; omega)
ztjqw (by unfold InvRG; omega)
ztjqx (by unfold LVRG; omega)
ztjqy (by unfold LbRG; omega)
ztjqz (by unfold NF.nChords; grind)
ztjra (by unfold PLRG; omega)
ztjrb (by unfold RowRG; omega)
ztjrc (by unfold k1K; omega)
ztjrd (by unfold pairK; omega)
ztjre (by unfold slotA; omega)
ztjrf (by unfold sw at b; unfold nO sw; omega)
ztjrg (c + d)
ztjrh (c - 1 - p)
ztjri (c ∩ D)
ztjrj (c'.nreg 120160, c'.nreg 120161, c'.nreg 120162, c'.nreg 120163)
ztjrk (c'.nreg 81180)
ztjrl (c'.nreg o)
ztjrm (c'.nreg oKd)
ztjrn (c'.nreg wO)
ztjro (c.d0 + ε * c.d1)
ztjrp (c.nmem (c.nreg 240300 + 7 * j + 1))
ztjrq (c.nmem f1)
ztjrr (c.nmem f2)
ztjrs (c.nreg 110101)
ztjrt (c.nreg 130130)
ztjru (c.nreg 150034 + c.nreg 150082)
ztjrv (c.nreg 170014)
ztjrw (c.nreg 212098)
ztjrx (c.nreg 218000)
ztjry (c.nreg 30000)
ztjrz (c.nreg 30001)
ztjsa (c.nreg 30007 + c.nreg 30013)
ztjsb (c.nreg 50105)
ztjsc (c.nreg 50202)
ztjsd (c.nreg 81004)
ztjse (c.nreg 81089 + c.nreg x)
ztjsf (c.nreg base)
ztjsg (c.nreg fE)
ztjsh (c.nreg hpA < c.nreg hpB)
ztjsi (c.nreg kN)
ztjsj (c.nreg lT)
ztjsk (c.nreg oD)
ztjsl (c.nreg sCl + c.nreg sT)
ztjsm (c.nreg t)
ztjsn (c.nreg v)
ztjso (c.rreg a1, c.rreg a2)
ztjsp (c.rreg b1, c.rreg b2)
ztjsq (c2.nreg ALLOC)
ztjsr (cVtx_lt C e)
ztjss (callS E.sF)
ztjst (cfgRen f c)
ztjsu (chunks C s a L)
ztjsv (cntBase A B)
ztjsw (copy2List R ℓ)
ztjsx (cs E.M E.Q E.N st.cur)
ztjsy (curLab P J N₂ c')
ztjsz (cw.nreg wE)
ztjta (cw.nreg wH)
ztjtb (cyc_open hin)
ztjtc (c₁.nreg 81000)
ztjtd (c₂.nreg 61 + c₂.nreg 63)
ztjte (d + 3)
ztjtf (d + δ)
ztjtg (d' + δ + t')
ztjth (d.b0 + d.oDeg + r)
ztjti (d.b0 + d.oDeg + x)
ztjtj (d.b0 + d.oExb + x)
ztjtk (d.b0 + d.oNd0 + i)
ztjtl (d.b0 + d.oNd1 + i)
ztjtm (d.b0 + d.oS0 + u)
ztjtn (d.b0 + d.oS1 + u)
ztjto (d.b0 + d.oWt + x)
ztjtp (d.nreg 217150)
ztjtq (d.nreg 217160)
ztjtr (d.nreg 217161)
ztjts (d.nreg bE)
ztjtt (d.nreg bH)
ztjtu (dBands ∪ Bo)
ztjtv (db - δ)
ztjtw (dbK E N + 2)
ztjtx (dirCode M x.edge)
ztjty (dirOf (c₂.nreg qD))
ztjtz (dirOf σ)
ztjua (dirS d b)
ztjub (div_nonneg hs0.le hk0.le)
ztjuc (dnC M Q L E)
ztjud (dst, 50046)
ztjue (d₁.nreg rR1 + d₁.nreg rc)
ztjuf (d₁.nreg rR2 + d₁.nreg rc)
ztjug (e - a)
ztjuh (e - g₀)
ztjui (e'.1.symm.trans e.1)
ztjuj (e'.2.1.symm.trans e.2.1)
ztjuk (e'.2.2.1.symm.trans e.2.2.1)
ztjul (e.1 + δ, y)
ztjum (e.1 - a.1)
ztjun (e.1 - w.1)
ztjuo (e.2 - a.2)
ztjup (eIdx (Qof P).n V.s (c'.nreg 120052))
ztjuq (eV u)
ztjur (ee - 2)
ztjus (ek M Q N q)
ztjut (endOrigin J Q N j')
ztjuu (eqT cT nr (.instr (.copyN cX K6)))
ztjuv (eqT qD K1 (.instr (.constN rho 0)))
ztjuy (e₀ + t)
ztjuz (f = 11 ∨ f = 12 ∨ f = 16)
ztjva (f srX + f srX)
ztjvb (f.compile d)
ztjvc (farW li Q i d)
ztjvd (finCfg c')
ztjve (flφ c.nmem FL v = none → c'.nreg 60104 = 0)
ztjvf (flφ c.nmem FL)
ztjvg (freeIn C'.dom Si)
ztjvj (fun _ _ => 11)
ztjvk (fun _ _ _ _ _ h1 h2 => h1.trans h2)
ztjvl (fun a _ => by rw [f₇.2.2.1, f₆.2.2.1])
ztjvm (fun a h => h)
ztjvn (fun c => 3 * (E - c.nreg ALLOC))
ztjvo (fun c => ∃ newL, RegI E c₀ newL c)
ztjvp (fun c hc => hc.1)
ztjvq (fun c' hP => ?_)
ztjvr (fun c2 h => h.1)
ztjvs (fun d => Nat.log 2 L + 1 - d.nreg 150082)
ztjvt (fun d hd => hd.1.wb)
ztjvu (fun g hg => ?_)
ztjvx (fun i hi' => ?_)
ztjvy (fun j => m₃ _)
ztjvz (fun j hj => ?_)
ztjwb (fun k hk => ?_)
ztjwc (fun m' p => ∃ r, p.1 = m'.rotate r)
ztjwd (fun q hq => by unfold FFix at hq; omega)
ztjwe (fun r a b c d e f g => ?_)
ztjwf (fun r h => by simp [Bk0, h])
ztjwg (fun r hr => by simp [BcmpG, hr])
ztjwh (fun r hr => by simp [Bgap, hr])
ztjwi (fun r hr => by simp [Bpass, hr])
ztjwj (fun r hr => by simp [Btv, hr])
ztjwl (fun r hr => hAr r (hrsl r hr))
ztjwm (fun s hs => ?_)
ztjwn (fun t ht => ?_)
ztjwo (fun t ht1 ht2 => hsub ⟨ht1, ht2⟩)
ztjwp (fun x hx => ?_)
ztjws (f₁ ≠ 1 ∨ σ * x₂ < σ * x₁)
ztjwt (f₁.1 r hr)
ztjwv (g p)
ztjww (g' + 1)
ztjwx (g' + d₂)
