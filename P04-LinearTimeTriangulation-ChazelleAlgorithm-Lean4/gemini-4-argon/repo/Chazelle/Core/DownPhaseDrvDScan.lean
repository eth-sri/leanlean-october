module

public import Chazelle.Core.DownPhaseDrvDProg
public import Chazelle.Core.DownPhaseDrvDLoc
public import Chazelle.Core.DownPhaseDrvRLib

/-!
# Down-phase restoration rounds (D8), part 5: the arc scan on the RAM

`scanS` visits the arcs `j` of region `r` (its arc list at `lp`, arc records at `AB`), decides
`t₁ = [key s_j ≤ key x]` and `t₂ = [key x ≤ key e_j]` for the end `x` with two key decisions
(`BuildRam.halfS`), and on a match (`matchB`) sets the bucket `bktB` (`decS`).

**`scanS_exec`**: if some arc of the region matches, the bucket at the end satisfies the bucket
condition on an arc of the region (`ScanFound`); at most `scanK` steps per arc; only the
registers `Bscan` are written, no memory.
-/

namespace Chazelle.Core

namespace DrvD

open Machine Machine.Stmt Programs SignK WalkKey

@[expose] public section

/-- The first decision: the start of arc `j` is not after `x`. -/
noncomputable def tA (M : Model) (Q : Polygon) (N : NF) (x : WPos) (j : ℕ) : Bool :=
  decide (M.key Q (N.arc j).s ≤ M.key Q x)

/-- The second decision: `x` is not after the end of arc `j`. -/
noncomputable def tB (M : Model) (Q : Polygon) (N : NF) (x : WPos) (j : ℕ) : Bool :=
  decide (M.key Q x ≤ M.key Q (N.arc j).e)

/-- **The result of a scan**: the bucket condition of `x`, on an arc of region `r`. -/
def ScanFound (M : Model) (Q : Polygon) (N : NF) (r : ℕ) (x : WPos) (b : ℕ) : Prop :=
  BktKey M Q N (M.key Q x) b ∧ arcOfB N.arcs.length b ∈ (N.region r).arcs

/-- The data of an arc scan: the end `x`, region `r` of `N` (its arc list at `lp`, the arc
records at `AB`, in the memory `m`), the model descriptor at `MD`. -/
structure ScanGood (P : Polygon) (W : ℕ) (M : Model) (N : NF) (r : ℕ) (x : WPos) (m : ℕ → ℕ)
    (MD AB lp : ℕ) : Prop where
  hG : GoodEnv P
  hW : hostWords P.n ≤ W
  hDW : MD + 6 ≤ W
  hCW : NFLoc.LocChainWF P W m MD
  hM : ModelDescAt m MD (Qof P) M
  xe : x.edge < M.W.n
  xh : 1 ≤ x.hgt
  xp : ProperPos M (Qof P) P.n x
  lpW : lp + (N.region r).arcs.length ≤ W
  ABW : AB + 5 * N.arcs.length ≤ W
  list : ∀ t, t < (N.region r).arcs.length → m (lp + t) = (N.region r).arcs.getD t 0
  arcs : ∀ j ∈ (N.region r).arcs, j < N.arcs.length ∧
    m (AB + 5 * j + 1) = (N.arc j).s.edge ∧ m (AB + 5 * j + 2) = (N.arc j).s.hgt ∧
    m (AB + 5 * j + 3) = (N.arc j).e.edge ∧ m (AB + 5 * j + 4) = (N.arc j).e.hgt ∧
    ProperPos M (Qof P) P.n (N.arc j).s ∧ ProperPos M (Qof P) P.n (N.arc j).e ∧
    1 ≤ (N.arc j).e.hgt ∧ (N.arc j).e.edge < M.W.n

/-- The step bound of one arc of the scan. -/
def scanK : ℕ := 11000

section exec

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 2000000 in
/-- Loading arc `j`. -/
theorem ldArc_exec (d : Config) (hw : WordsBounded W d) {lp t AB j xe xh : ℕ}
    (h43 : d.nreg 216043 = lp) (h44 : d.nreg 216044 = t) (h14 : d.nreg 216014 = AB)
    (h02 : d.nreg 216002 = 1) (h40 : d.nreg 216040 = xe) (h41 : d.nreg 216041 = xh)
    (hj : d.nmem (lp + t) = j) (hW : AB + 5 * j + 5 ≤ W) (hW' : lp + t ≤ W) :
    ∃ d' k, Exec P W ldArc d d' k ∧ k = 17 ∧
      d'.nreg 42100 = xe ∧ d'.nreg 42101 = xh ∧
      d'.nreg 42102 = d.nmem (AB + 5 * j + 1) ∧ d'.nreg 42103 = d.nmem (AB + 5 * j + 2) ∧
      d'.nreg 42104 = d.nmem (AB + 5 * j + 3) ∧ d'.nreg 42105 = d.nmem (AB + 5 * j + 4) ∧ d'.nreg 216054 = j + 1 ∧ FrameB BldArc d d' := by
  obtain ⟨d', k, ex, hk, q⟩ : ∃ d' k, Exec P W ldArc d d' k ∧ k = 17 ∧
      (d'.nreg 42100 = xe ∧ d'.nreg 42101 = xh ∧
      d'.nreg 42102 = d.nmem (AB + 5 * j + 1) ∧ d'.nreg 42103 = d.nmem (AB + 5 * j + 2) ∧
      d'.nreg 42104 = d.nmem (AB + 5 * j + 3) ∧ d'.nreg 42105 = d.nmem (AB + 5 * j + 4) ∧
      d'.nreg 216045 = j ∧ d'.nreg 216054 = j + 1) := by
    unfold ldArc
    exec_block
    all_goals try (config_simp; simp only [h43, h44, h14, h02, h40, h41, hj]; omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp <;>
      simp only [h43, h44, h14, h02, h40, h41, hj] <;> (congr 1; ring)
  exact ⟨d', k, ex, hk, q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2.1, q.2.2.2.2.2.1, q.2.2.2.2.2.2.2, exec_frameB ex wr_ldArc⟩

/-- The decision on arc `j`. -/
theorem decS_exec (d : Config) (hw : WordsBounded W d) {A j : ℕ} {t₁ t₂ : Bool}
    (h54 : d.nreg 216054 = j + 1) (h17 : d.nreg 216017 = A) (h03 : d.nreg 216003 = 0)
    (h07 : d.nreg 42107 = if t₁ then 1 else 0) (h09 : d.nreg 42109 = if t₂ then 1 else 0) :
    ∃ d' k, Exec P W decS d d' k ∧ k ≤ 7 ∧
      d'.nreg 216053 = (if matchB A j t₁ t₂ then bktB A j t₂ else d.nreg 216053) ∧
      FrameB (fun r => decide (r = 216053)) d d' := by
  obtain ⟨d', k, ex, hk, q⟩ : ∃ d' k, Exec P W decS d d' k ∧ k ≤ 7 ∧
      d'.nreg 216053 = (if matchB A j t₁ t₂ then bktB A j t₂ else d.nreg 216053) := by
    unfold decS matchB bktB
    by_cases hjA : j + 1 < A
    · refine spec_ifLtN_true (by rwa [h54, h17]) ?_
      rw [ite_eq_left hjA, ite_eq_left hjA]
      cases t₁
      · refine spec_ifLtN_false (by rw [h03, h07]; simp) (spec_skip hw ⟨by omega, by simp⟩)
      · refine spec_ifLtN_true (by rw [h03, h07]; simp) ?_
        cases t₂
        · exact spec_ifLtN_false (by rw [h03, h09]; simp) (spec_skip hw ⟨by omega, by simp⟩)
        · refine spec_ifLtN_true (by rw [h03, h09]; simp)
            (spec_instr (Exec.copyN hw _ _) fun _ => ⟨by omega, ?_⟩)
          config_simp; simp [h54]
    · refine spec_ifLtN_false (by rwa [h54, h17]) ?_
      rw [ite_eq_right hjA, ite_eq_right hjA]
      cases t₂
      · refine spec_ifLtN_false (by rw [h03, h09]; simp) ?_
        cases t₁
        · exact spec_ifLtN_false (by rw [h03, h07]; simp) (spec_skip hw ⟨by omega, by simp⟩)
        · refine spec_ifLtN_true (by rw [h03, h07]; simp)
            (spec_instr (Exec.copyN hw _ _) fun _ => ⟨by omega, ?_⟩)
          config_simp; simp [h17]
      · refine spec_ifLtN_true (by rw [h03, h09]; simp)
          (spec_instr (Exec.constN hw _ _ (Nat.zero_le _)) fun _ => ⟨by omega, ?_⟩)
        config_simp; simp
  exact ⟨d', k, ex, hk, q, exec_frameB ex wr_decS⟩

/-- The decision bit of `halfS` as a key comparison. -/
theorem keyBit {M : Model} {x s : WPos} (hx : ProperPos M (Qof P) P.n x)
    (hs : ProperPos M (Qof P) P.n s) (hx1 : 1 ≤ x.hgt) :
    (if keyDec (Qof P) P.n x (dirCode M x.edge) s = true then 1 else 0) =
      (if decide (M.key (Qof P) s ≤ M.key (Qof P) x) = true then 1 else 0) := by
  have h := keyDec_iff hx hs
  unfold KeyPred at h
  rw [ite_eq_right (by omega)] at h
  by_cases hk : M.key (Qof P) s ≤ M.key (Qof P) x
  · rw [ite_eq_left (h.2 hk), ite_eq_left (by simpa using hk)]
  · rw [ite_eq_right (fun h' => hk (h.1 h')), ite_eq_right (by simpa using hk)]

set_option maxHeartbeats 4000000 in
/-- **One arc of the scan.** -/
theorem scanBody_exec {M : Model} {N : NF} {r : ℕ} {x : WPos} {m : ℕ → ℕ} {MD AB lp : ℕ}
    (hS : ScanGood P W M N r x m MD AB lp) (d : Config) (hw : WordsBounded W d) (hm : d.nmem = m)
    {t : ℕ} (ht : t < (N.region r).arcs.length)
    (h40 : d.nreg 216040 = x.edge) (h41 : d.nreg 216041 = x.hgt) (h43 : d.nreg 216043 = lp)
    (h44 : d.nreg 216044 = t) (h14 : d.nreg 216014 = AB) (h17 : d.nreg 216017 = N.arcs.length)
    (h02 : d.nreg 216002 = 1) (h03 : d.nreg 216003 = 0) (h4 : d.nreg 40000 = MD) :
    ∃ d' k, Exec P W scanBody d d' k ∧ k ≤ scanK ∧ d'.nreg 216044 = t + 1 ∧
      d'.nreg 216053 = (if matchB N.arcs.length ((N.region r).arcs.getD t 0)
          (tA M (Qof P) N x ((N.region r).arcs.getD t 0))
          (tB M (Qof P) N x ((N.region r).arcs.getD t 0))
        then bktB N.arcs.length ((N.region r).arcs.getD t 0)
          (tB M (Qof P) N x ((N.region r).arcs.getD t 0))
        else d.nreg 216053) ∧ FrameB Bscan d d' := by
  set j := (N.region r).arcs.getD t 0 with hjd
  have hjm : j ∈ (N.region r).arcs := by
    rw [hjd, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
    exact List.getElem_mem ht
  obtain ⟨hjA, ms1, ms2, me1, me2, hps, hpe, he1, hee⟩ := hS.arcs j hjm
  have hW3 : P.n + 3 ≤ W := by have := hS.hW; unfold hostWords at this; omega
  -- load
  obtain ⟨d₁, k₁, e₁, hk₁, a00, a01, a02, a03, a04, a05, a54, f₁⟩ := ldArc_exec (P := P) d hw
    h43 h44 h14 h02 h40 h41 (by rw [hm, hS.list t ht]) (by have := hS.ABW; omega)
    (by have := hS.lpW; omega)
  rw [hm, ms1] at a02
  rw [hm, ms2] at a03
  rw [hm, me1] at a04
  rw [hm, me2] at a05
  have w₁ := e₁.wb_right
  have g₁ : ∀ q, BldArc q = false → d₁.nreg q = d.nreg q := f₁.1
  have hm₁ : d₁.nmem = m := by rw [f₁.2.2.1, hm]
  -- the first decision
  obtain ⟨d₂, k₂, e₂, hk₂, -, b07, f₂⟩ := BuildRam.halfS_exec (P := P) hS.hG hW3 d₁ w₁
    (qe := 42100) (qh := 42101) (se := 42102) (sh := 42103) (dd := 42106) (dst := 42107)
    (by decide) (by decide) (by decide) (by rw [g₁ _ (by decide), h4]; exact hS.hDW)
    (by rw [g₁ _ (by decide), h4, hm₁]; exact hS.hCW) (M := M)
    (by rw [g₁ _ (by decide), h4, hm₁]; exact hS.hM) (by rw [a00]; exact hS.xe)
    (by rw [a01]; exact hS.xp.2.2)
  rw [a00, a01, a02, a03, keyBit hS.xp hps hS.xh] at b07
  have w₂ := e₂.wb_right
  have g₂ : ∀ q, BuildRam.BhalfS 42106 42107 q = false → d₂.nreg q = d₁.nreg q := f₂.1
  -- the second decision
  obtain ⟨d₃, k₃, e₃, hk₃, -, b09, f₃⟩ := BuildRam.halfS_exec (P := P) hS.hG hW3 d₂ w₂
    (qe := 42104) (qh := 42105) (se := 42100) (sh := 42101) (dd := 42108) (dst := 42109)
    (by decide) (by decide) (by decide)
    (by rw [g₂ _ (by decide), g₁ _ (by decide), h4]; exact hS.hDW)
    (by rw [g₂ _ (by decide), g₁ _ (by decide), h4, f₂.2.2.1, hm₁]; exact hS.hCW) (M := M)
    (by rw [g₂ _ (by decide), g₁ _ (by decide), h4, f₂.2.2.1, hm₁]; exact hS.hM)
    (by rwa [g₂ _ (by decide), a04])
    (by rw [g₂ _ (by decide), a05]; exact hpe.2.2)
  rw [g₂ _ (by decide), g₂ _ (by decide), g₂ _ (by decide), g₂ _ (by decide), a04, a05, a00,
    a01, keyBit hpe hS.xp he1] at b09
  have w₃ := e₃.wb_right
  have g₃ : ∀ q, BuildRam.BhalfS 42108 42109 q = false → d₃.nreg q = d₂.nreg q := f₃.1
  -- the decision
  have b07' : d₃.nreg 42107 = if tA M (Qof P) N x j then 1 else 0 := by
    rw [g₃ _ (by decide), b07]; rfl
  have b09' : d₃.nreg 42109 = if tB M (Qof P) N x j then 1 else 0 := by
    rw [b09]; rfl
  obtain ⟨d₄, k₄, e₄, hk₄, v53, f₄⟩ := decS_exec (P := P) d₃ w₃ (A := N.arcs.length) (j := j)
    (by rw [g₃ _ (by decide), g₂ _ (by decide), a54])
    (by rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), h17])
    (by rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), h03]) b07' b09'
  have w₄ := e₄.wb_right
  -- the increment
  have i44 : d₄.nreg 216044 = t := by
    rw [f₄.1 _ (by decide), g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), h44]
  have i02 : d₄.nreg 216002 = 1 := by
    rw [f₄.1 _ (by decide), g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), h02]
  obtain ⟨d₅, k₅, e₅, hk₅, v44⟩ : ∃ d₅ k₅, Exec P W (block [.addN 216044 216044 216002]) d₄ d₅ k₅ ∧
      k₅ = 1 ∧ d₅ = { d₄ with nreg := upd d₄.nreg 216044 (t + 1) } := by
    exec_block
    · rw [i44, i02]; have := hS.lpW; omega
    · refine ⟨rfl, ?_⟩
      rw [i44, i02]
  have f₅ : FrameB Bscan d₄ d₅ := by
    rw [v44]
    exact ⟨fun q hq => by
      simp only
      rw [Machine.upd_other _ _ _ (by rintro rfl; simp [Bscan] at hq)], fun _ _ => rfl, rfl, rfl,
      rfl⟩
  have F₁ : FrameB Bscan d d₁ := fbMono f₁ bldArc_scan
  have F₂ : FrameB Bscan d₁ d₂ := fbMono f₂ (bhalf_scan (by norm_num) (by norm_num))
  have F₃ : FrameB Bscan d₂ d₃ := fbMono f₃ (bhalf_scan (by norm_num) (by norm_num))
  have F₄ : FrameB Bscan d₃ d₄ := fbMono f₄ b53_scan
  refine ⟨d₅, k₁ + (k₂ + (k₃ + (k₄ + k₅))), .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), ?_, ?_, ?_,
    F₁.trans (F₂.trans (F₃.trans (F₄.trans f₅)))⟩
  · unfold scanK; omega
  · rw [v44]; simp
  · rw [v44]
    simp only
    rw [Machine.upd_other _ _ _ (by decide), v53, g₃ _ (by decide), g₂ _ (by decide),
      g₁ _ (by decide)]

/-- A match gives a scan result. -/
theorem found_of_match {M : Model} {Q : Polygon} {N : NF} {r : ℕ} {x : WPos} {j : ℕ}
    (hj : j ∈ (N.region r).arcs) (hjA : j < N.arcs.length)
    (hm : matchB N.arcs.length j (tA M Q N x j) (tB M Q N x j) = true) :
    ScanFound M Q N r x (bktB N.arcs.length j (tB M Q N x j)) :=
  ⟨bkt_of_match N hjA (by simp [tA]) (by simp [tB]) hm, by rw [arcOfB_bktB hjA]; exact hj⟩

set_option maxHeartbeats 4000000 in
/-- **The arc scan**: if some arc of the region matches, the bucket found is a scan result. -/
theorem scanS_exec {M : Model} {N : NF} {r : ℕ} {x : WPos} {m : ℕ → ℕ} {MD AB lp : ℕ}
    (hS : ScanGood P W M N r x m MD AB lp) (d : Config) (hw : WordsBounded W d) (hm : d.nmem = m)
    (h40 : d.nreg 216040 = x.edge) (h41 : d.nreg 216041 = x.hgt)
    (h42 : d.nreg 216042 = (N.region r).arcs.length) (h43 : d.nreg 216043 = lp)
    (h14 : d.nreg 216014 = AB) (h17 : d.nreg 216017 = N.arcs.length)
    (h02 : d.nreg 216002 = 1) (h03 : d.nreg 216003 = 0) (h4 : d.nreg 40000 = MD)
    (hex : ∃ j ∈ (N.region r).arcs,
      matchB N.arcs.length j (tA M (Qof P) N x j) (tB M (Qof P) N x j) = true) :
    ∃ d' k, Exec P W scanS d d' k ∧ k ≤ (scanK + 2) * (N.region r).arcs.length + 3 ∧
      ScanFound M (Qof P) N r x (d'.nreg 216053) ∧ FrameB Bscan d d' := by
  have e₀ := Exec.constN (P := P) hw 216044 0 (Nat.zero_le _)
  set d₀ : Config := { d with nreg := upd d.nreg 216044 0 } with hd₀
  have f₀ : FrameB Bscan d d₀ := exec_frameB e₀ (by decide)
  set nA := (N.region r).arcs.length
  set lst : ℕ → ℕ := fun t => (N.region r).arcs.getD t 0 with hlst
  let Inv : ℕ → Config → Prop := fun t e => WordsBounded W e ∧ e.nreg 216044 = t ∧
    e.nreg 216042 = nA ∧ FrameB Bscan d e ∧
    ((∃ t', t' < t ∧ matchB N.arcs.length (lst t') (tA M (Qof P) N x (lst t'))
      (tB M (Qof P) N x (lst t')) = true) → ScanFound M (Qof P) N r x (e.nreg 216053))
  obtain ⟨d', k, ex, ⟨w', -, -, hf', hfound⟩, hk⟩ := DrvR.forLoop (P := P) (W := W)
    (ir := 216044) (nr := 216042) Inv scanK nA
    (fun t e ⟨hw, h1, h2, _⟩ => ⟨hw, h1, h2⟩)
    (fun t e ht ⟨hw, h1, h2, hf, hI⟩ => by
      have g : ∀ q, Bscan q = false → e.nreg q = d.nreg q := hf.1
      obtain ⟨e', k, ex, hk, h44, h53, hf'⟩ := scanBody_exec hS e hw (by rw [hf.2.2.1, hm]) ht
        (by rw [g _ (by decide), h40]) (by rw [g _ (by decide), h41])
        (by rw [g _ (by decide), h43]) h1 (by rw [g _ (by decide), h14])
        (by rw [g _ (by decide), h17]) (by rw [g _ (by decide), h02])
        (by rw [g _ (by decide), h03]) (by rw [g _ (by decide), h4])
      refine ⟨e', k, ex, ⟨ex.wb_right, h44, by rw [hf'.1 _ (by decide), h2], hf.trans hf',
        fun ⟨t', ht', hmt⟩ => ?_⟩, hk⟩
      have hjm : lst t ∈ (N.region r).arcs := by
        simp only [hlst]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
        exact List.getElem_mem ht
      rw [h53]
      by_cases hmt' : matchB N.arcs.length (lst t) (tA M (Qof P) N x (lst t))
          (tB M (Qof P) N x (lst t)) = true
      · rw [ite_eq_left hmt']
        exact found_of_match hjm (hS.arcs _ hjm).1 hmt'
      · rw [ite_eq_right hmt']
        refine hI ⟨t', ?_, hmt⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 ht' with h | h
        · exact h
        · subst h; exact absurd hmt hmt')
    (j := 0) ⟨e₀.wb_right, by rw [hd₀]; simp, by rw [hd₀]; simp [h42], f₀,
      fun ⟨t', ht', _⟩ => absurd ht' (Nat.not_lt_zero _)⟩ (Nat.zero_le _)
  refine ⟨d', 1 + k, .seq e₀ ex, ?_, ?_, hf'⟩
  · have : (scanK + 2) * (nA - 0) = (scanK + 2) * nA := by rw [Nat.sub_zero]
    omega
  · obtain ⟨j, hj, hmj⟩ := hex
    obtain ⟨t', ht', hjt⟩ := List.mem_iff_getElem.1 hj
    refine hfound ⟨t', ht', ?_⟩
    have : lst t' = j := by
      simp only [hlst]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht', Option.getD_some, hjt]
    rwa [this]

end exec

end

end DrvD

end Chazelle.Core
