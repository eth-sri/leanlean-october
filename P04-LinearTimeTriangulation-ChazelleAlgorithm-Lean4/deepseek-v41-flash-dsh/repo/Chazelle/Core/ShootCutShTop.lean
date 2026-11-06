module

public import Chazelle.Golf

public import Chazelle.Golf

public import Chazelle.Core.ShootCutShLpB
public import Chazelle.Core.ShootCutCutterOK

/-!
# WP-G, part 59: the ray-shooter

`shooter query`: the inputs into the registers of the core (`shPro`), the origin of the ray
(`orig`), the piece records (`shInit`, the core with `shEmit`, `shFin`), the loop over the pieces
(`shLoop`), and the answer into `140010 … 140012` (`shEpi`).

* `shooter_cost`: the arithmetic of the step bound;
* `shooter_ok`: the ray-shooter meets `ShooterOK` for the grade-table context, with
  `F(γ) = κs ((⌈log₂ γ⌉ + 1) ⌈(cutGran γ (γ + 1)²)^{1/3}⌉ + 1)`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace Chazelle.Core

namespace ShootCut

open Machine Machine.Stmt Programs SignK WalkKey NFLoc SweepPrim

@[expose] public section

/-! ## The programs -/

/-- The inputs of the core. -/
def shPro : Stmt := block (copies [(150000, 140000), (150001, 140001), (150002, 140002),
  (150003, 140003), (150004, 140004), (150009, 140009), (150013, 140013)])

/-- The piece records. -/
def shPh : Stmt := .seq shInit (.seq (core shEmit) shFin)

/-- The answer. -/
def shEpi : Stmt := block [.copyN 140010 140210, .copyN 140011 140215, .copyN 140012 140216]

/-- **The ray-shooter.** -/
def shooter (query : Stmt) : Stmt :=
  .seq shPro (.seq orig (.seq shPh (.seq (shLoop query) shEpi)))

/-- The registers written by the piece records: bands `1, 5, 15`, the record registers and the
allocator. -/
def Bph (r : ℕ) : Bool :=
  decide (r / 10000 = 1) || decide (r / 10000 = 5) || decide (r / 10000 = 15) ||
    decide (140100 ≤ r ∧ r < 140110) || decide (r = 9999)

theorem wrM_shPh : BuildRam.wrM Bph shPh = true := ⌖

/-- The real registers written by the piece records: bands `1, 5, 15`. -/
def BphR (r : ℕ) : Bool :=
  decide (r / 10000 = 1) || decide (r / 10000 = 5) || decide (r / 10000 = 15)

theorem wrM2_shPh : BuildRam.wrM2 Bph BphR shPh = true := ⌖

theorem BphR_false {r : ℕ} (hr : bandOf r ∉ oracleBands) : BphR r = false := by
  have h1 : (1 : ℕ) ∈ oracleBands := ⌖
  have h5 : (5 : ℕ) ∈ oracleBands := ⌖
  have h15 : (15 : ℕ) ∈ oracleBands := ⌖
  unfold bandOf at hr
  have a1 : r / 10000 ≠ 1 := fun h => hr (h ▸ h1)
  have a5 : r / 10000 ≠ 5 := fun h => hr (h ▸ h5)
  have a15 : r / 10000 ≠ 15 := fun h => hr (h ▸ h15)
  ϴ BphR, Bool.or_eq_false_iff, decide_eq_false_iff_not
  omega

/-! ## Small facts -/

theorem originIn_unique {c : Config} {r : ℕ} {o o' : Origin} (h : OriginIn c r o)
    (h' : OriginIn c r o') : o = o' := by
  cases o with
  | sym s =>
    cases o' with
    | sym s' =>
      cases s with
      | vtx i =>
        cases s' with
        | vtx i' => obtain ⟨a, b⟩ := h; obtain ⟨a', b'⟩ := h'; Ξ ← b, ← b'
        | onEdge e' h'' => obtain ⟨a, -⟩ := h; obtain ⟨a', -⟩ := h'; omega
      | onEdge e hh =>
        cases s' with
        | vtx i' => obtain ⟨a, -⟩ := h; obtain ⟨a', -⟩ := h'; omega
        | onEdge e' h'' =>
          obtain ⟨-, b, d⟩ := h; obtain ⟨-, b', d'⟩ := h'; Ξ ← b, ← b', ← d, ← d'
    | walk x =>
      obtain ⟨a', -⟩ := h'
      cases s with
      | vtx i => obtain ⟨a, -⟩ := h; omega
      | onEdge e hh => obtain ⟨a, -⟩ := h; omega
  | walk x =>
    cases o' with
    | sym s' =>
      obtain ⟨a, -⟩ := h
      cases s' with
      | vtx i => obtain ⟨a', -⟩ := h'; omega
      | onEdge e hh => obtain ⟨a', -⟩ := h'; omega
    | walk x' =>
      obtain ⟨-, b, d⟩ := h; obtain ⟨-, b', d'⟩ := h'
      obtain ⟨xe, xh⟩ := x
      obtain ⟨xe', xh'⟩ := x'
      simp only at b d b' d'
      Ξ ← b, ← b', ← d, ← d'

theorem one_le_rpowCeil (γ : ℕ) : 1 ≤ rpowCeil (cutGran γ * (γ + 1) ^ 2) ((1 : ℝ) / 3) := by
  have h1 : 1 ≤ cutGran γ := by
    unfold cutGran gradeGran
    have := Nat.one_le_two_pow (n := Cost.ceilBeta (Nat.clog 2 γ))
    omega
  have h2 : 1 ≤ cutGran γ * (γ + 1) ^ 2 := Nat.mul_le_mul h1 (Nat.one_le_pow _ _ (⋄))
  unfold rpowCeil
  apply Nat.one_le_iff_ne_zero.2
  intro h0
  Ξ' Nat.ceil_eq_zero at h0
  have : (0 : ℝ) < ((cutGran γ * (γ + 1) ^ 2 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) := by
    apply Real.rpow_pos_of_pos; exact_mod_cast h2
  linarith

/-- The constant of the ray-shooter. -/
def κs (O : OracleIface) : ℕ := 18900 * (2 * O.κ + 600503) + 3000000

/-- The step bound of the loop. -/
theorem loop_budget {κO T R q : ℕ} (hR : 1 ≤ R) (hqT : q ≤ 2100 * T) :
    9 * q * (κO * (R + 1) + 600500 + 2) ≤ 18900 * (2 * κO + 600503) * (T * R) := by
  have hKR : κO * (R + 1) + 600500 + 2 ≤ (2 * κO + 600503) * R := by
    have : κO ≤ κO * R := Nat.le_mul_of_pos_right _ hR
    have : 600503 ≤ 600503 * R := Nat.le_mul_of_pos_right _ hR
    nlinarith
  have := Nat.mul_le_mul (Nat.mul_le_mul_left 9 hqT) hKR
  have e : 9 * (2100 * T) * ((2 * κO + 600503) * R) = 18900 * (2 * κO + 600503) * (T * R) := by
    ring
  omega

/-- **The step bound of the ray-shooter.** -/
theorem shooter_cost {κO T L R q k₁ k₂ k₃ k₄ k₅ k₆ k₇ : ℕ} (hR : 1 ≤ R) (hLT : L + 1 ≤ T)
    (hq : q ≤ 2100 * (L + 1)) (h1 : k₁ ≤ 7) (h2 : k₂ ≤ 16000) (h3 : k₃ ≤ 5 * (T - 1) + 20)
    (h4 : k₄ ≤ 1100 * ((2 * 30 + 90) * (L + 1) + 1702) + 2 * 30 + 20000 + 30 + 20000)
    (h5 : k₅ ≤ 3 * (1 + 9 * q) + 2)
    (h6 : k₆ ≤ 9 * q * (κO * (R + 1) + 600500 + 2) + 20) (h7 : k₇ ≤ 3) :
    k₁ + (k₂ + (k₃ + (k₄ + k₅) + (k₆ + k₇))) ≤
      (18900 * (2 * κO + 600503) + 3000000) * T * R + (18900 * (2 * κO + 600503) + 3000000) := by
  have hKR : κO * (R + 1) + 600500 + 2 ≤ (2 * κO + 600503) * R := by
    have : κO ≤ κO * R := Nat.le_mul_of_pos_right _ hR
    have : 600503 ≤ 600503 * R := Nat.le_mul_of_pos_right _ hR
    nlinarith
  have hqT : q ≤ 2100 * T := ⋄
  have h6' : k₆ ≤ 9 * (2100 * T) * ((2 * κO + 600503) * R) + 20 := by
    have := Nat.mul_le_mul (Nat.mul_le_mul_left 9 hqT) hKR
    omega
  have hTR : T ≤ T * R := Nat.le_mul_of_pos_right _ hR
  have e : 9 * (2100 * T) * ((2 * κO + 600503) * R) = 18900 * (2 * κO + 600503) * (T * R) := by
    ring
  Ξ' e at h6'
  have e2 : (18900 * (2 * κO + 600503) + 3000000) * T * R =
      18900 * (2 * κO + 600503) * (T * R) + 3000000 * (T * R) := ⋆
  Ξ e2
  have : 3 * (1 + 9 * q) ≤ 3 + 27 * (2100 * T) := ⋄
  have hT1 : 1 ≤ T := ⋄
  have hk4 : k₄ ≤ 165000 * T + 1912290 := ⟡
  clear h4 e e2
  set Y := 18900 * (2 * κO + 600503) * (T * R)
  set Z := T * R
  omega

theorem originIn_of_eq {c c' : Config} {r : ℕ} {o : Origin} (h : OriginIn c r o)
    (he : ∀ j, r ≤ j → j < r + 3 → c'.nreg j = c.nreg j) : OriginIn c' r o := by
  cases o with
  | sym s => exact symPtIn_of_eq h he
  | walk x =>
    obtain ⟨a, b, d⟩ := h
    exact ⟨by rw [he r le_rfl (⋄), a], by rw [he (r + 1) (⋄) (by omega), b],
      by rw [he (r + 2) (⋄) (⋄), d]⟩

theorem Borg_ob (r : ℕ) (h : Borg r = true) :
    (bandOf r = 1 ∨ bandOf r = 5 ∨ bandOf r = 12 ∨ bandOf r = 14) ∧ r ≠ ALLOC := by
  ϴ' Borg, Bld, Bprim, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq at h
  unfold bandOf ALLOC
  omega

theorem Bph_false {r : ℕ} (hr : bandOf r ∉ oracleBands) (ha : r ≠ ALLOC) : Bph r = false := by
  have h1 : (1 : ℕ) ∈ oracleBands := ⌖
  have h5 : (5 : ℕ) ∈ oracleBands := ⌖
  have h14 : (14 : ℕ) ∈ oracleBands := ⌖
  have h15 : (15 : ℕ) ∈ oracleBands := ⌖
  unfold bandOf at hr
  have a1 : r / 10000 ≠ 1 := fun h => hr (h ▸ h1)
  have a5 : r / 10000 ≠ 5 := fun h => hr (h ▸ h5)
  have a14 : r / 10000 ≠ 14 := fun h => hr (h ▸ h14)
  have a15 : r / 10000 ≠ 15 := fun h => hr (h ▸ h15)
  have a9 : r ≠ 9999 := ha
  ϴ Bph, Bool.or_eq_false_iff, decide_eq_false_iff_not
  omega

/-- **The ray-shooter meets `ShooterOK`.** -/
theorem shooter_ok {O : OracleIface} (hV : O.Valid) :
    ShooterOK (shooter O.query) oracleBands
      (fun γ => κs O * (Nat.clog 2 γ + 1) * rpowCeil (cutGran γ * (γ + 1) ^ 2) ((1 : ℝ) / 3) +
        κs O) (gradeCtx O) OkModel := by
  intro P W c hw hpre hcost
  obtain ⟨hG, hHW, hX, hcap, hMDWF, hG10, M, hMD, hOk, hsP, heP, hs1, he1, hin1, hin2, hwt, o,
    hoLt, hoIn, hoK, hzA⟩ := hpre
  set MD := c.nreg 140000 with hMDd
  set γ := c.nreg 140009 with hγd
  set h := c.nreg 140013 with hhd
  set A₀ := c.nreg ALLOC with hA₀
  set m₀ := c.nmem with hm₀
  set s : WPos := ⟨c.nreg 140001, c.nreg 140002⟩ with hsd
  set e : WPos := ⟨c.nreg 140003, c.nreg 140004⟩ with hed
  set R := rpowCeil (cutGran γ * (γ + 1) ^ 2) ((1 : ℝ) / 3) with hRd
  set σ := dirOf (c.nreg 140008) with hσd
  replace hX : Robust A₀ m₀ (fun m' => GradeRaw O P m' h A₀) := hX
  replace hcap : γ ≤ 2 ^ (m₀ h - 1) := hcap
  replace hMDWF : ModelDescWF P A₀ m₀ MD := hMDWF
  replace hG10 : m₀ MD = 0 → ∀ H C, ChainDescAt m₀ (MD + 1) (Qof P) H C →
      HostRegular (Qof P).n H := hG10
  replace hMD : ModelDescAt m₀ MD (Qof P) M := hMD
  replace hsP : ProperPos M (Qof P) P.n s := hsP
  replace heP : ProperPos M (Qof P) P.n e := heP
  replace hs1 : s.edge < M.W.n := hs1
  replace he1 : e.edge < M.W.n := he1
  replace hin1 : s.hgt = 0 ∨ M.InnerPt (M.pos (Qof P) s) := hin1
  replace hin2 : e.hgt = 0 ∨ M.InnerPt (M.pos (Qof P) e) := hin2
  replace hwt : M.arcWt (M.key (Qof P) s) (M.key (Qof P) e) ≤ γ := hwt
  replace hoIn : OriginIn c 140005 o := hoIn
  replace hzA : o.eval M (Qof P) ∉ M.arcSet (M.key (Qof P) s) (M.key (Qof P) e) := hzA
  replace hcost : A₀ + (κs O * (Nat.clog 2 γ + 1) * R + κs O) ≤ W := hcost
  -- the chain
  obtain ⟨H₀, C₀, -, -, -, -, hM₀⟩ := hOk
  obtain ⟨h0, H, C, hD, hMC⟩ := modelDesc_chain hMD hM₀
  subst hMC
  obtain ⟨hMD6, hwf6⟩ := hMDWF
  have hwfC := hwf6 h0
  obtain ⟨hlen, hHwf, hHA, hsC⟩ := hwfC.2 H C hD
  have hn3 : 3 ≤ P.n := Chazelle.Jordan.simple_three_le hG.1
  have hAW : A₀ ≤ W := by omega
  have hnW : (chainModel C).W.n = 2 * C.m + 7 := chainModel_n C
  rw [hnW] at hs1 he1
  have S : SEnv O P C H (m₀ (MD + 1)) h γ m₀ A₀ W :=
    ⟨hD.2.1, hD.1, hHA, hHwf, hlen, hsC, hX, hcap, hAW, hHW, by omega, hG⟩
  have hm2 := S.hm2'
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hreg : ∀ H', HostAt m₀ (m₀ (MD + 1)) H' → HostRegular P.n H' := fun H' hH' => by
    have := NFLoc.hostAt_unique hD.1 hH'
    subst this; rw [← hQn]; exact hG10 h0 H C hD
  have hγW : 2 * γ ≤ W := by
    have hG0 := hX.holds
    have hΛ := hG0.1
    have h2 : 2 ^ (m₀ h - 1) ≤ 2 ^ topGrade P.n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 := Setup.pow_topGrade_le (n := P.n) (by omega)
    unfold hostWords at hHW
    omega
  have hlog := Nat.log_le_clog 2 γ
  have hR1 : 1 ≤ R := one_le_rpowCeil γ
  set T := Nat.clog 2 γ + 1 with hT
  have hTR : T ≤ T * R := Nat.le_mul_of_pos_right _ hR1
  have hκ : κs O = 18900 * (2 * O.κ + 600503) + 3000000 := rfl
  have hbig : 3000000 * T ≤ κs O * T * R := by
    have a : 3000000 * T ≤ κs O * T := Nat.mul_le_mul_right _ (by rw [hκ]; omega)
    have b : κs O * T ≤ κs O * T * R := Nat.le_mul_of_pos_right _ hR1
    omega
  have hκ3 : 3000000 ≤ κs O := by rw [hκ]; omega
  -- the inputs of the core
  obtain ⟨c₁, e₁, v₁, k₁, rr₁, m₁, rm₁, o₁⟩ := copies_exec (P := P) (W := W)
    [(150000, 140000), (150001, 140001), (150002, 140002), (150003, 140003), (150004, 140004),
      (150009, 140009), (150013, 140013)] c hw (by first | (simp; done) | (simp; omega))
      (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at v₁
  obtain ⟨v00, v01, v02, v03, v04, v09, v13⟩ := v₁
  have g₁ : ∀ r, r / 10000 ≠ 15 → c₁.nreg r = c.nreg r := fun r hr =>
    k₁ r (by simp; omega)
  have ex₁ := e₁
  have fb₁ : FrameB (fun r => decide (r / 10000 = 15)) c c₁ :=
    ⟨fun r hr => g₁ r (by simpa using hr), fun r _ => by rw [rr₁], m₁, rm₁, o₁⟩
  -- the origin
  have hoIn₁ : OriginIn c₁ 140005 o :=
    originIn_of_eq hoIn fun j h1 h2 => g₁ j (by omega)
  have q00 : c₁.nreg 140000 = MD := g₁ _ (by norm_num)
  have qA : c₁.nreg ALLOC = A₀ := g₁ ALLOC (by decide)
  have hD₁ : ChainDescAt c₁.nmem (c₁.nreg 140000 + 1) (Qof P) H C := by rw [m₁, q00]; exact hD
  have hwf₁ : ChainWF P (c₁.nreg ALLOC) c₁.nmem (c₁.nreg 140000 + 1) := by
    rw [m₁, q00, qA]; exact hwfC
  have hreg₁ : ∀ H', HostAt c₁.nmem (c₁.nmem (c₁.nreg 140000 + 1)) H' → HostRegular P.n H' := by
    rw [m₁, q00]; exact hreg
  have hroom₁ : c₁.nreg ALLOC + 15800 ≤ W := by rw [qA]; omega
  have hMD₁ : c₁.nreg 140000 + 1 ≤ W := by rw [q00]; omega
  obtain ⟨c₂, k₂, e₂, hk₂, E₂, Og₂, f₂, h403⟩ := orig_exec (P := P) (W := W) (H := H) (C := C)
    c₁ e₁.wb_right hG hHW hD₁ hwf₁ hreg₁ hoIn₁ hoLt hoK hroom₁ hMD₁
  rw [g₁ _ (by norm_num)] at E₂ Og₂
  have k₂' := f₂.1
  have mem₂ : c₂.nmem = m₀ := by rw [f₂.2.2.1, m₁]
  have A₂ : c₂.nreg ALLOC = A₀ := by rw [k₂' _ (by decide), g₁ ALLOC (by decide)]
  -- the set-up of the records
  obtain ⟨c₃, k₃, Nmax, e₃, hk₃, hI₃, hNmax, r₃, m₃, rr₃, rm₃, o₃⟩ := shInit_exec (P := P) c₂
    e₂.wb_right (m₀ := m₀) (fun a _ => by rw [mem₂]) (by rw [k₂' _ (by decide), v09]) A₂ hγW
    (by
      have : 18900 * Nat.clog 2 γ + 18910 ≤ 3000000 * T := by omega
      omega)
  have g₃ : ∀ r, 150000 ≤ r → r < 150100 → c₃.nreg r = c₁.nreg r := fun r a b => by
    rw [r₃ r (by omega)]
    have hb : Borg r = false := by
      simp only [Borg, Bld, Bprim, Bool.or_eq_false_iff, decide_eq_false_iff_not,
        beq_eq_false_iff_ne]; omega
    rw [k₂' r hb]
  -- the core
  obtain ⟨c₄, k₄, ps, e₄, hk₄, hI₄, arc, hok, hl, hm₄⟩ := core_exec S
    (shEmit_ok (c₀ := c₂) (PcOK P C m₀ h γ) Nmax) (ps₀ := []) (MD := MD)
    (mode := c₃.nreg 150020) (s := s) (e := e) hD (by omega) rfl c₃ e₃.wb_right
    (fun a _ => by rw [m₃, mem₂]) (by rw [g₃ _ (by norm_num) (by norm_num)]; exact v00)
    (by rw [g₃ _ (by norm_num) (by norm_num)]; exact v01)
    (by rw [g₃ _ (by norm_num) (by norm_num)]; exact v02)
    (by rw [g₃ _ (by norm_num) (by norm_num)]; exact v03)
    (by rw [g₃ _ (by norm_num) (by norm_num)]; exact v04)
    (by rw [g₃ _ (by norm_num) (by norm_num)]; exact v09)
    (by rw [g₃ _ (by norm_num) (by norm_num)]; exact v13) rfl hI₃ hsP heP hs1 he1 hin2 hwt
  rw [List.nil_append] at hI₄
  have hq : ps.length ≤ Nmax := by linarith
  -- the finish of the records
  obtain ⟨c₅, k₅, e₅, hk₅, a₅, aψ, r₅, m₅⟩ := shFin_exec (P := P) c₄ e₄.wb_right hI₄ hq
  have mem₅ : c₅.nmem = c₄.nmem := by rw [m₅]
  have exph : Exec P W shPh c₂ c₅ (k₃ + (k₄ + k₅)) := by unfold shPh; exact .seq e₃ (.seq e₄ e₅)
  have FM := BuildRam.exec_frameM exph wrM_shPh
  have hA₄ := hI₄.alloc
  have hmem₅ : ∀ a, a < A₀ → c₅.nmem a = m₀ a := fun a ha => by rw [mem₅]; exact hm₄ a ha
  have Fph : Frame oracleBands c₂ c₅ (k₃ + (k₄ + k₅)) :=
    ⟨fun r hr ha => FM.1 r (Bph_false hr ha),
      fun r hr => BuildRam.exec_frameM2 exph wrM2_shPh r (BphR_false hr), fun a ha => by rw [hmem₅ a (by rw [← A₂]; exact ha), mem₂],
      fun a _ => by rw [FM.2.2.1], FM.2.2.2, by rw [A₂, a₅]; omega, by rw [A₂]; omega⟩
  -- the loop
  set q := ps.length with hqd
  set K := O.κ * (R + 1) + 600500 with hKd
  have hlq : q ≤ 2100 * T := by omega
  have hlb : 9 * q * (K + 2) ≤ 18900 * (2 * O.κ + 600503) * (T * R) :=
    loop_budget (κO := O.κ) hR1 hlq
  have hsplit : κs O * T * R = 18900 * (2 * O.κ + 600503) * (T * R) + 3000000 * (T * R) := by
    rw [hκ]; ring
  have hTR' : 1 + 9 * q ≤ 3000000 * (T * R) := by
    have : T ≤ T * R := hTR
    omega
  have hQs : (Qof P).Simple := (shearInvariance (epsOf P) P).1 hG.1
  have hsin : s.hgt = 0 ∨ |((chainModel C).pos (Qof P) s).2| < C.radius := by
    rcases hin1 with h' | h'
    · exact Or.inl h'
    · exact Or.inr (innerPt_bounds C h').1
  have hein : e.hgt = 0 ∨ |((chainModel C).pos (Qof P) e).2| < C.radius := by
    rcases hin2 with h' | h'
    · exact Or.inl h'
    · exact Or.inr (innerPt_bounds C h').1
  have X : LpCtx O P W C (o.eval (chainModel C) (Qof P)) m₀ h γ A₀ s e ps :=
    ⟨hV, arc, hok, hsP, heP, hs1, he1, hsin, hein, hwt, hzA, hX, hQs, by
      unfold hostWords at hHW; omega⟩
  have kph := FM.1
  have kenv : ∀ r, envR r → r ≠ ALLOC → c₅.nreg r = c₂.nreg r := fun r hr ha => by
    have hb : Bph r = false := by
      unfold envR at hr; unfold ALLOC at ha
      simp only [Bph, K1, ALLOC, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr ⊢; omega
    exact kph r hb
  have E₅ : ShEnv P W H C (o.eval (chainModel C) (Qof P)) σ c₅ := E₂.of_agree kenv
    (fun a ha => by rw [hmem₅ a (by rw [← A₂]; exact ha), mem₂]) (by rw [A₂, a₅]; omega)
  have korg : ∀ r, 140234 ≤ r → r < 140241 → c₅.nreg r = c₂.nreg r := fun r a b => by
    have hb : Bph r = false := by
      simp only [Bph, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
    exact kph r hb
  have Og₅ := Og₂.keep korg
  have h08₅ : dirOf (c₅.nreg 140008) = σ := by
    rw [kph _ (by decide), k₂' _ (by decide), g₁ _ (by norm_num)]
  obtain ⟨c₆, k₆, e₆, hk₆, hB₆, F₆, E₆⟩ := shLoop_exec (H := H) (σ := σ) (K := K) X le_rfl c₅
    e₅.wb_right E₅ Og₅ h08₅
    (by rw [r₅ _ (by decide), hI₄.ptr, min_eq_left hq])
    (by rw [r₅ _ (by decide)]; exact hI₄.base)
    (by rw [mem₅]; have := hI₄.recs; rwa [List.take_of_length_le hq] at this)
    hmem₅ (by rw [a₅]) (by show c₅.nreg ALLOC + 9 * q * (K + 2) ≤ W; rw [a₅]; omega)
  -- the answer
  obtain ⟨c₇, k₇, e₇, hk₇, u10, u11, u12, r₇, m₇⟩ : ∃ c₇ k₇, Exec P W shEpi c₆ c₇ k₇ ∧ k₇ = 3 ∧
      c₇.nreg 140010 = c₆.nreg 140210 ∧ c₇.nreg 140011 = c₆.nreg 140215 ∧
      c₇.nreg 140012 = c₆.nreg 140216 ∧
      (∀ r, r ≠ 140010 → r ≠ 140011 → r ≠ 140012 → c₇.nreg r = c₆.nreg r) ∧
      c₇ = { c₆ with nreg := c₇.nreg } := by
    have w₆ := e₆.wb_right
    unfold shEpi
    exec_block
    all_goals first | omega | skip
    refine ⟨rfl, by config_simp, by config_simp, by config_simp, fun r h1 h2 h3 => ?_, rfl⟩
    simp only [upd]; split_ifs <;> first | rfl | omega
  have F₇ : Frame oracleBands c₆ c₇ k₇ := by
    refine ⟨fun r hr ha => r₇ r ?_ ?_ ?_, fun r _ => by rw [m₇], fun a _ => by rw [m₇],
      fun a _ => by rw [m₇], by rw [m₇], by rw [r₇ _ (by decide) (by decide) (by decide)],
      by rw [r₇ _ (by decide) (by decide) (by decide)]; omega⟩
    all_goals intro hr'; subst hr'; exact hr (by decide)
  have ex : Exec P W (shooter O.query) c c₇ (7 + (k₂ + ((k₃ + (k₄ + k₅)) + (k₆ + k₇)))) := by
    unfold shooter; exact .seq ex₁ (.seq e₂ (.seq exph (.seq e₆ e₇)))
  have hkt : 7 + (k₂ + ((k₃ + (k₄ + k₅)) + (k₆ + k₇))) ≤ κs O * T * R + κs O := by
    have := shooter_cost (κO := O.κ) (T := T) (L := Nat.log 2 γ) (R := R) (q := q)
      (k₁ := 7) (k₂ := k₂) (k₃ := k₃) (k₄ := k₄) (k₅ := k₅) (k₆ := k₆) (k₇ := k₇) hR1
      (by omega) hl le_rfl hk₂ (by omega) (by unfold coreCost genCost at hk₄; exact hk₄)
      hk₅ (by omega) (by omega)
    rw [hκ]; omega
  refine ⟨c₇, _, ex, hkt, ?_, ?_⟩
  · -- the answer
    intro M' o' hM' hO'
    have hM'C : M' = chainModel C := by
      rcases (show ModelDescAt m₀ MD (Qof P) M' from hM') with ⟨-, H', C', hC', hM''⟩ | ⟨h1, -⟩
      · rw [hM'', chainDesc_unique hC' hD]
      · rw [h0] at h1; exact absurd h1 (by decide)
    subst hM'C
    have ho : o' = o := originIn_unique hO' hoIn
    subst ho
    have hAeq : psSet C (Qof P) ps = (chainModel C).arcSet ((chainModel C).key (Qof P) s)
        ((chainModel C).key (Qof P) e) :=
      (arcSet_pieces arc (key_range hsP hs1) (key_range heP he1)
        (fun q hq => pcOK_keys (hok q hq))).symm
    rw [hAeq] at hB₆
    obtain ⟨-, hb1, hb2⟩ := hB₆
    refine ⟨fun hf => ?_, fun hf => hb1 (by rw [← u10]; exact hf)⟩
    have hf' : c₆.nreg 140210 = 1 := by rw [← u10]; exact hf
    obtain ⟨x, -, hF, hpp, hlt, hpos⟩ := hb2 hf'
    refine ⟨σ * (x - (o'.eval (chainModel C) (Qof P)).1), hF, ?_, ?_, ?_⟩
    · show ProperPos (chainModel C) (Qof P) P.n ⟨c₇.nreg 140011, c₇.nreg 140012⟩
      rw [u11, u12]; exact hpp
    · show c₇.nreg 140011 < (chainModel C).W.n
      rw [u11]; exact hlt
    · show (chainModel C).pos (Qof P) ⟨c₇.nreg 140011, c₇.nreg 140012⟩ =
        Visibility.rayPt (o'.eval (chainModel C) (Qof P)) σ
          (σ * (x - (o'.eval (chainModel C) (Qof P)).1))
      rw [u11, u12, hpos]
      have hσ' : σ = 1 ∨ σ = -1 := E₂.hσ
      ext
      · simp only [Visibility.rayPt_fst]
        rcases hσ' with hs | hs <;> rw [hs] <;> ring
      · simp only [Visibility.rayPt_snd]
  · -- the frame
    have F₁ : Frame oracleBands c c₁ 7 := frame_of_frameB fb₁ (fun r hr =>
      ⟨by simp at hr; unfold bandOf; rw [hr]; decide, by simp at hr; unfold ALLOC; omega⟩) 7
    have F₂ : Frame oracleBands c₁ c₂ k₂ := frame_of_frameB f₂ (fun r hr =>
      ⟨oracleBands_mem r (by have := (Borg_ob r hr).1; omega), (Borg_ob r hr).2⟩) k₂
    have F := F₁.trans (F₂.trans (Fph.trans (F₆.trans F₇)))
    simp only [Finset.union_self] at F
    exact F

end

end ShootCut

end Chazelle.Core
