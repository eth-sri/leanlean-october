module

public import Chazelle.MacT
public import Chazelle.Core.SweepChainT
public import Chazelle.Core.ShotListGLeaf
public import Chazelle.Core.RestoreTPos
public import Chazelle.Core.ShotListCut

section
set_option hygiene false
local macro "zqtm" : tactic => `(tactic| (exec_block; all_goals first | omega | skip; all_goals first | (config_simp; rw [hS.r16]; omega) | skip; all_goals first | (config_simp; rw [hS.r16, m1]; omega) | skip; all_goals first | (config_simp; rw [hS.r16, m1]; omega) | skip; all_goals first | (config_simp; rw [hS.r16, m1, m2']; omega) | skip; all_goals first | (config_simp; rw [hS.r16, m1, m2', m3]; omega) | skip; refine ⟨by_omega, ?_, fun r h1 h2 h3 => ?_, rfl⟩))
local macro "zqtq" : tactic => `(tactic| (have hW := hS.hW; unfold hostWords at hW; have hA := hw.1 ALLOC; have hal := hS.alloc))
local macro "zqtr" : tactic => `(tactic| (obtain ⟨hgΛ, hb⟩ := hblk by_grind; rw [k0 170052 by_decide by_decide] at hgΛ hb; rw [c51] at hb))
local macro "zqtx" : tactic => `(tactic| (config_simp; zunse; have := hlow.2.2 _ hq; have := hS.alloc; have := hw.1 ALLOC; omega))
local macro "zqua" : tactic => `(tactic| refine ⟨rfl, ?_, fun r h1 h2 h3 => ?_, rfl⟩)
local macro "zqub" : tactic => `(tactic| (config_simp; rw [ite_eq_right by_omega, hS.r16, m1, m2', m3]))
set_option hygiene true

/-!
# WP-M (E7-B, RAM part 4): the top of a chain by the grade table (O5)

`topLoop` runs the bottom-up dyadic cover of the vertex range `[x, y]` of `Q`
(`y ≤ n - 1`), one grade per iteration (registers `170050` `q_l`, `170051` `q_r`, `170052` the
grade `g`, `170053` `2^g`, `170054` `lo = q_l 2^g`, `170055` `hi = q_r 2^g`): an odd `q_l`
contributes the block `(g, q_l)` (its top from the grade table, or its end vertex for `g = 0`),
an odd `q_r` the block `(g, q_r - 1)`; the running maximum `170046` (a vertex index of `Q`) is
kept by one sign test per block (`cmpUpd`).  Invariant (`TopI`): every vertex of `[x, lo]` and of
`[hi, y]` is at most as high as the running maximum.
-/
namespace Chazelle.Core
namespace IOrc
open Machine Machine.Stmt Programs SignK WalkKey
@[expose] public section
def parL : Stmt :=
  block [.addN 170056 170017 170050, .loadN 170057 170056, .subN 170058 170050 170057,
    .subN 170058 170058 170057]

/-- `170058 := q_r mod 2`. -/
def parR : Stmt :=
  block [.addN 170056 170017 170051, .loadN 170057 170056, .subN 170058 170051 170057,
    .subN 170058 170058 170057]

/-- The candidate of the block `(g, q_l)` starting at `lo`: its end vertex for `g = 0`, else its top read from the grade table. -/
def candL : Stmt :=
  .ifLtN 170052 170011 (block [.addN 170059 170054 170011])
    (block [.addN 170056 170016 170052, .loadN 170056 170056, .addN 170056 170056 170050,
      .addN 170056 170056 170050, .addN 170056 170056 170050, .loadN 170056 170056,
      .constN 170067 3, .addN 170056 170056 170067, .loadN 170056 170056,
      .addN 170059 170054 170056])

/-- The right candidate for `g = 0` is the start of the block (its end is covered). -/
def candR : Stmt :=
  .ifLtN 170052 170011 (block [.copyN 170059 170055])
    (block [.addN 170056 170016 170052, .loadN 170056 170056, .addN 170056 170056 170051,
      .addN 170056 170056 170051, .addN 170056 170056 170051, .loadN 170056 170056,
      .constN 170067 3, .addN 170056 170056 170067, .loadN 170056 170056,
      .addN 170059 170055 170056])

/-- The running maximum: `170046 := 170059` if it is higher. -/
def cmpUpd : Stmt :=
  .seq ztcqs
    (.seq (SweepPrim.kbit 170060 170063 170060 1 170066)
      (.ifLtN 170012 170066 (block [.copyN 170046 170059]) .skip))

/-- The left block of a grade (if `q_l` is odd). -/
def stepL : Stmt :=
  .ifLtN 170012 170058
    (.seq candL (.seq cmpUpd (block [.addN 170050 170050 170011, .addN 170054 170054 170053])))
    .skip

/-- The right block of a grade (if `q_r` is odd). -/
def stepR : Stmt :=
  .ifLtN 170012 170058
    (.seq (block [.subN 170051 170051 170011, .subN 170055 170055 170053]) (.seq candR cmpUpd))
    .skip

/-- The next grade. -/
def halve : Stmt :=
  block [.addN 170056 170017 170050, .loadN 170050 170056, .addN 170056 170017 170051,
    .loadN 170051 170056, .addN 170052 170052 170011, .addN 170053 170053 170053]

/-- One grade of the cover. -/
def topBody : Stmt := .seq parL (.seq stepL (.seq parR (.seq stepR halve)))

/-- **The cover of `[x, y]`** (`x` in `170050`, `y` in `170051` on entry; the maximum already
covers both ends). -/
def topLoop : Stmt :=
  .seq ztcqr
    (.whileLtN 170050 170051 topBody)

/-- The registers the top computation writes. -/
def Btop (r : ℕ) : Bool := decide ztgxy || Bk r
theorem wr_kbit_top (a b d op dst : ℕ) (h1 : 170046 ≤ dst) (h2 : dst < 170070) :
    wr Btop (SweepPrim.kbit a b d op dst) = true :=
  SweepPrim.wr_mono (SweepPrim.wr_kbit a b d op dst) (fun r hr => by
    simp only [SweepPrim.Bkb, Bool.or_eq_true, beq_iff_eq] at hr
    unfold Btop; grind)
theorem wr_cmpUpd : wr Btop cmpUpd = true := by
  rfl
theorem wr_topLoop : wr Btop topLoop = true := by
  rfl

/-! ## The steps -/
section steps
variable {P : Polygon} {W : ℕ} {O : OracleIface} {s : Stat}

/-- The height of vertex `v` of `Q`. -/
noncomputable abbrev Y (P : Polygon) (v : ℕ) : ℝ := ((Qof P).vtx v).2

/-- **The parity of `q_l`.** -/
theorem parL_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c)
    (hq : c.nreg 170050 ≤ P.n) :
    ∃ c' k, Exec P W parL c c' k ∧ k = 4 ∧ c'.nreg 170058 = c.nreg 170050 % 2 ∧
      ztbkx ∧ c'.nmem = c.nmem := by
  zuwj

  have hm : ztbxb := by
    zucjm
  zucg

  unfold parL
  exec_block
  · zqtx
  zqua
  · config_simp; rw [hS.r17, hm]; omega
  simp_all

/-- **The parity of `q_r`.** -/
theorem parR_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c)
    (hq : c.nreg 170051 ≤ P.n) :
    ∃ c' k, Exec P W parR c c' k ∧ k = 4 ∧ c'.nreg 170058 = c.nreg 170051 % 2 ∧
      ztbkx ∧ c'.nmem = c.nmem := by
  zuwj

  have hm : ztbxc := by
    zucjm
  unfold parR
  exec_block
  · zqtx
  zqua
  · config_simp; rw [hS.r17, hm]; omega
  simp_all

/-- The top index read from the descriptor of the block `(g, b)`. -/
def blkT (m : ℕ → ℕ) (h g b : ℕ) : ℕ := m ztepg

/-- **The left candidate**: the end vertex `lo + 1` of an edge (`g = 0`), else the top of the
block `(g, q_l)` from the grade table. -/
theorem candL_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c)
    (hblk : 1 ≤ c.nreg 170052 → c.nreg 170052 < s.m₀ s.h ∧
      zteeo * 2 ^ c.nreg 170052 ≤ P.n - 1)
    (hlo : c.nreg 170054 + 2 ^ c.nreg 170052 ≤ P.n) :
    ∃ c' k, Exec P W candL c c' k ∧ k ≤ 12 ∧
      c'.nreg 170059 = (if c.nreg 170052 = 0 then c.nreg 170054 + 1 else
        c.nreg 170054 + blkT s.m₀ s.h ztmfu ztvhr) ∧
      ztbky ∧ c'.nmem = c.nmem := by
  zqtq
  unfold candL
  zucfm
  · zudfg

    exec_block
    · config_simp; rw [hS.r11]; grind
    refine ztdxc
    · config_simp; rw [ite_eq_left hg0, hS.r11]
    simp_all
  · zurb

    have m1 : ztiza :=
      hS.mem _ ar
    have m2 : c.nmem _ =
        blkD s.m₀ s.h _ _ := hS.mem _ ae
    have m3 : c.nmem _ =
        blkT s.m₀ s.h _ _ := hS.mem _ ad
    zudpa
    have m2' : c.nmem (s.m₀ ztdpl + c.nreg 170050 + c.nreg 170050 +
        c.nreg 170050) = blkD s.m₀ s.h (c.nreg 170052) (c.nreg 170050) := by
      grind
    have hTb' : ztdxp := hTb
    zqtm
    · zqub
    simp_all

/-- **The right candidate**: the start vertex `hi` of an edge (`g = 0`), else the top of the
block `(g, q_r)` (after the decrement). -/
theorem candR_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c)
    (hblk : 1 ≤ c.nreg 170052 → c.nreg 170052 < s.m₀ s.h ∧
      ztrlr * 2 ^ c.nreg 170052 ≤ P.n - 1)
    (hhi : c.nreg 170055 + 2 ^ c.nreg 170052 ≤ P.n) :
    ∃ c' k, Exec P W candR c c' k ∧ k ≤ 12 ∧
      c'.nreg 170059 = (if c.nreg 170052 = 0 then c.nreg 170055 else
        c.nreg 170055 + blkT s.m₀ s.h ztmfu ztvhs) ∧
      ztbky ∧ c'.nmem = c.nmem := by
  zqtq
  unfold candR
  zucfm
  · zudfg

    exec_block
    simp_all
  · zurb

    have m1 : ztiza :=
      hS.mem _ ar
    have m2 : c.nmem _ =
        blkD s.m₀ s.h _ _ := hS.mem _ ae
    have m3 : c.nmem _ =
        blkT s.m₀ s.h _ _ := hS.mem _ ad
    zudpa
    have m2' : c.nmem (s.m₀ ztdpl + c.nreg 170051 + c.nreg 170051 +
        c.nreg 170051) = blkD s.m₀ s.h (c.nreg 170052) (c.nreg 170051) := by
      grind
    have hTb' : ztdxp := hTb
    zqtm
    · zqub
    simp_all

/-- **The running maximum.** -/
theorem cmpUpd_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c)
    (hv : c.nreg 170046 < P.n) (hc : c.nreg 170059 < P.n) :
    ∃ c' k, Exec P W cmpUpd c c' k ∧ k ≤ 250 ∧
      c'.nreg 170046 = (if Y P ztyh < Y P zthum then c.nreg 170059
        else c.nreg 170046) ∧
      (∀ r, r ≠ 170046 → zteuz → ztcu →
        c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem := by
  zucwc
  obtain ⟨c₁, k₁, e₁, hk₁, h60, h61, h63, h64, r₁, m₁⟩ : ∃ c₁ k₁, Exec P W
      ztcqs
      c c₁ k₁ ∧ k₁ = 4 ∧ c₁.nreg 170060 = 0 ∧ c₁.nreg 170061 = c.nreg 170046 ∧
      c₁.nreg 170063 = 0 ∧ c₁.nreg 170064 = c.nreg 170059 ∧
      ztegq ∧
      c₁.nmem = c.nmem := by
    exec_block
    all_goals first | omega | skip
    simp_all
  zufhs

  obtain ⟨c₂, k₂, e₂, hk₂, F₂, b₂, t₂⟩ := SweepPrim.kbit_exec (P := P) hS.good hW c₁ e₁.wb_right
    (a := 170060) (b := 170063) (d := 170060) (op := 1) (dst := 170066) by_norm_num
    by_norm_num by_norm_num by_norm_num by_norm_num (sa := .vtx ztyh)
    (sb := .vtx zthum) (sd := .vtx ztyh) hv hc hv s1 s2 s1
  zubzp
  have k2 : zthpf := fun r h1 h2 =>
    F₂.1 r (by simp only [SweepPrim.Bkb, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not,
      beq_eq_false_iff_ne]; omega)
  zue
  have hfr : ∀ r, r ≠ 170046 → zteuz → ztcu →
      c₂.nreg r = c.nreg r := fun r h1 h2 h3 => by
    rw [F₂.1 r (by simp only [SweepPrim.Bkb, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not,
      beq_eq_false_iff_ne]; omega), r₁ r by_omega by_omega by_omega
      by_omega]
  zudgy
  have c59 : ztsgy := by
    simp_all
  have c46 : ztsgx := by
    simp_all
  zuhsv
  · have hy : Y P _ < Y P _ := t₂.1 by_omega
    have e₃ := exec_copyN_upd (P := P) w₂ 170046 170059
    refine ztdqh
    · zumb
    · zugzr
    · show c₂.nmem = c.nmem; zuoji
  · have hy : ¬ Y P ztyh < Y P zthum := by_grind
    refine ⟨_, _, .seq e₁ ztyof, by_omega, ?_,
      by omega, ?_⟩
    · grind
    · zukpi

/-! ## The invariant of the cover -/

/-- **The invariant of the cover of `[x, y]`**: the grade registers, the covered ranges `[x, lo]`
and `[hi, y]` below the running maximum, which is a good vertex. -/
structure TopI (P : Polygon) (W : ℕ) (O : OracleIface) (s : Stat) (x y : ℕ) (G : ℕ → Prop)
    (c : Config) : Prop where
  env : SEnv P W O s c
  pw : c.nreg 170053 = 2 ^ c.nreg 170052
  lo : c.nreg 170054 = c.nreg 170050 * c.nreg 170053
  hi : c.nreg 170055 = c.nreg 170051 * c.nreg 170053
  xlo : x ≤ c.nreg 170054
  qq : c.nreg 170050 ≤ c.nreg 170051
  hiy : c.nreg 170055 ≤ y
  yn : y ≤ P.n - 1
  cap : y - x ≤ 2 ^ ztbwe
  vbG : G ztyh
  vbn : c.nreg 170046 < P.n
  cov : ∀ v, ztmpj ∨ ztmfv →
    Y P v ≤ Y P ztyh
  good : ∀ v, x ≤ v → v ≤ y → G v
variable {x y : ℕ} {G : ℕ → Prop}
theorem TopI.keep {c c' : Config} (hI : TopI P W O s x y G c)
    (hk : ∀ r, ztekm ∨ ztnev → c'.nreg r = c.nreg r)
    (hm : c'.nmem = c.nmem) (hA : c'.nreg ALLOC = c.nreg ALLOC) : TopI P W O s x y G c' := by
  zulo

  refine ⟨hI.env.keep by_simp_all by_simp_all
    ztchd, ?_, ?_, ?_, ?_, ?_, ?_, hI.yn, hI.cap, ?_, ?_, ?_, hI.good⟩
  zudco
  · exact hI.pw
  · exact hI.lo
  · exact hI.hi
  · exact hI.xlo
  · exact hI.qq
  · exact hI.hiy
  · zulyo
  · zulyp
  · zulym
theorem pow_le_of_cap {g Λ d : ℕ} (hg : 1 ≤ g) (h1 : 2 ^ g ≤ d) (h2 : d ≤ 2 ^ ztufb) :
    g < Λ := by
  have h3 := h1.trans h2
  have h4 := (Nat.pow_le_pow_iff_right by_norm_num).1 h3
  omega
theorem Y_max_le {P : Polygon} {a b : ℕ} :
    Y P a ≤ Y P ztisz ∧ Y P b ≤ Y P ztisz := by
  grind

/-- **The left block of a grade.** -/
theorem stepL_exec (c : Config) (hw : WordsBounded W c)
    (hI : TopI P W O s x y G c) (hpar : c.nreg 170058 = c.nreg 170050 % 2)
    (hlt : c.nreg 170050 < c.nreg 170051) :
    ∃ c' k, Exec P W stepL c c' k ∧ k ≤ 280 ∧ TopI P W O s x y G c' ∧
      c'.nreg 170050 = c.nreg 170050 + c.nreg 170050 % 2 ∧ c'.nreg 170051 = c.nreg 170051 ∧
      c'.nreg 170052 = c.nreg 170052 ∧
      ztwjo ∧
      Y P ztyh ≤ Y P ztbso ∧ c'.nmem = c.nmem := by
  zuccv

  zugmh

  have hprod : ztxzx := by
    grind
  have hloHi : ztfdo := by
    zubva
    have : ztbfq :=
      Nat.mul_le_mul_right _ by_omega
    simp_all
  zucdi

  have hqlo : ztguf := by
    zugeb
  have hblk : 1 ≤ c.nreg 170052 → c.nreg 170052 < s.m₀ s.h ∧
      zteeo * 2 ^ c.nreg 170052 ≤ P.n - 1 := fun hg1 =>
    ⟨pow_le_of_cap hg1 by_omega hI.cap, by_omega⟩
  unfold stepL
  zucfo
  · zubed

    -- the candidate

    have hcand : ztcpe := by
      zudau

      · omega
      · zubxp
        zudoa

    -- every vertex of the block is below the candidate
    have hblkv : ∀ v, c.nreg 170054 < v → v ≤ c.nreg 170054 + c.nreg 170053 →
        Y P v ≤ Y P ztmia := by
      zugoo
      zudau

      · grind
      · zubxp
        have hT := (block_top hS.grade hgΛ hb).2.2.2.2.2 ztibo by_omega
        zucam

    have S₁ := hS.keep ztdda
      by_grind ztbvs
    zukiv
    obtain ⟨c₂, k₂, e₂, hk₂, v46', r₂, m₂⟩ := cmpUpd_exec c₁ e₁.wb_right S₁
      ztdyy hcand.1
    have k2 : ∀ r, ztmt → ztcu →
        c₂.nreg r = c.nreg r := fun r h1 h2 => by
      zuemp
    have k2' : zthpj := fun r h1 h2 => by
      zuemo
    have S₂ := S₁.keep (fun r h1 h2 => by
        zunyj) by_grind (by
        zunbx)
    zue
    zucmf
    zudkt

    zucg

    exec_block
    · config_simp; rw [k2' _ by_norm_num by_norm_num, S₂.r11]; omega
    · config_simp; rw [k2' _ by_norm_num by_norm_num, k2' _ by_norm_num by_norm_num]
      omega
    refine ⟨by_omega, ⟨S₂.keep (fun r h1 h2 => by
          zumyp; zvmyn)
        by_grind by_rfl, ?_, ?_, ?_, ?_, ?_, ?_, hI.yn, hI.cap, ?_, ?_, ?_,
        hI.good⟩, ?_, ?_, ?_, fun r h1 h2 => ?_, ?_, m₂.trans m₁⟩
    all_goals config_simp
    zujru
    zumc

    · omega
    · grind
    · omega
    · omega
    · omega
    · omega
    · zubbj
      · zueox
      · zudas
    · zubbj
      · omega
      · zudat
    · zuml
      zucuu
      · zucfs
      zucuv
      · zucfs
      · zubvu
    · omega
    · zucui
    grind
  · zucbw

/-- The configuration after the decrement of `q_r` and `hi`. -/
def decCfg (c : Config) : Config :=
  { c with nreg := upd (upd c.nreg 170051 (c.nreg 170051 - c.nreg 170011)) 170055
                          (c.nreg 170055 - c.nreg 170053) }

/-- **The right block of a grade.** -/
theorem stepR_exec (c : Config) (hw : WordsBounded W c)
    (hI : TopI P W O s x y G c) (hpar : c.nreg 170058 = c.nreg 170051 % 2)
    (hlt : c.nreg 170051 % 2 = 1 → c.nreg 170050 < c.nreg 170051) :
    ∃ c' k, Exec P W stepR c c' k ∧ k ≤ 280 ∧ TopI P W O s x y G c' ∧
      c'.nreg 170051 = c.nreg 170051 - c.nreg 170051 % 2 ∧ c'.nreg 170050 = c.nreg 170050 ∧
      c'.nreg 170052 = c.nreg 170052 ∧
      ztwjo ∧
      Y P ztyh ≤ Y P ztbso ∧ c'.nmem = c.nmem := by
  zuccv

  zugmh

  zucdi

  unfold stepR
  zucfo
  · zuecb

    have hprod : c.nreg 170051 * c.nreg 170053 = ztrls * c.nreg 170053 +
        c.nreg 170053 := by
      zukpv
      have : ztoqo :=
        Nat.le_mul_of_pos_left _ by_omega
      omega
    have hloHi : ztfdo := by
      zubva
      have : ztbfq :=
        Nat.mul_le_mul_right _ by_omega
      grind
    refine spec_seq ?_
    exec_block
    -- the configuration after the decrement
    set c₀ : Config := decCfg c with hc₀
    zuibl
    have k0 : zthpn := fun r a b => by
      zunad; simp [decCfg, upd, a, b]
    have c51 : ztpmp := by zunad; simp only [decCfg]; config_simp; zvnem
    zujwv
    have S₀ : SEnv P W O s c₀ := hS.keep by_grind
      ztcve by_rfl
    have hblk : 1 ≤ c₀.nreg 170052 → c₀.nreg 170052 < s.m₀ s.h ∧
        ztrny * 2 ^ c₀.nreg 170052 ≤ P.n - 1 := fun hg1 => by
      zugvx
      refine ⟨pow_le_of_cap hg1 by_omega hI.cap, ?_⟩
      grind
    obtain ⟨c₁, k₁, e₁, hk₁, v59, r₁, m₁⟩ := candR_exec c₀ w₀ S₀ hblk (by
      grind)
    zuexa
    have hcand : ztcpe := by
      zudau

      · omega
      · zqtr
        zudoa

    have hblkv : ∀ v, c.nreg 170055 - c.nreg 170053 ≤ v → v < c.nreg 170055 →
        Y P v ≤ Y P ztmia := by
      zugoo
      zudau

      · zudcs

      · zqtr
        have hT := (block_top hS.grade hgΛ hb).2.2.2.2.2 ztdpu
          by_omega
        have e1 : ztgtk := by
          zuhnx
        rw [e1, show c.nreg 170055 - c.nreg 170053 + ztdpu = v by
          omega] at hT
        exact hT
    have S₁ := S₀.keep ztdda
      by_grind ztbvs
    have v46 : ztizj := by
      grind
    obtain ⟨c₂, k₂, e₂, hk₂, v46', r₂, m₂⟩ := cmpUpd_exec c₁ e₁.wb_right S₁
      ztdyy hcand.1
    zucmf
    zudvp

    have k2' : zthpk := fun r h1 h2 => by
      zuemo
    refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by_omega, ⟨S₁.keep (fun r h1 h2 =>
        r₂ r by_omega by_omega by_omega) by_grind (by
        zunbx), ?_, ?_, ?_, ?_, ?_, ?_, hI.yn, hI.cap, ?_,
        ?_, ?_, hI.good⟩, ?_, ?_, ?_, fun r h1 h2 => ?_, ?_, m₂.trans m₁⟩
    zumc

    zupk

    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · zubbj
      · zueox
      · zudas
    · zubbj
      · omega
      · zudat
    · zuml
      zucuu
      · zucft
      zucuv
      · zucft
      · zubvu
    · omega
    · rw [r₂ r by_omega by_omega h2, r₁ r by_omega by_omega by_omega,
        k0 r by_omega by_omega]
    grind
  · zucbx

/-- **The next grade**: halve `q_l`, `q_r` (both even), double `2^g`. -/
theorem halve_exec (c : Config) (hw : WordsBounded W c)
    (hI : TopI P W O s x y G c) (hl : c.nreg 170050 % 2 = 0) (hr : c.nreg 170051 % 2 = 0)
    (hpn : c.nreg 170053 ≤ P.n) :
    ∃ c' k, Exec P W halve c c' k ∧ k = 6 ∧ TopI P W O s x y G c' ∧
      c'.nreg 170050 = c.nreg 170050 / 2 ∧ c'.nreg 170051 = c.nreg 170051 / 2 ∧
      ztybv ∧
      c'.nreg 170046 = c.nreg 170046 ∧ c'.nmem = c.nmem := by
  zuheo

  have hpw := hI.pw
  zumdx
  zuon

  zudzn
  zucdi

  zudpb

  have h50 : ztbxb := by
    zuelt
  have h51 : ztbxc := by
    zuelu
  zueqy
  zqtq
  zufey

  unfold halve
  exec_block
  all_goals first
    | (config_simp; zunse; omega)
    | (config_simp; zuojj; omega)
    | (config_simp; zvnem; omega)
    | (config_simp; omega)
    | skip
  refine ⟨rfl, ⟨hS.keep (fun r h1 h2 => by
      zumyp; grind) by_simp_all
      by_rfl, ?_, ?_, ?_, ?_, ?_, ?_, hI.yn, hI.cap, ?_, ?_, ?_, hI.good⟩,
    ?_, ?_, fun r h1 => ?_, ?_, rfl⟩
  all_goals config_simp
  all_goals try rw [hS.r17]
  all_goals try rw [h50]
  all_goals try rw [h51]
  all_goals try rw [hS.r11]
  · omega
  · zuemc

    zubpz
  · zuelw

    zubpz
  · omega
  · omega
  · omega
  · zulyo
  · zulyp
  · zulym
  · zubd

/-- **One grade of the cover.** -/
theorem topBody_exec (c : Config) (hw : WordsBounded W c)
    (hI : TopI P W O s x y G c) (hlt : c.nreg 170050 < c.nreg 170051) :
    ∃ c' k, Exec P W topBody c c' k ∧ k ≤ 600 ∧ TopI P W O s x y G c' ∧
      2 * ztqgx ≤ c.nreg 170051 - c.nreg 170050 ∧
      ztwjo ∧
      Y P ztyh ≤ Y P ztbso ∧ c'.nmem = c.nmem := by
  zuccv

  zuon

  zudzn
  have hpn : ztunt := by
    have : ztbfq :=
      by simp_all
    zuelc
    have := hI.hiy; have := hI.yn; omega
  -- `q_l`
  zubdx
  have I₁ := hI.keep by_grind
    m₁ ztqvr
  zuffg

  obtain ⟨c₂, k₂, e₂, hk₂, I₂, q50, q51, q52, r₂, y₂, m₂⟩ := stepL_exec c₁ e₁.wb_right I₁
    by_omega by_omega
  -- `q_r`
  obtain ⟨c₃, k₃, e₃, hk₃, p₃, r₃, m₃⟩ := parR_exec c₂ e₂.wb_right I₂.env
    (by have := I₂.hiy; have := I₂.yn; have := I₂.hi; have := I₂.pw
        grind)
  have I₃ := I₂.keep ztlot
    m₃ ztqvs
  zuffn

  obtain ⟨c₄, k₄, e₄, hk₄, I₄, s51, s50, s52, r₄, y₄, m₄⟩ := stepR_exec c₃ e₃.wb_right I₃
    by_omega (by
      omega)
  have hpn4 : ztuss := by
    have g3 : ztshn := by
      zudvh
    zuewr
  obtain ⟨c₅, k₅, e₅, hk₅, I₅, t50, t51, r₅, y₅, m₅⟩ := halve_exec c₄ e₄.wb_right I₄
    by_omega
    by_omega
    hpn4
  zuctv

  refine ⟨c₅, _, .seq e₁ ztbq, by_omega, I₅, ?_, fun r h1 h2 => ?_,
    by grind, by_grind⟩
  · zuccf
  · rw [r₅ r h1, r₄ r h1 h2, r₃ r by_omega by_omega by_omega, r₂ r h1 h2,
      r₁ r by_omega by_omega by_omega]

/-- The potential of the cover drops under halving: `2 d' ≤ d`, `0 < d` give
`log (2 d') < log (2 d)`. -/
theorem log_half_lt {d d' : ℕ} (h : 2 * d' ≤ d) (hd : 0 < d) :
    Nat.log 2 (2 * d') < Nat.log 2 ztnfd := by
  have e : Nat.log 2 ztnfd = Nat.log 2 d + 1 := by
    zuhnb
  zui
  have := Nat.log_mono_right (b := 2) h
  omega

/-- **The cover of `[x, y]`.**  From `q_l = x ≤ y = q_r` (`y ≤ n - 1`, `y - x` within the cap)
and a running maximum `170046` at least as high as both ends, `topLoop` ends with a running
maximum at least as high as every vertex of `[x, y]`, within `602 size (y - x) + 6` steps. -/
theorem topLoop_exec (c : Config) (hw : WordsBounded W c)
    (hS : SEnv P W O s c) (hx : c.nreg 170050 = x) (hy : c.nreg 170051 = y) (hxy : x ≤ y)
    (hyn : y ≤ P.n - 1) (hcap : y - x ≤ 2 ^ ztbwe) (hvG : G ztyh)
    (hvn : c.nreg 170046 < P.n) (hvx : Y P x ≤ Y P ztyh)
    (hvy : Y P y ≤ Y P ztyh) (hgood : ∀ v, x ≤ v → v ≤ y → G v) :
    ∃ c' k, Exec P W topLoop c c' k ∧ k ≤ 602 * Nat.log 2 zteks + 6 ∧ SEnv P W O s c' ∧
      G ztbso ∧ c'.nreg 170046 < P.n ∧
      ztwrd ∧
      ztwjo ∧
      Y P ztyh ≤ Y P ztbso ∧ c'.nmem = c.nmem := by
  obtain ⟨c₀, k₀, e₀, hk₀, I₀, h50, h51, h46, r₀, m₀⟩ : ∃ c₀ k₀, Exec P W
      ztcqr
      c c₀ k₀ ∧ k₀ = 4 ∧ TopI P W O s x y G c₀ ∧ c₀.nreg 170050 = x ∧ c₀.nreg 170051 = y ∧
      c₀.nreg 170046 = c.nreg 170046 ∧
      ztybw ∧ c₀.nmem = c.nmem := by
    zumee
    exec_block
    all_goals first | omega | skip
    refine ⟨rfl, ⟨hS.keep (fun r h1 h2 => by
        zumyp; grind) by_simp_all
        by_rfl, ?_, ?_, ?_, ?_, ?_, ?_, hyn, hcap, ?_, ?_, ?_, hgood⟩,
      ?_, ?_, ?_, fun r h1 => ?_, rfl⟩
    all_goals config_simp
    all_goals try rw [hx]
    all_goals try rw [hy]
    all_goals try (first | exact hvG | exact hvn | omega | simp; done)
    · grind
    · zubd
  let I : Config → Prop := fun c' => TopI P W O s x y G c' ∧ WordsBounded W c' ∧
    ztwjo ∧
    Y P ztyh ≤ Y P ztbso ∧ c'.nmem = c.nmem
  obtain ⟨c', k, e, ⟨I', w', f', y', m'⟩, hex, hk⟩ := Exec.whileLtN_potential (P := P) (W := W)
    (a := 170050) (b := 170051) (body := topBody) I
    ztfye ztqng
    (fun c₁ ⟨I₁, w₁, f₁, y₁, m₁⟩ hlt => by
      zubty
      refine ⟨c₂, k₂, e₂, ⟨I₂, e₂.wb_right, by_simp_all,
        y₁.trans y₂, m₂.trans m₁⟩, ?_⟩
      have := log_half_lt hd by_omega
      grind)
    (c := c₀) ztfjt
  zubcc
end steps
end
end IOrc
end Chazelle.Core
end
section
set_option hygiene false
local macro "zqbap" : tactic => `(tactic| (exec_block
                                           all_goals first | omega | skip
                                           all_goals first | (config_simp; rw [hS.r16]; omega) | skip
                                           all_goals first | (config_simp; rw [hS.r16, m1]; omega) | skip
                                           all_goals first | (config_simp; rw [hS.r16, m1]; omega) | skip
                                           all_goals first | (config_simp; rw [hS.r16, m1, m2']; omega) | skip
                                           all_goals first | (config_simp; rw [hS.r16, m1, m2', m3]; omega) | skip
                                           refine ztdxc))
local macro "zqbaq" : tactic => `(tactic| (all_goals try rw [k2' 170050 by_norm_num by_norm_num]
                                           all_goals try rw [k2' 170051 by_norm_num by_norm_num]
                                           all_goals try rw [k2' 170052 by_norm_num by_norm_num]
                                           all_goals try rw [k2' 170053 by_norm_num by_norm_num]
                                           all_goals try rw [k2' 170054 by_norm_num by_norm_num]
                                           all_goals try rw [k2' 170055 by_norm_num by_norm_num]))
local macro "zqbar" : tactic => `(tactic| (have hpw := hI.pw
                                           have hlo := hI.lo
                                           zuon

                                           have hqhi : ztmun := by rw [hhi]; exact Nat.le_mul_of_pos_right _ hp1))
local macro "zqbas" : tactic => `(tactic| (refine spec_ifLtN_false hg ?_
                                           have hg1 : ztphz := by zvnem at hg; omega
                                           obtain ⟨hgΛ, hb⟩ := hblk hg1
                                           obtain ⟨a2, ar, ae, ad, hTb, -⟩ := IOrc.block_top hS.grade hgΛ hb))
local macro "zqbat" : tactic => `(tactic| (obtain ⟨hgΛ, hb⟩ := hblk by_grind
                                           rw [k0 170052 by_decide by_decide] at hgΛ hb; rw [c51] at hb))
local macro "zqbau" : tactic => `(tactic| rw [r₂ r by_omega by_omega by_omega, r₁ r by_omega by_omega by_omega])
local macro "zqbav" : tactic => `(tactic| (have hW := hS.hW
                                           unfold hostWords at hW
                                           zuhea
                                           have hal := hS.alloc))
local macro "zqbaw" : tactic => `(tactic| (have hS := hI.env
                                           have hpw := hI.pw
                                           zumdx
                                           have hhi := hI.hi
                                           have hp1 : ztdjp := Nat.one_le_two_pow))
local macro "zqbax" : tactic => `(tactic| (have hT := (IOrc.block_top hS.grade hgΛ hb).2.2.2.2.1
                                           have : ztgal := hT
                                           omega))
local macro "zqbay" : tactic => `(tactic| (have hxlo := hI.xlo
                                           have hhiy := hI.hiy
                                           have hyn := hI.yn))
local macro "zqbaz" : tactic => `(tactic| have hmx := IOrc.Y_max_le (P := P) (a := c.nreg 170046) (b := c₁.nreg 170059))
local macro "zqbba" : tactic => `(tactic| (config_simp; zunse; have := hlow.2.2 _ hq; have := hS.alloc; have := hw.1 ALLOC
                                           omega))
local macro "zqbbb" : tactic => `(tactic| (refine spec_ifLtN_true hg ?_
                                           have hg0 : ztply := by zvnem at hg; omega
                                           exec_block))
local macro "zqbbc" : tactic => `(tactic| (rw [v59]
                                           split_ifs with hg0))
local macro "zqbbd" : tactic => `(tactic| refine ⟨rfl, ?_, fun r h1 h2 h3 => ?_, rfl⟩)
local macro "zqbbe" : tactic => `(tactic| (config_simp; rw [ite_eq_right by_omega, hS.r16, m1, m2', m3]))
set_option hygiene true

/-!
# Down-phase pieces (D4), part 1: the grade-table cover with a light environment

A port of the grade-table cover of the interior oracles (`IOrc.topLoop`, file `DownPhaseOracleTop`) to
a light static environment `TEnv` (the grade table of the up-phase data robust below `A₀`, the
memory below `A₀` unchanged, the registers `170011 = 1`, `170012 = 0`, `170016`, `170017` the
row and halving tables), without the adapter's other registers.  The programs are those of
`IOrc` (registers `170046 … 170069` of band `17`, and the sign kernel); only the proofs are
redone (`topLoop_exec`).
-/
namespace Chazelle.Core
namespace DrvP
open Machine Machine.Stmt Programs SignK WalkKey
@[expose] public section
structure TSt where
  /-- The entry allocator. -/
  A₀ : ℕ
  /-- The entry memory. -/
  m₀ : ℕ → ℕ
  /-- The handle of the up-phase data. -/
  h : ℕ

/-- **The light static environment** of the cover. -/
structure TEnv (P : Polygon) (W : ℕ) (O : OracleIface) (s : TSt) (c : Config) : Prop where
  good : GoodEnv P
  hW : hostWords P.n ≤ W
  r11 : c.nreg 170011 = 1
  r12 : c.nreg 170012 = 0
  r16 : c.nreg 170016 = s.m₀ ztohm
  r17 : c.nreg 170017 = s.m₀ ztkeo
  mem : ∀ a, a < s.A₀ → c.nmem a = s.m₀ a
  alloc : s.A₀ ≤ c.nreg ALLOC
  grade : Robust s.A₀ s.m₀ ztfrr
namespace TEnv
variable {P : Polygon} {W : ℕ} {O : OracleIface} {s : TSt} {c c' : Config}
theorem keep (h : TEnv P W O s c) (hr : ∀ r, 170000 ≤ r → r < 170030 → c'.nreg r = c.nreg r)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) (ha : c.nreg ALLOC ≤ c'.nreg ALLOC) :
    TEnv P W O s c' := by
  zumcz
  exact ⟨h.good, h.hW, (hr _ by_omega by_omega).trans h.r11,
    (hr _ by_omega by_omega).trans h.r12, (hr _ by_omega by_omega).trans h.r16,
    (hr _ by_omega by_omega).trans h.r17, fun a ha' => (hm a by_omega).trans (h.mem a ha'),
    by omega, h.grade⟩
theorem nW (h : TEnv P W O s c) : P.n + 3 ≤ W := by have := h.hW; unfold hostWords at this; omega
end TEnv

/-! ## The steps -/
section steps
variable {P : Polygon} {W : ℕ} {O : OracleIface} {s : TSt}

/-- **The parity of `q_l`.** -/
theorem parL_exec (c : Config) (hw : WordsBounded W c) (hS : TEnv P W O s c)
    (hq : c.nreg 170050 ≤ P.n) :
    ∃ c' k, Exec P W IOrc.parL c c' k ∧ k = 4 ∧ c'.nreg 170058 = c.nreg 170050 % 2 ∧
      ztbkx ∧ c'.nmem = c.nmem := by
  zuwj

  have hm : ztbxb := by
    zucjm
  zucg

  unfold IOrc.parL
  exec_block
  · zqbba
  zqbbd
  · config_simp; rw [hS.r17, hm]; omega
  simp_all

/-- **The parity of `q_r`.** -/
theorem parR_exec (c : Config) (hw : WordsBounded W c) (hS : TEnv P W O s c)
    (hq : c.nreg 170051 ≤ P.n) :
    ∃ c' k, Exec P W IOrc.parR c c' k ∧ k = 4 ∧ c'.nreg 170058 = c.nreg 170051 % 2 ∧
      ztbkx ∧ c'.nmem = c.nmem := by
  zuwj

  have hm : ztbxc := by
    zucjm
  unfold IOrc.parR
  exec_block
  · zqbba
  zqbbd
  · config_simp; rw [hS.r17, hm]; omega
  simp_all

/-- **The left candidate**: the end vertex `lo + 1` of an edge (`g = 0`), else the top of the
block `(g, q_l)` from the grade table. -/
theorem candL_exec (c : Config) (hw : WordsBounded W c) (hS : TEnv P W O s c)
    (hblk : 1 ≤ c.nreg 170052 → c.nreg 170052 < s.m₀ s.h ∧
      zteeo * 2 ^ c.nreg 170052 ≤ P.n - 1)
    (hlo : c.nreg 170054 + 2 ^ c.nreg 170052 ≤ P.n) :
    ∃ c' k, Exec P W IOrc.candL c c' k ∧ k ≤ 12 ∧
      c'.nreg 170059 = (if c.nreg 170052 = 0 then c.nreg 170054 + 1 else
        c.nreg 170054 + IOrc.blkT s.m₀ s.h ztmfu ztvhr) ∧
      ztbky ∧ c'.nmem = c.nmem := by
  zqbav
  unfold IOrc.candL
  zucfm
  · zqbbb
    · config_simp; rw [hS.r11]; grind
    refine ztdxc
    · config_simp; rw [ite_eq_left hg0, hS.r11]
    simp_all
  · zqbas
    have m1 : ztiza :=
      hS.mem _ ar
    have m2 : c.nmem _ =
        IOrc.blkD s.m₀ s.h _ _ := hS.mem _ ae
    have m3 : c.nmem _ =
        IOrc.blkT s.m₀ s.h _ _ := hS.mem _ ad
    zudpa
    have m2' : c.nmem (s.m₀ ztdpl + c.nreg 170050 + c.nreg 170050 +
        c.nreg 170050) = IOrc.blkD s.m₀ s.h (c.nreg 170052) (c.nreg 170050) := by
      grind
    have hTb' : ztgal := hTb
    zqbap
    · zqbbe
    simp_all

/-- **The right candidate**: the start vertex `hi` of an edge (`g = 0`), else the top of the
block `(g, q_r)` (after the decrement). -/
theorem candR_exec (c : Config) (hw : WordsBounded W c) (hS : TEnv P W O s c)
    (hblk : 1 ≤ c.nreg 170052 → c.nreg 170052 < s.m₀ s.h ∧
      ztrlr * 2 ^ c.nreg 170052 ≤ P.n - 1)
    (hhi : c.nreg 170055 + 2 ^ c.nreg 170052 ≤ P.n) :
    ∃ c' k, Exec P W IOrc.candR c c' k ∧ k ≤ 12 ∧
      c'.nreg 170059 = (if c.nreg 170052 = 0 then c.nreg 170055 else
        c.nreg 170055 + IOrc.blkT s.m₀ s.h ztmfu ztvhs) ∧
      ztbky ∧ c'.nmem = c.nmem := by
  zqbav
  unfold IOrc.candR
  zucfm
  · zqbbb
    simp_all
  · zqbas
    have m1 : ztiza :=
      hS.mem _ ar
    have m2 : c.nmem _ =
        IOrc.blkD s.m₀ s.h _ _ := hS.mem _ ae
    have m3 : c.nmem _ =
        IOrc.blkT s.m₀ s.h _ _ := hS.mem _ ad
    zudpa
    have m2' : c.nmem (s.m₀ ztdpl + c.nreg 170051 + c.nreg 170051 +
        c.nreg 170051) = IOrc.blkD s.m₀ s.h (c.nreg 170052) (c.nreg 170051) := by
      grind
    have hTb' : ztgal := hTb
    zqbap
    · zqbbe
    simp_all

/-- **The running maximum.** -/
theorem cmpUpd_exec (c : Config) (hw : WordsBounded W c) (hS : TEnv P W O s c)
    (hv : c.nreg 170046 < P.n) (hc : c.nreg 170059 < P.n) :
    ∃ c' k, Exec P W IOrc.cmpUpd c c' k ∧ k ≤ 250 ∧
      c'.nreg 170046 = (if IOrc.Y P ztyh < IOrc.Y P zthum then c.nreg 170059
        else c.nreg 170046) ∧
      (∀ r, r ≠ 170046 → zteuz → ztcu →
        c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem := by
  zucwc
  obtain ⟨c₁, k₁, e₁, hk₁, h60, h61, h63, h64, r₁, m₁⟩ : ∃ c₁ k₁, Exec P W
      ztcqs
      c c₁ k₁ ∧ k₁ = 4 ∧ c₁.nreg 170060 = 0 ∧ c₁.nreg 170061 = c.nreg 170046 ∧
      c₁.nreg 170063 = 0 ∧ c₁.nreg 170064 = c.nreg 170059 ∧
      ztegq ∧
      c₁.nmem = c.nmem := by
    exec_block
    all_goals first | omega | skip
    simp_all
  zufhs

  obtain ⟨c₂, k₂, e₂, hk₂, F₂, b₂, t₂⟩ := SweepPrim.kbit_exec (P := P) hS.good hW c₁ e₁.wb_right
    (a := 170060) (b := 170063) (d := 170060) (op := 1) (dst := 170066) by_norm_num
    by_norm_num by_norm_num by_norm_num by_norm_num (sa := .vtx ztyh)
    (sb := .vtx zthum) (sd := .vtx ztyh) hv hc hv s1 s2 s1
  zubzp
  have k2 : zthpf := fun r h1 h2 =>
    F₂.1 r (by simp only [SweepPrim.Bkb, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not,
      beq_eq_false_iff_ne]; omega)
  zue
  have hfr : ∀ r, r ≠ 170046 → zteuz → ztcu →
      c₂.nreg r = c.nreg r := fun r h1 h2 h3 => by
    rw [F₂.1 r (by simp only [SweepPrim.Bkb, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not,
      beq_eq_false_iff_ne]; omega), r₁ r by_omega by_omega by_omega
      by_omega]
  zudgy
  have c59 : ztsgy := by
    simp_all
  have c46 : ztsgx := by
    simp_all
  zuhsv
  · have hy : IOrc.Y P _ < IOrc.Y P _ := t₂.1 by_omega
    have e₃ := IOrc.exec_copyN_upd (P := P) w₂ 170046 170059
    refine ztdqh
    · zumb
    · zugzr
    · show c₂.nmem = c.nmem; zuoji
  · have hy : ¬ IOrc.Y P ztyh < IOrc.Y P zthum := by_grind
    refine ⟨_, _, .seq e₁ ztyof, by_omega, ?_,
      by omega, ?_⟩
    · grind
    · zukpi

/-! ## The invariant of the cover -/

/-- **The invariant of the cover of `[x, y]`**: the grade registers, the covered ranges `[x, lo]`
and `[hi, y]` below the running maximum, which is a good vertex. -/
structure TopI (P : Polygon) (W : ℕ) (O : OracleIface) (s : TSt) (x y : ℕ) (G : ℕ → Prop)
    (c : Config) : Prop where
  env : TEnv P W O s c
  pw : c.nreg 170053 = 2 ^ c.nreg 170052
  lo : c.nreg 170054 = c.nreg 170050 * c.nreg 170053
  hi : c.nreg 170055 = c.nreg 170051 * c.nreg 170053
  xlo : x ≤ c.nreg 170054
  qq : c.nreg 170050 ≤ c.nreg 170051
  hiy : c.nreg 170055 ≤ y
  yn : y ≤ P.n - 1
  cap : y - x ≤ 2 ^ ztbwe
  vbG : G ztyh
  vbn : c.nreg 170046 < P.n
  cov : ∀ v, ztmpj ∨ ztmfv →
    IOrc.Y P v ≤ IOrc.Y P ztyh
  good : ∀ v, x ≤ v → v ≤ y → G v
variable {x y : ℕ} {G : ℕ → Prop}
theorem TopI.keep {c c' : Config} (hI : TopI P W O s x y G c)
    (hk : ∀ r, ztekm ∨ ztnev → c'.nreg r = c.nreg r)
    (hm : c'.nmem = c.nmem) (hA : c'.nreg ALLOC = c.nreg ALLOC) : TopI P W O s x y G c' := by
  zulo

  refine ⟨hI.env.keep by_simp_all by_simp_all
    ztchd, ?_, ?_, ?_, ?_, ?_, ?_, hI.yn, hI.cap, ?_, ?_, ?_, hI.good⟩
  zudco
  · exact hI.pw
  · exact hI.lo
  · exact hI.hi
  · exact hI.xlo
  · exact hI.qq
  · exact hI.hiy
  · zulyo
  · zulyp
  · zulym

/-- **The left block of a grade.** -/
theorem stepL_exec (c : Config) (hw : WordsBounded W c)
    (hI : TopI P W O s x y G c) (hpar : c.nreg 170058 = c.nreg 170050 % 2)
    (hlt : c.nreg 170050 < c.nreg 170051) :
    ∃ c' k, Exec P W IOrc.stepL c c' k ∧ k ≤ 280 ∧ TopI P W O s x y G c' ∧
      c'.nreg 170050 = c.nreg 170050 + c.nreg 170050 % 2 ∧ c'.nreg 170051 = c.nreg 170051 ∧
      c'.nreg 170052 = c.nreg 170052 ∧
      ztwjo ∧
      IOrc.Y P ztyh ≤ IOrc.Y P ztbso ∧ c'.nmem = c.nmem := by
  zqbaw
  have hprod : ztxzx := by
    grind
  have hloHi : ztfdo := by
    zubva
    have : ztbfq :=
      Nat.mul_le_mul_right _ by_omega
    simp_all
  zqbay
  have hqlo : ztguf := by
    zugeb
  have hblk : 1 ≤ c.nreg 170052 → c.nreg 170052 < s.m₀ s.h ∧
      zteeo * 2 ^ c.nreg 170052 ≤ P.n - 1 := fun hg1 =>
    ⟨IOrc.pow_le_of_cap hg1 by_omega hI.cap, by_omega⟩
  unfold IOrc.stepL
  zucfo
  · zubed

    -- the candidate

    have hcand : ztcpe := by
      zqbbc
      · omega
      · zubxp
        zqbax
    -- every vertex of the block is below the candidate
    have hblkv : ∀ v, c.nreg 170054 < v → v ≤ c.nreg 170054 + c.nreg 170053 →
        IOrc.Y P v ≤ IOrc.Y P ztmia := by
      zugoo
      zqbbc
      · grind
      · zubxp
        have hT := (IOrc.block_top hS.grade hgΛ hb).2.2.2.2.2 ztibo by_omega
        zucam

    have S₁ := hS.keep ztdda
      by_grind ztbvs
    zukiv
    obtain ⟨c₂, k₂, e₂, hk₂, v46', r₂, m₂⟩ := cmpUpd_exec c₁ e₁.wb_right S₁
      ztdyy hcand.1
    have k2 : ∀ r, ztmt → ztcu →
        c₂.nreg r = c.nreg r := fun r h1 h2 => by
      zuemp
    have k2' : zthpj := fun r h1 h2 => by
      zqbau
    have S₂ := S₁.keep (fun r h1 h2 => by
        zunyj) by_grind (by
        zunbx)
    zue
    zqbaz
    zudkt

    zucg

    exec_block
    · config_simp; rw [k2' _ by_norm_num by_norm_num, S₂.r11]; omega
    · config_simp; rw [k2' _ by_norm_num by_norm_num, k2' _ by_norm_num by_norm_num]
      omega
    refine ⟨by_omega, ⟨S₂.keep (fun r h1 h2 => by
          zumyp; zvmyn)
        by_grind by_rfl, ?_, ?_, ?_, ?_, ?_, ?_, hI.yn, hI.cap, ?_, ?_, ?_,
        hI.good⟩, ?_, ?_, ?_, fun r h1 h2 => ?_, ?_, m₂.trans m₁⟩
    all_goals config_simp
    zujru
    zqbaq
    · omega
    · grind
    · omega
    · omega
    · omega
    · omega
    · zubbj
      · zueox
      · zudas
    · zubbj
      · omega
      · zudat
    · zuml
      zucuu
      · zucfs
      zucuv
      · zucfs
      · zubvu
    · omega
    · zucui
    grind
  · zucbw

/-- **The right block of a grade.** -/
theorem stepR_exec (c : Config) (hw : WordsBounded W c)
    (hI : TopI P W O s x y G c) (hpar : c.nreg 170058 = c.nreg 170051 % 2)
    (hlt : c.nreg 170051 % 2 = 1 → c.nreg 170050 < c.nreg 170051) :
    ∃ c' k, Exec P W IOrc.stepR c c' k ∧ k ≤ 280 ∧ TopI P W O s x y G c' ∧
      c'.nreg 170051 = c.nreg 170051 - c.nreg 170051 % 2 ∧ c'.nreg 170050 = c.nreg 170050 ∧
      c'.nreg 170052 = c.nreg 170052 ∧
      ztwjo ∧
      IOrc.Y P ztyh ≤ IOrc.Y P ztbso ∧ c'.nmem = c.nmem := by
  zqbaw
  zqbay
  unfold IOrc.stepR
  zucfo
  · zuecb

    have hprod : c.nreg 170051 * c.nreg 170053 = ztrls * c.nreg 170053 +
        c.nreg 170053 := by
      zukpv
      have : ztoqo :=
        Nat.le_mul_of_pos_left _ by_omega
      omega
    have hloHi : ztfdo := by
      zubva
      have : ztbfq :=
        Nat.mul_le_mul_right _ by_omega
      grind
    refine spec_seq ?_
    exec_block
    -- the configuration after the decrement
    set c₀ : Config := IOrc.decCfg c with hc₀
    zuibl
    have k0 : zthpn := fun r a b => by
      zunad; simp [IOrc.decCfg, upd, a, b]
    have c51 : ztpmp := by zunad; simp only [IOrc.decCfg]; config_simp; zvnem
    zujwv
    have S₀ : TEnv P W O s c₀ := hS.keep by_grind
      ztcve by_rfl
    have hblk : 1 ≤ c₀.nreg 170052 → c₀.nreg 170052 < s.m₀ s.h ∧
        ztrny * 2 ^ c₀.nreg 170052 ≤ P.n - 1 := fun hg1 => by
      zugvx
      refine ⟨IOrc.pow_le_of_cap hg1 by_omega hI.cap, ?_⟩
      grind
    obtain ⟨c₁, k₁, e₁, hk₁, v59, r₁, m₁⟩ := candR_exec c₀ w₀ S₀ hblk (by
      grind)
    zuexa
    have hcand : ztcpe := by
      zqbbc
      · omega
      · zqbat
        zqbax
    have hblkv : ∀ v, c.nreg 170055 - c.nreg 170053 ≤ v → v < c.nreg 170055 →
        IOrc.Y P v ≤ IOrc.Y P ztmia := by
      zugoo
      zqbbc
      · zudcs

      · zqbat
        have hT := (IOrc.block_top hS.grade hgΛ hb).2.2.2.2.2 ztdpu
          by_omega
        have e1 : ztgtk := by
          zuhnx
        rw [e1, show c.nreg 170055 - c.nreg 170053 + ztdpu = v by
          omega] at hT
        exact hT
    have S₁ := S₀.keep ztdda
      by_grind ztbvs
    have v46 : ztizj := by
      grind
    obtain ⟨c₂, k₂, e₂, hk₂, v46', r₂, m₂⟩ := cmpUpd_exec c₁ e₁.wb_right S₁
      ztdyy hcand.1
    zqbaz
    zudvp

    have k2' : zthpk := fun r h1 h2 => by
      zqbau
    refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by_omega, ⟨S₁.keep (fun r h1 h2 =>
        r₂ r by_omega by_omega by_omega) by_grind (by
        zunbx), ?_, ?_, ?_, ?_, ?_, ?_, hI.yn, hI.cap, ?_,
        ?_, ?_, hI.good⟩, ?_, ?_, ?_, fun r h1 h2 => ?_, ?_, m₂.trans m₁⟩
    zqbaq
    zupk

    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · zubbj
      · zueox
      · zudas
    · zubbj
      · omega
      · zudat
    · zuml
      zucuu
      · zucft
      zucuv
      · zucft
      · zubvu
    · omega
    · rw [r₂ r by_omega by_omega h2, r₁ r by_omega by_omega by_omega,
        k0 r by_omega by_omega]
    grind
  · zucbx

/-- **The next grade**: IOrc.halve `q_l`, `q_r` (both even), double `2^g`. -/
theorem halve_exec (c : Config) (hw : WordsBounded W c)
    (hI : TopI P W O s x y G c) (hl : c.nreg 170050 % 2 = 0) (hr : c.nreg 170051 % 2 = 0)
    (hpn : c.nreg 170053 ≤ P.n) :
    ∃ c' k, Exec P W IOrc.halve c c' k ∧ k = 6 ∧ TopI P W O s x y G c' ∧
      c'.nreg 170050 = c.nreg 170050 / 2 ∧ c'.nreg 170051 = c.nreg 170051 / 2 ∧
      ztybv ∧
      c'.nreg 170046 = c.nreg 170046 ∧ c'.nmem = c.nmem := by
  zuheo

  zqbar
  zqbay
  zudpb

  have h50 : ztbxb := by
    zuelt
  have h51 : ztbxc := by
    zuelu
  zueqy
  zqbav
  zufey

  unfold IOrc.halve
  exec_block
  all_goals first
    | (config_simp; zunse; omega)
    | (config_simp; zuojj; omega)
    | (config_simp; zvnem; omega)
    | (config_simp; omega)
    | skip
  refine ⟨rfl, ⟨hS.keep (fun r h1 h2 => by
      zumyp; grind) by_simp_all
      by_rfl, ?_, ?_, ?_, ?_, ?_, ?_, hI.yn, hI.cap, ?_, ?_, ?_, hI.good⟩,
    ?_, ?_, fun r h1 => ?_, ?_, rfl⟩
  all_goals config_simp
  all_goals try rw [hS.r17]
  all_goals try rw [h50]
  all_goals try rw [h51]
  all_goals try rw [hS.r11]
  · omega
  · zuemc

    zubpz
  · zuelw

    zubpz
  · omega
  · omega
  · omega
  · zulyo
  · zulyp
  · zulym
  · zubd

/-- **One grade of the cover.** -/
theorem topBody_exec (c : Config) (hw : WordsBounded W c)
    (hI : TopI P W O s x y G c) (hlt : c.nreg 170050 < c.nreg 170051) :
    ∃ c' k, Exec P W IOrc.topBody c c' k ∧ k ≤ 600 ∧ TopI P W O s x y G c' ∧
      2 * ztqgx ≤ c.nreg 170051 - c.nreg 170050 ∧
      ztwjo ∧
      IOrc.Y P ztyh ≤ IOrc.Y P ztbso ∧ c'.nmem = c.nmem := by
  have hS := hI.env
  zqbar
  have hpn : ztunt := by
    have : ztbfq :=
      by simp_all
    zuelc
    have := hI.hiy; have := hI.yn; omega
  -- `q_l`
  zubdx
  have I₁ := hI.keep by_grind
    m₁ ztqvr
  zuffg

  obtain ⟨c₂, k₂, e₂, hk₂, I₂, q50, q51, q52, r₂, y₂, m₂⟩ := stepL_exec c₁ e₁.wb_right I₁
    by_omega by_omega
  -- `q_r`
  obtain ⟨c₃, k₃, e₃, hk₃, p₃, r₃, m₃⟩ := parR_exec c₂ e₂.wb_right I₂.env
    (by have := I₂.hiy; have := I₂.yn; have := I₂.hi; have := I₂.pw
        grind)
  have I₃ := I₂.keep ztlot
    m₃ ztqvs
  zuffn

  obtain ⟨c₄, k₄, e₄, hk₄, I₄, s51, s50, s52, r₄, y₄, m₄⟩ := stepR_exec c₃ e₃.wb_right I₃
    by_omega (by
      omega)
  have hpn4 : ztuss := by
    have g3 : ztshn := by
      zudvh
    zuewr
  obtain ⟨c₅, k₅, e₅, hk₅, I₅, t50, t51, r₅, y₅, m₅⟩ := halve_exec c₄ e₄.wb_right I₄
    by_omega
    by_omega
    hpn4
  zuctv

  refine ⟨c₅, _, .seq e₁ ztbq, by_omega, I₅, ?_, fun r h1 h2 => ?_,
    by grind, by_grind⟩
  · zuccf
  · rw [r₅ r h1, r₄ r h1 h2, r₃ r by_omega by_omega by_omega, r₂ r h1 h2,
      r₁ r by_omega by_omega by_omega]

/-- **The cover of `[x, y]`.**  From `q_l = x ≤ y = q_r` (`y ≤ n - 1`, `y - x` within the cap)
and a running maximum `170046` at least as high as both ends, `IOrc.topLoop` ends with a running
maximum at least as high as every vertex of `[x, y]`, within `602 size (y - x) + 6` steps. -/
theorem topLoop_exec (c : Config) (hw : WordsBounded W c)
    (hS : TEnv P W O s c) (hx : c.nreg 170050 = x) (hy : c.nreg 170051 = y) (hxy : x ≤ y)
    (hyn : y ≤ P.n - 1) (hcap : y - x ≤ 2 ^ ztbwe) (hvG : G ztyh)
    (hvn : c.nreg 170046 < P.n) (hvx : IOrc.Y P x ≤ IOrc.Y P ztyh)
    (hvy : IOrc.Y P y ≤ IOrc.Y P ztyh) (hgood : ∀ v, x ≤ v → v ≤ y → G v) :
    ∃ c' k, Exec P W IOrc.topLoop c c' k ∧ k ≤ 602 * Nat.log 2 zteks + 6 ∧ TEnv P W O s c' ∧
      G ztbso ∧ c'.nreg 170046 < P.n ∧
      (∀ v, x ≤ v → v ≤ y → IOrc.Y P v ≤ IOrc.Y P ztbso) ∧
      ztwjo ∧
      IOrc.Y P ztyh ≤ IOrc.Y P ztbso ∧ c'.nmem = c.nmem := by
  obtain ⟨c₀, k₀, e₀, hk₀, I₀, h50, h51, h46, r₀, m₀⟩ : ∃ c₀ k₀, Exec P W
      ztcqr
      c c₀ k₀ ∧ k₀ = 4 ∧ TopI P W O s x y G c₀ ∧ c₀.nreg 170050 = x ∧ c₀.nreg 170051 = y ∧
      c₀.nreg 170046 = c.nreg 170046 ∧
      ztybw ∧ c₀.nmem = c.nmem := by
    zumee
    exec_block
    all_goals first | omega | skip
    refine ⟨rfl, ⟨hS.keep (fun r h1 h2 => by
        zumyp; grind) by_simp_all
        by_rfl, ?_, ?_, ?_, ?_, ?_, ?_, hyn, hcap, ?_, ?_, ?_, hgood⟩,
      ?_, ?_, ?_, fun r h1 => ?_, rfl⟩
    all_goals config_simp
    all_goals try rw [hx]
    all_goals try rw [hy]
    all_goals try (first | exact hvG | exact hvn | omega | simp; done)
    · grind
    · zubd
  let I : Config → Prop := fun c' => TopI P W O s x y G c' ∧ WordsBounded W c' ∧
    ztwjo ∧
    IOrc.Y P ztyh ≤ IOrc.Y P ztbso ∧ c'.nmem = c.nmem
  obtain ⟨c', k, e, ⟨I', w', f', y', m'⟩, hex, hk⟩ := Exec.whileLtN_potential (P := P) (W := W)
    (a := 170050) (b := 170051) (body := IOrc.topBody) I
    ztfye ztqng
    (fun c₁ ⟨I₁, w₁, f₁, y₁, m₁⟩ hlt => by
      zubty
      refine ⟨c₂, k₂, e₂, ⟨I₂, e₂.wb_right, by_simp_all,
        y₁.trans y₂, m₂.trans m₁⟩, ?_⟩
      have := IOrc.log_half_lt hd by_omega
      grind)
    (c := c₀) ztfjt
  zubcc
end steps
end
end DrvP
end Chazelle.Core
end
section
set_option hygiene false
local macro "zqyj" : tactic => `(tactic| (obtain ⟨c', k₂, e₂, hk₂, hI', hrf₂, hc'⟩ := RS.copy (P := P) hI₁ (r := d) (a := 50210) hd
                                          refine ⟨c', k₁ + k₂, .seq e₁ e₂, by_omega, hI', hrf₁.trans hrf₂, ?_, ?_⟩))
local macro "zqyk" : tactic => `(tactic| rw [a₂ _ by_norm_num by_norm_num by_simp, a₁ _ by_norm_num by_norm_num by_simp])
local macro "zqyl" : tactic => `(tactic| refine RS.ifT by_omega (RS.ifF by_omega (leaf_set hI hs by_norm_num ?_)))
local macro "zqyn" : tactic => `(tactic| (have hW1 : ztbla := by have := hI.hw.1 83023; rw [hI.h23] at this; omega))
local macro "zqyo" : tactic => `(tactic| refine RS.ifF by_omega ztclu)
local macro "zqyp" : tactic => `(tactic| (rw [g 83031 by_norm_num by_norm_num by_simp]; exact hL))
set_option hygiene true

/-!
# WP-E, the candidate test on the RAM, part 10: the arc scan

The first half of the validity check scans the arcs of the region `r` (register `83002`): for
each arc it reads the two ends, compares their keys with the key of the candidate `x`, and
accumulates three flags: `83042` (the key of `x` is strictly inside the arc), `83043` (an arc
begins at `x`), `83044` (an arc ends at `x`).

Scratch registers: `83030` the place in the arc list, `83031` its length, `83032` the arc, `83033
… 83036` its ends, `83037 … 83041` the comparison bits (`s < x`, `x < s`, `x < e`, `e < x`,
`s < e`).

* `Agr c c' S`: the registers of band `bRestore` outside `S` agree.
* `arcRead_rs`: reading the ends of the `t`-th arc.
-/
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim

/-- The registers of band `bRestore` outside `S` agree. -/
def Agr (c c' : Config) (S : List ℕ) : Prop :=
  ∀ q, 80000 ≤ q → q < 90000 → q ∉ S → c'.nreg q = c.nreg q
theorem Agr.refl (c : Config) (S : List ℕ) : Agr c c S := fun _ _ _ _ => rfl
theorem Agr.trans {c c₁ c₂ : Config} {S₁ S₂ : List ℕ} (h₁ : Agr c c₁ S₁) (h₂ : Agr c₁ c₂ S₂) :
    Agr c c₂ (S₁ ++ S₂) := fun q h1 h2 hq => by
  simp only [List.mem_append, not_or] at hq
  rw [h₂ q h1 h2 hq.2, h₁ q h1 h2 hq.1]
theorem Agr.mono {c c' : Config} {S S' : List ℕ} (h : Agr c c' S) (hS : ∀ q ∈ S, q ∈ S') :
    Agr c c' S' := fun q h1 h2 hq => h q h1 h2 by_grind
theorem Agr.of_upd {c c' : Config} {r v : ℕ} (h : c'.nreg = upd c.nreg r v) : Agr c c' [r] :=
  fun q _ _ hq => by
    simp_all
theorem Agr.of_band {c c' : Config} (h : ∀ q, 80000 ≤ q → q < 90000 → c'.nreg q = c.nreg q)
    (S : List ℕ) : Agr c c' S := fun q h1 h2 _ => by_simp_all
variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ c : Config}

/-- The arc at place `t` of the region. -/
def arcAt (N : NF) (r t : ℕ) : ℕ := (N.region r).arcs.getD t 0

/-- A field read of the arc in `83032` and a copy into `d`. -/
def arcF (f d : ℕ) : Stmt := .seq (tArcF f 83032) ztovx

/-- **Reading the ends of the arc at place `83030`.** -/
def arcRead : Stmt :=
  .seq (tRegItem 1 83030) (.seq ztigl
    (.seq (arcF 1 83033) (.seq (arcF 2 83034) (.seq (arcF 3 83035) (arcF 4 83036)))))
variable {f d : ℕ} {kc : ℕ → ℕ → ℕ → ℕ → Stmt} {Kk : ℕ} {r K : ℕ} {cond : Prop}
/-- A field read of the arc in `83032` followed by a copy into a scratch register. -/
theorem arcF_rs (hf : f < 5) (hd : Scr d) (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
    (hj : c.nreg 83032 < N.arcs.length) (hroom : c.nreg ALLOC + 11 ≤ W) :
    RS P W c₀ (arcF f d) c 14
      (fun c' => c'.nreg d = arFld (N.arc ztvja) f ∧ Agr c c' [d]) := by
  obtain ⟨c₁, k₁, e₁, hk₁, v₁, hI₁, hrf₁, h8₁⟩ :=
    tArcF_exec hf ztmnu hE hI hj hroom
  zqyj
  · simp_all
  · zuhck

/-- The arc at place `t` of the region is an arc record. -/
theorem arcAt_lt (hE : TGood P W M N c₀) {t : ℕ}
    (ht : t < (N.region ztco).arcs.length) :
    arcAt N ztco t < N.arcs.length ∧
      arcAt N ztco t ∈ (N.region ztco).arcs := by
  zugnb
  obtain ⟨-, -, -, reg, -, -, harcs, -⟩ := hE.hNF
  have hmem : arcAt N ztco t ∈ (N.region ztco).arcs := by
    zulub

  exact ⟨((harcs.2.2.2 _ hr _).1 hmem).1, hmem⟩

/-- **The ends of the arc at place `t`.** -/
theorem arcRead_rs (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
    (ht : c.nreg 83030 < (N.region ztco).arcs.length)
    (hroom : c.nreg ALLOC + 80 ≤ W) :
    RS P W c₀ arcRead c 80 (fun c' =>
      c'.nreg 83033 = (N.arc ztxnf).s.edge ∧
      c'.nreg 83034 = (N.arc ztxnf).s.hgt ∧
      c'.nreg 83035 = (N.arc ztxnf).e.edge ∧
      c'.nreg 83036 = (N.arc ztxnf).e.hgt ∧
      Agr c c' [83032, 83033, 83034, 83035, 83036]) := by
  have hjl := (arcAt_lt hE ht).1
  set j := arcAt N _ _ with hjdef
  have h1 := tRegItem_exec (tr := 83030) ztp by_trivial hE hI
    by_simp_all by_omega
  rw [ite_eq_left rfl] at h1
  refine RS.mono (K := 20 + (1 + (14 + (14 + ztsrc)))) ?_ by_norm_num ztb
  refine RS.seq ztqck fun c₁ hI₁ hA₁ ⟨v₁, h8₁⟩ =>
    RS.seq (RS.copy hI₁ (r := 83032) (a := 50210) by_trivial)
    fun c₂ hI₂ hA₂ hc₂ => ?_
  have q2 : c₂.nreg 83032 = j := by zunie; rfl
  zuclq
  refine RS.seq (arcF_rs (f := 1) (d := 83033) by_norm_num by_trivial hE hI₂
    by_omega by_omega) fun c₃ hI₃ hA₃ ⟨v₃, a₃⟩ => ?_
  have q3 : c₃.nreg 83032 = j := by zunea
  refine RS.seq (arcF_rs (f := 2) (d := 83034) by_norm_num by_trivial hE hI₃
    by_omega by_omega) fun c₄ hI₄ hA₄ ⟨v₄, a₄⟩ => ?_
  have q4 : c₄.nreg 83032 = j := by rw [a₄ _ by_norm_num by_norm_num by_simp, q3]
  refine RS.seq (arcF_rs (f := 3) (d := 83035) by_norm_num by_trivial hE hI₄
    by_omega by_omega) fun c₅ hI₅ hA₅ ⟨v₅, a₅⟩ => ?_
  have q5 : c₅.nreg 83032 = j := by zuntn
  refine (arcF_rs (f := 4) (d := 83036) by_norm_num by_trivial hE hI₅
    by_omega by_omega).mono le_rfl fun c₆ ⟨v₆, a₆⟩ => ?_
  have a26 := (((a2.trans a₃).trans a₄).trans a₅).trans a₆
  refine ⟨?_, ?_, ?_, ?_, by_simp_all⟩
  · rw [a₆ _ by_norm_num by_norm_num by_simp, a₅ _ by_norm_num by_norm_num by_simp,
      a₄ _ by_norm_num by_norm_num by_simp, v₃, q2]; rfl
  · rw [a₆ _ by_norm_num by_norm_num by_simp, a₅ _ by_norm_num by_norm_num by_simp,
      v₄, q3]; rfl
  · zuelg
  · zuine

/-! ## Comparisons -/

/-- Copy the two comparison bits into `u`, `v`. -/
def cp2 (u v : ℕ) : Stmt := .seq (.instr (.copyN u 50210)) (.instr (.copyN v 50211))
theorem cp2_rs {u v : ℕ} (hu : Scr u) (hv : Scr v) (huv : u ≠ v) (hI : TInv W c₀ c) :
    RS P W c₀ zttik c 2 (fun c' => c'.nreg u = c.nreg 50210 ∧ c'.nreg v = c.nreg 50211 ∧
      Agr c c' [u, v]) := by
  unfold Scr at hu hv
  refine RS.seq (RS.copy hI (r := u) (a := 50210) hu) fun c₁ hI₁ _ h₁ =>
    (RS.copy hI₁ (r := v) (a := 50211) hv).mono le_rfl fun c₂ h₂ => ztcg
  · simp_all
  · rw [h₂, upd_eq, h₁, upd_ne by_omega]
  · exact ((Agr.of_upd h₁).trans ztpvt).mono by_simp

/-- **A key comparison with its bits saved** in `u`, `v`. -/
theorem kcmp_rs (hK : KeyOK kc Kk) {a b d e u v : ℕ}
    (ha : InR a) (hb : InR b) (hd : InR d) (he : InR e) (hu : Scr u) (hv : Scr v) (huv : u ≠ v)
    (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
    (hx : PosG M zta P.n ztel) (hy : PosG M zta P.n ztge)
    (hroom : c.nreg ALLOC + Kk ≤ W) :
    RS P W c₀ (.seq ztjzj zttik) c ztblz (fun c' =>
      BitIs c' u ztxkf ∧
      BitIs c' v ztypi ∧
      Agr c c' [u, v]) := by
  obtain ⟨c₁, k₁, e₁, hk₁, b1, b2, hst⟩ := hK a b d e ha hb hd he P W M N c₀ c hE hI hx hy hroom
  refine RS.seq (RS.op (Q := fun c₁ => BitIs c₁ 50210 _ ∧ BitIs c₁ 50211 _)
    by_grind)
    fun c₁ hI₁ _ ⟨⟨b1, b2⟩, h8⟩ => (cp2_rs hu hv huv hI₁).mono le_rfl fun c₂ ⟨q1, q2, a2⟩ =>
      ⟨b1.of_eq q1, b2.of_eq q2, ((Agr.of_band h8 []).trans a2).mono by_simp⟩

/-- **The three comparisons of an arc** with the candidate. -/
def cmpArc (kc : ℕ → ℕ → ℕ → ℕ → Stmt) : Stmt :=
  .seq (.seq (kc 83033 83034 83005 83006) zttij)
    (.seq (.seq (kc 83005 83006 83035 83036) (cp2 83039 83040))
      (.seq (kc 83033 83034 83035 83036) (cp2 83041 83051)))

/-- The key of the position held in the registers `a`, `b`. -/
noncomputable def keyAt (M : Model) (P : Polygon) (c : Config) (a b : ℕ) : ℝ :=
  M.key zta ztel
theorem cmpArc_rs (hK : KeyOK kc Kk)
    (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
    (hs : PosG M zta P.n ⟨c.nreg 83033, c.nreg 83034⟩)
    (he : PosG M zta P.n ⟨c.nreg 83035, c.nreg 83036⟩)
    (hroom : c.nreg ALLOC + 3 * ztblz ≤ W) :
    RS P W c₀ ztvlk c (3 * ztblz) (fun c' =>
      BitIs c' 83037 (keyAt M P c 83033 83034 < keyAt M P c₀ 83005 83006) ∧
      BitIs c' 83038 (keyAt M P c₀ 83005 83006 < keyAt M P c 83033 83034) ∧
      BitIs c' 83039 (keyAt M P c₀ 83005 83006 < keyAt M P c 83035 83036) ∧
      BitIs c' 83040 (keyAt M P c 83035 83036 < keyAt M P c₀ 83005 83006) ∧
      BitIs c' 83041 (keyAt M P c 83033 83034 < keyAt M P c 83035 83036) ∧
      Agr c c' [83037, 83038, 83039, 83040, 83041, 83051]) := by
  zucwv
  zuess
  have hx : ztyli := by
    zudkd
  have kx : keyAt M P c₀ 83005 83006 = keyAt M P c 83005 83006 := by
    unfold keyAt; simp_all
  rw [kx]
  unfold cmpArc
  refine RS.mono (K := ztblz + ztzys) ?_ by_omega ztb
  refine RS.seq (kcmp_rs hK by_trivial by_trivial by_trivial
    by_trivial by_trivial by_trivial by_omega hE hI hs hx
    by_omega) fun c₁ hI₁ hA₁ ⟨b37, b38, a₁⟩ => ?_
  have g : ∀ q, q ∈ [83033, 83034, 83035, 83036, 83005, 83006] → c₁.nreg q = c.nreg q := by
    zuco
    zughb
    exact a₁ q by_omega by_omega by_grind
  refine RS.seq (kcmp_rs hK by_trivial by_trivial by_trivial
    by_trivial by_trivial by_trivial by_omega hE hI₁
    by_simp_all
    by_simp_all by_omega)
    fun c₂ hI₂ hA₂ ⟨b39, b40, a₂⟩ => ?_
  have g2 : ∀ q, q ∈ [83033, 83034, 83035, 83036, 83005, 83006] → c₂.nreg q = c.nreg q := by
    zuco
    rw [← g q hq]
    zughb
    exact a₂ q by_omega by_omega by_grind
  refine (kcmp_rs hK by_trivial by_trivial by_trivial
    by_trivial by_trivial by_trivial by_omega hE hI₂
    by_simp_all
    by_simp_all by_omega).mono le_rfl
    fun c₃ ⟨b41, _, a₃⟩ => ?_
  unfold keyAt at *
  rw [g 83005 by_simp, g 83006 by_simp, g 83035 by_simp, g 83036 by_simp] at b39 b40
  rw [g2 83033 by_simp, g2 83034 by_simp, g2 83035 by_simp, g2 83036 by_simp] at b41
  have a12 := (a₁.trans a₂).trans a₃
  refine ⟨?_, ?_, ?_, ?_, b41, by_simp_all⟩
  · exact b37.of_eq (by rw [a₃ _ by_norm_num by_norm_num by_simp,
      a₂ _ by_norm_num by_norm_num by_simp])
  · exact b38.of_eq (by rw [a₃ _ by_norm_num by_norm_num by_simp,
      a₂ _ by_norm_num by_norm_num by_simp])
  · exact b39.of_eq ztlgs
  · exact b40.of_eq ztlgs

/-! ## Flags -/

/-- The effect of a conditional flag update: the flag `r` becomes `1` if `cond`, else stays. -/
def FlagUpd (c c' : Config) (r : ℕ) (cond : Prop) : Prop :=
  (c'.nreg r = 1 ↔ c.nreg r = 1 ∨ cond) ∧ (c.nreg r ≤ 1 → c'.nreg r ≤ 1) ∧ Agr c c' [r]

/-- Set a flag. -/
def setF (r : ℕ) : Stmt := .instr ztnaa
theorem leaf_set (hI : TInv W c₀ c) (hr : Scr r) (hK : 1 ≤ K)
    (hc : cond) : RS P W c₀ ztwdp c K ztmjk :=
  (RS.const hI hr (by have := hI.hw.1 83023; rw [hI.h23] at this; omega)).mono hK
    fun c' h => ⟨by_simp_all, by_simp_all, Agr.of_upd h⟩
theorem leaf_skip (hI : TInv W c₀ c) (hc : ¬ cond) :
    RS P W c₀ .skip c K ztmjk :=
  RS.skip hI ⟨by_simp_all, id, Agr.refl c _⟩

/-- **Update of the inside flag** `83042`: set if the candidate's key is strictly inside the arc
(`83041`: `s < e`, `83037`: `s < x`, `83039`: `x < e`). -/
def updIn : Stmt :=
  .ifLtN 83041 83023
    (.ifLtN 83037 83023 ztlzz (setF 83042))
    (.ifLtN 83037 83023 .skip ztlzz)
theorem updIn_rs {pse psx pxe : Prop} (hI : TInv W c₀ c) (h41 : BitIs c 83041 pse)
    (h37 : BitIs c 83037 psx) (h39 : BitIs c 83039 pxe) :
    RS P W c₀ updIn c 7 (fun c' => FlagUpd c c' 83042
      ((pse ∧ psx ∧ pxe) ∨ (¬ pse ∧ (psx ∨ pxe)))) := by
  zuglc
  have hs : Scr 83042 := by_trivial
  unfold updIn
  rcases bit01 h41 with ⟨q41, n41⟩ | ⟨q41, n41⟩ <;>
  rcases bit01 h37 with ⟨q37, n37⟩ | ⟨q37, n37⟩ <;>
  rcases bit01 h39 with ⟨q39, n39⟩ | ⟨q39, n39⟩
  · zuloe

  · refine RS.ifT by_omega (RS.ifT by_omega ztlfn)
    simp_all
  · zqyl
    simp_all
  · zqyl
    simp_all
  · zqyo
    simp_all
  · zqyo
    simp_all
  · zulod

  · refine RS.ifF by_omega (RS.ifF by_omega ztlfn)
    simp_all

/-- **Update of an equality flag** `f`: set if both bits `u` (`a < b`) and `v` (`b < a`) are
`0`. -/
def updEq (u v f : ℕ) : Stmt := .ifLtN u 83023 (.ifLtN v 83023 ztwdo .skip) .skip
theorem updEq_rs {u v f : ℕ} {a b : ℝ} (hf : Scr f) (hI : TInv W c₀ c) (hu : BitIs c u ztteo)
    (hv : BitIs c v (b < a)) :
    RS P W c₀ (updEq u v f) c 5 (fun c' => FlagUpd c c' f (a = b)) := by
  zuglc
  unfold updEq
  rcases bit01 hu with ⟨qu, nu⟩ | ⟨qu, nu⟩ <;>
  rcases bit01 hv with ⟨qv, nv⟩ | ⟨qv, nv⟩
  · exact RS.ifT by_omega (RS.ifT by_omega (leaf_set hI hf le_rfl
      by_grind))
  · exact RS.ifT by_omega (RS.ifF by_omega
      zttrz)
  · exact RS.ifF by_omega zttrz
  grind

/-! ## The arc loop -/

/-- The body of the arc loop. -/
def arcBody (kc : ℕ → ℕ → ℕ → ℕ → Stmt) : Stmt :=
  .seq arcRead (.seq ztvlk (.seq updIn (.seq (updEq 83037 83038 83043)
    (.seq (updEq 83039 83040 83044) ztejr))))

/-- The cost bound of the body of the arc loop. -/
def arcKB (Kk : ℕ) : ℕ := 80 + (3 * ztblz + (7 + (5 + ztngt)))

/-- The start key of the arc at place `t`. -/
noncomputable def ksAt (M : Model) (P : Polygon) (N : NF) (r t : ℕ) : ℝ :=
  M.key zta (N.arc ztfpa).s

/-- The end key of the arc at place `t`. -/
noncomputable def keAt (M : Model) (P : Polygon) (N : NF) (r t : ℕ) : ℝ :=
  M.key zta (N.arc ztfpa).e

/-- **The invariant of the arc loop** (started in `cS`). -/
def ArcI (M : Model) (P : Polygon) (N : NF) (c₀ cS c : Config) : Prop :=
  c.nreg 83031 = (N.region ztco).arcs.length ∧
    c.nreg 83030 ≤ c.nreg 83031 ∧
    c.nreg 83042 ≤ 1 ∧ c.nreg 83043 ≤ 1 ∧ c.nreg 83044 ≤ 1 ∧
    (c.nreg 83042 = 1 ↔ ∃ t < c.nreg 83030, Chazelle.Chain.sideInArc (ksAt M P N ztco t)
      (keAt M P N ztco t) ztwmu) ∧
    (c.nreg 83043 = 1 ↔ ∃ t < c.nreg 83030,
      ksAt M P N ztco t = M.key zta ztfy) ∧
    (c.nreg 83044 = 1 ↔ ∃ t < c.nreg 83030,
      M.key zta ztfy = keAt M P N ztco t) ∧
    Agr cS c [83030, 83032, 83033, 83034, 83035, 83036, 83037, 83038, 83039, 83040, 83041,
      83042, 83043, 83044, 83051]
theorem sideInArc_bits {a b x : ℝ} :
    ((a < b ∧ a < x ∧ x < b) ∨ ztyxr) ↔
      Chazelle.Chain.sideInArc a b x := by
  unfold Chazelle.Chain.sideInArc
  grind
theorem lt_succ_exists {p : ℕ → Prop} {t : ℕ} :
    (∃ t' < t + 1, p t') ↔ (∃ t' < t, p t') ∨ p t := by
  grind

/-- **One iteration of the arc loop.** -/
theorem arcBody_rs (hK : KeyOK kc Kk)
    (hE : TGood P W M N c₀) (hne : (N.F M zta).Nonempty) {cS : Config}
    (hI : TInv W c₀ c) (hA : ArcI M P N c₀ cS c) (ht : c.nreg 83030 < c.nreg 83031)
    (hroom : c.nreg ALLOC + arcKB Kk ≤ W) :
    RS P W c₀ ztvek c (arcKB Kk) (fun c' => ArcI M P N c₀ cS c' ∧
      c'.nreg 83030 = c.nreg 83030 + 1) := by
  obtain ⟨hL, htL, f1, f2, f3, i1, i2, i3, aS⟩ := hA
  zuhol
  set t := c.nreg 83030 with htdef
  have ht' : ztjaq := by_omega
  obtain ⟨hjl, -⟩ := arcAt_lt hE ht'
  have hpos := hE.arcPosG hne hjl
  unfold arcBody arcKB
  refine RS.seq (arcRead_rs hE hI ht' ztnvo)
    fun c₁ hI₁ hA₁ ⟨s1, s2, s3, s4, a₁⟩ => ?_
  have hs : PosG M zta P.n ⟨c₁.nreg 83033, c₁.nreg 83034⟩ := by_simp_all
  have he : PosG M zta P.n ⟨c₁.nreg 83035, c₁.nreg 83036⟩ := by_simp_all
  refine RS.seq (cmpArc_rs hK hE hI₁ hs he ztnvo)
    fun c₂ hI₂ hA₂ ⟨b37, b38, b39, b40, b41, a₂⟩ => ?_
  have ks : keyAt M P c₁ 83033 83034 = ksAt M P N r t := by
    unfold keyAt ksAt; zumzh
  have ke : keyAt M P c₁ 83035 83036 = keAt M P N r t := by
    unfold keyAt keAt; rw [s3, s4]
  have kx : keyAt M P c₀ 83005 83006 = M.key _ ztfy := rfl
  rw [ks, kx] at b37 b38
  rw [kx, ke] at b39 b40
  rw [ks, ke] at b41
  refine RS.seq (updIn_rs hI₂ b41 b37 b39) fun c₃ hI₃ hA₃ ⟨u1, u2, a₃⟩ => ?_
  have b37' := b37.of_eq (a₃ 83037 by_norm_num by_norm_num by_simp)
  have b38' := b38.of_eq (a₃ 83038 by_norm_num by_norm_num by_simp)
  refine RS.seq (updEq_rs by_trivial hI₃ b37' b38')
    fun c₄ hI₄ hA₄ ⟨v1, v2, a₄⟩ => ?_
  have b39' := (b39.of_eq (a₃ 83039 by_norm_num by_norm_num by_simp)).of_eq
    (a₄ 83039 by_norm_num by_norm_num by_simp)
  have b40' := (b40.of_eq (a₃ 83040 by_norm_num by_norm_num by_simp)).of_eq
    (a₄ 83040 by_norm_num by_norm_num by_simp)
  refine RS.seq (updEq_rs by_trivial hI₄ b39' b40')
    fun c₅ hI₅ hA₅ ⟨w1, w2, a₅⟩ => ?_
  have e30 : c₅.nreg 83030 = t := by
    rw [a₅ _ by_norm_num by_norm_num by_simp, a₄ _ by_norm_num by_norm_num by_simp,
      a₃ _ by_norm_num by_norm_num by_simp, a₂ _ by_norm_num by_norm_num by_simp,
      a₁ _ by_norm_num by_norm_num by_simp]
  have e23 := hI₅.h23
  refine (RS.add hI₅ by_trivial
    (by zuoni; have := hI.hw.1 83031; omega)).mono le_rfl fun c₆ h₆ => ?_
  have a₆ := Agr.of_upd h₆
  have e6 : c₆.nreg 83030 = t + 1 := by rw [h₆, upd_eq, e30, e23]
  -- the chain of agreements
  have a16 := ((((a₁.trans a₂).trans a₃).trans a₄).trans a₅).trans a₆
  have g : ∀ q, 80000 ≤ q → q < 90000 → q ∉ [83030, 83032, 83033, 83034, 83035, 83036, 83037,
      83038, 83039, 83040, 83041, 83042, 83043, 83044, 83051] → c₆.nreg q = c.nreg q :=
    fun q h1 h2 hq => a16 q h1 h2 (fun h => hq (by simp at h ⊢; omega))
  -- the flags at `c₆`
  have fl42 : c₆.nreg 83042 = c₃.nreg 83042 := by
    rw [h₆, upd_ne by_norm_num, a₅ _ by_norm_num by_norm_num by_simp,
      a₄ _ by_norm_num by_norm_num by_simp]
  have fl43 : c₆.nreg 83043 = c₄.nreg 83043 := by
    rw [h₆, upd_ne by_norm_num, a₅ _ by_norm_num by_norm_num by_simp]
  have fl44 : c₆.nreg 83044 = c₅.nreg 83044 := by rw [h₆, upd_ne by_norm_num]
  have o42 : c₂.nreg 83042 = c.nreg 83042 := by
    zqyk
  have o43 : c₃.nreg 83043 = c.nreg 83043 := by
    rw [a₃ _ by_norm_num by_norm_num by_simp, a₂ _ by_norm_num by_norm_num by_simp,
      a₁ _ by_norm_num by_norm_num by_simp]
  have o44 : c₄.nreg 83044 = c.nreg 83044 := by
    rw [a₄ _ by_norm_num by_norm_num by_simp, a₃ _ by_norm_num by_norm_num by_simp,
      a₂ _ by_norm_num by_norm_num by_simp, a₁ _ by_norm_num by_norm_num by_simp]
  refine ⟨ztbfh, e6⟩
  · zqyp
  · rw [e6, g 83031 by_norm_num by_norm_num by_simp]; omega
  · omega
  · omega
  · omega
  · rw [fl42, u1, o42, i1, e6, lt_succ_exists, sideInArc_bits]
  · rw [fl43, v1, o43, i2, e6, lt_succ_exists]
  · rw [fl44, w1, o44, i3, e6, lt_succ_exists]
  · zuetd
    by_cases hq' : q ∈ [83030, 83032, 83033, 83034, 83035, 83036, 83037, 83038, 83039, 83040,
      83041, 83042, 83043, 83044, 83051]
    · grind
    · rw [g q h1 h2 hq', aS q h1 h2 hq]

/-- **The arc scan.** -/
def arcScan (kc : ℕ → ℕ → ℕ → ℕ → Stmt) : Stmt :=
  .seq (.instr (.constN 83042 0)) (.seq (.instr (.constN 83043 0))
    (.seq (.instr (.constN 83044 0)) (.seq ztwgp (.seq ztfey
      (.seq ztfer (.whileLtN 83030 83031 ztvek))))))

/-- The cost bound of the arc scan for a region with `A` arcs. -/
def arcScanK (Kk A : ℕ) : ℕ := 1 + (1 + (1 + (13 + (1 + (1 + (ztlfx * A + 2))))))

/-- A statement over the places of a region's arc list is one over its arcs. -/
theorem exists_place {N : NF} {r : ℕ} {p : ℕ → Prop} :
    (∃ t < (N.region r).arcs.length, p ztfpa) ↔ ∃ j ∈ (N.region r).arcs, p j := by
  constructor
  · zucjf
    refine ztrag
    zulub

  · zueco
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hj
    refine ztkna
    zulub

/-- **Contract of the arc scan**: the three flags. -/
theorem arcScan_rs (hK : KeyOK kc Kk)
    (hE : TGood P W M N c₀) (hne : (N.F M zta).Nonempty) (hI : TInv W c₀ c)
    (hroom : c.nreg ALLOC + arcScanK Kk (N.region ztco).arcs.length ≤ W) :
    RS P W c₀ ztvem c (arcScanK Kk (N.region ztco).arcs.length) (fun c' =>
      c'.nreg 83042 ≤ 1 ∧ c'.nreg 83043 ≤ 1 ∧ c'.nreg 83044 ≤ 1 ∧
      (c'.nreg 83042 = 1 ↔ FIn M P N ztco ztfy) ∧
      (c'.nreg 83043 = 1 ↔ FS M P N ztco ztfy) ∧
      (c'.nreg 83044 = 1 ↔ FE M P N ztco ztfy) ∧
      Agr c c' [83030, 83031, 83032, 83033, 83034, 83035, 83036, 83037, 83038, 83039, 83040,
        83041, 83042, 83043, 83044, 83051]) := by
  zqyn
  unfold arcScan arcScanK
  refine RS.seq zthsa
    fun c₁ hI₁ hA₁ h₁ => ?_
  refine RS.seq ztrke
    fun c₂ hI₂ hA₂ h₂ => ?_
  refine RS.seq ztrkf
    fun c₃ hI₃ hA₃ h₃ => ?_
  refine RS.seq (RS.op (tRegLen_exec (f := 0) ztp hE hI₃ (by unfold arcScanK at hroom; omega)))
    fun c₄ hI₄ hA₄ ⟨v₄, h8₄⟩ => ?_
  refine RS.seq (RS.copy hI₄ by_trivial)
    fun c₅ hI₅ hA₅ h₅ => ?_
  refine RS.seq (RS.const hI₅ by_trivial by_omega)
    fun c₆ hI₆ hA₆ h₆ => ?_
  have a₆ : Agr c c₆ [83042, 83043, 83044, 83031, 83030] :=
    (((((Agr.of_upd h₁).trans ztpvt).trans ztmai).trans
      ztril).trans (Agr.of_upd h₅)).trans (Agr.of_upd h₆) |>.mono by_simp
  have e31 : c₆.nreg 83031 = (N.region ztco).arcs.length := by
    rw [h₆, upd_ne by_norm_num, h₅, upd_eq, v₄]; rfl
  have e30 : c₆.nreg 83030 = 0 := by_simp_all
  have e42 : c₆.nreg 83042 = 0 := by
    simp_all
  have e43 : c₆.nreg 83043 = 0 := by
    simp_all
  have e44 : c₆.nreg 83044 = 0 := by
    simp_all
  have hI0 : ArcI M P N c₀ c₆ c₆ := by
    refine ⟨e31, by_omega, by_omega, by_omega, by_omega, ?_, ?_, ?_, Agr.refl _ _⟩ <;>
    · omega
  have hμ : ztlfx * (c₆.nreg 83031 - c₆.nreg 83030) =
      ztlfx * (N.region ztco).arcs.length := by
    simp_all
  refine (RS.while _ ztgiv _
    by_simp_all
    (fun c hIc hA ht hr => (arcBody_rs hK hE hne hIc hA ht hr).mono le_rfl
      fun c' ⟨hA', h30⟩ => ⟨hA', by zunqf; have := hA.1; omega⟩)
    hI₆ hI0 (by zvnhc; unfold arcScanK at hroom; omega)).mono (by zvnhc) ?_
  rintro c' ⟨⟨hL, htL, f1, f2, f3, i1, i2, i3, aS⟩, hnt⟩
  have hT : c'.nreg 83030 = (N.region ztco).arcs.length := by_omega
  zvncs at i1 i2 i3
  refine ⟨f1, f2, f3, i1.trans (exists_place (p := fun j => Chazelle.Chain.sideInArc
      (M.key _ (N.arc j).s) (M.key _ (N.arc j).e) _)),
    i2.trans (exists_place (p := fun j => M.key _ (N.arc j).s = M.key _ _)),
    i3.trans (exists_place (p := fun j => M.key _ _ = M.key _ (N.arc j).e) |>.trans
      ⟨fun ⟨j, hj, h⟩ => ⟨j, hj, h.symm⟩, fun ⟨j, hj, h⟩ => by_grind⟩), ?_⟩
  exact (a₆.trans aS).mono by_simp

/-! ## The exit scan -/

/-- The exit chord at place `t` of the region. -/
def chordAt (N : NF) (r t : ℕ) : ℕ := (N.region r).chords.getD t 0

/-- The end of a chord record the ray from the candidate would run along: the left end for
`σ = 1`, the right end otherwise. -/
def endPos (σb : ℕ) (cr : CRec) : WPos := if σb = 1 then cr.lpos else cr.rpos

/-- A field read of the chord in `83032` and a copy into `d`. -/
def chF (f d : ℕ) : Stmt := .seq (tChordF f 83032) ztovx
theorem chF_rs (hf : f < 5) (hd : Scr d) (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
    (hi : c.nreg 83032 < N.nChords) (hroom : c.nreg ALLOC + 11 ≤ W) :
    RS P W c₀ (chF f d) c 14
      (fun c' => c'.nreg d = crFld (N.chord ztvja) f ∧ Agr c c' [d]) := by
  obtain ⟨c₁, k₁, e₁, hk₁, v₁, hI₁, hrf₁, h8₁⟩ :=
    tChordF_exec hf ztmnu hE hI hi hroom
  zqyj
  · simp_all
  · zuhck

/-- The chord at place `t` of the region is a chord record. -/
theorem chordAt_lt (hE : TGood P W M N c₀) {t : ℕ}
    (ht : t < (N.region ztco).chords.length) :
    chordAt N ztco t < N.nChords ∧
      chordAt N ztco t ∈ (N.region ztco).chords := by
  zugnb
  zuchj
  have hmem : chordAt N ztco t ∈ (N.region ztco).chords := by
    zulbl
    simp_all
  exact ⟨(((hregs _ hr).1 _).1 hmem).1, hmem⟩

/-- **Reading the relevant end of the chord at place `83030`** into `83048`, `83047`. -/
def endRead : Stmt :=
  .seq ztuby (.seq ztigl
    (.seq ztthw (.seq ztnax
      (.ifLtN 83008 83023 (chF 2 83048) ztthx))))
theorem endRead_rs (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
    (ht : c.nreg 83030 < (N.region ztco).chords.length)
    (hroom : c.nreg ALLOC + 60 ≤ W) :
    RS P W c₀ endRead c 60 (fun c' =>
      c'.nreg 83048 = (endPos ztbkn (N.chord (chordAt N ztco
        ztccu))).edge ∧
      c'.nreg 83047 = (endPos ztbkn (N.chord (chordAt N ztco
        ztccu))).hgt ∧
      Agr c c' [83032, 83047, 83048]) := by
  zuhfa
  have h1 := tRegItem_exec (tr := 83030) ztbt by_trivial hE hI
    by_simp_all by_omega
  zujkf
  refine RS.mono (K := 20 + (1 + (14 + (1 + (14 + 2))))) ?_ by_norm_num ztb
  refine RS.seq ztqck fun c₁ hI₁ hA₁ ⟨v₁, h8₁⟩ =>
    RS.seq (RS.copy hI₁ (r := 83032) (a := 50210) by_trivial)
    fun c₂ hI₂ hA₂ hc₂ => ?_
  have q2 : c₂.nreg 83032 = chordAt N ztco ztccu := by
    zunie; rfl
  zuclq
  refine RS.seq (chF_rs (f := 0) (d := 83047) by_norm_num by_trivial hE hI₂
    by_omega by_omega) fun c₃ hI₃ hA₃ ⟨v₃, a₃⟩ => ?_
  have q3 : c₃.nreg 83032 = chordAt N ztco ztccu := by
    zunea
  zugkx
  have hh : (N.chord ztxdx).h < P.n := by
    zubtv
    have := hh _ hil
    zuic
  refine RS.seq (RS.add hI₃ by_trivial
    (by zuoal; have := hE.hW; unfold hostWords at this; zuosy; omega))
    fun c₄ hI₄ hA₄ h₄ => ?_
  have q4 : c₄.nreg 83032 = chordAt N ztco ztccu := by
    simp_all
  have v4 : c₄.nreg 83047 = (N.chord ztxdx).h + 1 := by
    zunmq; rfl
  have a4 : Agr c c₄ [83032, 83047] :=
    ((a2.trans a₃).trans ztjgm).mono by_simp
  have i8 := hI₄.hin 83008 by_norm_num by_norm_num
  have e23' := hI₄.h23
  have fin : ∀ f, f < 5 → (f = 1 ↔ c₀.nreg 83008 = 1) → (f = 2 ↔ c₀.nreg 83008 ≠ 1) →
      RS P W c₀ _ c₄ 14 (fun c' =>
      c'.nreg 83048 = (endPos _ _).edge ∧
      c'.nreg 83047 = (endPos ztbkn _).hgt ∧
      Agr c c' [83032, 83047, 83048]) := fun f hf h1 h2 =>
    (chF_rs (d := 83048) hf by_trivial hE hI₄ by_omega
      by_omega).mono le_rfl fun c₅ ⟨v₅, a₅⟩ => by
      refine ⟨?_, ?_, (a4.trans a₅).mono by_simp⟩
      · rw [v₅, q4]
        zuiqc
        by_cases hσ : c₀.nreg 83008 = 1
        · rw [ite_eq_left hσ, h1.2 hσ]; rfl
        · rw [ite_eq_right hσ, h2.2 hσ]; rfl
      · rw [a₅ _ by_norm_num by_norm_num by_simp, v4]
        zuiqc
        zujpl
  have hσ1 := hE.hσ
  by_cases hσ : c₄.nreg 83008 < c₄.nreg 83023
  · refine RS.ifT hσ (fin 2 by_norm_num by_omega by_omega)
  · refine RS.ifF hσ by_grind

/-- The body of the exit loop. -/
def exitBody (kc : ℕ → ℕ → ℕ → ℕ → Stmt) : Stmt :=
  .seq endRead (.seq (.seq ztqsg zttij)
    (.seq (updEq 83037 83038 83046) ztejr))

/-- The cost bound of the body of the exit loop. -/
def exitKB (Kk : ℕ) : ℕ := 60 + (ztblz + ztngt)

/-- The key of the relevant end of the exit chord at place `t`. -/
noncomputable def kendAt (M : Model) (P : Polygon) (N : NF) (r σb t : ℕ) : ℝ :=
  M.key zta (endPos σb (N.chord ztdna))

/-- **The invariant of the exit loop** (started in `cS`). -/
def ExitI (M : Model) (P : Polygon) (N : NF) (c₀ cS c : Config) : Prop :=
  c.nreg 83031 = (N.region ztco).chords.length ∧
    c.nreg 83030 ≤ c.nreg 83031 ∧ c.nreg 83046 ≤ 1 ∧
    (c.nreg 83046 = 1 ↔ ∃ t < c.nreg 83030,
      kendAt M P N ztco ztbkn t = M.key zta ztfy) ∧
    Agr cS c [83030, 83032, 83037, 83038, 83046, 83047, 83048]
theorem endPos_posG (hE : TGood P W M N c₀) {i : ℕ} (hi : i < N.nChords) (σb : ℕ) :
    PosG M zta P.n ztpba := by
  zuiqc
  split_ifs
  · exact (hE.chordPosG hi).1
  · exact (hE.chordPosG hi).2

/-- **One iteration of the exit loop.** -/
theorem exitBody_rs (hK : KeyOK kc Kk)
    (hE : TGood P W M N c₀) {cS : Config}
    (hI : TInv W c₀ c) (hA : ExitI M P N c₀ cS c) (ht : c.nreg 83030 < c.nreg 83031)
    (hroom : c.nreg ALLOC + exitKB Kk ≤ W) :
    RS P W c₀ ztvqa c (exitKB Kk) (fun c' => ExitI M P N c₀ cS c' ∧
      c'.nreg 83030 = c.nreg 83030 + 1) := by
  obtain ⟨hL, htL, f1, i1, aS⟩ := hA
  zudpj

  have hpos := endPos_posG hE hil ztbkn
  unfold exitBody exitKB
  refine RS.seq (endRead_rs hE hI ht' ztnvs)
    fun c₁ hI₁ hA₁ ⟨s1, s2, a₁⟩ => ?_
  have hy : ztzoz := by_simp_all
  zuehn

  have hx : PosG M zta P.n ztkkd := by
    zudkd
  refine RS.seq (kcmp_rs hK by_trivial by_trivial by_trivial
    by_trivial by_trivial by_trivial by_omega hE hI₁ hy hx
    ztnvs) fun c₂ hI₂ hA₂ ⟨b37, b38, a₂⟩ => ?_
  refine RS.seq (updEq_rs by_trivial hI₂ b37 b38) fun c₃ hI₃ hA₃ ⟨v1, v2, a₃⟩ => ?_
  have e30 : c₃.nreg 83030 = c.nreg 83030 := by
    rw [a₃ _ by_norm_num by_norm_num by_simp, a₂ _ by_norm_num by_norm_num by_simp,
      a₁ _ by_norm_num by_norm_num by_simp]
  zugkx
  refine (RS.add hI₃ by_trivial
    (by zuoni; have := hI.hw.1 83031; omega)).mono le_rfl fun c₄ h₄ => ?_
  have e4 : c₄.nreg 83030 = c.nreg 83030 + 1 := by_simp_all
  have a14 := ((a₁.trans a₂).trans a₃).trans ztjgm
  have g : ∀ q, 80000 ≤ q → q < 90000 →
      q ∉ [83030, 83032, 83037, 83038, 83046, 83047, 83048] → c₄.nreg q = c.nreg q :=
    fun q h1 h2 hq => a14 q h1 h2 by_simp_all
  have fl : c₄.nreg 83046 = c₃.nreg 83046 := by rw [h₄, upd_ne by_norm_num]
  have o46 : c₂.nreg 83046 = c.nreg 83046 := by
    zqyk
  have kx : M.key zta ztkkd = M.key zta ztfy := by
    zuikw
  have ky : M.key zta ztkke =
      kendAt M P N ztco ztbkn ztccu := by
    zumzh; rfl
  refine ⟨ztln, e4⟩
  · zqyp
  · rw [e4, g 83031 by_norm_num by_norm_num by_simp]; omega
  · omega
  · grind
  · zuetd
    rw [g q h1 h2 hq, aS q h1 h2 hq]

/-- **The exit scan.** -/
def exitScan (kc : ℕ → ℕ → ℕ → ℕ → Stmt) : Stmt :=
  .seq (.instr (.constN 83046 0)) (.seq ztqxg (.seq ztfey
    (.seq ztfer (.whileLtN 83030 83031 ztvqa))))

/-- The cost bound of the exit scan for a region with `D` exit chords. -/
def exitScanK (Kk D : ℕ) : ℕ := 1 + (13 + (1 + (1 + (ztlnr * D + 2))))

/-- A statement over the places of a region's chord list is one over its exit chords. -/
theorem exists_cplace {N : NF} {r : ℕ} {p : ℕ → Prop} :
    (∃ t < (N.region r).chords.length, p ztdna) ↔ ∃ i ∈ (N.region r).chords, p i := by
  constructor
  · zucjf
    refine ztrag
    zulbl
    simp_all
  · zucjd
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hi
    refine ztkna
    zulbl
    simp_all
theorem not_clear_iff {M : Model} {P : Polygon} {N : NF} {r : ℕ} {x : WPos} {σb : ℕ} :
    ¬ Clear M P N r x σb ↔ ∃ i ∈ (N.region r).chords,
      M.key zta ztpba = M.key zta x := by
  unfold Clear endPos
  grind

/-- **Contract of the exit scan**: the flag `83046` is `1` iff some exit chord of the region
leaves the candidate in the direction. -/
theorem exitScan_rs (hK : KeyOK kc Kk)
    (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
    (hroom : c.nreg ALLOC + exitScanK Kk (N.region ztco).chords.length ≤ W) :
    RS P W c₀ ztvqb c (exitScanK Kk (N.region ztco).chords.length) (fun c' =>
      c'.nreg 83046 ≤ 1 ∧
      (c'.nreg 83046 = 1 ↔ ¬ Clear M P N ztco ztfy ztbkn) ∧
      Agr c c' [83030, 83031, 83032, 83037, 83038, 83046, 83047, 83048]) := by
  zqyn
  unfold exitScan exitScanK
  refine RS.seq zthsa
    fun c₁ hI₁ hA₁ h₁ => ?_
  refine RS.seq (RS.op (tRegLen_exec (f := 2) ztbt hE hI₁
    (by unfold exitScanK at hroom; omega))) fun c₂ hI₂ hA₂ ⟨v₂, h8₂⟩ => ?_
  refine RS.seq zttbt
    fun c₃ hI₃ hA₃ h₃ => ?_
  refine RS.seq (RS.const hI₃ by_trivial by_omega)
    fun c₄ hI₄ hA₄ h₄ => ?_
  have a₄ : Agr c c₄ [83046, 83031, 83030] :=
    ((((Agr.of_upd h₁).trans ztrik).trans ztmai).trans
      ztjgm).mono by_simp
  have e31 : c₄.nreg 83031 = (N.region ztco).chords.length := by
    rw [h₄, upd_ne by_norm_num, h₃, upd_eq, v₂]; rfl
  have e30 : ztuta := by_simp_all
  have e46 : c₄.nreg 83046 = 0 := by
    simp_all
  have hI0 : ExitI M P N c₀ c₄ c₄ := by
    refine ⟨e31, by_omega, by_omega, ?_, Agr.refl _ _⟩
    omega
  have hμ : ztlnr * (c₄.nreg 83031 - c₄.nreg 83030) =
      ztlnr * (N.region ztco).chords.length := by
    simp_all
  refine (RS.while _ ztgiv _
    by_simp_all
    (fun c hIc hA ht hr => (exitBody_rs hK hE hIc hA ht hr).mono le_rfl
      fun c' ⟨hA', h30⟩ => ⟨hA', by zunqf; have := hA.1; omega⟩)
    hI₄ hI0 (by zvnhc; unfold exitScanK at hroom; omega)).mono (by zvnhc) ?_
  rintro c' ⟨⟨hL, htL, f1, i1, aS⟩, hnt⟩
  have hT : c'.nreg 83030 = (N.region ztco).chords.length := by_omega
  zvncs at i1
  refine ⟨f1, i1.trans ((exists_cplace).trans not_clear_iff.symm),
    (a₄.trans aS).mono by_simp⟩
end
end Restore
end Chazelle.Core
end
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Set
open Chazelle.Chain (SideAttach sideInArc sidePt TouchesIn)
open Classical in
/-- The number of places `t' < t` satisfying `p`. -/
noncomputable def cntP (p : ℕ → Prop) (t : ℕ) : ℕ := ((Finset.range t).filter p).card
open Classical in
theorem cntP_succ (p : ℕ → Prop) (t : ℕ) :
    cntP p ztbx = cntP p t + (if p t then 1 else 0) := by
  unfold cntP
  zuewn
variable (p : ℕ → Prop)
open Classical in
theorem cntP_zero : cntP p 0 = 0 := by_rfl
open Classical in
theorem cntP_le (t : ℕ) : cntP p t ≤ t := by
  unfold cntP
  grind
variable {M : Model} {P : Polygon} {N : NF}

/-- The exit chord record `i` has an end with key strictly inside `(k₁, k₂)`. -/
def SideHit (M : Model) (P : Polygon) (N : NF) (k₁ k₂ : ℝ) (i : ℕ) : Prop :=
  sideInArc k₁ k₂ (M.key zta (N.chord i).lpos) ∨
    sideInArc k₁ k₂ (M.key zta (N.chord i).rpos)

/-- **The attachments of a record** are its ends (by key). -/
theorem record_attach (hGM : GoodModel M) (hNF : IsNF M zta N) {i : ℕ} (hi : i < N.nChords)
    {p : ℕ} {t : ℝ} (h : SideAttach M.W ztymj p t) :
    (p : ℝ) + t = M.key zta (N.chord i).lpos ∨ (p : ℝ) + t = M.key zta (N.chord i).rpos := by
  zubm
  have hadm : (N.chord i).toSet M zta ∈ M.Adm := hNF.1.2.1 (chord_toSet_mem' hi)
  zukba
  have hne : sidePt M.W (N.chord i).lp (M.param zta (N.chord i).lpos) ≠
      sidePt M.W (N.chord i).rp (M.param zta (N.chord i).rpos) := by
    zuhgj
    have := endpoints_lt hM hadm hat
    have e : M.pos zta (N.chord i).lpos = M.pos zta (N.chord i).rpos := h'
    simp_all
  exact attach_key_cases hM hadm hat.1 hat.2 hne h

/-- **An exit chord record is attached inside `(k₁, k₂)` iff one of its ends is.** -/
theorem attach_side_iff (hGM : GoodModel M) (hNF : IsNF M zta N) {i : ℕ} (hi : i < N.nChords)
    (k₁ k₂ : ℝ) :
    (∃ (p : ℕ) (t : ℝ), SideAttach M.W ztymj p t ∧ sideInArc k₁ k₂ ztk) ↔
      SideHit M P N k₁ k₂ i := by
  zukba
  constructor
  · rintro ⟨p, t, hA, hin⟩
    rcases record_attach hGM hNF hi hA with h | h
    · exact Or.inl zttli
    · exact Or.inr zttli
  · zunp
    · exact ⟨_, _, hat.1, h⟩
    · exact ⟨_, _, hat.2, h⟩

/-- **The side counts are the numbers of places of the region's chord list** satisfying
`SideHit`. -/
theorem sideExits_ncard (hGM : GoodModel M) (hNF : IsNF M zta N) {reg : ℕ → Set Point}
    (hregs : NFRegs M zta N reg) {r : ℕ} (hr : r < N.nRegions) (k₁ k₂ : ℝ) :
    (sideExits M ztwiv ztcz k₁ k₂).ncard =
      cntP (fun t => SideHit M P N k₁ k₂ ztdna) (N.region r).chords.length := by
  obtain ⟨-, -, -, hRok⟩ := hregs
  obtain ⟨hlist, hnd, -, -⟩ := hRok r hr
  set L := (N.region r).chords with hL
  -- the chords of the side are the images of the places
  have himg : sideExits M ztwiv ztcz k₁ k₂ =
      ztyax ''
        {t | t < L.length ∧ SideHit M P N k₁ k₂ ztdna} := by
    zubcj
    constructor
    · rintro ⟨⟨hcF, htouch⟩, p, t, hA, hin⟩
      obtain ⟨i, hi, rfl⟩ := mem_F_iff hcF
      have hmem : i ∈ L := (hlist i).2 ⟨hi, htouch⟩
      obtain ⟨t', ht', hti⟩ := List.getElem_of_mem hmem
      have hat : chordAt N r t' = i := by
        zulbl
        grind
      refine ⟨t', ⟨ht', ?_⟩, by_simp_all⟩
      rw [hat]
      exact (attach_side_iff hGM hNF hi k₁ k₂).1 ⟨p, t, hA, hin⟩
    · rintro ⟨t', ⟨ht', hs⟩, rfl⟩
      have hmem : chordAt N r t' ∈ L := by
        zulbl
        grind
      obtain ⟨hi, htouch⟩ := (hlist _).1 hmem
      exact ⟨⟨chord_toSet_mem' hi, htouch⟩, (attach_side_iff hGM hNF hi k₁ k₂).2 hs⟩
  -- the map from places to chords is injective
  have hinj : Set.InjOn ztyax
      {t | t < L.length ∧ SideHit M P N k₁ k₂ ztdna} := by
    rintro t₁ ⟨h₁, -⟩ t₂ ⟨h₂, -⟩ heq
    have g : ∀ t (ht : t < L.length), chordAt N r t = L[t] := fun t ht => by
      zulbl
      grind
    have m₁ : chordAt N r t₁ ∈ L := by_grind
    have m₂ : chordAt N r t₂ ∈ L := by_grind
    have hi₁ : chordAt N r t₁ < N.nChords := ((hlist _).1 m₁).1
    have hi₂ : chordAt N r t₂ < N.nChords := ((hlist _).1 m₂).1
    have hij := hNF.2.1 _ _ hi₁ hi₂ heq
    simp_all
  rw [himg, hinj.ncard_image]
  classical
  unfold cntP
  zuezr
  zucr
  zufso
  simp
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim ShotList
variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ c : Config}

/-! ## Mathematics -/
theorem param_vtx (M : Model) (Q : Polygon) (e : ℕ) : M.param Q ztjy = 0 := rfl
theorem key_vtx' (M : Model) (Q : Polygon) (e : ℕ) : M.key Q ztjy = e := by
  simp [Model.key, param_vtx]

/-- A position with parameter `0` has the point and key of the start vertex of its edge. -/
theorem param_zero_same {M : Model} {Q : Polygon} {e h : ℕ} (hp : M.param Q ztcq = 0) :
    M.pos Q ztcq = M.pos Q ztjy ∧ M.key Q ztcq = M.key Q ztjy := by
  zujx
  · zunuw; tauto
  · simp only [Model.key]; tauto

/-- The key of `(e, 0)` is below that of `(e, h)` iff the parameter of `(e, h)` is positive. -/
theorem key_vtx_lt_iff {M : Model} {Q : Polygon} {e h : ℕ} :
    M.key Q ztjy < M.key Q ztcq ↔ 0 < M.param Q ztcq := by
  simp only [Model.key, param_vtx]; simp

/-- **The normal form of a position**: `(e, 0)` if its parameter is `0`, else itself. -/
noncomputable def normOf (M : Model) (Q : Polygon) (u : WPos) : WPos :=
  if M.param Q u = 0 then ⟨u.edge, 0⟩ else u
theorem normOf_facts {M : Model} {Q : Polygon} {n : ℕ} {u : WPos} (hu : ProperPos M Q n u) :
    NormPos M Q n zthza ∧ (normOf M Q u).edge = u.edge ∧
      M.pos Q zthza = M.pos Q u ∧ M.key Q zthza = M.key Q u ∧
      ((normOf M Q u).hgt = 0 ∨ 0 < M.param Q zthza) := by
  obtain ⟨e, h⟩ := u
  unfold normOf
  by_cases hp : M.param Q ztcq = 0
  · zuhmg
    obtain ⟨p1, k1⟩ := param_zero_same hp
    refine ⟨⟨⟨by_rfl, by_positivity, by_simp⟩, Or.inl rfl⟩, rfl,
      p1.symm, k1.symm, Or.inl rfl⟩
  · zuhmq
    have h0 : 0 < M.param Q ztcq := lt_of_le_of_ne hu.1 (Ne.symm hp)
    exact ⟨⟨hu, Or.inr h0⟩, rfl, rfl, rfl, Or.inr h0⟩

/-! ## The machine -/

/-- The parameter test by the key comparison: `(e, h)` becomes `(e, 0)` if `key (e, 0)` is not
below `key (e, h)`. -/
def tNormK (s : ℕ) : Stmt :=
  .seq (.seq (gKey s 83022 s ztbk) (cp2 ztfp ztjv))
    (.ifLtN ztfp 83023 (.instr (.constN ztbk 0)) .skip)

/-- **Normalising the position in `s`, `s + 1`** (scratch `s + 2 … s + 4`). -/
def tNorm (s : ℕ) : Stmt :=
  .ifLtN 83022 ztbk
    (.seq (.instr (.constN ztiz 6))
      (.ifLtN 83021 83023 (.ifLtN s ztiz .skip ztqxf) ztqxf))
    .skip

/-- The cost bound of `tNorm`. -/
def normK : ℕ := 11010 + 20
variable {s : ℕ}
/-- The key-comparison branch. -/
theorem tNormK_rs (hs : Scr s ∧ Scr ztbk ∧ Scr ztfp ∧ Scr ztjv ∧ Scr ztiz)
    (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
    (hp : ProperPos M zta P.n ztwlz) (he : c.nreg s < M.W.n)
    (h0 : 0 < c.nreg ztbk)
    (hbox : ∀ C : Chain, M = chainModel C → 6 ≤ c.nreg s) (hroom : c.nreg ALLOC + normK ≤ W) :
    RS P W c₀ ztqxf c (11010 + 6) (fun c' => c'.nreg s = c.nreg s ∧
      ⟨c'.nreg s, c'.nreg ztbk⟩ = normOf M zta ⟨c.nreg s, c.nreg ztbk⟩ ∧
      Agr c c' [s + 1, s + 2, s + 3]) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hs
  unfold Scr at h1 h2 h3 h4
  zumfh
  have i23 := hI.h23
  have inR : ∀ r, Scr r → InR r := fun r hr => by unfold Scr at hr; unfold InR; omega
  have hk := kcmp_rs (P := P) (W := W) gKey_ok (a := s) (b := 83022) (d := s) (e := s + 1)
    (u := s + 2) (v := s + 3) ztjqv by_trivial ztjqv
    ztjqv by_tauto by_tauto by_omega hE hI
    ⟨by exact he, by rw [i22]; exact ⟨le_rfl, by_positivity, Nat.zero_le _⟩,
      fun C hM _ => hbox C hM⟩
    ⟨he, hp, fun C _ hh => by_simp_all⟩ (by unfold normK at hroom; omega)
  rw [i22] at hk
  refine RS.mono (K := (11010 + 2) + (0 + 2 + 1)) ?_ by_norm_num ztb
  unfold tNormK
  refine RS.seq hk fun c₁ hI₁ _ ⟨b1, _, a1⟩ => ?_
  have k1s : ztsgq := a1 _ by_omega by_omega by_simp
  have k1h : c₁.nreg ztbk = c.nreg ztbk := a1 _ by_omega by_omega by_simp
  have k23 : ztlxx := hI₁.h23
  rw [key_vtx_lt_iff] at b1
  rcases bit01 b1 with ⟨bz, hnp⟩ | ⟨bo, hpos⟩
  · -- parameter `0`
    have hp0 : M.param zta ztwlz = 0 := le_antisymm ztwaj hp.1
    refine RS.ifT by_omega ((RS.const hI₁ (r := s + 1) (v := 0) by_tauto
      ztbg).mono by_norm_num fun c₂ hc₂ => ?_)
    have e2s : c₂.nreg s = c.nreg s := by_simp_all
    refine ⟨e2s, ?_, (a1.trans zthqq).mono by_simp⟩
    rw [e2s, hc₂, upd_eq]; unfold normOf; simp_all
  · -- positive parameter
    refine RS.ifF by_omega ((RS.skip hI₁ (K := 1) (Q := fun c' =>
      c'.nreg s = c.nreg s ∧ ⟨c'.nreg s, c'.nreg ztbk⟩ =
        normOf M zta ztwlz ∧ Agr c c' [s + 1, s + 2, s + 3])
      ⟨k1s, ?_, a1.mono by_simp⟩))
    rw [k1s, k1h]; unfold normOf; grind

/-- **Normalising a position.** -/
theorem tNorm_rs (hs : Scr s ∧ Scr ztbk ∧ Scr ztfp ∧ Scr ztjv ∧ Scr ztiz)
    (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
    (hp : ProperPos M zta P.n ztwlz) (he : c.nreg s < M.W.n)
    (hy : ∀ C : Chain, M = chainModel C →
      |(M.pos (Qof P) ⟨c.nreg s, c.nreg (s + 1)⟩).2| < C.radius)
    (hroom : c.nreg ALLOC + normK ≤ W) :
    RS P W c₀ ztwgo c normK (fun c' => c'.nreg s = c.nreg s ∧
      ⟨c'.nreg s, c'.nreg ztbk⟩ = normOf M zta ⟨c.nreg s, c.nreg ztbk⟩ ∧
      Agr c c' [s + 1, s + 2, s + 3, s + 4]) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  have hs' : Scr s ∧ Scr ztbk ∧ Scr ztfp ∧ Scr ztjv ∧ Scr ztiz :=
    ⟨h1, h2, h3, h4, h5⟩
  unfold Scr at h1 h2 h3 h4 h5
  zumfh
  unfold tNorm
  by_cases hh : c.nreg 83022 < c.nreg ztbk
  swap
  · -- a vertex: already normal
    have hz : ztback := by_omega
    refine RS.ifF hh (RS.skip hI ztoph)
    unfold normOf; simp_all
  have h0 : ztbabq := by_omega
  refine RS.ifT hh ?_
  refine RS.mono (K := 1 + (11010 + 6 + 2 + 2)) ?_ by_norm_num ztb
  refine RS.seq (RS.const hI (r := s + 4) (v := 6) by_simp_all
    (by have := hE.hW; unfold hostWords at this; omega)) fun c₁ hI₁ hA₁ hc₁ => ?_
  have k1 : ∀ r, r ≠ s + 4 → c₁.nreg r = c.nreg r := fun r hr => by_simp_all
  have p1 : ProperPos M zta P.n ztxzl := by
    simp_all
  have e1 : c₁.nreg s < M.W.n := by_simp_all
  have z1 : 0 < c₁.nreg ztbk := by_simp_all
  have a1 : Agr c c₁ [s + 4] := Agr.of_upd hc₁
  have fin : ∀ c₂, (c₂.nreg s = c₁.nreg s ∧ ztzij =
      normOf M zta ztxzl ∧ Agr c₁ c₂ [s + 1, s + 2, s + 3]) →
      (c₂.nreg s = c.nreg s ∧ ztzij =
        normOf M zta ztwlz ∧ Agr c c₂ [s + 1, s + 2, s + 3, s + 4]) :=
    fun c₂ ⟨q1, q2, q3⟩ => by
      refine ⟨by_simp_all, by_simp_all,
        (a1.trans q3).mono by_simp⟩
  have hroom1 : c₁.nreg ALLOC + normK ≤ W := by
    have := hI₁.hA; rw [k1 _ ztu]; omega
  have i21 := hI₁.h21
  have i23 := hI₁.h23
  rcases hE.kind with ⟨hz, C, hMC⟩ | ⟨h1', hMi, -⟩
  · -- a chain model
    refine RS.ifT by_omega ?_
    by_cases hb : c₁.nreg s < c₁.nreg ztiz
    · -- a box edge: the parameter is positive
      have h6 : ztuox := by rw [k1 s by_omega, hc₁, upd_eq] at hb; exact hb
      have hpos : 0 < M.param zta ztwlz := by
        subst hMC
        exact box_param_pos C (x := ztwlz) h6 hp.1 (hy C rfl)
      refine RS.ifT hb (RS.skip hI₁ (fin c₁ ztoph))
      rw [k1 s by_omega, k1 ztbk by_omega]
      unfold normOf; grind
    · refine RS.ifF hb ((tNormK_rs hs' hE hI₁ p1 e1 z1 (fun C' _ => ?_) hroom1).mono
        by_norm_num fin)
      have v4 : c₁.nreg ztiz = 6 := by rw [hc₁, upd_eq]
      omega
  · -- the interior model
    refine RS.ifF by_omega ((tNormK_rs hs' hE hI₁ p1 e1 z1
      (fun C' hC' => absurd (hC'.symm.trans hMi) (chainModel_ne_interior C' _)) hroom1).mono
      by_norm_num fin)
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim SignK
variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ c : Config}

/-! ## Programs without stores keep the memory -/
variable {s : Stmt} {K : ℕ} {Q : Config → Prop} {m : ℕ → ℕ}
/-- A run step of a program without memory writes keeps the memory. -/
theorem RS.nomem (hs : wr (fun _ => true) s = true)
    (h : RS P W c₀ s c K Q) : RS P W c₀ s c K (fun c' => Q c' ∧ c'.nmem = c.nmem) := by
  zuw
  exact ⟨c', k, ex, hk, hI, hrf, hq, (exec_frameB ex hs).2.2.1⟩

/-- Registers other than the allocator. -/
def NotA (r : ℕ) : Bool := decide (r ≠ ALLOC)

/-- A run step of a program that writes neither the memory nor the allocator keeps both. -/
theorem RS.keepA (hs : wr NotA s = true)
    (h : RS P W c₀ s c K Q) :
    RS P W c₀ s c K (fun c' => Q c' ∧ c'.nmem = c.nmem ∧ c'.nreg ALLOC = c.nreg ALLOC) := by
  zuw
  have f := exec_frameB ex hs
  exact ⟨c', k, ex, hk, hI, hrf, hq, f.2.2.1, f.1 _ by_rfl⟩
theorem wr_notA_gKey (a b d e : ℕ) : wr NotA ztjxb = true :=
  wr_mono ztqyr (fun r h => by simp [NotA, (opW_BgK r h).2])
theorem wr_notA_tNorm {s : ℕ} (hs : s + 4 < ALLOC ∨ ALLOC < s) : wr NotA ztwgo = true := by
  unfold ALLOC at hs
  simp only [tNorm, tNormK, cp2, wr, wrOK, wr_notA_gKey, Bool.and_true, Bool.true_and, NotA,
    ALLOC]
  zuhos
  grind
theorem wr_notA_arcRead : wr NotA arcRead = true := by_decide

/-! ## Storing a record -/

/-- Store the two ends `83060, 83061` and `83070, 83071` at the allocator and advance it. -/
def storeRec : Stmt := block [.storeN ALLOC 83060, .addN ALLOC ALLOC 83023,
  .storeN ALLOC 83061, .addN ALLOC ALLOC 83023, .storeN ALLOC 83070, .addN ALLOC ALLOC 83023,
  .storeN ALLOC 83071, .addN ALLOC ALLOC 83023]
theorem storeRec_exec (c : Config) (hw : WordsBounded W c) {a : ℕ} (hA : c.nreg ALLOC = a)
    (h23 : c.nreg 83023 = 1) (ha : a + 4 ≤ W) :
    ∃ c' k, Exec P W storeRec c c' k ∧ k = 8 ∧ c'.nreg ALLOC = a + 4 ∧
      c'.nmem = upd (upd (upd (upd c.nmem a ztvjb) ztdf ztvjc)
        ztvj (c.nreg 83070)) (a + 3) (c.nreg 83071) ∧
      ztjn ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold storeRec
  zubtg
  exec_block
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, hA', h23, ALLOC]; omega)
  refine ⟨rfl, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp (disch := omega) only [Machine.upd_same, Machine.upd_other, hA', h23,
      ALLOC]
  · simp (disch := omega) only [Machine.upd_other, hA', h23, ALLOC]
  simp_all

/-- **Storing a record** as a run step. -/
theorem storeRec_rs (hI : TInv W c₀ c) (hroom : c.nreg ALLOC + 8 ≤ W) :
    RS P W c₀ storeRec c 8 (fun c' => c'.nreg ALLOC = c.nreg ALLOC + 4 ∧
      c'.nmem = upd (upd (upd (upd c.nmem ztm ztvjb) ztccv
        ztvjc) (c.nreg ALLOC + 2) (c.nreg 83070)) (c.nreg ALLOC + 3) (c.nreg 83071) ∧
      ztjn) := by
  obtain ⟨c', k, ex, hk, hA', hm, hr, hrr, hrm, ho⟩ := storeRec_exec (P := P) c hI.hw rfl hI.h23
    by_omega
  zubnp
  have mlow : zteih := fun a ha => by
    zvmwi; zvmwf
    grind
  refine ⟨c', k, ex, by_omega, ⟨ex.wb_right, fun q h1 h2 => by
      rw [hr q ztu]; exact hI.hin q h1 h2, by_omega,
      fun a ha => by rw [mlow a by_omega]; exact hI.hm a ha,
      by zumwn; exact hI.h20,
      by zumwn; exact hI.h21,
      by zumwn; exact hI.h22,
      by zumwn; exact hI.h23⟩,
    ⟨by_simp_all, by_simp_all, by_grind,
      by simp_all, ho, by_omega, by_omega⟩, hA', hm, hr⟩

/-! ## The arc ends of a chain model are inside the box band -/

/-- The box radius is determined by the chain model. -/
theorem radius_eq_of_model {C C' : Chain} (h : chainModel C = chainModel C') :
    C.radius = C'.radius := by
  have := congrArg (fun M : Model => (M.W.vtx 1).2) h
  tauto

/-- **The ends of the arc records** of a nonempty family of a chain model are strictly inside the
height band of the box. -/
theorem arc_abs_lt {C : Chain} (hP : C.P.Simple) (hNF : IsNF ztc zta N)
    (hne : (N.F ztc zta).Nonempty) {j : ℕ} (hj : j < N.arcs.length) :
    |((chainModel C).pos (Qof P) (N.arc j).s).2| < C.radius ∧
      |((chainModel C).pos (Qof P) (N.arc j).e).2| < C.radius := by
  zubua
  zuls

  zufjs
  have key : ∀ x : WPos, ProperPos ztc zta (Qof P).n x →
      (chainModel C).IsCut ztwjq ztwol →
      |((chainModel C).pos (Qof P) x).2| < C.radius := by
    zucse

    obtain ⟨hpp, htt⟩ := Chazelle.Chain.sideKey_inj hx.1 hx.2.1 hA.2.1 hA.2.2.1 hk
    zugxu
    exact chord_height_lt hP ztvtb hA.2.2.2.1
  simp_all

/-- The arc ends of a run are inside the box band, for every chain of the model. -/
theorem TGood.arc_abs (hE : TGood P W M N c₀) (hne : (N.F M zta).Nonempty) {j : ℕ}
    (hj : j < N.arcs.length) :
    (∀ C : Chain, M = chainModel C → |(M.pos zta (N.arc j).s).2| < C.radius) ∧
      (∀ C : Chain, M = chainModel C → |(M.pos zta (N.arc j).e).2| < C.radius) := by
  refine ztklb <;>
  · obtain ⟨C', hs, hM'⟩ := hE.chain_simple hM
    zucly

    have := arc_abs_lt hs hNF hne hj
    zuimi

/-! ## The loop -/

/-- The normalised ends of the arc at place `t` of region `r`. -/
noncomputable def nArc (M : Model) (Q : Polygon) (N : NF) (r t : ℕ) : WPos × WPos :=
  (normOf M Q (N.arc ztfpa).s, normOf M Q (N.arc ztfpa).e)

/-- **One arc**: read, normalise, store, advance. -/
def buildBody : Stmt :=
  .seq arcRead (.seq (.instr (.copyN 83060 83033)) (.seq (.instr (.copyN 83061 83034))
    (.seq (.instr (.copyN 83070 83035)) (.seq (.instr (.copyN 83071 83036))
      (.seq (tNorm 83060) (.seq (tNorm 83070) (.seq storeRec
        ztejr)))))))

/-- The cost of one arc. -/
def bodyK : ℕ := 80 + 4 + 2 * normK + 8 + 1

/-- The scratch registers of the arc loop. -/
def buildL : List ℕ := [83030, 83032, 83033, 83034, 83035, 83036, 83060, 83061, 83062, 83063,
  83064, 83070, 83071, 83072, 83073, 83074]

/-- The loop invariant: `t = 83030` records written at `base`. -/
def BuildI (M : Model) (Q : Polygon) (N : NF) (r K base : ℕ) (cB c : Config) : Prop :=
  c.nreg 83031 = K ∧ c.nreg 83081 = base ∧ c.nreg 83030 ≤ K ∧
    c.nreg ALLOC = base + 4 * c.nreg 83030 ∧
    (∀ j, j < c.nreg 83030 → ShotList.arcAt c.nmem base j = nArc M Q N r j) ∧
    Agr cB c buildL
theorem arcAt_upd4 {base t j : ℕ} {v0 v1 v2 v3 : ℕ} (hj : j < t) :
    ShotList.arcAt (upd (upd ztewb
      ztnrx v2) (base + 4 * t + 3) v3) base j = ShotList.arcAt m base j := by
  zujoa
  grind
theorem arcAt_upd4_new {base t : ℕ} {v0 v1 v2 v3 : ℕ} :
    ShotList.arcAt (upd (upd ztewb
      ztnrx v2) (base + 4 * t + 3) v3) base t = (⟨v0, v1⟩, ⟨v2, v3⟩) := by
  zujoa
  simp
set_option maxHeartbeats 1000000 in
/-- **One arc of the loop.** -/
theorem buildBody_rs (hE : TGood P W M N c₀) (hne : (N.F M zta).Nonempty) {K base : ℕ}
    {cB : Config} (hI : TInv W c₀ c)
    (hB : BuildI M zta N ztco K base cB c)
    (hK : K = (N.region ztco).arcs.length) (hlt : c.nreg 83030 < c.nreg 83031)
    (hroom : c.nreg ALLOC + bodyK ≤ W) :
    RS P W c₀ buildBody c bodyK (fun c' => BuildI M zta N ztco K base cB c' ∧
      c'.nreg 83030 = c.nreg 83030 + 1) := by
  obtain ⟨h31, h81, htK, hA, hrec, hag⟩ := hB
  set t := c.nreg 83030 with ht
  zuhol
  zukgg
  obtain ⟨hjl, -⟩ := arcAt_lt hE htl
  set j := arcAt N r t with hj
  zuc
  obtain ⟨hps, hpe⟩ : ProperPos M (Qof P) (Qof P).n (N.arc j).s ∧
      ProperPos M zta (Qof P).n (N.arc j).e := by
    obtain ⟨-, -, -, reg, -, -, -, -, -, -, hpp⟩ := hE.hNF
    simp_all
  zuexu
  obtain ⟨gs, ge⟩ := hE.arcPosG hne hjl
  obtain ⟨ys, ye⟩ := hE.arc_abs hne hjl
  have sc : ztmxq := by
    zucnh

  unfold bodyK at hroom ⊢
  refine RS.mono (K := 80 + (1 + (1 + (1 + (1 + (normK + (normK + ztsuf))))))) ?_
    by_omega ztb
  refine RS.seq (RS.keepA wr_notA_arcRead (arcRead_rs hE hI by_omega by_omega))
    fun c₁ hI₁ hA₁ ⟨⟨v33, v34, v35, v36, a₁⟩, m₁, al₁⟩ => ?_
  have cp : ∀ {cc : Config} (r a : ℕ), TInv W c₀ cc → r ∈ buildL →
      RS P W c₀ _ cc 1 (fun c' => (c'.nreg = upd cc.nreg r (cc.nreg a)) ∧
        c'.nmem = cc.nmem ∧ c'.nreg ALLOC = cc.nreg ALLOC) := fun r a hIc hr =>
    (RS.keepA (by
      have : ztjag := by
        simp only [buildL, List.mem_cons, List.not_mem_nil, or_false] at hr; unfold ALLOC; omega
      simp [wr, wrOK, NotA, this]) (RS.copy hIc by_simp_all))
  refine RS.seq (cp 83060 83033 hI₁ by_decide) fun c₂ hI₂ hA₂ ⟨hc₂, m₂, al₂⟩ => ?_
  refine RS.seq (cp 83061 83034 hI₂ by_decide) fun c₃ hI₃ hA₃ ⟨hc₃, m₃, al₃⟩ => ?_
  refine RS.seq (cp 83070 83035 hI₃ by_decide) fun c₄ hI₄ hA₄ ⟨hc₄, m₄, al₄⟩ => ?_
  refine RS.seq (cp 83071 83036 hI₄ by_decide) fun c₅ hI₅ hA₅ ⟨hc₅, m₅, al₅⟩ => ?_
  -- the registers after the copies
  have v60 : c₅.nreg 83060 = (N.arc j).s.edge := by
    rw [hc₅, upd_ne by_omega, hc₄, upd_ne by_omega, hc₃, upd_ne by_omega, hc₂, upd_eq, v33]
  have v61 : c₅.nreg 83061 = (N.arc j).s.hgt := by
    rw [hc₅, upd_ne by_omega, hc₄, upd_ne by_omega, hc₃, upd_eq, hc₂, upd_ne by_omega, v34]
  have v70 : c₅.nreg 83070 = (N.arc j).e.edge := by
    rw [hc₅, upd_ne by_omega, hc₄, upd_eq, hc₃, upd_ne by_omega, hc₂, upd_ne by_omega, v35]
  have v71 : c₅.nreg 83071 = (N.arc j).e.hgt := by
    rw [hc₅, upd_eq, hc₄, upd_ne by_omega, hc₃, upd_ne by_omega, hc₂, upd_ne by_omega, v36]
  have m15 : ztlaq := by_grind
  have A15 : ztizp := by_omega
  have ag5 : Agr c c₅ [83032, 83033, 83034, 83035, 83036, 83060, 83061, 83070, 83071] :=
    ((((a₁.trans zthqq).trans (Agr.of_upd hc₃)).trans ztuwk).trans
      (Agr.of_upd hc₅)).mono by_simp
  -- normalise the start
  have ps : (⟨c₅.nreg 83060, c₅.nreg 83061⟩ : WPos) = (N.arc j).s := by rw [v60, v61]
  refine RS.seq (RS.keepA ztwhw (tNorm_rs (s := 83060)
    ⟨sc _ by_decide, sc _ by_decide, sc _ by_decide,
      sc _ by_decide, sc _ by_decide⟩ hE hI₅ by_grind
    (by rw [v60]; exact gs.1) by_grind by_omega))
    fun c₆ hI₆ hA₆ ⟨⟨n60, n6, a₆⟩, m₆, al₆⟩ => ?_
  have k6 : ∀ q, 80000 ≤ q → q < 90000 → q ≠ 83061 → q ≠ 83062 → q ≠ 83063 → q ≠ 83064 →
      c₆.nreg q = c₅.nreg q := fun q h1 h2 h3 h4 h5 h6 => a₆ q h1 h2 by_grind
  have pe : (⟨c₆.nreg 83070, c₆.nreg 83071⟩ : WPos) = (N.arc j).e := by
    rw [k6 83070 by_norm_num by_norm_num by_omega by_omega by_omega by_omega,
      k6 83071 by_norm_num by_norm_num by_omega by_omega by_omega by_omega, v70, v71]
  refine RS.seq (RS.keepA ztwhw (tNorm_rs (s := 83070)
    ⟨sc _ by_decide, sc _ by_decide, sc _ by_decide,
      sc _ by_decide, sc _ by_decide⟩ hE hI₆ by_grind
    (by rw [k6 83070 by_norm_num by_norm_num by_omega by_omega by_omega by_omega,
      v70]; exact ge.1) by_grind
      by_omega))
    fun c₇ hI₇ hA₇ ⟨⟨n70, n7, a₇⟩, m₇, al₇⟩ => ?_
  have k7 : ∀ q, 80000 ≤ q → q < 90000 → q ≠ 83071 → q ≠ 83072 → q ≠ 83073 → q ≠ 83074 →
      c₇.nreg q = c₆.nreg q := fun q h1 h2 h3 h4 h5 h6 => a₇ q h1 h2 by_grind
  have A7 : c₇.nreg ALLOC = c.nreg ALLOC := by_omega
  have M7 : c₇.nmem = c.nmem := by_grind
  have w60 : c₇.nreg 83060 = c₆.nreg 83060 :=
    by grind
  have w61 : c₇.nreg 83061 = c₆.nreg 83061 :=
    by grind
  have ns : (⟨c₇.nreg 83060, c₇.nreg 83061⟩ : WPos) = normOf M zta (N.arc j).s := by
    grind
  have ne' : (⟨c₇.nreg 83070, c₇.nreg 83071⟩ : WPos) = normOf M zta (N.arc j).e := by
    grind
  -- store the record
  refine RS.seq (storeRec_rs hI₇ by_omega)
    fun c₈ hI₈ hA₈ ⟨A8, M8, R8⟩ => ?_
  have k8 : c₈.nreg 83030 = t := by
    rw [R8 _ by_decide, k7 _ by_norm_num by_norm_num by_omega by_omega
      by_omega by_omega, k6 _ by_norm_num by_norm_num by_omega by_omega by_omega
      by_omega, ag5 _ by_norm_num by_norm_num by_simp]
  refine (RS.nomem rfl (RS.add hI₈ (r := 83030) (a := 83030) (b := 83023) zttzv
    (by rw [k8, hI₈.h23]; omega))).mono le_rfl fun c₉ ⟨hc₉, M9⟩ => ?_
  have ag9 : Agr c c₉ buildL := by
    have a78 : Agr c₇ c₈ [] := fun q h1 h2 _ => R8 q ztu
    exact ((((ag5.trans a₆).trans a₇).trans a78).trans (Agr.of_upd hc₉)).mono (by
      decide)
  have q30 : c₉.nreg 83030 = t + 1 := by rw [hc₉, upd_eq, k8, hI₈.h23]
  have hA9 : c₉.nreg ALLOC = c.nreg ALLOC + 4 := by
    rw [hc₉, upd_ne by_decide, A8, A7]
  have hM9 : c₉.nmem = upd (upd (upd (upd c.nmem (base + 4 * t) (c₇.nreg 83060))
      (base + 4 * t + 1) (c₇.nreg 83061)) (base + 4 * t + 2) (c₇.nreg 83070))
      (base + 4 * t + 3) (c₇.nreg 83071) := by_grind
  refine ⟨⟨by rw [ag9 _ by_norm_num by_norm_num by_decide, h31],
    by rw [ag9 _ by_norm_num by_norm_num by_decide, h81], by_omega,
    by omega, fun j' hj' => ?_, (hag.trans ag9).mono by_simp⟩, q30⟩
  rw [q30] at hj'
  rw [hM9]
  rcases Nat.lt_or_ge j' t with hl | hg
  · rw [arcAt_upd4 hl]; grind
  · have : j' = t := by_omega
    zumo
    rw [arcAt_upd4_new]
    zujqr
    grind

/-- **The arc array of the region** at the allocator. -/
def arcBuild : Stmt :=
  .seq ztfer (.seq (.instr (.copyN 83081 ALLOC))
    (.seq ztwgp (.seq ztfey (.whileLtN 83030 83031 buildBody))))

/-- The cost of the arc array for `K` arcs. -/
def buildK (K : ℕ) : ℕ := 20 + zttgx * K

/-- **The arc array.** -/
theorem arcBuild_rs (hE : TGood P W M N c₀) (hne : (N.F M zta).Nonempty) (hI : TInv W c₀ c)
    (hroom : c.nreg ALLOC + buildK (N.region ztco).arcs.length ≤ W) :
    RS P W c₀ arcBuild c (buildK (N.region ztco).arcs.length) (fun c' =>
      c'.nreg 83081 = c.nreg ALLOC ∧
      c'.nreg ALLOC = c.nreg ALLOC + 4 * (N.region ztco).arcs.length ∧
      c'.nreg 83031 = (N.region ztco).arcs.length ∧
      (∀ j, j < (N.region ztco).arcs.length →
        ShotList.arcAt c'.nmem ztm j = nArc M zta N ztco j) ∧
      Agr c c' (83031 :: 83081 :: 50210 :: buildL)) := by
  set K := (N.region _).arcs.length with hKd
  set base := c.nreg ALLOC with hbase
  have sc : ztmxq := by
    zucnh

  unfold buildK at hroom ⊢
  refine RS.mono (K := 1 + (1 + (13 + (1 + (zttgx * K + 2))))) ?_ by_omega ztb
  refine RS.seq (RS.const hI zttzv ztbg)
    fun c₁ hI₁ hA₁ hc₁ => ?_
  have A1 : c₁.nreg ALLOC = base := by rw [hc₁, upd_ne by_decide]
  refine RS.seq (RS.copy hI₁ by_trivial)
    fun c₂ hI₂ hA₂ hc₂ => ?_
  have A2 : c₂.nreg ALLOC = base := by rw [hc₂, upd_ne by_decide, A1]
  obtain ⟨c₃, k₃, e₃, hk₃, v₃, st₃⟩ := tRegLen_exec (f := 0) ztp hE hI₂ by_omega
  refine RS.seq (RS.keepA by_decide (RS.op (Q := fun c' => c'.nreg 50210 = K)
    ⟨c₃, k₃, e₃, hk₃, v₃, st₃⟩)) fun c₃ hI₃ hA₃ ⟨⟨v3, h83⟩, _, A3⟩ => ?_
  refine RS.seq (RS.copy hI₃ by_trivial)
    fun c₄ hI₄ hA₄ hc₄ => ?_
  have A4 : c₄.nreg ALLOC = base := by rw [hc₄, upd_ne by_decide, A3, A2]
  have ag4 : Agr c c₄ [83030, 83081, 83031] :=
    (((Agr.of_upd hc₁).trans zthqq).trans ((Agr.of_band h83 []).trans
      ztuwk)).mono by_simp
  have q31 : c₄.nreg 83031 = K := by_simp_all
  have q81 : c₄.nreg 83081 = base := by
    simp_all
  have q30 : ztuta := by
    simp_all
  have I4 : BuildI M zta N ztco K base c₄ c₄ :=
    ⟨q31, q81, by_omega, by_omega, by_simp_all, Agr.refl _ _⟩
  refine (RS.while (BuildI M zta N ztco K base c₄)
    (fun cc => K - cc.nreg 83030) bodyK
    (fun cc hcc hlt => by obtain ⟨h1, -, -, -, -, -⟩ := hcc; omega)
    (fun cc hIc hcc hlt hr => (buildBody_rs hE hne hIc hcc hKd hlt hr).mono le_rfl
      fun c' ⟨h1, h2⟩ => ⟨h1, by obtain ⟨h31, -, h3, -⟩ := hcc; omega⟩)
    hI₄ I4 by_grind).mono by_simp
    fun c' ⟨hB, hnlt⟩ => ?_
  obtain ⟨h31, h81, htK, hA', hrec, hag⟩ := hB
  have ht : c'.nreg 83030 = K := by_omega
  refine ⟨h81, by_omega, h31, by_simp_all, ?_⟩
  exact (ag4.trans hag).mono (by
    decide)
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Set
open Chazelle.Chain (sideE sidePt sideInArc)
open Chazelle.Geometry (lerp)
open SweepPrim

/-! ## Tour indices -/
theorem tour_mod {m S a : ℕ} (hS : S ≤ 2 * m) (ha : a < 2 * m) :
    zttbx % ztdk = if S + a < 2 * m then S + a else S + a - 2 * m := by
  zus
  · zubql
  · zul

/-- The tour position determines the tour step. -/
theorem tour_inj {m S a b : ℕ} (hS : S ≤ 2 * m) (ha : a < 2 * m) (hb : b < 2 * m)
    (h : zttbx % ztdk = (S + b) % ztdk) : a = b := by
  rw [tour_mod hS ha, tour_mod hS hb] at h
  grind

/-- The tour positions of the chain edge `k`: `k` going up and `2m - 1 - k` going down. -/
theorem cover_pos {m j k : ℕ} (hj : j < 2 * m) (hk : k < m)
    (h : (sideE m j = k ∧ sideE m ztl = k + 1) ∨ (sideE m j = k + 1 ∧ sideE m ztl = k)) :
    j = k ∨ j = 2 * m - 1 - k := by
  unfold sideE at h; grind

/-! ## Positions in a chain model -/
variable {C : Chain}

/-- **The positions of a point inside an open chain edge** are the tour edge and its twin. -/
theorem chain_open_positions (hP : C.P.Simple) {i : ℕ} (hi : i < 2 * C.m) {t : ℝ} (ht : 0 < t)
    (ht1 : t < 1) {p' : ℕ} {t' : ℝ} (hp' : p' < (chainModel C).W.n) (ht' : 0 ≤ t')
    (ht1' : t' < 1)
    (heq : sidePt (chainModel C).W p' t' = sidePt (chainModel C).W ztcy t) :
    0 < t' ∧ (p' = i + 6 ∨ p' = tourTwin C i + 6) := by
  zucn
  rw [hW] at heq hp'
  zubt
  zuec
  obtain ⟨k, hk, s, hs, hz, hcov⟩ := C.sideTour_open C.sideBeta hi ztuih
  have hzmem : sidePt _ _ t ∈ C.set :=
    C.sideWalk_tour_pt_mem C.sideBeta hi.le by_grind ht.le ht1
  rcases C.sideWalk_pos_cases C.sideBeta hp' ht' with hbox | ⟨i', hi', rfl, hit'⟩
  · exact absurd by_simp_all (C.sideWalk_box_pt C.sideBeta hbox ht' ht1').1
  -- a tour position
  zugad
  swap
  · exfalso
    subst ht'0
    rw [Chazelle.Chain.sidePt_zero, C.sideWalk_vtx_tour _ hi', hz] at heq
    exact C.sideOpen_ne_vertex hP hs heq.symm
  have hi'2 : ztsjj := by
    grind
  obtain ⟨k', hk', s', hs', hz', hcov'⟩ := C.sideTour_open C.sideBeta hi'2 ⟨ht'0, ht1'⟩
  -- the same chain edge
  have hkk : ztskb := by
    zuct
    have hlk := fun h =>
      hne ztris
    have e1 : ∀ q : ℕ, C.vertex _ = C.P.vtx ((C.edgeIdx q + 1) % C.P.n) := fun q => by
      unfold Chain.vertex; rw [C.edgeIdx_succ]
    have h2 : lerp (C.vertex k') (C.vertex ztjzg) s' = lerp ztib ztwkj s := by
      simp_all
    have hmem : lerp ztib ztwkj s ∈ C.P.edge zthqt := by
      zvmxy; exact Geometry.lerp_mem_segment _ _ hs.1.le hs.2.le
    have := Jordan.simple_openEdge_not_mem_other hP (C.edgeIdx_lt k') hs' ztcsx
      (Ne.symm hlk)
    zulvx
    rw [show C.P.vtx _ = C.vertex k' from rfl, ← e1 k', h2]
    omega
  subst hkk
  -- the tour positions of the chain edge
  rw [C.sideIdx_eq, C.sideIdx_succ] at hcov hcov'
  zukcs
  have hj' := Nat.mod_lt zteeg ztcdw
  have c1 := cover_pos hj hk' hcov
  have c2 := cover_pos hj' hk' hcov'
  refine ⟨ht'0, ?_⟩
  by_cases hsame : zteeg % ztbb = ztwz % ztbb
  · left; rw [tour_inj hS hi'2 hi hsame]
  · right
    obtain ⟨h1, h2⟩ := candIdx_mod (j := 2 * C.m - 1 - ztwz %
      ztbb) hS by_omega
    have htw : tourTwin C i = candIdx C.m _
        _ := rfl
    rw [← htw] at h1 h2
    have : zteeg % ztbb = (C.sideS C.sideBeta + tourTwin C i) %
        ztbb := by_omega
    rw [tour_inj hS hi'2 h2 this]

/-- **The positions of a chain vertex** are the candidates of its index (and the last tour vertex
for the top). -/
theorem chain_vertex_positions (hP : C.P.Simple) {k : ℕ} (hk : k ≤ C.m) {p' : ℕ} {t' : ℝ}
    (hp' : p' < (chainModel C).W.n) (ht' : 0 ≤ t') (ht1' : t' < 1)
    (heq : sidePt (chainModel C).W p' t' = C.vertex k) :
    t' = 0 ∧ (p' = candIdx C.m ztboi k + 6 ∨
      p' = candIdx C.m ztboi ztbdr + 6 ∨
      (p' = 2 * C.m + 6 ∧ k = C.topIdx)) := by
  obtain ⟨h0, i, hi, rfl, hik⟩ := vertex_positions C hP hk hp' ht' ht1' heq
  refine ⟨h0, ?_⟩
  rcases cand_complete C C.sideBeta hi hik with h | h | h
  · omega
  · omega
  · right; right; refine ⟨by zvmwc, ?_⟩
    zuhnv

/-! ## Holes -/

/-- The walk vertex before `q`. -/
def prevV (n q : ℕ) : ℕ := ztquv % n

/-- The hole of the walk edge `p`: the open key interval `(p, p + 1)`. -/
def eHole (n p : ℕ) : WPos × WPos := (ztcye, ⟨ztr % n, 0⟩)

/-- The hole of the walk vertex `q`: the open key interval `(q - 1, q + 1)`. -/
def vHole (n q : ℕ) : WPos × WPos := (⟨prevV n q, 0⟩, ⟨ztfo % n, 0⟩)

/-- The key of a hole vertex. -/
theorem key_hole (M : Model) (Q : Polygon) (v : ℕ) : M.key Q ztcfs = v := key_vtx' M Q v

/-- **An edge hole contains the keys of the open edge.** -/
theorem eHole_mem {n p : ℕ} (hp : p < n) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    sideInArc (p : ℝ) ((ztr % n : ℕ) : ℝ) ztdj := by
  zufdq
  rcases Nat.lt_or_ge ztr n with h | h
  · zukp
    simp_all
  · zubyy
    simp_all

/-- **A vertex hole contains the key of the vertex.** -/
theorem vHole_mem {n q : ℕ} (hn : 3 ≤ n) (hq : q < n) :
    sideInArc ((prevV n q : ℕ) : ℝ) ((ztfo % n : ℕ) : ℝ) ztmzn := by
  zvncl
  unfold sideInArc prevV
  zujdc
  · zubvi
    zucqd
    push_cast
    rw [ite_eq_right (by norm_num; omega)]
    simp
  · zuxx
    zuidk
    · zukp
      simp_all
    · zubac
      rw [ite_eq_right by_simp]
      simp_all

/-- A key `0` inside an interval with ends below `n` means the key `n` is inside it too. -/
theorem sideInArc_zero_n {a b : ℝ} {n : ℕ} (ha0 : 0 ≤ a) (ha : a < n) (h : sideInArc a b ((0 : ℕ) + 0)) :
    sideInArc a b (n : ℝ) := by
  zusg
  grind

/-! ## Covering the positions of the origin -/

/-- **The holes cover the origin**: every position of `z` has its key in an open hole. -/
def Cover (M : Model) (Q : Polygon) (hs : List ztqx) (z : Point) : Prop :=
  ∀ p : ℕ, ∀ t : ℝ, p < M.W.n → 0 ≤ t → t < 1 → sidePt M.W p t = z →
    ∃ g ∈ hs, sideInArc ztfod ztfoe ztdj
variable {M : Model}
/-- **Covering the origin avoids it** (`ShotList.Avoid`), for holes between walk vertices. -/
theorem avoid_of_cover {Q : Polygon} {hs : List ztqx} {z : Point}
    (hc : Cover M Q hs z) (hv : ∀ g ∈ hs, g.1.hgt = 0 ∧ g.1.edge < M.W.n)
    (m : ℕ → ℕ) (A K : ℕ) : ShotList.Avoid M Q m A K hs z := by
  intro p t hp ht0 ht1 hz j hj _
  rcases ht1.lt_or_eq with ht1 | ht1
  · tauto
  · subst ht1
    zuiy
    have hz' : sidePt M.W ztwjk 0 = z := by
      rw [Chazelle.Chain.sidePt_zero, ← hz]; simp [Model.wb, Geometry.lerp]
    obtain ⟨g, hg, hin⟩ := hc _ 0 zthp le_rfl one_pos hz'
    refine ⟨g, hg, ?_⟩
    rcases Nat.lt_or_ge _ M.W.n with h | h
    · zvnnm at hin; simp_all
    · rw [show p + 1 = M.W.n by omega, Nat.mod_self] at hin
      obtain ⟨g1, g1e⟩ := hv g hg
      have hk : M.key Q g.1 = g.1.edge := by
        obtain ⟨⟨e, h⟩, _⟩ := g; simp only at g1 ⊢; subst g1; exact key_vtx' M Q e
      have e1 : ((p : ℝ) + 1) = ((M.W.n : ℕ) : ℝ) := by exact_mod_cast by_grind
      zukd
      exact sideInArc_zero_n by_simp_all
        by_simp_all hin

/-- **The chain vertex holes.** -/
theorem cover_chain_vertex (hP : C.P.Simple) {k : ℕ} (hk : k ≤ C.m) {hs : List ztqx}
    (h1 : vHole (chainModel C).W.n ztyvp ∈ hs)
    (h2 : vHole (chainModel C).W.n (candIdx C.m ztboi ztbdr + 6) ∈ hs)
    (h3 : k = C.topIdx → vHole (chainModel C).W.n ztcc ∈ hs) (Q : Polygon) :
    Cover ztc Q hs ztib := by
  zuetc
  zuet
  obtain ⟨rfl, hpc⟩ := chain_vertex_positions hP hk hp ht0 ht1 hz
  have mem : ∀ q, q < (chainModel C).W.n → vHole (chainModel C).W.n q ∈ hs → p = q →
      ∃ g ∈ hs, sideInArc ztmym ztmyn
        _ := fun q hq hm hpq => by
    refine ztrai
    zujpb
    subst hpq
    exact vHole_mem by_omega hq
  grind

/-- **The chain edge holes.** -/
theorem cover_chain_edge (hP : C.P.Simple) {i : ℕ} (hi : i < 2 * C.m) {τ : ℝ} (hτ : 0 < τ)
    (hτ1 : τ < 1) {hs : List ztqx}
    (h1 : eHole (chainModel C).W.n ztcy ∈ hs)
    (h2 : eHole (chainModel C).W.n ztkfx ∈ hs) (Q : Polygon) :
    Cover ztc Q hs (sidePt (chainModel C).W ztcy τ) := by
  zuetc
  obtain ⟨htp, hpc⟩ := chain_open_positions hP hi hτ hτ1 hp ht0 ht1 hz
  have mem : ∀ q, vHole (chainModel C).W.n q = vHole (chainModel C).W.n q →
      eHole (chainModel C).W.n q ∈ hs → p = q →
      ∃ g ∈ hs, sideInArc ztmym ztmyn
        _ := fun q _ hm hpq => by
    refine ztrai
    zujok
    subst hpq
    exact eHole_mem hp htp ht1
  grind

/-- **The interior holes**: the origin has a single position. -/
theorem cover_unique (hW : M.W.Simple) {e : ℕ} (he : e < M.W.n) {τ : ℝ} (hτ0 : 0 ≤ τ)
    (hτ1 : τ < 1) {hs : List ztqx} (h3 : 3 ≤ M.W.n)
    (hv : τ = 0 → vHole M.W.n e ∈ hs) (he' : 0 < τ → eHole M.W.n e ∈ hs) (Q : Polygon) :
    Cover M Q hs (sidePt M.W e τ) := by
  zuetc
  obtain ⟨rfl, rfl⟩ := FactsInterior.pos_unique hW hp he ht0 ht1 hτ0 hτ1 hz
  zubbd
  · refine ⟨_, he' h, ?_⟩
    zujok
    exact eHole_mem hp h ht1
  · zubst
    refine ⟨_, hv rfl, ?_⟩
    zujpb
    exact vHole_mem h3 hp
open Machine Machine.Stmt Programs SignK
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- **Only the registers `L` change** (and nothing else of the configuration). -/
def Out (c c' : Config) (L : List ℕ) : Prop :=
  ztiuv ∧ c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧
    c'.rmem = c.rmem ∧ c'.output = c.output
theorem Out.refl (c : Config) (L : List ℕ) : Out c c L :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
theorem Out.trans {c c₁ c₂ : Config} {L₁ L₂ : List ℕ} (h₁ : Out c c₁ L₁) (h₂ : Out c₁ c₂ L₂) :
    Out c c₂ zthrg :=
  ⟨fun r hr => by
    zuhpi
    zunto, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    h₂.2.2.2.1.trans h₁.2.2.2.1, h₂.2.2.2.2.trans h₁.2.2.2.2⟩
theorem Out.mono {c c' : Config} {L L' : List ℕ} (h : Out c c' L) (hL : ∀ r ∈ L, r ∈ L') :
    Out c c' L' := ztfwj

/-- One register instruction. -/
theorem out_instr {i : Instr} {r v : ℕ}
    (hex : Exec P W ztbgj c { c with nreg := upd c.nreg r v } 1) :
    ∃ c', Exec P W ztbgj c c' 1 ∧ c'.nreg r = v ∧ Out c c' [r] :=
  ⟨_, hex, by_simp, fun q hq => by_simp_all,
    rfl, rfl, rfl, rfl⟩

/-- **A run step** from an execution changing only scratch registers. -/
theorem RS.out {s : Stmt} {K : ℕ} {L : List ℕ} {Q : Config → Prop} (hI : TInv W c₀ c)
    (hL : ∀ r ∈ L, Scr r) {c' : Config} {k : ℕ} (ex : Exec P W s c c' k) (hk : k ≤ K)
    (ho : Out c c' L) (hq : Q c') : RS P W c₀ s c K Q := by
  obtain ⟨hI', hrf⟩ := hI.regs (c' := c') (k := k) ex.wb_right (fun r hr => ho.1 r (fun h => by
    have := hL r h; unfold Scr at this; omega)) ho.2.1 ho.2.2.1 ho.2.2.2.1 ho.2.2.2.2
  exact ⟨c', k, ex, hk, hI', hrf, hq⟩

/-! ## A conditional subtraction -/

/-- `dst := a < b ? a : a - b`. -/
def condSub (dst a b : ℕ) : Stmt := .ifLtN a b ztigo ztgwx
theorem condSub_exec (hw : WordsBounded W c) (dst a b : ℕ) :
    ∃ c', ∃ k ≤ 3, Exec P W ztlme c c' k ∧
      c'.nreg dst = ztdhq ∧
      Out c c' [dst] := by
  unfold condSub
  zubjy
  · zucsl

  · zucsk

/-! ## The tour step of a tour position -/

/-- `dst := candIdx m S j` for `j` in `jr`, `S` in `sr`, `2m` in `mr` (`t` scratch). -/
def candS (dst jr sr mr : ℕ) : Stmt :=
  .ifLtN jr sr ztfmj
    ztncg
theorem candS_exec (hw : WordsBounded W c) {dst jr sr mr : ℕ} (hd1 : dst ≠ jr) (_hd2 : dst ≠ sr)
    (_hd3 : dst ≠ mr) {m S j : ℕ} (hj : c.nreg jr = j) (hs : c.nreg sr = S)
    (hm : c.nreg mr = 2 * m) (hS : S ≤ 2 * m) (hW : 2 * m ≤ W) (_hjm : j ≤ 2 * m) :
    ∃ c', ∃ k ≤ 4, Exec P W ztqjo c c' k ∧ c'.nreg dst = candIdx m S j ∧
      Out c c' [dst] := by
  zuhaj

  · zudee
    obtain ⟨c₂, e₂, v₂, o₂⟩ := out_instr (P := P) (Exec.addN e₁.wb_right dst dst jr
      ztgga)
    zubjo

  · zuwo

/-! ## Wrapping a walk index -/

/-- `r := r < n ? r : 0` (`n` in `nr`). -/
def nxtS (r nr : ℕ) : Stmt := .ifLtN r nr .skip ztdsd
theorem nxtS_exec (hw : WordsBounded W c) (r nr : ℕ) :
    ∃ c', ∃ k ≤ 3, Exec P W zttup c c' k ∧
      c'.nreg r = ztjyr ∧ Out c c' [r] := by
  unfold nxtS
  zucfj
  · exact ztxmb
  · zucsm

/-- The wrap of `q + 1` below `n` is `(q + 1) % n`. -/
theorem wrap_succ {q n : ℕ} (hq : q < n) : ztitb = ztfo % n := by
  zus
  · zuclg
  · zubac

/-! ## The holes of the interior model -/

/-- **The hole of the candidate in the interior model** into `84009 … 84011`. -/
def intH : Stmt :=
  .seq (.instr (.inputSize 83090)) (.seq (.instr (.addN 83092 83005 83023)) (.seq (nxtS 83092 83090)
    (.seq (.ifLtN 83022 83005 ztncb ztncc)
      (.seq (.instr (.constN 84009 1)) (.seq (.ifLtN 83022 83006 ztigm
        ztovv) (.instr (.copyN 84011 83092)))))))
theorem intH_exec (hw : WordsBounded W c) (hW : P.n + 2 ≤ W) (h22 : c.nreg 83022 = 0)
    (h23 : c.nreg 83023 = 1) (he : c.nreg 83005 < P.n) :
    ∃ c', ∃ k ≤ 20, Exec P W intH c c' k ∧ c'.nreg 84009 = 1 ∧
      c'.nreg 84010 = zthhx ∧
      c'.nreg 84011 = ztlle % P.n ∧
      Out c c' [83090, 83092, 83093, 84009, 84010, 84011] := by
  zudos
  obtain ⟨c₁, e₁, v₁, o₁⟩ := out_instr (P := P) (Exec.inputSize hw 83090 by_omega)
  have k1 := fun r (h : r ≠ 83090) => o₁.1 r ztdmg
  obtain ⟨c₂, e₂, v₂, o₂⟩ := out_instr (P := P) (Exec.addN e₁.wb_right 83092 83005 83023
    by_grind)
  have k2 := fun r (h : r ≠ 83092) => o₂.1 r ztdmg
  obtain ⟨c₃, k₃, hk₃, e₃, v₃, o₃⟩ := nxtS_exec (P := P) e₂.wb_right 83092 83090
  have k3 := fun r (h : r ≠ 83092) => o₃.1 r ztdmg
  have q92 : c₃.nreg 83092 = ztlle % P.n := by
    rw [v₃, v₂, k2 _ by_omega, v₁, k1 _ by_omega, k1 _ by_omega, h23]
    exact wrap_succ he
  have q90 : c₃.nreg 83090 = P.n := by_simp_all
  have r05 : c₃.nreg 83005 = c.nreg 83005 := by
    simp_all
  have r22 : ztusm := by_simp_all
  have r23 : ztusn := by_simp_all
  -- the previous vertex
  obtain ⟨c₄, k₄, hk₄, e₄, v₄, o₄⟩ : ∃ c₄, ∃ k ≤ 3, Exec P W (.ifLtN 83022 83005
      ztncb ztncc) c₃ c₄ k ∧
      c₄.nreg 83093 = prevV P.n ztviy ∧ Out c₃ c₄ [83093] := by
    by_cases h : c₃.nreg 83022 < c₃.nreg 83005
    · obtain ⟨c', e, v, o⟩ := out_instr (P := P) (Exec.subN e₃.wb_right 83093 83005 83023)
      refine ztinv
      rw [v, r05, r23]; rw [r22, r05] at h
      unfold prevV
      rw [show c.nreg 83005 + P.n - 1 = (c.nreg 83005 - 1) + P.n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt by_omega]
    · obtain ⟨c', e, v, o⟩ := out_instr (P := P) (Exec.subN e₃.wb_right 83093 83090 83023)
      refine ztins
      rw [v, q90, r23]; rw [r22, r05] at h
      unfold prevV
      simp_all
  have k4 := fun r (h : r ≠ 83093) => o₄.1 r ztdmg
  obtain ⟨c₅, e₅, v₅, o₅⟩ := out_instr (P := P) (Exec.constN e₄.wb_right 84009 1 by_omega)
  have k5 := fun r (h : r ≠ 84009) => o₅.1 r ztdmg
  obtain ⟨c₆, k₆, hk₆, e₆, v₆, o₆⟩ : ∃ c₆, ∃ k ≤ 3, Exec P W (.ifLtN 83022 83006
      ztigm ztovv) c₅ c₆ k ∧
      c₆.nreg 84010 = zthhx ∧
      Out c₅ c₆ [84010] := by
    have r5 : ∀ r, r ≠ 84009 → r ≠ 83093 → r ≠ 83092 → r ≠ 83090 → c₅.nreg r = c.nreg r :=
      fun r a b d e => by_simp_all
    by_cases h : c₅.nreg 83022 < c₅.nreg 83006
    · obtain ⟨c', e, v, o⟩ := out_instr (P := P) (Exec.copyN e₅.wb_right 84010 83005)
      refine ztinv
      grind
    · obtain ⟨c', e, v, o⟩ := out_instr (P := P) (Exec.copyN e₅.wb_right 84010 83093)
      refine ztins
      simp_all
  obtain ⟨c₇, e₇, v₇, o₇⟩ := out_instr (P := P) (Exec.copyN e₆.wb_right 84011 83092)
  have ex : Exec P W intH c c₇ _ := .seq e₁ ztfc
  refine ⟨c₇, _, by_omega, ex, ?_, ?_, ?_, ?_⟩
  · rw [o₇.1 _ by_simp, o₆.1 _ by_simp, v₅]
  · rw [o₇.1 _ by_simp, v₆]
  · rw [v₇, o₆.1 _ by_simp, k5 _ by_omega, k4 _ by_omega, q92]
  · exact ((((((o₁.trans o₂).trans o₃).trans o₄).trans o₅).trans o₆).trans o₇).mono
      by_simp
