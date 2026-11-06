module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.GranSize
public import Chazelle.Core.SortRam

/-!
# WP-F, init part 6: the header, the layout and the allocation

* `hdrStmt`: read the header of the normal form (`K, A, R` and the area bases) and the model
  descriptor (kind, chain length), set the constants, and the number of counted edges `sz`
  (`hdr_exec`);
* `mulS`: a product by repeated addition (`mul_exec`);
* `baseStmt`: the products `R D`, `D K`, the bases of the layout `Dm` from the allocator, and the
  allocation of the state area (`base_exec`).
-/

namespace Chazelle.Core

namespace Gran

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-- Read the header. Registers: `r10 = K`, `r11 = A`, `r12 = R`, `r13 = CB`, `r15 = AB`,
`r16 = RB`, `r17 = SB`, `r22 = LB`, `r23` the model kind, `r24` the chain length, `r14 = γ`,
`r19 = 1`, `r20 = 3`, `r21 = 2`, `lr 0`, `lr 1` the handles. -/
def hdrBlock : Stmt := block [.constN 90019 1, .constN 90020 3, .constN 90021 2,
  .copyN 90014 90003, .loadN 90010 90001, .addN 90060 90001 90019, .loadN 90011 90060,
  .addN 90060 90060 90019, .loadN 90012 90060, .addN 90060 90060 90019, .loadN 90013 90060,
  .addN 90060 90060 90019, .loadN 90015 90060, .addN 90060 90060 90019, .loadN 90016 90060,
  .addN 90060 90060 90019, .loadN 90017 90060, .addN 90060 90060 90019, .loadN 90022 90060,
  .loadN 90023 90000, .addN 90060 90000 90020, .loadN 90024 90060, .copyN 50000 90000,
  .copyN 50001 90001]

/-- The number of counted edges: `2 m` (chain) or `n` (interior). -/
def szStmt : Stmt := .ifLtN 90023 90019 (.instr (.addN 90018 90024 90024)) (.instr (.inputSize 90018))

/-- The header. -/
def hdrStmt : Stmt := .seq hdrBlock szStmt

/-- The registers of the header. -/
def Bhdr (r : ℕ) : Bool := decide (90010 ≤ r ∧ r < 90025) || decide (r = 90060) ||
  decide (r = 50000) || decide (r = 50001)

theorem wr_hdrStmt : wr Bhdr hdrStmt = true := by decide

/-- The number of counted edges computed by `szStmt`. -/
def szOf (P : Polygon) (kind m : ℕ) : ℕ := if kind = 0 then 2 * m else P.n

theorem hdr_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {MD B : ℕ}
    (h0 : c.nreg 90000 = MD) (h1 : c.nreg 90001 = B) (hB : B + 7 ≤ W) (hMD : MD + 3 ≤ W)
    (hn : P.n ≤ W) (hm : c.nmem MD = 0 → 2 * c.nmem (MD + 3) ≤ W) :
    ∃ c' k, Exec P W hdrStmt c c' k ∧ k ≤ 30 ∧
      c'.nreg 90010 = c.nmem B ∧ c'.nreg 90011 = c.nmem (B + 1) ∧
      c'.nreg 90012 = c.nmem (B + 2) ∧ c'.nreg 90013 = c.nmem (B + 3) ∧
      c'.nreg 90015 = c.nmem (B + 4) ∧ c'.nreg 90016 = c.nmem (B + 5) ∧
      c'.nreg 90017 = c.nmem (B + 6) ∧ c'.nreg 90022 = c.nmem (B + 7) ∧
      c'.nreg 90023 = c.nmem MD ∧ c'.nreg 90024 = c.nmem (MD + 3) ∧
      c'.nreg 90018 = szOf P (c.nmem MD) (c.nmem (MD + 3)) ∧
      c'.nreg 90014 = c.nreg 90003 ∧ c'.nreg 90019 = 1 ∧ c'.nreg 90020 = 3 ∧
      c'.nreg 90021 = 2 ∧ c'.nreg 50000 = MD ∧ c'.nreg 50001 = B ∧ FrameB Bhdr c c' := by
  suffices hh : ∃ c' k, Exec P W hdrStmt c c' k ∧ k ≤ 30 ∧
      c'.nreg 90010 = c.nmem B ∧ c'.nreg 90011 = c.nmem (B + 1) ∧
      c'.nreg 90012 = c.nmem (B + 2) ∧ c'.nreg 90013 = c.nmem (B + 3) ∧
      c'.nreg 90015 = c.nmem (B + 4) ∧ c'.nreg 90016 = c.nmem (B + 5) ∧
      c'.nreg 90017 = c.nmem (B + 6) ∧ c'.nreg 90022 = c.nmem (B + 7) ∧
      c'.nreg 90023 = c.nmem MD ∧ c'.nreg 90024 = c.nmem (MD + 3) ∧
      c'.nreg 90018 = szOf P (c.nmem MD) (c.nmem (MD + 3)) ∧
      c'.nreg 90014 = c.nreg 90003 ∧ c'.nreg 90019 = 1 ∧ c'.nreg 90020 = 3 ∧
      c'.nreg 90021 = 2 ∧ c'.nreg 50000 = MD ∧ c'.nreg 50001 = B by
    obtain ⟨c', k, e, hk, q⟩ := hh
    exact ⟨c', k, e, hk, q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2.1, q.2.2.2.2.2.1,
      q.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2.2.2.1,
      q.2.2.2.2.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2.2.2.2.2.2.1,
      q.2.2.2.2.2.2.2.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      q.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
      exec_frameB e wr_hdrStmt⟩
  have hW3 : 3 ≤ W := by omega
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W hdrBlock c c₁ k₁ ∧ k₁ = 24 ∧
      (c₁.nreg 90010 = c.nmem B ∧ c₁.nreg 90011 = c.nmem (B + 1) ∧
      c₁.nreg 90012 = c.nmem (B + 2) ∧ c₁.nreg 90013 = c.nmem (B + 3) ∧
      c₁.nreg 90015 = c.nmem (B + 4) ∧ c₁.nreg 90016 = c.nmem (B + 5) ∧
      c₁.nreg 90017 = c.nmem (B + 6) ∧ c₁.nreg 90022 = c.nmem (B + 7) ∧
      c₁.nreg 90023 = c.nmem MD ∧ c₁.nreg 90024 = c.nmem (MD + 3) ∧
      c₁.nreg 90014 = c.nreg 90003 ∧ c₁.nreg 90019 = 1 ∧ c₁.nreg 90020 = 3 ∧
      c₁.nreg 90021 = 2 ∧ c₁.nreg 50000 = MD ∧ c₁.nreg 50001 = B ∧ c₁.nmem = c.nmem) := by
    unfold hdrBlock
    exec_block
    all_goals try omega
    all_goals try (config_simp; rw [h1]; omega)
    all_goals try (config_simp; rw [h0]; omega)
    refine ⟨rfl, ?_⟩
    config_simp
    rw [h0, h1]
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, rfl, rfl⟩ <;> ring_nf
  obtain ⟨q10, q11, q12, q13, q15, q16, q17, q22, q23, q24, q14, q19, q20, q21, q50, q51,
    qm⟩ := q
  have w₁ := e₁.wb_right
  by_cases hk : c.nmem MD = 0
  · have t : c₁.nreg 90023 < c₁.nreg 90019 := by rw [q23, q19, hk]; omega
    have e₂ := Exec.addN (P := P) w₁ 90018 90024 90024 (by rw [q24]; have := hm hk; omega)
    refine ⟨_, _, .seq e₁ (.ifLtN_true t e₂), by omega, ?_⟩
    config_simp
    refine ⟨q10, q11, q12, q13, q15, q16, q17, q22, q23, q24, ?_, q14, q19, q20, q21, q50, q51⟩
    rw [q24]; unfold szOf; rw [ite_eq_left hk]; ring
  · have t : ¬ c₁.nreg 90023 < c₁.nreg 90019 := by rw [q23, q19]; omega
    have e₂ := Exec.inputSize (P := P) w₁ 90018 hn
    refine ⟨_, _, .seq e₁ (.ifLtN_false t e₂), by omega, ?_⟩
    config_simp
    refine ⟨q10, q11, q12, q13, q15, q16, q17, q22, q23, q24, ?_, q14, q19, q20, q21, q50, q51⟩
    unfold szOf; rw [ite_eq_right hk]

/-! ## Products -/

/-- `dst := r a * r b` (counter `cnt`). -/
def mulS (dst a b cnt : ℕ) : Stmt :=
  .seq (block [.constN dst 0, .constN cnt 0])
    (.whileLtN cnt a (block [.addN dst dst b, .addN cnt cnt 90019]))

theorem mul_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {dst a b cnt : ℕ}
    (h1 : dst ≠ cnt) (h2 : dst ≠ a) (h3 : dst ≠ b) (h4 : cnt ≠ a) (h5 : cnt ≠ b)
    (h6 : dst ≠ 90019) (h7 : cnt ≠ 90019) (h19 : c.nreg 90019 = 1)
    (hW : c.nreg a * c.nreg b ≤ W) (ha : c.nreg a ≤ W) :
    ∃ c' k, Exec P W (mulS dst a b cnt) c c' k ∧ k ≤ 4 * c.nreg a + 4 ∧
      c'.nreg dst = c.nreg a * c.nreg b ∧
      (∀ r, r ≠ dst → r ≠ cnt → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      FrameB (fun r => decide (r = dst) || decide (r = cnt)) c c' := by
  suffices hh : ∃ c' k, Exec P W (mulS dst a b cnt) c c' k ∧ k ≤ 4 * c.nreg a + 4 ∧
      c'.nreg dst = c.nreg a * c.nreg b by
    obtain ⟨c', k, e, hk, hd⟩ := hh
    have F := exec_frameB e (B := fun r => decide (r = dst) || decide (r = cnt))
      (by simp [mulS, wr, block, wrOK])
    exact ⟨c', k, e, hk, hd, fun r a1 a2 => F.1 r (by simp_all), F.2.2.1, F⟩
  have hW0 : 0 ≤ W := Nat.zero_le _
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.constN dst 0, .constN cnt 0]) c c₁ k₁ ∧
      k₁ = 2 ∧ (c₁.nreg dst = 0 ∧ c₁.nreg cnt = 0 ∧
        ∀ r, r ≠ dst → r ≠ cnt → c₁.nreg r = c.nreg r) := by
    refine spec_step (Exec.constN hw dst 0 hW0) fun hw₁ => ?_
    refine spec_step (Exec.constN hw₁ cnt 0 hW0) fun hw₂ => ?_
    refine spec_nil hw₂ ⟨rfl, by simp_all, by simp [upd], fun r a1 a2 => by simp_all⟩
  obtain ⟨q1, q2, qr⟩ := q
  obtain ⟨c', k, e, ⟨hw', hc', hd', hr'⟩, hx, hk⟩ := Exec.whileLtN_bounded (P := P) (a := cnt)
    (b := a) (body := block [.addN dst dst b, .addN cnt cnt 90019])
    (fun d => WordsBounded W d ∧ d.nreg cnt ≤ c.nreg a ∧ d.nreg dst = d.nreg cnt * c.nreg b ∧
      ∀ r, r ≠ dst → r ≠ cnt → d.nreg r = c.nreg r)
    (fun d => c.nreg a - d.nreg cnt) 2 (fun _ h => h.1)
    (fun d ⟨hwd, hle, hdd, hrd⟩ ht => by
      rw [hrd a (Ne.symm h2) (Ne.symm h4)] at ht
      have hb : d.nreg b = c.nreg b := hrd b (Ne.symm h3) (Ne.symm h5)
      have h19' : d.nreg 90019 = 1 := by grind
      have hmul : (d.nreg cnt + 1) * c.nreg b ≤ c.nreg a * c.nreg b :=
        Nat.mul_le_mul_right _ (by omega)
      have hsum : d.nreg dst + d.nreg b ≤ W := by
        grind
      refine spec_step (Exec.addN hwd dst dst b hsum) fun hw₁ => ?_
      refine spec_step (Exec.addN hw₁ cnt cnt 90019 (by
        grind [upd]))
        fun hw₂ => ?_
      refine spec_nil hw₂ ⟨⟨hw₂, ?_, ?_, fun r a1 a2 => ?_⟩, by omega, ?_⟩
      · grind [upd]
      all_goals (grind [upd]))
    ⟨e₁.wb_right, by omega, by simp_all, qr⟩
  rw [hr' a (Ne.symm h2) (Ne.symm h4)] at hx
  have hfull : c'.nreg cnt = c.nreg a := by omega
  refine ⟨c', _, .seq e₁ e, ?_, by simp_all⟩
  omega

/-! ## The layout -/

/-- The products, the bases and the allocation. -/
def baseBlock : Stmt := block [.copyN 90030 9999, .addN 90031 90030 90010,
  .addN 90032 90031 90010, .addN 90033 90032 90010, .addN 90034 90033 90010,
  .addN 90035 90034 90010, .addN 90036 90035 90012, .addN 90037 90036 90012,
  .addN 90027 90037 90012, .addN 90038 90027 90025, .addN 90039 90038 90011,
  .addN 90040 90039 90011, .addN 90041 90040 90011, .addN 90042 90041 90011,
  .addN 90043 90042 90011, .addN 90044 90043 90010, .addN 90044 90044 90026,
  .addN 90028 90044 90002, .addN 90028 90028 90019, .addN 90029 90028 90010,
  .addN 90029 90029 90010, .addN 90029 90029 90010]

/-- The allocation loop. -/
def allocLoop : Stmt := .whileLtN 9999 90029 (.instr (.addN 9999 9999 90019))

/-- Products, bases, allocation. -/
def baseStmt : Stmt :=
  .seq (mulS 90025 90012 90002 90061) (.seq (mulS 90026 90002 90010 90061)
    (.seq baseBlock allocLoop))

/-- The registers of `baseStmt`. -/
def Bbase (r : ℕ) : Bool := decide (90025 ≤ r ∧ r < 90062) || decide (r = 9999)

theorem wrS_baseStmt : wrS Bbase baseStmt = true := by decide

/-- The dimensions of the layout. -/
def dmOf (K A R D b0 : ℕ) : Dm := ⟨K, A, R, D, b0⟩

/-- The base registers of the layout. -/
structure Bases (c : Config) (d : Dm) : Prop where
  bLive : c.nreg 90030 = d.b0
  bS0 : c.nreg 90031 = d.b0 + d.oS0
  bS1 : c.nreg 90032 = d.b0 + d.oS1
  bNd0 : c.nreg 90033 = d.b0 + d.oNd0
  bNd1 : c.nreg 90034 = d.b0 + d.oNd1
  bDeg : c.nreg 90035 = d.b0 + d.oDeg
  bWt : c.nreg 90036 = d.b0 + d.oWt
  bExb : c.nreg 90037 = d.b0 + d.oExb
  bCnt : c.nreg 90038 = d.b0 + d.oCnt
  bNxt : c.nreg 90039 = d.b0 + d.oNxt
  bPrv : c.nreg 90040 = d.b0 + d.oPrv
  bEg : c.nreg 90041 = d.b0 + d.oEg
  bPz : c.nreg 90042 = d.b0 + d.oPz
  bStk : c.nreg 90043 = d.b0 + d.oStk
  bTmp : c.nreg 90044 = d.b0 + d.oTmp

theorem Bases.frame {c c' : Config} {d : Dm} (h : Bases c d)
    (hr : ∀ r, 90030 ≤ r → r < 90045 → c'.nreg r = c.nreg r) : Bases c' d := by
  core_grind

/-- The constants and the bases give `Cst`. -/
theorem Cst.of_bases {c : Config} {E : Env} {d : Dm} (h : Bases c d) (hγ : c.nreg 90014 = E.γ)
    (hsz : c.nreg 90018 = E.sz) (h1 : c.nreg 90019 = 1) (h3 : c.nreg 90020 = 3)
    (h2 : c.nreg 90021 = 2) : Cst c E d :=
  ⟨hγ, hsz, h1, h3, h2, h.bLive, h.bS0, h.bS1, h.bNd0, h.bNd1, h.bDeg, h.bWt, h.bExb, h.bCnt,
    h.bNxt, h.bPrv, h.bEg, h.bPz, h.bStk, h.bTmp⟩

theorem dmOf_oEnd (K A R D b0 : ℕ) : (dmOf K A R D b0).oEnd =
    9 * K + 3 * R + R * D + 5 * A + D * K + D + 1 := by
  simp only [dmOf, Dm.oEnd, Dm.oList, Dm.oTmp, Dm.cap, Dm.oStk, Dm.oPz, Dm.oEg, Dm.oPrv, Dm.oNxt,
    Dm.oCnt, Dm.oEx]
  ring

set_option maxHeartbeats 4000000 in
/-- The bases. -/
theorem baseBlock_exec {P : Polygon} {W : ℕ} (c₂ : Config) (w₂ : WordsBounded W c₂)
    {K A R D b0 : ℕ} (g10 : c₂.nreg 90010 = K) (g11 : c₂.nreg 90011 = A)
    (g12 : c₂.nreg 90012 = R) (g02 : c₂.nreg 90002 = D) (g19 : c₂.nreg 90019 = 1)
    (g25 : c₂.nreg 90025 = R * D) (d₂ : c₂.nreg 90026 = D * K) (gA : c₂.nreg 9999 = b0)
    (hroom : b0 + (9 * K + 3 * R + R * D + 5 * A + D * K + D + 1) ≤ W) :
    ∃ c₃ k₃, Exec P W baseBlock c₂ c₃ k₃ ∧ k₃ = 22 ∧
      (Bases c₃ (dmOf K A R D b0) ∧ c₃.nreg 90027 = b0 + (dmOf K A R D b0).oEx ∧
        c₃.nreg 90028 = b0 + (dmOf K A R D b0).oList ∧
        c₃.nreg 90029 = b0 + (dmOf K A R D b0).oEnd) := by
  have hE := dmOf_oEnd K A R D b0
  have o0 : (dmOf K A R D b0).b0 = b0 := rfl
  have o1 : (dmOf K A R D b0).oS0 = K := rfl
  have o2 : (dmOf K A R D b0).oS1 = 2 * K := rfl
  have o3 : (dmOf K A R D b0).oNd0 = 3 * K := rfl
  have o4 : (dmOf K A R D b0).oNd1 = 4 * K := rfl
  have o5 : (dmOf K A R D b0).oDeg = 5 * K := rfl
  have o6 : (dmOf K A R D b0).oWt = 5 * K + R := rfl
  have o7 : (dmOf K A R D b0).oExb = 5 * K + 2 * R := rfl
  have o8 : (dmOf K A R D b0).oEx = 5 * K + 3 * R := rfl
  have o9 : (dmOf K A R D b0).oCnt = 5 * K + 3 * R + R * D := rfl
  have o10 : (dmOf K A R D b0).oNxt = 5 * K + 3 * R + R * D + A := rfl
  have o11 : (dmOf K A R D b0).oPrv = 5 * K + 3 * R + R * D + A + A := rfl
  have o12 : (dmOf K A R D b0).oEg = 5 * K + 3 * R + R * D + A + A + A := rfl
  have o13 : (dmOf K A R D b0).oPz = 5 * K + 3 * R + R * D + A + A + A + A := rfl
  have o14 : (dmOf K A R D b0).oStk = 5 * K + 3 * R + R * D + A + A + A + A + A := rfl
  have o15 : (dmOf K A R D b0).oTmp = 5 * K + 3 * R + R * D + A + A + A + A + A + (K + D * K) :=
    rfl
  have o16 : (dmOf K A R D b0).oList =
      5 * K + 3 * R + R * D + A + A + A + A + A + (K + D * K) + D + 1 := rfl
  unfold baseBlock
  exec_block
  all_goals try (config_simp; omega)
  refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
    config_simp <;> omega 


theorem base_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {K A R D : ℕ}
    (h10 : c.nreg 90010 = K) (h11 : c.nreg 90011 = A) (h12 : c.nreg 90012 = R)
    (h02 : c.nreg 90002 = D) (h19 : c.nreg 90019 = 1)
    (hroom : c.nreg ALLOC + (dmOf K A R D (c.nreg ALLOC)).oEnd ≤ W) :
    ∃ c' k, Exec P W baseStmt c c' k ∧
      k ≤ 4 * R + 4 * D + 32 + 3 * (dmOf K A R D (c.nreg ALLOC)).oEnd ∧
      Bases c' (dmOf K A R D (c.nreg ALLOC)) ∧
      c'.nreg ALLOC = c.nreg ALLOC + (dmOf K A R D (c.nreg ALLOC)).oEnd ∧
      c'.nreg 90027 = c.nreg ALLOC + (dmOf K A R D (c.nreg ALLOC)).oEx ∧
      c'.nreg 90028 = c.nreg ALLOC + (dmOf K A R D (c.nreg ALLOC)).oList ∧
      c'.nreg 90026 = D * K ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k ∧
      (∀ r, (r < 90025 ∨ 90045 ≤ r) → r ≠ 90061 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ FrameS Bbase c c' := by
  set b0 := c.nreg ALLOC with hb0
  have hE := dmOf_oEnd K A R D b0
  rw [hE] at hroom ⊢
  have hRD : R * D ≤ W := by omega
  have hDK : D * K ≤ W := by omega
  -- the products
  obtain ⟨c₁, k₁, e₁, hk₁, d₁, r₁, m₁, F₁⟩ := mul_exec (P := P) (dst := 90025) (a := 90012)
    (b := 90002) (cnt := 90061) c hw (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) h19 (by simp_all) (by omega)
  rw [h12, h02] at d₁
  rw [h12] at hk₁
  obtain ⟨c₂, k₂, e₂, hk₂, d₂, r₂, m₂, F₂⟩ := mul_exec (P := P) (dst := 90026) (a := 90002)
    (b := 90010) (cnt := 90061) c₁ e₁.wb_right (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by simp_all)
    (by simp_all)
    (by grind)
  rw [r₁ _ (by decide) (by decide), r₁ _ (by decide) (by decide), h02, h10] at d₂
  rw [r₁ _ (by decide) (by decide), h02] at hk₂
  have g : ∀ r, r ≠ 90025 → r ≠ 90026 → r ≠ 90061 → c₂.nreg r = c.nreg r := fun r a1 a2 a3 => by
    simp_all
  have w₂ := e₂.wb_right
  have g10 : c₂.nreg 90010 = K := by grind
  have g11 : c₂.nreg 90011 = A := by grind
  have g12 : c₂.nreg 90012 = R := by grind
  have g02 : c₂.nreg 90002 = D := by grind
  have g19 : c₂.nreg 90019 = 1 := by grind
  have g25 : c₂.nreg 90025 = R * D := by grind
  have gA : c₂.nreg 9999 = b0 := by rw [g _ (by decide) (by decide) (by decide)]; rfl
  -- the bases
  obtain ⟨c₃, k₃, e₃, hk₃, q⟩ := baseBlock_exec (P := P) c₂ w₂ g10 g11 g12 g02 g19 g25 d₂ gA
    hroom
  have F₃ := exec_frameB e₃ (B := fun r => decide (90027 ≤ r ∧ r < 90045))
    (by simp [baseBlock, wr, block, wrOK])
  have r₃ : ∀ r, (r < 90025 ∨ 90045 ≤ r) → c₃.nreg r = c₂.nreg r := fun r hr =>
    F₃.1 r (by simp; omega)
  have m₃ : c₃.nmem = c₂.nmem := F₃.2.2.1
  obtain ⟨B₃, q27, q28, q29⟩ := q
  have w₃ := e₃.wb_right
  -- the allocation
  have t29 : c₃.nreg 90029 = b0 + (dmOf K A R D b0).oEnd := q29
  rw [hE] at t29
  obtain ⟨c₄, k₄, e₄, ⟨hw₄, hle₄, hr₄, hm₄, hrr₄, hrm₄, ho₄⟩, hx, hk₄, hlb⟩ :=
    SortR.whileLtN_potential_lb (P := P) (W := W) (a := 9999) (b := 90029)
    (body := .instr (.addN 9999 9999 90019))
    (fun d => WordsBounded W d ∧ d.nreg 9999 ≤ c₃.nreg 90029 ∧
      (∀ r, r ≠ 9999 → d.nreg r = c₃.nreg r) ∧ d.nmem = c₃.nmem ∧ d.rreg = c₃.rreg ∧
      d.rmem = c₃.rmem ∧ d.output = c₃.output)
    (fun d => 3 * (c₃.nreg 90029 - d.nreg 9999)) (fun d => d.nreg 9999) (fun d h => h.1)
    (fun d ⟨hwd, hled, hrd, hmd, hrrd, hrmd, hod⟩ ht => by
      have h1d : d.nreg 90019 = 1 := by
        grind
      have h29 : d.nreg 90029 = c₃.nreg 90029 := hrd _ (by decide)
      rw [h29] at ht
      refine spec_instr (Exec.addN hwd _ _ _ (by omega)) fun hw2 => ?_
      refine ⟨⟨hw2, by config_simp; omega, fun r hr => ?_, hmd, hrrd, hrmd, hod⟩, ?_, ?_⟩
      · config_simp; rw [Machine.upd_other _ _ _ hr]; grind
      · config_simp; omega
      · config_simp; rw [h1d])
    ⟨w₃, by grind, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  have h29 : c₄.nreg 90029 = c₃.nreg 90029 := hr₄ _ (by decide)
  rw [h29] at hx
  refine ⟨c₄, _, .seq e₁ (.seq e₂ (.seq e₃ e₄)), ?_, B₃.frame fun r a1 a2 => hr₄ r (by omega),
    ?_, ?_, ?_, ?_, ?_, fun r hr a1 a2 => ?_, ?_, exec_frameS (.seq e₁ (.seq e₂ (.seq e₃ e₄)))
      wrS_baseStmt⟩
  · grind
  · have h1 : c₄.nreg 9999 ≤ c₃.nreg 90029 := hle₄
    rw [t29] at h1 hx
    show c₄.nreg 9999 = _
    grind
  · grind
  · grind
  · rw [hr₄ _ (by decide), F₃.1 _ (by decide), d₂]
  · rw [r₃ 9999 (by left; decide), gA] at hlb
    show c₄.nreg 9999 ≤ b0 + _
    omega
  · rw [hr₄ r a2, r₃ r hr, g r (by omega) (by omega) a1]
  grind

end

end Gran

end Chazelle.Core
