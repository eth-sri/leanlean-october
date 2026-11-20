module
public import Chazelle.Programs.Address
public import Chazelle.Programs.Verification

public import Chazelle.Core.SweepEvStopFinS0
public import Chazelle.Core.SweepEvStopRF

/-!
# The sweep (WP-D), stage 2: the counterpart of a stretch attachment (mathematics, helpers)

* `strD_eq`, `strQ_eq`, `strMod_eq`: the RAM values of the offset `d`, of `dq d` and of the
  reduction modulo `n₂`;
* `str_param`: corresponding positions of the walk of `C` and of `C₂` along the right stretch
  have the same parameter at the same height code;
* `slfAdd_irs`, `slfSub_irs`: one-register run steps.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Chain (SideAttach sidePt)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## Values -/

theorem strD_eq {n g e : ℕ} (hg : g < n) (he : e < n) :
    (if e < g then e + n - g else e - g) = dOf n g e := by
  unfold dOf
  split_ifs with h
  · frame_simp [Nat.mod_eq_of_lt]
  · rw [show e + n - g = (e - g) + n by omega, Nat.add_mod_right, guarded Nat.mod_eq_of_lt]

theorem strMod_eq {n s : ℕ} (hs : s < 2 * n) : (if s < n then s else s - n) = s % n := by
  split_ifs with h
  · exact (Nat.mod_eq_of_lt h).symm
  · frame_simp [Nat.mod_eq_sub_mod, Nat.mod_eq_of_lt]

/-- **Corresponding positions along the right stretch** have the same parameter. -/
theorem str_param {J : Merge.Junction} (hP : J.P.Simple) {d : ℕ} (hd : d < Lst J) (Q : Polygon)
    (h : ℕ) :
    (chainModel J.whole).param Q ⟨(gW J + d) % (chainModel J.whole).W.n, h⟩ =
      (chainModel J.right).param Q ⟨cpA J d, h⟩ := by
  have hS := sideConvR J hP
  have hc := hS.corr d hd
  obtain ⟨h1, h2⟩ := wab_of_sidePt hc
  exact (param_pos_of_wab (M := chainModel J.whole) (M' := chainModel J.right) h1 h2 Q h).1

/-! ## One-register steps -/

theorem slfAdd_irs (hI : IInv W c₀ c) {r a b : ℕ} (hr : 240700 ≤ r ∧ r < 250000)
    (hv : c.nreg a + c.nreg b ≤ W) :
    IRS P W c₀ (.instr (.addN r a b)) c 1 (fun c' => c'.nreg r = c.nreg a + c.nreg b ∧
      (∀ q, q ≠ r → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  refine (IRS.instr1 (i := .addN r a b) hI ⟨iscr_sw hr.1 hr.2, hv⟩).mono le_rfl ?_
  rintro c' rfl
  refine ⟨by simp [regI, upd], fun q hq => by simp [regI, upd, hq], rfl⟩

theorem slfSub_irs (hI : IInv W c₀ c) {r a b : ℕ} (hr : 240700 ≤ r ∧ r < 250000) :
    IRS P W c₀ (.instr (.subN r a b)) c 1 (fun c' => c'.nreg r = c.nreg a - c.nreg b ∧
      (∀ q, q ≠ r → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  refine (IRS.instr1 (i := .subN r a b) hI (iscr_sw hr.1 hr.2)).mono le_rfl ?_
  rintro c' rfl
  refine ⟨by simp [regI, upd], fun q hq => by simp [regI, upd, hq], rfl⟩

/-! ## The arithmetic of the counterpart -/

def sflN : ℕ := sw 4118
def slD' : ℕ := sw 4120
def slQ' : ℕ := sw 4121
def slA : ℕ := sw 4122
def slD1 : ℕ := sw 4123
def slQ1 : ℕ := sw 4124
def slB : ℕ := sw 4125

/-- The offset `d` of the position. -/
def slDS : Stmt :=
  .ifLtN slfSE cGW (.seq (.instr (.addN slD' slfSE (sw 35))) (.instr (.subN slD' slD' cGW)))
    (.instr (.subN slD' slfSE cGW))

/-- `dq` of the offset in `src`. -/
def slQS (src dst : ℕ) : Stmt :=
  .ifLtN src (sw 42) (.instr (.copyN dst src)) (.instr (.addN dst src (sw 44)))

/-- The reduction modulo `n₂`. -/
def slModS (r : ℕ) : Stmt := .ifLtN r (sw 34) .skip (.instr (.subN r r (sw 34)))

/-- The positions for the faced regions. -/
def slFS : Stmt :=
  .ifLtN K0 slfSH (.seq (.instr (.copyN fqE slA)) (.instr (.copyN fqH slfSH)))
    (.seq (.instr (.copyN fqE slB)) (.instr (.constN fqH 0)))

/-- **The counterpart positions.** -/
def slAr : Stmt :=
  .seq slDS (.seq (slQS slD' slQ') (.seq (.instr (.subN slD1 slD' K1)) (.seq (slQS slD1 slQ1)
    (.seq (.instr (.addN slA (sw 41) slQ')) (.seq (.instr (.addN slB (sw 41) slQ1))
    (.seq (.instr (.addN slB slB K1)) (.seq (slModS slA) (.seq (slModS slB)
    (.seq (.instr (.copyN fpE slA)) (.seq (.instr (.copyN fpH slfSH)) slFS))))))))))

/-- The registers `slAr` writes. -/
def SlArW (q : ℕ) : Prop := (sw 4110 ≤ q ∧ q ≤ sw 4113) ∨ (sw 4120 ≤ q ∧ q ≤ sw 4125)

/-- A step keeping the registers outside `SlArW` and the memory. -/
def SlKp (c c' : Config) : Prop := (∀ q, ¬ SlArW q → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem

theorem slQS_irs (hI : IInv W c₀ c) {src dst : ℕ}
    (hdr : 240700 ≤ dst ∧ dst < 250000) (hv : c.nreg src + c.nreg (sw 44) ≤ W) :
    IRS P W c₀ (slQS src dst) c 3 (fun c' =>
      c'.nreg dst = dq (c.nreg (sw 42)) (c.nreg (sw 44)) (c.nreg src) ∧
      (∀ q, q ≠ dst → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  unfold slQS
  refine IRS.ite (fun h => ?_) (fun h => ?_)
  · refine (copy1_irs hI hdr).mono le_rfl ?_
    simp_all [dq]
  · refine (slfAdd_irs hI hdr hv).mono (by norm_num) ?_
    simp_all [dq]

theorem slModS_irs (hI : IInv W c₀ c) {r : ℕ} (hdr : 240700 ≤ r ∧ r < 250000)
    (hs : c.nreg r < 2 * c.nreg (sw 34)) :
    IRS P W c₀ (slModS r) c 3 (fun c' => c'.nreg r = c.nreg r % c.nreg (sw 34) ∧
      (∀ q, q ≠ r → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  unfold slModS
  refine IRS.ite (fun h => ?_) (fun h => ?_)
  · refine IRS.skip hI ⟨?_, fun _ _ => rfl, rfl⟩
    exact (Nat.mod_eq_of_lt h).symm
  · refine (slfSub_irs hI hdr).mono (by norm_num) ?_
    rintro c' ⟨a1, a2, a3⟩
    refine ⟨?_, a2, a3⟩
    rw [a1, ← strMod_eq hs, ite_eq_right h]

/-- Register disequalities of the counterpart arithmetic. -/
local macro "rne" : tactic => `(tactic| (simp only [slfSE, slfSH, slD', slQ', slA, slD1, slQ1,
  slB, fpE, fpH, fqE, fqH, cGW, K0, K1, sflN, sw, SlArW, ALLOC] at * <;> omega))

set_option maxHeartbeats 2000000 in
/-- **The counterpart positions** as a run step. -/
theorem slAr_irs (hI : IInv W c₀ c) {n g g' n₂ : ℕ} (hE : c.nreg slfSE < n)
    (hn : c.nreg (sw 35) = n) (hg : c.nreg cGW = g) (hgn : g < n) (hg' : c.nreg (sw 41) = g')
    (hn2 : c.nreg (sw 34) = n₂) (hg'n : g' < n₂) (hK0 : c.nreg K0 = 0) (hK1 : c.nreg K1 = 1)
    (hq : dq (c.nreg (sw 42)) (c.nreg (sw 44)) (dOf n g (c.nreg slfSE)) < n₂)
    (hq1 : dq (c.nreg (sw 42)) (c.nreg (sw 44)) (dOf n g (c.nreg slfSE) - 1) < n₂)
    (hW : 2 * n ≤ W) (hn₂n : n₂ ≤ n) (hδ : c.nreg (sw 44) ≤ n₂) :
    IRS P W c₀ slAr c 26 (fun c' =>
      c'.nreg fpE = (g' + dq (c.nreg (sw 42)) (c.nreg (sw 44)) (dOf n g (c.nreg slfSE))) % n₂ ∧
      c'.nreg fpH = c.nreg slfSH ∧
      c'.nreg fqE = (if c.nreg slfSH = 0 then
        (g' + (dq (c.nreg (sw 42)) (c.nreg (sw 44)) (dOf n g (c.nreg slfSE) - 1) + 1)) % n₂ else
        (g' + dq (c.nreg (sw 42)) (c.nreg (sw 44)) (dOf n g (c.nreg slfSE))) % n₂) ∧
      c'.nreg fqH = (if c.nreg slfSH = 0 then 0 else c.nreg slfSH) ∧ SlKp c c') := by
  set d := dOf n g (c.nreg slfSE) with hd
  set L1 := c.nreg (sw 42) with hL1
  set δ := c.nreg (sw 44) with hδd
  have hdn : d < n := dOf_lt (by omega) _ _
  unfold slAr
  -- 1. the offset
  have s1 : IRS P W c₀ slDS c 4 (fun c' => c'.nreg slD' = d ∧
      (∀ q, q ≠ slD' → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
    unfold slDS
    refine IRS.ite (fun h => ?_) (fun h => ?_)
    · refine IRS.seq (K₁ := 1) (K₂ := 1) (slfAdd_irs hI (by rne) (by rw [hn]; omega)) ?_
      rintro c₁ hI₁ - - ⟨a1, a2, a3⟩
      refine (slfSub_irs hI₁ (by rne)).mono le_rfl ?_
      rintro c' ⟨b1, b2, b3⟩
      refine ⟨?_, fun q hq => by rw [b2 q hq, a2 q hq], by rw [b3, a3]⟩
      rw [b1, a1, a2 _ (by rne), hn, hg, hd, ← strD_eq hgn hE, ite_eq_left (by rw [← hg]; exact h)]
    · refine (slfSub_irs hI (by rne)).mono (by norm_num) ?_
      rintro c' ⟨b1, b2, b3⟩
      refine ⟨?_, b2, b3⟩
      rw [b1, hg, hd, ← strD_eq hgn hE, ite_eq_right (by rw [← hg]; exact h)]
  refine IRS.seq (K₁ := 4) (K₂ := 22) s1 ?_
  rintro c₁ hI₁ - - ⟨v1, k1, m1⟩
  have e1 : ∀ q, ¬ SlArW q → c₁.nreg q = c.nreg q := fun q hq => k1 q (by rne)
  -- 2. `dq d`
  refine IRS.seq (K₁ := 3) (K₂ := 19) (slQS_irs (src := slD') (dst := slQ') hI₁ (by rne)
    (by rw [v1, e1 _ (by rne)]; omega)) ?_
  rintro c₂ hI₂ - - ⟨v2, k2, m2⟩
  rw [v1, at_index e1 _, at_index e1 _] at v2
  have e2 : ∀ q, ¬ SlArW q → c₂.nreg q = c.nreg q := fun q hq => (at_index k2 q).trans (e1 q hq)
  -- 3. `d - 1`
  refine IRS.seq (K₁ := 1) (K₂ := 18) (guarded (slfSub_irs (r := slD1) (a := slD') (b := K1) hI₂)) ?_
  rintro c₃ hI₃ - - ⟨v3, k3, m3⟩
  rw [at_index k2 _, v1, at_index e2 _, hK1] at v3
  have e3 : ∀ q, ¬ SlArW q → c₃.nreg q = c.nreg q := fun q hq => (at_index k3 q).trans (e2 q hq)
  have c3Q : c₃.nreg slQ' = dq L1 δ d := by rw [at_index k3 _, v2]
  -- 4. `dq (d - 1)`
  refine IRS.seq (K₁ := 3) (K₂ := 15) (slQS_irs (src := slD1) (dst := slQ1) hI₃ (by rne)
    (by rw [v3, e3 _ (by rne)]; omega)) ?_
  rintro c₄ hI₄ - - ⟨v4, k4, m4⟩
  rw [v3, at_index e3 _, at_index e3 _] at v4
  have e4 : ∀ q, ¬ SlArW q → c₄.nreg q = c.nreg q := fun q hq => (at_index k4 q).trans (e3 q hq)
  have c4Q : c₄.nreg slQ' = dq L1 δ d := by rw [at_index k4 _, c3Q]
  -- 5. the sums
  refine IRS.seq (K₁ := 1) (K₂ := 14) (slfAdd_irs (r := slA) (a := sw 41) (b := slQ') hI₄ (by rne)
    (by rw [e4 _ (by rne), hg', c4Q]; omega)) ?_
  rintro c₅ hI₅ - - ⟨v5, k5, m5⟩
  rw [at_index e4 _, hg', c4Q] at v5
  have e5 : ∀ q, ¬ SlArW q → c₅.nreg q = c.nreg q := fun q hq => (at_index k5 q).trans (e4 q hq)
  have c5Q1 : c₅.nreg slQ1 = dq L1 δ (d - 1) := by rw [at_index k5 _, v4]
  refine IRS.seq (K₁ := 1) (K₂ := 13) (slfAdd_irs (r := slB) (a := sw 41) (b := slQ1) hI₅ (by rne)
    (by rw [e5 _ (by rne), hg', c5Q1]; omega)) ?_
  rintro c₆ hI₆ - - ⟨v6, k6, m6⟩
  rw [at_index e5 _, hg', c5Q1] at v6
  have e6 : ∀ q, ¬ SlArW q → c₆.nreg q = c.nreg q := fun q hq => (at_index k6 q).trans (e5 q hq)
  have c6A : c₆.nreg slA = g' + dq L1 δ d := by rw [at_index k6 _, v5]
  refine IRS.seq (K₁ := 1) (K₂ := 12) (slfAdd_irs (r := slB) (a := slB) (b := K1) hI₆ (by rne)
    (by rw [v6, e6 _ (by rne), hK1]; omega)) ?_
  rintro c₇ hI₇ - - ⟨v7, k7, m7⟩
  rw [v6, at_index e6 _, hK1] at v7
  have e7 : ∀ q, ¬ SlArW q → c₇.nreg q = c.nreg q := fun q hq => (at_index k7 q).trans (e6 q hq)
  have c7A : c₇.nreg slA = g' + dq L1 δ d := by rw [at_index k7 _, c6A]
  -- 6. the reductions
  have hn2' : c₇.nreg (sw 34) = n₂ := by rw [at_index e7 _, hn2]
  refine IRS.seq (K₁ := 3) (K₂ := 9) (guarded (slModS_irs (r := slA) hI₇)) ?_
  rintro c₈ hI₈ - - ⟨v8, k8, m8⟩
  rw [c7A, hn2'] at v8
  have e8 : ∀ q, ¬ SlArW q → c₈.nreg q = c.nreg q := fun q hq => (at_index k8 q).trans (e7 q hq)
  have c8B : c₈.nreg slB = g' + dq L1 δ (d - 1) + 1 := by rw [at_index k8 _, v7]
  have hn2'' : c₈.nreg (sw 34) = n₂ := by rw [at_index e8 _, hn2]
  refine IRS.seq (K₁ := 3) (K₂ := 6) (guarded (slModS_irs (r := slB) hI₈)) ?_
  rintro c₉ hI₉ - - ⟨v9, k9, m9⟩
  rw [c8B, hn2''] at v9
  have c9A : c₉.nreg slA = (g' + dq L1 δ d) % n₂ := by rw [at_index k9 _, v8]
  -- 7. the positions
  refine IRS.seq (K₁ := 1) (K₂ := 5) (guarded (copy1_irs (r := fpE) (a := slA) hI₉)) ?_
  rintro c₁₀ hI₁₀ - - ⟨v10, k10, m10⟩
  rw [c9A] at v10
  have e10 : ∀ q, ¬ SlArW q → c₁₀.nreg q = c.nreg q :=
    fun q hq => (at_index k10 q).trans ((fun q hq => (at_index k9 q).trans (e8 q hq)) q hq)
  refine IRS.seq (K₁ := 1) (K₂ := 4) (guarded (copy1_irs (r := fpH) (a := slfSH) hI₁₀)) ?_
  rintro c₁₁ hI₁₁ - - ⟨v11, k11, m11⟩
  rw [at_index e10 _] at v11
  have e11 : ∀ q, ¬ SlArW q → c₁₁.nreg q = c.nreg q :=
    fun q hq => (at_index k11 q).trans (e10 q hq)
  have c11A : c₁₁.nreg slA = (g' + dq L1 δ d) % n₂ := by
    rw [at_index k11 _, at_index k10 _, c9A]
  have c11B : c₁₁.nreg slB = (g' + (dq L1 δ (d - 1) + 1)) % n₂ := by
    rw [at_index k11 _, at_index k10 _, v9, show g' + dq L1 δ (d - 1) + 1 =
      g' + (dq L1 δ (d - 1) + 1) by ring]
  have c11E : c₁₁.nreg fpE = (g' + dq L1 δ d) % n₂ := by rw [at_index k11 _, v10]
  have c11H : c₁₁.nreg slfSH = c.nreg slfSH := at_index e11 _
  have c11K0 : c₁₁.nreg K0 = 0 := by rw [at_index e11 _, hK0]
  unfold slFS
  refine IRS.ite (fun h => ?_) (fun h => ?_)
  · have hH : c.nreg slfSH ≠ 0 := by rw [c11K0, c11H] at h; omega
    refine IRS.seq (K₁ := 1) (K₂ := 1) (guarded (copy1_irs (r := fqE) (a := slA) hI₁₁)) ?_
    rintro c₁₂ hI₁₂ - - ⟨w1, w2, w3⟩
    refine (guarded (copy1_irs (r := fqH) (a := slfSH) hI₁₂)).mono le_rfl ?_
    rintro c' ⟨z1, z2, z3⟩
    refine ⟨by rw [at_index z2 _, at_index w2 _, c11E], by rw [at_index z2 _, at_index w2 _, v11],
      by rw [at_index z2 _, w1, c11A, ite_eq_right hH], by rw [z1, at_index w2 _, c11H, ite_eq_right hH],
      fun q hq => by rw [at_index z2 q, at_index w2 q, e11 q hq], by grind⟩
  · have hH : c.nreg slfSH = 0 := by rw [c11K0, c11H] at h; omega
    refine IRS.seq (K₁ := 1) (K₂ := 1) (guarded (copy1_irs (r := fqE) (a := slB) hI₁₁)) ?_
    rintro c₁₂ hI₁₂ - - ⟨w1, w2, w3⟩
    refine (set1_irs (r := fqH) (v := 0) hI₁₂ (by rne) (Nat.zero_le _)).mono (by norm_num) ?_
    rintro c' ⟨z1, z2, z3⟩
    refine ⟨by rw [at_index z2 _, at_index w2 _, c11E], by rw [at_index z2 _, at_index w2 _, v11],
      by rw [at_index z2 _, w1, c11B, ite_eq_left hH], by rw [z1, ite_eq_left hH],
      fun q hq => by rw [at_index z2 q, at_index w2 q, e11 q hq], by grind⟩

end

end SweepEv

end Chazelle.Core
