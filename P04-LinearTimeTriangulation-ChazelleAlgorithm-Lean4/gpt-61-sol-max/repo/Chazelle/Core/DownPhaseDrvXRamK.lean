module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseDrvXRamJ
public import Chazelle.Core.NFBuildMain

/-!
# Down phase, extraction (D6), RAM part 11: set-up, padding, outputs; the program `xS`

* `setupS`: the globals (`XG`), the allocation of `5 K` words at the allocator;
* `padS`: `3 · 5 K + 2` steps, which pay for the allocation (`Frame`);
* `finS`: the outputs `217010 … 217012`;
* `xS = setupS; padS; loopS; finS`.
-/

namespace Chazelle.Core

namespace DrvX

open Machine Machine.Stmt Programs BuildRam SignK
open DrvR (ivB qE keyBkt endPos)

@[expose] public section

/-- The straight-line part of the set-up. -/
def setupB : Stmt :=
  block [.inputSize 217020, .constN 217027 1, .constN 217041 6, .constN 217044 2,
    .copyN 217026 217002,
    .constN 217106 3, .constN 217107 4, .constN 217108 5, .constN 217109 7,
    .addN 217100 217005 217106, .loadN 217021 217100,
    .addN 217100 217005 217107, .loadN 217023 217100,
    .addN 217100 217005 217108, .loadN 217024 217100,
    .addN 217022 217021 217021, .addN 217042 217022 217041,
    .loadN 217034 217003, .addN 217035 217003 217027,
    .loadN 217028 217006, .addN 217100 217006 217106, .loadN 217029 217100,
    .addN 217100 217000 217027, .loadN 217030 217100,
    .addN 217100 217000 217107, .loadN 217031 217100,
    .addN 217100 217000 217108, .loadN 217101 217100,
    .addN 217100 217000 217109, .loadN 217103 217100,
    .addN 217104 217001 217001, .addN 217104 217104 217104, .addN 217104 217104 217001,
    .addN 217104 217101 217104, .loadN 217032 217104,
    .addN 217104 217104 217027, .loadN 217105 217104,
    .addN 217033 217103 217105,
    .copyN 217036 9999, .addN 217047 217028 217028, .addN 217047 217047 217028,
    .addN 217037 217036 217047, .addN 217047 217047 217028, .addN 217047 217047 217028,
    .addN 9999 9999 217047,
    .copyN 217045 217036, .copyN 217046 217037, .constN 217038 0, .constN 217039 0,
    .copyN 217040 217029, .constN 217043 0]

/-- **The set-up**: the globals, the allocation of `5 K` words (`K` chords of `N_R`), the
tour offset `tS`. -/
def setupS : Stmt :=
  .seq setupB
    (.ifLtN 217024 217027 (block [.subN 217025 217022 217023])
      (.ifLtN 217027 217024 (block [.subN 217025 217022 217023]) (block [.copyN 217025 217023])))

/-- **Padding**: `3 · 5 K + 2` steps, so that the allocation is paid for. -/
def padS : Stmt := .whileLtN 217043 217047 (block [.addN 217043 217043 217027])

/-- The outputs. -/
def finS : Stmt := block [.copyN 217010 217036, .copyN 217011 217038, .copyN 217012 217037]

/-- **The extraction (D6).** -/
def xS : Stmt := seqs [setupS, padS, loopS, finS]

/-- The registers the extraction writes. -/
def Bx (r : ℕ) : Bool := decide ((217000 ≤ r ∧ r < 218000) ∨ r = 9999)

/-- The real registers the extraction writes. -/
def BxR (r : ℕ) : Bool := decide (217000 ≤ r ∧ r < 218000)

theorem wrM_x : wrM Bx xS = true := by decide

theorem wrM2_x : wrM2 Bx BxR xS = true := by decide

section setup

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 8000000 in
/-- **The set-up.** -/
theorem setupS_exec (d : Config) (hw : WordsBounded W d)
    {MD HB BN BR r v2 m T b5 HL K CB A AB RB LB nRA off : ℕ}
    (h00 : d.nreg 217000 = BN) (h01 : d.nreg 217001 = r) (h02 : d.nreg 217002 = v2)
    (h03 : d.nreg 217003 = HB) (h05 : d.nreg 217005 = MD) (h06 : d.nreg 217006 = BR)
    (mMD3 : d.nmem (MD + 3) = m) (mMD4 : d.nmem (MD + 4) = T) (mMD5 : d.nmem (MD + 5) = b5)
    (mHB : d.nmem HB = HL) (mBR : d.nmem BR = K) (mBR3 : d.nmem (BR + 3) = CB)
    (mBN1 : d.nmem (BN + 1) = A) (mBN4 : d.nmem (BN + 4) = AB) (mBN5 : d.nmem (BN + 5) = RB)
    (mBN7 : d.nmem (BN + 7) = LB) (mR0 : d.nmem (RB + 5 * r) = nRA)
    (mR1 : d.nmem (RB + 5 * r + 1) = off)
    (hnW : P.n ≤ W) (hMD : MD + 5 ≤ W) (hm : 2 * m + 6 ≤ W) (hHB : HB + 1 ≤ W) (hBR : BR + 3 ≤ W)
    (hBN : BN + 7 ≤ W) (hR : RB + 5 * r + 1 ≤ W) (hLB : LB + off ≤ W)
    (hA : d.nreg ALLOC + 5 * K ≤ W) (hW7 : 7 ≤ W) :
    ∃ d' k, Exec P W setupS d d' k ∧ k ≤ 60 ∧
      d'.nreg 217020 = P.n ∧ d'.nreg 217021 = m ∧ d'.nreg 217022 = 2 * m ∧
      d'.nreg 217025 = (if b5 = 1 then T else 2 * m - T) ∧ d'.nreg 217026 = v2 ∧
      d'.nreg 217027 = 1 ∧ d'.nreg 217028 = K ∧ d'.nreg 217030 = A ∧ d'.nreg 217031 = AB ∧
      d'.nreg 217032 = nRA ∧ d'.nreg 217033 = LB + off ∧ d'.nreg 217034 = HL ∧
      d'.nreg 217035 = HB + 1 ∧ d'.nreg 217036 = d.nreg ALLOC ∧
      d'.nreg 217037 = d.nreg ALLOC + 3 * K ∧ d'.nreg 217041 = 6 ∧
      d'.nreg 217042 = 2 * m + 6 ∧ d'.nreg 217044 = 2 ∧ d'.nreg 217038 = 0 ∧
      d'.nreg 217039 = 0 ∧ d'.nreg 217040 = CB ∧ d'.nreg 217043 = 0 ∧
      d'.nreg 217045 = d.nreg ALLOC ∧ d'.nreg 217046 = d.nreg ALLOC + 3 * K ∧
      d'.nreg 217047 = 5 * K ∧ d'.nreg ALLOC = d.nreg ALLOC + 5 * K ∧ d'.nmem = d.nmem := by
  have hAL : ALLOC = 9999 := rfl
  rw [hAL] at hA ⊢
  
  
  obtain ⟨d1, k1, e1, hk1, a20, a21, a22, a23, a24, a26, a27, a28, a30, a31, a32, a33, a34, a35,
      a36, a37, a41, a42, a44, a38, a39, a40, a43, a45, a46, a47, a99, m1⟩ :
      ∃ d1 k1, Exec P W setupB d d1 k1 ∧ k1 ≤ 51 ∧
      d1.nreg 217020 = P.n ∧ d1.nreg 217021 = m ∧ d1.nreg 217022 = 2 * m ∧
      d1.nreg 217023 = T ∧ d1.nreg 217024 = b5 ∧ d1.nreg 217026 = v2 ∧
      d1.nreg 217027 = 1 ∧ d1.nreg 217028 = K ∧ d1.nreg 217030 = A ∧ d1.nreg 217031 = AB ∧
      d1.nreg 217032 = nRA ∧ d1.nreg 217033 = LB + off ∧ d1.nreg 217034 = HL ∧
      d1.nreg 217035 = HB + 1 ∧ d1.nreg 217036 = d.nreg 9999 ∧
      d1.nreg 217037 = d.nreg 9999 + 3 * K ∧ d1.nreg 217041 = 6 ∧
      d1.nreg 217042 = 2 * m + 6 ∧ d1.nreg 217044 = 2 ∧ d1.nreg 217038 = 0 ∧
      d1.nreg 217039 = 0 ∧ d1.nreg 217040 = CB ∧ d1.nreg 217043 = 0 ∧
      d1.nreg 217045 = d.nreg 9999 ∧ d1.nreg 217046 = d.nreg 9999 + 3 * K ∧
      d1.nreg 217047 = 5 * K ∧ d1.nreg 9999 = d.nreg 9999 + 5 * K ∧ d1.nmem = d.nmem := by
    unfold setupB
    exec_block
    all_goals (try (config_simp; ram_grind))
    all_goals (try (refine ⟨by omega, ?_⟩))
    all_goals (repeat' ram_grind)
    all_goals ram_simp <;> omega_nf
    all_goals omega
  have hw1 := e1.wb_right
  obtain ⟨d2, k2, e2, hk2, n2⟩ := x_ifR (P := P) (W := W) (a := 217024) (b := 217027)
    (r := 217025) (t := block [.subN 217025 217022 217023])
    (e := .ifLtN 217027 217024 (block [.subN 217025 217022 217023]) (block [.copyN 217025 217023]))
    (d := d1) (K := 3) (fun _ => x_mono (x_sub d1 hw1 217025 217022 217023) (by omega))
    (fun _ => x_ifR (fun _ => x_sub d1 hw1 217025 217022 217023)
      (fun _ => x_copy d1 hw1 217025 217023))
  have o : ∀ r, r ≠ 217025 → d2.nreg r = d1.nreg r := fun r hr => n2.other hr
  refine ⟨d2, k1 + k2, .seq e1 e2, by omega, by ram_grind,
    by ram_grind, by ram_grind, ?_,
    by ram_grind, by ram_grind, by ram_grind,
    by ram_grind, by ram_grind, by ram_grind,
    by ram_grind, by ram_grind, by ram_grind,
    by ram_grind, by ram_grind, by ram_grind,
    by ram_grind, by ram_grind, by ram_grind,
    by ram_grind, by ram_grind, by ram_grind,
    by ram_grind, by ram_grind, by ram_grind,
    by ram_grind, by ram_grind⟩
  rw [n2.same, a24, a27, a22, a23]
  grind

end setup

section pad

variable {P : Polygon} {W : ℕ}

/-- **Padding**: exactly `3 (N - j) + 2` steps. -/
theorem padS_exec (d : Config) (hw : WordsBounded W d) {N j : ℕ} (h43 : d.nreg 217043 = j)
    (h47 : d.nreg 217047 = N) (h27 : d.nreg 217027 = 1) (hj : j ≤ N) (hNW : N ≤ W) :
    ∃ d' k, Exec P W padS d d' k ∧ k = 3 * (N - j) + 2 ∧ NRegs d d' (upd d.nreg 217043 N) := by
  induction hn : N - j generalizing d j with
  | zero =>
    have hjN : j = N := by omega
    subst hjN
    refine ⟨d, 2, .whileLtN_false (by omega) hw, by omega, ?_⟩
    grind [Chazelle.Core.DrvX.NRegs, Machine.upd_eq_self]
  | succ t ih =>
    have hlt : j < N := by omega
    have hb : d.nreg 217043 + d.nreg 217027 ≤ W := by omega
    have ea := Machine.Exec.addN (P := P) hw 217043 217043 217027 hb
    have e1 : Exec P W (block [.addN 217043 217043 217027]) d
        { d with nreg := upd d.nreg 217043 (d.nreg 217043 + d.nreg 217027) } (0 + 1) :=
      Exec.block_cons ea (Exec.block_nil ea.wb_right)
    have b43 : ({ d with nreg := upd d.nreg 217043 (d.nreg 217043 + d.nreg 217027) } : Config).nreg
        217043 = j + 1 := by ram_simp
    obtain ⟨d', k', e', hk', n'⟩ := ih _ e1.wb_right b43 (by simp [h47]) (by simp [h27]) (by omega)
      (by omega)
    refine ⟨d', 0 + 1 + 2 + k', .whileLtN_true (by omega) e1 e', by omega, ?_⟩
    obtain ⟨n1, n2, n3, n4, n5⟩ := n'
    refine ⟨?_, n2, n3, n4, n5⟩
    rw [n1]; simp

end pad

end

end DrvX

end Chazelle.Core
