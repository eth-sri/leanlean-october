module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepIoS0CandInitBlk

/-!
# The sweep RAM (WP-D), answers: the slot table of the side-0 candidates (environment)

`IE`: the environment of the initialisation (`AEnv` at the entry configuration `c₀` and the
outputs of stages 2 and 3, `OD`).  Facts at a run configuration (`IE.fix`, `IE.odc`, `IE.nw`),
the binary search (`LSBody`, `IE.search`) and the origin of a stop record (`stOrg_irs`).
-/

namespace Chazelle.Core

namespace SweepIo

namespace S0C

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep SweepEv

@[expose] public section

/-- The body of `LSearchSpec` for the program `lsearch` and the constant `κ`. -/
def LSBody (lsearch : Stmt) (κ : ℕ) : Prop :=
  ∀ (P : Polygon) (W : ℕ) (J : Merge.Junction) (c₀ c : Config),
    IInv W c₀ c → Consts c₀ → ChainCtx P W c (sw 2) J.whole →
    (∀ j, j < c.nreg TLR → c.nmem (c.nreg TBR + j) = 2 ^ j) →
    c.nreg TBR + c.nreg TLR ≤ c.nreg ALLOC →
    c.nreg (sw 301) < 2 ^ c.nreg TLR →
    c.nreg (sw 300) + 7 * c.nreg (sw 301) ≤ c.nreg ALLOC →
    c.nreg (sw 40) < (chainModel J.whole).W.n →
    (∀ j, j < c.nreg (sw 301) → SweepEv.PosW P J (c.nmem (c.nreg (sw 300) + 7 * j))
      (c.nmem (c.nreg (sw 300) + 7 * j + 1))) →
    SweepEv.PosW P J (c.nreg lsxE) (c.nreg lsxH) →
    (∀ i j, i ≤ j → j < c.nreg (sw 301) →
      lsPr P J c.nmem (c.nreg (sw 300)) (c.nreg (sw 40)) ⟨c.nreg lsxE, c.nreg lsxH⟩ j →
      lsPr P J c.nmem (c.nreg (sw 300)) (c.nreg (sw 40)) ⟨c.nreg lsxE, c.nreg lsxH⟩ i) →
    c.nreg ALLOC + κ * (c.nreg TLR + 1) ≤ W →
    IRS P W c₀ lsearch c (κ * (c.nreg TLR + 1)) (fun c' =>
      c'.nreg lsI ≤ c.nreg (sw 301) ∧
      (∀ j, j < c'.nreg lsI →
        lsPr P J c.nmem (c.nreg (sw 300)) (c.nreg (sw 40)) ⟨c.nreg lsxE, c.nreg lsxH⟩ j) ∧
      (∀ j, c'.nreg lsI ≤ j → j < c.nreg (sw 301) →
        ¬ lsPr P J c.nmem (c.nreg (sw 300)) (c.nreg (sw 40)) ⟨c.nreg lsxE, c.nreg lsxH⟩ j) ∧
      (∀ r, bandOf r ∉ oracleBands → ¬ LSet r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a))

/-- **The environment of the initialisation.** -/
structure IE (P : Polygon) (W : ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop)
    (J : Merge.Junction) (H : Host) (N₁ N₂ : NF) (Eb : ℕ) (c₀ : Config)
    (rs : List (ℕ × ℕ × ℕ × ℕ × ℕ)) (ls : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)) : Prop where
  hA : AEnv P W X Ok J H N₁ N₂ Eb c₀
  od : OD P J N₂ c₀.nmem (rd c₀ bSweep 200) (rd c₀ bSweep 201) (rd c₀ bSweep 300)
    (rd c₀ bSweep 301) (rd c₀ bSweep 302) rs ls

section env

variable {P : Polygon} {W : ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction}
  {H : Host} {N₁ N₂ : NF} {Eb : ℕ} {c₀ c : Config} {rs : List (ℕ × ℕ × ℕ × ℕ × ℕ)}
  {ls : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)}

theorem IE.fix (_e : IE P W X Ok J H N₁ N₂ Eb c₀ rs ls) (hI : IInv W c₀ c) {k : ℕ}
    (hk : k < 700) : c.nreg (sw k) = c₀.nreg (sw k) :=
  hI.hin _ (by omega_nf)

section
variable (e : IE P W X Ok J H N₁ N₂ Eb c₀ rs ls)
include e
/-- The outputs of stages 2 and 3 at a run configuration. -/
theorem IE.odc {m : ℕ → ℕ}
    (hm : ∀ a, a < c₀.nreg ALLOC → m a = c₀.nmem a) :
    OD P J N₂ m (rd c₀ bSweep 200) (rd c₀ bSweep 201) (rd c₀ bSweep 300)
      (rd c₀ bSweep 301) (rd c₀ bSweep 302) rs ls :=
  e.od.congr hm e.hA.hstops e.hA.hlog e.hA.htabw

theorem IE.st0 :
    c₀.nreg (sw 40) = gW J ∧ c₀.nreg (sw 41) = cstR J 1 ∧
      c₀.nreg (sw 34) = 2 * J.right.m + 7 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h40, -, -, h34, -⟩ := e.hA.hst
  exact ⟨h40 0 (by norm_num), h40 1 (by norm_num), h34⟩

theorem IE.nw (hI : IInv W c₀ c) :
    NFWithin c.nmem (c.nreg (sw 4)) (c.nreg ALLOC) N₂ := by
  rw [e.fix hI (k := 4) (by norm_num)]
  have hE := e.hA.hE
  exact (e.hA.hN₂.transport (fun a ha => hI.hm a (by omega))).mono (hE.trans hI.hA)


end

theorem ini_gW_lt_nat (J : Merge.Junction) : gW J < (chainModel J.whole).W.n := by
  exact_mod_cast gW_lt J

/-- **The binary search** for the key `(lsxE, lsxH)` at a run configuration. -/
theorem IE.search {lsS : Stmt} {κL : ℕ} (hls : LSBody lsS κL)
    (e : IE P W X Ok J H N₁ N₂ Eb c₀ rs ls) (hI : IInv W c₀ c)
    (hx : PosW P J (c.nreg lsxE) (c.nreg lsxH))
    (hroom : c.nreg ALLOC + κL * (c₀.nreg TLR + 1) ≤ W) :
    IRS P W c₀ lsS c (κL * (c₀.nreg TLR + 1)) (fun c' =>
      (∀ j, j < c'.nreg lsI → lsPr P J c.nmem (c₀.nreg (sw 300)) (gW J)
        ⟨c.nreg lsxE, c.nreg lsxH⟩ j) ∧
      (∀ j, c'.nreg lsI ≤ j → j < c₀.nreg (sw 301) → ¬ lsPr P J c.nmem (c₀.nreg (sw 300)) (gW J)
        ⟨c.nreg lsxE, c.nreg lsxH⟩ j) ∧
      (∀ r, bandOf r ∉ oracleBands → ¬ LSet r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  have hA := e.hA
  have f300 := e.fix hI (k := 300) (by norm_num)
  have f301 := e.fix hI (k := 301) (by norm_num)
  have f40 := e.fix hI (k := 40) (by norm_num)
  have fTB : c.nreg TBR = c₀.nreg TBR := e.fix hI (k := 600) (by norm_num)
  have fTL : c.nreg TLR = c₀.nreg TLR := e.fix hI (k := 601) (by norm_num)
  have g40 := e.st0.1
  have od := e.odc (m := c.nmem) (fun a ha => hI.hm a ha)
  have hbig := hA.hbigE
  simp only [rd_sw] at hbig od
  have hlog := hA.hlog
  simp only [rd_sw] at hlog
  have hTW := hA.hTW
  have h := hls P W J c₀ c hI hA.hK (hA.ctxW hI)
    (fun j hj => by
      rw [fTB, hI.hm _ (by omega)]
      rw [fTL] at hj; exact hA.htab j hj)
    (by rw [fTB, fTL]; exact hTW.trans hI.hA)
    (by ram_grind)
    (by rw [f300, f301]; exact hlog.trans hI.hA)
    (by rw [f40, g40]; exact ini_gW_lt_nat J)
    (fun j hj => by rw [f300]; rw [f301] at hj; exact od.logW hj)
    hx
    (by rw [f300, f301, f40, g40]; exact od.down rfl _)
    (by simp_all)
  rw [fTL, f300, f301, f40, g40] at h
  exact h.mono le_rfl (fun c' h' => h'.2)

set_option maxHeartbeats 4000000 in
/-- **The origin position of a stop record** by its kind. -/
theorem stOrg_irs (e : IE P W X Ok J H N₁ N₂ Eb c₀ rs ls) (hI : IInv W c₀ c) {kind k b : ℕ}
    (hk1 : c.nreg ipK = kind) (hk2 : c.nreg ipKk = k) (hb : c.nreg ipS = sOf b)
    (hkind : kind ≤ 2) (hkk : kind = 1 → k < N₂.nChords) (hroom : c.nreg ALLOC + 11110 ≤ W) :
    IRS P W c₀ stOrg c 11110 (fun c' =>
      c'.nreg ipE = (stopPos P J N₂ kind k b).edge ∧ c'.nreg ipH = (stopPos P J N₂ kind k b).hgt ∧
      (∀ r, bandOf r ∉ oracleBands → (r < sw 2200 ∨ sw 2217 < r) → r ≠ ipE → r ≠ ipH →
        r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  have hK : Consts c := e.hA.hK.fix hI
  obtain ⟨k0, k1, k6, -, -, k2, -⟩ := hK
  have h41 : c.nreg (sw 41) = cstR J 1 := (e.fix hI (k := 41) (by norm_num)).trans e.st0.2.1
  have nE : ipH ≠ ipE := by omega_nf
  unfold stOrg
  by_cases c0 : kind = 0
  · refine (IRS.ifT (K := 2) (by omega) (IRS.block _ hI ?_)).mono
      (by norm_num) ?_
    · simp [okB, okI, ipE, ipH, sw, IScr]
    simp_all [regB, regI, upd_same, stopPos] <;> omega_nf
  refine (IRS.ifF (K := 11108) (by omega) ?_).mono (by norm_num) (fun _ h => h)
  by_cases c1 : kind = 1
  · subst c1
    refine (IRS.ifT (K := 11104) (by omega) ?_).mono (by norm_num) (fun _ h => h)
    have hko := hkk rfl
    refine IRS.seq (K₁ := 2) (K₂ := 11102) (IRS.block [.copyN oK ipKk, .copyN oS ipS] hI ?_) ?_
    · simp [okB, okI, oK, oS, sw, IScr]
    rintro c₁ hI₁ hA₁ hA₁' rfl
    have v1 : ∀ r, r ≠ oK → r ≠ oS → regB c.nmem [.copyN oK ipKk, .copyN oS ipS] c.nreg r =
        c.nreg r := fun r h1 h2 => by
      simp_all [regB, regI] 
    have vK : regB c.nmem [.copyN oK ipKk, .copyN oS ipS] c.nreg oK = k := by
      simp_all [regB, regI, oK, oS, sw, upd_same] 
    have vS : regB c.nmem [.copyN oK ipKk, .copyN oS ipS] c.nreg oS = sOf b := by
      simp_all [regB, regI, upd_same, oK, ipS, sw] 
    refine IRS.seq (K₁ := 11100) (K₂ := 2) (orgHead_irs hI₁ e.hA.hK (e.hA.ctxR hI₁)
      e.hA.hNF₂ (e.nw hI₁) le_rfl (by simp_all)
      (by simp only; rw [vS]; exact ini_sOf_le b) (by omega)) ?_
    rintro c₂ hI₂ hA₂ hA₂' ⟨-, -, -, -, vE, vC, -, -, fr₂, hAl₂, hm₂⟩
    simp only at vE vC fr₂ hAl₂ hm₂
    rw [vK, vS] at vE vC
    have eA : regB c.nmem [.copyN oK ipKk, .copyN oS ipS] c.nreg ALLOC = c.nreg ALLOC :=
      v1 _ (by omega_nf) (by omega_nf)
    rw [eA] at hAl₂ hm₂
    refine (IRS.block [.copyN ipE oE, .copyN ipH oC] hI₂ ?_).mono le_rfl ?_
    · simp [okB, okI, ipE, ipH, sw, IScr]
    rintro c' rfl
    refine ⟨?_, ?_, fun r hr h1 h2 h3 h4 => ?_, ?_, fun a ha => ?_⟩
    · simp only [regB, regI, upd_same, upd_other _ _ _ nE.symm]
      grind [stopPos]
    · simp only [regB, regI, upd_same,
        upd_other _ _ _ (show oC ≠ ipE by omega_nf)]
      grind [stopPos]
    · simp only [regB, regI]
      rw [upd_other _ _ _ h3, upd_other _ _ _ h2, fr₂ r hr (by core_grind) h4,
        v1 r (by core_grind) (by core_grind)]
    · simp only [regB, regI]
      rw [upd_other _ _ _ (show ALLOC ≠ ipH by omega_nf),
        upd_other _ _ _ (show ALLOC ≠ ipE by omega_nf)]
      exact hAl₂
    ram_grind
  · have c2 : kind = 2 := by omega
    refine (IRS.ifF (K := 2) (by omega) (IRS.block _ hI ?_)).mono
      (by norm_num) ?_
    · simp [okB, okI, ipE, ipH, sw, IScr]
    simp_all [regB, regI, upd_same, stopPos] <;> omega_nf

end env

end

end S0C

end SweepIo

end Chazelle.Core
