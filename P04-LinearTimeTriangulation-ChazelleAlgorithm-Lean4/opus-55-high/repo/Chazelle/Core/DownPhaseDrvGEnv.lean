module

public import Chazelle.Core.DownPhaseDrvGPiece
public import Chazelle.Core.DownPhaseDrvGCost
public import Chazelle.Core.GradeCtx
public import Chazelle.Core.DownPhaseDegHost
public import Chazelle.Core.DownPhaseMathLevel

/-!
# Down-phase driver, region procedure (D5), part 5: the environment of the piece loop

* `RData`: the data of a run of the region procedure (host, handle, number of points, merge
  grade, piece granularity, context handle, the memory `m₁` and allocator `A₁` after the setup,
  the leaf table);
* `RFacts`: the static facts (the precondition of `RegionSpec`, the leaf table);
* `REnv R d`: the registers of the region procedure and the memory below `A₁` in a configuration;
* `AccOK R d pos γ`: the accumulated chain `⟨H.poly Q, 0, pos⟩` (descriptor at `r219110 + 1`,
  normal form `r219111`, `γ`-canonical, cap `130`), robust below the allocator.
-/

namespace Chazelle.Core

namespace DrvG

open Machine Machine.Stmt Programs BuildRam DrvR

@[expose] public section

theorem Robust.imp {A : ℕ} {m : ℕ → ℕ} {Φ Ψ : (ℕ → ℕ) → Prop} (h : Robust A m Φ)
    (hi : ∀ m', Φ m' → Ψ m') : Robust A m Ψ := fun m' hm' => hi m' (h m' hm')

theorem fullDegLe_mono {M : Model} {Q : Polygon} {D D' : ℕ} (h : M.FullDegLe Q D) (hD : D ≤ D') :
    M.FullDegLe Q D' := fun F hF => Model.DegLe.mono _ (h F hF) hD

/-- The capacity of the up-phase data is at most `2 n`. -/
theorem gradeCtx_cap_le {O : OracleIface} {P : Polygon} {m : ℕ → ℕ} {g A : ℕ} (hn : 1 ≤ P.n)
    (h : (gradeCtx O).holds P m g A) : (gradeCtx O).cap P m g ≤ 2 * P.n := by
  have h1 : m g ≤ topGrade P.n + 1 := h.holds.1
  show 2 ^ (m g - 1) ≤ 2 * P.n
  have h2 : 2 ^ (m g - 1) ≤ 2 ^ topGrade P.n := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine h2.trans ?_
  unfold topGrade
  rcases Nat.lt_or_ge (P.n - 1) 2 with h3 | h3
  · have : Nat.clog 2 (P.n - 1) = 0 := Nat.clog_of_right_le_one (by omega) 2
    rw [this]; simp; omega
  · have h4 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (show 1 < P.n - 1 by omega)
    have h5 : 1 ≤ Nat.clog 2 (P.n - 1) := Nat.clog_pos (by norm_num) (by omega)
    have e : 2 ^ Nat.clog 2 (P.n - 1) = 2 * 2 ^ (Nat.clog 2 (P.n - 1)).pred := by
      rw [← pow_succ', Nat.pred_eq_sub_one, Nat.sub_add_cancel h5]
    omega

/-- **The data of a run of the region procedure.** -/
structure RData where
  /-- The host. -/
  H : Host
  /-- Its handle. -/
  HB : ℕ
  /-- Its number of points. -/
  NP : ℕ
  /-- The merge grade. -/
  μ : ℕ
  /-- The granularity of the pieces. -/
  γ₀ : ℕ
  /-- The handle of the up-phase data. -/
  g : ℕ
  /-- The memory after the setup. -/
  m₁ : ℕ → ℕ
  /-- The allocator after the setup. -/
  A₁ : ℕ
  /-- The leaf table. -/
  T : ℕ

/-- The leaves of the host. -/
noncomputable def RData.leaves (P : Polygon) (R : RData) : List (ℕ × ℕ × ℕ) :=
  hostLeaves (Qof P).n (2 ^ R.μ) 0 R.H

/-- **The static facts** of a run of the region procedure. -/
structure RFacts (O : OracleIface) (P : Polygon) (W : ℕ) (R : RData) : Prop where
  hG : GoodEnv P
  hWn : hostWords P.n ≤ W
  hHA : Robust R.A₁ R.m₁ (fun m => HostAt m R.HB R.H)
  hHB : R.HB + 3 * R.H.length + 4 ≤ R.A₁
  hHl : R.H.length ≤ 20
  hwf : HostWF (Qof P).n R.H
  hreg : HostRegular (Qof P).n R.H
  hsimp : (R.H.poly (Qof P)).Simple
  hNP : R.NP = (R.H.pts (Qof P).n).length
  hNP3 : 3 ≤ R.NP
  hruns : ∀ a ℓ, HostItem.run a ℓ ∈ R.H → ℓ ≤ 2 * 2 ^ R.μ
  hμ7 : 7 ≤ R.μ
  hμg : R.μ ≤ R.m₁ R.g
  hg0 : 2 * gradeGran R.μ ≤ R.γ₀
  h128 : 128 ≤ R.γ₀
  hg1 : R.γ₀ ≤ 4096 * 2 ^ Cost.ceilBeta R.μ
  hcap : R.γ₀ + 129 ≤ (gradeCtx O).cap P R.m₁ R.g
  hX : (gradeCtx O).holds P R.m₁ R.g R.A₁
  hT : ChordListAt R.m₁ R.T (R.leaves P)
  hTA : R.T + 3 * (R.leaves P).length ≤ R.A₁
  hγW : R.γ₀ + 129 ≤ W

/-- **The registers of the region procedure** and the memory below `A₁`. -/
structure REnv (R : RData) (d : Config) : Prop where
  r200 : d.nreg 219200 = R.HB
  r201 : d.nreg 219201 = R.NP
  r202 : d.nreg 219202 = R.μ
  r204 : d.nreg 219204 = R.γ₀
  r205 : d.nreg 219205 = R.g
  r230 : d.nreg 219230 = 1
  r231 : d.nreg 219231 = 3
  r223 : d.nreg 219223 = R.NP - 1
  r003 : d.nreg 219003 = R.T
  mg : MgConst d
  r100 : d.nreg 219100 = R.HB
  r101 : d.nreg 219101 = R.NP
  r103 : d.nreg 219103 = 130
  r104 : d.nreg 219104 = R.g
  r107 : d.nreg 219107 = R.H.length
  low : ∀ a, a < R.A₁ → d.nmem a = R.m₁ a
  alloc : R.A₁ ≤ d.nreg ALLOC

/-- The registers `REnv` reads (all of band `bDownDrv`, outside `218000 … 218999`, `219110 …
219139` and `219240 … 219243`). -/
def envRegs : List ℕ :=
  [219200, 219201, 219202, 219204, 219205, 219230, 219231, 219223, 219003, 219140, 219141,
    219142, 219143, 219144, 219145, 219146, 219100, 219101, 219103, 219104, 219107]

theorem envRegs_band : ∀ q ∈ envRegs, bandOf q = bDownDrv ∧ 219000 ≤ q ∧
    (q < 219110 ∨ 219139 < q) ∧ q ≠ 219222 := by decide

theorem envRegs_band2 : ∀ q ∈ envRegs, q ≠ 219220 ∧ q ≠ 219221 ∧ q ≠ 219222 ∧
    (q < 219224 ∨ 219229 < q) ∧ (q < 219240 ∨ 219251 < q) := by decide

/-- The environment survives a step keeping its registers and the memory below `A₁`. -/
theorem REnv.keep {R : RData} {d d' : Config} (h : REnv R d)
    (hr : ∀ q ∈ envRegs, d'.nreg q = d.nreg q) (hm : ∀ a, a < R.A₁ → d'.nmem a = d.nmem a)
    (hA : d.nreg ALLOC ≤ d'.nreg ALLOC) : REnv R d' := by
  have e : ∀ q, q ∈ envRegs → d'.nreg q = d.nreg q := hr
  exact ⟨by rw [e _ (by simp [envRegs]), h.r200], by rw [e _ (by simp [envRegs]), h.r201],
    by rw [e _ (by simp [envRegs]), h.r202], by rw [e _ (by simp [envRegs]), h.r204],
    by rw [e _ (by simp [envRegs]), h.r205], by rw [e _ (by simp [envRegs]), h.r230],
    by rw [e _ (by simp [envRegs]), h.r231], by rw [e _ (by simp [envRegs]), h.r223],
    by rw [e _ (by simp [envRegs]), h.r003],
    ⟨by rw [e _ (by simp [envRegs]), h.mg.r40], by rw [e _ (by simp [envRegs]), h.mg.r41],
      by rw [e _ (by simp [envRegs]), h.mg.r42], by rw [e _ (by simp [envRegs]), h.mg.r43],
      by rw [e _ (by simp [envRegs]), h.mg.r44], by rw [e _ (by simp [envRegs]), h.mg.r45],
      by rw [e _ (by simp [envRegs]), h.mg.r46]⟩,
    by rw [e _ (by simp [envRegs]), h.r100], by rw [e _ (by simp [envRegs]), h.r101],
    by rw [e _ (by simp [envRegs]), h.r103], by rw [e _ (by simp [envRegs]), h.r104],
    by rw [e _ (by simp [envRegs]), h.r107], fun a ha => by rw [hm a ha, h.low a ha],
    le_trans h.alloc hA⟩

section facts

variable {O : OracleIface} {P : Polygon} {W : ℕ} {R : RData}

theorem REnv.mem_eq {d : Config} (h : REnv R d) : ∀ a, a < R.A₁ → R.m₁ a = d.nmem a :=
  fun a ha => (h.low a ha).symm

theorem REnv.hostAt (hF : RFacts O P W R) {d : Config} (h : REnv R d) :
    Robust (d.nreg ALLOC) d.nmem (fun m => HostAt m R.HB R.H) :=
  (hF.hHA.transport h.low).mono h.alloc

theorem REnv.holds (hF : RFacts O P W R) {d : Config} (h : REnv R d) :
    (gradeCtx O).holds P d.nmem R.g (d.nreg ALLOC) :=
  (gradeCtx O).mono P _ _ _ _ h.alloc ((gradeCtx O).local_ P _ _ _ _ h.mem_eq hF.hX)

theorem REnv.cap (hF : RFacts O P W R) {d : Config} (h : REnv R d) :
    (gradeCtx O).cap P d.nmem R.g = (gradeCtx O).cap P R.m₁ R.g :=
  gradeCtx_capLocal O P _ _ _ _ h.low hF.hX

theorem REnv.grades (hF : RFacts O P W R) {d : Config} (h : REnv R d) :
    d.nmem R.g = R.m₁ R.g :=
  h.low _ (gradeRaw_handle_lt (O := O) hF.hX)

theorem REnv.table (hF : RFacts O P W R) {d : Config} (h : REnv R d) :
    ChordListAt d.nmem R.T (R.leaves P) := by
  intro i hi
  obtain ⟨a1, a2, a3⟩ := hF.hT i hi
  have := hF.hTA
  refine ⟨?_, ?_, ?_⟩
  · rw [h.low _ (by omega)]; exact a1
  · rw [h.low _ (by omega)]; exact a2
  · rw [h.low _ (by omega)]; exact a3

end facts

/-- **The accumulated chain** `⟨H.poly Q, 0, pos⟩`: descriptor, normal form, granularity `γ`. -/
structure AccOK (P : Polygon) (R : RData) (d : Config) (pos γ : ℕ) : Prop where
  r22 : d.nreg 219222 = 1
  r12 : d.nreg 219112 = pos
  r13 : d.nreg 219113 = γ
  dA : d.nreg 219110 + 6 ≤ d.nreg ALLOC
  lo1 : R.A₁ ≤ d.nreg 219110
  lo2 : R.A₁ ≤ d.nreg 219111
  desc : ∀ C : Chain, C.P = R.H.poly (Qof P) → C.s = 0 → C.m = pos →
    Robust (d.nreg ALLOC) d.nmem (fun m => m (d.nreg 219110) = 0 ∧
      m (d.nreg 219110 + 1) = R.HB ∧ ChainDescAt m (d.nreg 219110 + 1) (Qof P) R.H C) ∧
    ∃ N, NFWithin d.nmem (d.nreg 219111) (d.nreg ALLOC) N ∧
      IsCanonicalNF (chainModel C) (Qof P) N γ 130

/-- The accumulated chain survives a frame keeping its registers. -/
theorem AccOK.keep {P : Polygon} {R : RData} {d d' : Config} {pos γ : ℕ} {B : Finset ℕ} {k : ℕ}
    (h : AccOK P R d pos γ) (hf : Frame B d d' k)
    (hr : ∀ q, q = 219110 ∨ q = 219111 ∨ q = 219112 ∨ q = 219113 ∨ q = 219222 →
      d'.nreg q = d.nreg q) : AccOK P R d' pos γ := by
  have r10 := hr 219110 (by simp)
  have r11 := hr 219111 (by simp)
  refine ⟨by rw [hr _ (by simp), h.r22], by rw [hr _ (by simp), h.r12],
    by rw [hr _ (by simp), h.r13], by rw [r10]; have := hf.2.2.2.2.2.1; have := h.dA; omega,
    by rw [r10]; exact h.lo1, by rw [r11]; exact h.lo2, fun C hP hs hm => ?_⟩
  obtain ⟨h1, N, h2, h3⟩ := h.desc C hP hs hm
  rw [r10, r11]
  exact ⟨h1.frame hf, N, h2.frame hf, h3⟩

end

end DrvG

end Chazelle.Core
