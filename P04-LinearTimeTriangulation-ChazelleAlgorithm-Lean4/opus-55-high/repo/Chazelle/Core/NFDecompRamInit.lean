module

public import Chazelle.MacT
public import Chazelle.Core.OracleBook

namespace Chazelle.Core.DecR
open Machine Machine.Stmt Programs
@[expose] public section
set_option maxHeartbeats 1000000
section setup
variable {P : Polygon} {W : ℕ}

/-- **The setup.** -/
theorem setupS_exec {c : Config} (hw : WordsBounded W c) {B K R CB RB LB : ℕ}
    (hB : c.nreg 60001 = B) (hK : c.nmem B = K) (hR : c.nmem zthb = R)
    (hCB : c.nmem ztkh = CB) (hRB : c.nmem zter = RB) (hLB : c.nmem ztlw = LB)
    (hBW : B + 7 ≤ W) (hroom : c.nreg ALLOC + 12 + 20 * R + 3 * K ≤ W) :
    ∃ c' k, Exec P W setupS c c' k ∧ k = 38 ∧ DRegs ztm R K CB RB LB c' ∧
      c'.nreg ALLOC = c.nreg ALLOC ∧
      c'.nreg 60086 = c.nreg ALLOC + 12 + 19 * R + 3 * K ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧
      (∀ r, (r < 60010 ∨ (60032 ≤ r ∧ r < 60086) ∨ (60087 ≤ r ∧ r < 60100) ∨ 60120 ≤ r) →
        r ≠ ALLOC →
        c'.nreg r = c.nreg r) := by
  have hA : c.nreg 9999 = c.nreg ALLOC := rfl
  unfold setupS
  exec_block
  all_goals first
    | omega
    | (config_simp; simp (config := { failIfUnchanged := false }) only [hB, hR, hK, hA]; omega)
    | skip
  have e3 : B + 2 + 1 = B + 3 := rfl
  have e5 : B + 2 + 1 + 2 = B + 5 := rfl
  have e7 : B + 2 + 1 + 2 + 2 = B + 7 := rfl
  refine ⟨by_omega, ztbie, ?_, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · config_simp
  · config_simp
  · config_simp
  · config_simp; grind
  · config_simp; grind
  · config_simp; grind
  · config_simp; grind
  · config_simp; grind
  · rfl
  · config_simp; grind
  · zuhgh
    simp only [fb]
    interval_cases f <;> config_simp <;>
      simp (config := { failIfUnchanged := false }) only [hB, hR, hA] <;> omega
  · rfl
  · config_simp; grind
  · zujbl
    zugzy
    config_simp
    zup
end setup
end
end Chazelle.Core.DecR
namespace Chazelle.Core.DecR
open Machine Machine.Stmt Programs
@[expose] public section
theorem DRegs.b {A R K CB RB LB : ℕ} {c : Config} (h : DRegs A R K CB RB LB c) (f : ℕ)
    (hf : f < 20) : c.nreg (60100 + f) = A + 12 + f * R := h.base f hf
section alloc
variable {P : Polygon} {W : ℕ}
end alloc
section init
variable {P : Polygon} {W : ℕ}
variable {A R K CB RB LB : ℕ} {c : Config}
theorem initBody_exec (hw : WordsBounded W c)
    (hR : DRegs A R K CB RB LB c) (hi : c.nreg 60020 < R) (hroom : A + 12 + 20 * R ≤ W) :
    ∃ c' k, Exec P W initBody c c' k ∧ k = 9 ∧ DFr ztiq zten c c' ∧
      c'.nreg 60020 = c.nreg 60020 + 1 ∧
      ∀ f j, f < 19 → j < R → fv c'.nmem A R f j =
        if j = c.nreg 60020 ∧ (f = 2 ∨ f = 7 ∨ f = 11 ∨ f = 12) then (if f = 7 then 1 else 0)
        else fv c.nmem A R f j := by
  have b2 := hR.b 2 by_norm_num; have b7 := hR.b 7 by_norm_num
  have b11 := hR.b 11 by_norm_num; have b12 := hR.b 12 by_norm_num
  zvmxv at b2 b7 b11 b12
  zumgb
  zujaf
  unfold initBody
  exec_block
  all_goals first
    | (config_simp; simp (config := { failIfUnchanged := false }) only [b2, b7, b11, b12, o]; omega)
    | skip
  refine ⟨rfl, ?_, by_simp_all, fun f j hf hj => ?_⟩
  · refine ztcqy
    · zuhae
      config_simp
      zup
    · config_simp
      simp only [b2, b7, b11, b12]
      zup
  · config_simp
    simp only [b2, b7, b11, b12, z, o]
    rw [fv_store hi hj, fv_store hi hj, fv_store hi hj, fv_store hi hj]
    grind

/-- The initialisation loop. -/
theorem initLoop_exec (hw : WordsBounded W c)
    (hR : DRegs A R K CB RB LB c) (h0 : c.nreg 60020 = 0) (hroom : A + 12 + 20 * R ≤ W) :
    ∃ c' k, Exec P W ztrif c c' k ∧ k ≤ 11 * R + 2 ∧
      WordsBounded W c' ∧ DFr ztiq zten c c' ∧
      ∀ j, j < R → fv c'.nmem A R 2 j = 0 ∧ fv c'.nmem A R 7 j = 1 ∧ fv c'.nmem A R 11 j = 0 ∧
        fv c'.nmem A R 12 j = 0 := by
  obtain ⟨c', k, e, ⟨hw', hf', hle, hv⟩, htest, hk⟩ := Exec.whileLtN_potential (P := P) (W := W)
    (a := 60020) (b := 60013) (body := initBody)
    (fun d => WordsBounded W d ∧ DFr ztiq zten c d ∧ d.nreg 60020 ≤ R ∧
      ∀ j, j < d.nreg 60020 → fv d.nmem A R 2 j = 0 ∧ fv d.nmem A R 7 j = 1 ∧
        fv d.nmem A R 11 j = 0 ∧ fv d.nmem A R 12 j = 0)
    (fun d => 11 * zthrx) ztesk
    (fun d ⟨hwd, hfd, hled, hvd⟩ ht => by
      zubdq
      zuktd
      obtain ⟨d', k', e', rfl, hf', hi', hv'⟩ := initBody_exec (P := P) hwd hRd ht hroom
      refine ⟨d', 9, e', ⟨e'.wb_right, hfd.trans hf', by_omega, fun j hj => ?_⟩, by_omega⟩
      grind)
    ⟨hw, DFr.refl _ _ c, by_omega, fun j hj => by_omega⟩
  zuut

  grind

/-- **The initialisation.** -/
theorem initS_exec (hw : WordsBounded W c)
    (hR : DRegs A R K CB RB LB c) (hR1 : 1 ≤ R) (hroom : A + 12 + 20 * R ≤ W) :
    ∃ c' k, Exec P W initS c c' k ∧ k ≤ 11 * R + 11 ∧
      WordsBounded W c' ∧ DFr ztiq zten c c' ∧
      (∀ j, j < R → fv c'.nmem A R 2 j = (if j = 0 then 1 else 0) ∧ fv c'.nmem A R 7 j = 1 ∧
        fv c'.nmem A R 11 j = 0 ∧ fv c'.nmem A R 12 j = 0) ∧
      fv c'.nmem A R 1 0 = 0 ∧ fv c'.nmem A R 13 0 = 1 ∧ fv c'.nmem A R 15 0 = 2 := by
  zujqm
  refine spec_seq ztwmb
  have hf1 : DFr ztiq zten c
      { c with nreg := upd c.nreg 60020 0 } :=
    DFr.nreg _ fun r hr _ => by unfold Prot at hr; zumyl
  obtain ⟨c2, k2, e2, hk2, hw2, hf2, hv2⟩ := initLoop_exec (P := P) hw1 (hR.frame hf1)
    (by config_simp) hroom
  have hR2 := (hR.frame hf1).frame hf2
  refine spec_seq ⟨c2, k2, e2, ?_⟩
  have b1 := hR2.b 1 by_norm_num; have b2 := hR2.b 2 by_norm_num
  have b13 := hR2.b 13 by_norm_num; have b15 := hR2.b 15 by_norm_num
  zvmxv at b1 b2 b13 b15
  have z := hR2.zero; have o := hR2.one; have t := hR2.two
  unfold rootInit
  exec_block
  all_goals first
    | (config_simp; simp (config := { failIfUnchanged := false }) only [b1, b2, b13, b15, z]; omega)
    | skip
  zudny
  refine ⟨by_omega, ‹_›, hf1.trans (hf2.trans ztcqy),
    fun j hj => ?_, ?_, ?_, ?_⟩
  · unfold Prot at hr; config_simp; simp (disch := omega) only [Machine.upd_other]
  · config_simp; simp only [b1, b2, b13, b15, z]
    zup
  · config_simp; zunfh
    obtain ⟨v1, v2, v3, v4⟩ := hv2 j hj
    simp only [fv_store hR0 hj]
    simp_all
  all_goals
    config_simp
    zunfh
    zumsr
    zudi
    zuwd
end init
open Chazelle.Core.Dec
structure InEnv (m : ℕ → ℕ) (A R K CB RB LB : ℕ) (up dn : ℕ → ℕ) (lst : ℕ → List ℕ) : Prop where
  hup : ∀ i, i < K → m ztdfl = up i ∧ m ztdfm = dn i ∧ CB + 5 * i + 4 < A
  hlen : ∀ r, r < R → m zthci = (lst r).length ∧ RB + 5 * r + 3 < A
  hent : ∀ r, r < R → ∀ t, t < (lst r).length →
    m ztyvg = (lst r).getD t 0 ∧ LB + m ztvi + t < A
theorem InEnv.transport {m m' : ℕ → ℕ} {A R K CB RB LB : ℕ} {up dn : ℕ → ℕ} {lst : ℕ → List ℕ}
    (h : InEnv m A R K CB RB LB up dn lst) (hm : ∀ a, a < A → m' a = m a) :
    InEnv m' A R K CB RB LB up dn lst := by
  refine ztfwh
  · obtain ⟨a1, a2, a3⟩ := h.hup i hi
    grind
  · obtain ⟨a1, a2⟩ := h.hlen r hr
    grind
  · obtain ⟨-, a2⟩ := h.hlen r hr
    have e : ztskj := hm _ a2
    obtain ⟨b1, b2⟩ := h.hent r hr t ht
    simp_all

/-- The memory holds the search state `st` (on the `R` entries of its fields). -/
def BEnc (m : ℕ → ℕ) (A R : ℕ) (st : BS) : Prop :=
  ∀ j, j < R → fv m A R 1 j = st.ord j ∧ fv m A R 2 j = st.vis j ∧ fv m A R 3 j = st.prg j ∧
    fv m A R 4 j = st.pch j ∧ fv m A R 5 j = st.isdn j ∧ fv m A R 6 j = st.chOf j

/-- The fields outside `S` are those of `m₀`. -/
def FFix (S : ℕ → Prop) (m₀ m : ℕ → ℕ) (A R : ℕ) : Prop :=
  ∀ f, f < 19 → ¬ S f → ∀ j, j < R → fv m A R f j = fv m₀ A R f j

/-- The fields written by the search. -/
def BFields (f : ℕ) : Prop := 1 ≤ f ∧ f ≤ 6
section inner
variable {P : Polygon} {W : ℕ}

/-- The registers outside `l` (and the real state and output) are unchanged. -/
def Same (l : List ℕ) (c c' : Config) : Prop :=
  (∀ x, x ∉ l → c'.nreg x = c.nreg x) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
variable {l : List ℕ} {c : Config}
theorem Same.trans {c₁ c₂ c₃ : Config} (h₁ : Same l c₁ c₂) (h₂ : Same l c₂ c₃) :
    Same l c₁ c₃ :=
  ⟨fun x hx => (h₂.1 x hx).trans (h₁.1 x hx), h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    h₂.2.2.2.trans h₁.2.2.2⟩
theorem Same.mono {l l' : List ℕ} {c c' : Config} (h : Same l c c') (hl : ∀ x ∈ l, x ∈ l') :
    Same l' c c' :=
  ⟨fun x hx => h.1 x by_grind, h.2.1, h.2.2.1, h.2.2.2⟩
theorem DRegs.of_same {A R K CB RB LB : ℕ} {l : List ℕ} {c c' : Config}
    (h : DRegs A R K CB RB LB c) (hs : Same l c c') (hl : ∀ x ∈ l, ¬ Prot x) :
    DRegs A R K CB RB LB c' :=
  h.of_regs fun x hx _ => hs.1 x by_grind

/-- A step writing only non-protected registers and memory in `[lo, hi)` is in the frame. -/
theorem DFr.of_same {lo hi : ℕ} {l : List ℕ} {c c' : Config} (hs : Same l c c')
    (hl : ∀ x ∈ l, ¬ Prot x) (hm : ∀ a, ztnqq → c'.nmem a = c.nmem a) :
    DFr lo hi c c' :=
  ⟨fun x hx _ => hs.1 x by_grind, hs.2.1, hs.2.2.1, hs.2.2.2, hm⟩
theorem Same.upd1 {x v : ℕ} (hx : x ∈ l) :
    Same l c { c with nreg := upd c.nreg x v } :=
  ⟨fun y hy => by
    show upd c.nreg x v y = c.nreg y
    zumlr
    grind, rfl, rfl, rfl⟩

/-- `ldF`, relationally. -/
theorem ldF_rel (hw : WordsBounded W c) (d f x : ℕ)
    (hb : c.nreg ztgip + c.nreg x ≤ W) :
    ∃ c' k, Exec P W ztrsz c c' k ∧ k = 2 ∧ c'.nmem = c.nmem ∧ Same [60030, d] c c' ∧
      c'.nreg d = c.nmem ztcut := by
  obtain ⟨c', k, e, hk, rfl⟩ := ldF_exec (P := P) hw d f x hb
  refine ⟨_, k, e, hk, rfl, ztkle, by config_simp⟩
  simp_all

/-- `stF`, relationally. -/
theorem stF_rel (hw : WordsBounded W c) (f x v : ℕ) (hv : v ≠ 60030)
    (hb : c.nreg ztgip + c.nreg x ≤ W) :
    ∃ c' k, Exec P W ztrxf c c' k ∧ k = 2 ∧
      c'.nmem = upd c.nmem ztcut ztjsn ∧ Same [60030] c c' := by
  obtain ⟨c', k, e, hk, rfl⟩ := stF_exec (P := P) hw f x v hv hb
  refine ⟨_, k, e, hk, rfl, ztkle⟩
  simp_all

/-- **Reading a chord of the current list** and its endpoints. -/
theorem bfsRead_exec {A R K CB RB LB : ℕ} {up dn : ℕ → ℕ} {c : Config} (hw : WordsBounded W c)
    (hR : DRegs A R K CB RB LB c) (hAW : A ≤ W) {L t i : ℕ} (h28 : c.nreg 60028 = L)
    (h21 : c.nreg 60021 = t) (hLt : LB + L + t < A) (hi : c.nmem ztpzn = i)
    (hup : c.nmem ztdfl = up i) (hdn : c.nmem ztdfm = dn i)
    (hCB : CB + 5 * i + 4 < A) :
    ∃ c' k, Exec P W bfsRead c c' k ∧ k = 12 ∧ c'.nmem = c.nmem ∧
      Same [60030, 60032, 60033, 60034, 60035] c c' ∧ c'.nreg 60032 = i ∧
      c'.nreg 60034 = up i ∧ c'.nreg 60035 = dn i := by
  have o := hR.one; have tw := hR.two; have hcb := hR.rCB; have hlb := hR.rLB
  have hi' : c.nmem (LB + ztsza) = i := by_grind
  unfold bfsRead
  exec_block
  all_goals first
    | (config_simp; simp (config := { failIfUnchanged := false }) only [h28, h21, hi', hcb, hlb, o, tw]
       omega)
    | skip
  refine ⟨rfl, rfl, ztcxx, ?_, ?_, ?_⟩
  · simp_all
  · simp_all
  · config_simp; grind
  · config_simp; grind

/-- **Discovering a region**: the six stores of `bfsNew`. -/
theorem bfsNew_exec {A R K CB RB LB : ℕ} {c : Config} (hw : WordsBounded W c)
    (hR : DRegs A R K CB RB LB c) (hAW : A + 12 + 20 * R ≤ W) {sv tl r i v : ℕ}
    (h36 : c.nreg 60036 = sv) (h26 : c.nreg 60026 = tl) (h29 : c.nreg 60029 = r)
    (h32 : c.nreg 60032 = i) (h37 : c.nreg 60037 = v) (hs : sv < R) (htl : tl < R) (hi : i < R) :
    ∃ c' k, Exec P W bfsNew c c' k ∧ k = 13 ∧ DFr ztiq zten c c' ∧
      Same [60030, 60026] c c' ∧ c'.nreg 60026 = tl + 1 ∧
      ∀ j, j < R → fv c'.nmem A R 1 j = (if j = tl then sv else fv c.nmem A R 1 j) ∧
        fv c'.nmem A R 2 j = (if j = sv then 1 else fv c.nmem A R 2 j) ∧
        fv c'.nmem A R 3 j = (if j = sv then r else fv c.nmem A R 3 j) ∧
        fv c'.nmem A R 4 j = (if j = sv then i else fv c.nmem A R 4 j) ∧
        fv c'.nmem A R 5 j = (if j = sv then v else fv c.nmem A R 5 j) ∧
        fv c'.nmem A R 6 j = (if j = i then sv else fv c.nmem A R 6 j) ∧
        ∀ f, f < 19 → ¬ BFields f → fv c'.nmem A R f j = fv c.nmem A R f j := by
  have b1 := hR.b 1 by_norm_num; have b2 := hR.b 2 by_norm_num; have b3 := hR.b 3 by_norm_num
  have b4 := hR.b 4 by_norm_num; have b5 := hR.b 5 by_norm_num; have b6 := hR.b 6 by_norm_num
  zvmxv at b1 b2 b3 b4 b5 b6
  zujaf
  unfold bfsNew
  exec_block
  all_goals first
    | (config_simp; simp (config := { failIfUnchanged := false }) only [b1, b2, b3, b4, b5, b6,
        h36, h26, h32, o]; omega)
    | skip
  refine ⟨rfl, ⟨fun x hx hxa => ?_, rfl, rfl, rfl, fun a ha => ?_⟩, ztcxx,
    ?_, fun j hj => ?_⟩
  · unfold Prot at hx; config_simp; simp (disch := omega) only [Machine.upd_other]
  · config_simp
    simp only [b1, b2, b3, b4, b5, b6, h36, h26, h32]
    zup
  · simp_all
  · simp_all
  · config_simp
    simp only [b1, b2, b3, b4, b5, b6, h36, h26, h29, h32, h37, o]
    simp only [fv_store hi hj, fv_store hs hj, fv_store htl hj]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun f hf hnf => ?_⟩
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · unfold BFields at hnf
      grind

/-- The other endpoint of the chord and the side bit. -/
theorem bfsSel_exec (hw : WordsBounded W c) {u d r : ℕ} (h34 : c.nreg 60034 = u)
    (h35 : c.nreg 60035 = d) (h29 : c.nreg 60029 = r) (o : c.nreg 60011 = 1) (z : c.nreg 60010 = 0) :
    ∃ c' k, Exec P W (ifEqN 60034 60029 ztksl
        ztksk) c c' k ∧ k ≤ 6 ∧ c'.nmem = c.nmem ∧
      Same [60036, 60037] c c' ∧ c'.nreg 60036 = (if u = r then d else u) ∧
      c'.nreg 60037 = (if u = r then 1 else 0) := by
  have hsame : ∀ (a b : ℕ), Same [60036, 60037] c
      { c with nreg := upd (upd c.nreg 60036 a) 60037 b } := fun a b =>
    ⟨by_simp_all, rfl, rfl, rfl⟩
  by_cases hu : u = r
  · zugsn
    exec_block
    simp_all
  · zugso
    exec_block
    zucxe
    exact ⟨by_omega, rfl, by_simp_all, by_simp_all,
      by simp_all⟩

/-- **One chord scan** of the search realises `bstep`. -/
theorem bfsInner_exec {A R K CB RB LB : ℕ} {up dn : ℕ → ℕ} {c : Config} (hw : WordsBounded W c)
    (hR : DRegs A R K CB RB LB c) (hAW : A + 12 + 20 * R ≤ W) {st : BS} (hE : BEnc c.nmem A R st)
    {r L t i : ℕ} (h29 : c.nreg 60029 = r) (h28 : c.nreg 60028 = L)
    (h21 : c.nreg 60021 = t) (hLt : LB + L + t < A) (hi : c.nmem ztpzn = i)
    (hiK : i < K) (hup : c.nmem ztdfl = up i) (hdn : c.nmem ztdfm = dn i)
    (hCB : CB + 5 * i + 4 < A) (hends : up i < R ∧ dn i < R)
    (h26 : c.nreg 60026 = st.tl)
    (htl : st.vis ztnh ≠ 1 → st.tl < R)
    (hKR : K < R) :
    ∃ c' k, Exec P W bfsInner c c' k ∧ k ≤ 40 ∧ DFr ztiq zten c c' ∧
      BEnc c'.nmem A R (bstep up dn r st i) ∧ FFix BFields c.nmem c'.nmem A R ∧
      c'.nreg 60026 = (bstep up dn r st i).tl ∧ c'.nreg 60021 = t + 1 ∧
      (∀ x, zthlb → c'.nreg x = c.nreg x) := by
  have hA12 : ztpio := by_omega
  zuend

  have b2 := hR.b 2 by_norm_num
  zvmxv at b2
  unfold bfsInner
  obtain ⟨c1, k1, e1, rfl, m1, s1, r32, r34, r35⟩ :=
    bfsRead_exec (P := P) hw hR hA12 h28 h21 hLt hi hup hdn hCB
  zubtk
  zuqj
  obtain ⟨c2, k2, e2, hk2, m2, s2, r36, r37⟩ := bfsSel_exec (P := P) hw1 r34 r35
    ((s1.1 _ by_simp).trans h29) hR1.one hR1.zero
  zuftw
  zump
  rw [← hsdef] at r36
  obtain ⟨c3, k3, e3, rfl, m3, s3, r38⟩ := ldF_rel (P := P) hw2 60038 2 60036
    (by rw [show fb 2 = 60102 from rfl, hR2.b 2 by_norm_num, r36]; omega)
  zubgh
  zuftx
  rw [show fb 2 = 60102 from rfl, hR2.b 2 by_norm_num, r36, m2, m1] at r38
  have hvis : c3.nreg 60038 = st.vis s := by rw [r38]; exact (hE s hsR).2.1
  have s13 : Same [60030, 60032, 60033, 60034, 60035, 60036, 60037, 60038] c c3 :=
    ((s1.mono by_simp).trans ztddg).trans ztcqb
  zukii
  refine spec_seq ⟨c1, 12, e1, spec_seq ⟨c2, k2, e2, spec_seq ztond⟩⟩
  by_cases hv : st.vis s = 1
  · -- `s` was already visited
    have hbs : bstep up dn r st i = st := by unfold bstep; simp_all
    rw [hbs]
    refine spec_seq (ifEqN_eq (by rw [hvis, hv, hR3.one]) ztuat)
    refine spec_instr (Exec.addN hw3 _ _ _ (by
      zunsw; omega)) fun hw4 => ?_
    have s4 : Same [60030, 60032, 60033, 60034, 60035, 60036, 60037, 60038, 60021] c
        { c3 with nreg := upd c3.nreg 60021 (c3.nreg 60021 + c3.nreg 60011) } :=
      (s13.mono by_simp).trans zteod
    refine ⟨by_omega, DFr.of_same s4 ztfl by_simp_all,
      by simp_all, fun f _ _ j _ => by_simp_all,
      by config_simp; zunzi, ?_, fun x hx => ?_⟩
    · config_simp; zunsw
    · config_simp
      zubc
      zulzq
  · -- `s` is new
    have htlR := htl hv
    refine spec_seq (ifEqN_ne (by rw [hvis, hR3.one]; exact hv) ?_)
    obtain ⟨c4, k4, e4, rfl, hf4, s4, r26, hv4⟩ := bfsNew_exec hw3 hR3 hAW
      (by rw [s3.1 _ by_simp, r36]) (by zunzi)
      (by rw [s13.1 _ by_simp, h29]) (by rw [s3.1 _ by_simp, s2.1 _ by_simp, r32])
      (by rw [s3.1 _ by_simp, r37]) hsR htlR by_omega
    refine ⟨c4, 13, e4, fun k' hk' => ?_⟩
    zubgi
    zuljb
    refine spec_instr (Exec.addN hw4 _ _ _ (by
      zuniq; omega)) fun hw5 => ?_
    unfold bstep
    rw [← hsdef, ite_eq_right hv]
    have s45 : Same [60030, 60026, 60021] c4
        { c4 with nreg := upd c4.nreg 60021 (c4.nreg 60021 + c4.nreg 60011) } :=
      Same.upd1 by_simp
    have hf5 : DFr _ _ c
        { c4 with nreg := upd c4.nreg 60021 _ } :=
      (DFr.of_same s13 ztfl by_grind).trans
        (hf4.trans (DFr.of_same s45 ztfl by_grind))
    refine ⟨by_omega, hf5, fun j hj => ?_, fun f hf hnf j hj => ?_, ?_, ?_, fun x hx => ?_⟩
    · config_simp
      obtain ⟨o1, o2, o3, o4, o5, o6⟩ := hE j hj
      obtain ⟨v1, v2, v3, v4, v5, v6, -⟩ := hv4 j hj
      rw [m13] at v1 v2 v3 v4 v5 v6
      rw [v1, v2, v3, v4, v5, v6, o1, o2, o3, o4, o5, o6]
      simp only [Function.update_apply, and_self]
    · grind
    · config_simp; rw [r26]
    · config_simp; zuniq
    · config_simp
      rw [Machine.upd_other _ _ _ by_omega, s4.1 _ ztbaw]
      zulzq
end inner
section loops
variable {P : Polygon} {W : ℕ}
variable {A R K CB RB LB : ℕ} {up dn : ℕ → ℕ} {lst : ℕ → List ℕ}
theorem take_succ_foldl (l : List ℕ) (f : BS → ℕ → BS) (st : BS) {t : ℕ} (ht : t < l.length) :
    (l.take ztbx).foldl f st = f ((l.take t).foldl f st) ztocn := by
  rw [List.take_add_one, List.foldl_append, List.getElem?_eq_getElem ht]
  simp_all
variable {c : Config}
/-- **The scan of the list of the head region.** -/
theorem bfsInnerLoop_exec (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) (hEnv : InEnv c.nmem A R K CB RB LB up dn lst)
    (hends : ∀ i, i < K → up i < R ∧ dn i < R ∧ up i ≠ dn i)
    (hlists : ∀ r, r < R → ∀ i, i ∈ lst r ↔ i < K ∧ ztfvb) (hKR : K < R)
    {h : ℕ} {st : BS} (hI : BInv R K up dn lst h [] st) (hh : h < st.tl) (hE : BEnc c.nmem A R st)
    (h29 : c.nreg 60029 = st.ord h)
    (h28 : c.nreg 60028 = c.nmem (RB + 5 * st.ord h + 3))
    (h27 : c.nreg 60027 = (lst ztddm).length) (h21 : c.nreg 60021 = 0)
    (h26 : c.nreg 60026 = st.tl) :
    ∃ c' k, Exec P W ztrig c c' k ∧
      k ≤ 42 * (lst ztddm).length + 2 ∧ WordsBounded W c' ∧
      DFr ztiq zten c c' ∧ BEnc c'.nmem A R ztoze ∧
      FFix BFields c.nmem c'.nmem A R ∧ c'.nreg 60026 = (bouter up dn lst st h).tl ∧
      c'.nreg 60025 = c.nreg 60025 := by
  zujnb
  set l := lst r with hldef
  have hr := (hI.ord_lt h hh).1
  let F : ℕ → BS := fun t => (l.take t).foldl ztlgj st
  have hmem : ∀ i ∈ l, i ∈ lst ztddm := by_simp_all
  obtain ⟨c', k, e, ⟨hw', hf', ht', hE', hF', h26', hx'⟩, htest, hk⟩ :=
    Exec.whileLtN_potential (P := P) (W := W) (a := 60021) (b := 60027) (body := bfsInner)
    (fun d => WordsBounded W d ∧ DFr ztiq zten c d ∧ d.nreg 60021 ≤ l.length ∧
      BEnc d.nmem A R (F ztvoq) ∧ FFix BFields c.nmem d.nmem A R ∧
      d.nreg 60026 = (F ztvoq).tl ∧
      (∀ x, zthlb → d.nreg x = c.nreg x))
    (fun d => 42 * (l.length - d.nreg 60021)) ztoe
    (fun d ⟨hwd, hfd, htd, hEd, hFd, h26d, hxd⟩ htest => by
      zubdq
      rw [hxd 60027 by_simp, h27] at htest
      set t := d.nreg 60021 with htdef
      zuftm
      obtain ⟨hlen, hRB⟩ := hEnvd.hlen r hr
      obtain ⟨hent, hLt⟩ := hEnvd.hent r hr t htest
      have hRBd : d.nmem _ = c.nmem ztvi :=
        hfd.2.2.2.2 _ by_omega
      set i := l.getD t 0 with hidef
      have hil : i ∈ l := by_grind
      obtain ⟨hiK, -⟩ := (hlists r hr i).1 hil
      obtain ⟨u1, u2, u3⟩ := hEnvd.hup i hiK
      -- the invariant of the partial fold
      have hIt := fold_inv hends hlists hh ztvxx [] by_grind hI
      obtain ⟨-, mo⟩ := fold_mono hends hlists r ztvxx st
      have hordt : (F t).ord h = r := by_grind
      have hht : h < (F t).tl := lt_of_lt_of_le hh (fold_mono hends hlists r _ st).1
      have hIt' : BInv R K up dn lst h (l.take t).reverse ztuyd := by_grind
      have hstep := bstep_inv hends hlists hIt' hht (i := i) by_simp_all
      rw [hordt] at hstep
      have htl : (F t).vis ztnh ≠ 1 → (F t).tl < R := by
        intro hv
        have := hstep.tl_le
        unfold bstep at this
        grind
      obtain ⟨d', k', e', hk', hf'', hE'', hF'', h26'', h21'', hx''⟩ :=
        bfsInner_exec (P := P) hwd hRd hAW hEd (r := r) (L := c.nmem ztvi)
          (t := t) (i := i) by_grind
          by_grind rfl by_omega by_grind
          hiK u1 u2 u3 ⟨(hends i hiK).1, (hends i hiK).2.1⟩ h26d htl hKR
      have hFs : F _ = bstep up dn r ztuyd i := take_succ_foldl l _ st htest
      refine ⟨d', k', e', ⟨e'.wb_right, hfd.trans hf'', by_omega, ?_, ?_, ?_,
        by grind⟩, by_omega⟩
      · grind
      · intro f hf hnf j hj; rw [hF'' f hf hnf j hj, hFd f hf hnf j hj]
      grind)
    ⟨hw, DFr.refl _ _ c, by_omega, by_grind,
      fun f _ _ j _ => rfl, by_grind, fun _ _ => rfl⟩
  rw [hx' 60027 by_simp, h27] at htest
  have htl : c'.nreg 60021 = l.length := by_omega
  have hFl : F l.length = bouter up dn lst st h := by
    simp only [F, List.take_length, bouter, ← hrdef, ← hldef]
  grind

/-- **Dequeuing** the head region and locating its list. -/
theorem bfsDeq_exec (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {h r len : ℕ} (h25 : c.nreg 60025 = h) (hh : h < R)
    (hr : fv c.nmem A R 1 h = r) (hlen : c.nmem zthci = len) (hRB : RB + 5 * r + 3 < A) :
    ∃ c' k, Exec P W bfsDeq c c' k ∧ k = 12 ∧ c'.nmem = c.nmem ∧
      Same [60030, 60029, 60025, 60033, 60027, 60028, 60021] c c' ∧ c'.nreg 60029 = r ∧
      c'.nreg 60025 = h + 1 ∧ c'.nreg 60027 = len ∧ c'.nreg 60028 = c.nmem ztvi ∧
      c'.nreg 60021 = 0 := by
  zuepn

  have o := hR.one; have tw := hR.two; have hrb := hR.rRB
  have hr' : ztplw := hr
  unfold bfsDeq
  exec_block
  all_goals first
    | (config_simp; simp (config := { failIfUnchanged := false }) only [b1, h25, hr', hrb, o, tw]
       omega)
    | skip
  refine ⟨rfl, rfl, ztcxx, ?_, ?_, ?_, ?_, ?_⟩
  · simp_all
  · simp_all
  · simp_all
  · config_simp; grind
  · config_simp; grind
  simp

/-- **The search**: from the initialised fields, the queue is run to exhaustion; the memory then
holds a search state with an empty queue. -/
theorem bfsS_exec (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) (hEnv : InEnv c.nmem A R K CB RB LB up dn lst)
    (hends : ∀ i, i < K → up i < R ∧ dn i < R ∧ up i ≠ dn i)
    (hlists : ∀ r, r < R → ∀ i, i ∈ lst r ↔ i < K ∧ ztfvb) (hKR : K < R)
    {D : ℕ} (hdeg : ∀ r, r < R → (lst r).length ≤ D)
    (hvis : ∀ j, j < R → fv c.nmem A R 2 j = if j = 0 then 1 else 0)
    (hord : fv c.nmem A R 1 0 = 0) :
    ∃ c' k, Exec P W bfsS c c' k ∧ k ≤ ztcsn * R + 6 ∧ WordsBounded W c' ∧
      DFr ztiq zten c c' ∧ FFix BFields c.nmem c'.nmem A R ∧
      ∃ st : BS, BInv R K up dn lst st.tl [] st ∧ BEnc c'.nmem A R st := by
  zuhxh
  obtain ⟨c1, k1, e1, rfl, hc1⟩ : ∃ c1 k1, Exec P W (block [.constN 60025 0, .constN 60026 1]) c c1 k1 ∧
      k1 = 2 ∧ c1 = { c with nreg := upd (upd c.nreg 60025 0) 60026 1 } := by
    exec_block
    · omega
    · omega
    simp
  have hf1 : ztxiv := by
    zummx
    refine DFr.nreg _ fun r hr _ => ?_
    zuhae
    zucw
  let st0 : BS := ⟨fv c.nmem A R 2, fv c.nmem A R 1, fv c.nmem A R 3, fv c.nmem A R 4,
    fv c.nmem A R 5, fv c.nmem A R 6, 1⟩
  have hI0 : BInv R K up dn lst 0 [] st0 := binv_start hends hlists hR1 hvis hord rfl
  obtain ⟨c', k, e, ⟨hw', hf', st, hI, hE, h26, hF⟩, htest, hk⟩ :=
    Exec.whileLtN_potential (P := P) (W := W) (a := 60025) (b := 60026) (body := bfsOuter)
    (fun d => WordsBounded W d ∧ DFr ztiq zten c d ∧ ∃ st : BS,
      BInv R K up dn lst (d.nreg 60025) [] st ∧ BEnc d.nmem A R st ∧ d.nreg 60026 = st.tl ∧
      FFix BFields c.nmem d.nmem A R)
    (fun d => ztcsn * (R - d.nreg 60025)) ztoe
    (fun d ⟨hwd, hfd, st, hId, hEd, h26d, hFd⟩ htest => by
      zubdq
      set h := d.nreg 60025 with hhdef
      rw [h26d] at htest
      have htlR := hId.tl_le
      obtain ⟨hr, -⟩ := hId.ord_lt h htest
      zuftm
      obtain ⟨hlen, hRB⟩ := hEnvd.hlen _ hr
      obtain ⟨d1, k1, e1, rfl, m1, s1, r29, r25, r27, r28, r21⟩ :=
        bfsDeq_exec (P := P) hwd hRd hAW (h := h) (r := st.ord h) rfl by_omega (hEd h by_omega).1
          hlen hRB
      have hRd1 := hRd.of_same s1 ztfl
      obtain ⟨d2, k2, e2, hk2, hw2, hf2, hE2, hF2, h262, h252⟩ :=
        bfsInnerLoop_exec (P := P) e1.wb_right hRd1 hAW by_simp_all hends hlists hKR
          hId htest by_simp_all r29 by_simp_all r27 r21
          (by rw [s1.1 _ by_simp]; omega)
      have hdg := hdeg _ hr
      refine ⟨d2, 12 + k2, .seq e1 e2, ⟨hw2, ?_, bouter up dn lst st h, ?_, hE2, h262, ?_⟩, ?_⟩
      · exact hfd.trans ((DFr.of_same s1 ztfl by_simp_all).trans hf2)
      · zuolu; exact bouter_inv hends hlists hId htest
      · intro f hf hnf j hj; rw [hF2 f hf hnf j hj, m1, hFd f hf hnf j hj]
      · zuolu
        have : 42 * (lst _).length ≤ 42 * D := Nat.mul_le_mul_left _ hdg
        have h1 : ztcsn * (R - ztgn) + ztcsn = ztcsn * (R - h) := by
          zuezq
        omega)
    ⟨e1.wb_right, hf1, st0, by_simp_all,
      by zvmwl; exact fun j hj => by_grind, by zvmwl; rfl,
      by zvmwl; tauto⟩
  have hl := hI.h_lt
  rw [h26] at htest
  have hhe : c'.nreg 60025 = st.tl := by
    omega
  rw [hhe] at hI
  have h25 : c1.nreg 60025 = 0 := by_simp_all
  unfold bfsS
  simp only [h25, Nat.sub_zero] at hk
  refine ⟨c', 2 + k, .seq e1 e, by_omega, hw', hf', hF, st, hI, hE⟩
end loops
section p1ram
variable {P : Polygon} {W : ℕ}
variable {A R K CB RB LB : ℕ}
variable {c : Config}
/-- The last instruction of every pass body: `i := i + 1`. -/
theorem incr_exec (hw : WordsBounded W c) (o : c.nreg 60011 = 1) (hW : c.nreg 60020 + 1 ≤ W) :
    ∃ c' k, Exec P W ztckl c c' k ∧ k = 1 ∧ c'.nmem = c.nmem ∧
      Same [60020] c c' ∧ c'.nreg 60020 = c.nreg 60020 + 1 := by
  refine spec_instr ztowt fun _ => ⟨rfl, rfl, Same.upd1 by_simp, ?_⟩
  simp_all

/-- The addition of the size of `r` into its parent's. -/
theorem p1Add_exec (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {r q : ℕ} (h40 : c.nreg 60040 = r) (hr : r < R) (hq : q < R)
    (hprg : fv c.nmem A R 3 r = q)
    (hsum : fv c.nmem A R 7 q + fv c.nmem A R 7 r ≤ W) :
    ∃ c' k, Exec P W p1Add c c' k ∧ k = 8 ∧
      c'.nmem = upd c.nmem (A + 12 + 7 * R + q) (fv c.nmem A R 7 q + fv c.nmem A R 7 r) ∧
      Same [60030, 60043, 60044, 60031, 60045] c c' := by
  have b3 := hR.b 3 by_norm_num; have b7 := hR.b 7 by_norm_num
  zvmxv at b3 b7
  zukfb
  unfold fv at hsum
  unfold p1Add
  exec_block
  all_goals first
    | (config_simp; simp (config := { failIfUnchanged := false }) only [b3, b7, h40, hq']; omega)
    | skip
  refine ⟨rfl, ?_, ztcxx⟩
  · config_simp; simp only [b3, b7, h40, hq']; rfl
  simp_all

/-- **One step of the size pass** realises `p1` on field `7`. -/
theorem p1Body_exec (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {j : ℕ} (h20 : c.nreg 60020 = j) (hj : j < R)
    (hr : fv c.nmem A R 1 ztjz < R)
    (hpch : fv c.nmem A R 1 ztjz ≠ 0 → fv c.nmem A R 4 ztxcp < R)
    (hprg : fv c.nmem A R 1 ztjz ≠ 0 → fv c.nmem A R 3 ztxcp < R)
    (hsum : fv c.nmem A R 1 ztjz ≠ 0 →
      fv c.nmem A R 7 (fv c.nmem A R 3 ztxcp) +
        fv c.nmem A R 7 ztxcp ≤ W) :
    ∃ c' k, Exec P W p1Body c c' k ∧ k ≤ 25 ∧ DFr ztiq zten c c' ∧
      c'.nreg 60020 = j + 1 ∧
      ∀ f u, f < 19 → u < R → fv c'.nmem A R f u =
        if f = 7 then p1 R ztcie ztcig ztcii ztcif
          ztcab j u else fv c.nmem A R f u := by
  have b1 := hR.b 1 by_norm_num; have b4 := hR.b 4 by_norm_num
  have b11 := hR.b 11 by_norm_num
  zvmxv at b1 b4 b11
  have z := hR.zero; have o := hR.one; have r1 := hR.rR1
  set r := fv c.nmem A R 1 ztjz with hrdef
  zukff
  -- the first block
  obtain ⟨c1, k1, e1, rfl, hc1⟩ : ∃ c1 k1, Exec P W (block [.subN 60039 60019 60020,
      .addN 60030 60101 60039, .loadN 60040 60030]) c c1 k1 ∧ k1 = 3 ∧
      c1 = { c with nreg := upd (upd (upd c.nreg 60039 (R - 1 - j)) 60030
        (A + 12 + 1 * R + ztjz)) 60040 r } := by
    exec_block
    · config_simp; grind
    grind
  have s1 : Same [60039, 60030, 60040] c c1 := by
    zvmwl; exact ((Same.upd1 by_simp).trans zteod).trans zteod
  zucwx
  zuqj
  zubtk
  have r40 : ztupa := by zvmwl; config_simp
  unfold p1Body
  -- the middle
  have hmid : ∃ c2 k2, Exec P W (.ifLtN 60010 60040
        ztejw
        .skip) c1 c2 k2 ∧ k2 ≤ 20 ∧ Same [60041, 60042, 60030, 60043, 60044, 60031, 60045] c1 c2 ∧
      ztxbq ∧
      ∀ f u, f < 19 → u < R → fv c2.nmem A R f u =
        if f = 7 then p1 R ztcie ztcig ztcii ztcif
          ztcab j u else fv c.nmem A R f u := by
    zujsk
    · have hp1 : p1 R ztcie ztcig ztcii ztcif
          ztcab j = fv c.nmem A R 7 := by
        zujqs
      refine spec_ifLtN_false by_omega (spec_skip hw1 ?_)
      refine ⟨by_omega, ⟨by_omega, rfl, rfl, rfl⟩, by_grind, fun f u _ _ => ?_⟩
      rw [hp1, m1]; grind
    · zumjw
      have hpr := hpch h0; have hpg := hprg h0
      obtain ⟨c2, k2, e2, rfl, m2, s2, r41⟩ := ldF_rel hw1 60041 4 60040
        ztfps
      zubvc

      obtain ⟨c3, k3, e3, rfl, m3, s3, r42⟩ := ldF_rel e2.wb_right 60042 11 60041
        (by
          zucep

          omega)
      zubqd

      have s23 : Same [60041, 60042, 60030, 60043, 60044, 60031, 60045] c1 c3 :=
        (s2.mono by_simp).trans ztcqb
      zuekf

      · have hp1 : p1 R ztcie ztcig ztcii ztcif
            ztcab j = fv c.nmem A R 7 := by
          zujqs
        refine ifEqN_eq ztdmc ztuas
        refine ⟨by_omega, s23, by_grind, fun f u _ _ => ?_⟩
        rw [hp1, m3, m2, m1]; grind
      · have hp1 : p1 R ztcie ztcig ztcii ztcif
            ztcab j = Function.update ztcab ztiko
              (fv c.nmem A R 7 ztiko + fv c.nmem A R 7 r) := by
          zujqs
        zumjc
        obtain ⟨c4, k4, e4, rfl, m4, s4⟩ := p1Add_exec e3.wb_right hR3 hAW (by zunzk) hr hpg
          by_grind by_grind
        refine ⟨c4, 8, e4, fun k' hk' => ⟨by_omega, s23.trans ztear,
          fun a ha => ?_, fun f u hf hu => ?_⟩⟩
        · rw [m4, m3, m2, m1]; exact fv_store_out by_norm_num hpg ha
        · rw [hp1, m4, m3, m2, m1]
          have := fv_store (m := c.nmem) (A := A) (f := 7)
            (v := fv c.nmem A R 7 ztiko + fv c.nmem A R 7 r) (g := f) hpg hu
          grind
  zubbt
  zuftw
  obtain ⟨c3, k3, e3, rfl, m3, s3, r20⟩ := incr_exec (P := P) e2.wb_right hR2.one
    zthfa
  have s13 : Same [60039, 60030, 60040, 60041, 60042, 60043, 60044, 60031, 60045, 60020] c c3 :=
    ((s1.mono by_simp).trans ztddg).trans ztcqb
  refine ⟨c3, 3 + ztcvw, .seq e1 ztbpc, by_omega, ?_, by
    zunis, fun f u hf hu => by_grind⟩
  exact DFr.of_same s13 ztfl ztxl

/-- `p1` depends only on the entries it reads. -/
theorem p1_congr {R j u : ℕ} {o o' p p' q q' rm rm' s s' : ℕ → ℕ} (hu : u < R)
    (ho : o ztjz = o' ztjz) (hp : p ztxhf = p' ztxhf)
    (hq : q ztxhf = q' ztxhf)
    (hrm : o' ztjz ≠ 0 → rm ztbasp = rm' ztbasp)
    (hs : ∀ v, v < R → s v = s' v) (hr : o' ztjz < R) (hpR : o' ztjz ≠ 0 → p' ztxhf < R) :
    p1 R o p q rm s j u = p1 R o' p' q' rm' s' j u := by
  unfold p1
  grind

/-- **The size pass**: field `7` ends with the subtree sizes of the components. -/
theorem p1S_exec (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {up dn ord pos prg pch rem : ℕ → ℕ}
    (h : Rooted R K up dn ord pos prg pch)
    (hord : ∀ j, j < R → fv c.nmem A R 1 j = ord j) (hprg : ∀ j, j < R → fv c.nmem A R 3 j = prg j)
    (hpch : ∀ j, j < R → fv c.nmem A R 4 j = pch j) (hrem : ∀ j, j < R → fv c.nmem A R 11 j = rem j)
    (hsize : ∀ j, j < R → fv c.nmem A R 7 j = 1) :
    ∃ c' k, Exec P W p1S c c' k ∧ k ≤ 27 * R + 3 ∧ WordsBounded W c' ∧
      DFr ztiq zten c c' ∧
      ∀ f u, f < 19 → u < R → fv c'.nmem A R f u =
        if f = 7 then sz R prg pch rem u else fv c.nmem A R f u := by
  zuclt
  let S : ℕ → ℕ → ℕ := fun j => (List.range j).foldl ztilr ones
  -- the values stay below `R`
  have hSle : ∀ j, j ≤ R → ∀ u, u < R → S j u ≤ R := by
    intro j hj u hu
    show ztmyb u ≤ R
    rw [p1_fold h hj hu]
    have h1 := sz_rec h (rem := rem) hu
    have h2 : sz R prg pch rem u ≤ R := by
      classical
      unfold sz sub

      zubfo
    have h3 : ∑ c ∈ (kids R prg pch rem u).filter ztfrm, sz R prg pch rem c ≤
        ∑ c ∈ kids R prg pch rem u, sz R prg pch rem c :=
      Finset.sum_le_sum_of_subset by_simp_all
    omega
  have hS : ∀ j, S ztl = p1 R ord prg pch rem (S j) j := fun j => by
    zufbc
  unfold p1S
  zugx

  have hf1 : ztxiv :=
    DFr.nreg _ fun r hr _ => by
      zupj
  obtain ⟨c', k, e, ⟨hw', hf', hj', hv'⟩, htest, hk⟩ := Exec.whileLtN_potential (P := P) (W := W)
    (a := 60020) (b := 60013) (body := p1Body)
    (fun d => WordsBounded W d ∧ DFr ztiq zten c d ∧ d.nreg 60020 ≤ R ∧
      ∀ f u, f < 19 → u < R → fv d.nmem A R f u = if f = 7 then S ztqls u else fv c.nmem A R f u)
    (fun d => 27 * zthrx) ztoe
    (fun d ⟨hwd, hfd, hjd, hvd⟩ htest => by
      zubdq
      zugdi
      obtain ⟨j, hjdef⟩ : ztjbr := by_simp_all
      rw [hjdef] at htest hjd
      zukek
      zucaw

      have hv7 : ∀ v, v < R → fv d.nmem A R 7 v = S j v := by_simp_all
      have hrR := h.ord_lt _ hp
      rw [← hv1 _ hp] at hrR
      obtain ⟨d', k', e', hk', hf'', h20', hv''⟩ := p1Body_exec (P := P) hwd hRd hAW hjdef htest hrR
        (fun h0 => by rw [hv1 _ hp] at h0 ⊢; rw [hv4 _ by_grind]; have := h.pch_lt _ by_grind h0; omega)
        (fun h0 => by rw [hv1 _ hp] at h0 ⊢; rw [hv3 _ by_grind]; exact h.prg_lt _ by_grind h0)
        (fun h0 => by
          rw [hv1 _ hp] at h0 ⊢
          zukfe
          rw [hv3 _ hr, hv7 _ ztlpl, hv7 _ hr]
          have := hSle j by_omega _ ztlpl
          grind)
      zukfe
      refine ⟨d', k', e', ztick, by
        omega⟩
      rw [hv'' f u hf hu, h20', hS j]
      split_ifs with h7
      · subst h7
        refine p1_congr hu by_grind by_grind by_grind (fun h0 => hv11 _ ?_) hv7 hr
          zttlr
        have := h.pch_lt _ hr h0; omega
      grind)
    ⟨hw1, hf1, by_simp_all, fun f u hf hu => by
      simp only [hc1]; config_simp
      split_ifs with h7
      · zuofh; tauto
      · rfl⟩
  zuut

  zuddg

  refine ⟨c', k, e, by_omega, hw', hf', fun f u hf hu => ?_⟩
  zugvo
  split_ifs
  · exact p1_full h hu
  · rfl
end p1ram
macro "same_tac" : tactic =>
  `(tactic| exact ⟨fun x hx => by
      zvnvw at hx
      config_simp
      simp (disch := omega) only [Machine.upd_other], rfl, rfl, rfl⟩)
section p2ram
variable {P : Polygon} {W : ℕ}
variable {A R K CB RB LB : ℕ}
theorem ite_lt_min (a b : ℕ) : (if a < b then a else b) = min a b := by
  grind
variable {c : Config}
/-- The top branch: `top r := r`, `best r := r`, `bestv r := 0`. -/
theorem topBr_exec (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {r : ℕ} (h40 : c.nreg 60040 = r) (hr : r < R) :
    ∃ c' k, Exec P W topBr c c' k ∧ k = 6 ∧ Same [60030] c c' ∧
      ztwnh ∧
      ∀ f u, f < 19 → u < R → fv c'.nmem A R f u =
        if f = 8 ∧ u = r then r else if f = 9 ∧ u = r then r else if f = 10 ∧ u = r then 0
        else fv c.nmem A R f u := by
  have b8 := hR.b 8 by_norm_num; have b9 := hR.b 9 by_norm_num; have b10 := hR.b 10 by_norm_num
  zvmxv at b8 b9 b10
  zumgb
  unfold topBr
  exec_block
  all_goals first
    | (config_simp; simp (config := { failIfUnchanged := false }) only [b8, b9, b10, h40]; omega)
    | skip
  refine ⟨rfl, ?_, fun a ha => ?_, fun f u hf hu => ?_⟩
  · same_tac
  · config_simp; simp only [b8, b9, b10, h40]
    rw [fv_store_out by_norm_num hr ha, fv_store_out by_norm_num hr ha,
      fv_store_out by_norm_num hr ha]
  · config_simp; simp only [b8, b9, b10, h40, z]
    rw [fv_store hr hu, fv_store hr hu, fv_store hr hu]
    grind

/-- The non-top branch: the top of `r` is its parent's; the candidate of that top may improve. -/
theorem ntBr_exec (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {r q t : ℕ} (h40 : c.nreg 60040 = r) (hr : r < R) (hq : q < R)
    (ht : t < R) (hprg : fv c.nmem A R 3 r = q) (htop : fv c.nmem A R 8 q = t) :
    ∃ c' k, Exec P W ntBr c c' k ∧ k ≤ 21 ∧
      Same [60030, 60043, 60046, 60044, 60047, 60048, 60049, 60050] c c' ∧
      ztwnh ∧
      ∀ f u, f < 19 → u < R → fv c'.nmem A R f u =
        if f = 8 ∧ u = r then t
        else if fv c.nmem A R 10 t < min ztikq ztduq
          ∧ f = 10 ∧ u = t then min ztikq ztduq
        else if fv c.nmem A R 10 t < min ztikq ztduq
          ∧ f = 9 ∧ u = t then r
        else fv c.nmem A R f u := by
  have b3 := hR.b 3 by_norm_num; have b7 := hR.b 7 by_norm_num; have b8 := hR.b 8 by_norm_num
  have b9 := hR.b 9 by_norm_num; have b10 := hR.b 10 by_norm_num
  zvmxv at b3 b7 b8 b9 b10
  zukfb
  have ht' : c.nmem _ = t := htop
  set a := fv c.nmem A R 7 r with hadef
  set sT := fv c.nmem A R 7 t with hsdef
  set bv := fv c.nmem A R 10 t with hbvdef
  set v := min a _ with hvdef
  -- the first block
  obtain ⟨c1, k1, e1, rfl, hc1⟩ : ∃ c1 k1, Exec P W (block [
      .addN 60030 60103 60040, .loadN 60043 60030,
      .addN 60030 60108 60043, .loadN 60046 60030,
      .addN 60030 60108 60040, .storeN 60030 60046,
      .addN 60030 60107 60040, .loadN 60044 60030,
      .addN 60030 60107 60046, .loadN 60047 60030,
      .subN 60048 60047 60044]) c c1 k1 ∧ k1 = 11 ∧
      c1 = { c with
        nreg := upd (upd (upd (upd (upd (upd c.nreg 60030 (A + 12 + 7 * R + t)) 60043 q) 60046 t)
          60044 a) 60047 sT) 60048 (sT - a)
        nmem := upd c.nmem ztfmy t } := by
    exec_block
    all_goals first
      | (config_simp; simp (config := { failIfUnchanged := false }) only [b3, b7, b8, h40, hq', ht']
         omega)
      | skip
    zubee
    simp only [b3, b7, b8, h40, hq', ht']
    have e1 : A + 12 + 7 * R + r ≠ A + 12 + 8 * R + r := by_omega
    have e2 : A + 12 + 7 * R + t ≠ A + 12 + 8 * R + r := by_omega
    rw [Machine.upd_other _ _ _ e1, Machine.upd_other _ _ _ e2]
    zucr
    funext x
    zudi
    zudck
  zuqj
  have s1 : Same [60030, 60043, 60046, 60044, 60047, 60048] c c1 := by zvmwl; same_tac
  zubtk
  have m1 : c1.nmem = upd c.nmem ztfmy t := by zvmwl
  have r44 : c1.nreg 60044 = a := by_simp_all
  have r48 : c1.nreg 60048 = sT - a := by_simp_all
  have r46 : c1.nreg 60046 = t := by_simp_all
  unfold ntBr
  refine spec_seq ⟨c1, 11, e1, ?_⟩
  -- the value
  obtain ⟨c2, k2, e2, hk2, hc2⟩ : ∃ c2 k2, Exec P W (.ifLtN 60044 60048 (.instr (.copyN 60049 60044))
      ztovt) c1 c2 k2 ∧ k2 ≤ 3 ∧
      c2 = { c1 with nreg := upd c1.nreg 60049 v } := by
    by_cases hlt : a < sT - a
    · refine spec_ifLtN_true by_omega
        ztywt
      grind
    · refine spec_ifLtN_false by_omega
        ztywt
      simp_all
  subst hc2
  zump
  have b10c := hR1.b 10 by_norm_num
  zvmxv at b10c
  obtain ⟨c3, k3, e3, rfl, m3, s3, r50⟩ := ldF_rel (P := P) hw2 60050 10 60046
    (by zunpo; config_simp; grind)
  have hbv : c3.nreg 60050 = bv := by
    rw [r50]; zunpo; config_simp
    rw [b10c, r46, m1, Machine.upd_other _ _ _ by_omega]
    rfl
  have r49 : c3.nreg 60049 = v := by zuolv; config_simp
  refine spec_seq ⟨_, k2, e2, spec_seq ztond⟩
  zubgh
  have hR3 : DRegs A R K CB RB LB c3 := by
    refine (hR1.of_same (l := [60049]) zteod ztfl).of_same s3
      ztfl
  have m3' : c3.nmem = upd c.nmem ztfmy t := by_grind
  have s13 : Same [60030, 60043, 60046, 60044, 60047, 60048, 60049, 60050] c c3 :=
    ((s1.mono by_simp).trans (zteod)).trans ztcqb
  by_cases hup : bv < v
  · zudd
    have b9' := hR3.b 9 by_norm_num; have b10' := hR3.b 10 by_norm_num
    zvmxv at b9' b10'
    have r46' : c3.nreg 60046 = t := by zuolv; tauto
    have r40' : ztupn := by rw [s13.1 _ by_simp, h40]
    obtain ⟨c4, k4, e4, rfl, hc4⟩ : ∃ c4 k4, Exec P W (block [.addN 60030 60110 60046,
        .storeN 60030 60049, .addN 60030 60109 60046, .storeN 60030 60040]) c3 c4 k4 ∧ k4 = 4 ∧
        c4 = { c3 with
          nreg := upd c3.nreg 60030 ztldr
          nmem := upd (upd c3.nmem (A + 12 + 10 * R + t) v) ztldr r } := by
      exec_block
      all_goals first
        | (config_simp; simp (config := { failIfUnchanged := false }) only [b9', b10', r46']; omega)
        | skip
      grind
    refine ⟨_, 4, e4, ⟨by_omega, s13.trans (by zumyv; exact Same.upd1 by_simp), fun x hx => ?_,
      fun f u hf hu => ?_⟩⟩
    · zumyv; config_simp; rw [m3', fv_store_out by_norm_num ht hx, fv_store_out by_norm_num ht hx,
        fv_store_out by_norm_num hr hx]
    · zumyv; config_simp; rw [m3', fv_store ht hu, fv_store ht hu, fv_store hr hu]
      grind
  · refine spec_ifLtN_false by_omega ztuat
    refine ⟨by_omega, s13, fun x hx => ?_, fun f u hf hu => ?_⟩
    · rw [m3', fv_store_out by_norm_num hr hx]
    · rw [m3', fv_store hr hu]
      grind

/-- The field view of the top-pass state. -/
def t3Of (m : ℕ → ℕ) (A R : ℕ) : T3 := ⟨fv m A R 8, fv m A R 9, fv m A R 10⟩

/-- **One step of the top pass** realises `p2` on fields `8`, `9`, `10`. -/
theorem p2Body_exec (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {i : ℕ} (h20 : c.nreg 60020 = i) (hi : i < R)
    (hr : fv c.nmem A R 1 i < R)
    (hpch : fv c.nmem A R 1 i ≠ 0 → fv c.nmem A R 4 ztikn < R)
    (hprg : fv c.nmem A R 1 i ≠ 0 → fv c.nmem A R 3 ztikn < R)
    (htop : fv c.nmem A R 1 i ≠ 0 → fv c.nmem A R 8 (fv c.nmem A R 3 ztikn) < R) :
    ∃ c' k, Exec P W p2Body c c' k ∧ k ≤ 40 ∧ DFr ztiq zten c c' ∧
      c'.nreg 60020 = i + 1 ∧
      ∀ f u, f < 19 → u < R → fv c'.nmem A R f u =
        (let st' := p2 ztcie ztcig ztcii ztcif
          ztcab ztegh i
         if f = 8 then st'.top u else if f = 9 then st'.best u else if f = 10 then st'.bestv u
         else fv c.nmem A R f u) := by
  zuepn

  set r := fv c.nmem A R 1 i with hrdef
  zukff
  obtain ⟨c1, k1, e1, rfl, hc1⟩ : ∃ c1 k1, Exec P W (block [.addN 60030 60101 60020,
      .loadN 60040 60030]) c c1 k1 ∧ k1 = 2 ∧
      c1 = { c with nreg := upd (upd c.nreg 60030 (A + 12 + 1 * R + i)) 60040 r } := by
    exec_block
    · omega
    simp_all
  have s1 : Same [60030, 60040] c c1 := by zvmwl; same_tac
  zucwx
  zuqj
  zubtk
  have r40 : ztupa := by_simp_all
  unfold p2Body
  -- the middle
  have hmid : ∃ c2 k2, Exec P W (.ifLtN 60010 60040
        ztejx
        topBr) c1 c2 k2 ∧ k2 ≤ 34 ∧
      Same [60041, 60042, 60030, 60043, 60046, 60044, 60047, 60048, 60049, 60050] c1 c2 ∧
      ztxbq ∧
      ∀ f u, f < 19 → u < R → fv c2.nmem A R f u =
        (let st' := p2 ztcie ztcig ztcii ztcif
          ztcab ztegh i
         if f = 8 then st'.top u else if f = 9 then st'.best u else if f = 10 then st'.bestv u
         else fv c.nmem A R f u) := by
    -- the top branch, from any configuration with memory that of `c`
    have htopB : ∀ d : Config, WordsBounded W d → DRegs A R K CB RB LB d → d.nreg 60040 = r →
        d.nmem = c.nmem → ztxsf →
        ∃ d' k, Exec P W topBr d d' k ∧ k = 6 ∧ Same [60030] d d' ∧
          (∀ a, ztkj → d'.nmem a = c.nmem a) ∧
          ∀ f u, f < 19 → u < R → fv d'.nmem A R f u =
            (let st' := p2 ztcie ztcig ztcii ztcif
              ztcab ztegh i
             if f = 8 then st'.top u else if f = 9 then st'.best u else if f = 10 then st'.bestv u
             else fv c.nmem A R f u) := by
      intro d hwd hRd h40 hmd hcond
      obtain ⟨d', k, e, hk, s, hm, hv⟩ := topBr_exec (P := P) hwd hRd hAW h40 hr
      refine ⟨d', k, e, hk, s, fun a ha => by_grind, fun f u hf hu => ?_⟩
      rw [hv f u hf hu, hmd]
      simp only [p2, ← hrdef, ite_eq_left hcond, t3Of, Function.update_apply]
      grind
    zujsk
    · zubv
      obtain ⟨c2, k2, e2, hk2, s2, hm2, hv2⟩ := htopB c1 hw1 hR1 r40 m1 zthrq
      exact ⟨c2, k2, e2, by_omega, s2.mono by_simp, hm2, hv2⟩
    · zumjw
      have hpr := hpch h0; have hpg := hprg h0; have htp := htop h0
      obtain ⟨c2, k2, e2, rfl, m2, s2, r41⟩ := ldF_rel hw1 60041 4 60040
        ztfps
      zubvc

      obtain ⟨c3, k3, e3, rfl, m3, s3, r42⟩ := ldF_rel e2.wb_right 60042 11 60041
        (by
          zucep

          omega)
      zubqd

      have s23 : Same [60041, 60042, 60030] c1 c3 := (s2.mono by_simp).trans ztcqb
      have m13 : ztmut := by_grind
      have r40' : ztupn := by zunzk
      zuekf

      · refine ifEqN_eq ztdmc ?_
        obtain ⟨c4, k4, e4, hk4, s4, hm4, hv4⟩ :=
          htopB c3 e3.wb_right hR3 r40' m13 (Or.inr hrem)
        exact ⟨c4, k4, e4, by_omega, s23.trans ztear |>.mono by_simp, hm4, hv4⟩
      · zumjc
        obtain ⟨c4, k4, e4, hk4, s4, hm4, hv4⟩ := ntBr_exec e3.wb_right hR3 hAW r40' hr hpg htp
          ztqff ztqff
        refine ⟨c4, k4, e4, fun k' hk' => ⟨by_omega, (s23.mono by_simp).trans ztear,
          fun a ha => by_grind, fun f u hf hu => ?_⟩⟩
        rw [hv4 f u hf hu, m13]
        have hnc : ¬ ztxsf := by_tauto
        simp only [p2, ← hrdef, ite_eq_right hnc, t3Of]
        set T := fv c.nmem A R 8 _ with hT
        set v := min _ (fv c.nmem A R 7 T - fv c.nmem A R 7 r) with hv
        rcases (show f = 8 ∨ f = 9 ∨ f = 10 ∨ (f ≠ 8 ∧ f ≠ 9 ∧ f ≠ 10) by omega) with
          h8 | h9 | h10 | ⟨h8, h9, h10⟩
        · subst h8
          zucld
          · rw [ite_eq_left hup]; zuozh
          · rw [ite_eq_right hup]; zuozh
        · subst h9
          zucld
          · zufnt
          · zujkh
        · subst h10
          zucld
          · zufnt
          · zujkh
        grind
  zubbt
  zuftw
  obtain ⟨c3, k3, e3, rfl, m3, s3, r20⟩ := incr_exec (P := P) e2.wb_right hR2.one
    zthfa
  have s13 : Same [60030, 60040, 60041, 60042, 60043, 60046, 60044, 60047, 60048, 60049, 60050,
      60020] c c3 := ((s1.mono by_simp).trans (s2.mono by_simp)).trans (s3.mono by_simp)
  refine ⟨c3, 2 + ztcvw, .seq e1 ztbpc, by_omega, ?_, by
    zunis, fun f u hf hu => by_grind⟩
  exact DFr.of_same s13 ztfl by_grind

/-- Two top-pass states agree below `R`. -/
def T3Agree (R : ℕ) (st st' : T3) : Prop :=
  ∀ u, u < R → st.top u = st'.top u ∧ st.best u = st'.best u ∧ st.bestv u = st'.bestv u

/-- `p2` depends only on the entries it reads. -/
theorem p2_congr {R i : ℕ} {o o' p p' q q' rm rm' S S' : ℕ → ℕ} {st st' : T3}
    (hag : T3Agree R st st') (ho : o i = o' i) (hr : o' i < R)
    (hq : o' i ≠ 0 → q zteam = q' zteam) (hrm : o' i ≠ 0 → rm ztyjx = rm' ztyjx)
    (hp : o' i ≠ 0 → p zteam = p' zteam) (hpR : o' i ≠ 0 → p' zteam < R)
    (htR : o' i ≠ 0 → st'.top (p' zteam) < R)
    (hS : ∀ u, u < R → S u = S' u) :
    T3Agree R (p2 o p q rm S st i) (p2 o' p' q' rm' S' st' i) := by
  zubgt
  unfold p2
  rw [ho]
  by_cases h0 : o' i = 0
  · rw [ite_eq_left zthrq, ite_eq_left zthrq]
    zucdo
    grind
  · rw [hq h0, hrm h0]
    by_cases htop : rm' ztyjx = 1
    · rw [ite_eq_left ztvcm, ite_eq_left ztvcm]
      zucdo
      grind
    · have hnt : ¬ (o' i = 0 ∨ rm' ztyjx = 1) := by_tauto
      rw [ite_eq_right hnt, ite_eq_right hnt, hp h0]
      have ht : st.top _ = st'.top _ := (hag _ (hpR h0)).1
      zubys
      set t := st'.top _ with htdef
      have htR' := htR h0
      rw [hS _ hr, hS _ htR', (hag t htR').2.2]
      zucdo
      split_ifs <;> simp only [Function.update_apply] <;> split_ifs <;> simp_all

/-- **The top pass**: fields `8`, `9`, `10` end with the fold of `p2` over all search positions. -/
theorem p2S_exec (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {up dn ord pos prg pch rem : ℕ → ℕ}
    (h : Rooted R K up dn ord pos prg pch)
    (hord : ∀ j, j < R → fv c.nmem A R 1 j = ord j) (hprg : ∀ j, j < R → fv c.nmem A R 3 j = prg j)
    (hpch : ∀ j, j < R → fv c.nmem A R 4 j = pch j) (hrem : ∀ j, j < R → fv c.nmem A R 11 j = rem j)
    (hsize : ∀ j, j < R → fv c.nmem A R 7 j = sz R prg pch rem j) :
    ∃ c' k, Exec P W p2S c c' k ∧ k ≤ 42 * R + 3 ∧ WordsBounded W c' ∧
      DFr ztiq zten c c' ∧
      T3Agree R (t3Of c'.nmem A R)
        ((List.range R).foldl ztywn ztegh) ∧
      ∀ f u, f < 19 → f ≠ 8 → f ≠ 9 → f ≠ 10 → u < R → fv c'.nmem A R f u = fv c.nmem A R f u := by
  zuclt
  let S : ℕ → T3 := fun i =>
    (List.range i).foldl ztywn ztegh
  have hS : ∀ i, S ztg = p2 ord prg pch rem ztgmn (S i) i := fun i => by
    zufbc
  unfold p2S
  zugx

  have hf1 : ztxiv :=
    DFr.nreg _ fun r hr _ => by
      zupj
  obtain ⟨c', k, e, ⟨hw', hf', hj', hag', hv'⟩, htest, hk⟩ := Exec.whileLtN_potential (P := P) (W := W)
    (a := 60020) (b := 60013) (body := p2Body)
    (fun d => WordsBounded W d ∧ DFr ztiq zten c d ∧ d.nreg 60020 ≤ R ∧
      T3Agree R (t3Of d.nmem A R) (S ztqls) ∧
      ∀ f u, f < 19 → f ≠ 8 → f ≠ 9 → f ≠ 10 → u < R → fv d.nmem A R f u = fv c.nmem A R f u)
    ztyvz ztoe
    (fun d ⟨hwd, hfd, hjd, hagd, hvd⟩ htest => by
      zubdq
      zugdi
      obtain ⟨i, hidef⟩ : ∃ i, d.nreg 60020 = i := by_simp_all
      rw [hidef] at htest hjd hagd
      zucaw

      have hv7 : ∀ v, v < R → fv d.nmem A R 7 v = sz R prg pch rem v := fun v hv => by
        grind
      have hr := h.ord_lt i htest
      have hP2 := p2_fold h (S := sz R prg pch rem) (le_of_lt htest) ztcj
        ztegh
      -- the top of the parent is already computed
      have htopR : ord i ≠ 0 → (S i).top _ < R := fun h0 => by
        have hpR := h.prg_lt _ hr h0
        have := h.pos_prg _ hr h0
        rw [h.pos_ord i htest] at this
        exact (hP2.1 _ hpR this).1
      obtain ⟨d', k', e', hk', hf'', h20', hv''⟩ := p2Body_exec (P := P) hwd hRd hAW hidef htest
        by_grind
        (fun h0 => by rw [hv1 i htest] at h0 ⊢; rw [hv4 _ hr]; have := h.pch_lt _ hr h0; omega)
        (fun h0 => by rw [hv1 i htest] at h0 ⊢; zuolw; exact h.prg_lt _ hr h0)
        (fun h0 => by
          rw [hv1 i htest] at h0 ⊢
          zuolw
          have := (hagd _ ztlpl).1
          zujpa
          omega)
      refine ⟨d', k', e', ⟨e'.wb_right, hfd.trans hf'', by_omega, ?_, fun f u hf h8 h9 h10 hu => ?_⟩,
        by omega⟩
      · rw [h20', hS i]
        have hc := p2_congr hagd
          (hv1 i htest) hr (fun h0 => hv4 _ hr) (fun h0 => hv11 _ (by have := h.pch_lt _ hr h0; omega))
          (fun h0 => hv3 _ hr) zttlr htopR hv7
        zubgt
        obtain ⟨a1, a2, a3⟩ := hc u hu
        zusk
        · show fv d'.nmem A R 8 u = _; grind
        · show fv d'.nmem A R 9 u = _; grind
        · show fv d'.nmem A R 10 u = _; grind
      grind)
    ⟨hw1, hf1, by_simp_all, by
      tauto, fun _ _ _ _ _ _ _ => rfl⟩
  zuut

  grind
end p2ram
end
end Chazelle.Core.DecR
section
set_option hygiene false
local macro "zqbcy" : tactic => `(tactic| (have hKR := hF.hKR
                                           have heR : ztsid := by_omega
                                           obtain ⟨hc1, hc2, hc3⟩ := hF.chOf e he))
local macro "zqbcz" : tactic => `(tactic| (rw [show fb 6 = 60106 from rfl, hR.b 6 by_norm_num, h20] at r53
                                           change c1.nreg 60053 = ch at r53
                                           have hR1 := hR.of_same s1 ztfl))
local macro "zqbda" : tactic => `(tactic| have hR2 := hR1.of_same s2 ztfl)
local macro "zqbdb" : tactic => `(tactic| (have hR4 := hR3.of_same s4 ztfl
                                           have m14 : c4.nmem = c.nmem := by_simp_all))
set_option hygiene true

/-!
# Tree decomposition (WP-C), part 17: the chord pass on the RAM

* `tv`: the truncated field view (`0` from `R` on), so that memories agreeing on the fields give
  equal states; `rsOf`: the round state held in memory;
* `codeS_exec`: the code of a component;
* `cpS_exec`: the chord pass writes the fields `rem`, `pend`, `dpar`, `dlo`, `dhi` of `next`.
-/
namespace Chazelle.Core.DecR
open Machine Machine.Stmt Programs Chazelle.Core.Dec
@[expose] public section
def tv (m : ℕ → ℕ) (A R f : ℕ) : ℕ → ℕ := fun j => if j < R then fv m A R f j else 0
theorem tv_lt {m : ℕ → ℕ} {A R f j : ℕ} (hj : j < R) : tv m A R f j = fv m A R f j := by
  unfold tv; simp_all

/-- The round state held in memory (root and finished count from registers). -/
def rsOf (m : ℕ → ℕ) (A R root fin : ℕ) : RS :=
  ⟨tv m A R 11, tv m A R 12, tv m A R 13, tv m A R 14, tv m A R 15, tv m A R 16, tv m A R 17,
    tv m A R 18, tv m A R 0, root, fin⟩
section cpram
variable {P : Polygon} {W : ℕ}
variable {A R K CB RB LB : ℕ}
variable {c : Config} {m m' : ℕ → ℕ}
/-- **The code of a component** with top `x` (in register `xr`). -/
theorem codeS_exec (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {d xr x : ℕ} (hd : d ≠ 60030 ∧ d ≠ 60051 ∧ d ≠ 60052 ∧ d ≠ 60011)
    (hxr : xr ≠ 60030 ∧ xr ≠ 60051 ∧ xr ≠ 60052 ∧ xr ≠ d)
    (h : c.nreg xr = x) (hx : x < R) (hb : fv c.nmem A R 9 x < R)
    (hp : fv c.nmem A R 9 x ≠ x → fv c.nmem A R 4 (fv c.nmem A R 9 x) < R) :
    ∃ c' k, Exec P W (codeS d xr) c c' k ∧ k ≤ 12 ∧ c'.nmem = c.nmem ∧
      Same [60030, 60051, 60052, d] c c' ∧ c'.nreg d = code ztcje ztcjd x := by
  have b9 := hR.b 9 by_norm_num; have b4 := hR.b 4 by_norm_num
  zvmxv at b9 b4
  unfold codeS
  obtain ⟨c1, k1, e1, rfl, m1, s1, r51⟩ := ldF_rel (P := P) hw 60051 9 xr
    (by rw [show fb 9 = 60109 from rfl, b9, h]; omega)
  rw [show fb 9 = 60109 from rfl, b9, h] at r51
  have r51' : c1.nreg 60051 = fv c.nmem A R 9 x := r51
  have hxr1 : c1.nreg xr = x := by rw [s1.1 _ by_simp_all, h]
  zubtk
  zuloo
  unfold code
  zuosg
  by_cases hbx : fv c.nmem A R 9 x = x
  · zugsn
    rw [ite_eq_left hbx]
    zuqj
    zujuq
    exec_block
    · omega
    · config_simp; zunmk; omega
    · refine ⟨by_omega, by zvnmf, ?_, ?_⟩
      · refine (s1.mono by_simp).trans ?_
        exact ⟨fun y hy => by
          zvnvw at hy
          config_simp; rw [Machine.upd_other _ _ _ hy.2.2.2], rfl, rfl, rfl⟩
      · config_simp; zunmk; ring
  · zugso
    rw [ite_eq_right hbx]
    have hpx := hp hbx
    obtain ⟨c2, k2, e2, rfl, m2, s2, r52⟩ := ldF_rel e1.wb_right 60052 4 60051
      (by rw [show fb 4 = 60104 from rfl, hR1.b 4 by_norm_num, r51']; omega)
    rw [show fb 4 = 60104 from rfl, hR1.b 4 by_norm_num, r51', m1] at r52
    zujfp
    zump
    refine spec_instr (Exec.addN hw2 _ _ _ (by rw [r52]; unfold fv at hpx ⊢; omega)) fun _ => ?_
    zucxe
    refine ztoms
    · refine ((s1.mono by_simp).trans ztddg).trans ?_
      exact Same.upd1 by_simp
    · config_simp; rw [r52, tv_lt hb]; unfold fv; ring

/-- The facts on the fields the chord pass relies on. -/
structure CPFacts (m : ℕ → ℕ) (A R K : ℕ) : Prop where
  hKR : K < R
  chOf : ∀ e, e < K → fv m A R 6 e < R ∧ fv m A R 6 e ≠ 0 ∧ fv m A R 3 (fv m A R 6 e) < R
  topR : ∀ u, u < R → fv m A R 8 u < R
  topTop : ∀ u, u < R → fv m A R 8 (fv m A R 8 u) = fv m A R 8 u
  best : ∀ x, x < R → fv m A R 8 x = x →
    fv m A R 9 x < R ∧ (fv m A R 9 x ≠ x → fv m A R 4 (fv m A R 9 x) < R)
  cpar : ∀ t, t < R → fv m A R 8 t = t → fv m A R 13 t = 1 → fv m A R 15 t ≠ 2 →
    fv m A R 14 t < R

/-- **Filling the slots** of chord `e` (in `60020`) cut in the previous round. -/
theorem fillS_exec (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) (hF : CPFacts c.nmem A R K) {e : ℕ} (h20 : c.nreg 60020 = e)
    (he : e < K) (hpend : fv c.nmem A R 12 e = 1)
    (hpt : fv c.nmem A R 8 ztikp = fv c.nmem A R 6 e) :
    ∃ c' k, Exec P W fillS c c' k ∧ k ≤ 50 ∧
      Same [60030, 60053, 60054, 60055, 60056, 60057, 60058, 60059, 60060, 60051, 60052] c c' ∧
      ztwnh ∧
      ∀ f u, f < 19 → u < R → fv c'.nmem A R f u =
        if u = e ∧ f = 12 then 0
        else if u = e ∧ f = 18 then code ztcje ztcjd
          ztdjj
        else if u = e ∧ f = 17 then code ztcje ztcjd
          ztdjk
        else fv c.nmem A R f u := by
  zqbcy
  set ch := fv c.nmem A R 6 e with hchdef
  set pc := fv c.nmem A R 3 ch with hpcdef
  set tp := fv c.nmem A R 8 pc with htpdef
  have htpR := hF.topR pc hc3
  have hchTop := hpt
  have htpTop := hF.topTop pc hc3
  unfold fillS
  obtain ⟨c1, k1, e1, rfl, m1, s1, r53⟩ := ldF_rel (P := P) hw 60053 6 60020
    ztfpt
  zqbcz
  obtain ⟨c2, k2, e2, rfl, m2, s2, r54⟩ := ldF_rel (P := P) e1.wb_right 60054 3 60053
    (by rw [show fb 3 = 60103 from rfl, hR1.b 3 by_norm_num, r53]; omega)
  rw [show fb 3 = 60103 from rfl, hR1.b 3 by_norm_num, r53, m1] at r54
  change c2.nreg 60054 = pc at r54
  zqbda
  obtain ⟨c3, k3, e3, rfl, m3, s3, r55⟩ := ldF_rel (P := P) e2.wb_right 60055 8 60054
    (by rw [show fb 8 = 60108 from rfl, hR2.b 8 by_norm_num, r54]; omega)
  rw [show fb 8 = 60108 from rfl, hR2.b 8 by_norm_num, r54, m2, m1] at r55
  change c3.nreg 60055 = tp at r55
  zuftx
  obtain ⟨c4, k4, e4, rfl, m4, s4, r56⟩ := ldF_rel (P := P) e3.wb_right 60056 5 60053
    (by rw [show fb 5 = 60105 from rfl, hR3.b 5 by_norm_num, s3.1 _ by_simp, s2.1 _ by_simp, r53]
        omega)
  rw [show fb 5 = 60105 from rfl, hR3.b 5 by_norm_num, s3.1 _ by_simp, s2.1 _ by_simp, r53,
    m3, m2, m1] at r56
  zqbdb
  have s14 : Same [60030, 60053, 60054, 60055, 60056] c c4 :=
    (((s1.mono by_simp).trans ztddg).trans ztcqb).trans ztear
  refine spec_seq ⟨c1, 2, e1, spec_seq ⟨c2, 2, e2, spec_seq ⟨c3, 2, e3, spec_seq ztone⟩⟩⟩
  -- the low and high tops
  set lo := loTop _ _ _ _ e with hlodef
  set hi := hiTop _ _ _ _ e with hhidef
  have hlo : lo = if fv c.nmem A R 5 ch = 1 then ch else tp := by
    rw [hlodef]; unfold loTop; zunir
  have hhi : hi = if fv c.nmem A R 5 ch = 1 then tp else ch := by
    rw [hhidef]; unfold hiTop; zunir
  obtain ⟨c5, k5, e5, hk5, hc5⟩ : ∃ c5 k5, Exec P W (ifEqN 60056 60011
      ztksm
      ztksn) c4 c5 k5 ∧ k5 ≤ 6 ∧
      c5 = { c4 with nreg := upd (upd c4.nreg 60057 lo) 60058 hi } := by
    have r53' : ztupp := by zungm
    have r55' : c4.nreg 60055 = tp := by rw [s4.1 _ by_simp, r55]
    zubgi
    zujuq
    by_cases hd : fv c.nmem A R 5 ch = 1
    · refine ifEqN_eq ztkug ?_
      exec_block
      simp_all
    · refine ifEqN_ne ztkug ?_
      exec_block
      grind
  subst hc5
  zudpn
  set c5 := { c4 with nreg := upd (upd c4.nreg 60057 lo) 60058 hi } with hc5def
  have s45 : Same [60057, 60058] c4 c5 := by rw [hc5def]; same_tac
  have hR5 := hR4.of_same s45 ztfl
  have hloR : lo < R ∧ fv c.nmem A R 8 lo = lo := by
    grind
  have hhiR : hi < R ∧ fv c.nmem A R 8 hi = hi := by
    grind
  obtain ⟨blo1, blo2⟩ := hF.best lo hloR.1 hloR.2
  obtain ⟨bhi1, bhi2⟩ := hF.best hi hhiR.1 hhiR.2
  obtain ⟨c6, k6, e6, hk6, m6, s6, r59⟩ := codeS_exec (P := P) hw5 hR5 hAW (d := 60059) (xr := 60057)
    (x := lo) by_decide by_decide by_rfl
    hloR.1 by_simp_all
    by_simp_all
  rw [hc5def] at r59; simp only [m14] at r59
  zukab
  obtain ⟨c7, k7, e7, hk7, m7, s7, r60⟩ := codeS_exec (P := P) e6.wb_right hR6 hAW (d := 60060)
    (xr := 60058) (x := hi) by_decide by_decide
    (by rw [s6.1 _ by_simp, hc5def]; config_simp)
    hhiR.1 by_simp_all
    by_simp_all
  rw [m6, hc5def] at r60; simp only [m14] at r60
  zukac
  have m17 : c7.nmem = c.nmem := by_simp_all
  have s17 : Same [60030, 60053, 60054, 60055, 60056, 60057, 60058, 60059, 60060, 60051, 60052] c c7 :=
    (((s14.mono by_simp).trans (s45.mono by_simp)).trans ztmnl).trans ztwcz
  have r20 : ztupt := by rw [s17.1 _ by_simp, h20]
  have r59' : c7.nreg 60059 = code ztcje ztcjd lo := by
    rw [s7.1 _ by_simp, r59]
  have hcodeR : ∀ x, x < R → fv c.nmem A R 8 x = x →
      code ztcje ztcjd x ≤ 2 * R + 1 := by
    intro x hx htx
    zucnp
    unfold code; zuosg
    split_ifs with hb
    · omega
    · rw [tv_lt b1]; omega
  refine spec_seq ⟨c5, k5, e5, spec_seq ⟨c6, k6, e6, spec_seq ⟨c7, k7, e7, ?_⟩⟩⟩
  obtain ⟨c8, k8, e8, rfl, m8, s8⟩ := stF_rel (P := P) e7.wb_right 17 60020 60059 by_decide
    (by rw [show fb 17 = 60117 from rfl, hR7.b 17 by_norm_num, r20]; omega)
  have hR8 := hR7.of_same s8 ztfl
  obtain ⟨c9, k9, e9, rfl, m9, s9⟩ := stF_rel (P := P) e8.wb_right 18 60020 60060 by_decide
    (by rw [show fb 18 = 60118 from rfl, hR8.b 18 by_norm_num, s8.1 _ by_simp, r20]; omega)
  have hR9 := hR8.of_same s9 ztfl
  obtain ⟨c10, k10, e10, rfl, m10, s10⟩ := stF_rel (P := P) e9.wb_right 12 60020 60010 by_decide
    (by rw [show fb 12 = 60112 from rfl, hR9.b 12 by_norm_num, s9.1 _ by_simp, s8.1 _ by_simp, r20]
        omega)
  refine spec_seq ⟨_, 2, e8, spec_seq ⟨_, 2, e9, ⟨_, 2, e10, ?_⟩⟩⟩
  have r20' : ∀ d : Config, Same [60030] c7 d → d.nreg 60020 = e := fun d hs => by
    rw [hs.1 _ by_simp, r20]
  refine ⟨by_omega, s17.trans (((s8.trans s9).trans s10).mono by_simp), fun a ha => ?_,
    fun f u hf hu => ?_⟩
  · zuill
    simp only [show fb 17 = 60117 from rfl, show fb 18 = 60118 from rfl,
      show fb 12 = 60112 from rfl, hR7.b 17 by_norm_num, hR8.b 18 by_norm_num,
      hR9.b 12 by_norm_num, s9.1 60020 by_simp, s8.1 60020 by_simp, r20]
    rw [fv_store_out by_norm_num heR ha, fv_store_out by_norm_num heR ha,
      fv_store_out by_norm_num heR ha, m17]
  · zuill
    simp only [show fb 17 = 60117 from rfl, show fb 18 = 60118 from rfl,
      show fb 12 = 60112 from rfl, hR7.b 17 by_norm_num, hR8.b 18 by_norm_num,
      hR9.b 12 by_norm_num, s9.1 60020 by_simp, s8.1 60020 by_simp, r20]
    rw [fv_store heR hu, fv_store heR hu, fv_store heR hu, m17]
    rw [s8.1 60060 by_simp,
      s9.1 60010 by_simp, s8.1 60010 by_simp, s17.1 60010 by_simp, hR.zero, r59']
    grind

/-- **Cutting the chord** `e` if it is the chosen chord of its component. -/
theorem chkS_exec (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) (hF : CPFacts c.nmem A R K) {e : ℕ} (h20 : c.nreg 60020 = e)
    (he : e < K) :
    ∃ c' k, Exec P W chkS c c' k ∧ k ≤ 40 ∧
      Same [60030, 60053, 60055, 60064, 60065, 60061, 60062, 60063] c c' ∧
      ztwnh ∧
      ∀ f u, f < 19 → u < R → fv c'.nmem A R f u =
        if fv c.nmem A R 13 ztus = 1 ∧
          fv c.nmem A R 9 ztus = fv c.nmem A R 6 e ∧ u = e ∧
          ztjuz then
          (if f = 16 then
            (if fv c.nmem A R 15 ztus = 2 then 2 * e
              else 2 * fv c.nmem A R 14 ztus)
           else 1)
        else fv c.nmem A R f u := by
  zqbcy
  set ch := fv c.nmem A R 6 e with hchdef
  set t := fv c.nmem A R 8 ch with htdef
  have htR : t < R := hF.topR ch hc1
  have htt := hF.topTop ch hc1
  unfold chkS
  obtain ⟨c1, k1, e1, rfl, m1, s1, r53⟩ := ldF_rel (P := P) hw 60053 6 60020
    ztfpt
  zqbcz
  obtain ⟨c2, k2, e2, rfl, m2, s2, r55⟩ := ldF_rel (P := P) e1.wb_right 60055 8 60053
    (by rw [show fb 8 = 60108 from rfl, hR1.b 8 by_norm_num, r53]; omega)
  rw [show fb 8 = 60108 from rfl, hR1.b 8 by_norm_num, r53, m1] at r55
  change c2.nreg 60055 = t at r55
  zqbda
  obtain ⟨c3, k3, e3, rfl, m3, s3, r64⟩ := ldF_rel (P := P) e2.wb_right 60064 13 60055
    (by rw [show fb 13 = 60113 from rfl, hR2.b 13 by_norm_num, r55]; omega)
  rw [show fb 13 = 60113 from rfl, hR2.b 13 by_norm_num, r55, m2, m1] at r64
  zuftx
  zukii
  have s13 : Same [60030, 60053, 60055, 60064] c c3 :=
    ((s1.mono by_simp).trans ztddg).trans ztcqb
  refine spec_seq ztykp
  by_cases hact : fv c.nmem A R 13 t = 1
  · refine ifEqN_eq ztlio ?_
    obtain ⟨c4, k4, e4, rfl, m4, s4, r65⟩ := ldF_rel e3.wb_right 60065 9 60055
      (by rw [show fb 9 = 60109 from rfl, hR3.b 9 by_norm_num, s3.1 _ by_simp, r55]; omega)
    rw [show fb 9 = 60109 from rfl, hR3.b 9 by_norm_num, s3.1 _ by_simp, r55, m13] at r65
    zqbdb
    have s14 : Same [60030, 60053, 60055, 60064, 60065] c c4 :=
      (s13.mono by_simp).trans ztear
    refine spec_seq ztone
    have r53' : ztupp := by
      zungm
    by_cases hbest : fv c.nmem A R 9 t = ch
    · refine ifEqN_eq ztlip ?_
      -- cut the chord
      have r20 : c4.nreg 60020 = e := by rw [s14.1 _ by_simp, h20]
      have r55' : c4.nreg 60055 = t := by rw [s4.1 _ by_simp, s3.1 _ by_simp, r55]
      unfold doS
      obtain ⟨c5, k5, e5, rfl, m5, s5⟩ := stF_rel e4.wb_right 11 60020 60011 by_decide
        (by rw [show fb 11 = 60111 from rfl, hR4.b 11 by_norm_num, r20]; omega)
      zukaa
      obtain ⟨c6, k6, e6, rfl, m6, s6⟩ := stF_rel e5.wb_right 12 60020 60011 by_decide
        (by rw [show fb 12 = 60112 from rfl, hR5.b 12 by_norm_num, s5.1 _ by_simp, r20]; omega)
      zukab
      have r55'' : c6.nreg 60055 = t := by rw [s6.1 _ by_simp, s5.1 _ by_simp, r55']
      have r20'' : c6.nreg 60020 = e := by rw [s6.1 _ by_simp, s5.1 _ by_simp, r20]
      -- the memory after the two stores
      set m2' := upd _ _ 1 with hm2'
      have m6' : c6.nmem = m2' := by
        rw [m6, m5, show fb 12 = 60112 from rfl, hR5.b 12 by_norm_num, show fb 11 = 60111 from rfl,
          hR4.b 11 by_norm_num, s5.1 _ by_simp, r20, s5.1 60011 by_simp, hR4.one, m14]
      have hside : fv m2' A R 15 t = fv c.nmem A R 15 t := by
        zuemf
      have hcpar : fv m2' A R 14 t = fv c.nmem A R 14 t := by
        zuemf
      obtain ⟨c7, k7, e7, rfl, m7, s7, r61⟩ := ldF_rel (P := P) e6.wb_right 60061 15 60055
        (by rw [show fb 15 = 60115 from rfl, hR6.b 15 by_norm_num, r55'']; omega)
      rw [show fb 15 = 60115 from rfl, hR6.b 15 by_norm_num, r55'', m6'] at r61
      change c7.nreg 60061 = fv m2' A R 15 t at r61
      rw [hside] at r61
      zukac
      set y := if fv c.nmem A R 15 t = 2 then 2 * e else 2 * fv c.nmem A R 14 t with hydef
      obtain ⟨c8, k8, e8, hk8, m8, s8, r62⟩ : ∃ c8 k8, Exec P W (ifEqN 60061 60012
          ztnav
          ztgql) c7 c8 k8 ∧ k8 ≤ 7 ∧
          c8.nmem = c7.nmem ∧ Same [60030, 60062, 60063] c7 c8 ∧ c8.nreg 60062 = y := by
        have r20' : ztupt := by rw [s7.1 _ by_simp, r20'']
        by_cases hs2 : fv c.nmem A R 15 t = 2
        · refine ifEqN_eq ztlin ?_
          refine spec_instr (Exec.addN e7.wb_right _ _ _ by_omega) fun _ => ?_
          refine ⟨by_omega, rfl, Same.upd1 by_simp, ?_⟩
          config_simp; grind
        · refine ifEqN_ne ztlin ?_
          have hcR := hF.cpar t htR htt hact hs2
          obtain ⟨c8, k8, e8, rfl, m8, s8, r63⟩ := ldF_rel e7.wb_right 60063 14 60055
            (by rw [show fb 14 = 60114 from rfl, hR7.b 14 by_norm_num, s7.1 _ by_simp, r55'']; omega)
          rw [show fb 14 = 60114 from rfl, hR7.b 14 by_norm_num, s7.1 _ by_simp, r55'', m7, m6'] at r63
          change c8.nreg 60063 = fv m2' A R 14 t at r63
          rw [hcpar] at r63
          refine spec_seq ⟨c8, 2, e8, ?_⟩
          refine spec_instr (Exec.addN e8.wb_right _ _ _ by_omega) fun _ => ?_
          zucxe
          refine ⟨by_omega, m8, (s8.mono by_simp).trans zteod, ?_⟩
          config_simp; grind
      obtain ⟨c9, k9, e9, rfl, m9, s9⟩ := stF_rel e8.wb_right 16 60020 60062 by_decide
        (by rw [show fb 16 = 60116 from rfl, s8.1 60116 by_simp, s8.1 60020 by_simp,
          hR7.b 16 by_norm_num, s7.1 _ by_simp, r20'']; omega)
      refine spec_seq ⟨_, 2, e5, spec_seq ⟨_, 2, e6, spec_seq ⟨c7, 2, e7, spec_seq ⟨c8, k8, e8,
        ⟨_, 2, e9, ?_⟩⟩⟩⟩⟩
      have s19 : Same [60030, 60053, 60055, 60064, 60065, 60061, 60062, 60063] c c9 :=
        (((((s14.mono by_simp).trans ztwcy).trans ztmnl).trans
          ztwcz).trans (s8.mono by_simp)).trans (s9.mono by_simp)
      have m9' : c9.nmem = upd m2' (A + 12 + 16 * R + e) y := by
        rw [m9, m8, m7, m6', show fb 16 = 60116 from rfl, s8.1 60116 by_simp, s8.1 60020 by_simp,
          hR7.b 16 by_norm_num, s7.1 60020 by_simp, r20'', r62]
      refine ⟨by_omega, s19, fun a ha => ?_, fun f u hf hu => ?_⟩
      · rw [m9', hm2', fv_store_out by_norm_num heR ha, fv_store_out by_norm_num heR ha,
          fv_store_out by_norm_num heR ha]
      · rw [m9', hm2', fv_store heR hu, fv_store heR hu, fv_store heR hu]
        grind
    · refine ifEqN_ne ztlip (spec_skip e4.wb_right ?_)
      zucxe
      refine ⟨by_omega, s14.mono by_simp, by_simp_all, fun f u _ _ => ?_⟩
      simp_all
  · refine ifEqN_ne ztlio ztuas
    zucxe
    refine ⟨by_omega, s13.mono by_simp, by_simp_all, fun f u _ _ => ?_⟩
    simp_all

/-- The round `next` computed from the state held in memory. -/
def nxt (m : ℕ → ℕ) (A R K : ℕ) : RS :=
  next R K (tv m A R 3) (tv m A R 4) (tv m A R 5) (tv m A R 6) (tv m A R 8) (tv m A R 9)
    (rsOf m A R 0 0)

/-- The fields written by the chord pass, with their new values at `e`. -/
def cpv (m : ℕ → ℕ) (A R K f e : ℕ) : ℕ :=
  if f = 11 then (nxt m A R K).rem e else if f = 12 then (nxt m A R K).pend e
  else if f = 16 then (nxt m A R K).dpar e else if f = 17 then (nxt m A R K).dlo e
  else (nxt m A R K).dhi e

/-- The fields of the chord pass. -/
def CPF (f : ℕ) : Prop := f = 11 ∨ f = 12 ∨ f = 16 ∨ f = 17 ∨ f = 18
instance (f : ℕ) : Decidable (CPF f) := inferInstanceAs ztdta

/-- **One step of the chord pass.** -/
theorem cpBody_exec (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) (hF : CPFacts c.nmem A R K) {e : ℕ} (h20 : c.nreg 60020 = e)
    (he : e < K)
    (hpt : fv c.nmem A R 12 e = 1 → fv c.nmem A R 8 ztikp = fv c.nmem A R 6 e) :
    ∃ c' k, Exec P W cpBody c c' k ∧ k ≤ 62 ∧ DFr ztiq zten c c' ∧
      c'.nreg 60020 = e + 1 ∧
      ∀ f u, f < 19 → u < R → fv c'.nmem A R f u =
        if u = e ∧ CPF f then cpv c.nmem A R K f e else fv c.nmem A R f u := by
  zqbcy
  have htR := hF.topR _ hc1
  -- the next values at `e`
  have hN : ∀ f, CPF f → cpv c.nmem A R K f e =
      (if fv c.nmem A R 12 e = 1 then
        (if f = 12 then 0
         else if f = 17 then code ztcje ztcjd
           ztdjk
         else if f = 18 then code ztcje ztcjd
           ztdjj
         else fv c.nmem A R f e)
      else if fv c.nmem A R 11 e ≠ 1 ∧
          fv c.nmem A R 13 ztus = 1 ∧
          fv c.nmem A R 9 ztus = fv c.nmem A R 6 e ∧
          ztjuz then
        (if f = 16 then
          (if fv c.nmem A R 15 ztus = 2 then 2 * e
            else 2 * fv c.nmem A R 14 ztus)
         else 1)
      else fv c.nmem A R f e) := by
    zuhgh
    have ht := tv_lt (m := c.nmem) (A := A) (f := 8) hc1
    have hc := tv_lt (m := c.nmem) (A := A) (f := 6) heR
    rcases hf with rfl | rfl | rfl | rfl | rfl <;>
      simp only [cpv, nxt, next, nPend, rsOf, Chosen, ite_eq_left he, hc, ht, tv_lt heR, tv_lt htR] <;> norm_num
  unfold cpBody
  obtain ⟨c1, k1, e1, rfl, m1, s1, r66⟩ := ldF_rel (P := P) hw 60066 12 60020
    (by rw [show fb 12 = 60112 from rfl, hR.b 12 by_norm_num, h20]; omega)
  rw [show fb 12 = 60112 from rfl, hR.b 12 by_norm_num, h20] at r66
  change c1.nreg 60066 = fv c.nmem A R 12 e at r66
  zubtk
  have hF1 : CPFacts c1.nmem A R K := by_grind
  have r20 : c1.nreg 60020 = e := by zunzj
  -- the middle, with its effect
  have hmid : ∃ c2 k2, Exec P W (ifEqN 60066 60011 fillS
        zthqg) c1 c2 k2 ∧ k2 ≤ 56 ∧
      Same [60030, 60053, 60054, 60055, 60056, 60057, 60058, 60059, 60060, 60051, 60052, 60067,
        60064, 60065, 60061, 60062, 60063] c1 c2 ∧
      ztxbq ∧
      ∀ f u, f < 19 → u < R → fv c2.nmem A R f u =
        if u = e ∧ CPF f then cpv c.nmem A R K f e else fv c.nmem A R f u := by
    by_cases hp : fv c.nmem A R 12 e = 1
    · refine ifEqN_eq ztkuh ?_
      obtain ⟨c2, k2, e2, hk2, s2, hm2, hv2⟩ := fillS_exec e1.wb_right hR1 hAW hF1 r20 he
        by_simp_all by_simp_all
      refine ⟨c2, k2, e2, by_omega, s2.mono by_simp, fun a ha => by_grind,
        fun f u hf hu => ?_⟩
      rw [hv2 f u hf hu, m1]
      zufrn
      · zujpr

        · grind
        · have : f ≠ 11 ∧ f ≠ 12 ∧ f ≠ 16 ∧ f ≠ 17 ∧ f ≠ 18 := by unfold CPF at hcf; omega
          grind
      grind
    · refine ifEqN_ne ztkuh ?_
      obtain ⟨c2, k2, e2, rfl, m2, s2, r67⟩ := ldF_rel e1.wb_right 60067 11 60020
        (by rw [show fb 11 = 60111 from rfl, hR1.b 11 by_norm_num, r20]; omega)
      rw [show fb 11 = 60111 from rfl, hR1.b 11 by_norm_num, r20, m1] at r67
      change c2.nreg 60067 = fv c.nmem A R 11 e at r67
      zqbda
      zukih
      zujfp
      by_cases hr : fv c.nmem A R 11 e = 1
      · refine ifEqN_eq ztkui ztoib
        zucxe
        refine ⟨by_omega, s2.mono by_simp, by_simp_all, fun f u hf hu => ?_⟩
        simp_all
      · refine ifEqN_ne ztkui ?_
        have hF2 : ztsbb := by_simp_all
        obtain ⟨c3, k3, e3, hk3, s3, hm3, hv3⟩ := chkS_exec e2.wb_right hR2 hAW hF2
          (by zunhx) he
        refine ⟨c3, k3, e3, fun k' hk' => fun k'' hk'' => ⟨by_omega,
          (s2.mono by_simp).trans ztcqb, fun a ha => by_grind,
          fun f u hf hu => ?_⟩⟩
        rw [hv3 f u hf hu, m12]
        zufrn
        · zujpr

          · grind
          · have  := fun hh => hcf ztqft
            grind
        grind
  zubbt
  zqbda
  obtain ⟨c3, k3, e3, rfl, m3, s3, r20'⟩ := incr_exec (P := P) e2.wb_right hR2.one
    (by zunhx; omega)
  refine ⟨c3, 2 + ztcvw, .seq e1 ztbpc, by_omega, ?_, by
    rw [r20', s2.1 _ by_simp, r20], fun f u hf hu => by_grind⟩
  exact DFr.of_same (((s1.mono (l' := [60066, 60030, 60053, 60054, 60055, 60056, 60057, 60058,
    60059, 60060, 60051, 60052, 60067, 60064, 60065, 60061, 60062, 60063, 60020]) by_simp).trans
    ztddg).trans (s3.mono by_simp)) (by zuozg)
    ztxl
theorem tv_congr {A R f : ℕ} (h : ∀ u, u < R → fv m A R f u = fv m' A R f u) :
    tv m A R f = tv m' A R f := by
  funext j; unfold tv; simp_all

/-- The new values at `e` depend only on the static fields and the entries at `e`. -/
theorem cpv_congr {e : ℕ} (heR : e < R)
    (hs : ∀ f, f < 19 → ¬ CPF f → ∀ u, u < R → fv m A R f u = fv m' A R f u)
    (he : ∀ f, CPF f → fv m A R f e = fv m' A R f e) (f : ℕ) :
    cpv m A R K f e = cpv m' A R K f e := by
  have t : ∀ f, f < 19 → ¬ CPF f → tv m A R f = tv m' A R f := fun f hf hc => tv_congr by_simp_all
  have t3 := t 3 by_norm_num by_decide
  have t4 := t 4 by_norm_num by_decide
  have t5 := t 5 by_norm_num by_decide
  have t6 := t 6 by_norm_num by_decide
  have t8 := t 8 by_norm_num by_decide
  have t9 := t 9 by_norm_num by_decide
  have t13 := t 13 by_norm_num by_decide
  have t14 := t 14 by_norm_num by_decide
  have t15 := t 15 by_norm_num by_decide
  have t0 := t 0 by_norm_num by_decide
  have e11 := he 11 by_decide; have e12 := he 12 by_decide
  have e16 := he 16 by_decide; have e17 := he 17 by_decide
  have e18 := he 18 by_decide
  simp only [cpv, nxt, next, nPend, rsOf, Chosen, t3, t4, t5, t6, t8, t9, t13, t14, t15, t0,
    tv_lt heR, e11, e12, e16, e17, e18]

/-- **The chord pass.** -/
theorem cpS_exec (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) (hF : CPFacts c.nmem A R K)
    (hpt : ∀ e, e < K → fv c.nmem A R 12 e = 1 →
      fv c.nmem A R 8 ztikp = fv c.nmem A R 6 e) :
    ∃ c' k, Exec P W cpS c c' k ∧ k ≤ 64 * K + 3 ∧ WordsBounded W c' ∧
      DFr ztiq zten c c' ∧
      ∀ f u, f < 19 → u < R → fv c'.nmem A R f u =
        if u < K ∧ CPF f then cpv c.nmem A R K f u else fv c.nmem A R f u := by
  zumbw
  unfold cpS
  zugx

  have hf1 : ztxiv :=
    DFr.nreg _ fun r hr _ => by
      zupj
  have hstat : ∀ d : Config, (∀ f u, f < 19 → u < R → fv d.nmem A R f u =
      if u < d.nreg 60020 ∧ CPF f then cpv c.nmem A R K f u else fv c.nmem A R f u) →
      ∀ f, f < 19 → ¬ CPF f → ∀ u, u < R → fv d.nmem A R f u = fv c.nmem A R f u :=
    by simp_all
  obtain ⟨c', k, e, ⟨hw', hf', hj', hv'⟩, htest, hk⟩ := Exec.whileLtN_potential (P := P) (W := W)
    (a := 60020) (b := 60014) (body := cpBody)
    (fun d => WordsBounded W d ∧ DFr ztiq zten c d ∧ d.nreg 60020 ≤ K ∧
      ∀ f u, f < 19 → u < R → fv d.nmem A R f u =
        if u < d.nreg 60020 ∧ CPF f then cpv c.nmem A R K f u else fv c.nmem A R f u)
    (fun d => 64 * ztrjt) ztoe
    (fun d ⟨hwd, hfd, hjd, hvd⟩ htest => by
      zubdq
      zuktc
      obtain ⟨e, hedef⟩ : ∃ e, d.nreg 60020 = e := by_grind
      rw [hedef] at htest hjd hvd
      have heR : ztsid := by_omega
      zukfl
      have h6 := hs 6 by_norm_num by_decide
      have h3 := hs 3 by_norm_num by_decide
      have h8 := hs 8 by_norm_num by_decide
      have h9 := hs 9 by_norm_num by_decide
      have h4 := hs 4 by_norm_num by_decide
      have h13 := hs 13 by_norm_num by_decide
      have h14 := hs 14 by_norm_num by_decide
      have h15 := hs 15 by_norm_num by_decide
      have hFd : CPFacts d.nmem A R K := by
        refine ⟨hKR, fun e' he' => ?_, fun u hu => ?_, fun u hu => ?_, fun x hx htx => ?_,
          fun t ht htt ha hs2 => ?_⟩
        · zuetr

        · zugcy
        · zuecy
        · zuiil
          zucnp
          grind
        · zuww

      have heC : ∀ f, CPF f → fv d.nmem A R f e = fv c.nmem A R f e := fun f hc => by
        zufgp
        grind
      obtain ⟨d', k', e', hk', hf'', h20', hv''⟩ := cpBody_exec (P := P) hwd hRd hAW hFd hedef htest
        (fun hp => by
          rw [heC 12 by_decide] at hp
          obtain ⟨a1, -, -⟩ := hF.chOf e htest
          grind)
      refine ⟨d', k', e', ztick,
        by omega⟩
      rw [hv'' f u hf hu, h20', cpv_congr heR hs heC]
      zufrn
      · subst hue
        by_cases hc : CPF f
        · grind
        grind
      · zuget
        have hiff : (u < e ↔ u < e + 1) := by_omega
        zuosh)
    ⟨hw1, hf1, by_positivity, fun f u hf hu => by
      rfl⟩
  zuftv

  have hjK : c'.nreg 60020 = K := by_omega
  have h0 : ztpml := by_rfl
  grind
end cpram
end
end Chazelle.Core.DecR
end
section
set_option hygiene false
local macro "zqbfi" : tactic => `(tactic| have hR1 := hR.of_same s1 ztfl)
local macro "zqbfj" : tactic => `(tactic| have hR2 := hR1.of_same s2 ztfl)
local macro "zqbfk" : tactic => `(tactic| by_cases hpd : fv c.nmem A R 12 ztcih = 1)
local macro "zqbfl" : tactic => `(tactic| have hR3 := hR2.of_same s3 ztfl)
local macro "zqbfm" : tactic => `(tactic| by_cases hur : u = r)
local macro "zqbfn" : tactic => `(tactic| rw [m3, m12, fv_store_out by_norm_num hr hA, fv_store_out by_norm_num hr hA])
local macro "zqbfo" : tactic => `(tactic| have r20 : ztuoz := by zunzl)
local macro "zqbfp" : tactic => `(tactic| have r20' : ztpmm := by rw [s2.1 60020 by_simp, r20])
set_option hygiene true

/-!
# Tree decomposition (WP-C), part 18: the root step and the region pass on the RAM

* `rootS_exec`: in the first round (root active with the root slot) the root code is set;
* `rpS_exec`: the region pass writes, at every region, the fields `size` (`1`), `act`, `cpar`,
  `side`, `lpar` given by `rpv`, and counts the finished singletons.
-/
namespace Chazelle.Core.DecR
open Machine Machine.Stmt Programs Chazelle.Core.Dec
@[expose] public section
def rpv (m : ℕ → ℕ) (A R f r : ℕ) : ℕ :=
  if f = 7 then 1
  else if fv m A R 8 r = r then
    (if fv m A R 13 r = 1 then
      (if fv m A R 9 r = r then
        (if f = 13 then 0
         else if f = 0 then (if fv m A R 15 r = 2 then 2 * r + 1 else 2 * fv m A R 14 r)
         else fv m A R f r)
       else
        (if f = 14 then fv m A R 4 ztpby
         else if f = 15 then (if fv m A R 5 ztpby = 1 then 1 else 0)
         else fv m A R f r))
     else fv m A R f r)
  else if fv m A R 12 (fv m A R 4 r) = 1 then
    (if f = 13 then 1 else if f = 14 then fv m A R 4 r
     else if f = 15 then (if fv m A R 5 r = 1 then 0 else 1) else fv m A R f r)
  else fv m A R f r

/-- The fields of the region pass. -/
def RPF (f : ℕ) : Prop := f = 0 ∨ f = 7 ∨ f = 13 ∨ f = 14 ∨ f = 15
instance (f : ℕ) : Decidable (RPF f) := inferInstanceAs ztdta

/-- Region `r` finishes as a singleton in this round. -/
def SingAt (m : ℕ → ℕ) (A R r : ℕ) : Prop :=
  fv m A R 8 r = r ∧ fv m A R 13 r = 1 ∧ fv m A R 9 r = r
instance (m : ℕ → ℕ) (A R r : ℕ) : Decidable (SingAt m A R r) :=
  inferInstanceAs (Decidable (_ ∧ _))
section rpram
variable {P : Polygon} {W : ℕ}
variable {A R K CB RB LB : ℕ}
variable {c : Config}
/-- A store helper: `field f [e] := v` through `stF` with the index in `60020`. -/
theorem stF_at (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {f r v vr : ℕ} (hf : f < 19) (h20 : c.nreg 60020 = r) (hr : r < R)
    (hvr : c.nreg vr = v) (hv : vr ≠ 60030) :
    ∃ c' k, Exec P W (stF f 60020 vr) c c' k ∧ k = 2 ∧
      c'.nmem = upd c.nmem (A + 12 + f * R + r) v ∧ Same [60030] c c' := by
  obtain ⟨c', k, e, hk, m, s⟩ := stF_rel (P := P) hw f 60020 vr hv
    (by rw [show fb f = 60100 + f from rfl, hR.b f by_omega, h20]
        have : ztizt := Nat.mul_le_mul_right _ by_omega
        omega)
  refine ⟨c', k, e, hk, ?_, s⟩
  rw [m, show fb f = 60100 + f from rfl, hR.b f by_omega, h20, hvr]

/-- A load helper: `d := field f [x]`. -/
theorem ldF_at (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {d f x xr : ℕ} (hf : f < 19) (hxr : c.nreg xr = x) (hx : x < R) :
    ∃ c' k, Exec P W (ldF d f xr) c c' k ∧ k = 2 ∧ c'.nmem = c.nmem ∧ Same [60030, d] c c' ∧
      c'.nreg d = fv c.nmem A R f x := by
  obtain ⟨c', k, e, hk, m, s, r⟩ := ldF_rel (P := P) hw d f xr
    (by rw [show fb f = 60100 + f from rfl, hR.b f by_omega, hxr]
        have : ztizt := Nat.mul_le_mul_right _ by_omega
        omega)
  refine ⟨c', k, e, hk, m, s, ?_⟩
  rw [r, show fb f = 60100 + f from rfl, hR.b f by_omega, hxr]; rfl

/-- **The root step.** -/
theorem rootS_exec (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) (hF : CPFacts c.nmem A R K) (h0 : fv c.nmem A R 8 0 = 0) :
    ∃ c' k, Exec P W rootS c c' k ∧ k ≤ 30 ∧ c'.nmem = c.nmem ∧
      Same [60030, 60068, 60069, 60070, 60051, 60052, 60024] c c' ∧
      c'.nreg 60024 = (if fv c.nmem A R 13 0 = 1 then (if fv c.nmem A R 15 0 = 2 then
        code ztcje ztcjd 0 else c.nreg 60024) else c.nreg 60024) := by
  have hR0 : ztgac := by have := hF.hKR; omega
  unfold rootS
  obtain ⟨c1, k1, e1, rfl, m1, s1, r68⟩ := ldF_rel (P := P) hw 60068 13 60010
    (by rw [show fb 13 = 60113 from rfl, hR.b 13 by_norm_num, hR.zero]; omega)
  rw [show fb 13 = 60113 from rfl, hR.b 13 by_norm_num, hR.zero] at r68
  change c1.nreg 60068 = fv c.nmem A R 13 0 at r68
  zqbfi
  zuloo
  by_cases ha : fv c.nmem A R 13 0 = 1
  · refine ifEqN_eq ztkuj ?_
    obtain ⟨c2, k2, e2, rfl, m2, s2, r69⟩ := ldF_rel e1.wb_right 60069 15 60010
      (by rw [show fb 15 = 60115 from rfl, hR1.b 15 by_norm_num, hR1.zero]; omega)
    rw [show fb 15 = 60115 from rfl, hR1.b 15 by_norm_num, hR1.zero, m1] at r69
    change c2.nreg 60069 = fv c.nmem A R 15 0 at r69
    zqbfj
    zujfp
    by_cases hs : fv c.nmem A R 15 0 = 2
    · refine ifEqN_eq ztkuk ?_
      obtain ⟨b1, b2⟩ := hF.best 0 hR0 h0
      obtain ⟨c3, k3, e3, hk3, m3, s3, r70⟩ := codeS_exec e2.wb_right hR2 hAW
        (d := 60070) by_decide by_decide hR2.zero hR0
        by_simp_all by_simp_all
      rw [m2, m1] at r70
      refine spec_seq ⟨c3, k3, e3, ?_⟩
      refine spec_instr (Exec.copyN e3.wb_right _ _) fun _ => ?_
      refine ztoms
      · exact ((((s1.mono by_simp).trans ztddg).trans ztcqb).trans
          zteod)
      simp_all
    · refine ifEqN_ne ztkuk ztoib
      zucxe
      refine ⟨by_omega, by_simp_all, (s1.mono by_simp).trans ztddg, ?_⟩
      rw [ite_eq_left ha, ite_eq_right hs, s2.1 _ by_simp, s1.1 _ by_simp]
  · refine ifEqN_ne ztkuj ztuar
    zucxe
    refine ⟨by_omega, m1, s1.mono by_simp, ?_⟩
    rw [ite_eq_right ha, s1.1 _ by_simp]

/-- A finishing singleton. -/
theorem singS_exec (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {r : ℕ} (h20 : c.nreg 60020 = r) (hr : r < R)
    (hcp : fv c.nmem A R 15 r ≠ 2 → fv c.nmem A R 14 r < R) (hfin : c.nreg 60023 + 1 ≤ W) :
    ∃ c' k, Exec P W singS c c' k ∧ k ≤ 16 ∧
      c'.nmem = upd (upd c.nmem ztldo 0) (A + 12 + 0 * R + r)
        (if fv c.nmem A R 15 r = 2 then 2 * r + 1 else 2 * fv c.nmem A R 14 r) ∧
      Same [60030, 60071, 60072, 60073, 60023] c c' ∧ c'.nreg 60023 = c.nreg 60023 + 1 := by
  unfold singS
  obtain ⟨c1, k1, e1, rfl, m1, s1⟩ := stF_at (P := P) hw hR hAW (f := 13) by_norm_num h20 hr
    hR.zero by_decide
  zqbfi
  have r20 : ztuoz := by zunzj
  obtain ⟨c2, k2, e2, rfl, m2, s2, r71⟩ := ldF_at (P := P) e1.wb_right hR1 hAW (d := 60071)
    (f := 15) by_norm_num r20 hr
  rw [m1, fv_store hr hr, ite_eq_right (show ¬ (15 = 13 ∧ r = r) by omega)] at r71
  zqbfj
  have r20' : ztpmm := by zunhx
  set y := if fv c.nmem A R 15 r = 2 then 2 * r + 1 else 2 * fv c.nmem A R 14 r with hy
  obtain ⟨c3, k3, e3, hk3, m3, s3, r72⟩ : ∃ c3 k3, Exec P W (ifEqN 60071 60012
      ztiqr
      ztgqm) c2 c3 k3 ∧ k3 ≤ 7 ∧
      c3.nmem = c2.nmem ∧ Same [60030, 60072, 60073] c2 c3 ∧ c3.nreg 60072 = y := by
    zump
    by_cases hs : fv c.nmem A R 15 r = 2
    · refine ifEqN_eq ztkul ?_
      zujuq
      exec_block
      · omega
      · config_simp; rw [r20', hR2.one]; omega
      · refine ⟨by_omega, rfl, by same_tac, ?_⟩
        config_simp; rw [r20', hR2.one, hy, ite_eq_left hs]; ring
    · refine ifEqN_ne ztkul ?_
      obtain ⟨c3, k3, e3, rfl, m3, s3, r73⟩ := ldF_at hw2 hR2 hAW
        (f := 14) by_norm_num r20' hr
      rw [m2, m1, fv_store hr hr, ite_eq_right by_simp_all] at r73
      have hc := hcp hs
      refine spec_seq ⟨c3, 2, e3, spec_instr (Exec.addN e3.wb_right _ _ _ (by
        omega)) fun _ => ?_⟩
      zucxe
      refine ⟨by_omega, m3, (s3.mono by_simp).trans zteod, ?_⟩
      config_simp; grind
  zqbfl
  have r20'' : ztupm := by rw [s3.1 _ by_simp, r20']
  obtain ⟨c4, k4, e4, rfl, m4, s4⟩ := stF_at (P := P) e3.wb_right hR3 hAW (f := 0) by_norm_num
    r20'' hr r72 by_decide
  have s14 : Same [60030, 60071, 60072, 60073, 60023] c c4 :=
    (((s1.mono by_simp).trans ztddg).trans ztcqb).trans ztear
  refine spec_seq ⟨c1, 2, e1, spec_seq ⟨c2, 2, e2, spec_seq ⟨c3, k3, e3, spec_seq ⟨c4, 2, e4,
    spec_instr (Exec.addN e4.wb_right _ _ _ (by
      rw [s14.1 60011 by_simp, hR.one]
      have : ztsfh := by
        rw [s4.1 _ by_simp, s3.1 _ by_simp, s2.1 _ by_simp, s1.1 _ by_simp]
      omega)) fun _ => ?_⟩⟩⟩⟩
  refine ⟨by_omega, by_simp_all, s14.trans zteod, ?_⟩
  config_simp
  rw [s14.1 60011 by_simp, hR.one, s4.1 _ by_simp, s3.1 _ by_simp, s2.1 _ by_simp,
    s1.1 _ by_simp]

/-- A cut component records its new slot. -/
theorem cutS_exec (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {r b : ℕ} (h20 : c.nreg 60020 = r) (hr : r < R)
    (h75 : c.nreg 60075 = b) (hb : b < R) :
    ∃ c' k, Exec P W cutS c c' k ∧ k ≤ 13 ∧
      c'.nmem = upd (upd c.nmem ztldp (fv c.nmem A R 4 b)) ztldq
        (if fv c.nmem A R 5 b = 1 then 1 else 0) ∧
      Same [60030, 60074, 60076] c c' := by
  unfold cutS
  obtain ⟨c1, k1, e1, rfl, m1, s1, r74⟩ := ldF_at (P := P) hw hR hAW (d := 60074) (f := 4)
    by_norm_num h75 hb
  zqbfi
  obtain ⟨c2, k2, e2, rfl, m2, s2⟩ := stF_at (P := P) e1.wb_right hR1 hAW (f := 14) by_norm_num
    (by zunzl) hr r74 by_decide
  zqbfj
  obtain ⟨c3, k3, e3, rfl, m3, s3, r76⟩ := ldF_at (P := P) e2.wb_right hR2 hAW (d := 60076) (f := 5)
    by_norm_num (by rw [s2.1 60075 by_simp, s1.1 60075 by_simp, h75]) hb
  rw [m2, m1, fv_store hr hb, ite_eq_right (show ¬ (5 = 14 ∧ b = r) by omega)] at r76
  zqbfl
  have r20 : ztupm := by rw [s3.1 60020 by_simp, s2.1 60020 by_simp, s1.1 60020 by_simp, h20]
  have s13 : Same [60030, 60074, 60076] c c3 :=
    ((s1.mono by_simp).trans ztddg).trans ztcqb
  refine spec_seq ztykp
  by_cases hd : fv c.nmem A R 5 b = 1
  · refine ifEqN_eq ztkum ?_
    obtain ⟨c4, k4, e4, rfl, m4, s4⟩ := stF_at e3.wb_right hR3 hAW (f := 15) by_norm_num
      r20 hr hR3.one by_decide
    exact ⟨_, 2, e4, by_omega, by_simp_all, s13.trans ztear⟩
  · refine ifEqN_ne ztkum ?_
    obtain ⟨c4, k4, e4, rfl, m4, s4⟩ := stF_at e3.wb_right hR3 hAW (f := 15) by_norm_num
      r20 hr hR3.zero by_decide
    exact ⟨_, 2, e4, fun k' hk' => ⟨by_omega, by_simp_all,
      s13.trans ztear⟩⟩

/-- A region that becomes a top when its parent chord was just cut. -/
theorem ntR_exec (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {r : ℕ} (h20 : c.nreg 60020 = r) (hr : r < R)
    (hp : fv c.nmem A R 4 r < R) :
    ∃ c' k, Exec P W ntR c c' k ∧ k ≤ 22 ∧
      c'.nmem = (if fv c.nmem A R 12 ztcih = 1 then
        upd (upd (upd c.nmem ztldo 1) ztldp ztcih)
          ztldq (if fv c.nmem A R 5 r = 1 then 0 else 1)
        else c.nmem) ∧
      Same [60030, 60078, 60079, 60080] c c' := by
  unfold ntR
  obtain ⟨c1, k1, e1, rfl, m1, s1, r78⟩ := ldF_at (P := P) hw hR hAW (d := 60078) (f := 4)
    by_norm_num h20 hr
  zqbfi
  obtain ⟨c2, k2, e2, rfl, m2, s2, r79⟩ := ldF_at (P := P) e1.wb_right hR1 hAW (d := 60079) (f := 12)
    by_norm_num r78 hp
  zvnmf at r79
  zqbfj
  have r20 : ztpmm := by rw [s2.1 60020 by_simp, s1.1 60020 by_simp, h20]
  have s12 : Same [60030, 60078, 60079, 60080] c c2 := (s1.mono by_simp).trans ztddg
  refine spec_seq ⟨c1, 2, e1, spec_seq ztdja⟩
  zqbfk
  · refine ifEqN_eq ztliq ?_
    obtain ⟨c3, k3, e3, rfl, m3, s3⟩ := stF_at e2.wb_right hR2 hAW (f := 13) by_norm_num
      r20 hr hR2.one by_decide
    zqbfl
    obtain ⟨c4, k4, e4, rfl, m4, s4⟩ := stF_at e3.wb_right hR3 hAW (f := 14) by_norm_num
      (by rw [s3.1 60020 by_simp, r20]) hr (by rw [s3.1 60078 by_simp, s2.1 60078 by_simp, r78]) by_decide
    zujzz
    obtain ⟨c5, k5, e5, rfl, m5, s5, r80⟩ := ldF_at e4.wb_right hR4 hAW (d := 60080) (f := 5)
      by_norm_num (by rw [s4.1 60020 by_simp, s3.1 60020 by_simp, r20]) hr
    rw [m4, m3, m2, m1, fv_store hr hr, fv_store hr hr, ite_eq_right by_simp_all,
      ite_eq_right by_simp_all] at r80
    zukaa
    have r20' : c5.nreg 60020 = r := by
      rw [s5.1 60020 by_simp, s4.1 60020 by_simp, s3.1 60020 by_simp, r20]
    have s15 :=
      ((s12.trans ztcqb).trans ztear).trans ztwcy
    refine spec_seq ⟨_, 2, e3, spec_seq ⟨_, 2, e4, spec_seq ⟨c5, 2, e5, ?_⟩⟩⟩
    by_cases hd : fv c.nmem A R 5 r = 1
    · refine ifEqN_eq ztkuo ?_
      obtain ⟨c6, k6, e6, rfl, m6, s6⟩ := stF_at e5.wb_right hR5 hAW (f := 15) by_norm_num
        r20' hr hR5.zero by_decide
      exact ⟨_, 2, e6, by_omega, by_simp_all,
        s15.trans ztmnl⟩
    · refine ifEqN_ne ztkuo ?_
      obtain ⟨c6, k6, e6, rfl, m6, s6⟩ := stF_at e5.wb_right hR5 hAW (f := 15) by_norm_num
        r20' hr hR5.one by_decide
      exact ⟨_, 2, e6, fun k' hk' => ⟨by_omega, by
        simp_all, s15.trans ztmnl⟩⟩
  · refine ifEqN_ne ztliq ztoib
    grind

/-- The top branch of the region pass. -/
theorem topR_exec (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {r : ℕ} (h20 : c.nreg 60020 = r) (hr : r < R)
    (ht : fv c.nmem A R 8 r = r)
    (hb : fv c.nmem A R 13 r = 1 → fv c.nmem A R 9 r < R)
    (hcp : fv c.nmem A R 13 r = 1 → fv c.nmem A R 9 r = r → fv c.nmem A R 15 r ≠ 2 →
      fv c.nmem A R 14 r < R)
    (hfin : c.nreg 60023 + 1 ≤ W) :
    ∃ c' k, Exec P W topR c c' k ∧ k ≤ 28 ∧
      Same [60030, 60077, 60075, 60071, 60072, 60073, 60023, 60074, 60076] c c' ∧
      ztwnh ∧
      (∀ f u, f < 19 → u < R → fv c'.nmem A R f u =
        if u = r ∧ RPF f ∧ f ≠ 7 then rpv c.nmem A R f r else fv c.nmem A R f u) ∧
      c'.nreg 60023 = c.nreg 60023 + ztfce := by
  unfold topR
  obtain ⟨c1, k1, e1, rfl, m1, s1, r77⟩ := ldF_at (P := P) hw hR hAW (d := 60077) (f := 13)
    by_norm_num h20 hr
  zqbfi
  zqbfo
  zuloo
  by_cases ha : fv c.nmem A R 13 r = 1
  · refine ifEqN_eq ztkun ?_
    obtain ⟨c2, k2, e2, rfl, m2, s2, r75⟩ := ldF_at e1.wb_right hR1 hAW (d := 60075)
      (f := 9) by_norm_num r20 hr
    zvnmf at r75
    zqbfj
    zqbfp
    zukih
    have s12 : Same [60030, 60077, 60075, 60071, 60072, 60073, 60023, 60074, 60076] c c2 :=
      (s1.mono by_simp).trans ztddg
    zujfp
    by_cases hs : fv c.nmem A R 9 r = r
    · zugsn
      obtain ⟨c3, k3, e3, hk3, m3, s3, r23⟩ := singS_exec e2.wb_right hR2 hAW r20' hr
        by_simp_all
        ztiin
      have hsing : SingAt c.nmem A R r := ⟨ht, ha, hs⟩
      refine ⟨c3, k3, e3, by_omega, s12.trans ztcqb, fun a hA => ?_,
        fun f u hf hu => ?_, ?_⟩
      · zqbfn
      · rw [m3, m12, fv_store hr hu, fv_store hr hu]
        zqbfm
        · zultj
          by_cases h0 : f = 0
          · subst h0; zumzl
          by_cases h13 : f = 13
          · subst h13; zumzl
          · simp only [h0, h13, false_and, ite_false, true_and]
            zuhau
        simp_all
      · rw [r23, ite_eq_left hsing, s2.1 60023 by_simp, s1.1 60023 by_simp]
    · zugso
      obtain ⟨c3, k3, e3, hk3, m3, s3⟩ := cutS_exec e2.wb_right hR2 hAW r20' hr
        (by rw [r75]) (hb ha)
      have hsing : ztlbp := fun h => hs h.2.2
      refine ⟨c3, k3, e3, fun k' hk' => ⟨by_omega, s12.trans ztcqb, fun a hA => ?_,
        fun f u hf hu => ?_, ?_⟩⟩
      · zqbfn
      · rw [m3, m12, fv_store hr hu, fv_store hr hu]
        zqbfm
        · zultj
          by_cases h14 : f = 14
          · subst h14; zumzl
          by_cases h15 : f = 15
          · subst h15; zumzl
          · simp only [h14, h15, false_and, ite_false, true_and]
            zuhau
        simp_all
      · rw [ite_eq_right hsing, Nat.add_zero, s3.1 60023 by_simp, s2.1 60023 by_simp,
          s1.1 60023 by_simp]
  · refine ifEqN_ne ztkun ztuar
    have hsing : ztlbp := fun h => ha h.2.1
    zucxe
    refine ⟨by_omega, s1.mono by_simp, by_simp_all, fun f u hf hu => ?_, ?_⟩
    · zumoo
      zqbfm
      · zultj
        zuhau
      simp_all
    · rw [ite_eq_right hsing, Nat.add_zero, s1.1 60023 by_simp]

/-- The non-top branch of the region pass. -/
theorem ntR_exec' (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {r : ℕ} (h20 : c.nreg 60020 = r) (hr : r < R)
    (ht : fv c.nmem A R 8 r ≠ r) (hp : fv c.nmem A R 4 r < R) :
    ∃ c' k, Exec P W ntR c c' k ∧ k ≤ 28 ∧
      Same [60030, 60078, 60079, 60080] c c' ∧
      ztwnh ∧
      (∀ f u, f < 19 → u < R → fv c'.nmem A R f u =
        if u = r ∧ RPF f ∧ f ≠ 7 then rpv c.nmem A R f r else fv c.nmem A R f u) := by
  obtain ⟨c', k, e, hk, hm, s⟩ := ntR_exec (P := P) hw hR hAW h20 hr hp
  refine ⟨c', k, e, by_omega, s, fun a hA => ?_, fun f u hf hu => ?_⟩
  · zucjq
    zqbfk
    · rw [ite_eq_left hpd, fv_store_out by_norm_num hr hA, fv_store_out by_norm_num hr hA,
        fv_store_out by_norm_num hr hA]
    simp_all
  · zucjq
    zqbfk
    · rw [ite_eq_left hpd, fv_store hr hu, fv_store hr hu, fv_store hr hu]
      zqbfm
      · zultj
        unfold rpv; simp only [ht, hpd, ite_true, ite_false, RPF]; grind
      simp_all
    · rw [ite_eq_right hpd]
      zqbfm
      · zultj
        zuhau
      simp_all

/-- The field-`7` store does not change the other region-pass values. -/
theorem rpv_store7 {m : ℕ → ℕ} {r v f : ℕ} (hr : r < R) (hf : f ≠ 7) (_hf' : f < 19)
    (hb : fv m A R 8 r = r → fv m A R 13 r = 1 → fv m A R 9 r < R)
    (hp : fv m A R 8 r ≠ r → fv m A R 4 r < R) :
    rpv (upd m (A + 12 + 7 * R + r) v) A R f r = rpv m A R f r := by
  have e : ∀ g j, g ≠ 7 → j < R → fv (upd m _ v) A R g j = fv m A R g j :=
    fun g j hg hj => by rw [fv_store hr hj, ite_eq_right (fun h => hg h.1)]
  unfold rpv
  grind

/-- **One step of the region pass.** -/
theorem rpBody_exec (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {r : ℕ} (h20 : c.nreg 60020 = r) (hr : r < R)
    (hb : fv c.nmem A R 8 r = r → fv c.nmem A R 13 r = 1 → fv c.nmem A R 9 r < R)
    (hcp : fv c.nmem A R 8 r = r → fv c.nmem A R 13 r = 1 → fv c.nmem A R 9 r = r →
      fv c.nmem A R 15 r ≠ 2 → fv c.nmem A R 14 r < R)
    (hp : fv c.nmem A R 8 r ≠ r → fv c.nmem A R 4 r < R)
    (hfin : c.nreg 60023 + 1 ≤ W) :
    ∃ c' k, Exec P W rpBody c c' k ∧ k ≤ 40 ∧ DFr ztiq zten c c' ∧
      c'.nreg 60020 = r + 1 ∧
      c'.nreg 60023 = c.nreg 60023 + ztfce ∧
      ∀ f u, f < 19 → u < R → fv c'.nmem A R f u =
        if u = r ∧ RPF f then rpv c.nmem A R f r else fv c.nmem A R f u := by
  unfold rpBody
  obtain ⟨c1, k1, e1, rfl, m1, s1⟩ := stF_at (P := P) hw hR hAW (f := 7) by_norm_num h20 hr
    hR.one by_decide
  zqbfi
  zqbfo
  have e1v : ∀ g j, j < R → fv c1.nmem A R g j = if g = 7 ∧ j = r then 1 else fv c.nmem A R g j :=
    fun g j hj => by rw [m1, fv_store hr hj]
  have e1' : ∀ g j, g ≠ 7 → j < R → fv c1.nmem A R g j = fv c.nmem A R g j :=
    by simp_all
  obtain ⟨c2, k2, e2, rfl, m2, s2, r81⟩ := ldF_at (P := P) e1.wb_right hR1 hAW (d := 60081) (f := 8)
    by_norm_num r20 hr
  rw [e1' 8 r by_norm_num hr] at r81
  zqbfj
  zqbfp
  have m12 := m2
  have s12 : Same [60030, 60081] c c2 := (s1.mono by_simp).trans by_omega
  -- the middle
  have hmid : ∃ c3 k3, Exec P W ztqrj c2 c3 k3 ∧ k3 ≤ 32 ∧
      Same [60030, 60077, 60075, 60071, 60072, 60073, 60023, 60074, 60076, 60078, 60079, 60080]
        c2 c3 ∧
      (∀ a, ztkj → c3.nmem a = c2.nmem a) ∧
      (∀ f u, f < 19 → u < R → fv c3.nmem A R f u =
        if u = r ∧ RPF f ∧ f ≠ 7 then rpv c2.nmem A R f r else fv c2.nmem A R f u) ∧
      c3.nreg 60023 = c2.nreg 60023 + ztfce := by
    by_cases ht : fv c.nmem A R 8 r = r
    · zugsn
      have hs : SingAt c2.nmem A R r ↔ SingAt c.nmem A R r := by
        unfold SingAt
        simp_all
      obtain ⟨c3, k3, e3, hk3, s3, ho, hv, h23⟩ := topR_exec e2.wb_right hR2 hAW r20' hr
        by_simp_all
        by_simp_all
        by_simp_all
        ztiin
      refine ⟨c3, k3, e3, by_omega, s3.mono by_simp, ho, hv, ?_⟩
      grind
    · zugso
      have hs : ztlbp := fun h => ht h.1
      obtain ⟨c3, k3, e3, hk3, s3, ho, hv⟩ := ntR_exec' e2.wb_right hR2 hAW r20' hr
        by_simp_all
        by_simp_all
      exact ⟨c3, k3, e3, fun k' hk' => ⟨by_omega, s3.mono by_simp, ho, hv, by
        rw [ite_eq_right hs, Nat.add_zero, s3.1 60023 by_simp]⟩⟩
  obtain ⟨c3, k3, e3, hk3, s3, ho3, hv3, h23⟩ := hmid
  zqbfl
  obtain ⟨c4, k4, e4, rfl, m4, s4, r20''⟩ := incr_exec (P := P) e3.wb_right hR3.one
    (by rw [s3.1 60020 by_simp, r20']; omega)
  refine ⟨c4, 2 + (2 + (k3 + 1)), .seq e1 ztbal, by_omega, ?_, by
    rw [r20'', s3.1 60020 by_simp, r20'], by
    rw [s4.1 60023 by_simp, h23, s2.1 60023 by_simp, s1.1 60023 by_simp], ?_⟩
  · refine DFr.of_same ((s12.mono (l' := [60030, 60081, 60077, 60075, 60071, 60072, 60073, 60023,
      60074, 60076, 60078, 60079, 60080, 60020]) by_simp).trans ((s3.mono by_simp).trans
      ztear)) (by zuozg) (fun a hA => ?_)
    rw [m4, ho3 a hA, m12, m1, fv_store_out by_norm_num hr hA]
  · intro f u hf hu
    rw [m4, hv3 f u hf hu, m12]
    by_cases h7 : f = 7
    · subst h7
      rw [ite_eq_right by_omega, e1v 7 u hu]
      zqbfm
      · subst hur; simp [rpv, RPF]
      grind
    · by_cases hur : u = r ∧ RPF f
      · rw [ite_eq_left by_grind, ite_eq_left hur, m1,
          rpv_store7 hr h7 hf hb hp]
      grind

/-- The region-pass values at `r` depend only on the static fields and the entries at `r`. -/
theorem rpv_congr {m m' : ℕ → ℕ} {r : ℕ} (hr : r < R)
    (hs : ∀ f, f < 19 → ¬ RPF f → ∀ u, u < R → fv m A R f u = fv m' A R f u)
    (he : ∀ f, RPF f → fv m A R f r = fv m' A R f r)
    (hb : fv m A R 8 r = r → fv m A R 13 r = 1 → fv m A R 9 r < R)
    (hp : fv m A R 8 r ≠ r → fv m A R 4 r < R) (f : ℕ) (hf : f < 19) :
    rpv m A R f r = rpv m' A R f r := by
  have n : ∀ g, g < 19 → ¬ RPF g → ∀ u, u < R → fv m' A R g u = fv m A R g u :=
    by simp_all
  have hff : fv m' A R f r = fv m A R f r := by
    grind
  unfold rpv
  simp only [n 8 by_norm_num by_decide r hr,
    n 9 by_norm_num by_decide r hr, n 4 by_norm_num by_decide r hr,
    n 5 by_norm_num by_decide r hr, ← he 13 by_decide,
    ← he 14 by_decide, ← he 15 by_decide, hff]
  by_cases h8 : fv m A R 8 r = r
  · by_cases h13 : fv m A R 13 r = 1
    · have := hb h8 h13
      simp only [n 4 by_norm_num by_decide _ this,
        n 5 by_norm_num by_decide _ this, h8, h13, ite_true]
    simp_all
  · have := hp h8
    simp only [n 12 by_norm_num by_decide _ this, h8, ite_false]

/-- Counting a filter over `range (j + 1)`. -/
theorem card_filter_succ (p : ℕ → Prop) [DecidablePred p] (j : ℕ) :
    ((Finset.range ztl).filter p).card =
      ((Finset.range j).filter p).card + if p j then 1 else 0 := by
  zuewn

/-- **The region pass.** -/
theorem rpS_exec (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W)
    (hb : ∀ r, r < R → fv c.nmem A R 8 r = r → fv c.nmem A R 13 r = 1 → fv c.nmem A R 9 r < R)
    (hcp : ∀ r, r < R → fv c.nmem A R 8 r = r → fv c.nmem A R 13 r = 1 →
      fv c.nmem A R 9 r = r → fv c.nmem A R 15 r ≠ 2 → fv c.nmem A R 14 r < R)
    (hp : ∀ r, r < R → fv c.nmem A R 8 r ≠ r → fv c.nmem A R 4 r < R)
    (hfin : c.nreg 60023 + R ≤ W) :
    ∃ c' k, Exec P W rpS c c' k ∧ k ≤ 42 * R + 3 ∧ WordsBounded W c' ∧
      DFr ztiq zten c c' ∧
      c'.nreg 60023 = c.nreg 60023 + ((Finset.range R).filter zteab).card ∧
      ∀ f u, f < 19 → u < R → fv c'.nmem A R f u =
        if RPF f then rpv c.nmem A R f u else fv c.nmem A R f u := by
  unfold rpS
  zugx

  have hf1 : ztxiv :=
    DFr.nreg _ fun r hr _ => by
      zupj
  have hstat : ∀ d : Config, (∀ f u, f < 19 → u < R → fv d.nmem A R f u =
      if u < d.nreg 60020 ∧ RPF f then rpv c.nmem A R f u else fv c.nmem A R f u) →
      ∀ f, f < 19 → ¬ RPF f → ∀ u, u < R → fv d.nmem A R f u = fv c.nmem A R f u :=
    by simp_all
  obtain ⟨c', k, e, ⟨hw', hf', hj', h23', hv'⟩, htest, hk⟩ :=
    Exec.whileLtN_potential (P := P) (W := W)
    (a := 60020) (b := 60013) (body := rpBody)
    (fun d => WordsBounded W d ∧ DFr ztiq zten c d ∧ d.nreg 60020 ≤ R ∧
      d.nreg 60023 = c.nreg 60023 +
        ((Finset.range ztqls).filter zteab).card ∧
      ∀ f u, f < 19 → u < R → fv d.nmem A R f u =
        if u < d.nreg 60020 ∧ RPF f then rpv c.nmem A R f u else fv c.nmem A R f u)
    ztyvz ztoe
    (fun d ⟨hwd, hfd, hjd, h23d, hvd⟩ htest => by
      zubdq
      zugdi
      obtain ⟨j, hjdef⟩ : ztjbr := by_grind
      rw [hjdef] at htest hjd hvd h23d
      zukfl
      have heC : ∀ f, RPF f → fv d.nmem A R f j = fv c.nmem A R f j := fun f hc => by
        zufgq
        grind
      have e8 := hs 8 by_norm_num by_decide j htest
      have e9 := hs 9 by_norm_num by_decide j htest
      have e4 := hs 4 by_norm_num by_decide j htest
      have e13 := heC 13 by_decide
      have e14 := heC 14 by_decide
      have e15 := heC 15 by_decide
      have hcard := card_filter_succ zteab j
      have hcnt : ((Finset.range j).filter zteab).card ≤ j := by
        grind
      obtain ⟨d', k', e', hk', hf'', h20', h23'', hv''⟩ := rpBody_exec (P := P) hwd hRd hAW hjdef
        htest by_grind by_grind
        by_grind by_omega
      have hsing : SingAt d.nmem A R j ↔ SingAt c.nmem A R j := by
        unfold SingAt; omega
      refine ⟨d', k', e', ⟨e'.wb_right, hfd.trans hf'', by_omega, ?_, fun f u hf hu => ?_⟩,
        by omega⟩
      · rw [h23'', h20', h23d, hcard]; simp only [hsing]; omega
      · rw [hv'' f u hf hu, h20', rpv_congr htest hs heC by_grind
          by_grind f hf]
        by_cases hue : u = j
        · subst hue
          zuldl
          · grind
          grind
        · zuget
          have hiff : (u < j ↔ u < j + 1) := by_omega
          zuosh)
    ⟨hw1, hf1, by_positivity, by
      rfl, fun f u hf hu => by
      rfl⟩
  zuut

  zuddg

  refine ⟨c', k, e, by_omega, hw', hf', by_grind, fun f u hf hu => ?_⟩
  zugvo
  zuldl
  · grind
  grind
