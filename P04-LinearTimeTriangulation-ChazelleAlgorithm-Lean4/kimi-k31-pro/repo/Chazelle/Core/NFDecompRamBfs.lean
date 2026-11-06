module

public import Chazelle.Core.NFDecompRamInit
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics
public import Chazelle.MiscTactics
public import Chazelle.ConfigTactics

/-!
# Tree decomposition (WP-C), part 14: the search on the RAM

* `InEnv`: the input records the search reads (chord endpoints, exit-chord lists), below `A`;
* `BEnc`: the memory holds a search state `BS` in the fields `ord`, `vis`, `prg`, `pch`, `isdn`,
  `chOf`;
* `bfsInner_exec`: one chord scan realises `bstep`;
* `bfsS_exec`: the whole search realises the iteration of `bouter` until the queue is empty.
-/

namespace Chazelle.Core.DecR

open Machine Machine.Stmt Programs Chazelle.Core.Dec

@[expose] public section

/-- The input records read by the search, below `A`: chord endpoints at `CB + 5 i + 3, 4`,
region list lengths at `RB + 5 r + 2`, offsets at `RB + 5 r + 3`, entries at `LB + off + t`. -/
structure InEnv (m : ℕ → ℕ) (A R K CB RB LB : ℕ) (up dn : ℕ → ℕ) (lst : ℕ → List ℕ) : Prop where
  hup : ∀ i, i < K → m (CB + 5 * i + 3) = up i ∧ m (CB + 5 * i + 4) = dn i ∧ CB + 5 * i + 4 < A
  hlen : ∀ r, r < R → m (RB + 5 * r + 2) = (lst r).length ∧ RB + 5 * r + 3 < A
  hent : ∀ r, r < R → ∀ t, t < (lst r).length →
    m (LB + m (RB + 5 * r + 3) + t) = (lst r).getD t 0 ∧ LB + m (RB + 5 * r + 3) + t < A

theorem InEnv.transport {m m' : ℕ → ℕ} {A R K CB RB LB : ℕ} {up dn : ℕ → ℕ} {lst : ℕ → List ℕ}
    (h : InEnv m A R K CB RB LB up dn lst) (hm : ∀ a, a < A → m' a = m a) :
    InEnv m' A R K CB RB LB up dn lst := by
  refine ⟨fun i hi => ?_, fun r hr => ?_, fun r hr t ht => ?_⟩
  · obtain ⟨a1, a2, a3⟩ := h.hup i hi
    exact ⟨by rw [hm _ (by omega), a1], by rw [hm _ (by omega), a2], a3⟩
  · obtain ⟨a1, a2⟩ := h.hlen r hr
    exact ⟨by rw [hm _ (by omega), a1], a2⟩
  · obtain ⟨-, a2⟩ := h.hlen r hr
    have e : m' (RB + 5 * r + 3) = m (RB + 5 * r + 3) := hm _ a2
    obtain ⟨b1, b2⟩ := h.hent r hr t ht
    rw [e]
    exact ⟨by rw [hm _ b2, b1], b2⟩

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

theorem Same.trans {l : List ℕ} {c₁ c₂ c₃ : Config} (h₁ : Same l c₁ c₂) (h₂ : Same l c₂ c₃) :
    Same l c₁ c₃ :=
  ⟨fun x hx => (h₂.1 x hx).trans (h₁.1 x hx), h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    h₂.2.2.2.trans h₁.2.2.2⟩

theorem Same.mono {l l' : List ℕ} {c c' : Config} (h : Same l c c') (hl : ∀ x ∈ l, x ∈ l') :
    Same l' c c' :=
  ⟨fun x hx => h.1 x (fun h' => hx (hl x h')), h.2.1, h.2.2.1, h.2.2.2⟩

theorem DRegs.of_same {A R K CB RB LB : ℕ} {l : List ℕ} {c c' : Config}
    (h : DRegs A R K CB RB LB c) (hs : Same l c c') (hl : ∀ x ∈ l, ¬ Prot x) :
    DRegs A R K CB RB LB c' :=
  h.of_regs fun x hx _ => hs.1 x (fun h' => hl x h' hx)

/-- A step writing only non-protected registers and memory in `[lo, hi)` is in the frame. -/
theorem DFr.of_same {lo hi : ℕ} {l : List ℕ} {c c' : Config} (hs : Same l c c')
    (hl : ∀ x ∈ l, ¬ Prot x) (hm : ∀ a, (a < lo ∨ hi ≤ a) → c'.nmem a = c.nmem a) :
    DFr lo hi c c' :=
  ⟨fun x hx _ => hs.1 x (fun h' => hl x h' hx), hs.2.1, hs.2.2.1, hs.2.2.2, hm⟩

theorem Same.upd1 {l : List ℕ} {c : Config} {x v : ℕ} (hx : x ∈ l) :
    Same l c { c with nreg := upd c.nreg x v } :=
  ⟨fun y hy => by
    show upd c.nreg x v y = c.nreg y
    rw [Machine.upd_other]
    rintro rfl; exact hy hx, rfl, rfl, rfl⟩

/-- `ldF`, relationally. -/
theorem ldF_rel {c : Config} (hw : WordsBounded W c) (d f x : ℕ)
    (hb : c.nreg (fb f) + c.nreg x ≤ W) :
    ∃ c' k, Exec P W (ldF d f x) c c' k ∧ k = 2 ∧ c'.nmem = c.nmem ∧ Same [60030, d] c c' ∧
      c'.nreg d = c.nmem (c.nreg (fb f) + c.nreg x) := by
  obtain ⟨c', k, e, hk, rfl⟩ := ldF_exec (P := P) hw d f x hb
  refine ⟨_, k, e, hk, rfl, ⟨fun y hy => ?_, rfl, rfl, rfl⟩, by config_simp⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  config_simp; rw [Machine.upd_other _ _ _ hy.2, Machine.upd_other _ _ _ hy.1]

/-- `stF`, relationally. -/
theorem stF_rel {c : Config} (hw : WordsBounded W c) (f x v : ℕ) (hv : v ≠ 60030)
    (hb : c.nreg (fb f) + c.nreg x ≤ W) :
    ∃ c' k, Exec P W (stF f x v) c c' k ∧ k = 2 ∧
      c'.nmem = upd c.nmem (c.nreg (fb f) + c.nreg x) (c.nreg v) ∧ Same [60030] c c' := by
  obtain ⟨c', k, e, hk, rfl⟩ := stF_exec (P := P) hw f x v hv hb
  refine ⟨_, k, e, hk, rfl, ⟨fun y hy => ?_, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  config_simp; rw [Machine.upd_other _ _ _ hy]

/-- **Reading a chord of the current list** and its endpoints. -/
theorem bfsRead_exec {A R K CB RB LB : ℕ} {up dn : ℕ → ℕ} {c : Config} (hw : WordsBounded W c)
    (hR : DRegs A R K CB RB LB c) (hAW : A ≤ W) {L t i : ℕ} (h28 : c.nreg 60028 = L)
    (h21 : c.nreg 60021 = t) (hLt : LB + L + t < A) (hi : c.nmem (LB + L + t) = i)
    (hup : c.nmem (CB + 5 * i + 3) = up i) (hdn : c.nmem (CB + 5 * i + 4) = dn i)
    (hCB : CB + 5 * i + 4 < A) :
    ∃ c' k, Exec P W bfsRead c c' k ∧ k = 12 ∧ c'.nmem = c.nmem ∧
      Same [60030, 60032, 60033, 60034, 60035] c c' ∧ c'.nreg 60032 = i ∧
      c'.nreg 60034 = up i ∧ c'.nreg 60035 = dn i := by
  have o := hR.one; have tw := hR.two; have hcb := hR.rCB; have hlb := hR.rLB
  have hi' : c.nmem (LB + (L + t)) = i := by rwx [← Nat.add_assoc]
  unfold bfsRead
  exec_block
  all_goals first
    | (config_simp; simp (config := { failIfUnchanged := false }) only [h28, h21, hi', hcb, hlb, o, tw]
       omega)
    | skip
  refine ⟨rfl, rfl, ⟨fun x hx => ?_, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    config_simp
    simp only [Machine.upd_other _ _ _ hx.1, Machine.upd_other _ _ _ hx.2.1,
      Machine.upd_other _ _ _ hx.2.2.1, Machine.upd_other _ _ _ hx.2.2.2.1,
      Machine.upd_other _ _ _ hx.2.2.2.2]
  · config_simp; rw [h28, h21, hlb, hi']
  · config_simp; simp only [h28, h21, hi', hcb, hlb, o, tw]; convert hup using 2; ring
  · config_simp; simp only [h28, h21, hi', hcb, hlb, o, tw]; convert hdn using 2; ring

/-- **Discovering a region**: the six stores of `bfsNew`. -/
theorem bfsNew_exec {A R K CB RB LB : ℕ} {c : Config} (hw : WordsBounded W c)
    (hR : DRegs A R K CB RB LB c) (hAW : A + 12 + 20 * R ≤ W) {sv tl r i v : ℕ}
    (h36 : c.nreg 60036 = sv) (h26 : c.nreg 60026 = tl) (h29 : c.nreg 60029 = r)
    (h32 : c.nreg 60032 = i) (h37 : c.nreg 60037 = v) (hs : sv < R) (htl : tl < R) (hi : i < R) :
    ∃ c' k, Exec P W bfsNew c c' k ∧ k = 13 ∧ DFr (A + 12) (A + 12 + 19 * R) c c' ∧
      Same [60030, 60026] c c' ∧ c'.nreg 60026 = tl + 1 ∧
      ∀ j, j < R → fv c'.nmem A R 1 j = (if j = tl then sv else fv c.nmem A R 1 j) ∧
        fv c'.nmem A R 2 j = (if j = sv then 1 else fv c.nmem A R 2 j) ∧
        fv c'.nmem A R 3 j = (if j = sv then r else fv c.nmem A R 3 j) ∧
        fv c'.nmem A R 4 j = (if j = sv then i else fv c.nmem A R 4 j) ∧
        fv c'.nmem A R 5 j = (if j = sv then v else fv c.nmem A R 5 j) ∧
        fv c'.nmem A R 6 j = (if j = i then sv else fv c.nmem A R 6 j) ∧
        ∀ f, f < 19 → ¬ BFields f → fv c'.nmem A R f j = fv c.nmem A R f j := by
  have b1 := hR.b 1 (by norm_num); have b2 := hR.b 2 (by norm_num); have b3 := hR.b 3 (by norm_num)
  have b4 := hR.b 4 (by norm_num); have b5 := hR.b 5 (by norm_num); have b6 := hR.b 6 (by norm_num)
  simp only [Nat.reduceAdd] at b1 b2 b3 b4 b5 b6
  have o := hR.one
  unfold bfsNew
  exec_block
  all_goals first
    | (config_simp; simp (config := { failIfUnchanged := false }) only [b1, b2, b3, b4, b5, b6,
        h36, h26, h32, o]; omega)
    | skip
  refine ⟨rfl, ⟨fun x hx hxa => ?_, rfl, rfl, rfl, fun a ha => ?_⟩, ⟨fun x hx => ?_, rfl, rfl, rfl⟩,
    ?_, fun j hj => ?_⟩
  · unfold Prot at hx; config_simp; simp (disch := omega) only [Machine.upd_other]
  · config_simp
    simp only [b1, b2, b3, b4, b5, b6, h36, h26, h32]
    simp (disch := omega) only [Machine.upd_other]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    config_simp
    simp only [Machine.upd_other _ _ _ hx.1, Machine.upd_other _ _ _ hx.2]
  · config_simp; rw [h26, o]
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
      have h1 : f ≠ 1 := by omega
      have h2 : f ≠ 2 := by omega
      have h3 : f ≠ 3 := by omega
      have h4 : f ≠ 4 := by omega
      have h5 : f ≠ 5 := by omega
      have h6 : f ≠ 6 := by omega
      simp [h1, h2, h3, h4, h5, h6]

/-- The other endpoint of the chord and the side bit. -/
theorem bfsSel_exec {c : Config} (hw : WordsBounded W c) {u d r : ℕ} (h34 : c.nreg 60034 = u)
    (h35 : c.nreg 60035 = d) (h29 : c.nreg 60029 = r) (o : c.nreg 60011 = 1) (z : c.nreg 60010 = 0) :
    ∃ c' k, Exec P W (ifEqN 60034 60029 (block [.copyN 60036 60035, .copyN 60037 60011])
        (block [.copyN 60036 60034, .copyN 60037 60010])) c c' k ∧ k ≤ 6 ∧ c'.nmem = c.nmem ∧
      Same [60036, 60037] c c' ∧ c'.nreg 60036 = (if u = r then d else u) ∧
      c'.nreg 60037 = (if u = r then 1 else 0) := by
  have hsame : ∀ (a b : ℕ), Same [60036, 60037] c
      { c with nreg := upd (upd c.nreg 60036 a) 60037 b } := fun a b =>
    ⟨fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      config_simp; rw [Machine.upd_other _ _ _ hx.2, Machine.upd_other _ _ _ hx.1], rfl, rfl, rfl⟩
  by_cases hu : u = r
  · refine ifEqN_eq (by rw [h34, h29, hu]) ?_
    exec_block
    exact ⟨by omega, rfl, hsame _ _, by config_simp; rw [h35, ite_eq_left hu],
      by config_simp; rw [o, ite_eq_left hu]⟩
  · refine ifEqN_ne (by rwx [h34, h29]) ?_
    exec_block
    intro k' hk'
    exact ⟨by omega, rfl, hsame _ _, by config_simp; rw [h34, ite_eq_right hu],
      by config_simp; rw [z, ite_eq_right hu]⟩

/-- **One chord scan** of the search realises `bstep`. -/
theorem bfsInner_exec {A R K CB RB LB : ℕ} {up dn : ℕ → ℕ} {c : Config} (hw : WordsBounded W c)
    (hR : DRegs A R K CB RB LB c) (hAW : A + 12 + 20 * R ≤ W) {st : BS} (hE : BEnc c.nmem A R st)
    {r L t i : ℕ} (h29 : c.nreg 60029 = r) (h28 : c.nreg 60028 = L)
    (h21 : c.nreg 60021 = t) (hLt : LB + L + t < A) (hi : c.nmem (LB + L + t) = i)
    (hiK : i < K) (hup : c.nmem (CB + 5 * i + 3) = up i) (hdn : c.nmem (CB + 5 * i + 4) = dn i)
    (hCB : CB + 5 * i + 4 < A) (hends : up i < R ∧ dn i < R)
    (h26 : c.nreg 60026 = st.tl)
    (htl : st.vis (if up i = r then dn i else up i) ≠ 1 → st.tl < R)
    (hKR : K < R) :
    ∃ c' k, Exec P W bfsInner c c' k ∧ k ≤ 40 ∧ DFr (A + 12) (A + 12 + 19 * R) c c' ∧
      BEnc c'.nmem A R (bstep up dn r st i) ∧ FFix BFields c.nmem c'.nmem A R ∧
      c'.nreg 60026 = (bstep up dn r st i).tl ∧ c'.nreg 60021 = t + 1 ∧
      (∀ x, (x = 60025 ∨ x = 60027 ∨ x = 60028 ∨ x = 60029) → c'.nreg x = c.nreg x) := by
  have hA12 : A ≤ W := by omega
  set s := (if up i = r then dn i else up i) with hsdef
  have hsR : s < R := by rw [hsdef]; splao
  have b2 := hR.b 2 (by norm_num)
  simp only [Nat.reduceAdd] at b2
  unfold bfsInner
  obtain ⟨c1, k1, e1, rfl, m1, s1, r32, r34, r35⟩ :=
    bfsRead_exec (P := P) hw hR hA12 h28 h21 hLt hi hup hdn hCB
  have hR1 : DRegs A R K CB RB LB c1 := hR.of_same s1 (by simp [Prot])
  have hw1 := e1.wb_right
  obtain ⟨c2, k2, e2, hk2, m2, s2, r36, r37⟩ := bfsSel_exec (P := P) hw1 r34 r35
    ((s1.1 _ (by simp)).trans h29) hR1.one hR1.zero
  have hR2 : DRegs A R K CB RB LB c2 := hR1.of_same s2 (by simp [Prot])
  have hw2 := e2.wb_right
  rw [← hsdef] at r36
  obtain ⟨c3, k3, e3, rfl, m3, s3, r38⟩ := ldF_rel (P := P) hw2 60038 2 60036
    (by rwo [show fb 2 = 60102 from rfl, hR2.b 2 (by norm_num), r36])
  have hw3 := e3.wb_right
  have hR3 : DRegs A R K CB RB LB c3 := hR2.of_same s3 (by simp [Prot])
  rw [show fb 2 = 60102 from rfl, hR2.b 2 (by norm_num), r36, m2, m1] at r38
  have hvis : c3.nreg 60038 = st.vis s := by rw [r38]; exact (hE s hsR).2.1
  have s13 : Same [60030, 60032, 60033, 60034, 60035, 60036, 60037, 60038] c c3 :=
    ((s1.mono (by simp)).trans (s2.mono (by simp))).trans (s3.mono (by simp))
  have m13 : c3.nmem = c.nmem := by rw [m3, m2, m1]
  refine spec_seq ⟨c1, 12, e1, spec_seq ⟨c2, k2, e2, spec_seq ⟨c3, 2, e3, ?_⟩⟩⟩
  by_cases hv : st.vis s = 1
  · -- `s` was already visited
    have hbs : bstep up dn r st i = st := by unfold bstep; rw [← hsdef, ite_eq_left hv]
    rw [hbs]
    refine spec_seq (ifEqN_eq (by rw [hvis, hv, hR3.one]) (spec_skip hw3 ?_))
    refine spec_instr (Exec.addN hw3 _ _ _ (by
      rwo [s13.1 _ (by simp), h21, hR3.one])) fun hw4 => ?_
    have s4 : Same [60030, 60032, 60033, 60034, 60035, 60036, 60037, 60038, 60021] c
        { c3 with nreg := upd c3.nreg 60021 (c3.nreg 60021 + c3.nreg 60011) } :=
      (s13.mono (by simp)).trans (Same.upd1 (by simp))
    refine ⟨by omega, DFr.of_same s4 (by simp [Prot]) (fun a _ => by config_simp; rw [m13]),
      by config_simp; rwx [m13], fun f _ _ j _ => by config_simp; rw [m13],
      by config_simp; rw [s13.1 _ (by simp), h26], ?_, fun x hx => ?_⟩
    · config_simp; rw [s13.1 _ (by simp), h21, hR3.one]
    · config_simp
      rw [Machine.upd_other _ _ _ (by omega)]
      exact s13.1 x (by sio)
  · -- `s` is new
    have htlR := htl hv
    refine spec_seq (ifEqN_ne (by rwx [hvis, hR3.one]) ?_)
    obtain ⟨c4, k4, e4, rfl, hf4, s4, r26, hv4⟩ := bfsNew_exec (P := P) hw3 hR3 hAW (sv := s)
      (tl := st.tl) (r := r) (i := i) (v := if up i = r then 1 else 0)
      (by rw [s3.1 _ (by simp), r36]) (by rw [s13.1 _ (by simp), h26])
      (by rw [s13.1 _ (by simp), h29]) (by rw [s3.1 _ (by simp), s2.1 _ (by simp), r32])
      (by rw [s3.1 _ (by simp), r37]) hsR htlR (by omega)
    refine ⟨c4, 13, e4, fun k' hk' => ?_⟩
    have hw4 := e4.wb_right
    have hR4  := hR3.frame hf4
    refine spec_instr (Exec.addN hw4 _ _ _ (by
      rwo [s4.1 _ (by simp), s13.1 _ (by simp), h21, hR4.one])) fun hw5 => ?_
    unfold bstep
    rw [← hsdef, ite_eq_right hv]
    have s45 : Same [60030, 60026, 60021] c4
        { c4 with nreg := upd c4.nreg 60021 (c4.nreg 60021 + c4.nreg 60011) } :=
      Same.upd1 (by simp)
    have hf5 : DFr (A + 12) (A + 12 + 19 * R) c
        { c4 with nreg := upd c4.nreg 60021 (c4.nreg 60021 + c4.nreg 60011) } :=
      (DFr.of_same s13 (by simp [Prot]) (fun a _ => by rw [m13])).trans
        (hf4.trans (DFr.of_same s45 (by simp [Prot]) (fun a _ => rfl)))
    refine ⟨by omega, hf5, fun j hj => ?_, fun f hf hnf j hj => ?_, ?_, ?_, fun x hx => ?_⟩
    · config_simp
      obtain ⟨o1, o2, o3, o4, o5, o6⟩ := hE j hj
      obtain ⟨v1, v2, v3, v4, v5, v6, -⟩ := hv4 j hj
      rw [m13] at v1 v2 v3 v4 v5 v6
      rw [v1, v2, v3, v4, v5, v6, o1, o2, o3, o4, o5, o6]
      simp only [Function.update_apply, and_self]
    · config_simp
      rw [(hv4 j hj).2.2.2.2.2.2 f hf hnf, m13]
    · config_simp; rw [r26]
    · config_simp; rw [s4.1 _ (by simp), s13.1 _ (by simp), h21, hR4.one]
    · config_simp
      rw [Machine.upd_other _ _ _ (by omega), s4.1 _ (by sio)]
      exact s13.1 x (by sio)

end inner




section loops

variable {P : Polygon} {W : ℕ}
variable {A R K CB RB LB : ℕ} {up dn : ℕ → ℕ} {lst : ℕ → List ℕ}

theorem take_succ_foldl (l : List ℕ) (f : BS → ℕ → BS) (st : BS) {t : ℕ} (ht : t < l.length) :
    (l.take (t + 1)).foldl f st = f ((l.take t).foldl f st) (l.getD t 0) := by
  rw [List.take_add_one, List.foldl_append, List.getElem?_eq_getElem ht]
  simp [List.getElem?_eq_getElem ht]

/-- **The scan of the list of the head region.** -/
theorem bfsInnerLoop_exec {c : Config} (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) (hEnv : InEnv c.nmem A R K CB RB LB up dn lst)
    (hends : ∀ i, i < K → up i < R ∧ dn i < R ∧ up i ≠ dn i)
    (hlists : ∀ r, r < R → ∀ i, i ∈ lst r ↔ i < K ∧ (up i = r ∨ dn i = r)) (hKR : K < R)
    {h : ℕ} {st : BS} (hI : BInv R K up dn lst h [] st) (hh : h < st.tl) (hE : BEnc c.nmem A R st)
    (h29 : c.nreg 60029 = st.ord h)
    (h28 : c.nreg 60028 = c.nmem (RB + 5 * st.ord h + 3))
    (h27 : c.nreg 60027 = (lst (st.ord h)).length) (h21 : c.nreg 60021 = 0)
    (h26 : c.nreg 60026 = st.tl) :
    ∃ c' k, Exec P W (.whileLtN 60021 60027 bfsInner) c c' k ∧
      k ≤ 42 * (lst (st.ord h)).length + 2 ∧ WordsBounded W c' ∧
      DFr (A + 12) (A + 12 + 19 * R) c c' ∧ BEnc c'.nmem A R (bouter up dn lst st h) ∧
      FFix BFields c.nmem c'.nmem A R ∧ c'.nreg 60026 = (bouter up dn lst st h).tl ∧
      c'.nreg 60025 = c.nreg 60025 := by
  set r := st.ord h with hrdef
  set l := lst r with hldef
  have hr  := (hI.ord_lt h hh).1
  let F : ℕ → BS := fun t => (l.take t).foldl (bstep up dn r) st
  have hmem : ∀ i ∈ l, i ∈ lst (st.ord h) := fun _ => id
  obtain ⟨c', k, e, ⟨hw', hf', ht', hE', hF', h26', hx'⟩, htest, hk⟩ :=
    Exec.whileLtN_potential (P := P) (W := W) (a := 60021) (b := 60027) (body := bfsInner)
    (fun d => WordsBounded W d ∧ DFr (A + 12) (A + 12 + 19 * R) c d ∧ d.nreg 60021 ≤ l.length ∧
      BEnc d.nmem A R (F (d.nreg 60021)) ∧ FFix BFields c.nmem d.nmem A R ∧
      d.nreg 60026 = (F (d.nreg 60021)).tl ∧
      (∀ x, (x = 60025 ∨ x = 60027 ∨ x = 60028 ∨ x = 60029) → d.nreg x = c.nreg x))
    (fun d => 42 * (l.length - d.nreg 60021)) (fun d hd => hd.1)
    (fun d ⟨hwd, hfd, htd, hEd, hFd, h26d, hxd⟩ htest => by
      have hRd := hR.frame hfd
      rw [hxd 60027 (by simp), h27] at htest
      set t := d.nreg 60021 with htdef
      have hEnvd := hEnv.transport (m' := d.nmem) fun a ha => hfd.2.2.2.2 a (Or.inl (by omega))
      obtain ⟨hlen, hRB⟩ := hEnvd.hlen r hr
      obtain ⟨hent, hLt⟩ := hEnvd.hent r hr t htest
      have hRBd : d.nmem (RB + 5 * r + 3) = c.nmem (RB + 5 * r + 3) :=
        hfd.2.2.2.2 _ (Or.inl (by omega))
      set i := l.getD t 0 with hidef
      have hil : i ∈ l := by rw [hidef, Dec.getD_of_lt htest]; exact List.getElem_mem htest
      obtain ⟨hiK, -⟩ := (hlists r hr i).1 hil
      obtain ⟨u1, u2, u3⟩ := hEnvd.hup i hiK
      -- the invariant of the partial fold
      have hIt := fold_inv hends hlists hh (l.take t) [] (fun j hj => hmem j (List.mem_of_mem_take hj)) hI
      obtain ⟨-, mo⟩ := fold_mono hends hlists r (l.take t) st
      have hordt  := mo h hh
      have hht  := lt_of_lt_of_le hh (fold_mono hends hlists r (l.take t) st).1
      have hIt' : BInv R K up dn lst h (l.take t).reverse (F t) := by simpa using hIt
      have hstep := bstep_inv hends hlists hIt' hht (i := i) (by rwx [hordt])
      rw [hordt] at hstep
      have htl : (F t).vis (if up i = r then dn i else up i) ≠ 1 → (F t).tl < R := by
        intro hv
        have := hstep.tl_le
        unfold bstep at this
        rw [ite_eq_right hv] at this
        exact this
      obtain ⟨d', k', e', hk', hf'', hE'', hF'', h26'', h21'', hx''⟩ :=
        bfsInner_exec (P := P) hwd hRd hAW hEd (r := r) (L := c.nmem (RB + 5 * r + 3))
          (t := t) (i := i) (by rw [hxd 60029 (by simp), h29])
          (by rw [hxd 60028 (by simp), h28]) rfl (by rwx [← hRBd]) (by rwx [← hRBd])
          hiK u1 u2 u3 ⟨(hends i hiK).1, (hends i hiK).2.1⟩ h26d htl hKR
      have hFs : F (t + 1) = bstep up dn r (F t) i := take_succ_foldl l _ st htest
      refine ⟨d', k', e', ⟨e'.wb_right, hfd.trans hf'', by rwo [h21''], ?_, ?_, ?_,
        fun x hx => (hx'' x hx).trans (hxd x hx)⟩, by rwo [h21'']⟩
      · rwx [h21'', hFs]
      · intro f hf hnf j hj; rw [hF'' f hf hnf j hj, hFd f hf hnf j hj]
      · rw [h26'', h21'', hFs])
    ⟨hw, DFr.refl _ _ c, by rwo [h21], by rw [h21]; simpa [F] using hE,
      fun f _ _ j _ => rfl, by rwr [h26, h21], fun _ _ => rfl⟩
  rw [hx' 60027 (by simp), h27] at htest
  have htl : c'.nreg 60021 = l.length := by omega
  have hFl : F l.length = bouter up dn lst st h := by
    simp only [F, List.take_length, bouter, ← hrdef, ← hldef]
  rw [htl, hFl] at hE' h26'
  refine ⟨c', k, e, by rwo [h21] at hk, hw', hf', hE', hF', h26', hx' 60025 (by simp)⟩

/-- **Dequeuing** the head region and locating its list. -/
theorem bfsDeq_exec {c : Config} (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {h r len : ℕ} (h25 : c.nreg 60025 = h) (hh : h < R)
    (hr : fv c.nmem A R 1 h = r) (hlen : c.nmem (RB + 5 * r + 2) = len) (hRB : RB + 5 * r + 3 < A) :
    ∃ c' k, Exec P W bfsDeq c c' k ∧ k = 12 ∧ c'.nmem = c.nmem ∧
      Same [60030, 60029, 60025, 60033, 60027, 60028, 60021] c c' ∧ c'.nreg 60029 = r ∧
      c'.nreg 60025 = h + 1 ∧ c'.nreg 60027 = len ∧ c'.nreg 60028 = c.nmem (RB + 5 * r + 3) ∧
      c'.nreg 60021 = 0 := by
  have b1 := hR.b 1 (by norm_num)
  simp only [Nat.reduceAdd] at b1
  have o := hR.one; have tw := hR.two; have hrb := hR.rRB
  have hr' : c.nmem (A + 12 + 1 * R + h) = r := hr
  unfold bfsDeq
  exec_block
  all_goals first
    | (config_simp; simp (config := { failIfUnchanged := false }) only [b1, h25, hr', hrb, o, tw]
       omega)
    | skip
  refine ⟨rfl, rfl, ⟨fun x hx => ?_, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    config_simp
    simp only [Machine.upd_other _ _ _ hx.1, Machine.upd_other _ _ _ hx.2.1,
      Machine.upd_other _ _ _ hx.2.2.1, Machine.upd_other _ _ _ hx.2.2.2.1,
      Machine.upd_other _ _ _ hx.2.2.2.2.1, Machine.upd_other _ _ _ hx.2.2.2.2.2.1,
      Machine.upd_other _ _ _ hx.2.2.2.2.2.2]
  · config_simp; rw [b1, h25, hr']
  · config_simp; rw [h25, o]
  · config_simp; simp only [b1, h25, hr', hrb, tw]; convert hlen using 2; ring
  · config_simp; simp only [b1, h25, hr', hrb, o, tw]; congr 1; ring
  · config_simp

/-- **The search**: from the initialised fields, the queue is run to exhaustion; the memory then
holds a search state with an empty queue. -/
theorem bfsS_exec {c : Config} (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) (hEnv : InEnv c.nmem A R K CB RB LB up dn lst)
    (hends : ∀ i, i < K → up i < R ∧ dn i < R ∧ up i ≠ dn i)
    (hlists : ∀ r, r < R → ∀ i, i ∈ lst r ↔ i < K ∧ (up i = r ∨ dn i = r)) (hKR : K < R)
    {D : ℕ} (hdeg : ∀ r, r < R → (lst r).length ≤ D)
    (hvis : ∀ j, j < R → fv c.nmem A R 2 j = if j = 0 then 1 else 0)
    (hord : fv c.nmem A R 1 0 = 0) :
    ∃ c' k, Exec P W bfsS c c' k ∧ k ≤ (42 * D + 16) * R + 6 ∧ WordsBounded W c' ∧
      DFr (A + 12) (A + 12 + 19 * R) c c' ∧ FFix BFields c.nmem c'.nmem A R ∧
      ∃ st : BS, BInv R K up dn lst st.tl [] st ∧ BEnc c'.nmem A R st := by
  have hR1 : 1 ≤ R := by omega
  obtain ⟨c1, k1, e1, rfl, hc1⟩ : ∃ c1 k1, Exec P W (block [.constN 60025 0, .constN 60026 1]) c c1 k1 ∧
      k1 = 2 ∧ c1 = { c with nreg := upd (upd c.nreg 60025 0) 60026 1 } := by
    exec_block
    · omega
    · omega
    · exact ⟨rfl, rfl⟩
  have hf1 : DFr (A + 12) (A + 12 + 19 * R) c c1 := by
    rw [hc1]
    refine DFr.nreg _ fun r hr _ => ?_
    unfold Prot at hr
    rw [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega)]
  let st0 : BS := ⟨fv c.nmem A R 2, fv c.nmem A R 1, fv c.nmem A R 3, fv c.nmem A R 4,
    fv c.nmem A R 5, fv c.nmem A R 6, 1⟩
  have hI0 : BInv R K up dn lst 0 [] st0 := binv_start hends hlists hR1 hvis hord rfl
  obtain ⟨c', k, e, ⟨hw', hf', st, hI, hE, h26, hF⟩, htest, hk⟩ :=
    Exec.whileLtN_potential (P := P) (W := W) (a := 60025) (b := 60026) (body := bfsOuter)
    (fun d => WordsBounded W d ∧ DFr (A + 12) (A + 12 + 19 * R) c d ∧ ∃ st : BS,
      BInv R K up dn lst (d.nreg 60025) [] st ∧ BEnc d.nmem A R st ∧ d.nreg 60026 = st.tl ∧
      FFix BFields c.nmem d.nmem A R)
    (fun d => (42 * D + 16) * (R - d.nreg 60025)) (fun d hd => hd.1)
    (fun d ⟨hwd, hfd, st, hId, hEd, h26d, hFd⟩ htest => by
      have hRd := hR.frame hfd
      set h := d.nreg 60025 with hhdef
      rw [h26d] at htest
      have htlR := hId.tl_le
      obtain ⟨hr, -⟩ := hId.ord_lt h htest
      have hEnvd := hEnv.transport (m' := d.nmem) fun a ha => hfd.2.2.2.2 a (Or.inl (by omega))
      obtain ⟨hlen, hRB⟩ := hEnvd.hlen _ hr
      obtain ⟨d1, k1, e1, rfl, m1, s1, r29, r25, r27, r28, r21⟩ :=
        bfsDeq_exec (P := P) hwd hRd hAW (h := h) (r := st.ord h) rfl (by omega) (hEd h (by omega)).1
          hlen hRB
      have hRd1 : DRegs A R K CB RB LB d1 := hRd.of_same s1 (by simp [Prot])
      obtain ⟨d2, k2, e2, hk2, hw2, hf2, hE2, hF2, h262, h252⟩ :=
        bfsInnerLoop_exec (P := P) e1.wb_right hRd1 hAW (by rwx [m1]) hends hlists hKR
          hId htest (by rwx [m1]) r29 (by rw [r28, m1]) r27 r21
          (by rwx [s1.1 _ (by simp)])
      have hdg := hdeg _ hr
      refine ⟨d2, 12 + k2, .seq e1 e2, ⟨hw2, ?_, bouter up dn lst st h, ?_, hE2, h262, ?_⟩, ?_⟩
      · exact hfd.trans ((DFr.of_same s1 (by simp [Prot]) (fun a _ => by rw [m1])).trans hf2)
      · rw [h252, r25]; exact bouter_inv hends hlists hId htest
      · intro f hf hnf j hj; rw [hF2 f hf hnf j hj, m1, hFd f hf hnf j hj]
      · rw [h252, r25]
        have : 42 * (lst (st.ord h)).length ≤ 42 * D := Nat.mul_le_mul_left _ hdg
        have h1 : (42 * D + 16) * (R - (h + 1)) + (42 * D + 16) = (42 * D + 16) * (R - h) := by
          rw [← Nat.mul_succ]; congr 1; omega
        omega)
    ⟨e1.wb_right, hf1, st0, by rw [hc1]; config_simp; exact hI0,
      by rw [hc1]; exact fun j hj => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, by rw [hc1]; csr,
      by rw [hc1]; exact fun _ _ _ _ _ => rfl⟩
  have hl := hI.h_lt
  rw [h26] at htest
  have hhe : c'.nreg 60025 = st.tl := by
    rcases hl with hl | ⟨hl, -⟩
    · omega
    · exact hl
  rw [hhe] at hI
  have h25 : c1.nreg 60025 = 0 := by rw [hc1]; config_simp
  unfold bfsS
  simp only [h25, Nat.sub_zero] at hk
  refine ⟨c', 2 + k, .seq e1 e, by omega, hw', hf', hF, st, hI, hE⟩

end loops

end

end Chazelle.Core.DecR
