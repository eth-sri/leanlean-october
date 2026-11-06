module

public import Chazelle.Core.RestoreTNorm
public import Chazelle.Core.RestoreTShotOps
public import Chazelle.Core.RestoreTPos

/-!
# WP-E, the candidate test on the RAM: the arc array of the region

The shot wrapper reads the arcs to shoot at from a contiguous array of 4-word records below the
allocator.  `arcBuild` copies the arcs of the region `r` there, each end normalised (`tNorm`):
record `j` at `base + 4 j` holds `normOf` of the ends of the `j`-th arc of the region, where
`base` (register `83081`) is the allocator on entry; the allocator ends at `base + 4 K`.

Registers: `83030` the place, `83031` the number `K` of arcs, `83033 … 83036` the ends read,
`83060 … 83064` and `83070 … 83074` the two ends being normalised.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim SignK

variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ c : Config}

/-! ## Programs without stores keep the memory -/

/-- A run step of a program without memory writes keeps the memory. -/
theorem RS.nomem {s : Stmt} {K : ℕ} {Q : Config → Prop} (hs : wr (fun _ => true) s = true)
    (h : RS P W c₀ s c K Q) : RS P W c₀ s c K (fun c' => Q c' ∧ c'.nmem = c.nmem) := by
  obtain ⟨c', k, ex, hk, hI, hrf, hq⟩ := h
  exact ⟨c', k, ex, hk, hI, hrf, hq, (exec_frameB ex hs).2.2.1⟩

/-- Registers other than the allocator. -/
def NotA (r : ℕ) : Bool := decide (r ≠ ALLOC)

/-- A run step of a program that writes neither the memory nor the allocator keeps both. -/
theorem RS.keepA {s : Stmt} {K : ℕ} {Q : Config → Prop} (hs : wr NotA s = true)
    (h : RS P W c₀ s c K Q) :
    RS P W c₀ s c K (fun c' => Q c' ∧ c'.nmem = c.nmem ∧ c'.nreg ALLOC = c.nreg ALLOC) := by
  obtain ⟨c', k, ex, hk, hI, hrf, hq⟩ := h
  have f := exec_frameB ex hs
  exact ⟨c', k, ex, hk, hI, hrf, hq, f.2.2.1, f.1 _ (by simp [NotA])⟩

theorem wr_notA_gKey (a b d e : ℕ) : wr NotA (gKey a b d e) = true :=
  wr_mono (wr_gKey a b d e) (fun r h => by simp [NotA, (opW_BgK r h).2])

theorem wr_notA_tNorm {s : ℕ} (hs : s + 4 < ALLOC ∨ ALLOC < s) : wr NotA (tNorm s) = true := by
  unfold ALLOC at hs
  simp only [tNorm, tNormK, cp2, wr, wrOK, wr_notA_gKey, Bool.and_true, Bool.true_and, NotA,
    ALLOC]
  simp only [Bool.and_eq_true]
  refine ⟨?_, ⟨⟨?_, ?_⟩, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> exact decide_eq_true (by omega)

theorem wr_notA_arcRead : wr NotA arcRead = true := by decide

/-! ## Storing a record -/

/-- Store the two ends `83060, 83061` and `83070, 83071` at the allocator and advance it. -/
def storeRec : Stmt := block [.storeN ALLOC 83060, .addN ALLOC ALLOC 83023,
  .storeN ALLOC 83061, .addN ALLOC ALLOC 83023, .storeN ALLOC 83070, .addN ALLOC ALLOC 83023,
  .storeN ALLOC 83071, .addN ALLOC ALLOC 83023]

theorem storeRec_exec (c : Config) (hw : WordsBounded W c) {a : ℕ} (hA : c.nreg ALLOC = a)
    (h23 : c.nreg 83023 = 1) (ha : a + 4 ≤ W) :
    ∃ c' k, Exec P W storeRec c c' k ∧ k = 8 ∧ c'.nreg ALLOC = a + 4 ∧
      c'.nmem = upd (upd (upd (upd c.nmem a (c.nreg 83060)) (a + 1) (c.nreg 83061))
        (a + 2) (c.nreg 83070)) (a + 3) (c.nreg 83071) ∧
      (∀ r, r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold storeRec
  have hA' : c.nreg 9999 = a := hA
  exec_block
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, hA', h23, ALLOC]; omega)
  refine ⟨rfl, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp (disch := omega) only [Machine.upd_same, Machine.upd_other, hA', h23,
      ALLOC]
  · simp (disch := omega) only [Machine.upd_other, hA', h23, ALLOC]
  · simp (disch := omega) only [Machine.upd_other]

/-- **Storing a record** as a run step. -/
theorem storeRec_rs (hI : TInv W c₀ c) (hroom : c.nreg ALLOC + 8 ≤ W) :
    RS P W c₀ storeRec c 8 (fun c' => c'.nreg ALLOC = c.nreg ALLOC + 4 ∧
      c'.nmem = upd (upd (upd (upd c.nmem (c.nreg ALLOC) (c.nreg 83060)) (c.nreg ALLOC + 1)
        (c.nreg 83061)) (c.nreg ALLOC + 2) (c.nreg 83070)) (c.nreg ALLOC + 3) (c.nreg 83071) ∧
      (∀ r, r ≠ ALLOC → c'.nreg r = c.nreg r)) := by
  obtain ⟨c', k, ex, hk, hA', hm, hr, hrr, hrm, ho⟩ := storeRec_exec (P := P) c hI.hw rfl hI.h23
    (by omega)
  have hA0 := hI.hA
  have mlow : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a := fun a ha => by
    rw [hm]; simp only [upd]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  refine ⟨c', k, ex, by omega, ⟨ex.wb_right, fun q h1 h2 => by
      rw [hr q (by unfold ALLOC; omega)]; exact hI.hin q h1 h2, by omega,
      fun a ha => by rw [mlow a (by omega)]; exact hI.hm a ha,
      by rw [hr _ (by unfold ALLOC; omega)]; exact hI.h20,
      by rw [hr _ (by unfold ALLOC; omega)]; exact hI.h21,
      by rw [hr _ (by unfold ALLOC; omega)]; exact hI.h22,
      by rw [hr _ (by unfold ALLOC; omega)]; exact hI.h23⟩,
    ⟨fun r _ hra => hr r hra, fun r _ => by rw [hrr], fun a ha => mlow a (by omega),
      fun a _ => by rw [hrm], ho, by omega, by omega⟩, hA', hm, hr⟩

/-! ## The arc ends of a chain model are inside the box band -/

/-- The box radius is determined by the chain model. -/
theorem radius_eq_of_model {C C' : Chain} (h : chainModel C = chainModel C') :
    C.radius = C'.radius := by
  have := congrArg (fun M : Model => (M.W.vtx 1).2) h
  simp only [chainModel, Chain.sideWalk_vtx_one] at this
  exact this

/-- **The ends of the arc records** of a nonempty family of a chain model are strictly inside the
height band of the box. -/
theorem arc_abs_lt {C : Chain} (hP : C.P.Simple) (hNF : IsNF (chainModel C) (Qof P) N)
    (hne : (N.F (chainModel C) (Qof P)).Nonempty) {j : ℕ} (hj : j < N.arcs.length) :
    |((chainModel C).pos (Qof P) (N.arc j).s).2| < C.radius ∧
      |((chainModel C).pos (Qof P) (N.arc j).e).2| < C.radius := by
  obtain ⟨hFam, -, -, reg, -, -, harcs, -, -, -, hpp⟩ := hNF
  obtain ⟨hs, he⟩ := hpp j hj
  have harc := (harcs.1 j hj).2
  obtain ⟨hcs, hce, -⟩ := WalkAx.arc_cuts hne harc
  have key : ∀ x : WPos, ProperPos (chainModel C) (Qof P) (Qof P).n x →
      (chainModel C).IsCut (N.F (chainModel C) (Qof P)) ((chainModel C).key (Qof P) x) →
      |((chainModel C).pos (Qof P) x).2| < C.radius := by
    intro x hx hcut
    obtain ⟨c, hc, p, t, hA, hk⟩ := hcut
    obtain ⟨hpp, htt⟩ := Chazelle.Chain.sideKey_inj hx.1 hx.2.1 hA.2.1 hA.2.2.1 hk
    rw [← hpp, ← htt] at hA
    exact chord_height_lt hP (hFam.2.1 hc) hA.2.2.2.1
  exact ⟨key _ hs hcs, key _ he hce⟩

/-- The arc ends of a run are inside the box band, for every chain of the model. -/
theorem TGood.arc_abs (hE : TGood P W M N c₀) (hne : (N.F M (Qof P)).Nonempty) {j : ℕ}
    (hj : j < N.arcs.length) :
    (∀ C : Chain, M = chainModel C → |(M.pos (Qof P) (N.arc j).s).2| < C.radius) ∧
      (∀ C : Chain, M = chainModel C → |(M.pos (Qof P) (N.arc j).e).2| < C.radius) := by
  refine ⟨fun C hM => ?_, fun C hM => ?_⟩ <;>
  · obtain ⟨C', hs, hM'⟩ := hE.chain_simple hM
    have hNF := hE.hNF
    rw [hM'] at hNF hne
    have := arc_abs_lt hs hNF hne hj
    rw [radius_eq_of_model (hM.symm.trans hM'), hM']
    first | exact this.1 | exact this.2

/-! ## The loop -/

/-- The normalised ends of the arc at place `t` of region `r`. -/
noncomputable def nArc (M : Model) (Q : Polygon) (N : NF) (r t : ℕ) : WPos × WPos :=
  (normOf M Q (N.arc (arcAt N r t)).s, normOf M Q (N.arc (arcAt N r t)).e)

/-- **One arc**: read, normalise, store, advance. -/
def buildBody : Stmt :=
  .seq arcRead (.seq (.instr (.copyN 83060 83033)) (.seq (.instr (.copyN 83061 83034))
    (.seq (.instr (.copyN 83070 83035)) (.seq (.instr (.copyN 83071 83036))
      (.seq (tNorm 83060) (.seq (tNorm 83070) (.seq storeRec
        (.instr (.addN 83030 83030 83023)))))))))

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

theorem arcAt_upd4 {m : ℕ → ℕ} {base t j : ℕ} {v0 v1 v2 v3 : ℕ} (hj : j < t) :
    ShotList.arcAt (upd (upd (upd (upd m (base + 4 * t) v0) (base + 4 * t + 1) v1)
      (base + 4 * t + 2) v2) (base + 4 * t + 3) v3) base j = ShotList.arcAt m base j := by
  simp only [ShotList.arcAt, upd]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

theorem arcAt_upd4_new {m : ℕ → ℕ} {base t : ℕ} {v0 v1 v2 v3 : ℕ} :
    ShotList.arcAt (upd (upd (upd (upd m (base + 4 * t) v0) (base + 4 * t + 1) v1)
      (base + 4 * t + 2) v2) (base + 4 * t + 3) v3) base t = (⟨v0, v1⟩, ⟨v2, v3⟩) := by
  simp only [ShotList.arcAt, upd]
  simp (disch := omega) only [ite_eq_right, ↓reduceIte]

set_option maxHeartbeats 1000000 in
/-- **One arc of the loop.** -/
theorem buildBody_rs (hE : TGood P W M N c₀) (hne : (N.F M (Qof P)).Nonempty) {K base : ℕ}
    {cB : Config} (hI : TInv W c₀ c)
    (hB : BuildI M (Qof P) N (c₀.nreg 83002) K base cB c)
    (hK : K = (N.region (c₀.nreg 83002)).arcs.length) (hlt : c.nreg 83030 < c.nreg 83031)
    (hroom : c.nreg ALLOC + bodyK ≤ W) :
    RS P W c₀ buildBody c bodyK (fun c' => BuildI M (Qof P) N (c₀.nreg 83002) K base cB c' ∧
      c'.nreg 83030 = c.nreg 83030 + 1) := by
  obtain ⟨h31, h81, htK, hA, hrec, hag⟩ := hB
  set t := c.nreg 83030
  set r := c₀.nreg 83002
  have htl : t < (N.region r).arcs.length := by rw [← hK]; omega
  obtain ⟨hjl, -⟩ := arcAt_lt hE htl
  set j := arcAt N r t
  have hQn : (Qof P).n = P.n := shear_n _ _
  obtain ⟨hps, hpe⟩ : ProperPos M (Qof P) (Qof P).n (N.arc j).s ∧
      ProperPos M (Qof P) (Qof P).n (N.arc j).e := by
    obtain ⟨-, -, -, reg, -, -, -, -, -, -, hpp⟩ := hE.hNF
    exact hpp j hjl
  rw [hQn] at hps hpe
  obtain ⟨gs, ge⟩ := hE.arcPosG hne hjl
  obtain ⟨ys, ye⟩ := hE.arc_abs hne hjl
  have sc : ∀ q, q ∈ buildL → Scr q := by
    intro q hq; simp only [buildL, List.mem_cons, List.not_mem_nil, or_false] at hq
    unfold Scr; omega
  unfold bodyK at hroom ⊢
  refine RS.mono (K := 80 + (1 + (1 + (1 + (1 + (normK + (normK + (8 + 1)))))))) ?_
    (by omega) (fun _ h => h)
  refine RS.seq (RS.keepA wr_notA_arcRead (arcRead_rs hE hI (by omega) (by omega)))
    fun c₁ hI₁ hA₁ ⟨⟨v33, v34, v35, v36, a₁⟩, m₁, al₁⟩ => ?_
  have cp : ∀ {cc : Config} (r a : ℕ), TInv W c₀ cc → r ∈ buildL →
      RS P W c₀ (.instr (.copyN r a)) cc 1 (fun c' => (c'.nreg = upd cc.nreg r (cc.nreg a)) ∧
        c'.nmem = cc.nmem ∧ c'.nreg ALLOC = cc.nreg ALLOC) := fun r a hIc hr =>
    (RS.keepA (by
      have : r ≠ ALLOC := by
        simp only [buildL, List.mem_cons, List.not_mem_nil, or_false] at hr; unfold ALLOC; omega
      simp [wr, wrOK, NotA, this]) (RS.copy hIc (sc r hr)))
  refine RS.seq (cp 83060 83033 hI₁ (by simp [buildL])) fun c₂ hI₂ hA₂ ⟨hc₂, m₂, al₂⟩ => ?_
  refine RS.seq (cp 83061 83034 hI₂ (by simp [buildL])) fun c₃ hI₃ hA₃ ⟨hc₃, m₃, al₃⟩ => ?_
  refine RS.seq (cp 83070 83035 hI₃ (by simp [buildL])) fun c₄ hI₄ hA₄ ⟨hc₄, m₄, al₄⟩ => ?_
  refine RS.seq (cp 83071 83036 hI₄ (by simp [buildL])) fun c₅ hI₅ hA₅ ⟨hc₅, m₅, al₅⟩ => ?_
  -- the registers after the copies
  have v60 : c₅.nreg 83060 = (N.arc j).s.edge := by
    rw [hc₅, upd_ne (by omega), hc₄, upd_ne (by omega), hc₃, upd_ne (by omega), hc₂, upd_eq, v33]
  have v61 : c₅.nreg 83061 = (N.arc j).s.hgt := by
    rw [hc₅, upd_ne (by omega), hc₄, upd_ne (by omega), hc₃, upd_eq, hc₂, upd_ne (by omega), v34]
  have v70 : c₅.nreg 83070 = (N.arc j).e.edge := by
    rw [hc₅, upd_ne (by omega), hc₄, upd_eq, hc₃, upd_ne (by omega), hc₂, upd_ne (by omega), v35]
  have v71 : c₅.nreg 83071 = (N.arc j).e.hgt := by
    rw [hc₅, upd_eq, hc₄, upd_ne (by omega), hc₃, upd_ne (by omega), hc₂, upd_ne (by omega), v36]
  have m15 : c₅.nmem = c.nmem := by rw [m₅, m₄, m₃, m₂, m₁]
  have A15 : c₅.nreg ALLOC = c.nreg ALLOC := by rw [al₅, al₄, al₃, al₂, al₁]
  have ag5 : Agr c c₅ [83032, 83033, 83034, 83035, 83036, 83060, 83061, 83070, 83071] :=
    ((((a₁.trans (Agr.of_upd hc₂)).trans (Agr.of_upd hc₃)).trans (Agr.of_upd hc₄)).trans
      (Agr.of_upd hc₅)).mono (by simp)
  -- normalise the start
  have ps : (⟨c₅.nreg 83060, c₅.nreg 83061⟩ : WPos) = (N.arc j).s := by rw [v60, v61]
  refine RS.seq (RS.keepA (wr_notA_tNorm (by unfold ALLOC; omega)) (tNorm_rs (s := 83060)
    ⟨sc _ (by simp [buildL]), sc _ (by simp [buildL]), sc _ (by simp [buildL]),
      sc _ (by simp [buildL]), sc _ (by simp [buildL])⟩ hE hI₅ (by rwa [ps])
    (by rw [v60]; exact gs.1) (by rwa [ps]) (by rw [A15]; omega)))
    fun c₆ hI₆ hA₆ ⟨⟨n60, n6, a₆⟩, m₆, al₆⟩ => ?_
  have k6 : ∀ q, 80000 ≤ q → q < 90000 → q ≠ 83061 → q ≠ 83062 → q ≠ 83063 → q ≠ 83064 →
      c₆.nreg q = c₅.nreg q := fun q h1 h2 h3 h4 h5 h6 => a₆ q h1 h2 (by simp; omega)
  have pe : (⟨c₆.nreg 83070, c₆.nreg 83071⟩ : WPos) = (N.arc j).e := by
    rw [k6 83070 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega),
      k6 83071 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega), v70, v71]
  refine RS.seq (RS.keepA (wr_notA_tNorm (by unfold ALLOC; omega)) (tNorm_rs (s := 83070)
    ⟨sc _ (by simp [buildL]), sc _ (by simp [buildL]), sc _ (by simp [buildL]),
      sc _ (by simp [buildL]), sc _ (by simp [buildL])⟩ hE hI₆ (by rwa [pe])
    (by rw [k6 83070 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega),
      v70]; exact ge.1) (by rwa [pe])
      (by rw [al₆, A15]; omega)))
    fun c₇ hI₇ hA₇ ⟨⟨n70, n7, a₇⟩, m₇, al₇⟩ => ?_
  have k7 : ∀ q, 80000 ≤ q → q < 90000 → q ≠ 83071 → q ≠ 83072 → q ≠ 83073 → q ≠ 83074 →
      c₇.nreg q = c₆.nreg q := fun q h1 h2 h3 h4 h5 h6 => a₇ q h1 h2 (by simp; omega)
  have A7 : c₇.nreg ALLOC = c.nreg ALLOC := by rw [al₇, al₆, A15]
  have M7 : c₇.nmem = c.nmem := by rw [m₇, m₆, m15]
  have w60 : c₇.nreg 83060 = c₆.nreg 83060 :=
    k7 _ (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)
  have w61 : c₇.nreg 83061 = c₆.nreg 83061 :=
    k7 _ (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)
  have ns : (⟨c₇.nreg 83060, c₇.nreg 83061⟩ : WPos) = normOf M (Qof P) (N.arc j).s := by
    rw [w60, w61, n6, ps]
  have ne' : (⟨c₇.nreg 83070, c₇.nreg 83071⟩ : WPos) = normOf M (Qof P) (N.arc j).e := by
    rw [n7, pe]
  -- store the record
  refine RS.seq (storeRec_rs hI₇ (by rw [A7]; omega))
    fun c₈ hI₈ hA₈ ⟨A8, M8, R8⟩ => ?_
  have k8 : c₈.nreg 83030 = t := by
    rw [R8 _ (by unfold ALLOC; omega), k7 _ (by norm_num) (by norm_num) (by omega) (by omega)
      (by omega) (by omega), k6 _ (by norm_num) (by norm_num) (by omega) (by omega) (by omega)
      (by omega), ag5 _ (by norm_num) (by norm_num) (by simp)]
  refine (RS.nomem rfl (RS.add hI₈ (r := 83030) (a := 83030) (b := 83023) (sc _ (by simp [buildL]))
    (by rw [k8, hI₈.h23]; omega))).mono le_rfl fun c₉ ⟨hc₉, M9⟩ => ?_
  have ag9 : Agr c c₉ buildL := by
    have a78 : Agr c₇ c₈ [] := fun q h1 h2 _ => R8 q (by unfold ALLOC; omega)
    exact ((((ag5.trans a₆).trans a₇).trans a78).trans (Agr.of_upd hc₉)).mono (by
      intro q hq; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
      simp only [buildL, List.mem_cons, List.not_mem_nil, or_false]; omega)
  have q30 : c₉.nreg 83030 = t + 1 := by rw [hc₉, upd_eq, k8, hI₈.h23]
  have hA9 : c₉.nreg ALLOC = c.nreg ALLOC + 4 := by
    rw [hc₉, upd_ne (by unfold ALLOC; omega), A8, A7]
  have hM9 : c₉.nmem = upd (upd (upd (upd c.nmem (base + 4 * t) (c₇.nreg 83060))
      (base + 4 * t + 1) (c₇.nreg 83061)) (base + 4 * t + 2) (c₇.nreg 83070))
      (base + 4 * t + 3) (c₇.nreg 83071) := by rw [M9, M8, A7, hA, M7]
  refine ⟨⟨by rw [ag9 _ (by norm_num) (by norm_num) (by simp [buildL]), h31],
    by rw [ag9 _ (by norm_num) (by norm_num) (by simp [buildL]), h81], by omega,
    by rw [hA9, hA, q30]; ring, fun j' hj' => ?_, (hag.trans ag9).mono (by simp)⟩, q30⟩
  rw [q30] at hj'
  rw [hM9]
  rcases Nat.lt_or_ge j' t with hl | hg
  · rw [arcAt_upd4 hl]; exact hrec j' hl
  · have : j' = t := by omega
    subst this
    rw [arcAt_upd4_new]
    unfold nArc
    rw [← ns, ← ne']

/-- **The arc array of the region** at the allocator. -/
def arcBuild : Stmt :=
  .seq (.instr (.constN 83030 0)) (.seq (.instr (.copyN 83081 ALLOC))
    (.seq (tRegLen 0) (.seq (.instr (.copyN 83031 50210)) (.whileLtN 83030 83031 buildBody))))

/-- The cost of the arc array for `K` arcs. -/
def buildK (K : ℕ) : ℕ := 20 + (bodyK + 2) * K

/-- **The arc array.** -/
theorem arcBuild_rs (hE : TGood P W M N c₀) (hne : (N.F M (Qof P)).Nonempty) (hI : TInv W c₀ c)
    (hroom : c.nreg ALLOC + buildK (N.region (c₀.nreg 83002)).arcs.length ≤ W) :
    RS P W c₀ arcBuild c (buildK (N.region (c₀.nreg 83002)).arcs.length) (fun c' =>
      c'.nreg 83081 = c.nreg ALLOC ∧
      c'.nreg ALLOC = c.nreg ALLOC + 4 * (N.region (c₀.nreg 83002)).arcs.length ∧
      c'.nreg 83031 = (N.region (c₀.nreg 83002)).arcs.length ∧
      (∀ j, j < (N.region (c₀.nreg 83002)).arcs.length →
        ShotList.arcAt c'.nmem (c.nreg ALLOC) j = nArc M (Qof P) N (c₀.nreg 83002) j) ∧
      Agr c c' (83031 :: 83081 :: 50210 :: buildL)) := by
  set K := (N.region (c₀.nreg 83002)).arcs.length with hKd
  set base := c.nreg ALLOC
  have sc : ∀ q, q ∈ buildL → Scr q := by
    intro q hq; simp only [buildL, List.mem_cons, List.not_mem_nil, or_false] at hq
    unfold Scr; omega
  unfold buildK at hroom ⊢
  refine RS.mono (K := 1 + (1 + (13 + (1 + ((bodyK + 2) * K + 2))))) ?_ (by omega) (fun _ h => h)
  refine RS.seq (RS.const hI (r := 83030) (v := 0) (sc _ (by simp [buildL])) (Nat.zero_le _))
    fun c₁ hI₁ hA₁ hc₁ => ?_
  have A1 : c₁.nreg ALLOC = base := by rw [hc₁, upd_ne (by unfold ALLOC; omega)]
  refine RS.seq (RS.copy hI₁ (r := 83081) (a := ALLOC) (by unfold Scr; omega))
    fun c₂ hI₂ hA₂ hc₂ => ?_
  have A2 : c₂.nreg ALLOC = base := by rw [hc₂, upd_ne (by unfold ALLOC; omega), A1]
  obtain ⟨c₃, k₃, e₃, hk₃, v₃, st₃⟩ := tRegLen_exec (f := 0) (Or.inl rfl) hE hI₂ (by omega)
  refine RS.seq (RS.keepA (by decide) (RS.op (Q := fun c' => c'.nreg 50210 = K)
    ⟨c₃, k₃, e₃, hk₃, v₃, st₃⟩)) fun c₃ hI₃ hA₃ ⟨⟨v3, h83⟩, _, A3⟩ => ?_
  refine RS.seq (RS.copy hI₃ (r := 83031) (a := 50210) (by unfold Scr; omega))
    fun c₄ hI₄ hA₄ hc₄ => ?_
  have A4 : c₄.nreg ALLOC = base := by rw [hc₄, upd_ne (by unfold ALLOC; omega), A3, A2]
  have ag4 : Agr c c₄ [83030, 83081, 83031] :=
    (((Agr.of_upd hc₁).trans (Agr.of_upd hc₂)).trans ((Agr.of_band h83 []).trans
      (Agr.of_upd hc₄))).mono (by simp)
  have q31 : c₄.nreg 83031 = K := by rw [hc₄, upd_eq, v3]
  have q81 : c₄.nreg 83081 = base := by
    rw [hc₄, upd_ne (by omega), h83 _ (by norm_num) (by norm_num), hc₂, upd_eq, A1]
  have q30 : c₄.nreg 83030 = 0 := by
    rw [hc₄, upd_ne (by omega), h83 _ (by norm_num) (by norm_num), hc₂, upd_ne (by omega), hc₁,
      upd_eq]
  have I4 : BuildI M (Qof P) N (c₀.nreg 83002) K base c₄ c₄ :=
    ⟨q31, q81, by omega, by rw [A4, q30]; ring, fun j hj => by omega, Agr.refl _ _⟩
  refine (RS.while (BuildI M (Qof P) N (c₀.nreg 83002) K base c₄)
    (fun cc => K - cc.nreg 83030) bodyK
    (fun cc hcc hlt => by obtain ⟨h1, -, -, -, -, -⟩ := hcc; omega)
    (fun cc hIc hcc hlt hr => (buildBody_rs hE hne hIc hcc hKd hlt hr).mono le_rfl
      fun c' ⟨h1, h2⟩ => ⟨h1, by obtain ⟨h31, -, h3, -⟩ := hcc; omega⟩)
    hI₄ I4 (by rw [A4, q30, Nat.sub_zero]; omega)).mono (by rw [q30, Nat.sub_zero])
    fun c' ⟨hB, hnlt⟩ => ?_
  obtain ⟨h31, h81, htK, hA', hrec, hag⟩ := hB
  have ht : c'.nreg 83030 = K := by omega
  refine ⟨h81, by rw [hA', ht], h31, fun j hj => hrec j (by omega), ?_⟩
  exact (ag4.trans hag).mono (by
    intro q hq
    simp only [buildL, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    simp only [buildL, List.mem_cons, List.not_mem_nil, or_false]; omega)

end

end Restore

end Chazelle.Core
