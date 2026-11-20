module

public import Chazelle.Core.GranRamApp

/-!
# WP-F, RAM part 6: the removal, first half

* `Enc.mem_congr`, `Enc.st_congr`: the encoding only depends on the state area and on the
  fields in range;
* `gatherStmt`: the exit list `St.newEx c` of the merged class is gathered into the scratch
  area (`gather_exec`);
* `relLoop`: the exits of the class `Y` are relabelled to `X` (`relLoop_exec`).
-/

namespace Chazelle.Core

namespace Gran

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-! ## Congruences of the encoding -/

theorem Enc.mem_congr {m m' : ℕ → ℕ} {d : Dm} {st : St} (h : Enc m d st)
    (hm : ∀ a, d.b0 ≤ a → a < d.b0 + d.oTmp → m' a = m a) : Enc m' d st := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_,
    fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x t hx ht => ?_, fun j hj => ?_,
    fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun t ht => ?_⟩
  · rw [hm _ (by omega) (by dm_simp; omega)]; exact h.live i hi
  · rw [hm _ (by dm_simp; omega) (by dm_simp; omega)]; exact h.s0 i hi
  · rw [hm _ (by dm_simp; omega) (by dm_simp; omega)]; exact h.s1 i hi
  · rw [hm _ (by dm_simp; omega) (by dm_simp; omega)]; exact h.nd0 i hi
  · rw [hm _ (by dm_simp; omega) (by dm_simp; omega)]; exact h.nd1 i hi
  · rw [hm _ (by dm_simp; omega) (by dm_simp; omega)]; exact h.deg x hx
  · rw [hm _ (by dm_simp; omega) (by dm_simp; omega)]; exact h.wt x hx
  · rw [hm _ (by dm_simp; omega) (by dm_simp; omega)]; exact h.exb x hx
  · have := slot_lt (R := d.R) hx ht
    rw [hm _ (by dm_simp; omega) (by dm_simp; omega)]; exact h.ex x t hx ht
  · rw [hm _ (by dm_simp; omega) (by dm_simp; omega)]; exact h.cnt j hj
  · rw [hm _ (by dm_simp; omega) (by dm_simp; omega)]; exact h.nxt j hj
  · rw [hm _ (by dm_simp; omega) (by dm_simp; omega)]; exact h.prv j hj
  · rw [hm _ (by dm_simp; omega) (by dm_simp; omega)]; exact h.eg j hj
  · rw [hm _ (by dm_simp; omega) (by dm_simp; omega)]; exact h.pz j hj
  · rw [hm _ (by dm_simp; omega) (by dm_simp; omega)]; exact h.stk t ht

theorem Enc.st_congr {m : ℕ → ℕ} {d : Dm} {st st' : St} (h : Enc m d st)
    (h1 : ∀ i, i < d.K → st'.live i = st.live i) (h2 : ∀ i, i < d.K → st'.s0 i = st.s0 i)
    (h3 : ∀ i, i < d.K → st'.s1 i = st.s1 i) (h4 : ∀ i, i < d.K → st'.nd0 i = st.nd0 i)
    (h5 : ∀ i, i < d.K → st'.nd1 i = st.nd1 i) (h6 : ∀ x, x < d.R → st'.deg x = st.deg x)
    (h7 : ∀ x, x < d.R → st'.wt x = st.wt x)
    (h8 : ∀ x t, x < d.R → t < d.D → st'.ex x t = st.ex x t)
    (h9 : ∀ j, j < d.A → st'.cnt j = st.cnt j) (h10 : ∀ j, j < d.A → st'.nxt j = st.nxt j)
    (h11 : ∀ j, j < d.A → st'.prv j = st.prv j) (h12 : ∀ j, j < d.A → st'.eg j = st.eg j)
    (h13 : ∀ j, j < d.A → st'.pz j = st.pz j) (h14 : ∀ t, t < d.cap → st'.stk t = st.stk t) :
    Enc m d st' :=
  ⟨fun i hi => (h.live i hi).trans (h1 i hi).symm, fun i hi => (h.s0 i hi).trans (h2 i hi).symm,
    fun i hi => (h.s1 i hi).trans (h3 i hi).symm, fun i hi => (h.nd0 i hi).trans (h4 i hi).symm,
    fun i hi => (h.nd1 i hi).trans (h5 i hi).symm, fun x hx => (h.deg x hx).trans (h6 x hx).symm,
    fun x hx => (h.wt x hx).trans (h7 x hx).symm, h.exb,
    fun x t hx ht => (h.ex x t hx ht).trans (h8 x t hx ht).symm,
    fun j hj => (h.cnt j hj).trans (h9 j hj).symm, fun j hj => (h.nxt j hj).trans (h10 j hj).symm,
    fun j hj => (h.prv j hj).trans (h11 j hj).symm, fun j hj => (h.eg j hj).trans (h12 j hj).symm,
    fun j hj => (h.pz j hj).trans (h13 j hj).symm, fun t ht => (h.stk t ht).trans (h14 t ht).symm⟩

/-! ## List facts -/

theorem exl_length (st : St) (x : ℕ) : (st.exl x).length = st.deg x := by
  unfold St.exl; rw [List.length_ofFn]

theorem exl_getD (st : St) {x t : ℕ} (ht : t < st.deg x) : (st.exl x).getD t 0 = st.ex x t := by
  unfold St.exl
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [ht]

theorem getD_not_mem_take {l : List ℕ} (hl : l.Nodup) {t : ℕ} (ht : t < l.length) :
    l.getD t 0 ∉ l.take t := by
  intro hm
  have e := List.take_append_drop t l
  rw [List.drop_eq_getElem_cons ht] at e
  rw [← e, List.nodup_append] at hl
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some] at hm
  exact hl.2.2 _ hm _ List.mem_cons_self rfl

theorem mem_take_succ {l : List ℕ} {t : ℕ} (ht : t < l.length) (a : ℕ) :
    a ∈ l.take (t + 1) ↔ a ∈ l.take t ∨ a = l.getD t 0 := by
  rw [List.take_add_one, List.getElem?_eq_getElem ht, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem ht]
  simp only [List.mem_append, Option.toList_some, List.mem_singleton, Option.getD_some]

theorem slot_le {D x t R : ℕ} (hx : x < R) (ht : t ≤ D) : D * x + t ≤ R * D := by
  have : D * x + t ≤ D * (x + 1) := by rw [Nat.mul_succ]; omega
  have : D * (x + 1) ≤ D * R := Nat.mul_le_mul_left _ (by omega)
  rw [Nat.mul_comm R]; omega

/-- Layout facts. -/
theorem Dm.lay (d : Dm) : d.oExb + d.R = d.oEx ∧ d.oEx + d.R * d.D ≤ d.oTmp ∧
    d.oTmp + d.D + 1 ≤ d.oEnd ∧ d.oStk + d.cap = d.oTmp ∧ d.oS0 = d.K ∧ d.oS1 = 2 * d.K ∧
    d.oDeg = 5 * d.K ∧ d.oWt = 5 * d.K + d.R ∧ d.oExb = 5 * d.K + 2 * d.R ∧
    d.oCnt = d.oEx + d.R * d.D ∧ d.oNxt = d.oCnt + d.A ∧ d.oPrv = d.oNxt + d.A ∧
    d.oEg = d.oPrv + d.A ∧ d.oPz = d.oEg + d.A ∧ d.oStk = d.oPz + d.A := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp only [Dm.oS0, Dm.oS1, Dm.oDeg, Dm.oWt, Dm.oExb, Dm.oEx,
    Dm.oCnt, Dm.oNxt, Dm.oPrv, Dm.oEg, Dm.oPz, Dm.oStk, Dm.cap, Dm.oTmp, Dm.oList, Dm.oEnd] <;>
  omega

/-! ## Gathering the merged exit list -/

/-- Load the exit bases of `X`, `Y` and clear the counters. -/
def rmHead : Stmt := block [.addN 90105 90037 90064, .loadN 90103 90105,
  .addN 90105 90037 90065, .loadN 90104 90105, .constN 90100 0, .constN 90101 0]

/-- Gather `newEx c` into the scratch area. -/
def gatherStmt : Stmt :=
  .seq rmHead (.seq (appLoop 90103 90066) (.seq (.instr (.constN 90101 0)) (appLoop 90104 90067)))

/-- The registers `90100 … 90109`. -/
def Brm (r : ℕ) : Bool := decide (90100 ≤ r ∧ r < 90110)

theorem wrS_gather : wrS Brm gatherStmt = true := by decide

theorem gather_exec {P : Polygon} {W : ℕ} {E : Env} {d : Dm} {st : St} {c : Config}
    (hw : WordsBounded W c) (hC : Cst c E d) (henc : Enc c.nmem d st) (hD : DimOK E d W)
    {cc X Y : ℕ} (hX : X < E.R) (hY : Y < E.R) (hdX : st.deg X ≤ E.D) (hdY : st.deg Y ≤ E.D)
    (hroom : ((st.exl X).filter (· != cc)).length + st.deg Y ≤ E.D + 1)
    (h62 : c.nreg 90062 = cc) (h64 : c.nreg 90064 = X) (h65 : c.nreg 90065 = Y)
    (h66 : c.nreg 90066 = st.deg X) (h67 : c.nreg 90067 = st.deg Y) :
    ∃ c' k, Exec P W gatherStmt c c' k ∧ k ≤ 28 * E.D + 20 ∧
      c'.nreg 90100 = ((st.exl X).filter (· != cc) ++ (st.exl Y).filter (· != cc)).length ∧
      c'.nreg 90103 = d.b0 + d.oEx + d.D * X ∧ c'.nreg 90104 = d.b0 + d.oEx + d.D * Y ∧
      (∀ i, i < c'.nreg 90100 → c'.nmem (d.b0 + d.oTmp + i) =
        ((st.exl X).filter (· != cc) ++ (st.exl Y).filter (· != cc)).getD i 0) ∧
      (∀ a, (a < d.b0 + d.oTmp ∨ d.b0 + d.oTmp + (d.D + 1) ≤ a) → c'.nmem a = c.nmem a) ∧
      FrameS Brm c c' := by
  suffices hh : ∃ c' k, Exec P W gatherStmt c c' k ∧ k ≤ 28 * E.D + 20 ∧
      c'.nreg 90100 = ((st.exl X).filter (· != cc) ++ (st.exl Y).filter (· != cc)).length ∧
      c'.nreg 90103 = d.b0 + d.oEx + d.D * X ∧ c'.nreg 90104 = d.b0 + d.oEx + d.D * Y ∧
      (∀ i, i < c'.nreg 90100 → c'.nmem (d.b0 + d.oTmp + i) =
        ((st.exl X).filter (· != cc) ++ (st.exl Y).filter (· != cc)).getD i 0) ∧
      (∀ a, (a < d.b0 + d.oTmp ∨ d.b0 + d.oTmp + (d.D + 1) ≤ a) → c'.nmem a = c.nmem a) by
    obtain ⟨c', k, e, h1, h2, h3, h4, h5, h6⟩ := hh
    exact ⟨c', k, e, h1, h2, h3, h4, h5, h6, exec_frameS e wrS_gather⟩
  have hb := hD.base
  have hW3 := hD.W1
  obtain ⟨y1, y2, y3, -⟩ := d.lay
  rw [← hD.R] at hX hY
  rw [← hD.D] at hdX hdY hroom
  have eX : c.nmem (d.b0 + d.oExb + X) = d.b0 + d.oEx + d.D * X := henc.exb X hX
  have eY : c.nmem (d.b0 + d.oExb + Y) = d.b0 + d.oEx + d.D * Y := henc.exb Y hY
  have sX := slot_le (R := d.R) (D := d.D) hX (le_refl _)
  have sY := slot_le (R := d.R) (D := d.D) hY (le_refl _)
  have sX' := slot_le (R := d.R) (D := d.D) hX hdX
  have sY' := slot_le (R := d.R) (D := d.D) hY hdY
  -- the head
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W rmHead c c₁ k₁ ∧ k₁ = 6 ∧
      (c₁.nreg 90103 = d.b0 + d.oEx + d.D * X ∧ c₁.nreg 90104 = d.b0 + d.oEx + d.D * Y ∧
        c₁.nreg 90100 = 0 ∧ c₁.nreg 90101 = 0 ∧
        (∀ r, r ≠ 90100 → r ≠ 90101 → r ≠ 90103 → r ≠ 90104 → r ≠ 90105 →
          c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem) := by
    unfold rmHead
    exec_block
    · rw [hC.bExb, h64]; omega
    · config_simp; rw [hC.bExb, h65]; omega
    · omega
    · omega
    · refine ⟨rfl, ?_, ?_, ?_, ?_, fun r a1 a2 a3 a4 a5 => by simp [upd, a1, a2, a3, a4, a5],
        rfl⟩ <;> config_simp
      · rw [hC.bExb, h64, eX]
      · rw [hC.bExb, h65, eY]
  obtain ⟨q103, q104, q100, q101, qr, qm⟩ := q
  have hw₁ := e₁.wb_right
  have T44 : c₁.nreg 90044 = d.b0 + d.oTmp := by
    rw [qr _ (by decide) (by decide) (by decide) (by decide) (by decide), hC.bTmp]
  have T19 : c₁.nreg 90019 = 1 := by
    rw [qr _ (by decide) (by decide) (by decide) (by decide) (by decide), hC.one]
  have T62 : c₁.nreg 90062 = cc := by
    rw [qr _ (by decide) (by decide) (by decide) (by decide) (by decide), h62]
  -- the exits of `X`
  obtain ⟨c₂, k₂, e₂, hk₂, l₂, t₂, f₂, F₂⟩ := appLoop_exec (P := P) (rs := 90103) (rn := 90066)
    (S := d.b0 + d.oEx + d.D * X) (T := d.b0 + d.oTmp) (D' := d.D + 1) (cc := cc) (ℓ₀ := 0)
    (l := st.exl X) (P₀ := []) c₁ (by decide) (by decide) hw₁ q101 q100 rfl (fun i hi => by omega)
    q103 (by rw [exl_length, qr _ (by decide) (by decide) (by decide) (by decide) (by decide),
      h66]) T62 T44 T19
    (fun t ht => by
      rw [exl_length] at ht
      rw [qm, henc.ex X t hX (by omega), exl_getD _ ht])
    (fun t ht => by rw [exl_length] at ht; left; omega)
    (by rw [exl_length]; omega) (by omega) (by rw [exl_length]; omega)
  have hw₂ := e₂.wb_right
  have g₂ : ∀ r, Bapp r = false → c₂.nreg r = c₁.nreg r := F₂.1
  -- reset the counter
  have e₃ := Exec.constN (P := P) hw₂ 90101 0 (by omega)
  have hw₃ := e₃.wb_right
  -- the exits of `Y`
  obtain ⟨c₄, k₄, e₄, hk₄, l₄, t₄, f₄, F₄⟩ := appLoop_exec (P := P) (rs := 90104) (rn := 90067)
    (S := d.b0 + d.oEx + d.D * Y) (T := d.b0 + d.oTmp) (D' := d.D + 1) (cc := cc)
    (ℓ₀ := ((st.exl X).filter (· != cc)).length) (l := st.exl Y)
    (P₀ := (st.exl X).filter (· != cc)) _ (by decide) (by decide) hw₃ (by simp [upd])
    (by config_simp; rw [l₂]; simp) rfl
    (fun i hi => by
      config_simp
      rw [t₂ i (by rw [l₂]; simpa using hi)]; simp)
    (by config_simp; rw [g₂ _ (by decide), q104])
    (by config_simp; rw [g₂ _ (by decide), exl_length,
      qr _ (by decide) (by decide) (by decide) (by decide) (by decide), h67])
    (by config_simp; rw [g₂ _ (by decide), T62])
    (by config_simp; rw [g₂ _ (by decide), T44])
    (by config_simp; rw [g₂ _ (by decide), T19])
    (fun t ht => by
      rw [exl_length] at ht
      config_simp
      rw [f₂ _ (by left; have := slot_lt (R := d.R) hY (show t < d.D by omega); omega),
        qm, henc.ex Y t hY (by omega), exl_getD _ ht])
    (fun t ht => by
      rw [exl_length] at ht; left; have := slot_lt (R := d.R) hY (show t < d.D by omega)
      omega)
    (by rw [exl_length]; omega) (by omega)
    (by rw [exl_length]; omega)
  refine ⟨c₄, _, .seq e₁ (.seq e₂ (.seq e₃ e₄)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := exl_length st X; have := exl_length st Y; rw [← hD.D]; omega
  · rw [l₄, List.length_append]
  · rw [F₄.1 _ (by decide)]; config_simp; rw [g₂ _ (by decide), q103]
  · rw [F₄.1 _ (by decide)]; config_simp; rw [g₂ _ (by decide), q104]
  · intro i hi; rw [t₄ i hi]
  · intro a ha
    rw [f₄ a (by rcases ha with h | h <;> [left; right] <;> omega)]
    config_simp
    rw [f₂ a (by rcases ha with h | h <;> [left; right] <;> omega), qm]

/-! ## Relabelling the exits of `Y` -/

/-- The state with the exits in `l` of the class `Y = s1 c` relabelled to `X = s0 c`. -/
def St.rel (st : St) (c : ℕ) (l : List ℕ) : St :=
  { st with
    s0 := fun e => if e ∈ l ∧ e ≠ c ∧ st.s0 e = st.s1 c then st.s0 c else st.s0 e
    s1 := fun e => if e ∈ l ∧ e ≠ c ∧ st.s1 e = st.s1 c then st.s0 c else st.s1 e }

/-- Store `r v` at `r p` iff `r a = r b`. -/
def condStore (a b p v : ℕ) : Stmt := .ifLtN a b .skip (.ifLtN b a .skip (.instr (.storeN p v)))

theorem condStore_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c)
    (a b p v : ℕ) :
    ∃ c' k, Exec P W (condStore a b p v) c c' k ∧ k ≤ 5 ∧ c'.nreg = c.nreg ∧
      c'.nmem = (if c.nreg a = c.nreg b then upd c.nmem (c.nreg p) (c.nreg v) else c.nmem) := by
  unfold condStore
  by_cases h1 : c.nreg a < c.nreg b
  · exact ⟨c, _, .ifLtN_true h1 (.skip hw), by omega, rfl,
      (ite_eq_right (show ¬ c.nreg a = c.nreg b by omega)).symm⟩
  by_cases h2 : c.nreg b < c.nreg a
  · exact ⟨c, _, .ifLtN_false h1 (.ifLtN_true h2 (.skip hw)), by omega, rfl,
      (ite_eq_right (show ¬ c.nreg a = c.nreg b by omega)).symm⟩
  · exact ⟨_, _, .ifLtN_false h1 (.ifLtN_false h2 (Exec.storeN hw p v)), by omega, rfl,
      (ite_eq_left (show c.nreg a = c.nreg b by omega)).symm⟩

theorem Enc.cond_s0 {m : ℕ → ℕ} {d : Dm} {S : St} (h : Enc m d S) {e : ℕ} (he : e < d.K)
    (X Y : ℕ) : Enc (if S.s0 e = Y then upd m (d.b0 + d.oS0 + e) X else m) d
      { S with s0 := Function.update S.s0 e (if S.s0 e = Y then X else S.s0 e) } := by
  split_ifs
  · exact h.set_s0 he X
  · rw [Function.update_eq_self]; exact h

theorem Enc.cond_s1 {m : ℕ → ℕ} {d : Dm} {S : St} (h : Enc m d S) {e : ℕ} (he : e < d.K)
    (X Y : ℕ) : Enc (if S.s1 e = Y then upd m (d.b0 + d.oS1 + e) X else m) d
      { S with s1 := Function.update S.s1 e (if S.s1 e = Y then X else S.s1 e) } := by
  split_ifs
  · exact h.set_s1 he X
  · rw [Function.update_eq_self]; exact h

/-- Relabel the chord `e` from class `Y` to `X` on either side. -/
def St.relab (S : St) (e X Y : ℕ) : St :=
  { S with
    s0 := Function.update S.s0 e (if S.s0 e = Y then X else S.s0 e)
    s1 := Function.update S.s1 e (if S.s1 e = Y then X else S.s1 e) }

/-- Relabel the chord `r102` from `Y = r65` to `X = r64` on either side. -/
def relOne : Stmt :=
  .seq (block [.addN 90105 90031 90102, .loadN 90106 90105])
    (.seq (condStore 90106 90065 90105 90064)
      (.seq (block [.addN 90105 90032 90102, .loadN 90106 90105])
        (condStore 90106 90065 90105 90064)))

theorem relOne_exec {P : Polygon} {W : ℕ} {E : Env} {d : Dm} {S : St} {c : Config}
    (hw : WordsBounded W c) (hC : Cst c E d) (henc : Enc c.nmem d S) (hD : DimOK E d W)
    {e X Y : ℕ} (he : e < d.K) (h102 : c.nreg 90102 = e) (h64 : c.nreg 90064 = X)
    (h65 : c.nreg 90065 = Y) :
    ∃ c' k, Exec P W relOne c c' k ∧ k ≤ 14 ∧
      Enc c'.nmem d (S.relab e X Y) ∧
      (∀ r, r ≠ 90105 → r ≠ 90106 → c'.nreg r = c.nreg r) ∧
      (∀ a, (a < d.b0 + d.oS0 ∨ d.b0 + d.oNd0 ≤ a) → c'.nmem a = c.nmem a) := by
  have hb := hD.base
  obtain ⟨y1, y2, y3, y4, y5, y6, -⟩ := d.lay
  have hN0 : d.oNd0 = 3 * d.K := rfl
  have hK : 3 * d.K ≤ d.oTmp := by
    have : d.oNd0 ≤ d.oTmp := by dm_simp; omega
    omega
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.addN 90105 90031 90102,
      .loadN 90106 90105]) c c₁ k₁ ∧ k₁ = 2 ∧ (c₁.nreg 90105 = d.b0 + d.oS0 + e ∧
      c₁.nreg 90106 = S.s0 e ∧ (∀ r, r ≠ 90105 → r ≠ 90106 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem) := by
    exec_block
    · rw [hC.bS0, h102]; omega
    · refine ⟨rfl, ?_, ?_, fun r a1 a2 => by simp [upd, a1, a2], rfl⟩ <;> config_simp
      · rw [hC.bS0, h102]
      · rw [hC.bS0, h102, henc.s0 e he]
  obtain ⟨q105, q106, qr, qm⟩ := q
  obtain ⟨c₂, k₂, e₂, hk₂, r₂, m₂⟩ := condStore_exec (P := P) c₁ e₁.wb_right 90106 90065 90105 90064
  have hw₂ := e₂.wb_right
  rw [q106, qr _ (by decide) (by decide), h65, q105, qr _ (by decide) (by decide), h64, qm] at m₂
  have E₂ : Enc c₂.nmem d
      { S with s0 := Function.update S.s0 e (if S.s0 e = Y then X else S.s0 e) } := by
    rw [m₂]; exact henc.cond_s0 he X Y
  obtain ⟨c₃, k₃, e₃, hk₃, q⟩ : ∃ c₃ k₃, Exec P W (block [.addN 90105 90032 90102,
      .loadN 90106 90105]) c₂ c₃ k₃ ∧ k₃ = 2 ∧ (c₃.nreg 90105 = d.b0 + d.oS1 + e ∧
      c₃.nreg 90106 = S.s1 e ∧ (∀ r, r ≠ 90105 → r ≠ 90106 → c₃.nreg r = c.nreg r) ∧
      c₃.nmem = c₂.nmem) := by
    have c32 : c₂.nreg 90032 = d.b0 + d.oS1 := by
      rw [r₂, qr _ (by decide) (by decide), hC.bS1]
    have c102 : c₂.nreg 90102 = e := by rw [r₂, qr _ (by decide) (by decide), h102]
    exec_block
    · rw [c32, c102]; omega
    · refine ⟨rfl, ?_, ?_, fun r a1 a2 => by simp [upd, a1, a2, r₂, qr r a1 a2], rfl⟩ <;>
        config_simp
      · rw [c32, c102]
      · rw [c32, c102, E₂.s1 e he]
  obtain ⟨q105', q106', qr', qm'⟩ := q
  obtain ⟨c₄, k₄, e₄, hk₄, r₄, m₄⟩ := condStore_exec (P := P) c₃ e₃.wb_right 90106 90065 90105 90064
  rw [q106', qr' _ (by decide) (by decide), h65, q105', qr' _ (by decide) (by decide), h64,
    qm'] at m₄
  refine ⟨c₄, _, .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega, ?_, ?_, ?_⟩
  · rw [m₄]; exact E₂.cond_s1 he X Y
  · intro r a1 a2; rw [r₄, qr' r a1 a2]
  · intro a ha
    rw [m₄, m₂]
    split_ifs <;> simp only [upd] <;> split_ifs <;> first | rfl | omega

/-- One step of the relabelling loop: the exit `t` of `Y` (at `r104 + t`), skipped if it is
`c = r62`. -/
def relBody : Stmt :=
  .seq (block [.addN 90105 90104 90101, .loadN 90102 90105])
    (.seq (.ifLtN 90102 90062 relOne (.ifLtN 90062 90102 relOne .skip))
      (.instr (.addN 90101 90101 90019)))

/-- The relabelling loop. -/
def relStmt : Stmt := .seq (.instr (.constN 90101 0)) (.whileLtN 90101 90067 relBody)

theorem wrS_rel : wrS Brm relStmt = true := by decide

/-- The facts the relabelling loop keeps. -/
structure RelI (W : ℕ) (d : Dm) (st : St) (cc : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  t_le : c.nreg 90101 ≤ st.deg (st.s1 cc)
  enc : Enc c.nmem d (st.rel cc ((st.exl (st.s1 cc)).take (c.nreg 90101)))
  regs : ∀ r, r ≠ 90101 → r ≠ 90102 → r ≠ 90105 → r ≠ 90106 → c.nreg r = c₀.nreg r
  mem : ∀ a, (a < d.b0 + d.oS0 ∨ d.b0 + d.oNd0 ≤ a) → c.nmem a = c₀.nmem a

theorem relStmt_exec {P : Polygon} {W : ℕ} {E : Env} {d : Dm} {st : St} {c : Config}
    (hw : WordsBounded W c) (hC : Cst c E d) (henc : Enc c.nmem d st) (hD : DimOK E d W)
    {cc : ℕ} (hY : st.s1 cc < E.R) (hdY : st.deg (st.s1 cc) ≤ E.D)
    (hnd : (st.exl (st.s1 cc)).Nodup) (hK : ∀ i ∈ st.exl (st.s1 cc), i < E.K)
    (h62 : c.nreg 90062 = cc) (h64 : c.nreg 90064 = st.s0 cc) (h65 : c.nreg 90065 = st.s1 cc)
    (h67 : c.nreg 90067 = st.deg (st.s1 cc))
    (h104 : c.nreg 90104 = d.b0 + d.oEx + d.D * st.s1 cc) :
    ∃ c' k, Exec P W relStmt c c' k ∧ k ≤ 22 * E.D + 3 ∧
      Enc c'.nmem d (st.rel cc (st.exl (st.s1 cc))) ∧
      (∀ r, r ≠ 90101 → r ≠ 90102 → r ≠ 90105 → r ≠ 90106 → c'.nreg r = c.nreg r) ∧
      (∀ a, (a < d.b0 + d.oS0 ∨ d.b0 + d.oNd0 ≤ a) → c'.nmem a = c.nmem a) ∧
      FrameS Brm c c' := by
  suffices hh : ∃ c' k, Exec P W relStmt c c' k ∧ k ≤ 22 * E.D + 3 ∧
      Enc c'.nmem d (st.rel cc (st.exl (st.s1 cc))) ∧
      (∀ r, r ≠ 90101 → r ≠ 90102 → r ≠ 90105 → r ≠ 90106 → c'.nreg r = c.nreg r) ∧
      (∀ a, (a < d.b0 + d.oS0 ∨ d.b0 + d.oNd0 ≤ a) → c'.nmem a = c.nmem a) by
    obtain ⟨c', k, e, h1, h2, h3, h4⟩ := hh
    exact ⟨c', k, e, h1, h2, h3, h4, exec_frameS e wrS_rel⟩
  have hb := hD.base
  have hW3 := hD.W1
  obtain ⟨y1, y2, y3, -⟩ := d.lay
  rw [← hD.R] at hY
  rw [← hD.D] at hdY
  have hKd : ∀ i ∈ st.exl (st.s1 cc), i < d.K := fun i hi => by rw [hD.K]; exact hK i hi
  have e₀ := Exec.constN (P := P) hw 90101 0 (by omega)
  have I0 : RelI W d st cc c { c with nreg := upd c.nreg 90101 0 } := by
    refine ⟨e₀.wb_right, by simp [upd], ?_, fun r hr _ _ _ => by simp [upd, hr],
      fun _ _ => rfl⟩
    simp only [upd, ite_true, List.take_zero]
    refine henc.st_congr (fun _ _ => rfl) (fun i _ => ?_) (fun i _ => ?_) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) <;>
      simp [St.rel]
  obtain ⟨c', k, e, I', hx, hk⟩ := Exec.whileLtN_bounded (P := P) (a := 90101) (b := 90067)
    (body := relBody) (RelI W d st cc c) (fun d' => st.deg (st.s1 cc) - d'.nreg 90101) 20
    (fun _ h => h.wb)
    (fun c₁ I ht => by
      obtain ⟨hw₁, ht₁, henc₁, hr₁, hm₁⟩ := I
      rw [hr₁ 90067 (by decide) (by decide) (by decide) (by decide), h67] at ht
      set t := c₁.nreg 90101 with htdef
      set l := st.exl (st.s1 cc) with hldef
      have htl : t < l.length := by rw [exl_length]; exact ht
      set e₀ := l.getD t 0 with he₀
      have he₀K : e₀ < d.K := hKd _ (by
        rw [he₀, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htl, Option.getD_some]
        exact List.getElem_mem htl)
      have hnot : e₀ ∉ l.take t := getD_not_mem_take hnd htl
      -- load the exit
      obtain ⟨c₂, k₂, ex₂, hk₂, q⟩ : ∃ c₂ k₂, Exec P W (block [.addN 90105 90104 90101,
          .loadN 90102 90105]) c₁ c₂ k₂ ∧ k₂ = 2 ∧ (c₂.nreg 90102 = e₀ ∧
          (∀ r, r ≠ 90105 → r ≠ 90102 → c₂.nreg r = c₁.nreg r) ∧ c₂.nmem = c₁.nmem) := by
        have s := slot_le (R := d.R) (D := d.D) hY (show t ≤ d.D by omega)
        exec_block
        · rw [hr₁ _ (by decide) (by decide) (by decide) (by decide), h104]; omega
        · refine ⟨rfl, ?_, fun r a1 a2 => by simp [upd, a1, a2], rfl⟩
          config_simp
          rw [hr₁ _ (by decide) (by decide) (by decide) (by decide), h104,
            henc₁.ex _ _ hY (by omega), he₀, exl_getD _ ht]
          rfl
      obtain ⟨q102, qr, qm⟩ := q
      have hw₂ := ex₂.wb_right
      have c62 : c₂.nreg 90062 = cc := by
        rw [qr _ (by decide) (by decide), hr₁ _ (by decide) (by decide) (by decide) (by decide),
          h62]
      -- the relabelling (or not)
      obtain ⟨c₃, k₃, ex₃, hk₃, enc₃, r₃, m₃⟩ : ∃ c₃ k₃, Exec P W (.ifLtN 90102 90062 relOne
          (.ifLtN 90062 90102 relOne .skip)) c₂ c₃ k₃ ∧ k₃ ≤ 17 ∧
          Enc c₃.nmem d (st.rel cc (l.take (t + 1))) ∧
          (∀ r, r ≠ 90105 → r ≠ 90106 → c₃.nreg r = c₂.nreg r) ∧
          (∀ a, (a < d.b0 + d.oS0 ∨ d.b0 + d.oNd0 ≤ a) → c₃.nmem a = c₂.nmem a) := by
        by_cases hec : e₀ = cc
        · have n1 : ¬ c₂.nreg 90102 < c₂.nreg 90062 := by rw [q102, c62, hec]; omega
          have n2 : ¬ c₂.nreg 90062 < c₂.nreg 90102 := by rw [q102, c62, hec]; omega
          refine ⟨c₂, _, .ifLtN_false n1 (.ifLtN_false n2 (.skip hw₂)), by omega, ?_,
            fun _ _ _ => rfl, fun _ _ => rfl⟩
          rw [qm]
          refine henc₁.st_congr (fun _ _ => rfl) (fun i _ => ?_) (fun i _ => ?_) (fun _ _ => rfl)
            (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
            (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
            (fun _ _ => rfl) <;>
          · simp only [St.rel, mem_take_succ htl]
            by_cases hi : i = cc
            · simp [hi]
            · rw [← he₀]; simp only [show i ≠ e₀ from fun h => hi (h.trans hec), or_false]
        · have hC₂ : Cst c₂ E d := hC.frame fun r hr _ => by
            rw [qr r (by omega) (by omega), hr₁ r (by omega) (by omega) (by omega) (by omega)]
          have c64 : c₂.nreg 90064 = st.s0 cc := by
            rw [qr _ (by decide) (by decide), hr₁ _ (by decide) (by decide) (by decide) (by decide),
              h64]
          have c65 : c₂.nreg 90065 = st.s1 cc := by
            rw [qr _ (by decide) (by decide), hr₁ _ (by decide) (by decide) (by decide) (by decide),
              h65]
          obtain ⟨c₃, k₃, ex₃, hk₃, enc₃, r₃, m₃⟩ := relOne_exec (P := P) hw₂ hC₂
            (by rw [qm]; exact henc₁) hD he₀K q102 c64 c65
          have fin : Enc c₃.nmem d (st.rel cc (l.take (t + 1))) := by
            refine enc₃.st_congr (fun _ _ => rfl) (fun i _ => ?_) (fun i _ => ?_)
              (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
              (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
              (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) <;>
            · simp only [St.rel, St.relab, mem_take_succ htl, ← he₀]
              by_cases hi : i = e₀
              · rw [hi]
                simp [Function.update_self, hnot, hec]
              · rw [Function.update_of_ne hi]
                simp [hi]
          by_cases hlt : e₀ < cc
          · exact ⟨c₃, _, .ifLtN_true (by rw [q102, c62]; exact hlt) ex₃, by omega, fin, r₃, m₃⟩
          · exact ⟨c₃, _, .ifLtN_false (by rw [q102, c62]; exact hlt)
              (.ifLtN_true (by rw [q102, c62]; omega) ex₃), by omega, fin, r₃, m₃⟩
      have hw₃ := ex₃.wb_right
      have c101 : c₃.nreg 90101 = t := by rw [r₃ _ (by decide) (by decide), qr _ (by decide) (by decide)]
      have c19 : c₃.nreg 90019 = 1 := by
        rw [r₃ _ (by decide) (by decide), qr _ (by decide) (by decide),
          hr₁ _ (by decide) (by decide) (by decide) (by decide), hC.one]
      have ex₄ := Exec.addN (P := P) hw₃ 90101 90101 90019 (by rw [c101, c19]; omega)
      refine ⟨_, _, .seq ex₂ (.seq ex₃ ex₄), ⟨ex₄.wb_right, ?_, ?_, ?_, ?_⟩, by omega, ?_⟩
      · config_simp; rw [c101, c19]; omega
      · config_simp; rw [c101, c19]; exact enc₃
      · intro r a1 a2 a3 a4
        config_simp
        rw [upd_other _ _ _ a1, r₃ r a3 a4, qr r a3 a2, hr₁ r a1 a2 a3 a4]
      · intro a ha; config_simp; rw [m₃ a ha, qm, hm₁ a ha]
      · config_simp; rw [c101, c19]; omega) I0
  obtain ⟨hw', ht', henc', hr', hm'⟩ := I'
  rw [hr' 90067 (by decide) (by decide) (by decide) (by decide)] at hx
  rw [h67] at hx
  have hfull : c'.nreg 90101 = st.deg (st.s1 cc) := by omega
  rw [hfull, ← exl_length, List.take_length] at henc'
  refine ⟨c', _, .seq e₀ e, ?_, henc', fun r a1 a2 a3 a4 => ?_, fun a ha => ?_⟩
  · simp only [upd, ite_true, Nat.sub_zero] at hk
    rw [← hD.D]
    have : 22 * st.deg (st.s1 cc) ≤ 22 * d.D := Nat.mul_le_mul_left _ hdY
    omega
  · rw [hr' r a1 a2 a3 a4]
  · rw [hm' a ha]

end

end Gran

end Chazelle.Core
