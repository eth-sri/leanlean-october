module

public import Chazelle.Core.NFBuildRegRec

/-!
# WP-C (BuildNF), RAM part 17: filling the lists of the regions

`arcFillLoop`: each arc `j < A` goes to position `FA[key j]` of the list table `LT` (and the
pointer moves on), so that after the loop the arcs of region `r` are
`LT[off r + t] = (lstF key A r)[t]`.  `chFillLoop`: the same for the chords at
`LT[off r + cA r + t] = (lst2F u v K r)[t]` with the pointers `FC = FA + R`.
-/

namespace Chazelle.Core

namespace BuildRam

open Machine Machine.Stmt Programs SignK

@[expose] public section

theorem lstF_length (key : ℕ → ℕ) (n r : ℕ) : (lstF key n r).length = cntF key n r := rfl

theorem cntF_mono (key : ℕ → ℕ) {n n' : ℕ} (h : n ≤ n') (r : ℕ) : cntF key n r ≤ cntF key n' r := by
  induction n' with
  | zero => rw [Nat.le_zero.1 h]
  | succ k ih =>
    rcases Nat.lt_or_ge n (k + 1) with h' | h'
    · rw [cntF_succ]; have := ih (by omega); omega
    · rw [show n = k + 1 by omega]

theorem cnt2F_mono (u v : ℕ → ℕ) {n n' : ℕ} (h : n ≤ n') (r : ℕ) :
    cnt2F u v n r ≤ cnt2F u v n' r := by
  induction n' with
  | zero => rw [Nat.le_zero.1 h]
  | succ k ih =>
    rcases Nat.lt_or_ge n (k + 1) with h' | h'
    · rw [cnt2F_succ]; have := ih (by omega); omega
    · rw [show n = k + 1 by omega]

/-- The arc list fill. -/
def arcFillLoop : Stmt :=
  .whileLtN 43201 43102 (block [
    .addN 43220 43201 43201, .addN 43220 43220 43220, .addN 43220 43220 43201,
    .addN 43220 43220 44002, .loadN 43221 43220,
    .addN 43222 44011 43221, .loadN 43223 43222,
    .addN 43224 44005 43223, .storeN 43224 43201,
    .addN 43223 43223 43011, .storeN 43222 43223,
    .addN 43201 43201 43011])

theorem wr_arcFillLoop : wrM (fun r => decide (r = 43201 ∨ (43220 ≤ r ∧ r < 43225)))
    arcFillLoop = true := by decide

section exec

variable {P : Polygon} {W : ℕ}

/-- **The arc list fill.** -/
theorem arcFillLoop_exec (d : Config) (hw : WordsBounded W d) {m₂ : ℕ → ℕ}
    {A R AT FA LT : ℕ} {key : ℕ → ℕ} {cC : ℕ → ℕ} (hA : d.nreg 43102 = A)
    (hR : d.nreg 43200 = R) (h1 : d.nreg 43011 = 1) (hi : d.nreg 43201 = 0)
    (hAT : d.nreg 44002 = AT) (hFA : d.nreg 44011 = FA) (hLT : d.nreg 44005 = LT)
    (hkey : ∀ j, j < A → m₂ (AT + 5 * j) = key j) (hkR : ∀ j, j < A → key j < R)
    (hFAv : ∀ r, r < R → m₂ (FA + r) = offF (cntF key A) cC r)
    (hATW : AT + 5 * A ≤ W) (hFAW : FA + R ≤ W) (hoff : LT + offF (cntF key A) cC R ≤ W)
    (hdis1 : AT + 5 * A ≤ FA ∨ FA + R ≤ AT)
    (hdis2 : AT + 5 * A ≤ LT ∨ LT + offF (cntF key A) cC R ≤ AT)
    (hdis3 : FA + R ≤ LT ∨ LT + offF (cntF key A) cC R ≤ FA)
    (hm : d.nmem = m₂) :
    ∃ d' k, Exec P W arcFillLoop d d' k ∧ k ≤ 14 * A + 2 ∧ WordsBounded W d' ∧
      FrameM (fun r => decide (r = 43201 ∨ (43220 ≤ r ∧ r < 43225))) d d' ∧
      (∀ r, r < R → d'.nmem (FA + r) = offF (cntF key A) cC r + cntF key A r) ∧
      (∀ r, r < R → ∀ t, t < cntF key A r →
        d'.nmem (LT + offF (cntF key A) cC r + t) = (lstF key A r).getD t 0) ∧
      (∀ a, (a < FA ∨ FA + R ≤ a) →
        (∀ r, r < R → ∀ t, t < cntF key A r → a ≠ LT + offF (cntF key A) cC r + t) →
        d'.nmem a = m₂ a) := by
  obtain ⟨off, hoffdef⟩ : ∃ f : ℕ → ℕ, f = offF (cntF key A) cC := ⟨_, rfl⟩
  rw [← hoffdef] at hFAv hoff hdis2 hdis3 ⊢
  have osucc : ∀ r', off (r' + 1) = off r' + cntF key A r' + cC r' := fun r' => by
    rw [hoffdef]; exact offF_succ _ _ _
  have omono : ∀ {a b : ℕ}, a ≤ b → off a ≤ off b := fun h => by
    rw [hoffdef]; exact offF_mono _ _ h
  have seg : ∀ r', r' < R → ∀ t, t < cntF key A r' → off r' + t < off R := fun r' hr' t ht => by
    have := osucc r'
    have := omono (show r' + 1 ≤ R by omega)
    omega
  have odisj : ∀ {r₁ r₂ : ℕ}, r₁ < r₂ → off r₁ + cntF key A r₁ + cC r₁ ≤ off r₂ := fun h => by
    rw [← osucc]; exact omono h
  obtain ⟨d', k, e, ⟨hw', j, hj', hjA, hf, I1, I2, I3⟩, htest, hk⟩ := Exec.whileLtN_potential
    (P := P) (W := W) (a := 43201) (b := 43102) (body := _)
    (fun e => WordsBounded W e ∧ ∃ j, e.nreg 43201 = j ∧ j ≤ A ∧
      FrameM (fun r => decide (r = 43201 ∨ (43220 ≤ r ∧ r < 43225))) d e ∧
      (∀ r, r < R → e.nmem (FA + r) = off r + cntF key j r) ∧
      (∀ r, r < R → ∀ t, t < cntF key j r →
        e.nmem (LT + off r + t) = (lstF key j r).getD t 0) ∧
      (∀ a, (a < FA ∨ FA + R ≤ a) →
        (∀ r, r < R → ∀ t, t < cntF key j r → a ≠ LT + off r + t) → e.nmem a = m₂ a))
    (fun e => 14 * (A - e.nreg 43201)) (fun e he => he.1)
    (fun e ⟨hwe, j, hje, hjA, hfe, J1, J2, J3⟩ htest => by
      have r2 : e.nreg 43200 = R := by rw [hfe.1 _ (by decide), hR]
      have r4 : e.nreg 43011 = 1 := by rw [hfe.1 _ (by decide), h1]
      have r5 : e.nreg 44002 = AT := by rw [hfe.1 _ (by decide), hAT]
      have r6 : e.nreg 44011 = FA := by rw [hfe.1 _ (by decide), hFA]
      have r7 : e.nreg 44005 = LT := by rw [hfe.1 _ (by decide), hLT]
      have r8 : e.nreg 43102 = A := by rw [hfe.1 _ (by decide), hA]
      rw [hje, r8] at htest
      have hkj := hkR j htest
      set r := key j with hr
      have hcle : cntF key j r < cntF key A r := by
        have := cntF_mono key (show j + 1 ≤ A by omega) r
        rw [cntF_succ, ite_eq_left rfl] at this; omega
      have hpos : off r + cntF key j r < off R := seg r hkj _ hcle
      have mk : e.nmem (AT + 5 * j) = r := by
        rw [J3 _ (by omega) (fun r' hr' t ht => by
          have := seg r' hr' t (lt_of_lt_of_le ht (cntF_mono key (by omega) r')); omega),
          hkey j htest]
      have mp : e.nmem (FA + r) = off r + cntF key j r := J1 r hkj
      have X : ∃ e' k, Exec P W (block [
          .addN 43220 43201 43201, .addN 43220 43220 43220, .addN 43220 43220 43201,
          .addN 43220 43220 44002, .loadN 43221 43220,
          .addN 43222 44011 43221, .loadN 43223 43222,
          .addN 43224 44005 43223, .storeN 43224 43201,
          .addN 43223 43223 43011, .storeN 43222 43223,
          .addN 43201 43201 43011]) e e' k ∧ k = 12 ∧ e'.nreg 43201 = j + 1 ∧
          e'.nmem = upd (upd e.nmem (LT + (off r + cntF key j r)) j) (FA + r)
            (off r + cntF key j r + 1) := by
        exec_block
        all_goals first
          | (config_simp; simp (config := { failIfUnchanged := false }) only [r4, r5, r6, r7,
              hje, show j + j + (j + j) + j + AT = AT + 5 * j by omega, mk, mp]; omega)
          | skip
        refine ⟨rfl, ?_, ?_⟩ <;> config_simp
        · rw [hje, r4]
        · rw [r4, r5, r6, r7, hje, show j + j + (j + j) + j + AT = AT + 5 * j by omega, mk, mp]
      obtain ⟨e', k, x, hk, hj', hm'⟩ := X
      refine ⟨e', k, x, ⟨x.wb_right, j + 1, hj', by omega, hfe.trans (exec_frameM x (by decide)),
        fun r' hr' => ?_, fun r' hr' t ht => ?_, fun a ha hna => ?_⟩, by rw [hj', hje]; omega⟩
      · rw [hm', cntF_succ]
        by_cases h' : r' = r
        · subst h'; rw [upd_same, ite_eq_left rfl]; try omega
        · have := seg r' hr'
          rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), J1 r' hr',
            ite_eq_right (Ne.symm h')]
          try omega
      · have hseg := seg r' hr' t (lt_of_lt_of_le ht (cntF_mono key (by omega) r'))
        rw [hm', upd_other _ _ _ (by omega), lstF_succ]
        by_cases h' : r' = r
        · subst h'
          rw [ite_eq_left rfl]
          rw [cntF_succ, ite_eq_left rfl] at ht
          by_cases ht' : t = cntF key j r
          · subst ht'
            rw [show LT + off r + cntF key j r = LT + (off r + cntF key j r) by omega, upd_same,
              List.getD_append_right _ _ _ _ (by rw [lstF_length]), lstF_length, Nat.sub_self]
            rfl
          · rw [upd_other _ _ _ (by omega), J2 r hr' t (by omega),
              List.getD_append _ _ _ _ (by rw [lstF_length]; omega)]
        · rw [ite_eq_right (Ne.symm h'), List.append_nil]
          rw [cntF_succ, ite_eq_right (Ne.symm h'), Nat.add_zero] at ht
          have hdisj : LT + off r' + t ≠ LT + (off r + cntF key j r) := by
            rcases Nat.lt_or_gt_of_ne h' with hlt | hlt
            · have := odisj hlt
              have := cntF_mono key (show j ≤ A by omega) r'
              omega
            · have := odisj hlt
              omega
          rw [upd_other _ _ _ hdisj, J2 r' hr' t ht]
      · rw [hm', upd_other _ _ _ (by omega)]
        have hne : a ≠ LT + (off r + cntF key j r) := by
          have := hna r hkj (cntF key j r) (by rw [cntF_succ, ite_eq_left rfl]; omega)
          omega
        rw [upd_other _ _ _ hne]
        exact J3 a ha fun r' hr' t ht => hna r' hr' t (by
          have := cntF_mono key (show j ≤ j + 1 by omega) r'; omega))
    ⟨hw, 0, hi, Nat.zero_le _, FrameM.refl _ _, fun r hr => by
      rw [hm, hFAv r hr]; simp [cntF, lstF], fun r _ t ht => by simp [cntF, lstF] at ht,
      fun a _ _ => by rw [hm]⟩
  have hjA' : j = A := by
    rw [hj', hf.1 _ (by decide), hA] at htest; omega
  subst hjA'
  exact ⟨d', k, e, by rw [hi] at hk; omega, hw', hf, I1, I2, I3⟩

end exec

/-! ## The chord lists -/

/-- The state of a list fill: pointers at `FC`, lists at `LT + b r`, counts `c`, lists `ls`. -/
structure FillInv (R FC LT : ℕ) (b c : ℕ → ℕ) (ls : ℕ → List ℕ) (m₃ M : ℕ → ℕ) : Prop where
  ptr : ∀ r, r < R → M (FC + r) = b r + c r
  cells : ∀ r, r < R → ∀ t, t < c r → M (LT + b r + t) = (ls r).getD t 0
  rest : ∀ a, (a < FC ∨ FC + R ≤ a) → (∀ r, r < R → ∀ t, t < c r → a ≠ LT + b r + t) → M a = m₃ a
  len : ∀ r, (ls r).length = c r

/-- **One element appended to the list of region `r₀`.** -/
theorem FillInv.step {R FC LT : ℕ} {b c cap : ℕ → ℕ} {ls : ℕ → List ℕ} {m₃ M : ℕ → ℕ}
    (I : FillInv R FC LT b c ls m₃ M) {r₀ i : ℕ} (hr₀ : r₀ < R) (hc : c r₀ < cap r₀)
    (hdisj : ∀ r r', r < r' → r' < R → b r + cap r ≤ b r')
    (hcap : ∀ r, r < R → c r ≤ cap r)
    (hsep : ∀ r, r < R → ∀ t, t < cap r → LT + b r + t < FC ∨ FC + R ≤ LT + b r + t) :
    FillInv R FC LT b (Function.update c r₀ (c r₀ + 1)) (Function.update ls r₀ (ls r₀ ++ [i]))
      m₃ (upd (upd M (LT + (b r₀ + c r₀)) i) (FC + r₀) (b r₀ + c r₀ + 1)) := by
  have sep₀ := hsep r₀ hr₀ (c r₀) hc
  constructor
  · intro r hr
    by_cases h : r = r₀
    · subst h; rw [upd_same, Function.update_self]; omega
    · rw [upd_other _ _ _ (by omega), Function.update_of_ne h]
      have := hsep r₀ hr₀ (c r₀) hc
      rw [upd_other _ _ _ (by omega), I.ptr r hr]
  · intro r hr t ht
    by_cases h : r = r₀
    · subst h
      rw [Function.update_self] at ht ⊢
      have sep := hsep r hr t (by omega)
      rw [upd_other _ _ _ (by omega)]
      by_cases ht' : t = c r
      · subst ht'
        rw [show LT + b r + c r = LT + (b r + c r) by omega, upd_same,
          List.getD_append_right _ _ _ _ (by rw [I.len]), I.len, Nat.sub_self]
        rfl
      · rw [upd_other _ _ _ (by omega), I.cells r hr t (by omega),
          List.getD_append _ _ _ _ (by rw [I.len]; omega)]
    · rw [Function.update_of_ne h] at ht ⊢
      have sep := hsep r hr t (by have := hcap r hr; omega)
      rw [upd_other _ _ _ (by omega)]
      have hne : LT + b r + t ≠ LT + (b r₀ + c r₀) := by
        rcases Nat.lt_or_gt_of_ne h with hlt | hlt
        · have := hdisj r r₀ hlt hr₀; have := hcap r hr; omega
        · have := hdisj r₀ r hlt hr; omega
      rw [upd_other _ _ _ hne, I.cells r hr t ht]
  · intro a ha hna
    rw [upd_other _ _ _ (by omega)]
    have hne : a ≠ LT + (b r₀ + c r₀) := by
      have := hna r₀ hr₀ (c r₀) (by rw [Function.update_self]; omega)
      omega
    rw [upd_other _ _ _ hne]
    exact I.rest a ha fun r hr t ht => hna r hr t (by
      by_cases h : r = r₀
      · subst h; rw [Function.update_self]; omega
      · rw [Function.update_of_ne h]; exact ht)
  · intro r
    by_cases h : r = r₀
    · subst h; rw [Function.update_self, Function.update_self, List.length_append, I.len]; rfl
    · rw [Function.update_of_ne h, Function.update_of_ne h, I.len]

theorem lst2_update_eq (u v : ℕ → ℕ) (i : ℕ) (h : u i = v i) :
    Function.update (lst2F u v i) (u i) (lst2F u v i (u i) ++ [i]) = lst2F u v (i + 1) := by
  funext r
  by_cases hr : r = u i
  · subst hr; rw [Function.update_self, lst2F_succ, ite_eq_left (Or.inl rfl)]
  · rw [Function.update_of_ne hr, lst2F_succ, ite_eq_right (by rw [← h]; omega), List.append_nil]

theorem lst2_update_ne (u v : ℕ → ℕ) (i : ℕ) (_h : u i ≠ v i) :
    Function.update (Function.update (lst2F u v i) (u i) (lst2F u v i (u i) ++ [i])) (v i)
      (lst2F u v i (v i) ++ [i]) = lst2F u v (i + 1) := by
  funext r
  by_cases hr : r = v i
  · subst hr; rw [Function.update_self, lst2F_succ, ite_eq_left (Or.inr rfl)]
  · rw [Function.update_of_ne hr]
    by_cases hr' : r = u i
    · subst hr'; rw [Function.update_self, lst2F_succ, ite_eq_left (Or.inl rfl)]
    · rw [Function.update_of_ne hr', lst2F_succ, ite_eq_right (by omega), List.append_nil]

/-- Append chord `r43201` to the list of region `r43225`. -/
def fillV : Stmt :=
  block [.addN 43222 44012 43225, .loadN 43223 43222, .addN 43224 44005 43223,
    .storeN 43224 43201, .addN 43223 43223 43011, .storeN 43222 43223]

/-- The chord list fill. -/
def chFillLoop : Stmt :=
  .whileLtN 43201 43002
    (.seq (block [.addN 43220 43201 43201, .addN 43220 43220 43220, .addN 43220 43220 43201,
        .addN 43220 43220 44001, .addN 43220 43220 43013, .loadN 43221 43220,
        .addN 43220 43220 43011, .loadN 43225 43220,
        .addN 43222 44012 43221, .loadN 43223 43222, .addN 43224 44005 43223,
        .storeN 43224 43201, .addN 43223 43223 43011, .storeN 43222 43223])
      (.seq (.ifLtN 43221 43225 fillV (.ifLtN 43225 43221 fillV .skip))
        (.instr (.addN 43201 43201 43011))))

theorem wr_chFillLoop : wrM (fun r => decide (r = 43201 ∨ (43220 ≤ r ∧ r < 43226)))
    chFillLoop = true := by decide

section exec

variable {P : Polygon} {W : ℕ}

theorem fillV_exec (e : Config) (hw : WordsBounded W e) {FC LT v p : ℕ}
    (hFC : e.nreg 44012 = FC) (hLT : e.nreg 44005 = LT) (hv : e.nreg 43225 = v)
    (h1 : e.nreg 43011 = 1) (hp : e.nmem (FC + v) = p) (hW1 : FC + v ≤ W) (hW2 : LT + p ≤ W)
    (hW3 : p + 1 ≤ W) :
    ∃ e' k, Exec P W fillV e e' k ∧ k = 6 ∧
      e'.nmem = upd (upd e.nmem (LT + p) (e.nreg 43201)) (FC + v) (p + 1) ∧
      (∀ r, (r < 43222 ∨ 43224 < r) → e'.nreg r = e.nreg r) := by
  unfold fillV
  exec_block
  · rw [hFC, hv]; exact hW1
  · config_simp; rw [hFC, hv, hLT, hp]; exact hW2
  · config_simp; rw [hFC, hv, hp, h1]; exact hW3
  · refine ⟨rfl, ?_, fun r hr => ?_⟩ <;> config_simp
    · rw [hFC, hv, hLT, hp, h1]
    · simp (disch := omega) only [upd_other]

/-- **The chord list fill.** -/
theorem chFillLoop_exec (d : Config) (hw : WordsBounded W d) {m₃ : ℕ → ℕ}
    {K R CT FC LT : ℕ} {b : ℕ → ℕ} (hK : d.nreg 43002 = K) (h1 : d.nreg 43011 = 1)
    (h3 : d.nreg 43013 = 3) (hi : d.nreg 43201 = 0) (hCT : d.nreg 44001 = CT)
    (hFC : d.nreg 44012 = FC) (hLT : d.nreg 44005 = LT)
    (hu : ∀ i, i < K → m₃ (CT + 5 * i + 3) < R) (hv : ∀ i, i < K → m₃ (CT + 5 * i + 4) < R)
    (hFCv : ∀ r, r < R → m₃ (FC + r) = b r)
    (hdisj : ∀ r r', r < r' → r' < R → b r + cnt2F (fun i => m₃ (CT + 5 * i + 3))
      (fun i => m₃ (CT + 5 * i + 4)) K r ≤ b r')
    (hsep : ∀ r, r < R → ∀ t, t < cnt2F (fun i => m₃ (CT + 5 * i + 3))
      (fun i => m₃ (CT + 5 * i + 4)) K r → LT + b r + t < FC ∨ FC + R ≤ LT + b r + t)
    (hcell : ∀ r, r < R → ∀ t, t < cnt2F (fun i => m₃ (CT + 5 * i + 3))
      (fun i => m₃ (CT + 5 * i + 4)) K r → LT + b r + t + 1 ≤ W)
    (hCTL : ∀ r, r < R → CT + 5 * K ≤ LT + b r) (hCTF : CT + 5 * K ≤ FC) (hFCW : FC + R ≤ W)
    (hm : d.nmem = m₃) :
    ∃ d' k, Exec P W chFillLoop d d' k ∧ k ≤ 30 * K + 2 ∧ WordsBounded W d' ∧
      FrameM (fun r => decide (r = 43201 ∨ (43220 ≤ r ∧ r < 43226))) d d' ∧
      FillInv R FC LT b (cnt2F (fun i => m₃ (CT + 5 * i + 3)) (fun i => m₃ (CT + 5 * i + 4)) K)
        (lst2F (fun i => m₃ (CT + 5 * i + 3)) (fun i => m₃ (CT + 5 * i + 4)) K) m₃ d'.nmem := by
  obtain ⟨u, hudef⟩ : ∃ f : ℕ → ℕ, f = fun i => m₃ (CT + 5 * i + 3) := ⟨_, rfl⟩
  obtain ⟨v, hvdef⟩ : ∃ f : ℕ → ℕ, f = fun i => m₃ (CT + 5 * i + 4) := ⟨_, rfl⟩
  rw [← hudef, ← hvdef] at hdisj hsep hcell ⊢
  have hu' : ∀ i, i < K → u i < R := fun i hi => by rw [hudef]; exact hu i hi
  have hv' : ∀ i, i < K → v i < R := fun i hi => by rw [hvdef]; exact hv i hi
  have hcap : ∀ i, i ≤ K → ∀ r, cnt2F u v i r ≤ cnt2F u v K r := fun i hi r => cnt2F_mono u v hi r
  obtain ⟨d', k, e, ⟨hw', i, hi', hiK, hf, I⟩, htest, hk⟩ := Exec.whileLtN_potential
    (P := P) (W := W) (a := 43201) (b := 43002) (body := _)
    (fun e => WordsBounded W e ∧ ∃ i, e.nreg 43201 = i ∧ i ≤ K ∧
      FrameM (fun r => decide (r = 43201 ∨ (43220 ≤ r ∧ r < 43226))) d e ∧
      FillInv R FC LT b (cnt2F u v i) (lst2F u v i) m₃ e.nmem)
    (fun e => 30 * (K - e.nreg 43201)) (fun e he => he.1)
    (fun e ⟨hwe, i, hie, hiK, hfe, J⟩ htest => by
      have r4 : e.nreg 43011 = 1 := by rw [hfe.1 _ (by decide), h1]
      have r3 : e.nreg 43013 = 3 := by rw [hfe.1 _ (by decide), h3]
      have r5 : e.nreg 44001 = CT := by rw [hfe.1 _ (by decide), hCT]
      have r6 : e.nreg 44012 = FC := by rw [hfe.1 _ (by decide), hFC]
      have r7 : e.nreg 44005 = LT := by rw [hfe.1 _ (by decide), hLT]
      have r8 : e.nreg 43002 = K := by rw [hfe.1 _ (by decide), hK]
      rw [hie, r8] at htest
      have hui := hu' i htest
      have hvi := hv' i htest
      have notcell : ∀ a, a < CT + 5 * K → ∀ r, r < R → ∀ t, t < cnt2F u v i r →
          a ≠ LT + b r + t := fun a ha r hr t _ => by have := hCTL r hr; omega
      have mu : e.nmem (CT + 5 * i + 3) = u i := by
        rw [J.rest _ (by omega) (notcell _ (by omega)), hudef]
      have mv : e.nmem (CT + 5 * i + 4) = v i := by
        rw [J.rest _ (by omega) (notcell _ (by omega)), hvdef]
      have hcu : cnt2F u v i (u i) < cnt2F u v K (u i) := by
        have := hcap (i + 1) (by omega) (u i)
        rw [cnt2F_succ, ite_eq_left (Or.inl rfl)] at this; omega
      have pu := J.ptr (u i) hui
      have cellu := hcell (u i) hui _ hcu
      have hdisj' : ∀ r r', r < r' → r' < R → b r + cnt2F u v K r ≤ b r' := hdisj
      -- the list of `u i`
      obtain ⟨e₁, k₁, x₁, hk₁, v21, v25, v01, m₁, g₁⟩ : ∃ e₁ k₁, Exec P W
          (block [.addN 43220 43201 43201, .addN 43220 43220 43220, .addN 43220 43220 43201,
            .addN 43220 43220 44001, .addN 43220 43220 43013, .loadN 43221 43220,
            .addN 43220 43220 43011, .loadN 43225 43220,
            .addN 43222 44012 43221, .loadN 43223 43222, .addN 43224 44005 43223,
            .storeN 43224 43201, .addN 43223 43223 43011, .storeN 43222 43223]) e e₁ k₁ ∧
          k₁ = 14 ∧ e₁.nreg 43221 = u i ∧ e₁.nreg 43225 = v i ∧ e₁.nreg 43201 = i ∧
          e₁.nmem = upd (upd e.nmem (LT + (b (u i) + cnt2F u v i (u i))) i) (FC + u i)
            (b (u i) + cnt2F u v i (u i) + 1) ∧
          (∀ r, (r < 43220 ∨ 43225 < r) → e₁.nreg r = e.nreg r) := by
        exec_block
        all_goals first
          | (config_simp; simp (config := { failIfUnchanged := false }) only [r3, r4, r5, r6, r7,
              hie, show i + i + (i + i) + i + CT + 3 = CT + 5 * i + 3 by omega,
              show CT + 5 * i + 3 + 1 = CT + 5 * i + 4 by omega, mu, mv, pu]; omega)
          | skip
        refine ⟨rfl, ?_, ?_, ?_, ?_, fun r hr => ?_⟩ <;> config_simp
        · rw [r3, r5, hie, show i + i + (i + i) + i + CT + 3 = CT + 5 * i + 3 by omega, mu]
        · rw [r3, r4, r5, hie, show i + i + (i + i) + i + CT + 3 + 1 = CT + 5 * i + 4 by omega,
            mv]
        · rw [hie]
        · rw [r3, r4, r5, r6, r7, hie, show i + i + (i + i) + i + CT + 3 = CT + 5 * i + 3 by omega,
            mu, pu]
        · simp (disch := omega) only [upd_other]
      have w₁ := x₁.wb_right
      have J₁ := J.step (cap := cnt2F u v K) (i := i) hui hcu hdisj' (fun r _ => hcap i hiK r)
        (fun r hr t ht => hsep r hr t ht)
      rw [← m₁] at J₁
      -- the list of `v i`
      obtain ⟨e₂, k₂, x₂, hk₂, g₂, J₂⟩ : ∃ e₂ k₂, Exec P W
          (.ifLtN 43221 43225 fillV (.ifLtN 43225 43221 fillV .skip)) e₁ e₂ k₂ ∧ k₂ ≤ 9 ∧
          (∀ r, (r < 43222 ∨ 43224 < r) → e₂.nreg r = e₁.nreg r) ∧
          FillInv R FC LT b (cnt2F u v (i + 1)) (lst2F u v (i + 1)) m₃ e₂.nmem := by
        have fv : u i ≠ v i → ∃ e₂ k₂, Exec P W fillV e₁ e₂ k₂ ∧ k₂ = 6 ∧
            (∀ r, (r < 43222 ∨ 43224 < r) → e₂.nreg r = e₁.nreg r) ∧
            FillInv R FC LT b (cnt2F u v (i + 1)) (lst2F u v (i + 1)) m₃ e₂.nmem := fun hne => by
          have hcv : Function.update (cnt2F u v i) (u i) (cnt2F u v i (u i) + 1) (v i) <
              cnt2F u v K (v i) := by
            rw [Function.update_of_ne (Ne.symm hne)]
            have := hcap (i + 1) (by omega) (v i)
            rw [cnt2F_succ, ite_eq_left (Or.inr rfl)] at this; omega
          have pv := J₁.ptr (v i) hvi
          have cellv := hcell (v i) hvi _ hcv
          obtain ⟨e₂, k₂, x₂, hk₂, m₂, g₂⟩ := fillV_exec (P := P) e₁ w₁ (FC := FC) (LT := LT)
            (v := v i) (p := b (v i) + Function.update (cnt2F u v i) (u i)
              (cnt2F u v i (u i) + 1) (v i))
            (by rw [g₁ _ (by omega), r6]) (by rw [g₁ _ (by omega), r7]) v25
            (by rw [g₁ _ (by omega), r4]) pv (by omega) (by omega) (by omega)
          refine ⟨e₂, k₂, x₂, hk₂, g₂, ?_⟩
          have J₂ := J₁.step (cap := cnt2F u v K) (i := i) hvi hcv hdisj'
            (fun r _ => by
              by_cases h : r = u i
              · subst h; rw [Function.update_self]; omega
              · rw [Function.update_of_ne h]; exact hcap i hiK r)
            (fun r hr t ht => hsep r hr t ht)
          have q1 : Function.update (cnt2F u v i) (u i) (cnt2F u v i (u i) + 1) (v i) =
              cnt2F u v i (v i) := Function.update_of_ne (Ne.symm hne) _ _
          have q2 : Function.update (lst2F u v i) (u i) (lst2F u v i (u i) ++ [i]) (v i) =
              lst2F u v i (v i) := Function.update_of_ne (Ne.symm hne) _ _
          rw [m₂, v01, q1]
          rw [q1, q2, cnt2_update_ne u v i hne, lst2_update_ne u v i hne] at J₂
          exact J₂
        by_cases a1 : u i < v i
        · obtain ⟨e₂, k₂, x₂, hk₂, g₂, J₂⟩ := fv (by omega)
          exact ⟨e₂, _, .ifLtN_true (by rw [v21, v25]; exact a1) x₂, by omega, g₂, J₂⟩
        by_cases a2 : v i < u i
        · obtain ⟨e₂, k₂, x₂, hk₂, g₂, J₂⟩ := fv (by omega)
          exact ⟨e₂, _, .ifLtN_false (by rw [v21, v25]; exact a1)
            (.ifLtN_true (by rw [v21, v25]; exact a2) x₂), by omega, g₂, J₂⟩
        · refine ⟨e₁, _, .ifLtN_false (by rw [v21, v25]; exact a1)
            (.ifLtN_false (by rw [v21, v25]; exact a2) (.skip w₁)), by omega, fun _ _ => rfl, ?_⟩
          rw [← cnt2_update_eq u v i (by omega), ← lst2_update_eq u v i (by omega)]
          exact J₁
      have w₂ := x₂.wb_right
      have e1011 : e₂.nreg 43011 = 1 := by rw [g₂ _ (by omega), g₁ _ (by omega), r4]
      have e1201 : e₂.nreg 43201 = i := by rw [g₂ _ (by omega), v01]
      have x₃ := Exec.addN (P := P) w₂ 43201 43201 43011 (by rw [e1011, e1201]; omega)
      have X := Exec.seq x₁ (Exec.seq x₂ x₃)
      refine ⟨_, _, X, ⟨X.wb_right, i + 1, by simp [e1011, e1201], by omega,
        hfe.trans (exec_frameM X (by decide)), by simpa using J₂⟩, ?_⟩
      simp only [upd_same, e1011, e1201]
      omega)
    ⟨hw, 0, hi, Nat.zero_le _, FrameM.refl _ _,
      { ptr := fun r hr => by rw [hm, hFCv r hr]; simp [cnt2F, lst2F]
        cells := fun r _ t ht => by simp [cnt2F, lst2F] at ht
        rest := fun a _ _ => by rw [hm]
        len := fun r => rfl }⟩
  have hiK' : i = K := by
    rw [hi', hf.1 _ (by decide), hK] at htest; omega
  subst hiK'
  exact ⟨d', k, e, by rw [hi] at hk; omega, hw', hf, I⟩

end exec

end

end BuildRam

end Chazelle.Core
