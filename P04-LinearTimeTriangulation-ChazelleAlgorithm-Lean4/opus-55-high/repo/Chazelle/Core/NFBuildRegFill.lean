module

public import Chazelle.MacT
public import Chazelle.Core.ShootCutShK1M
public import Chazelle.Core.DownPhaseDrvBCtx
public import Chazelle.Core.NFBuildArcs
public import Chazelle.Core.NFDecompBfs
public import Chazelle.Core.Lemma41Cover
public import Chazelle.Programs.Tactics
public import Chazelle.Core.ShootCutGrade

namespace Chazelle.Core
namespace BuildRam
open Machine Machine.Stmt Programs SignK
@[expose] public section
theorem lstF_length (key : ℕ → ℕ) (n r : ℕ) : (lstF key n r).length = cntF key n r := rfl
theorem cntF_mono (key : ℕ → ℕ) {n n' : ℕ} (h : n ≤ n') (r : ℕ) : cntF key n r ≤ cntF key n' r := by
  induction n' with
  | zero => zunwb
  | succ k ih =>
    zuido
    · rw [cntF_succ]; omega
    · grind
theorem cnt2F_mono (u v : ℕ → ℕ) {n n' : ℕ} (h : n ≤ n') (r : ℕ) :
    cnt2F u v n r ≤ cnt2F u v n' r := by
  induction n' with
  | zero => zunwb
  | succ k ih =>
    zuido
    · rw [cnt2F_succ]; omega
    · grind

/-- The arc list fill. -/
def arcFillLoop : Stmt :=
  .whileLtN 43201 43102 (block [
    .addN 43220 43201 43201, .addN 43220 43220 43220, .addN 43220 43220 43201,
    .addN 43220 43220 44002, .loadN 43221 43220,
    .addN 43222 44011 43221, .loadN 43223 43222,
    .addN 43224 44005 43223, .storeN 43224 43201,
    .addN 43223 43223 43011, .storeN 43222 43223,
    .addN 43201 43201 43011])
theorem wr_arcFillLoop : wrM ztcnj
    arcFillLoop = true := by_decide
section exec
variable {P : Polygon} {W : ℕ}

/-- **The arc list fill.** -/
theorem arcFillLoop_exec (d : Config) (hw : WordsBounded W d) {m₂ : ℕ → ℕ}
    {A R AT FA LT : ℕ} {key : ℕ → ℕ} {cC : ℕ → ℕ} (hA : d.nreg 43102 = A)
    (hR : d.nreg 43200 = R) (h1 : d.nreg 43011 = 1) (hi : d.nreg 43201 = 0)
    (hAT : d.nreg 44002 = AT) (hFA : d.nreg 44011 = FA) (hLT : d.nreg 44005 = LT)
    (hkey : ∀ j, j < A → m₂ ztdkr = key j) (hkR : ∀ j, j < A → key j < R)
    (hFAv : ∀ r, r < R → m₂ ztjit = offF ztdud cC r)
    (hATW : AT + 5 * A ≤ W) (hFAW : FA + R ≤ W) (hoff : LT + offF ztdud cC R ≤ W)
    (hdis1 : AT + 5 * A ≤ FA ∨ FA + R ≤ AT)
    (hdis2 : AT + 5 * A ≤ LT ∨ LT + offF ztdud cC R ≤ AT)
    (hdis3 : FA + R ≤ LT ∨ LT + offF ztdud cC R ≤ FA)
    (hm : d.nmem = m₂) :
    ∃ d' k, Exec P W arcFillLoop d d' k ∧ k ≤ 14 * A + 2 ∧ WordsBounded W d' ∧
      FrameM ztcnj d d' ∧
      (∀ r, r < R → d'.nmem ztjit = offF ztdud cC r + cntF key A r) ∧
      (∀ r, r < R → ∀ t, t < cntF key A r →
        d'.nmem (LT + offF ztdud cC r + t) = (lstF key A r).getD t 0) ∧
      (∀ a, ztlfs →
        (∀ r, r < R → ∀ t, t < cntF key A r → a ≠ LT + offF ztdud cC r + t) →
        d'.nmem a = m₂ a) := by
  obtain ⟨off, hoffdef⟩ : ∃ f : ℕ → ℕ, f = offF (cntF key A) cC := by_simp_all
  rw [← hoffdef] at hFAv hoff hdis2 hdis3 ⊢
  have osucc : ∀ r', off _ = off r' + cntF key A r' + cC r' := fun r' => by
    zuozb; exact offF_succ _ _ _
  have omono : ∀ {a b : ℕ}, a ≤ b → off a ≤ off b := fun h => by
    zuozb; exact offF_mono _ _ h
  have seg : ∀ r', r' < R → ∀ t, t < cntF key A r' → off r' + t < off R := fun r' hr' t ht => by
    grind
  have odisj : ∀ {r₁ r₂ : ℕ}, r₁ < r₂ → off r₁ + cntF key A r₁ + cC r₁ ≤ off r₂ := fun h => by
    grind
  obtain ⟨d', k, e, ⟨hw', j, hj', hjA, hf, I1, I2, I3⟩, htest, hk⟩ := Exec.whileLtN_potential
    (P := P) (W := W) (a := 43201) (b := 43102) (body := _)
    (fun e => WordsBounded W e ∧ ∃ j, e.nreg 43201 = j ∧ j ≤ A ∧
      FrameM ztcnj d e ∧
      (∀ r, r < R → e.nmem ztjit = off r + cntF key j r) ∧
      (∀ r, r < R → ∀ t, t < cntF key j r →
        e.nmem (LT + off r + t) = (lstF key j r).getD t 0) ∧
      (∀ a, ztlfs →
        (∀ r, r < R → ∀ t, t < cntF key j r → a ≠ LT + off r + t) → e.nmem a = m₂ a))
    (fun e => 14 * ztldu) ztchu
    (fun e ⟨hwe, j, hje, hjA, hfe, J1, J2, J3⟩ htest => by
      zuboh

      zuehx
      zuehy
      zuehz
      have r8 : ztpon := by zunhw
      rw [hje, r8] at htest
      have hkj := hkR j htest
      set r := key j with hr
      have hcle : cntF key j r < cntF key A r := by
        have := cntF_mono key (show j + 1 ≤ A by omega) r
        rw [cntF_succ, ite_eq_left rfl] at this; omega
      have hpos := seg r hkj _ hcle
      have mk : e.nmem ztdkr = r := by
        rw [J3 _ by_omega (fun r' hr' t ht => by
          have := seg r' hr' t ztmmg; omega),
          hkey j htest]
      have mp := J1 r hkj
      have X : ∃ e' k, Exec P W (block [
          .addN 43220 43201 43201, .addN 43220 43220 43220, .addN 43220 43220 43201,
          .addN 43220 43220 44002, .loadN 43221 43220,
          .addN 43222 44011 43221, .loadN 43223 43222,
          .addN 43224 44005 43223, .storeN 43224 43201,
          .addN 43223 43223 43011, .storeN 43222 43223,
          .addN 43201 43201 43011]) e e' k ∧ k = 12 ∧ e'.nreg 43201 = j + 1 ∧
          e'.nmem = upd (upd e.nmem (LT + zteui) j) ztjit
            (off r + cntF key j r + 1) := by
        exec_block
        all_goals first
          | (config_simp; simp (config := { failIfUnchanged := false }) only [r4, r5, r6, r7,
              hje, show j + j + ztcvv + j + AT = AT + 5 * j by omega, mk, mp]; omega)
          | skip
        refine ztkw <;> config_simp
        · omega
        · rw [r4, r5, r6, r7, hje, show j + j + ztcvv + j + AT = AT + 5 * j by omega, mk, mp]
      zudrb
      refine ⟨e', k, x, ⟨x.wb_right, j + 1, hj', by_omega, hfe.trans ztjux,
        fun r' hr' => ?_, fun r' hr' t ht => ?_, fun a ha hna => ?_⟩, by_omega⟩
      · rw [hm', cntF_succ]
        zujsf
        · subst h'; rw [upd_same, ite_eq_left rfl]; rfl
        · have := seg r' hr'
          rw [upd_other _ _ _ by_omega, upd_other _ _ _ by_omega, J1 r' hr',
            ite_eq_right ztqau]
          simp
      · have hseg := seg r' hr' t ztmmg
        rw [hm', upd_other _ _ _ by_omega, lstF_succ]
        zujsf
        · zumqa
          zubyt
          rw [cntF_succ, ite_eq_left rfl] at ht
          by_cases ht' : t = cntF key j r
          · subst ht'
            rw [show LT + off r + cntF key j r = LT + zteui by omega, upd_same,
              List.getD_append_right _ _ _ _ by_rfl, lstF_length, Nat.sub_self]
            rfl
          · rw [upd_other _ _ _ by_omega, J2 r hr' t by_omega,
              List.getD_append _ _ _ _ (by rw [lstF_length]; omega)]
        · rw [ite_eq_right ztqau, List.append_nil]
          rw [cntF_succ, ite_eq_right ztqau, Nat.add_zero] at ht
          have hdisj : LT + off r' + t ≠ LT + zteui := by
            rcases Nat.lt_or_gt_of_ne h' with hlt | hlt
            · have := odisj hlt
              have := cntF_mono key (show j ≤ A by omega) r'
              omega
            grind
          rw [upd_other _ _ _ hdisj, J2 r' hr' t ht]
      · rw [hm', upd_other _ _ _ by_omega]
        have hne : a ≠ LT + zteui := by
          have := hna r hkj (cntF key j r) (by rw [cntF_succ, ite_eq_left rfl]; omega)
          omega
        zuimw
        exact J3 a ha fun r' hr' t ht => hna r' hr' t (by
          have := cntF_mono key (show j ≤ j + 1 by omega) r'; omega))
    ⟨hw, 0, hi, Nat.zero_le _, FrameM.refl _ _, fun r hr => by
      rw [hm, hFAv r hr]; rfl, fun r _ t ht => by_tauto,
      fun a _ _ => by zvmwi⟩
  have hjA' : ztsjq := by
    zuely
  subst hjA'
  exact ⟨d', k, e, by_omega, hw', hf, I1, I2, I3⟩
end exec

/-! ## The chord lists -/

/-- The state of a list fill: pointers at `FC`, lists at `LT + b r`, counts `c`, lists `ls`. -/
structure FillInv (R FC LT : ℕ) (b c : ℕ → ℕ) (ls : ℕ → List ℕ) (m₃ M : ℕ → ℕ) : Prop where
  ptr : ∀ r, r < R → M ztsxj = b r + c r
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
      m₃ (upd (upd M (LT + ztjoe) i) (FC + r₀) (b r₀ + c r₀ + 1)) := by
  have sep₀ := hsep r₀ hr₀ _ hc
  constructor
  · zuz
    zufqr
    · subst h; rw [upd_same, Function.update_self]; omega
    · rw [upd_other _ _ _ by_omega, Function.update_of_ne h]
      have := by_omega
      rw [upd_other _ _ _ by_omega, I.ptr r hr]
  · zulnj
    zufqr
    · zubst
      rw [Function.update_self] at ht ⊢
      have sep := hsep r hr t by_omega
      zutv
      by_cases ht' : t = c r
      · subst ht'
        rw [show LT + b r + c r = LT + (b r + c r) by omega, upd_same,
          List.getD_append_right _ _ _ _ (by zuozc), I.len, Nat.sub_self]
        rfl
      · rw [upd_other _ _ _ by_omega, I.cells r hr t by_omega,
          List.getD_append _ _ _ _ (by zuozc; omega)]
    · rw [Function.update_of_ne h] at ht ⊢
      have sep := hsep r hr t by_grind
      zutv
      have hne : LT + b r + t ≠ LT + ztjoe := by
        rcases Nat.lt_or_gt_of_ne h with hlt | hlt
        · grind
        grind
      rw [upd_other _ _ _ hne, I.cells r hr t ht]
  · intro a ha hna
    zutv
    have hne : a ≠ LT + ztjoe := by
      have := hna r₀ hr₀ (c r₀) by_simp
      omega
    zuimw
    exact I.rest a ha fun r hr t ht => hna r hr t (by
      grind)
  · intro r
    zufqr
    · subst h; rw [Function.update_self, Function.update_self, List.length_append, I.len]; rfl
    · rw [Function.update_of_ne h, Function.update_of_ne h, I.len]
theorem lst2_update_eq (u v : ℕ → ℕ) (i : ℕ) (h : u i = v i) :
    Function.update zthys ztbic ztxbn = lst2F u v ztg := by
  funext r
  zuirt
  · subst hr; zunwc
  · rw [Function.update_of_ne hr, lst2F_succ, ite_eq_right by_omega, List.append_nil]
theorem lst2_update_ne (u v : ℕ → ℕ) (i : ℕ) (_h : u i ≠ v i) :
    Function.update (Function.update zthys ztbic ztxbn) ztewd
      (lst2F u v i ztewd ++ [i]) = lst2F u v ztg := by
  funext r
  zuiru
  · subst hr; rw [Function.update_self, lst2F_succ, ite_eq_left ztbt]
  · zufmm

    · subst hr'; zunwc
    · rw [Function.update_of_ne hr', lst2F_succ, ite_eq_right by_omega, List.append_nil]

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
      (.seq ztjdb
        ztgwu))
theorem wr_chFillLoop : wrM ztcnk
    chFillLoop = true := by_decide
section exec
variable {P : Polygon} {W : ℕ}
theorem fillV_exec (e : Config) (hw : WordsBounded W e) {FC LT v p : ℕ}
    (hFC : e.nreg 44012 = FC) (hLT : e.nreg 44005 = LT) (hv : e.nreg 43225 = v)
    (h1 : e.nreg 43011 = 1) (hp : e.nmem ztsxk = p) (hW1 : FC + v ≤ W) (hW2 : LT + p ≤ W)
    (hW3 : p + 1 ≤ W) :
    ∃ e' k, Exec P W fillV e e' k ∧ k = 6 ∧
      e'.nmem = upd (upd e.nmem (LT + p) (e.nreg 43201)) ztsxk ztr ∧
      (∀ r, (r < 43222 ∨ 43224 < r) → e'.nreg r = e.nreg r) := by
  unfold fillV
  exec_block
  · omega
  · simp_all
  · simp_all
  · refine ztui <;> config_simp
    · simp_all
    · zuro

/-- **The chord list fill.** -/
theorem chFillLoop_exec (d : Config) (hw : WordsBounded W d) {m₃ : ℕ → ℕ}
    {K R CT FC LT : ℕ} {b : ℕ → ℕ} (hK : d.nreg 43002 = K) (h1 : d.nreg 43011 = 1)
    (h3 : d.nreg 43013 = 3) (hi : d.nreg 43201 = 0) (hCT : d.nreg 44001 = CT)
    (hFC : d.nreg 44012 = FC) (hLT : d.nreg 44005 = LT)
    (hu : ∀ i, i < K → m₃ ztbjh < R) (hv : ∀ i, i < K → m₃ ztbji < R)
    (hFCv : ∀ r, r < R → m₃ ztsxj = b r)
    (hdisj : ∀ r r', r < r' → r' < R → b r + cnt2F ztwzw
      ztwzx K r ≤ b r')
    (hsep : ∀ r, r < R → ∀ t, t < cnt2F ztwzw
      ztwzx K r → LT + b r + t < FC ∨ FC + R ≤ LT + b r + t)
    (hcell : ∀ r, r < R → ∀ t, t < cnt2F ztwzw
      ztwzx K r → LT + b r + t + 1 ≤ W)
    (hCTL : ∀ r, r < R → CT + 5 * K ≤ LT + b r) (hCTF : CT + 5 * K ≤ FC) (hFCW : FC + R ≤ W)
    (hm : d.nmem = m₃) :
    ∃ d' k, Exec P W chFillLoop d d' k ∧ k ≤ 30 * K + 2 ∧ WordsBounded W d' ∧
      FrameM ztcnk d d' ∧
      FillInv R FC LT b (cnt2F ztwzw ztwzx K)
        (lst2F ztwzw ztwzx K) m₃ d'.nmem := by
  obtain ⟨u, hudef⟩ : ∃ f : ℕ → ℕ, f = fun i => m₃ (CT + 5 * i + 3) := by_simp_all
  obtain ⟨v, hvdef⟩ : ∃ f : ℕ → ℕ, f = fun i => m₃ (CT + 5 * i + 4) := by_simp_all
  rw [← hudef, ← hvdef] at hdisj hsep hcell ⊢
  have hu' : ztlbu := fun i hi => by_grind
  have hv' : ztlbv := fun i hi => by_grind
  have hcap : ∀ i, i ≤ K → ∀ r, cnt2F u v i r ≤ cnt2F u v K r := fun i hi r => cnt2F_mono u v hi r
  obtain ⟨d', k, e, ⟨hw', i, hi', hiK, hf, I⟩, htest, hk⟩ := Exec.whileLtN_potential
    (P := P) (W := W) (a := 43201) (b := 43002) (body := _)
    (fun e => WordsBounded W e ∧ ∃ i, e.nreg 43201 = i ∧ i ≤ K ∧
      FrameM ztcnk d e ∧
      FillInv R FC LT b ztdnc zthys m₃ e.nmem)
    (fun e => 30 * ztrju) ztchu
    (fun e ⟨hwe, i, hie, hiK, hfe, J⟩ htest => by
      have r4 : ztizs := by zunhv
      zuboi

      have r6 : e.nreg 44012 = FC := by rw [hfe.1 _ by_decide, hFC]
      zuehz
      have r8 : ztuub := by zunzh
      rw [hie, r8] at htest
      have hui := hu' i htest
      have hvi := hv' i htest
      have notcell : ∀ a, a < CT + 5 * K → ∀ r, r < R → ∀ t, t < cnt2F u v i r →
          a ≠ LT + b r + t := fun a ha r hr t _ => by_grind
      have mu : e.nmem ztbjh = u i := by
        rw [J.rest _ by_omega by_grind, hudef]
      have mv : e.nmem ztbji = v i := by
        rw [J.rest _ by_omega by_grind, hvdef]
      have hcu : cnt2F u v i ztbic < cnt2F u v K ztbic := by
        have := hcap ztg by_omega ztbic
        rw [cnt2F_succ, ite_eq_left ztp] at this; omega
      have pu := J.ptr ztbic hui
      have cellu := hcell ztbic hui _ hcu
      have hdisj' := hdisj
      -- the list of `u i`
      obtain ⟨e₁, k₁, x₁, hk₁, v21, v25, v01, m₁, g₁⟩ : ∃ e₁ k₁, Exec P W
          (block [.addN 43220 43201 43201, .addN 43220 43220 43220, .addN 43220 43220 43201,
            .addN 43220 43220 44001, .addN 43220 43220 43013, .loadN 43221 43220,
            .addN 43220 43220 43011, .loadN 43225 43220,
            .addN 43222 44012 43221, .loadN 43223 43222, .addN 43224 44005 43223,
            .storeN 43224 43201, .addN 43223 43223 43011, .storeN 43222 43223]) e e₁ k₁ ∧
          k₁ = 14 ∧ e₁.nreg 43221 = u i ∧ e₁.nreg 43225 = v i ∧ e₁.nreg 43201 = i ∧
          e₁.nmem = upd (upd e.nmem (LT + (b ztbic + cnt2F u v i ztbic)) i) (FC + u i)
            (b ztbic + cnt2F u v i ztbic + 1) ∧
          (∀ r, (r < 43220 ∨ 43225 < r) → e₁.nreg r = e.nreg r) := by
        exec_block
        all_goals first
          | (config_simp; simp (config := { failIfUnchanged := false }) only [r3, r4, r5, r6, r7,
              hie, show i + i + ztjyl + i + CT + 3 = CT + 5 * i + 3 by omega,
              show CT + 5 * i + 3 + 1 = CT + 5 * i + 4 by omega, mu, mv, pu]; omega)
          | skip
        refine zthno <;> config_simp
        · rw [r3, r5, hie, show i + i + ztjyl + i + CT + 3 = CT + 5 * i + 3 by omega, mu]
        · rw [r3, r4, r5, hie, show i + i + ztjyl + i + CT + 3 + 1 = CT + 5 * i + 4 by omega,
            mv]
        · zuoyw
        · rw [r3, r4, r5, r6, r7, hie, show i + i + ztjyl + i + CT + 3 = CT + 5 * i + 3 by omega,
            mu, pu]
        · zuro
      zubcr
      have J₁ := J.step (cap := cnt2F u v K) (i := i) hui hcu hdisj' (fun r _ => hcap i hiK r)
        (fun r hr t ht => hsep r hr t ht)
      rw [← m₁] at J₁
      -- the list of `v i`
      obtain ⟨e₂, k₂, x₂, hk₂, g₂, J₂⟩ : ∃ e₂ k₂, Exec P W
          ztjdb e₁ e₂ k₂ ∧ k₂ ≤ 9 ∧
          ztfyv ∧
          FillInv R FC LT b (cnt2F u v ztg) (lst2F u v ztg) m₃ e₂.nmem := by
        have fv : u i ≠ v i → ∃ e₂ k₂, Exec P W fillV e₁ e₂ k₂ ∧ k₂ = 6 ∧
            ztfyv ∧
            FillInv R FC LT b _ _ m₃ e₂.nmem := fun hne => by
          have hcv : Function.update ztdnc ztbic ztwtt ztewd <
              cnt2F u v K ztewd := by
            rw [Function.update_of_ne ztnr]
            have := hcap ztg by_omega ztewd
            rw [cnt2F_succ, ite_eq_left ztbt] at this; omega
          have pv := J₁.ptr _ hvi
          have cellv := hcell _ hvi _ hcv
          obtain ⟨e₂, k₂, x₂, hk₂, m₂, g₂⟩ := fillV_exec (P := P) e₁ w₁ (FC := FC) (LT := LT)
            (v := v i) (p := b ztewd + Function.update ztdnc ztbic
              ztwtt ztewd)
            by_grind by_grind v25
            by_grind pv by_omega by_omega by_omega
          refine ztkkx
          have J₂ := J₁.step (i := i) hvi hcv hdisj'
            (fun r _ => by
              by_cases h : r = u i
              · grind
              · rw [Function.update_of_ne h]; grind)
            by_omega
          have q1 : Function.update ztdnc _ ztwtt _ =
              cnt2F u v i _ := Function.update_of_ne ztnr _ _
          have q2 : Function.update zthys _ ztxbn _ =
              lst2F u v i _ := Function.update_of_ne ztnr _ _
          rw [m₂, v01, q1]
          rw [q1, q2, cnt2_update_ne u v i hne, lst2_update_ne u v i hne] at J₂
          exact J₂
        by_cases a1 : u i < v i
        · zudir
          exact ⟨e₂, _, .ifLtN_true by_omega x₂, by_omega, g₂, J₂⟩
        by_cases a2 : v i < u i
        · zudir
          exact ⟨e₂, _, .ifLtN_false by_omega
            ztspf, by_omega, g₂, J₂⟩
        · refine ⟨e₁, _, .ifLtN_false by_omega
            ztzrm, by_omega, by_omega, ?_⟩
          rw [← cnt2_update_eq u v i by_omega, ← lst2_update_eq u v i by_omega]
          exact J₁
      zuboj
      have e1011 : ztuui := by_grind
      have e1201 : e₂.nreg 43201 = i := by_grind
      zueia
      have X := Exec.seq x₁ ztsxb
      refine ⟨_, _, X, ⟨X.wb_right, i + 1, by simp [e1011, e1201], by_omega,
        hfe.trans ztnyc, by_omega⟩, ?_⟩
      zudls
      omega)
    ⟨hw, 0, hi, Nat.zero_le _, FrameM.refl _ _,
      { ptr := fun r hr => by rw [hm, hFCv r hr]; rfl
        cells := fun r _ t ht => by_tauto
        rest := fun a _ _ => by zvmwi
        len := fun r => rfl }⟩
  have hiK' : i = K := by
    zuelx
  subst hiK'
  exact ⟨d', k, e, by_omega, hw', hf, I⟩
end exec
end
end BuildRam
end Chazelle.Core
namespace Chazelle.Core
namespace BuildRam
open Machine Machine.Stmt Programs SignK
@[expose] public section
def seqLoop : Stmt :=
  .whileLtN 43201 43102 (block [.addN 43230 44004 43201, .storeN 43230 43201,
    .addN 43201 43201 43011])
theorem wr_seqLoop : wrM ztdup seqLoop = true := by_decide

/-- The memory with the sequence table of length `j` at `QT`. -/
def seqMem (m : ℕ → ℕ) (QT j a : ℕ) : ℕ := if QT ≤ a ∧ a < QT + j then a - QT else m a
section exec
variable {P : Polygon} {W : ℕ}

/-- **The sequence table.** -/
theorem seqLoop_exec (d : Config) (hw : WordsBounded W d) {A QT : ℕ} (hA : d.nreg 43102 = A)
    (hQT : d.nreg 44004 = QT) (h1 : d.nreg 43011 = 1) (hi : d.nreg 43201 = 0)
    (hQW : QT + A ≤ W) :
    ∃ d' k, Exec P W seqLoop d d' k ∧ k ≤ 5 * A + 2 ∧ WordsBounded W d' ∧
      FrameM ztdup d d' ∧
      d'.nmem = seqMem d.nmem QT A := by
  obtain ⟨d', k, e, ⟨hw', j, hj', hjA, hf, hm'⟩, htest, hk⟩ := Exec.whileLtN_potential
    (P := P) (W := W) (a := 43201) (b := 43102) (body := _)
    (fun e => WordsBounded W e ∧ ∃ j, e.nreg 43201 = j ∧ j ≤ A ∧
      FrameM ztdup d e ∧ e.nmem = seqMem d.nmem QT j)
    (fun e => 5 * ztldu) ztchu
    (fun e ⟨hwe, j, hje, hjA, hfe, hme⟩ htest => by
      have r1 : e.nreg 44004 = QT := by rw [hfe.1 _ by_decide, hQT]
      have r2 : ztizs := by zunhv
      have r3 : ztpon := by zunhw
      rw [hje, r3] at htest
      have X : ∃ e' k, Exec P W (block [.addN 43230 44004 43201, .storeN 43230 43201,
          .addN 43201 43201 43011]) e e' k ∧ k = 3 ∧ e'.nreg 43201 = j + 1 ∧
          e'.nmem = seqMem d.nmem QT ztl := by
        exec_block
        · omega
        · config_simp; omega
        · refine ztkw <;> config_simp
          · omega
          · rw [r1, hje, hme]
            funext a
            simp only [upd_apply, seqMem]
            grind
      zudrb
      exact ⟨e', k, x, ⟨x.wb_right, j + 1, hj', by_omega, hfe.trans ztjux,
        hm'⟩, by_omega⟩)
    ⟨hw, 0, hi, Nat.zero_le _, FrameM.refl _ _, by
      funext a; simp only [seqMem]; simp⟩
  have hjA' : ztsjq := by
    zuely
  subst hjA'
  exact ⟨d', k, e, by_omega, hw', hf, hm'⟩
end exec

/-- The header of the normal form at `H = r44000`, and the handle into `r40003`. -/
def hdrB : Stmt :=
  block [.copyN 43231 44000, .storeN 43231 43002, .addN 43231 43231 43011,
    .storeN 43231 43102, .addN 43231 43231 43011, .storeN 43231 43200,
    .addN 43231 43231 43011, .storeN 43231 44001, .addN 43231 43231 43011,
    .storeN 43231 44002, .addN 43231 43231 43011, .storeN 43231 44003,
    .addN 43231 43231 43011, .storeN 43231 44004, .addN 43231 43231 43011,
    .storeN 43231 44005, .addN 43231 43231 43011, .storeN 43231 44000,
    .addN 43231 43231 43011, .storeN 43231 43010, .addN 43231 43231 43011,
    .storeN 43231 44000, .addN 43231 43231 43011, .storeN 43231 43010,
    .copyN 40003 44000]
theorem wr_hdrB : wrM ztike hdrB = true := by_decide

/-- The twelve header words. -/
def hdrW (K A R CT AT RT QT LT H : ℕ) (f : ℕ) : ℕ :=
  if f = 0 then K else if f = 1 then A else if f = 2 then R else if f = 3 then CT
  else if f = 4 then AT else if f = 5 then RT else if f = 6 then QT else if f = 7 then LT
  else if f = 8 then H else if f = 9 then 0 else if f = 10 then H else 0
section exec
variable {P : Polygon} {W : ℕ}

/-- **The header.** -/
theorem hdrB_exec (d : Config) (hw : WordsBounded W d) {K A R CT AT RT QT LT H : ℕ}
    (hH : d.nreg 44000 = H) (hK : d.nreg 43002 = K) (hA : d.nreg 43102 = A)
    (hR : d.nreg 43200 = R) (hCT : d.nreg 44001 = CT) (hAT : d.nreg 44002 = AT)
    (hRT : d.nreg 44003 = RT) (hQT : d.nreg 44004 = QT) (hLT : d.nreg 44005 = LT)
    (h0 : d.nreg 43010 = 0) (h1 : d.nreg 43011 = 1) (hHW : H + 12 ≤ W) :
    ∃ d' k, Exec P W hdrB d d' k ∧ k = 25 ∧ WordsBounded W d' ∧
      FrameM ztike d d' ∧ d'.nreg 40003 = H ∧
      ztedb ∧
      ztfje := by
  suffices X : ∃ d' k, Exec P W hdrB d d' k ∧ k = 25 ∧ d'.nreg 40003 = H ∧
      ztedb ∧
      ztfje by
    obtain ⟨d', k, x, hk, a1, a2, a3⟩ := X
    exact ⟨d', k, x, hk, x.wb_right, exec_frameM x wr_hdrB, a1, a2, a3⟩
  unfold hdrB
  exec_block
  all_goals first
    | (config_simp; simp (config := { failIfUnchanged := false }) only [hH, h1]; omega)
    | skip
  refine ⟨rfl, ?_, fun f hf => ?_, fun a ha => ?_⟩ <;> config_simp
  · zummn
  · simp only [hH, hK, hA, hR, hCT, hAT, hRT, hQT, hLT, h0, h1, upd_apply, hdrW]
    interval_cases f <;> ifs_omega
  · simp only [hH, h1, upd_apply]
    ifs_omega
end exec
end
end BuildRam
namespace BuildNF
@[expose] public section
open List
open BuildRam (lstF cntF wmaxF lst2F cnt2F offF rtv hdrW)
variable {M : Model} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}

/-! ## Region indices are at most `K` -/
theorem mem_foldl_step {st u : List ℕ} {x : ℕ} (h : x ∈ u.foldl BuildStack.step st) :
    x ∈ st ∨ x ∈ u := by
  induction u generalizing st with
  | nil => exact Or.inl h
  | cons y u ih =>
    rcases ih h with h' | h'
    · unfold BuildStack.step at h'
      split_ifs at h' with hy
      · rcases st with _ | ⟨z, st⟩
        · simp_all
        simp_all
      grind
    · simp_all
theorem ridx_label_le {w : List ℕ} {K : ℕ} (hw : ∀ x ∈ w, x < K) (m : ℕ) :
    ridx (BuildStack.label w m) ≤ K := by
  unfold BuildStack.label
  rcases hh : (BuildStack.run ztibp).head? with _ | x
  · positivity
  · zunvx
    have hx := mem_of_mem_head? hh
    unfold BuildStack.run at hx
    rcases mem_foldl_step hx with h' | h'
    · simp_all
    grind
theorem cw_lt (h : Input M Q L E) : ∀ x ∈ cw E, x < L.length := by
  zuh
  unfold cw at hx
  zufxu
  have := mem_range.1 ztvry
  omega
theorem topR_le (h : Input M Q L E) (m : ℕ) : topR E m ≤ L.length :=
  ridx_label_le ztvmc m
theorem chordRec_up_le (h : Input M Q L E) {i : ℕ} (hi : i < L.length) :
    (chordRec M Q L E i).up ≤ L.length ∧ (chordRec M Q L E i).dn ≤ L.length := by
  unfold chordRec outside
  zumpf
  have := ridx_label_le (w := E.map ztcfk) ztvmc
    ((evs M Q L E).idxOf (BuildRegions.e1 M Q L i))
  grind

/-- Every chord occurs in the word. -/
theorem mem_cw (h : Input M Q L E) {x : ℕ} (hx : x < L.length) : x ∈ cw E := by
  unfold cw
  exact mem_map.2 ⟨2 * x, h.perm.mem_iff.2 (mem_range.2 by_omega), by_omega⟩

/-! ## The machine functions -/

/-- The region of arc `j`. -/
noncomputable def keyA (M : Model) (Q : Polygon) (L : List zte) (E : List ℕ) (j : ℕ) : ℕ :=
  (arcRec M Q L E ztbhi).reg

/-- The weight of arc `j`. -/
noncomputable def wA (M : Model) (Q : Polygon) (L : List zte) (E : List ℕ) (j : ℕ) : ℕ :=
  arcW M Q ztyvj

/-- The region above chord `i`. -/
noncomputable def upC (M : Model) (Q : Polygon) (L : List zte) (E : List ℕ) (i : ℕ) : ℕ :=
  (chordRec M Q L E i).up

/-- The region below chord `i`. -/
noncomputable def dnC (M : Model) (Q : Polygon) (L : List zte) (E : List ℕ) (i : ℕ) : ℕ :=
  (chordRec M Q L E i).dn
theorem arcList_pos (hK : L.length ≠ 0) :
    arcList M Q L E = (gapStarts M Q L E).map ztgfc := by
  zuhah
theorem arcList_getD (hK : L.length ≠ 0) {j : ℕ} (hj : j < (gapStarts M Q L E).length) :
    (arcList M Q L E).getD j ztgp = arcRec M Q L E ztbhi := by
  rw [arcList_pos hK, getD_eq_getElem?_getD, getElem?_map, getElem?_eq_getElem hj,
    Option.map_some, Option.getD_some, getD_eq_getElem?_getD, getElem?_eq_getElem hj,
    Option.getD_some]
theorem regArcs_eq (hK : L.length ≠ 0) (r : ℕ) :
    regArcs M Q L E r = lstF ztcai (gapStarts M Q L E).length r := by
  unfold regArcs lstF
  zujhn
  zuldd
  zun
  rw [← arcList_pos hK, arcList_getD hK (mem_range.1 hj)]
  rfl
theorem regChords_eq (r : ℕ) :
    regChords M Q L E r = lst2F ztkgi ztjuc L.length r := rfl
theorem regWt_eq (hK : L.length ≠ 0) (r : ℕ) :
    regWt M Q L E r = wmaxF ztcai ztqyn (gapStarts M Q L E).length r := by
  unfold regWt wmaxF
  rw [← regArcs_eq hK]
  zucr
  apply map_congr_left
  zun
  have hj' : ztccc := by
    unfold regArcs at hj
    rw [arcList_pos hK, length_map] at hj
    simp_all
  rw [arcList_getD hK hj']
  rfl

/-! ## The layout -/

/-- **The normal form from the tables** (`K > 0`). -/
theorem nfAt_of_tables (h : Input M Q L E) (hK : L.length ≠ 0) {m : ℕ → ℕ}
    {H CT AT RT QT LT : ℕ}
    (hH : ∀ f, f < 12 → m ztjiz = hdrW L.length (gapStarts M Q L E).length ztkr
      CT AT RT QT LT H f)
    (hC : ∀ i, i < L.length → ∀ f, f < 5 → m (CT + 5 * i + f) = cf (chordRec M Q L E i) f)
    (hA : ∀ j, j < (gapStarts M Q L E).length → ∀ f, f < 5 →
      m ztgzs = af ztyvj f)
    (hR : ∀ r, r < L.length + 1 → ∀ f, f < 5 → m (RT + 5 * r + f) =
      rtv ztxbj
        ztdaw
        (wmaxF ztcai ztqyn (gapStarts M Q L E).length) ztgcs)
    (hLa : ∀ r, r < L.length + 1 → ∀ t, t < cntF ztcai (gapStarts M Q L E).length r →
      m (LT + offF ztxbj
        ztdaw r + t) =
        (lstF ztcai (gapStarts M Q L E).length r).getD t 0)
    (hLc : ∀ r, r < L.length + 1 → ∀ t, t < cnt2F ztkgi ztjuc L.length r →
      m (LT + (offF ztxbj
        ztdaw r +
          cntF ztcai (gapStarts M Q L E).length r) + t) =
        (lst2F ztkgi ztjuc L.length r).getD t 0)
    (hQ : ∀ j, j < (gapStarts M Q L E).length → m (QT + j) = j) :
    NFAt m H ztob := by
  have hlenA : (buildNF M Q L E).arcs.length = (gapStarts M Q L E).length := by
    show (arcList M Q L E).length = _
    zujhn
  have h0 := hH 0 by_norm_num; have h1 := hH 1 by_norm_num; have h2 := hH 2 by_norm_num
  have h3 := hH 3 by_norm_num; have h4 := hH 4 by_norm_num; have h5 := hH 5 by_norm_num
  have h6 := hH 6 by_norm_num; have h7 := hH 7 by_norm_num; have h9 := hH 9 by_norm_num
  have h11 := hH 11 by_norm_num
  simp only [hdrW, Nat.add_zero] at h0 h1 h2 h3 h4 h5 h6 h7 h9 h11
  norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h9 h11
  refine ⟨?_, ?_, ?_, ?_, ?_, fun i hi => ?_, fun j hj => ?_, fun r hr => ?_, fun j hj => ?_,
    fun k hk => ?_, fun r hr => ?_⟩
  · zvmzn; zuoyv
  · omega
  · zvmxx; zuoyv
  · tauto
  · tauto
  · -- chords
    have hi' : ztsjb := by simpa [buildNF] using hi
    rw [h3, Input.chord_eq hi']
    have c0 := hC i hi' 0 by_norm_num; have c1 := hC i hi' 1 by_norm_num
    tauto
  · -- arcs
    rw [hlenA] at hj
    have ha : (buildNF M Q L E).arc j = arcRec M Q L E ztbhi := by
      unfold NF.arc; exact arcList_getD hK hj
    rw [h4, ha]
    have c0 := hA j hj 0 by_norm_num; have c1 := hA j hj 1 by_norm_num
    tauto
  · -- regions
    have hr' : ztmwo := by simpa [buildNF] using hr
    rw [h5, h.region_eq hr']
    zubi
    have c0 := hR r hr' 0 by_norm_num; have c1 := hR r hr' 1 by_norm_num
    have c2 := hR r hr' 2 by_norm_num; have c3 := hR r hr' 3 by_norm_num
    have c4 := hR r hr' 4 by_norm_num
    rw [BuildRam.rtv_eq _ _ _ _ _ by_norm_num] at c0 c1 c2 c3 c4
    norm_num at c0 c1 c2 c3 c4
    refine ztgnw
    · rw [c0, regArcs_eq hK]; rfl
    · tauto
    · rw [c4, regWt_eq hK]
    · rw [h7, c1]
      rw [regArcs_eq hK] at ht ⊢
      tauto
    · rw [h7, c3]
      rw [regChords_eq] at ht ⊢
      exact hLc r hr' t ht
  · -- seq
    have hj' : ztccc := by
      have : (buildNF M Q L E).seq = range (arcList M Q L E).length := rfl
      rw [this, length_range, arcList_pos hK, length_map] at hj; exact hj
    rw [h6, hQ j hj']
    show j = (range (arcList M Q L E).length).getD j 0
    rw [getD_eq_getElem?_getD, getElem?_range (by rw [arcList_pos hK, length_map]; omega),
      Option.getD_some]
  · tauto
  tauto
end
end BuildNF
end Chazelle.Core
namespace Chazelle.Core
namespace BuildRam
open Machine Machine.Stmt Programs SignK
@[expose] public section
def setupB : Stmt :=
  block [.constN 42102 1, .constN 43013 3, .addN 43200 43002 43011,
    .copyN 44000 9999,
    .constN 43240 12, .addN 44001 44000 43240,
    .addN 43241 43002 43002, .addN 43241 43241 43241, .addN 43241 43241 43002,
    .addN 44002 44001 43241,
    .addN 43242 42001 42001, .addN 43242 43242 43242, .addN 43242 43242 42001,
    .addN 44003 44002 43242,
    .addN 43243 43200 43200, .addN 43243 43243 43243, .addN 43243 43243 43200,
    .addN 44004 44003 43243,
    .addN 44005 44004 42001,
    .addN 43244 42001 43002, .addN 43244 43244 43002, .addN 44006 44005 43244,
    .addN 44007 44006 42001, .addN 44008 44007 42001,
    .addN 43245 43200 43200, .addN 43245 43245 43200, .addN 44011 44008 43245,
    .addN 44012 44011 43200, .addN 9999 44012 43200,
    .constN 43100 0, .constN 43101 0, .constN 43102 0, .copyN 43103 30005, .copyN 43104 30005]

/-- The size of the tables of phase B. -/
def sizeB (K : ℕ) : ℕ := 35 * K + 22

/-- The registers that stay fixed during phase B (after its setup). -/
structure BConst (D T K B H lo hd kd : ℕ) (d : Config) : Prop where
  rD : d.nreg 40000 = D
  rT : d.nreg 42000 = T
  rN : d.nreg 42001 = 2 * K
  r1a : d.nreg 42102 = 1
  rB : d.nreg 43001 = B
  rK : d.nreg 43002 = K
  r0 : d.nreg 43010 = 0
  r1 : d.nreg 43011 = 1
  r3 : d.nreg 43013 = 3
  rR : d.nreg 43200 = K + 1
  rH : d.nreg 44000 = H
  rCT : d.nreg 44001 = H + 12
  rAT : d.nreg 44002 = H + 12 + 5 * K
  rRT : d.nreg 44003 = H + 12 + 15 * K
  rQT : d.nreg 44004 = H + 17 + 20 * K
  rLT : d.nreg 44005 = H + 17 + 22 * K
  rST : d.nreg 44006 = H + 17 + 26 * K
  rWT : d.nreg 44007 = H + 17 + 28 * K
  rCA : d.nreg 44008 = H + 17 + 30 * K
  rFA : d.nreg 44011 = H + 20 + 33 * K
  rFC : d.nreg 44012 = H + 21 + 34 * K
  rA : d.nreg 9999 = H + sizeB K
  rlo : d.nreg 44020 = lo
  rhd : d.nreg 44021 = hd
  r19 : d.nreg 41019 = 1
  r23 : d.nreg 41023 = kd

/-- The fixed registers. -/
def constRegs : List ℕ :=
  [40000, 42000, 42001, 42102, 43001, 43002, 43010, 43011, 43013, 43200, 44000, 44001, 44002,
    44003, 44004, 44005, 44006, 44007, 44008, 44011, 44012, 9999, 44020, 44021, 41019, 41023]

/-- The fixed registers survive a frame that does not write them. -/
theorem BConst.frame {D T K B H lo hd kd : ℕ} {d d' : Config} {Bw : ℕ → Bool}
    (h : BConst D T K B H lo hd kd d) (hf : FrameM Bw d d')
    (hB : ∀ r ∈ constRegs, Bw r = false) : BConst D T K B H lo hd kd d' := by
  have g : ∀ r ∈ constRegs, d'.nreg r = d.nreg r := fun r hr => hf.1 r ztfsg
  simp only [constRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at g
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19,
    g20, g21, g22, g23, g24, g25, g26⟩ := g
  exact ⟨by rw [g1, h.rD], by rw [g2, h.rT], by rw [g3, h.rN], by rw [g4, h.r1a],
    by rw [g5, h.rB], by rw [g6, h.rK], by rw [g7, h.r0], by rw [g8, h.r1], by rw [g9, h.r3],
    by rw [g10, h.rR], by rw [g11, h.rH], by rw [g12, h.rCT], by rw [g13, h.rAT],
    by rw [g14, h.rRT], by rw [g15, h.rQT], by rw [g16, h.rLT], by rw [g17, h.rST],
    by rw [g18, h.rWT], by rw [g19, h.rCA], by rw [g20, h.rFA], by rw [g21, h.rFC],
    by rw [g22, h.rA], by rw [g23, h.rlo], by rw [g24, h.rhd], by rw [g25, h.r19],
    by rw [g26, h.r23]⟩
section exec
variable {P : Polygon} {W : ℕ}

/-- The registers `setupB` writes. -/
def BsetupB (r : ℕ) : Bool :=
  decide (r ∈ [42102, 43013, 43200, 44000, 43240, 44001, 43241, 44002, 43242, 44003, 43243,
    44004, 44005, 43244, 44006, 44007, 44008, 43245, 44011, 44012, 9999, 43100, 43101,
    43102, 43103, 43104])
theorem wr_setupB : wr BsetupB setupB = true := by_decide

/-- **The setup of phase B.** -/
theorem setupB_exec (d : Config) (hw : WordsBounded W d) {K H SE : ℕ}
    (hK : d.nreg 43002 = K) (hN : d.nreg 42001 = 2 * K) (h1 : d.nreg 43011 = 1)
    (hH : d.nreg 9999 = H) (hSE : d.nreg 30005 = SE) (hW : H + sizeB K ≤ W) :
    ∃ d' k, Exec P W setupB d d' k ∧ k = 34 ∧
      d'.nreg 42102 = 1 ∧ d'.nreg 43013 = 3 ∧ d'.nreg 43200 = K + 1 ∧ d'.nreg 44000 = H ∧
      d'.nreg 44001 = H + 12 ∧ d'.nreg 44002 = H + 12 + 5 * K ∧
      d'.nreg 44003 = H + 12 + 15 * K ∧ d'.nreg 44004 = H + 17 + 20 * K ∧
      d'.nreg 44005 = H + 17 + 22 * K ∧ d'.nreg 44006 = H + 17 + 26 * K ∧
      d'.nreg 44007 = H + 17 + 28 * K ∧ d'.nreg 44008 = H + 17 + 30 * K ∧
      d'.nreg 44011 = H + 20 + 33 * K ∧ d'.nreg 44012 = H + 21 + 34 * K ∧
      d'.nreg 9999 = H + sizeB K ∧ d'.nreg 43100 = 0 ∧ d'.nreg 43101 = 0 ∧
      d'.nreg 43102 = 0 ∧ d'.nreg 43103 = SE ∧ d'.nreg 43104 = SE := by
  unfold sizeB at hW
  have hW1 : 12 ≤ W := by_omega
  unfold setupB
  exec_block
  all_goals first
    | (config_simp; simp (config := { failIfUnchanged := false }) only [hK, hN, h1, hH]; omega)
    | skip
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩ <;> config_simp
  all_goals first
    | (simp (config := { failIfUnchanged := false }) only [hK, hN, h1, hH, hSE, sizeB]; omega)
    | (· omega)
end exec
end
end BuildRam
end Chazelle.Core
namespace Chazelle.Core
namespace BuildRam
open Machine Machine.Stmt Programs SignK NFLoc
@[expose] public section
theorem sum_ind (k R : ℕ) :
    ((List.range R).map fun r => if k = r then 1 else 0).sum = if k < R then 1 else 0 := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    zuwd
theorem sum_cntF (key : ℕ → ℕ) {n R : ℕ} (h : ∀ j, j < n → key j < R) :
    ((List.range R).map (cntF key n)).sum = n := by
  induction n with
  | zero => simp [show cntF key 0 = fun _ => 0 from funext fun r => rfl]
  | succ n ih =>
    have e : (List.range R).map (cntF key ztkk) =
        (List.range R).map fun r => cntF key n r + ztlqc := by
      apply List.map_congr_left; intro r _; exact cntF_succ key n r
    rw [e, List.sum_map_add, ih (fun j hj => h j by_omega), sum_ind, ite_eq_left (h n by_omega)]
theorem sum_cnt2F_le (u v : ℕ → ℕ) (n R : ℕ) : ((List.range R).map (cnt2F u v n)).sum ≤ 2 * n := by
  induction n with
  | zero => simp [show cnt2F u v 0 = fun _ => 0 from funext fun r => rfl]
  | succ n ih =>
    have e : (List.range R).map (cnt2F u v ztkk) =
        (List.range R).map fun r => cnt2F u v n r + ztdor := by
      apply List.map_congr_left; intro r _; exact cnt2F_succ u v n r
    have hle : ((List.range R).map fun r => if u n = r ∨ v n = r then 1 else 0).sum ≤ 2 := by
      have : ∀ r, ztdor ≤
          ztlqe + ztlqf := fun r => by_grind
      calc _ ≤ ((List.range R).map fun r =>
              ztlqe + ztlqf).sum :=
            List.sum_le_sum (fun r _ => this r)
        _ = _ := by rw [List.sum_map_add]
        _ ≤ 2 := by rw [sum_ind, sum_ind]; split_ifs <;> omega
    rw [e, List.sum_map_add]
    omega
theorem offF_eq (cA cC : ℕ → ℕ) (R : ℕ) :
    offF cA cC R = ((List.range R).map cA).sum + ((List.range R).map cC).sum := by
  unfold offF; simp

/-- **The size of the list table.** -/
theorem offF_R_le (key u v : ℕ → ℕ) {A K R : ℕ} (h : ∀ j, j < A → key j < R) :
    offF ztdud (cnt2F u v K) R ≤ A + 2 * K := by
  rw [offF_eq, sum_cntF key h]
  have := sum_cnt2F_le u v K R
  omega
variable {key key' : ℕ → ℕ} {n : ℕ} {u v u' v' : ℕ → ℕ}
theorem lstF_congr (h : ∀ j, j < n → key j = key' j) (r : ℕ) :
    lstF key n r = lstF key' n r := by
  unfold lstF
  apply List.filter_congr
  simp_all
theorem cntF_congr (h : ∀ j, j < n → key j = key' j) :
    cntF key n = cntF key' n := by
  funext r; unfold cntF; zuosf
theorem wmaxF_congr {key key' w w' : ℕ → ℕ} {n : ℕ} (h : ∀ j, j < n → key j = key' j)
    (hw : ∀ j, j < n → w j = w' j) : wmaxF key w n = wmaxF key' w' n := by
  funext r
  unfold wmaxF
  zuosf
  zucr
  zucfh
  zun
  unfold lstF at hj
  simp_all
theorem lst2F_congr {n : ℕ} (hu : ∀ i, i < n → u i = u' i)
    (hv : ∀ i, i < n → v i = v' i) (r : ℕ) : lst2F u v n r = lst2F u' v' n r := by
  unfold lst2F
  apply List.filter_congr
  simp_all
theorem cnt2F_congr {n : ℕ} (hu : ∀ i, i < n → u i = u' i)
    (hv : ∀ i, i < n → v i = v' i) : cnt2F u v n = cnt2F u' v' n := by
  funext r; unfold cnt2F; rw [lst2F_congr hu hv]

/-- The counted interval of a chain descriptor fits the word bound. -/
theorem twice_m_le {P : Polygon} {W : ℕ} {m : ℕ → ℕ} {D : ℕ} {M : Model}
    (hM : ModelDescAt m D zta M) (hCW : LocChainWF P W m D) (h0 : m D = 0) :
    2 * m ztclg ≤ W := by
  rcases hM with ⟨-, H, C, hC, -⟩ | ⟨h1, -, -⟩
  · obtain ⟨-, -, -, -, h2⟩ := hCW h0 H C hC
    zukdn
    rw [show D + 3 = D + 1 + 2 by omega, hm]
    have := C.m_lt
    omega
  · omega
end
end BuildRam
end Chazelle.Core
namespace Chazelle.Core
namespace BuildRam
open Machine Machine.Stmt Programs SignK NFLoc
open BuildNF (stk gapsB)
@[expose] public section
def phaseB1 : Stmt := .seq setupB (.seq lohiS passLoop)
section exec
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 1000000 in
/-- **Phase B up to the end of the main pass.** -/
theorem phaseB1_exec (hG : GoodEnv P) (hWn : hostWords P.n ≤ W) (c : Config)
    (hw : WordsBounded W c) {M : Model} {L : List zte} {E : List ℕ} {D T SE B H : ℕ}
    (hI : BuildNF.Input M zta L E) (hlen : E.length = 2 * L.length)
    (hD : c.nreg 40000 = D) (hT : c.nreg 42000 = T) (hN : c.nreg 42001 = 2 * L.length)
    (hB : c.nreg 43001 = B) (hK : c.nreg 43002 = L.length) (h0 : c.nreg 43010 = 0)
    (h1 : c.nreg 43011 = 1) (hSEr : c.nreg 30005 = SE) (hH : c.nreg 9999 = H)
    (hwf : ModelDescWF P H c.nmem D) (hM : ModelDescAt c.nmem D zta M)
    (hR : RecsAt c.nmem T L) (hTH : T + 8 * L.length ≤ H) (hCL : ChordListAt c.nmem B L)
    (hBH : B + 3 * L.length ≤ H) (hSE : ∀ j, j < E.length → c.nmem ztjmr = E.getD j 0)
    (hSEH : SE + E.length ≤ H) (hroom : H + sizeB L.length ≤ W) :
    ∃ c₃ k, Exec P W phaseB1 c c₃ k ∧ k ≤ 11702 * E.length + 48 ∧ 12 * E.length ≤ k ∧
      WordsBounded W c₃ ∧
      BConst D T L.length B H ztkaj zthxz ztvhb c₃ ∧
      ∃ (F : PassFix P W M L E D H T SE B ztnli (H + 12 + 5 * L.length)
          (H + 17 + 26 * L.length) (H + 17 + 28 * L.length) ztkaj
          zthxz c.nmem) (c₂ : Config), PassInv F c₂ c₃ E.length := by
  zuvu
  zuccu

  -- 1. setup
  obtain ⟨c₁, k₁, x₁, hk₁, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15,
    s16, s17, s18, s19, s20⟩ := setupB_exec (P := P) c hw hK hN h1 hH hSEr hroom
  zubcr
  have f₁ := exec_frameB x₁ wr_setupB
  have g₁ : ∀ r, BsetupB r = false → c₁.nreg r = c.nreg r := f₁.1
  -- 2. the counted interval
  obtain ⟨c₂, k₂, x₂, hk₂, l1, l2, l3, l4, f₂⟩ := lohiS_exec (P := P) c₁ w₁ (D := D)
    (by rw [g₁ _ by_decide, hD]) (by rw [f₁.2.2.1]; exact twice_m_le hM hCW)
    by_omega ztnvt by_grind
  rw [f₁.2.2.1] at l1 l2 l3
  zuboj
  have g₂ : ∀ r, r ≠ 41023 → r ≠ 41019 → r ≠ 44020 → r ≠ 44021 → r ≠ 44022 →
      c₂.nreg r = c₁.nreg r := fun r a1 a2 a3 a4 a5 => f₂.1 r (by
    simp_all)
  have mm₂ : ztckc := by zuoit
  have G₂ : ∀ r, BsetupB r = false → r ≠ 41023 → r ≠ 41019 → r ≠ 44020 → r ≠ 44021 →
      r ≠ 44022 → c₂.nreg r = c.nreg r := fun r h a1 a2 a3 a4 a5 => by
    grind
  have C₂ : BConst D T K B H ztkaj zthxz ztvhb c₂ :=
    { rD := by rw [G₂ 40000 by_decide by_norm_num by_norm_num by_norm_num by_norm_num
          by_norm_num, hD]
      rT := by rw [G₂ 42000 by_decide by_norm_num by_norm_num by_norm_num by_norm_num
          by_norm_num, hT]
      rN := by rw [G₂ 42001 by_decide by_norm_num by_norm_num by_norm_num by_norm_num
          by_norm_num, hN]
      r1a := by_grind
      rB := by rw [G₂ 43001 by_decide by_norm_num by_norm_num by_norm_num by_norm_num
          by_norm_num, hB]
      rK := by rw [G₂ 43002 by_decide by_norm_num by_norm_num by_norm_num by_norm_num
          by_norm_num, hK]
      r0 := by rw [G₂ 43010 by_decide by_norm_num by_norm_num by_norm_num by_norm_num
          by_norm_num, h0]
      r1 := by rw [G₂ 43011 by_decide by_norm_num by_norm_num by_norm_num by_norm_num
          by_norm_num, h1]
      r3 := by_grind
      rR := by_grind
      rH := by_grind
      rCT := by_grind
      rAT := by_grind
      rRT := by_grind
      rQT := by_grind
      rLT := by_grind
      rST := by_grind
      rWT := by_grind
      rCA := by_grind
      rFA := by_grind
      rFC := by_grind
      rA := by_grind
      rlo := l1
      rhd := l2
      r19 := l4
      r23 := l3 }
  -- 3. the main pass
  obtain ⟨hcI, hcW⟩ := BuildRam.countedIv (P := P) hM
  have hlohi : loOf c.nmem D ≤ hiOf c.nmem D P.n := by
    unfold loOf hiOf; split_ifs <;> omega
  have F : PassFix P W M L E D H T SE B ztnli ztnlh (H + 17 + 26 * K)
      (H + 17 + 28 * K) ztkaj zthxz c.nmem :=
    { inp := hI, good := hG, hwords := hWn, len := hlen, wf := hwf, desc := hM, HW := hHW,
      recs := hR, TH := hTH, chl := hCL, BH := hBH, codes := hSE, SEH := hSEH,
      l1 := by_omega, l2 := by_omega, l3 := by_omega, l4 := by_omega,
      l5 := by unfold sizeB at hroom; omega
      cnt := fun p hp => by rw [hcI p hp, hdOf_eq]; omega
      cntW := by rw [hdOf_eq]; omega }
  have n100 : c₂.nreg 43100 = 0 := by
    grind
  have n103 : c₂.nreg 43103 = SE + 0 := by
    grind
  have n104 : c₂.nreg 43104 = SE := by
    grind
  have n101 : c₂.nreg 43101 = (stk E 0).length := by
    rw [g₂ _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num, s17]; rfl
  have n102 : c₂.nreg 43102 = (gapsB M zta L E 0).length := by
    rw [g₂ _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num, s18]; rfl
  have nN : c₂.nreg 42001 = E.length := by rw [C₂.rN, hlen]
  have I₀ : PassInv F c₂ c₂ 0 :=
    { m_le := Nat.zero_le _, r100 := n100, r103 := n103, r104 := n104, r101 := n101,
      sp_le := by_rfl, r102 := n102,
      rD := C₂.rD, rT := C₂.rT, rN := nN, r1a := C₂.r1a, rB := C₂.rB,
      r0 := C₂.r0, r1 := C₂.r1, rCT := C₂.rCT, rAT := C₂.rAT, rST := C₂.rST, rWT := C₂.rWT,
      rlo := C₂.rlo, rhd := C₂.rhd, r19 := C₂.r19, r23 := C₂.r23,
      low := fun a _ => by zuoyz,
      stack := fun k hk => by simp [stk, BuildNF.cw, BuildStack.run] at hk,
      chords := fun x _ hx => by simp at hx,
      arcs := fun j hj => by simp [gapsB] at hj,
      frame := FrameM.refl _ _ }
  obtain ⟨c₃, k₃, x₃, hk₃, hk₃', w₃, I₃⟩ := passLoop_exec F I₀ w₂
  have C₃ := C₂.frame I₃.frame by_decide
  exact ⟨c₃, _, .seq x₁ ztjdw, by_omega, by_omega, w₃, C₃, F, c₂, I₃⟩
end exec
end
end BuildRam
end Chazelle.Core
namespace Chazelle.Core
namespace BuildRam
open Machine Machine.Stmt Programs SignK NFLoc
open BuildNF (cf af chordRec arcRec gapStarts keyA wA upC dnC)
@[expose] public section
def regPhase : Stmt :=
  .seq ztcyn (.seq zeroLoop (.seq ztcyn
    (.seq arcCntLoop (.seq ztcyn (.seq chCntLoop
      (.seq ztkre (.seq regRecLoop
        (.seq ztcyn (.seq arcFillLoop (.seq ztcyn
          (.seq chFillLoop (.seq ztcyn (.seq seqLoop hdrB)))))))))))))

/-- The registers the region phase writes. -/
def BregPhase (r : ℕ) : Bool :=
  decide (43201 ≤ r ∧ r < 43232) || decide (r = 40003)
theorem wr_regPhase : wrM BregPhase regPhase = true := by
  rfl
section exec
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 4000000 in
/-- **The region phase.** -/
theorem regPhase_exec (d : Config) (hw : WordsBounded W d) {D T B H lo hd kd K A : ℕ}
    (C : BConst D T K B H lo hd kd d) (hA : d.nreg 43102 = A) (hAle : A ≤ 2 * K)
    {keyF uF vF wF : ℕ → ℕ}
    (hkey : ∀ j, j < A → d.nmem ztbdx = keyF j)
    (hkR : ∀ j, j < A → keyF j < K + 1)
    (hwt : ∀ j, j < A → d.nmem ztdkx = wF j)
    (hu : ∀ i, i < K → d.nmem ztcll = uF i)
    (hv : ∀ i, i < K → d.nmem ztclm = vF i)
    (huR : ∀ i, i < K → uF i < K + 1) (hvR : ∀ i, i < K → vF i < K + 1)
    (hroom : H + sizeB K ≤ W) :
    ∃ d' k, Exec P W regPhase d d' k ∧ k ≤ 200 * K + 150 ∧ 26 * ztbr ≤ k ∧
      WordsBounded W d' ∧ FrameM BregPhase d d' ∧ d'.nreg 40003 = H ∧
      (∀ f, f < 12 → d'.nmem ztjiz = hdrW K A ztbr ztnli ztnlh
        ztnlg (H + 17 + 20 * K) (H + 17 + 22 * K) H f) ∧
      (∀ a, (a < H ∨ (H + 12 ≤ a ∧ a < H + 12 + 15 * K)) → d'.nmem a = d.nmem a) ∧
      (∀ r, r < K + 1 → ∀ f, f < 5 → d'.nmem ztihe =
        rtv ztnxc ztlmc (wmaxF keyF wF A) ztgcs) ∧
      (∀ r, r < K + 1 → ∀ t, t < cntF keyF A r →
        d'.nmem (H + 17 + 22 * K + offF ztnxc ztlmc r + t) =
          (lstF keyF A r).getD t 0) ∧
      (∀ r, r < K + 1 → ∀ t, t < cnt2F uF vF K r →
        d'.nmem (H + 17 + 22 * K + (offF ztnxc ztlmc r + cntF keyF A r) + t) =
          (lst2F uF vF K r).getD t 0) ∧
      (∀ j, j < A → d'.nmem (H + 17 + 20 * K + j) = j) := by
  set m₃ := d.nmem with hm₃
  have hS := hroom; unfold sizeB at hS
  zudk
  -- the memory functions
  have ckey : cntF ztjvy A = cntF keyF A := cntF_congr hkey
  have cwmax : wmaxF ztjvy ztjvy A =
      wmaxF keyF wF A := wmaxF_congr hkey hwt
  have cc2 : cnt2F ztqnx ztqnx K =
      cnt2F uF vF K := cnt2F_congr hu hv
  have hkR' : ∀ j, j < A → m₃ ztbdx < K + 1 := by_simp_all
  -- 0/1. zero the arrays
  have z0 := Exec.constN (P := P) hw 43201 0 ztbg
  set e₀ : Config := { d with nreg := upd d.nreg 43201 0 } with he₀
  have C₀ := C.frame (Bw := fun r => decide ztevb)
    (exec_frameM z0 by_decide) by_decide
  obtain ⟨e₁, k₁, x₁, hk₁, w₁, f₁, m₁⟩ := zeroLoop_exec (P := P) e₀ z0.wb_right (m₀ := m₃)
    (CA := H + 17 + 30 * K) (R := K + 1) (fA := fun r => m₃ (H + 17 + 30 * K + r))
    (fC := fun r => m₃ (H + 17 + 30 * K + ztbr + r))
    (fW := fun r => m₃ (H + 17 + 30 * K + 2 * ztbr + r)) C₀.rCA C₀.rR C₀.r0 C₀.r1
    by_rfl by_omega (by rw [he₀]; exact (regMem_self _ _ _).symm)
  have C₁ := C₀.frame f₁ by_decide
  -- 2. arc counts
  have z2 := Exec.constN (P := P) w₁ 43201 0 ztbg
  set e₂ : Config := { e₁ with nreg := upd e₁.nreg 43201 0 } with he₂
  have C₂ := C₁.frame (Bw := fun r => decide ztevb)
    (exec_frameM z2 by_decide) by_decide
  have hA₂ : e₂.nreg 43102 = A := by
    show upd e₁.nreg 43201 0 43102 = A
    rw [upd_other _ _ _ by_norm_num, f₁.1 43102 by_decide, he₀]; tauto
  obtain ⟨e₃, k₃, x₃, hk₃, w₃, f₃, m₃'⟩ := arcCntLoop_exec (P := P) e₂ z2.wb_right (m₀ := m₃)
    (CA := H + 17 + 30 * K) (R := K + 1) (A := A) (AT := H + 12 + 5 * K)
    (WT := H + 17 + 28 * K) (fC := fun _ => 0) C₂.rCA C₂.rR C₂.r1 by_rfl hA₂
    C₂.rAT C₂.rWT by_omega by_omega by_omega hkR' by_omega
  have C₃ := C₂.frame f₃ by_decide
  -- 3. chord counts
  have z4 := Exec.constN (P := P) w₃ 43201 0 ztbg
  set e₄ : Config := { e₃ with nreg := upd e₃.nreg 43201 0 } with he₄
  have C₄ := C₃.frame (Bw := fun r => decide ztevb)
    (exec_frameM z4 by_decide) by_decide
  obtain ⟨e₅, k₅, x₅, hk₅, w₅, f₅, m₅⟩ := chCntLoop_exec (P := P) e₄ z4.wb_right (m₀ := m₃)
    (CA := H + 17 + 30 * K) (R := K + 1) (K := K) (CT := H + 12)
    (fA := cntF ztxwx A)
    (fW := wmaxF ztxwx ztzfg A)
    C₄.rCA C₄.rR C₄.r1 C₄.r3 by_rfl C₄.rK C₄.rCT by_omega by_omega
    ztbmx ztbmx
    by_omega
  have C₅ := C₄.frame f₅ by_decide
  have hA₅ : e₅.nreg 43102 = A := by
    rw [f₅.1 43102 by_decide]
    show upd e₃.nreg 43201 0 43102 = A
    rw [upd_other _ _ _ by_norm_num, f₃.1 43102 by_decide, hA₂]
  -- abbreviations of the counts
  obtain ⟨cA, hcA⟩ : ∃ f : ℕ → ℕ, f = cntF (fun j => m₃ (H + 12 + 5 * K + 5 * j)) A := by_grind
  obtain ⟨cC, hcC⟩ : ∃ f : ℕ → ℕ,
      f = cnt2F (fun i => m₃ ztcll) (fun i => m₃ ztclm) K :=
    by_grind
  obtain ⟨wR, hwR⟩ : ∃ f : ℕ → ℕ, f = wmaxF (fun j => m₃ (H + 12 + 5 * K + 5 * j))
      ztzfg A := by_grind
  rw [← hcA, ← hcC, ← hwR] at m₅
  have hoffR : offF cA cC ztbr ≤ A + 2 * K := by
    rw [hcA, hcC]; exact offF_R_le _ _ _ hkR'
  -- 4. region records
  have y1 := Exec.constN (P := P) w₅ 43201 0 ztbg
  have y2 := Exec.constN (P := P) y1.wb_right 43210 0 ztbg
  have X6 : Exec P W ztkre e₅ _ 2 :=
    .seq y1 ztffc
  set e₆ := { ({ e₅ with nreg := upd e₅.nreg 43201 0 } : Config) with
    nreg := upd ztrxx 43210 0 } with he₆
  have C₆ := C₅.frame (Bw := fun r => decide (r = 43201 ∨ r = 43210))
    (exec_frameM X6 by_decide) by_decide
  obtain ⟨e₇, k₇, x₇, hk₇, hk₇', w₇, f₇, m₇⟩ := regRecLoop_exec (P := P) e₆ X6.wb_right
    (m₀ := m₃) (CA := H + 17 + 30 * K) (R := K + 1) (RT := H + 12 + 15 * K)
    (FA := H + 20 + 33 * K) (cA := cA) (cC := cC) (wR := wR) C₆.rCA C₆.rR C₆.r1
    by_rfl by_rfl C₆.rRT C₆.rFA by_omega by_omega by_omega
    ⟨by_omega, by_omega⟩ by_omega by_omega by_omega
  have C₇ := C₆.frame f₇ by_decide
  have hA₇ : e₇.nreg 43102 = A := by
    rw [f₇.1 43102 by_decide, he₆]
    show upd ztrxx 43210 0 43102 = A
    rw [upd_other _ _ _ by_norm_num, upd_other _ _ _ by_norm_num, hA₅]
  obtain ⟨mem₇, hmem₇⟩ : ∃ f : ℕ → ℕ, f = recRMem (regMem m₃ (H + 17 + 30 * K) (K + 1) cA cC wR)
      ztnlg (H + 20 + 33 * K) ztbr cA cC wR ztbr := by_grind
  rw [← hmem₇] at m₇
  have r₇ : ∀ a, (a < H + 12 + 15 * K ∨ (H + 17 + 20 * K ≤ a ∧ a < H + 17 + 30 * K)) →
      mem₇ a = m₃ a := fun a ha => by
    zudae
    rw [ite_eq_right by_omega, ite_eq_right by_omega, ite_eq_right by_omega, regMem_out _ _ _ _ _ _ by_omega]
  have rFA₇ : ∀ r, r < K + 1 → mem₇ (H + 20 + 33 * K + r) = offF cA cC r := fun r hr => by
    zudae
    grind
  have rFC₇ : ∀ r, r < K + 1 → mem₇ (H + 20 + 33 * K + ztbr + r) = offF cA cC r + cA r :=
    fun r hr => by
    zudae
    grind
  have rRT₇ : ∀ r, r < K + 1 → ∀ f, f < 5 →
      mem₇ ztihe = rtv cA cC wR ztgcs := fun r hr f hf => by
    zudae
    grind
  -- 5. the arc lists
  have z8 := Exec.constN (P := P) w₇ 43201 0 ztbg
  set e₈ : Config := { e₇ with nreg := upd e₇.nreg 43201 0 } with he₈
  have C₈ := C₇.frame (Bw := fun r => decide ztevb)
    (exec_frameM z8 by_decide) by_decide
  have hA₈ : e₈.nreg 43102 = A := by
    show upd e₇.nreg 43201 0 43102 = A
    rw [upd_other _ _ _ by_norm_num, hA₇]
  have hoffR' : H + 17 + 22 * K + offF (cntF ztxwx A) cC ztbr
      ≤ H + 17 + 26 * K := by_grind
  obtain ⟨e₉, k₉, x₉, hk₉, w₉, f₉, a1, a2, a3⟩ := arcFillLoop_exec (P := P) e₈ z8.wb_right
    (m₂ := mem₇) (A := A) (R := K + 1) (AT := H + 12 + 5 * K) (FA := H + 20 + 33 * K)
    (LT := H + 17 + 22 * K) (key := fun j => m₃ ztbdx) (cC := cC)
    hA₈ C₈.rR C₈.r1 by_rfl C₈.rAT C₈.rFA C₈.rLT
    (fun j hj => r₇ _ by_omega) hkR' (fun r hr => by_grind) by_omega by_omega
    by_omega by_omega by_omega by_omega by_omega
  rw [← hcA] at a1 a2 a3
  have C₉ := C₈.frame f₉ by_decide
  have hA₉ : e₉.nreg 43102 = A := by rw [f₉.1 43102 by_decide, hA₈]
  have hoffA : ∀ r, r < K + 1 → ∀ t, t < cA r → offF cA cC r + t < offF cA cC ztbr :=
    fun r hr t ht => by
    have := offF_succ cA cC r
    have := offF_mono cA cC ztddk
    omega
  have hoffC : ∀ r, r < K + 1 → ∀ t, t < cC r → offF cA cC r + cA r + t < offF cA cC ztbr :=
    fun r hr t ht => by
    have := offF_succ cA cC r
    have := offF_mono cA cC ztddk
    omega
  -- memory after the arc lists, outside the pointers and the arc cells
  have r₉ : ∀ a, ztfoy → (a < H + 20 + 33 * K ∨
      H + 21 + 34 * K ≤ a) → e₉.nmem a = mem₇ a := fun a h1 h2 =>
    a3 a by_omega (fun r hr t ht => by have := hoffA r hr t ht; omega)
  have hu₉ : ∀ i, i < K → e₉.nmem ztcll = uF i := fun i hi => by
    rw [r₉ _ by_omega by_omega, r₇ _ by_omega, hu i hi]
  have hv₉ : ∀ i, i < K → e₉.nmem ztclm = vF i := fun i hi => by
    rw [r₉ _ by_omega by_omega, r₇ _ by_omega, hv i hi]
  have ccC : cnt2F (fun i => e₉.nmem ztcll) (fun i => e₉.nmem ztclm)
      K = cC := by rw [cnt2F_congr hu₉ hv₉, hcC, cc2]
  -- 6. the chord lists
  have z10 := Exec.constN (P := P) w₉ 43201 0 ztbg
  set e₁₀ : Config := { e₉ with nreg := upd e₉.nreg 43201 0 } with he₁₀
  have C₁₀ := C₉.frame (Bw := fun r => decide ztevb)
    (exec_frameM z10 by_decide) by_decide
  obtain ⟨e₁₁, k₁₁, x₁₁, hk₁₁, w₁₁, f₁₁, FI⟩ := chFillLoop_exec (P := P) e₁₀ z10.wb_right
    (m₃ := e₉.nmem) (K := K) (R := K + 1) (CT := H + 12) (FC := H + 21 + 34 * K)
    (LT := H + 17 + 22 * K) (b := fun r => offF cA cC r + cA r) C₁₀.rK C₁₀.r1 C₁₀.r3
    by_rfl C₁₀.rCT C₁₀.rFC C₁₀.rLT
    (fun i hi => by rw [hu₉ i hi]; exact huR i hi) (fun i hi => by rw [hv₉ i hi]; exact hvR i hi)
    (fun r hr => by
      rw [r₉ _ by_omega by_omega, show H + 21 + 34 * K + r = H + 20 + 33 * K + ztbr + r by
        omega, rFC₇ r hr])
    (fun r r' h1 h2 => by
      rw [ccC]
      have := offF_succ cA cC r
      have := offF_mono cA cC ztmof
      omega)
    (fun r hr t ht => by rw [ccC] at ht; have := hoffC r hr t ht; omega)
    (fun r hr t ht => by rw [ccC] at ht; have := hoffC r hr t ht; omega)
    ztjwk by_omega by_omega by_rfl
  rw [ccC] at FI
  have C₁₁ := C₁₀.frame f₁₁ by_decide
  have hA₁₁ : e₁₁.nreg 43102 = A := by
    rw [f₁₁.1 43102 by_decide]
    show upd e₉.nreg 43201 0 43102 = A
    rw [upd_other _ _ _ by_norm_num, hA₉]
  -- 7. the sequence table
  have z12 := Exec.constN (P := P) w₁₁ 43201 0 ztbg
  set e₁₂ : Config := { e₁₁ with nreg := upd e₁₁.nreg 43201 0 } with he₁₂
  have C₁₂ := C₁₁.frame (Bw := fun r => decide ztevb)
    (exec_frameM z12 by_decide) by_decide
  obtain ⟨e₁₃, k₁₃, x₁₃, hk₁₃, w₁₃, f₁₃, m₁₃⟩ := seqLoop_exec (P := P) e₁₂ z12.wb_right
    (A := A) (QT := H + 17 + 20 * K)
    (by show upd e₁₁.nreg 43201 0 43102 = A; zunsv)
    C₁₂.rQT C₁₂.r1 by_rfl by_omega
  have C₁₃ := C₁₂.frame f₁₃ by_decide
  have hA₁₃ : e₁₃.nreg 43102 = A := by
    rw [f₁₃.1 43102 by_decide]
    show upd e₁₁.nreg 43201 0 43102 = A
    zunsv
  -- 8. the header
  obtain ⟨e₁₄, k₁₄, x₁₄, hk₁₄, w₁₄, f₁₄, h40003, hh1, hh2⟩ := hdrB_exec (P := P) e₁₃ w₁₃
    (K := K) (A := A) (R := K + 1) (CT := H + 12) (AT := H + 12 + 5 * K) (RT := H + 12 + 15 * K)
    (QT := H + 17 + 20 * K) (LT := H + 17 + 22 * K) (H := H) C₁₃.rH C₁₃.rK hA₁₃ C₁₃.rR C₁₃.rCT
    C₁₃.rAT C₁₃.rRT C₁₃.rQT C₁₃.rLT C₁₃.r0 C₁₃.r1 by_omega
  have X : Exec P W regPhase d e₁₄ _ :=
    .seq z0 (.seq x₁ (.seq z2 (.seq x₃ (.seq z4 (.seq x₅ (.seq X6 (.seq x₇ (.seq z8 (.seq x₉
      (.seq z10 (.seq x₁₁ (.seq z12 (.seq x₁₃ x₁₄)))))))))))))
  -- the memory of `e₁₄` through the later writes
  have back : ∀ a, (a < H ∨ H + 12 ≤ a) → (a < H + 17 + 20 * K ∨ H + 17 + 20 * K + A ≤ a) →
      (a < H + 21 + 34 * K ∨ H + 21 + 34 * K + ztbr ≤ a) →
      (∀ r, r < K + 1 → ∀ t, t < cC r → a ≠ H + 17 + 22 * K + ztodw + t) →
      e₁₄.nmem a = e₉.nmem a := fun a h1 h2 h3 h4 => by
    rw [hh2 a h1, m₁₃]
    unfold seqMem
    zufa
    exact FI.rest a h3 h4
  have notch : ∀ a, ztfoy →
      ∀ r, r < K + 1 → ∀ t, t < cC r → a ≠ H + 17 + 22 * K + ztodw + t :=
    fun a ha r hr t ht => by have := hoffC r hr t ht; omega
  have ecA : cA = cntF keyF A := by rw [hcA, ckey]
  have ecC : cC = cnt2F uF vF K := by rw [hcC, cc2]
  have ewR : wR = wmaxF keyF wF A := by rw [hwR, cwmax]
  refine ⟨e₁₄, _, X, by_omega, by_omega, w₁₄, exec_frameM X wr_regPhase, h40003, hh1,
    fun a ha => ?_, fun r hr f hf => ?_, fun r hr t ht => ?_, fun r hr t ht => ?_, fun j hj => ?_⟩
  · -- below `H` and the chord and arc tables
    zufzt
    · rw [back a by_omega by_omega by_omega by_omega, r₉ a by_omega by_omega,
        r₇ a by_omega]
    · rw [back a by_omega by_omega by_omega by_omega, r₉ a by_omega by_omega,
        r₇ a by_omega]
  · -- the region table
    rw [back _ by_omega by_omega by_omega by_omega, r₉ _ by_omega by_omega,
      rRT₇ r hr f hf, ecA, ecC, ewR]
  · -- the arc lists
    rw [← ecA] at ht
    zuini
    have hlt := hoffA r hr t ht
    rw [back _ by_omega by_omega by_omega (fun r' hr' t' ht' => by
      rcases Nat.lt_trichotomy r' r with h' | rfl | h'
      · have := offF_succ cA cC r'
        have := offF_mono cA cC (show r' + 1 ≤ r by omega)
        omega
      · omega
      · have := offF_succ cA cC r
        have := offF_mono cA cC ztmof
        omega), a2 r hr t ht, lstF_congr hkey]
  · -- the chord lists
    rw [← ecC] at ht
    zuini
    have hlt := hoffC r hr t ht
    zuguw

    rw [ite_eq_right by_omega, FI.cells r hr t ht, lst2F_congr hu₉ hv₉]
  · -- the sequence table
    zuguw

    zubek
    omega
end exec
end
end BuildRam
end Chazelle.Core
namespace Chazelle.Core
namespace BuildRam
open Machine Machine.Stmt Programs SignK NFLoc
open BuildNF (cf af chordRec arcRec gapStarts keyA wA upC dnC stk gapsB cw)
@[expose] public section
def phaseB : Stmt := .seq phaseB1 regPhase

/-- The registers phase B writes: bands `bSign`, `bBuild` and the allocator. -/
def BphaseB (r : ℕ) : Bool :=
  decide (r = 9999 ∨ ztdew ∨ (40000 ≤ r ∧ r < 50000))
theorem wr_phaseB : wrM BphaseB phaseB = true := by
  have h1 : wrM BphaseB setupB = true := wrM_of_wr (wr_mono (fun r hr => by
    simp only [BsetupB, decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false] at hr
    zundu; omega) wr_setupB)
  have h2 : wrM BphaseB lohiS = true := wrM_of_wr (wr_mono (fun r hr => by
    zucy
    zundu; omega) wr_lohiS)
  have h3 : wrM BphaseB passLoop = true := by
    have := wrM_mono (B' := BphaseB) ztez wr_passBody
    · zuofl; omega
    · cases hb : Bpass r
      · simp_all
      · zukr
        zucko

  have h4 : wrM BphaseB regPhase = true := wrM_mono (fun r hr => by
    zucqr
    zundu; omega) wr_regPhase
  simp only [phaseB, phaseB1, wrM, h1, h2, h3, h4, Bool.and_self]
section exec
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 4000000 in
/-- **Phase B writes the normal form.** -/
theorem phaseB_exec (hG : GoodEnv P) (hWn : hostWords P.n ≤ W) (c : Config)
    (hw : WordsBounded W c) {M : Model} {L : List zte} {E : List ℕ} {D T SE B H : ℕ}
    (hI : BuildNF.Input M zta L E) (hK : 0 < L.length)
    (hD : c.nreg 40000 = D) (hT : c.nreg 42000 = T) (hN : c.nreg 42001 = 2 * L.length)
    (hB : c.nreg 43001 = B) (hKr : c.nreg 43002 = L.length) (h0 : c.nreg 43010 = 0)
    (h1 : c.nreg 43011 = 1) (hSEr : c.nreg 30005 = SE) (hH : c.nreg 9999 = H)
    (hwf : ModelDescWF P H c.nmem D) (hM : ModelDescAt c.nmem D zta M)
    (hR : RecsAt c.nmem T L) (hTH : T + 8 * L.length ≤ H) (hCL : ChordListAt c.nmem B L)
    (hBH : B + 3 * L.length ≤ H) (hSE : ∀ j, j < E.length → c.nmem ztjmr = E.getD j 0)
    (hSEH : SE + E.length ≤ H) (hroom : H + sizeB L.length ≤ W) :
    ∃ c' k, Exec P W phaseB c c' k ∧ k ≤ 23604 * L.length + 200 ∧
      sizeB L.length ≤ k ∧ WordsBounded W c' ∧ FrameM BphaseB c c' ∧
      c'.nreg 40003 = H ∧ c'.nreg 9999 = H + sizeB L.length ∧
      ztiuk ∧
      NFWithin c'.nmem H ztvgr ztwni := by
  zuvu
  have hlen : ztgtw := hI.length_E
  obtain ⟨c₃, k₃, x₃, hk₃, hk₃', w₃, C₃, F, c₂, I⟩ := phaseB1_exec (P := P) hG hWn c hw hI hlen
    hD hT hN hB hKr h0 h1 hSEr hH hwf hM hR hTH hCL hBH hSE hSEH hroom
  have hgs : gapsB M zta L E E.length = gapStarts M zta L E := BuildNF.gapsB_full _ _ _ _
  set A := (gapStarts M zta L E).length with hAdef
  have hAle : A ≤ 2 * K := by
    rw [hAdef, ← hgs]; have := BuildNF.gapsB_length_le M zta L E E.length; omega
  have htake : (cw E).take E.length = cw E := by
    rw [List.take_of_length_le (by simp [cw])]
  -- the tables of the pass
  have hkey : ∀ j, j < A → c₃.nmem ztbdx = keyA M zta L E j := fun j hj => by
    have := (I.arcs j by_simp_all).1 0 by_norm_num
    rw [Nat.add_zero, hgs] at this
    tauto
  have hkR : ∀ j, j < A → keyA M zta L E j < K + 1 := fun j _ => by
    unfold keyA; rw [BuildNF.arcRec_eq]; have := BuildNF.topR_le hI ((gapStarts M zta L E).getD j 0 + 1)
    simp_all
  have hwt : ∀ j, j < A → c₃.nmem ztdkx = wA M zta L E j := fun j hj => by
    have := (I.arcs j by_simp_all).2
    rw [hgs] at this
    zukyx
  have hch : ∀ i, i < K → ∀ f, f < 5 → c₃.nmem (H + 12 + 5 * i + f) = cf (chordRec M zta L E i) f :=
    fun i hi f hf => I.chords i hi (by rw [htake]; exact BuildNF.mem_cw hI hi) f hf
  have hu : ∀ i, i < K → c₃.nmem ztcll = upC M zta L E i := fun i hi => by
    rw [hch i hi 3 by_norm_num]; rfl
  have hv : ∀ i, i < K → c₃.nmem ztclm = dnC M zta L E i := fun i hi => by
    rw [hch i hi 4 by_norm_num]; rfl
  have huR : ∀ i, i < K → upC M zta L E i < K + 1 := fun i hi => by
    have := (BuildNF.chordRec_up_le hI hi).1; unfold upC; omega
  have hvR : ∀ i, i < K → dnC M zta L E i < K + 1 := fun i hi => by
    have := (BuildNF.chordRec_up_le hI hi).2; unfold dnC; omega
  have hA₃ : c₃.nreg 43102 = A := by rw [I.r102, hgs]
  -- the region phase
  obtain ⟨c', k, x, hk, hk', w', f', h40003, T1, T2, T3, T4, T5, T6⟩ := regPhase_exec (P := P) c₃ w₃
    C₃ hA₃ hAle hkey hkR hwt hu hv huR hvR hroom
  have C' := C₃.frame f' by_decide
  have X : Exec P W phaseB c c' (k₃ + k) := .seq x₃ x
  refine ⟨c', _, X, by_omega, by unfold sizeB; omega, w', exec_frameM X wr_phaseB, h40003, C'.rA,
    fun a ha => by rw [T2 a ztbbu, I.low a ha], ?_⟩
  -- the normal form
  zubxa
  rw [C'.rA] at hm'
  have hoff : offF ztwqi ztwlv
      ztbr ≤ A + 2 * K := offF_R_le _ _ _ hkR
  have hK0 : K ≠ 0 := by_omega
  refine BuildNF.nfAt_of_tables hI hK0 (H := H) (CT := H + 12) (AT := H + 12 + 5 * K)
    (RT := H + 12 + 15 * K) (QT := H + 17 + 20 * K) (LT := H + 17 + 22 * K)
    (fun f hf => by rw [hm' _ ztchi, T1 f hf])
    (fun i hi f hf => by
      rw [hm' _ ztchi, T2 _ ztbh, hch i hi f hf])
    (fun j hj f hf => by
      rw [hm' _ ztchi, T2 _ ztbh]
      have := (I.arcs j by_grind).1 f hf
      grind)
    (fun r hr f hf => by rw [hm' _ ztchi, T3 r hr f hf])
    (fun r hr t ht => by
      zufcs
      have := offF_succ ztwqi
        ztwlv r
      have := offF_mono ztwqi
        ztwlv ztddk
      rw [hm' _ ztchi, T4 r hr t ht])
    (fun r hr t ht => by
      zufcs
      have := offF_succ ztwqi
        ztwlv r
      have := offF_mono ztwqi
        ztwlv ztddk
      rw [hm' _ ztchi, T5 r hr t ht])
    (fun j hj => by rw [hm' _ ztchi, T6 j hj])
end exec
end
end BuildRam
end Chazelle.Core
namespace Chazelle.Core
open Set
open Chazelle.Chain (sideInArc)
@[expose] public section
theorem Model.arcWt_self (M : Model) {lo hi : ℕ}
    (hc : ∀ p, p < M.W.n → ztceo) (hhi : hi ≤ M.W.n) (x : ℝ) :
    M.arcWt x x = hi - lo := by
  zuiqa
  have hset : {p : ℕ | p < M.W.n ∧ M.counted p ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      sideInArc x x ztk} = ↑(Finset.Ico lo hi) := by
    zufj
    simp only [mem_ofPred_eq, Finset.coe_Ico, mem_Ico]
    rw [Model.mem_arcEdges_iff, ite_eq_right (lt_irrefl x)]
    grind
  zuikq
namespace BuildRam
open Machine Machine.Stmt Programs SignK NFLoc

/-- The normal form for `K = 0`. -/
def zeroCase : Stmt :=
  .seq (block [.copyN 44000 9999, .constN 44030 24, .addN 9999 9999 44030]) (.seq lohiS
    (block [.constN 44033 1, .copyN 44031 44000,
      .constN 44032 0, .storeN 44031 44032, .addN 44031 44031 44033,
      .constN 44032 1, .storeN 44031 44032, .addN 44031 44031 44033,
      .storeN 44031 44032, .addN 44031 44031 44033,
      .constN 44034 12, .addN 44032 44000 44034, .storeN 44031 44032,
      .addN 44031 44031 44033,
      .storeN 44031 44032, .addN 44031 44031 44033,
      .constN 44034 17, .addN 44032 44000 44034, .storeN 44031 44032,
      .addN 44031 44031 44033,
      .constN 44034 22, .addN 44032 44000 44034, .storeN 44031 44032,
      .addN 44031 44031 44033,
      .constN 44034 23, .addN 44032 44000 44034, .storeN 44031 44032,
      .addN 44031 44031 44033,
      .copyN 44032 44000, .storeN 44031 44032, .addN 44031 44031 44033,
      .constN 44032 0, .storeN 44031 44032, .addN 44031 44031 44033,
      .copyN 44032 44000, .storeN 44031 44032, .addN 44031 44031 44033,
      .constN 44032 0, .storeN 44031 44032, .addN 44031 44031 44033,
      .storeN 44031 44032, .addN 44031 44031 44033,
      .storeN 44031 44032, .addN 44031 44031 44033,
      .storeN 44031 44032, .addN 44031 44031 44033,
      .storeN 44031 44032, .addN 44031 44031 44033,
      .storeN 44031 44032, .addN 44031 44031 44033,
      .constN 44032 1, .storeN 44031 44032, .addN 44031 44031 44033,
      .constN 44032 0, .storeN 44031 44032, .addN 44031 44031 44033,
      .storeN 44031 44032, .addN 44031 44031 44033,
      .constN 44032 1, .storeN 44031 44032, .addN 44031 44031 44033,
      .copyN 44032 44021, .storeN 44031 44032, .addN 44031 44031 44033,
      .constN 44032 0, .storeN 44031 44032, .addN 44031 44031 44033,
      .storeN 44031 44032,
      .copyN 40003 44000]))

/-- The 24 words written by `zeroCase` at `H`. -/
def zeroW (H wt : ℕ) (f : ℕ) : ℕ :=
  if f = 1 ∨ f = 2 ∨ f = 17 ∨ f = 20 then 1 else if f = 3 ∨ f = 4 then H + 12
  else if f = 5 then H + 17 else if f = 6 then H + 22 else if f = 7 then H + 23
  else if f = 8 ∨ f = 10 then H else if f = 21 then wt else 0
theorem zeroW_eq (H wt f : ℕ) (hf : f < 24) : zeroW H wt f =
    [0, 1, 1, H + 12, H + 12, H + 17, H + 22, H + 23, H, 0, H, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, wt,
      0, 0].getD f 0 := by
  unfold zeroW
  interval_cases f <;> simp

/-- **The layout for `K = 0`.** -/
theorem nfAt_zero {M : Model} {Q : Polygon} {L : List zte} {E : List ℕ}
    (hL : L.length = 0) {m : ℕ → ℕ} {H : ℕ}
    (hm : ∀ f, f < 24 → m ztjiz =
      zeroW H (BuildNF.regWt M Q L E 0) f) :
    NFAt m H ztpwl := by
  zuiwh

  have hz : ∀ f, f < 24 → m _ = zeroW H _ f := hm
  have v : ∀ f, f < 24 → m _ = [0, 1, 1, H + 12, H + 12, H + 17, H + 22, H + 23, H, 0, H, 0,
      0, 0, 0, 0, 0, 1, 0, 0, 1, BuildNF.regWt M Q [] E 0, 0, 0].getD f 0 := fun f hf => by
    rw [hz f hf, zeroW_eq _ _ _ hf]
  have e0 := v 0 by_norm_num
  have e1 : ztlyo := v 1 by_norm_num
  have e2 : ztlyo := v 2 by_norm_num
  have e4 : m _ = H + 12 := v 4 by_norm_num
  have e5 : m _ = H + 17 := v 5 by_norm_num
  have e6 : m _ = H + 22 := v 6 by_norm_num
  have e7 : m _ = H + 23 := v 7 by_norm_num
  have e9 : ztdbk := v 9 by_norm_num
  have e11 : ztdbk := v 11 by_norm_num
  have e12 : ztdbk := v 12 by_norm_num
  have e13 : ztdbk := v 13 by_norm_num
  have e14 : ztdbk := v 14 by_norm_num
  have e15 : ztdbk := v 15 by_norm_num
  have e16 : ztdbk := v 16 by_norm_num
  have e17 : ztlyo := v 17 by_norm_num
  have e18 : ztdbk := v 18 by_norm_num
  have e19 : ztdbk := v 19 by_norm_num
  have e20 : ztlyo := v 20 by_norm_num
  have e21 : m _ = BuildNF.regWt M Q [] E 0 := v 21 by_norm_num
  have e22 : ztdbk := v 22 by_norm_num
  have e23 : ztdbk := v 23 by_norm_num
  have hA : BuildNF.arcList M Q [] E = [ztgp] := by
    rfl
  have hRA : BuildNF.regArcs M Q [] E 0 = [0] := by
    rfl
  have hRC : BuildNF.regChords M Q [] E 0 = [] := by
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, fun i hi => ?_, fun j hj => ?_, fun r hr => ?_, fun j hj => ?_,
    fun k hk => ?_, fun r hr => ?_⟩
  · tauto
  · tauto
  · tauto
  · tauto
  · tauto
  · tauto
  · have hj' : ztebi := by
      have : (BuildNF.buildNF M Q [] E).arcs = BuildNF.arcList M Q [] E := rfl
      simp_all
    subst hj'
    have ha : (BuildNF.buildNF M Q [] E).arc 0 = ztgp := by
      rfl
    grind
  · have hr' : r = 0 := by simpa [BuildNF.buildNF] using hr
    subst hr'
    have hreg := (show (BuildNF.buildNF M Q [] E).region 0 =
      ⟨BuildNF.regArcs M Q [] E 0, BuildNF.regChords M Q [] E 0, BuildNF.regWt M Q [] E 0⟩ by
        unfold NF.region BuildNF.buildNF; rfl)
    rw [e5, hreg, hRA, hRC]
    simp only [Nat.mul_zero, Nat.add_zero]
    refine ztgnw
    · omega
    · omega
    · omega
    · simp only [List.length_singleton, Nat.lt_one_iff] at ht
      zucfb
      rw [e7, show H + 17 + 1 = H + 18 from rfl, e18, Nat.add_zero, Nat.add_zero,
        show H + 23 = H + 23 from rfl, e23]; rfl
    omega
  · have hj' : ztebi := by
      have : (BuildNF.buildNF M Q [] E).seq = List.range (BuildNF.arcList M Q [] E).length := rfl
      simp_all
    subst hj'
    rw [e6, Nat.add_zero, show H + 22 = H + 22 from rfl, e22]
    rfl
  · tauto
  tauto

/-- The stores of `zeroCase`. -/
def zeroStores : Stmt :=
  match zeroCase with
  | .seq _ (.seq _ s) => s
  | _ => .skip
theorem zeroCase_eq : zeroCase = .seq (block [.copyN 44000 9999, .constN 44030 24,
    .addN 9999 9999 44030]) (.seq lohiS zeroStores) := rfl
section exec
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 4000000 in
theorem zeroStores_exec (d : Config) (hw : WordsBounded W d) {H hd : ℕ}
    (hH : d.nreg 44000 = H) (hhd : d.nreg 44021 = hd) (hW : H + 24 ≤ W) :
    ∃ d' k, Exec P W zeroStores d d' k ∧ k ≤ 90 ∧ 24 ≤ k ∧ d'.nreg 40003 = H ∧
      (∀ r, (r < 44031 ∨ 44034 < r) → r ≠ 40003 → d'.nreg r = d.nreg r) ∧
      (∀ f, f < 24 → d'.nmem ztjiz = zeroW H hd f) ∧
      (∀ a, (a < H ∨ H + 24 ≤ a) → d'.nmem a = d.nmem a) := by
  unfold zeroStores zeroCase
  zubi
  exec_block
  all_goals first
    | (config_simp; simp (config := { failIfUnchanged := false }) only [hH]; omega)
    | skip
  refine ⟨by_omega, by_omega, ?_, fun r h1 h2 => ?_, fun f hf => ?_, fun a ha => ?_⟩ <;>
    config_simp
  · zummn
  · zuro
  · simp only [hH, hhd, upd_apply]
    rw [zeroW_eq _ _ _ hf]
    interval_cases f <;> ifs_omega <;> rfl
  · simp only [hH, upd_apply]
    ifs_omega
end exec
theorem regWt_zero {M : Model} {P : Polygon} {L : List zte} {E : List ℕ}
    (hL : L.length = 0) {m : ℕ → ℕ} {D : ℕ} (hM : ModelDescAt m D zta M) :
    BuildNF.regWt M zta L E 0 = hdOf m D P.n := by
  zuiwh

  have hA : BuildNF.arcList M zta [] E = [ztgp] := by
    rfl
  have hRA : BuildNF.regArcs M zta [] E 0 = [0] := by
    rfl
  obtain ⟨hc, hhi⟩ := countedIv hM
  have hlohi : loOf m D ≤ hiOf m D P.n := by unfold loOf hiOf; grind
  unfold BuildNF.regWt
  rw [hRA, hA]
  simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, List.getD_cons_zero]
  unfold BuildNF.arcW
  rw [M.arcWt_self hc hhi, hdOf_eq]
  omega
section exec
variable {P : Polygon} {W : ℕ}
theorem wr_zeroCase : wrM BphaseB zeroCase = true := by_decide
set_option maxHeartbeats 1000000 in
/-- **The empty chord list.** -/
theorem zeroCase_exec (hWn : hostWords P.n ≤ W) (c : Config) (hw : WordsBounded W c)
    {M : Model} {L : List zte} {E : List ℕ} {D H : ℕ} (hL : L.length = 0)
    (hD : c.nreg 40000 = D) (hH : c.nreg 9999 = H) (hwf : ModelDescWF P H c.nmem D)
    (hM : ModelDescAt c.nmem D zta M) (hroom : H + 24 ≤ W) :
    ∃ c' k, Exec P W zeroCase c c' k ∧ k ≤ 110 ∧ 24 ≤ k ∧ WordsBounded W c' ∧
      FrameM BphaseB c c' ∧ c'.nreg 40003 = H ∧ c'.nreg 9999 = H + 24 ∧
      ztiuk ∧
      NFWithin c'.nmem H ztvgr ztwni := by
  zuccu

  obtain ⟨c₁, k₁, x₁, hk₁, v1, v2, g₁, mm₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 44000 9999,
      .constN 44030 24, .addN 9999 9999 44030]) c c₁ k₁ ∧ k₁ = 3 ∧ c₁.nreg 44000 = H ∧
      c₁.nreg 9999 = H + 24 ∧ (∀ r, r ≠ 44000 → r ≠ 44030 → r ≠ 9999 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem := by
    exec_block
    · omega
    · simp_all
    simp_all
  zubcr
  obtain ⟨c₂, k₂, x₂, hk₂, l1, l2, l3, l4, f₂⟩ := lohiS_exec (P := P) c₁ w₁ (D := D)
    by_simp_all
    (by rw [mm₁]; exact twice_m_le hM hCW) by_omega ztnvt
    by_omega
  rw [mm₁] at l1 l2 l3
  zuboj
  obtain ⟨c₃, k₃, x₃, hk₃, hk₃', v40003, g₃, T1, T2⟩ := zeroStores_exec (P := P) c₂ w₂ (H := H)
    (hd := hdOf c.nmem D P.n) (by rw [f₂.1 _ by_decide, v1]) l2 hroom
  have X : Exec P W zeroCase c c₃ ztxee := by
    rw [zeroCase_eq]; exact .seq x₁ ztjdw
  have h9999 : c₃.nreg 9999 = H + 24 := by rw [g₃ _ by_omega by_omega, f₂.1 _ by_decide, v2]
  refine ⟨c₃, _, X, by_omega, by_omega, x₃.wb_right, exec_frameM X wr_zeroCase, v40003, h9999,
    fun a ha => by rw [T2 a ztbbu, f₂.2.2.1, mm₁], ?_⟩
  zubxa
  rw [h9999] at hm'
  apply nfAt_zero hL
  zuhgh
  rw [hm' _ by_omega, T1 f hf, regWt_zero hL hM]
end exec
end BuildRam
end
end Chazelle.Core
namespace Chazelle.Core
namespace BuildRam
open Machine Machine.Stmt Programs SignK NFLoc SortL
open BuildNF (codeLe)
@[expose] public section
def buildStmt : Stmt :=
  .seq ztoub (.ifLtN 43250 40002 (.seq phaseA phaseB) zeroCase)

/-- The constant of the cost bound. -/
def κBuild : ℕ := 70000
variable (K : ℕ) {r : ℕ}
theorem clog_two_mul_le : Nat.clog 2 ztbds ≤ Nat.clog 2 K + 1 := by
  zudwq
  have := Nat.le_pow_clog (by norm_num : 1 < 2) K
  omega
theorem sortCost_le :
    SortR.sortCost 11010 ztbds ≤ 44160 * ztwko := by
  unfold SortR.sortCost
  have h1 := clog_two_mul_le K
  have h2 : 2 * K * (Nat.clog 2 ztbds + 1) ≤ 2 * K * ztqan :=
    Nat.mul_le_mul_left _ by_omega
  grind
theorem seg_getD {m : ℕ → ℕ} {a n : ℕ} {E : List ℕ} (h : seg m a n = E) {j : ℕ} (hj : j < n) :
    m ztdgj = E.getD j 0 := by
  zuezu
  zuhav
  simp_all

/-! ## Separate write sets with natural stores -/

/-- The instruction writes a natural register in `BN` (or natural memory) or a real one in
`BR`. -/
def wrOKM2 (BN BR : ℕ → Bool) : Instr → Bool
  | .storeN _ _ => true
  | .inputSize r | .constN r _ | .copyN r _ | .addN r _ _ | .subN r _ _ | .loadN r _ => BN r
  | .constR r _ | .copyR r _ | .addR r _ _ | .subR r _ _ | .mulR r _ _ | .divR r _ _ => BR r
  | .loadR r _ | .readX r _ | .readY r _ => BR r
  | _ => false

/-- Every instruction satisfies `wrOKM2 BN BR`. -/
def wrM2 (BN BR : ℕ → Bool) : Stmt → Bool
  | .skip => true
  | .instr i => wrOKM2 BN BR i
  | .seq s t => wrM2 BN BR s && wrM2 BN BR t
  | .ifLtN _ _ t e => wrM2 BN BR t && wrM2 BN BR e
  | .ifLtR _ _ t e => wrM2 BN BR t && wrM2 BN BR e
  | .whileLtN _ _ b => wrM2 BN BR b
  | .whileLtR _ _ b => wrM2 BN BR b

/-- **The real registers outside `BR` are unchanged.** -/
theorem exec_frameM2 {P : Polygon} {W : ℕ} {BN BR : ℕ → Bool} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W s c c' k) (hs : wrM2 BN BR s = true) :
    ∀ r, BR r = false → c'.rreg r = c.rreg r := by
  induction h with
  | skip _ => exact by_simp_all
  | @instr ins c c' _ he _ _ =>
    simp only [wrM2] at hs
    cases ins <;> simp only [wrOKM2, Bool.false_eq_true] at hs <;>
      zvncw at he <;>
      (try split at he) <;> (try simp only [Option.some.injEq, reduceCtorEq] at he) <;> subst he <;>
      intro j hj <;>
      first
      | rfl
      | (zvmwf; split_ifs with hh
         · simp_all
         · rfl)
  | seq _ _ ih₁ ih₂ =>
    simp only [wrM2, Bool.and_eq_true] at hs
    zufeo
  | ifLtN_true _ _ ih =>
    zufck
  | ifLtN_false _ _ ih =>
    zufcl
  | ifLtR_true _ _ ih =>
    zufck
  | ifLtR_false _ _ ih =>
    zufcl
  | whileLtN_false _ _ => exact by_simp_all
  | whileLtN_true _ _ _ ih₁ ih₂ => exact fun r hr => (ih₂ hs r hr).trans ztefj
  | whileLtR_false _ _ => exact by_simp_all
  | whileLtR_true _ _ _ ih₁ ih₂ => exact fun r hr => (ih₂ hs r hr).trans ztefj
theorem wrM2_of_wrM {B BN BR : ℕ → Bool} (hN : ∀ r, B r = true → BN r = true)
    (hR : ∀ r, B r = true → BR r = true) {s : Stmt} (h : wrM B s = true) :
    wrM2 BN BR s = true := by
  induction s with
  | skip => rfl
  | instr i =>
    zvofk at h; simp only [wrM2]
    cases i <;> simp only [wrOKM, wrOK] at h <;> simp only [wrOKM2] <;>
      zueft
  | seq s t ihs iht =>
    zusf
  | ifLtN a b s t ihs iht =>
    zusf
  | ifLtR a b s t ihs iht =>
    zusf
  | whileLtN a b s ih => zvofk at h; zunzf
  | whileLtR a b s ih => zvofk at h; zunzf
theorem wrM2_phaseB : wrM2 BphaseB BRb phaseB = true := by
  have h1 : wrM2 BphaseB BRb setupB = true := by_decide
  have h2 : wrM2 BphaseB BRb lohiS = true := by_decide
  have h3 : wrM2 BphaseB BRb passLoop = true := by
    refine wrM2_of_wrM (B := Bpass) ztez ztez ?_
    · cases hb : Bpass r
      · simp_all
      · zukr
        zucko

    · cases hb : Bpass r
      · simp_all
      · zukr
        have hc' : ¬ (r / 10000 = 1 ∨ r / 10000 = 4) := fun h' => hc (by
          unfold BRb bandOf bSign bBuild; simp_all)
        have : ztpis := Bpass_false by_omega
        simp_all
    · zuofl; exact wr_passBody
  have h4 : wrM2 BphaseB BRb regPhase = true := wrM2_of_wrM
    (fun r hr => by
      zucqr
      zundu; omega)
    (fun r hr => by
      zucqr
      unfold BRb bandOf bSign bBuild; grind) wr_regPhase
  simp only [phaseB, phaseB1, wrM2, h1, h2, h3, h4, Bool.and_self]
theorem wrM2_zeroCase : wrM2 BphaseB BRb zeroCase = true := by_decide
theorem BphaseB_false (hr : bandOf r ∉ ({bBuild, bSort, bSign} : Finset ℕ))
    (hra : r ≠ ALLOC) : BphaseB r = false := by
  zudle
  zugzy
  simp only [BphaseB, decide_eq_false_iff_not]
  omega
theorem BRb_false (hr : bandOf r ∉ ({bBuild, bSort, bSign} : Finset ℕ)) :
    BRb r = false := by
  zudle
  unfold BRb bandOf bSign bBuild
  simp_all

/-- A register frame of phase B gives the frame of the specification. -/
theorem frame_of_frameM {c c' : Config} {k : ℕ} (F : FrameM BphaseB c c')
    (hR : ∀ r, BRb r = false → c'.rreg r = c.rreg r)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)
    (h1 : c.nreg ALLOC ≤ c'.nreg ALLOC) (h2 : c'.nreg ALLOC ≤ c.nreg ALLOC + k) :
    Frame {bBuild, bSort, bSign} c c' k :=
  ⟨fun r hr hra => F.1 r ztnjq, fun r hr => hR r ztpwg,
    hm, fun a _ => by zuowi, F.2.2.2, h1, h2⟩
section exec
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 4000000 in
/-- **The RAM part of `BuildNFSpec`.** -/
theorem buildNFRam : BuildNF.BuildNFRamSpec := by
  unfold BuildNF.BuildNFRamSpec
  refine ⟨buildStmt, κBuild, ?_⟩
  zulq
  obtain ⟨hG, hWn, hwf, M, L, hM, hgood, hlen, hBL, hCL, hok⟩ := hpre
  simp only [rd, bandReg, bBuild] at hwf hM hlen hBL hCL ⊢
  norm_num at hwf hM hlen hBL hCL ⊢
  zuvu
  zuce
  zubfv
  zukau
  have hKX : ztzos := by_grind
  have hcost' : A₀ + κBuild * ztwko ≤ W := by
    zuiva

    zubmp
    simp_all
  zullf
  zumvo
  -- the first instruction
  zuql

  · -- phase A
    have t₀ : ztmva := by
      simp_all
    obtain ⟨c₁, k₁, x₁, hk₁, w₁, F₁, d1, d2, d3, d4, d5, d6, d7, hrec, e1, e2, E, hE, hperm,
      hsort⟩ := phaseA_exec (P := P) hG hWn c₀ w₀ (M := M) (L := L) (D := c.nreg 40000)
        (B := c.nreg 40001) hwf hM hok hCL hBL ztjxd ztjxd
        by_simp_all
        ztqgj
    zuhyg
    zuijl
    zugmv
    zucuf

    zucct
    have hlow₁ : ztfaj := fun a ha => by
      zuigj
    zuyb

    have hI : ztsaq :=
      ⟨walkAx_of_goodModel hgood, hok, hperm,
        BuildNF.sorted_of_codeLe ztqyp hok hperm hsort⟩
    have hCL₁ : ztpjb := fun i hi => by
      zubxj

    obtain ⟨c₂, k₂, x₂, hk₂, hk₂', w₂, F₂, h40003, h9999, hlow, hNF⟩ := phaseB_exec (P := P) hG
      hWn c₁ w₁ (M := M) (L := L) (E := E) (D := c.nreg 40000) (T := A₀) (SE := SE)
      (B := c.nreg 40001) (H := H) hI hK d1 d2 d3 d4 d5 d6 d7 rfl rfl
      zttto hM₁ hrec by_omega hCL₁ by_omega
      ztnzf by_omega
      ztkvh
    have X : Exec P W buildStmt c c₂ _ :=
      .seq x₀ ztnak
    refine ztfzf
    · rw [hlen]; unfold costA at hk₁; unfold κBuild; nlinarith
    · zuzd

      exact ⟨E, hperm, hsort, by_omega, by rw [h40003]; exact hNF⟩
    · zuife
      · rw [F₂.1 r ztnjq, F₁.1 r hr hra, g₀ r (by
          intro h; subst h; simp [bandOf, bSort, bSign] at hr)]
      · zufmu
      · grind
      · zuigk
      · zukpj
      · show A₀ ≤ c₂.nreg 9999; omega
      · show c₂.nreg 9999 ≤ A₀ + _; omega
  · -- `K = 0`
    zuftn
    have t₀ : ztlbq := by
      simp_all
    obtain ⟨c', k, x, hk, hk', w', F', h40003, h9999, hlow, hNF⟩ := zeroCase_exec hWn c₀
      w₀ hK0
      by_simp_all by_rfl hwf hM by_nlinarith
    have X : Exec P W buildStmt c c' _ := .seq x₀ ztnah
    refine ⟨c', _, X, by zuoju; unfold κBuild; omega, fun M' L' hM' hlen' hL' => ?_, ?_⟩
    · zuzd

      refine ⟨[], by_grind, List.Pairwise.nil, by_omega, ?_⟩
      zuexp
    · zuhvm
      have R' : zteij := fun r hr =>
        (exec_frameM2 x wrM2_zeroCase r hr).trans by_simp_all
      zujey
      · show A₀ ≤ c'.nreg 9999; omega
      · show c'.nreg 9999 ≤ A₀ + _; omega
end exec
end
end BuildRam
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section

/-- **WP-C: `BuildNFSpec`.** -/
theorem buildNFOK : BuildNFSpec := BuildNF.buildNFSpec_of_ram BuildRam.buildNFRam
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Machine Machine.Stmt Programs SortL
open BuildNF (codeLe)

/-- The `LeftInside` bit of an interior descriptor at `D`. -/
def liBit (m : ℕ → ℕ) (D : ℕ) : Bool := decide (m ztef = 1)

/-- **A1: drop the augmented chords.**  Inputs (band `bDown`): the interior descriptor `D`
(`bDown 0`, word `D + 1` the `LeftInside` bit), the chord list `B` (`bDown 1`) of length `K`
(`bDown 2`), the event list `SE` (`bDown 3`, a `codeLe`-sorted permutation of the codes).
Outputs, fresh above the allocator: the kept chord list (`bDown 4`) of length `K'` (`bDown 5`)
and the renumbered event list (`bDown 6`); the kept family is the old family intersected with
`Full`, and the outputs are a valid sorted input of `BuildNFSortedSpec`.  Cost `κ (K + 1)`. -/
def DropAugSpec : Prop :=
  ∃ (s : Stmt) (κ : ℕ), Meets s {bDown}
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ rd c bDown 0 + 2 ≤ c.nreg ALLOC ∧
      (c.nmem (rd c bDown 0 + 1) = 1 ↔ Mountain.LeftInside zta) ∧
      ∃ L : List zte, rd c bDown 2 = L.length ∧
        rd c bDown 1 + 3 * L.length ≤ c.nreg ALLOC ∧ ChordListAt c.nmem ztrve L ∧
        ChordTriplesOK ztwiq zta L ∧
        rd c bDown 3 + 2 * L.length ≤ c.nreg ALLOC ∧
        (seg c.nmem ztfuc ztpu).Perm ztct ∧
        (seg c.nmem ztfuc ztpu).Pairwise
          ztbajl)
    (fun P c c' => ∀ L : List zte, rd c bDown 2 = L.length →
      ChordListAt c.nmem ztrve L →
        c.nreg ALLOC ≤ rd c' bDown 4 ∧
        rd c' bDown 4 + 3 * (DownBase.keepL ztur (Qof P).n L).length ≤
          c'.nreg ALLOC ∧
        ChordListAt c'.nmem (rd c' bDown 4)
          ztxfz ∧
        rd c' bDown 5 = (DownBase.keepL ztur (Qof P).n L).length ∧
        c.nreg ALLOC ≤ rd c' bDown 6 ∧
        rd c' bDown 6 +
            2 * (DownBase.keepL ztur (Qof P).n L).length ≤
          c'.nreg ALLOC ∧
        seg c'.nmem (rd c' bDown 6)
            ztxqm =
          DownBase.dropE ztur (Qof P).n L
            ztyfp ∧
        {x | ∃ y ∈ DownBase.keepL ztur (Qof P).n L,
            x = (recOf y).toSet ztwiq zta} =
          {x | ∃ y ∈ L, x = (recOf y).toSet ztwiq zta} ∩
            (interiorModel zta).Full ∧
        ChordTriplesOK ztwiq zta
          ztxfz ∧
        (DownBase.dropE ztur (Qof P).n L
            ztyfp).Perm
          (List.range ztxqm) ∧
        (DownBase.dropE ztur (Qof P).n L
            ztyfp).Pairwise
          (codeLe ztwiq zta
            ztxfz))
    (fun _ c => κ * (rd c bDown 2 + 1))
namespace DownBase
section exec
variable {P : Polygon} {W : ℕ}
variable (c : Config)
set_option maxHeartbeats 8000000 in
/-- The setup block. -/
theorem dSetup_exec (hw : WordsBounded W c) {D B K A₀ : ℕ}
    (h0 : c.nreg 200000 = D) (h1 : c.nreg 200001 = B) (h2 : c.nreg 200002 = K)
    (hA : c.nreg 9999 = A₀) (hDW : D + 1 ≤ W) (hAW : A₀ + 7 * K + 2 ≤ W) (hnW : P.n ≤ W) :
    ∃ c' k, Exec P W dSetup c c' k ∧ k = 22 ∧
      c'.nreg 200100 = 1 ∧ c'.nreg 200101 = 0 ∧ c'.nreg 200105 = 2 ∧
      c'.nreg 200104 = P.n - 1 ∧ c'.nreg 200106 = c.nmem ztef ∧ c'.nreg 200103 = 0 ∧
      c'.nreg 200136 = 2 * K ∧ c'.nreg 200004 = A₀ ∧ c'.nreg 200121 = A₀ + 3 * K ∧
      c'.nreg 200122 = A₀ + 5 * K ∧ c'.nreg 9999 = A₀ + 7 * K ∧
      c'.nreg 200006 = A₀ + 5 * K ∧ c'.nreg 200110 = 0 ∧ c'.nreg 200111 = B ∧
      c'.nreg 200117 = A₀ + 3 * K ∧ c'.nreg 200118 = 0 ∧ c'.nreg 200119 = A₀ ∧
      (∀ r, (r < 200000 ∨ 210000 ≤ r) → r ≠ 9999 → c'.nreg r = c.nreg r) ∧
      (∀ r, (200000 ≤ r ∧ r < 200004) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold dSetup
  exec_block
  all_goals try omega
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h0, h1, h2, hA]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun r hr hra => ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h0, h1, h2, hA]
  all_goals omega

/-- The normalised bit. -/
theorem dBit_exec (hw : WordsBounded W c) (hW : 1 ≤ W) {b : ℕ}
    (h106 : c.nreg 200106 = b) (h105 : c.nreg 200105 = 2) (h101 : c.nreg 200101 = 0)
    (h103 : c.nreg 200103 = 0) :
    ∃ c' k, Exec P W dBit c c' k ∧ k ≤ 4 ∧
      c'.nreg 200103 = (if b = 1 then 1 else 0) ∧
      (∀ r, r ≠ 200103 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  by_cases hb1 : b < 2
  · have t1 : c.nreg 200106 < c.nreg 200105 := by_omega
    by_cases hb0 : 0 < b
    · have t2 : c.nreg 200101 < c.nreg 200106 := by_omega
      have e := Exec.constN (P := P) hw 200103 1 hW
      exact ⟨_, _, .ifLtN_true t1 ztspq, by_omega,
        by simp [show b = 1 by omega], fun r hr => by_simp_all, rfl, rfl, rfl, rfl⟩
    · have t2 : ¬ c.nreg 200101 < c.nreg 200106 := by_omega
      exact ⟨c, _, .ifLtN_true t1 (.ifLtN_false t2 ztjd), by_omega,
        by simp_all, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  · have t1 : ¬ c.nreg 200106 < c.nreg 200105 := by_omega
    exact ⟨c, _, .ifLtN_false t1 ztjd, by_omega,
      by grind, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
set_option maxHeartbeats 4000000 in
/-- Between the passes. -/
theorem dMid_exec (hw : WordsBounded W c) :
    ∃ c' k, Exec P W dMid c c' k ∧ k = 4 ∧ c'.nreg 200005 = c.nreg 200118 ∧
      c'.nreg 200130 = 0 ∧ c'.nreg 200131 = c.nreg 200003 ∧ c'.nreg 200134 = c.nreg 200122 ∧
      (∀ r, r ≠ 200005 → r ≠ 200130 → r ≠ 200131 → r ≠ 200134 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold dMid
  exec_block
  all_goals try omega
  simp_all
end exec
end DownBase
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Machine Machine.Stmt Programs SignK NFLoc SortL
open BuildNF (codeLe)

/-- **L1: the normal-form build over presorted events.**  Inputs as in `BuildNFSpec` (model
descriptor `bBuild 0`, chord list `bBuild 1`, length `bBuild 2`) and the event list at
`bBuild 4`: a permutation `E` of the `2K` event codes sorted by `codeLe`, below the allocator.
Output (`bBuild 3`): a fresh handle of the normal form `buildNF M Q L E` of that very ordering,
which is a normal form with the given chords and no decomposition.  Cost `κ (K + 1)`. -/
def BuildNFSortedSpec : Prop :=
  ∃ (s : Stmt) (κ : ℕ), Meets s {bBuild, bSort, bSign}
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
      ModelDescWF P ztm c.nmem ztue ∧
      ∃ M L E, ModelDescAt c.nmem ztue zta M ∧
      GoodModel M ∧ rd c bBuild 2 = L.length ∧ rd c bBuild 1 + 3 * L.length ≤ c.nreg ALLOC ∧
      ChordListAt c.nmem ztbis L ∧ ChordTriplesOK M zta L ∧
      rd c bBuild 4 + 2 * L.length ≤ c.nreg ALLOC ∧
      seg c.nmem ztcdp ztpu = E ∧
      E.Perm ztct ∧ E.Pairwise ztwqj)
    (fun P c c' => ∀ M L, ModelDescAt c.nmem ztue zta M →
      rd c bBuild 2 = L.length → ChordListAt c.nmem ztbis L →
        c.nreg ALLOC ≤ rd c' bBuild 3 ∧
        NFWithin c'.nmem ztdph ztdo
          ztbaku ∧
        IsNF M zta ztbaku ∧
        (BuildNF.buildNF M zta L ztwsq).chords.map
          ztwma = L ∧
        (BuildNF.buildNF M zta L ztwsq).dec = [])
    (fun _ c => κ * ztpdc)
namespace DownNF
open BuildRam

/-- The record part of phase A, then the event pointer. -/
def phaseAS : Stmt := .seq setupA (.seq recLoop (.instr (.copyN 30005 40004)))

/-- **The procedure of `BuildNFSortedSpec`.** -/
def sortedStmt : Stmt :=
  .seq ztoub (.ifLtN 43250 40002 (.seq phaseAS phaseB) zeroCase)

/-- The constant of the cost bound. -/
def κSorted : ℕ := 24000
section exec
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 1000000 in
/-- **The records and the event pointer.** -/
theorem phaseAS_exec (hWn : hostWords P.n ≤ W) (c : Config)
    (hw : WordsBounded W c) {M : Model} {L : List zte} {D B SE : ℕ}
    (hL : ChordTriplesOK M zta L) (hCL : ChordListAt c.nmem B L)
    (hB : B + 3 * L.length ≤ c.nreg ALLOC) (hD : c.nreg 40000 = D) (hB' : c.nreg 40001 = B)
    (hK : c.nreg 40002 = L.length) (hSE : c.nreg 40004 = SE)
    (hroom : c.nreg ALLOC + 32 * L.length + 22 ≤ W) :
    ∃ c' k, Exec P W phaseAS c c' k ∧ k ≤ 32 * L.length + 18 ∧ WordsBounded W c' ∧
      Frame {bBuild, bSort, bSign} c c' k ∧
      c'.nreg 40000 = D ∧ c'.nreg 42000 = c.nreg ALLOC ∧ c'.nreg 42001 = 2 * L.length ∧
      c'.nreg 43001 = B ∧ c'.nreg 43002 = L.length ∧ c'.nreg 43010 = 0 ∧ c'.nreg 43011 = 1 ∧
      RecsAt c'.nmem ztm L ∧ c'.nreg 30005 = SE ∧
      c'.nreg ALLOC = c.nreg ALLOC + 10 * L.length := by
  zuce
  zuvu
  zubfv
  zufgi
  -- setup
  zugs

  -- the record loop
  have hI₁ : ztyub :=
    { i_le := by_omega, rK := r2, r0 := r3, r1 := r4, a21 := by_omega,
      a22 := by_omega, a23 := by_omega, a24 := by_omega,
      fr := by_omega, rr := rfl, rm := rfl, out := rfl,
      mem := fun a => by zuojt; unfold recMem; grind }
  have hhW : ztlzc := fun x hx => by
    have := hL.2.2.2 x hx
    zubp
    omega
  obtain ⟨c₂, k₂, x₂, hk₂, hk₂', w₂, I₂, i₂⟩ :=
    recLoop_exec (P := P) hCL hB rfl by_omega hhW w₁ hI₁ r9
  -- the event pointer
  obtain ⟨c₃, x₃, n₃, m₃, rr₃, rm₃, out₃⟩ := SortR.copyN_char (P := P) w₂ 30005 40004
  have e₃ : ∀ r, r ≠ 30005 → c₃.nreg r = c₂.nreg r := fun r hr => by zuoeh; zunaw
  have s₃ : c₃.nreg 30005 = c₂.nreg 40004 := by zuoeh; simp
  -- registers untouched by the setup and the loop
  have hc₂ : ∀ r, r < 43020 → r ≠ 43001 → r ≠ 43002 → r ≠ 43010 → r ≠ 43011 → r ≠ 42001 →
      r ≠ 42000 → r ≠ 9999 → c₂.nreg r = c.nreg r := fun r h0 h1 h2 h3 h4 h5 h6 h9 => by
    rw [I₂.fr r zthrq]
    exact fr₁ r h1 h2 h3 h4 h5 h6 by_omega by_omega h9 by_omega by_omega by_omega
      by_omega by_omega
  have X : Exec P W phaseAS c c₃ _ := .seq x₁ ztjdw
  have hA₃ : ztora := by
    rw [e₃ _ by_norm_num, I₂.fr _ by_omega, r8]
  refine ⟨c₃, _, X, by_omega, x₃.wb_right, ⟨fun r hr hra => ?_, fun r hr => ?_,
    fun a ha => ?_, fun a ha => ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hA₃⟩
  · obtain ⟨-, hr'⟩ := band_out hr
    have hra' := hra
    rw [e₃ r by_omega, I₂.fr _ by_omega]
    exact fr₁ _ by_omega by_omega by_omega by_omega by_omega by_omega
        by_omega by_omega hra' by_omega by_omega by_omega by_omega by_omega
  · rw [rr₃, I₂.rr, rr₁]
  · zumcv
    zunyp; unfold recMem; zvmyn
  · rw [rm₃, I₂.rm, rm₁]
  · rw [out₃, I₂.out, out₁]
  · show A₀ ≤ c₃.nreg 9999; omega
  · show c₃.nreg 9999 ≤ A₀ + _; omega
  · rw [e₃ _ by_norm_num, hc₂ _ by_norm_num by_norm_num by_norm_num by_norm_num
      by_norm_num by_norm_num by_norm_num by_norm_num, hD]
  · rw [e₃ _ by_norm_num, I₂.fr _ by_omega, r6]
  · rw [e₃ _ by_norm_num, I₂.fr _ by_omega, r5]
  · rw [e₃ _ by_norm_num, I₂.fr _ by_omega, r1]
  · rw [e₃ _ by_norm_num, I₂.rK]
  · rw [e₃ _ by_norm_num, I₂.r0]
  · rw [e₃ _ by_norm_num, I₂.r1]
  · refine recsAt_of fun q hq => ?_
    zunyp; unfold recMem; zungc
  grind
set_option maxHeartbeats 4000000 in
/-- **L1: `BuildNFSortedSpec`.** -/
theorem buildNFSorted : BuildNFSortedSpec := by
  refine ⟨sortedStmt, κSorted, ?_⟩
  zulq
  obtain ⟨hG, hWn, hwf, M, L, E, hM, hgood, hlen, hBL, hCL, hok, hSEL, hE, hperm, hsort⟩ := hpre
  simp only [rd, bandReg, bBuild] at hwf hM hlen hBL hCL hSEL hE ⊢
  norm_num at hwf hM hlen hBL hCL hSEL hE ⊢
  zuvu
  zuce
  set SE := c.nreg 40004 with hSEdef
  zubfv
  have hcost' : A₀ + κSorted * ztbr ≤ W := by
    zuiva

    zubmp
    simp_all
  unfold κSorted at hcost'
  have hNF := BuildNF.isNF_goodModel hgood hok hperm hsort
  -- the first instruction
  zuql

  · -- records
    have t₀ : ztmva := by
      simp_all
    zuhyg
    obtain ⟨c₁, k₁, x₁, hk₁, w₁, F₁, d1, d2, d3, d4, d5, d6, d7, hrec, hSE₁, hH₁⟩ :=
      phaseAS_exec hWn c₀ w₀ hok hCL by_omega ztjxd
        by_simp_all by_simp_all ztjxd
        by_omega
    rw [hc0A] at d2 hrec hH₁
    zugmv
    set H := c₁.nreg 9999 with hHdef
    have hHv : H = A₀ + 10 * K := hH₁
    have hlow₁ : ztfaj := fun a ha => by
      zuigj
    have hk₁' : 10 * K ≤ k₁ := by
      have := F₁.2.2.2.2.2.2; omega
    obtain ⟨hM₁, hwf₁⟩ := desc_agree hwf hM hlow₁
    zucct
    have hI : ztsaq :=
      ⟨walkAx_of_goodModel hgood, hok, hperm,
        BuildNF.sorted_of_codeLe ztqyp hok hperm hsort⟩
    have hCL₁ : ztpjb := fun i hi => by
      zubxj

    obtain ⟨c₂, k₂, x₂, hk₂, hk₂', w₂, F₂, h40003, h9999, hlow, hNFW⟩ := phaseB_exec hG
      hWn c₁ w₁ hI hK d1 d2 d3 d4 d5 d6 d7 hSE₁ rfl
      (modelDescWF_mono hwf₁ by_omega) hM₁ hrec by_omega hCL₁ by_omega
      (fun j hj => by
        rw [hlow₁ _ by_omega]
        exact seg_getD hE by_omega)
      by_omega ztchi
    have X : Exec P W sortedStmt c c₂ _ :=
      .seq x₀ ztnak
    refine ztfzf
    · rw [hlen]; unfold κSorted; omega
    · zuzd

      zugun
      exact ztiwe
    · zuife
      · rw [F₂.1 r ztnjq, F₁.1 r hr hra, g₀ r (by
          intro h; subst h; simp [bandOf, bSort, bSign] at hr)]
      · zufmu
      · grind
      · zuigk
      · zukpj
      · show A₀ ≤ c₂.nreg 9999; omega
      · show c₂.nreg 9999 ≤ A₀ + _; omega
  · -- `K = 0`
    zuftn
    have t₀ : ztlbq := by
      simp_all
    obtain ⟨c', k, x, hk, hk', w', F', h40003, h9999, hlow, hNFW⟩ := zeroCase_exec hWn
      c₀ w₀ hK0
      by_simp_all by_rfl hwf hM by_omega
    have X : Exec P W sortedStmt c c' _ := .seq x₀ ztnah
    refine ⟨c', _, X, by zuoju; unfold κSorted; omega, fun M' L' hM' hlen' hL' => ?_, ?_⟩
    · zuzd

      zugun
      exact ztiwe
    · zuhvm
      have R' : zteij := fun r hr =>
        (exec_frameM2 x wrM2_zeroCase r hr).trans by_simp_all
      zujey
      · show A₀ ≤ c'.nreg 9999; omega
      · show c'.nreg 9999 ≤ A₀ + _; omega
end exec
end DownNF

/-- **L1: `BuildNFSortedSpec`** (the procedure `DownNF.sortedStmt`). -/
theorem buildNFSorted : BuildNFSortedSpec := DownNF.buildNFSorted
end
end Chazelle.Core
namespace Chazelle.Core
namespace DrvR
open Machine Machine.Stmt
open BuildNF (codeLe)
open SortL (seg)
@[expose] public section
noncomputable def nextLvl (lam : ℕ) : ℕ := Cost.ceilBeta lam + 11

/-- The next level is smaller from `16` on. -/
theorem nextLvl_lt {lam : ℕ} (h : 16 ≤ lam) : nextLvl lam < lam :=
  Cost.ceilBeta_add_eleven_lt h

/-- **The bands the components of the down phase may write**: every phase band except the core
band (so the handles of `coreReg 0 … 2` survive every component). -/
def drvBands : Finset ℕ := phaseBands.erase bCore
theorem bCore_notin_drvBands : bCore ∉ drvBands := by
  decide
theorem bDownDrv_mem_drvBands : bDownDrv ∈ drvBands := by
  decide
theorem drvBands_subset : drvBands ⊆ phaseBands := Finset.erase_subset _ _

/-! ## The environment -/

/-- **The environment of the down-phase components**: a good input, the word bounds, the setup
record at `coreReg 0` and the up-phase data `X` at `coreReg 1` (robust below the allocator),
whose oracles serve arcs of up to `n - 1` edges. -/
def EnvD (X : MemCtx) (P : Polygon) (W : ℕ) (c : Config) : Prop :=
  GoodEnv P ∧ P.n + 3 ≤ W ∧ hostWords P.n ≤ W ∧
    Robust ztm c.nmem ztxwy ∧
    X.holds P c.nmem ztyim ztm ∧
    P.n - 1 ≤ X.cap P c.nmem ztyim
theorem coreReg_band (i : ℕ) (hi : i < 10000) : bandOf ztfgz = bCore := by
  unfold coreReg; exact bandOf_bandReg _ _ hi
theorem coreReg_ne_alloc (i : ℕ) (hi : i < 10000) : coreReg i ≠ ALLOC := by
  unfold coreReg bandReg bCore ALLOC; omega

/-- The setup record survives a change of memory at or above its bound and a larger bound. -/
theorem setup_transport {A A' : ℕ} {m m' : ℕ → ℕ} {S n : ℕ}
    (h : Robust A m (fun m => SetupAt m S n A)) (hm : ∀ a, a < A → m' a = m a) (hA : A ≤ A') :
    Robust A' m' (fun m => SetupAt m S n A') := by
  intro m'' h''
  have := h m'' (fun a ha => (h'' a (lt_of_lt_of_le ha hA)).trans zttny)
  exact ⟨this.1, this.2.1, this.2.2.1, le_trans this.2.2.2 hA⟩
variable {X : MemCtx} {cnt : ℕ → ℕ} {P : Polygon}
/-- **The environment survives every frame that does not write the core band.** -/
theorem EnvD.transport (hX : X.CapLocal) {P : Polygon} {W : ℕ} {c c' : Config}
    (h : EnvD X P W c) (h0 : c'.nreg ztcpu = c.nreg ztcpu)
    (h1 : c'.nreg ztbzv = c.nreg ztbzv) (hA : c.nreg ALLOC ≤ c'.nreg ALLOC)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) : EnvD X P W c' := by
  obtain ⟨hG, hW3, hWh, hS, hXh, hcap⟩ := h
  refine ⟨hG, hW3, hWh, ?_, ?_, ?_⟩
  · zvmzn; exact setup_transport hS hm hA
  · zuwv
    exact X.mono P _ _ _ _ hA (X.local_ P c.nmem c'.nmem _ _ ztfbu hXh)
  · rw [h1, hX P c.nmem c'.nmem _ _ hm hXh]; omega

/-- **The environment survives every frame that does not write the core band.** -/
theorem EnvD.frame (hX : X.CapLocal) {P : Polygon} {W : ℕ} {B : Finset ℕ}
    {c c' : Config} {k : ℕ} (h : EnvD X P W c) (hf : Frame B c c' k) (hB : bCore ∉ B) :
    EnvD X P W c' := by
  have hr : ∀ i, i < 10000 → c'.nreg ztfgz = c.nreg ztfgz := fun i hi =>
    hf.1 _ (by rw [coreReg_band i hi]; exact hB) (coreReg_ne_alloc i hi)
  exact h.transport hX (hr 0 by_norm_num) (hr 1 by_norm_num) hf.2.2.2.2.2.1 hf.2.2.1

/-! ## The level invariant -/

/-- **The level invariant `Inv(λ)`** (design §2), with count bound `cnt`.  Registers of band
`bDownDrv`: `1` the interior model descriptor, `2` the chord list `L`, `3` its length `K`, `4`
the event list `E`, `5` the normal form `N = buildNF I Q L E`; everything robust below the
allocator.  `E` is a `codeLe`-sorted permutation of the `2K` event codes; the triples are
admissible, distinct and attached (`ChordTriplesOK`).  With `S = N.F I Q`:
(I1) `I.DegLe S 4`; (I2) `I.Semigranular S (2^(⌈βλ⌉+12))`;
(I3) `K 2^⌈βλ⌉ ≤ cnt λ (2^p + 2^⌈βλ⌉)` with `p = topGrade n`. -/
def InvAt (cnt : ℕ → ℕ) (P : Polygon) (c : Config) (lam : ℕ) : Prop :=
  rd c bDownDrv 1 + 6 ≤ c.nreg ALLOC ∧
    Robust ztm c.nmem
      ztbang ∧
    ∃ (L : List zte) (E : List ℕ),
      rd c bDownDrv 3 = L.length ∧
      rd c bDownDrv 2 + 3 * L.length ≤ c.nreg ALLOC ∧
      Robust ztm c.nmem ztyqo ∧
      rd c bDownDrv 4 + 2 * L.length ≤ c.nreg ALLOC ∧
      Robust ztm c.nmem ztyew ∧
      ChordTriplesOK ztwiq zta L ∧
      E.Perm ztct ∧
      E.Pairwise ztbajl ∧
      NFWithin c.nmem ztrvg ztm
        ztbaja ∧
      (interiorModel zta).DegLe
        ztbajd 4 ∧
      (interiorModel zta).Semigranular
        ztbajd
        ztxuo ∧
      L.length * 2 ^ Cost.ceilBeta lam ≤
        cnt lam * ztfmt

/-- **The invariant survives** when the registers `1 … 5` of `bDownDrv` are kept, the memory
below the allocator is kept, and the allocator is not lowered. -/
theorem InvAt.transport {c c' : Config} {lam : ℕ}
    (h : InvAt cnt P c lam) (hr : ∀ i, 1 ≤ i → i ≤ 5 → rd c' bDownDrv i = rd c bDownDrv i)
    (hA : c.nreg ALLOC ≤ c'.nreg ALLOC) (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) :
    InvAt cnt P c' lam := by
  obtain ⟨hD, hDa, L, E, hK, hLb, hLa, hEb, hEa, hok, hperm, hsort, hN, hdeg, hwt, hcnt⟩ := h
  have h1 := hr 1 le_rfl by_norm_num
  refine ⟨by_omega, by zvmwp; exact (hDa.transport hm).mono hA, L, E, ?_, ?_, ?_, ?_, ?_, hok, hperm, hsort, ?_,
    hdeg, hwt, hcnt⟩
  · simp_all
  · grind
  · rw [hr 2 by_norm_num by_norm_num]; exact (hLa.transport hm).mono hA
  · grind
  · rw [hr 4 by_norm_num by_norm_num]; exact (hEa.transport hm).mono hA
  · rw [hr 5 by_norm_num by_norm_num]; exact (hN.transport hm).mono hA

/-- (I3) as a bound on `K`: `K ≤ cnt λ (2^p + 2^⌈βλ⌉) / 2^⌈βλ⌉`. -/
theorem InvAt.len_le {c : Config} {lam : ℕ}
    (h : InvAt cnt P c lam) :
    rd c bDownDrv 3 ≤
      cnt lam * ztfmt / 2 ^ Cost.ceilBeta lam := by
  obtain ⟨-, -, L, E, hK, -, -, -, -, -, -, -, -, -, -, hcnt⟩ := h
  rw [hK, Nat.le_div_iff_mul_le by_positivity]
  omega

/-! ## The component contracts -/

/-- **D2, the transition** (design §4.1; math `Trans.transition`): from the input of
`DownPhaseSpec` (with the environment), establish `Inv(p)`, `p = topGrade n`, in `κ (n + 1)`
steps, writing only `drvBands`. -/
def TransSpec (X : MemCtx) (cnt : ℕ → ℕ) : Prop :=
  ∃ (s : Stmt) (κ : ℕ), Meets s drvBands
    (fun P W c => EnvD X P W c ∧
      ∃ C N, TopChain P C ∧ Robust ztm c.nmem ztijq ∧
        IsCanonicalNF ztc zta N ztmow 4)
    (fun P _ c' => InvAt cnt P c' ztcdz)
    ztwqk

/-- **One level of the down phase** (design §4.2–4.3: regions, leaves, merges, extraction,
splice, rebuild, restoration rounds): from `Inv(λ)` with `16 ≤ λ ≤ p` and `n₀ ≤ n` (λ in
register `0` of `bDownDrv`), establish `Inv(⌈βλ⌉ + 11)`, keeping register `0`, in
`κ (K + 1) (lemma41Nat (⌈βλ⌉ + 11) + 1)` steps (`K` the chord count, register `3`): a constant
number of Lemma 4.1 / merge budgets per region, and `K + 1` regions. -/
def LevelSpec (X : MemCtx) (cnt : ℕ → ℕ) (n₀ : ℕ) : Prop :=
  ∃ (s : Stmt) (κ : ℕ), Meets s drvBands
    (fun P W c => EnvD X P W c ∧ n₀ ≤ P.n ∧ 16 ≤ rd c bDownDrv 0 ∧
      rd c bDownDrv 0 ≤ topGrade P.n ∧ InvAt cnt P c ztxo)
    (fun P c c' => rd c' bDownDrv 0 = rd c bDownDrv 0 ∧
      InvAt cnt P c' ztbail)
    (fun _ c => κ * ztbaoe)

/-- **D9, the base case** (design §4.4: region brute force, splice, `dropAug`,
`buildNFSorted`): from `Inv(λ)` with `λ < 16` or `n < n₀`, write in register `6` of `bDownDrv`
the handle of a normal form of the full interior visibility map of `Q`, robust below the
allocator, in `κ (n + 1)` steps. -/
def BaseSpec (X : MemCtx) (cnt : ℕ → ℕ) (n₀ : ℕ) : Prop :=
  ∃ (s : Stmt) (κ : ℕ), Meets s drvBands
    (fun P W c => EnvD X P W c ∧
      ∃ lam, lam ≤ topGrade P.n ∧ (lam < 16 ∨ P.n < n₀) ∧ InvAt cnt P c lam)
    (fun P _ c' => ∃ N, Robust ztdo c'.nmem (fun m => NFAt m (rd c' bDownDrv 6) N) ∧
      IsNF ztwiq zta N ∧
      N.F ztwiq zta = (interiorModel zta).Full)
    ztwqk
end
end DrvR
end Chazelle.Core
namespace Chazelle.Core
namespace DrvR
open Finset
@[expose] public section
noncomputable def pot (f : ℕ → ℕ) (lam : ℕ) : ℕ :=
  if _h : 16 ≤ lam then f lam + pot f ztmc else 0
termination_by lam
decreasing_by exact nextLvl_lt _h
variable {f : ℕ → ℕ} {lam : ℕ} {cnt : ℕ → ℕ}
theorem pot_of_le (h : 16 ≤ lam) :
    pot f lam = f lam + pot f ztmc := by
  rw [pot, dite_eq_left h]
theorem pot_of_lt (h : lam < 16) : pot f lam = 0 := by
  rw [pot, dite_eq_right by_omega]

/-- **The potential is at most the sum of the per-level bounds** over `j ≤ λ`. -/
theorem pot_le_sum (f : ℕ → ℕ) (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (L₀ : ℕ)
    (hf : ∀ j, 16 ≤ j → j ≤ L₀ → (f j : ℝ) ≤ B j) :
    ∀ lam, lam ≤ L₀ → (pot f lam : ℝ) ≤ ∑ j ∈ range zttrt, B j := by
  intro lam
  induction lam using Nat.strong_induction_on with
  | _ lam ih =>
    intro hl
    by_cases h16 : 16 ≤ lam
    · rw [pot_of_le h16]
      have hlt := nextLvl_lt h16
      have hih := ih ztmc hlt by_omega
      have hsub : ∑ j ∈ range (nextLvl lam + 1), B j ≤ ∑ j ∈ range lam, B j :=
        Finset.sum_le_sum_of_subset_of_nonneg ztmbc
          (fun j _ _ => hB j)
      rw [Finset.sum_range_succ]
      grind
    · rw [pot_of_lt by_omega]
      push_cast
      exact Finset.sum_nonneg (fun j _ => hB j)

/-! ## The budget of one level -/

/-- The bound on the chord count at level `λ` given by (I3):
`Kb λ = cnt λ (2^p + 2^⌈βλ⌉) / 2^⌈βλ⌉`. -/
noncomputable def kBound (cnt : ℕ → ℕ) (p lam : ℕ) : ℕ :=
  cnt lam * ztdyg / 2 ^ Cost.ceilBeta lam

/-- **The budget of one level** (with the driver's bookkeeping in the constant `K₁`):
`K₁ (Kb λ + 1) (lemma41Nat (μ λ) + 1)`. -/
noncomputable def lvlBudget (K₁ : ℕ) (cnt : ℕ → ℕ) (p lam : ℕ) : ℕ :=
  K₁ * ((kBound cnt p lam + 1) * ztwuz)

/-- `lemma41Nat g + 1 ≤ 4 · lemma41Bound g` for `g ≥ 2`. -/
theorem lemma41Nat_add_one_le {g : ℕ} (hg : 2 ≤ g) :
    (lemma41Nat g : ℝ) + 1 ≤ 4 * Cost.lemma41Bound g := by
  unfold lemma41Nat
  rw [Cost.lemma41Bound_eq]
  have hc : (1 : ℝ) ≤ Nat.clog 2 g := by
    have : ztrzx := Nat.clog_pos by_norm_num by_omega
    simp_all
  have hg' : (2 : ℝ) ≤ g := by_simp_all
  have hq : (1 : ℝ) ≤ (2 : ℝ) ^ ztflp :=
    Real.one_le_rpow by_norm_num by_positivity
  have e : (74 : ℝ) / 75 * g = (74 / 75 : ℝ) * g := by_norm_num
  zui
  set x : ℝ := (2 : ℝ) ^ ztflp with hx
  have hx0 : 0 ≤ (g : ℝ) ^ 2 * zttu * x := by_positivity
  have hceil := Nat.ceil_lt_add_one hx0
  have hg2 : (4 : ℝ) ≤ (g : ℝ) ^ 2 := by_nlinarith
  have h1 : (g : ℝ) ^ 2 * zttu * x ≤
      2 * ((g : ℝ) ^ 2 * (Nat.clog 2 g : ℝ) * x) := by
    have : (g : ℝ) ^ 2 * x ≥ 0 := by_positivity
    nlinarith
  have h2 : (1 : ℝ) ≤ (g : ℝ) ^ 2 * (Nat.clog 2 g : ℝ) * x := by
    have h3 : (1 : ℝ) ≤ (g : ℝ) ^ 2 * (Nat.clog 2 g : ℝ) := by_nlinarith
    nlinarith
  linarith

/-- `Kb λ + 1 ≤ (C + 1)(2^p / 2^⌈βλ⌉ + 1)` when `cnt λ ≤ C`. -/
theorem kBound_add_one_le {C p lam : ℕ} (hc : cnt lam ≤ C) :
    (kBound cnt p lam : ℝ) + 1 ≤
      ((C : ℝ) + 1) * ztfxq := by
  unfold kBound
  have h2 : (0 : ℝ) < (2 : ℝ) ^ Cost.ceilBeta lam := by_positivity
  have hdiv := Nat.cast_div_le (α := ℝ) (m := cnt lam * ztdyg)
    (n := 2 ^ Cost.ceilBeta lam)
  push_cast at hdiv
  have e : (cnt lam : ℝ) * ((2 : ℝ) ^ p + (2 : ℝ) ^ Cost.ceilBeta lam) /
      (2 : ℝ) ^ Cost.ceilBeta lam = (cnt lam : ℝ) * ztfxq := by
    field_simp
  zvmwe at hdiv
  have hC : (cnt lam : ℝ) ≤ C := by_simp_all
  have hy : (1 : ℝ) ≤ (2 : ℝ) ^ p / (2 : ℝ) ^ Cost.ceilBeta lam + 1 := by
    have : (0 : ℝ) ≤ (2 : ℝ) ^ p / (2 : ℝ) ^ Cost.ceilBeta lam := by_positivity
    linarith
  have := mul_le_mul_of_nonneg_right hC (by linarith : (0 : ℝ) ≤
    (2 : ℝ) ^ p / (2 : ℝ) ^ Cost.ceilBeta lam + 1)
  nlinarith

/-- The per-level constant `4096 (C + 1) (4 K₁)`. -/
def lvlConst (C K₁ : ℕ) : ℕ := 4096 * ztsvu * (4 * K₁)

/-- **The budget of one level against Lemma 4.2's overhead**: for `16 ≤ λ ≤ p`,
`f λ ≤ lvlConst C K₁ · 2^p · downOverhead λ` (`Cost.downStep_cost_le`). -/
theorem lvlBudget_le {C K₁ p lam : ℕ} (hc : cnt lam ≤ C) (h16 : 16 ≤ lam)
    (hp : lam ≤ p) :
    (lvlBudget K₁ cnt p lam : ℝ) ≤ (lvlConst C K₁ : ℝ) * ((2 : ℝ) ^ p * Cost.downOverhead lam) := by
  have hR := kBound_add_one_le (p := p) hc
  have hl := lemma41Nat_add_one_le (g := nextLvl lam) (by unfold nextLvl; omega)
  have hK0 : (0 : ℝ) ≤ (C : ℝ) + 1 := by_positivity
  have hk0 : (0 : ℝ) ≤ 4 * (K₁ : ℝ) := by_positivity
  have hstep := Cost.downStep_cost_le hK0 hk0 (by omega : 14 ≤ lam) hp hR
  unfold lvlBudget lvlConst
  push_cast
  have hR0 : (0 : ℝ) ≤ (kBound cnt p lam : ℝ) + 1 := by_positivity
  have hK1 : (0 : ℝ) ≤ (K₁ : ℝ) := by_positivity
  have hn : nextLvl lam = Cost.ceilBeta lam + 11 := rfl
  zvmxq at hl ⊢
  have hmain : (K₁ : ℝ) * (ztkpk *
      ((lemma41Nat ztblw : ℝ) + 1)) ≤
      ztkpk * (4 * (K₁ : ℝ) * Cost.lemma41Bound ztblw) := by
    have := mul_le_mul_of_nonneg_left hl (mul_nonneg hK1 hR0)
    grind
  grind

/-- The constant of the whole level loop: `4500³ · 3000 · lvlConst C K₁`. -/
def potConst (C K₁ : ℕ) : ℕ := 4500 ^ 3 * 3000 * lvlConst C K₁

/-- **The cost of the level loop is linear**: `pot f λ ≤ potConst C K₁ · 2^p` for `λ ≤ p`, when
`cnt` is bounded by `C`. -/
theorem pot_lvlBudget_le {C : ℕ} (hc : ∀ l, cnt l ≤ C) (K₁ p lam : ℕ)
    (hl : lam ≤ p) : pot ztlrb lam ≤ potConst C K₁ * 2 ^ p := by
  have hB : ∀ j, (0 : ℝ) ≤ (lvlConst C K₁ : ℝ) * ((2 : ℝ) ^ p * Cost.downOverhead j) :=
    fun j => mul_nonneg by_positivity (mul_nonneg by_positivity (Cost.downOverhead_nonneg j))
  have h1 := pot_le_sum ztlrb _ hB p
    (fun j h16 hj => lvlBudget_le (hc j) h16 hj) lam hl
  rw [← Finset.mul_sum, ← Finset.mul_sum] at h1
  have h2 := Cost.sum_downOverhead_le zttrt
  have h3 : (pot ztlrb lam : ℝ) ≤ (potConst C K₁ : ℝ) * (2 : ℝ) ^ p := by
    unfold potConst
    push_cast
    have h0 : (0 : ℝ) ≤ (lvlConst C K₁ : ℝ) * (2 : ℝ) ^ p := by_positivity
    have := mul_le_mul_of_nonneg_left h2 h0
    nlinarith
  exact_mod_cast h3
end
end DrvR
end Chazelle.Core
namespace Chazelle.Core
namespace DrvR
open Machine Machine.Stmt Programs
@[expose] public section
def guardS (n₀ : ℕ) : Stmt :=
  .seq (block [.inputSize 210009, .constN 210010 n₀, .constN 210008 15, .constN 210007 0])
    (.ifLtN 210009 210010 .skip (.instr (.copyN 210007 210000)))

/-- `λ := p`, read from the setup record (`m (S + 1)`). -/
def lamP : Stmt :=
  block [.copyN 210011 230000, .constN 210012 1, .addN 210013 210011 210012, .loadN 210000 210013]

/-- `λ := ⌈λ/5⌉ + 11`, read from the table `m (S + p + 4 + λ) = ⌈λ/5⌉` of the setup record. -/
def lamNext : Stmt :=
  block [.copyN 210011 230000, .constN 210012 1, .addN 210013 210011 210012,
    .loadN 210014 210013, .addN 210013 210011 210014, .constN 210012 4,
    .addN 210013 210013 210012, .addN 210013 210013 210000, .loadN 210000 210013,
    .constN 210012 11, .addN 210000 210000 210012]

/-- The body of the level loop. -/
def levelBody (sL : Stmt) (n₀ : ℕ) : Stmt := .seq sL (.seq lamNext ztqos)

/-- The level loop. -/
def levelLoop (sL : Stmt) (n₀ : ℕ) : Stmt := .whileLtN 210008 210007 zttsf

/-- **The down phase** from its components: transition `sT`, one level `sL`, base `sB`. -/
def downS (sT sL sB : Stmt) (n₀ : ℕ) : Stmt :=
  .seq sT (.seq (.seq lamP ztqos)
    (.seq (levelLoop sL n₀) (.seq sB (.instr (.copyN 230003 210006)))))

/-! ## Registers -/
theorem rd_drv (c : Config) (i : ℕ) : rd c bDownDrv i = c.nreg ztjfn := rfl
variable {c c' : Config} {k : ℕ}
/-- A configuration change writing only band-`21` registers is a frame of `{bDownDrv}`. -/
theorem frame_drv
    (hr : ∀ r, (r < 210000 ∨ 220000 ≤ r) → c'.nreg r = c.nreg r) (hm : c'.nmem = c.nmem)
    (hrr : c'.rreg = c.rreg) (hrm : c'.rmem = c.rmem) (ho : c'.output = c.output) :
    Frame {bDownDrv} c c' k := by
  zucgg
  refine ⟨fun r hr' _ => hr r ?_, fun r _ => by zvnhk, fun a _ => by zvmwi,
    fun a _ => by zvnmc, ho, by_omega, by_omega⟩
  simp only [Finset.mem_singleton, bandOf, bDownDrv] at hr'
  omega

/-- The frame of the final copy into `coreReg 3`. -/
theorem frame_core
    (hr : ∀ r, r ≠ 230003 → c'.nreg r = c.nreg r) (hm : c'.nmem = c.nmem)
    (hrr : c'.rreg = c.rreg) (hrm : c'.rmem = c.rmem) (ho : c'.output = c.output) :
    Frame {bCore} c c' k := by
  zucgg
  refine ⟨fun r hr' _ => hr r ?_, fun r _ => by zvnhk, fun a _ => by zvmwi,
    fun a _ => by zvnmc, ho, by_omega, by_omega⟩
  simp only [Finset.mem_singleton, bandOf, bCore] at hr'
  omega

/-! ## The pieces -/
section exec
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 4000000 in
/-- **The guard.** -/
theorem guardS_exec (n₀ : ℕ) (c : Config) (hw : WordsBounded W c) (hn₀ : n₀ + 15 ≤ W)
    (hn : P.n ≤ W) :
    ∃ c' k, Exec P W ztqos c c' k ∧ k ≤ 7 ∧
      c'.nreg 210007 = ztlqd ∧ c'.nreg 210008 = 15 ∧
      ztcqw ∧
      (∀ r, 210001 ≤ r → r ≤ 210006 → c'.nreg r = c.nreg r) ∧ c'.nreg 210000 = c.nreg 210000 ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold guardS
  refine spec_seq ?_
  exec_block
  zubqj
  by_cases h : P.n < n₀
  · zuek
    zurc
    refine ztdrb
    · simp_all
    zuit
  · zudx
    refine spec_instr (Exec.copyN ‹_› 210007 210000) fun _ => ?_
    refine ztdrb
    · simp_all
    zuit
variable (c : Config)
set_option maxHeartbeats 4000000 in
/-- **`λ := p`.** -/
theorem lamP_exec (hw : WordsBounded W c) {S : ℕ} (hS : c.nreg 230000 = S)
    (hSW : S + 1 ≤ W) :
    ∃ c' k, Exec P W lamP c c' k ∧ k = 4 ∧ c'.nreg 210000 = c.nmem ztbgu ∧
      ztcqw ∧
      ztgsc ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lamP
  exec_block
  all_goals try omega
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, hS]; omega)
  refine ztehb
  all_goals simp (disch := omega) only [Machine.upd_same, Machine.upd_other, hS]
set_option maxHeartbeats 4000000 in
/-- **`λ := ⌈λ/5⌉ + 11`** from the setup table. -/
theorem lamNext_exec (hw : WordsBounded W c) {S p lam : ℕ}
    (hS : c.nreg 230000 = S) (hp : c.nmem ztbgu = p) (hl : c.nreg 210000 = lam)
    (hW1 : S + p + 4 + lam ≤ W) (hW2 : c.nmem ztnow + 11 ≤ W) :
    ∃ c' k, Exec P W lamNext c c' k ∧ k = 11 ∧
      c'.nreg 210000 = c.nmem ztnow + 11 ∧
      ztcqw ∧
      ztgsc ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lamNext
  exec_block
  all_goals try omega
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, hS, hp, hl]; omega)
  refine ztehb
  all_goals simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, hS, hp, hl]
end exec
end
end DrvR
end Chazelle.Core
namespace Chazelle.Core
namespace DrvR
@[expose] public section
open Machine

/-- **The contract of one piece (D4).**  For a sub-chain `C = ⟨H.poly Q, s, m⟩` of a well-formed,
regular, simple host `H` (at most `64` items): a model descriptor of `chainModel C` and a
`γ`-canonical normal form of degree cap `D` of it, fresh and robust below the new allocator.
Leaves need `γ ≥ 2 γ'_μ` and the up-phase data with at least `μ` grades; connectors need
`γ ≥ 2 m`.  Cost `κ (lemma41Nat μ + 1)`. -/
def PieceSpec (O : OracleIface) : Prop :=
  ∃ (sp : Stmt) (κ : ℕ), Meets sp drvBands
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
      (gradeCtx O).holds P c.nmem ztcuu ztm ∧
      4 ≤ c.nreg 218006 ∧ 1 ≤ c.nreg 218002 ∧ c.nreg 218003 ≤ 1 ∧
      ∃ H : Host, Robust ztm c.nmem ztfbw ∧
        c.nreg 218000 + 3 * H.length + 4 ≤ c.nreg ALLOC ∧
        H.length ≤ 64 ∧ HostWF (Qof P).n H ∧ HostRegular (Qof P).n H ∧
        (H.poly zta).Simple ∧
        c.nreg 218001 + c.nreg 218002 + 1 ≤ (H.pts (Qof P).n).length ∧
        (c.nreg 218003 = 1 →
          c.nreg 218002 ≤ 2 ^ c.nreg 218005 ∧ c.nreg 218005 ≤ c.nmem ztcuu ∧
          c.nreg 218004 + c.nreg 218002 + 1 ≤ (Qof P).n ∧
          2 * gradeGran ztmgb ≤ c.nreg 218007 ∧
          ∀ k, k ≤ c.nreg 218002 →
            (H.pts (Qof P).n).getD zthuq ztga = .vtx zthur) ∧
        ztghf)
    (fun P c c' =>
      ztexc ∧
      c.nreg ALLOC ≤ c'.nreg 218010 ∧ c.nreg ALLOC ≤ c'.nreg 218011 ∧
      ModelDescWF P ztdo c'.nmem ztmff ∧
      ∀ (H : Host) (C : Chain), HostAt c.nmem ztjrx H → C.P = H.poly zta →
        C.s = c.nreg 218001 → C.m = c.nreg 218002 →
        Robust ztdo c'.nmem
          (fun m => m ztmff = 0 ∧
            ChainDescAt m zthud zta H C ∧
            m zthud = c.nreg 218000) ∧
        ∃ N, NFWithin c'.nmem ztqhb ztdo N ∧
          IsCanonicalNF ztc zta N zthus ztvia)
    ztyqj
open Machine.Stmt Programs BuildRam
def plChBody : Stmt :=
  .seq (.ifLtN 219002 219014 (.instr (.copyN 219015 219002)) (.instr (.copyN 219015 219014)))
    (block [.storeN 219016 219012, .addN 219021 219016 219018, .storeN 219021 219015,
      .addN 219021 219021 219018, .storeN 219021 219013, .addN 219016 219016 219020,
      .addN 219004 219004 219018, .addN 219012 219012 219015, .addN 219013 219013 219015,
      .subN 219014 219014 219015])

/-- **The chunk loop.** -/
def plCh : Stmt := .whileLtN 219017 219014 plChBody

/-- The registers the chunk loop writes. -/
def Bch (r : ℕ) : Bool :=
  decide (r = 219004) || decide (219012 ≤ r ∧ r ≤ 219016) || decide zttxs
theorem wrM_plChBody : wrM Bch plChBody = true := by_decide

/-- One piece off the front. -/
theorem chunks_cons {C s a L : ℕ} (hC : 1 ≤ C) (hL : 1 ≤ L) :
    chunks C s a L = (s, min C L, a) :: chunks C (s + min C L) (a + min C L) (L - min C L) := by
  zujsb
  · rw [chunks_le by_omega zteg, min_eq_right h, Nat.sub_self, chunks_zero]
  · rw [chunks_gt by_omega by_omega by_omega, min_eq_left by_omega]
section exec
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 1000000 in
theorem plChBody_exec (d : Config) (hw : WordsBounded W d) {C L s a k ptr : ℕ}
    (h02 : d.nreg 219002 = C) (h14 : d.nreg 219014 = L) (h12 : d.nreg 219012 = s)
    (h13 : d.nreg 219013 = a) (h16 : d.nreg 219016 = ptr) (h04 : d.nreg 219004 = k)
    (h18 : d.nreg 219018 = 1) (h20 : d.nreg 219020 = 3)
    (hW1 : ptr + 3 ≤ W) (hW2 : s + L ≤ W) (hW3 : a + L ≤ W) (hW4 : k + 1 ≤ W) :
    ∃ d' j, Exec P W plChBody d d' j ∧ j ≤ 13 ∧
      d'.nreg 219012 = s + min C L ∧ d'.nreg 219013 = a + min C L ∧
      d'.nreg 219014 = L - min C L ∧ d'.nreg 219016 = ptr + 3 ∧ d'.nreg 219004 = k + 1 ∧
      d'.nmem = upd (upd (upd d.nmem ptr s) (ptr + 1) (min C L)) (ptr + 2) a ∧
      FrameM Bch d d' := by
  obtain ⟨d₁, j₁, e₁, hj₁, v15, g₁, m₁⟩ : ∃ d₁ j₁, Exec P W
      (.ifLtN 219002 219014 (.instr (.copyN 219015 219002)) (.instr (.copyN 219015 219014)))
      d d₁ j₁ ∧ j₁ ≤ 3 ∧ d₁.nreg 219015 = min C L ∧ (∀ r, r ≠ 219015 → d₁.nreg r = d.nreg r) ∧
      d₁.nmem = d.nmem := by
    by_cases h : C < L
    · refine ⟨_, _, .ifLtN_true (by omega) (Exec.copyN (P := P) hw 219015 219002),
        by omega, ?_, fun r hr => by simp_all, rfl⟩
      simp only [Machine.upd_same, h02]; omega
    · refine ⟨_, _, .ifLtN_false (by omega) (Exec.copyN (P := P) hw 219015 219014),
        by omega, ?_, fun r hr => by simp_all, rfl⟩
      simp_all
  have w₁ := e₁.wb_right
  have a12 : d₁.nreg 219012 = s := by simp_all
  have a13 : d₁.nreg 219013 = a := by simp_all
  have a14 : d₁.nreg 219014 = L := by simp_all
  have a16 : d₁.nreg 219016 = ptr := by simp_all
  have a04 : d₁.nreg 219004 = k := by simp_all
  have a18 : d₁.nreg 219018 = 1 := by simp_all
  have a20 : d₁.nreg 219020 = 3 := by simp_all
  have hmin : min C L ≤ L := min_le_right _ _
  obtain ⟨d₂, j₂, e₂, hj₂, b12, b13, b14, b16, b04, bm⟩ : ∃ d₂ j₂, Exec P W
      (block [.storeN 219016 219012, .addN 219021 219016 219018, .storeN 219021 219015,
        .addN 219021 219021 219018, .storeN 219021 219013, .addN 219016 219016 219020,
        .addN 219004 219004 219018, .addN 219012 219012 219015, .addN 219013 219013 219015,
        .subN 219014 219014 219015]) d₁ d₂ j₂ ∧ j₂ = 10 ∧
      d₂.nreg 219012 = s + min C L ∧ d₂.nreg 219013 = a + min C L ∧
      d₂.nreg 219014 = L - min C L ∧ d₂.nreg 219016 = ptr + 3 ∧ d₂.nreg 219004 = k + 1 ∧
      d₂.nmem = upd (upd (upd d₁.nmem ptr s) (ptr + 1) (min C L)) (ptr + 2) a := by
    exec_block
    all_goals try (config_simp; (try simp only [a12, a13, a14, a16, a04, a18, a20, v15]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp <;>
      (try simp only [a12, a13, a14, a16, a04, a18, a20, v15])
  refine ⟨d₂, j₁ + j₂, .seq e₁ e₂, by omega, b12, b13, b14, b16, b04, by simp_all, ?_⟩
  exact exec_frameM (.seq e₁ e₂) wrM_plChBody

/-- **The chunk loop** writes the pieces of the segment as triples at the pointer. -/
theorem plCh_exec {C : ℕ} (hC : 1 ≤ C) : ∀ (L : ℕ) (d : Config) (s a k ptr : ℕ),
    WordsBounded W d → d.nreg 219002 = C → d.nreg 219014 = L → d.nreg 219012 = s →
    d.nreg 219013 = a → d.nreg 219016 = ptr → d.nreg 219004 = k → d.nreg 219017 = 0 →
    d.nreg 219018 = 1 → d.nreg 219020 = 3 → s + L ≤ W → a + L ≤ W →
    ptr + 3 * (chunks C s a L).length ≤ W → k + (chunks C s a L).length ≤ W →
    ∃ d' j, Exec P W plCh d d' j ∧ j ≤ 15 * (chunks C s a L).length + 2 ∧
      d'.nreg 219016 = ptr + 3 * (chunks C s a L).length ∧
      d'.nreg 219004 = k + (chunks C s a L).length ∧
      ChordListAt d'.nmem ptr ztjsu ∧
      (∀ x, (x < ptr ∨ ptr + 3 * (chunks C s a L).length ≤ x) → d'.nmem x = d.nmem x) ∧
      FrameM Bch d d' := by
  zumgg
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro d s a k ptr hw h02 h14 h12 h13 h16 h04 h17 h18 h20 hWs hWa hWp hWk
    by_cases hL : L = 0
    · subst hL
      rw [chunks_zero]
      refine ⟨d, 2, .whileLtN_false by_omega hw, by_simp, by_omega,
        by omega, fun i hi => by_grind, fun _ _ => rfl, FrameM.refl _ _⟩
    · have hcons := chunks_cons (s := s) (a := a) hC (by omega : 1 ≤ L)
      set len := min C L with hlen
      have hlen1 : 1 ≤ len := le_min hC by_omega
      have hlenL : len ≤ L := min_le_right _ _
      rw [hcons] at hWp hWk
      simp only [List.length_cons] at hWp hWk
      obtain ⟨d₁, j₁, e₁, hj₁, b12, b13, b14, b16, b04, bm, f₁⟩ :=
        plChBody_exec (P := P) d hw h02 h14 h12 h13 h16 h04 h18 h20 by_omega hWs hWa by_omega
      have g₁ : ∀ r, Bch r = false → d₁.nreg r = d.nreg r := f₁.1
      obtain ⟨d', j₂, e₂, hj₂, c16, c04, cL, cm, cf⟩ := ih (L - len) by_omega d₁ (s + len)
        (a + len) zts ztoeq e₁.wb_right (by rw [g₁ _ by_decide, h02]) b14 b12 b13 b16
        b04 (by rw [g₁ _ by_decide, h17]) (by rw [g₁ _ by_decide, h18])
        (by rw [g₁ _ by_decide, h20]) by_omega by_omega by_omega by_omega
      refine ⟨d', j₁ + 2 + j₂, .whileLtN_true by_omega e₁ e₂, ?_, ?_, ?_, ?_,
        ?_, f₁.trans cf⟩
      · rw [hcons, List.length_cons]; omega
      · rw [c16, hcons, List.length_cons]; ring
      · grind
      · rw [hcons]
        zug
        zubuk
        · rw [cm _ ztec, cm _ ztec, cm _ ztec, bm]
          simp only [List.getD_cons_zero, Nat.mul_zero, Nat.add_zero]
          zusk
          · simp
          · rw [Machine.upd_other _ _ _ by_omega, Machine.upd_same]
          simp
        · zujnr
          obtain ⟨x1, x2, x3⟩ := cL i by_omega
          zufax
          grind
      · zuh
        rw [hcons, List.length_cons] at hx
        rw [cm x by_omega, bm, Machine.upd_other _ _ _ by_omega,
          Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega]
