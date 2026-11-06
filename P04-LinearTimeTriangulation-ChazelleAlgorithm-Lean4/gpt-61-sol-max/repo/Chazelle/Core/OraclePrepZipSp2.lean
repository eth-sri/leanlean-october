module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.OraclePrepZipSp

/-!
# Lemma 3.6 (WP-H), preprocessing part 13: the emission of the special pairs

* `emit1`: append the pair `(110291, 110292)` to the raw arrays when the flag `110290` is set
  (`emit1_exec`);
* `emitG`: normalise the pair `(110299, 110214)`, clear the flag unless the guard `110245` is
  set, append (`emitG_exec`).
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey NFLoc
open OracleQ
open Chazelle.Chain (sideInArc)

@[expose] public section

/-- **Append one pair** to the raw arrays when the flag is set. -/
def emit1 : Stmt :=
  .ifLtN 110290 120011 .skip
    (block [.addN 110296 110293 110295, .storeN 110296 110291, .addN 110296 110294 110295,
      .storeN 110296 110292, .addN 110295 110295 120011])

theorem emit1_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
    (h1 : c.nreg 120011 = 1) {R1 R2 c₀ : ℕ} (hR1 : c.nreg 110293 = R1) (hR2 : c.nreg 110294 = R2)
    (hc : c.nreg 110295 = c₀) (o : Option (ℕ × ℕ)) (hn : o = none → c.nreg 110290 = 0)
    (hs : ∀ z, o = some z → c.nreg 110290 = 1 ∧ c.nreg 110291 = z.1 ∧ c.nreg 110292 = z.2)
    (hR12 : R1 + c₀ + 1 ≤ R2) (hRW : R2 + c₀ + 1 ≤ W) :
    ∃ c' k, Exec P W emit1 c c' k ∧ k ≤ 7 ∧
      (∀ r, r ≠ 110295 → r ≠ 110296 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧ c'.nreg 110295 = c₀ + o.toList.length ∧
      PairsAt c'.nmem (R1 + c₀) (R2 + c₀) o.toList ∧
      (∀ a, (a < R1 + c₀ ∨ (R1 + c₀ + o.toList.length ≤ a ∧ a < R2 + c₀) ∨
        R2 + c₀ + o.toList.length ≤ a) → c'.nmem a = c.nmem a) := by
  unfold emit1
  cases ho : o with
  | none =>
    have hf := hn ho
    have ht : c.nreg 110290 < c.nreg 120011 := by omega
    exact ⟨c, 1, .ifLtN_true ht (.skip hw), by omega, fun _ _ _ => rfl, rfl, rfl, rfl,
      by rw [hc]; rfl, fun t ht => by simp at ht, fun _ _ => rfl⟩
  | some z =>
    obtain ⟨hf, hv1, hv2⟩ := hs z ho
    have ht : ¬ c.nreg 110290 < c.nreg 120011 := by omega
    obtain ⟨c', k, e, hk, n', m', rr', rm', o'⟩ : ∃ c' k, Exec P W (block [.addN 110296 110293 110295,
        .storeN 110296 110291, .addN 110296 110294 110295, .storeN 110296 110292,
        .addN 110295 110295 120011]) c c' k ∧ k = 5 ∧
        c'.nreg = upd (upd c.nreg 110296 (R2 + c₀)) 110295 (c₀ + 1) ∧
        c'.nmem = upd (upd c.nmem (R1 + c₀) z.1) (R2 + c₀) z.2 ∧ c'.rreg = c.rreg ∧
        c'.rmem = c.rmem ∧ c'.output = c.output := by
      exec_block
      · omega
      · omega_nf
      · omega_nf
      simp_all
    refine ⟨c', _, .ifLtN_false ht e, by omega, fun r a b => ?_, rr', rm', o', ?_, fun t ht' => ?_,
      fun a ha => ?_⟩
    · ram_simp
    · ram_simp
    · simp only [Option.toList_some, List.length_cons, List.length_nil] at ht'
      have : t = 0 := by omega
      ram_simp 
    · simp only [Option.toList_some, List.length_cons, List.length_nil] at ha
      rw [m', upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]

/-- **Normalise, guard, append.** -/
def emitG : Stmt :=
  .seq normS (.seq (.ifLtN 120012 110245 .skip (.instr (.constN 110290 0))) emit1)

/-- The option emitted by `emitG`. -/
def gOpt (g a b : ℕ) : Option (ℕ × ℕ) := if g = 0 then none else normP a b

theorem emitG_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
    (h1 : c.nreg 120011 = 1) (h0 : c.nreg 120012 = 0) {R1 R2 c₀ : ℕ} (hR1 : c.nreg 110293 = R1)
    (hR2 : c.nreg 110294 = R2) (hc : c.nreg 110295 = c₀) (hR12 : R1 + c₀ + 1 ≤ R2)
    (hRW : R2 + c₀ + 1 ≤ W) (ha : c.nreg 110299 + 1 ≤ W) (hb : c.nreg 110214 + 1 ≤ W) :
    ∃ c' k, Exec P W emitG c c' k ∧ k ≤ 25 ∧
      (∀ r, r ≠ 110295 → r ≠ 110296 → r ≠ 110215 → (r < 110290 ∨ 110292 < r) →
        c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧
      c'.nreg 110295 = c₀ + (gOpt (c.nreg 110245) (c.nreg 110299) (c.nreg 110214)).toList.length ∧
      PairsAt c'.nmem (R1 + c₀) (R2 + c₀) (gOpt (c.nreg 110245) (c.nreg 110299) (c.nreg 110214)).toList ∧
      (∀ a, (a < R1 + c₀ ∨ (R1 + c₀ + (gOpt (c.nreg 110245) (c.nreg 110299)
        (c.nreg 110214)).toList.length ≤ a ∧ a < R2 + c₀) ∨ R2 + c₀ + (gOpt (c.nreg 110245)
        (c.nreg 110299) (c.nreg 110214)).toList.length ≤ a) → c'.nmem a = c.nmem a) := by
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, n₁, s₁⟩ := normS_exec (P := P) hw h1 ha hb
  have R₁ : ∀ r, (r < 110290 ∨ 110292 < r) → r ≠ 110215 → c₁.nreg r = c.nreg r := fun r a b =>
    f₁.1 r (by simp; omega)
  -- the guard
  obtain ⟨g, hg⟩ : ∃ g, c.nreg 110245 = g := ⟨_, rfl⟩
  obtain ⟨c₂, k₂, e₂, hk₂, n₂, s₂, R₂⟩ : ∃ c₂ k₂, Exec P W (.ifLtN 120012 110245 .skip
      (.instr (.constN 110290 0))) c₁ c₂ k₂ ∧ k₂ ≤ 3 ∧
      (gOpt g (c.nreg 110299) (c.nreg 110214) = none → c₂.nreg 110290 = 0) ∧
      (∀ z, gOpt g (c.nreg 110299) (c.nreg 110214) = some z →
        c₂.nreg 110290 = 1 ∧ c₂.nreg 110291 = z.1 ∧ c₂.nreg 110292 = z.2) ∧
      (∀ r, r ≠ 110290 → c₂.nreg r = c₁.nreg r) ∧ c₂.nmem = c₁.nmem ∧ c₂.rreg = c₁.rreg ∧
      c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    have w₁ := e₁.wb_right
    unfold gOpt
    by_cases hg0 : g = 0
    · have ht : ¬ c₁.nreg 120012 < c₁.nreg 110245 := by
        grind
      refine ⟨_, _, .ifLtN_false ht (Exec.constN w₁ 110290 0 (Nat.zero_le _)), by omega,
        (fun _ => by config_simp), (fun z hz => by grind),
        (fun r hr => by config_simp; rw [upd_other _ _ _ hr]), rfl, rfl, rfl, rfl⟩
    · have ht : c₁.nreg 120012 < c₁.nreg 110245 := by
        grind
      refine ⟨_, _, .ifLtN_true ht (.skip w₁), by omega, fun hn => ?_, fun z hz => ?_,
        fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
      all_goals grind
  rw [hg]
  have g1 : c₂.nreg 120011 = 1 := by grind
  have g93 : c₂.nreg 110293 = R1 := by grind
  have g94 : c₂.nreg 110294 = R2 := by grind
  have g95 : c₂.nreg 110295 = c₀ := by grind
  obtain ⟨c₃, k₃, e₃, hk₃, r₃, rr₃, rm₃, o₃, cnt₃, pr₃, mm₃⟩ := emit1_exec (P := P) e₂.wb_right g1 g93
    g94 g95 _ n₂ s₂ hR12 hRW
  have hm₁ : c₁.nmem = c.nmem := f₁.2.2.1
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), by omega, fun r a b c' d => ?_, ?_, ?_, ?_, cnt₃, pr₃,
    fun x hx => ?_⟩
  · grind
  · rw [rr₃, R₂.2.2.1]; funext r
    exact WalkKey.exec_rframe e₁ (B := fun _ => false) (by decide) r rfl
  · ram_grind
  · ram_grind
  grind

/-! ## The special pairs from the analyses of the three top keys -/

/-- The facts of the analysis of a walk vertex `X`. -/
def KInfo (C : Chain) (Q : Polygon) (N : NF) (X : ℝ) (bef aft j s : ℕ) : Prop :=
  bef < N.arcs.length ∧ aft < N.arcs.length ∧ j < N.arcs.length ∧
    ((N.F (chainModel C) Q).Nonempty →
      Before C Q N bef X ∧ After C Q N aft X ∧
      (s = 0 ↔ sideInArc (sk (chainModel C) Q N j) (ek (chainModel C) Q N j) X) ∧
      ∀ q, q < N.arcs.length → sideInArc (sk (chainModel C) Q N q) (ek (chainModel C) Q N q) X →
        q = j)

/-- The five options emitted. -/
def spRam (R _bef6 aft6 j6 s6 befT aftT jT sT bef2 _aft2 j2 s2 : ℕ) : List (Option (ℕ × ℕ)) :=
  [gOpt (if 0 < R then 1 else 0) aft6 befT, gOpt 1 aftT bef2,
    gOpt (if 0 < R ∧ s6 + sT = 0 then 1 else 0) j6 jT,
    gOpt (if sT + s2 = 0 then 1 else 0) jT j2, gOpt (if s6 + s2 = 0 then 1 else 0) j6 j2]

section
variable {C : Chain} {Q : Polygon} {N : NF}
theorem inArc_iff {X : ℝ} {bef aft j s : ℕ}
    (hK : KInfo C Q N X bef aft j s) (hne : (N.F (chainModel C) Q).Nonempty) :
    (s = 0 ↔ InArc C Q N X) ∧ (InArc C Q N X → inArcIdx C Q N X = j) := by
  obtain ⟨-, -, hj, hK⟩ := hK
  obtain ⟨-, -, hs, hu⟩ := hK hne
  refine ⟨⟨fun h0 => ⟨j, hj, hs.1 h0⟩, fun ⟨q, hq, hin⟩ => hs.2 (hu q hq hin ▸ hin)⟩,
    fun hin => ?_⟩
  obtain ⟨a, b⟩ := inArcIdx_spec C Q N hin
  grind

/-- **The special pairs**: the options of the analyses are those of `zipSpO`. -/
theorem spRam_eq (hN : IsNF (chainModel C) Q N)
    (hP : C.P.Simple) {bef6 aft6 j6 s6 befT aftT jT sT bef2 aft2 j2 s2 : ℕ}
    (h6 : KInfo C Q N 6 bef6 aft6 j6 s6) (hT : KInfo C Q N (κT C) befT aftT jT sT)
    (h2 : KInfo C Q N (2 * C.m + 6) bef2 aft2 j2 s2) :
    (spRam (rT C) bef6 aft6 j6 s6 befT aftT jT sT bef2 aft2 j2 s2).filterMap id =
      zipSp C Q N := by
  have hGM : GoodModel (chainModel C) := Or.inl ⟨C, hP, rfl⟩
  unfold zipSp zipSpO spRam
  by_cases hne : (N.F (chainModel C) Q).Nonempty
  · obtain ⟨b6, a6, j6l, K6⟩ := h6
    obtain ⟨bT, aT, jTl, KT⟩ := hT
    obtain ⟨b2, a2, j2l, K2⟩ := h2
    obtain ⟨B6, A6, -, -⟩ := K6 hne
    obtain ⟨BT, AT, -, -⟩ := KT hne
    obtain ⟨B2, A2, -, -⟩ := K2 hne
    obtain ⟨i6, x6⟩ := inArc_iff ⟨b6, a6, j6l, K6⟩ hne
    obtain ⟨iT, xT⟩ := inArc_iff ⟨bT, aT, jTl, KT⟩ hne
    obtain ⟨i2, x2⟩ := inArc_iff ⟨b2, a2, j2l, K2⟩ hne
    have eA6 : aftArc C Q N 6 = aft6 := by
      obtain ⟨a, b⟩ := aftArc_spec C Q N ⟨aft6, a6, A6⟩
      exact after_unique hN hP hne a a6 b A6
    have eAT : aftArc C Q N (κT C) = aftT := by
      obtain ⟨a, b⟩ := aftArc_spec C Q N ⟨aftT, aT, AT⟩
      exact after_unique hN hP hne a aT b AT
    have eBT : befArc C Q N (κT C) = befT := by
      obtain ⟨a, b⟩ := befArc_spec C Q N ⟨befT, bT, BT⟩
      exact before_unique hN hP hne a bT b BT
    have eB2 : befArc C Q N (2 * C.m + 6) = bef2 := by
      obtain ⟨a, b⟩ := befArc_spec C Q N ⟨bef2, b2, B2⟩
      exact before_unique hN hP hne a b2 b B2
    have e1 : gOpt (if 0 < rT C then 1 else 0) aft6 befT = sp1 C Q N := by
      unfold sp1 gOpt
      by_cases hr : 0 < rT C
      · rw [ite_eq_left hr, ite_eq_right one_ne_zero, ite_eq_left ⟨hr, ⟨aft6, a6, A6⟩, ⟨befT, bT, BT⟩⟩, eA6, eBT]
      grind
    have e2 : gOpt 1 aftT bef2 = sp2 C Q N := by
      unfold sp2 gOpt
      rw [ite_eq_right one_ne_zero, ite_eq_left ⟨⟨aftT, aT, AT⟩, ⟨bef2, b2, B2⟩⟩, eAT, eB2]
    have e3 : gOpt (if 0 < rT C ∧ s6 + sT = 0 then 1 else 0) j6 jT = sp3 C Q N := by
      unfold sp3 gOpt
      grind
    have e4 : gOpt (if sT + s2 = 0 then 1 else 0) jT j2 = sp4 C Q N := by
      unfold sp4 gOpt
      grind
    have e5 : gOpt (if s6 + s2 = 0 then 1 else 0) j6 j2 = sp5 C Q N := by
      unfold sp5 gOpt
      grind
    grind
  · have hA := arcs_le_one_of_empty hN hGM (Set.not_nonempty_iff_eq_empty.1 hne)
    obtain ⟨b6, a6, j6l, -⟩ := h6
    obtain ⟨bT, aT, jTl, -⟩ := hT
    obtain ⟨b2, a2, j2l, -⟩ := h2
    have hn : ∀ g a b, a < N.arcs.length → b < N.arcs.length → gOpt g a b = none := by
      intro g a b ha hb
      unfold gOpt; split_ifs
      · rfl
      · exact normP_none_of_le_one hA (by omega) (by omega)
    have hs : ∀ o : Option (ℕ × ℕ), o ∈ zipSpO C Q N → o = none := by
      intro o ho
      have n1 := normP_none_of_le_one hA (aftArc_lt C Q N 6) (befArc_lt C Q N (κT C))
      have n2 := normP_none_of_le_one hA (aftArc_lt C Q N (κT C)) (befArc_lt C Q N (2 * C.m + 6))
      have n3 := normP_none_of_le_one hA (inArcIdx_lt C Q N 6) (inArcIdx_lt C Q N (κT C))
      have n4 := normP_none_of_le_one hA (inArcIdx_lt C Q N (κT C))
        (inArcIdx_lt C Q N (2 * C.m + 6))
      have n5 := normP_none_of_le_one hA (inArcIdx_lt C Q N 6) (inArcIdx_lt C Q N (2 * C.m + 6))
      simp only [zipSpO, List.mem_cons, List.mem_nil_iff, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl
      · unfold sp1; simp_all
      · unfold sp2; simp_all
      all_goals (grind [sp3, sp4, sp5])
    have hz : (zipSpO C Q N).filterMap id = [] := by
      grind [List.filterMap_eq_nil_iff]
    unfold zipSpO at hz
    rw [hz, hn _ _ _ a6 bT, hn _ _ _ aT b2, hn _ _ _ j6l jTl, hn _ _ _ jTl j2l, hn _ _ _ j6l j2l]
    rfl


end

end

end OracleR

end Chazelle.Core
