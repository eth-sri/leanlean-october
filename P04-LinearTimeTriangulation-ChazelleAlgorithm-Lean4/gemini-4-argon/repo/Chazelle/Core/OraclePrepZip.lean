module

public import Chazelle.Core.OraclePrepZipBody

/-!
# Lemma 3.6 (WP-H), preprocessing part 11: the zipper loops

* `zipBody d`: the analysis of an end of the arc at spine position `x` and, when its key lies in
  the open halves of the tour range, the located part; `zipBody_exec`: the flag and the pair of
  `zipSk x` (`d`) or `zipEk x` (`¬ d`).
* `zS`: two raw pair arrays of capacity `2 A + 5` at the allocator (bases `110293`, `110294`,
  count `110295`), and the pairs of the starts and of the ends emitted into them (`zS_exec`).
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey NFLoc
open OracleQ
open Chazelle.Chain (sideInArc)

@[expose] public section

/-- **One step of the zipper.** -/
def zipBody (d : Bool) : Stmt :=
  .seq (prepS d) (.ifLtN 120012 110104 (locS d) (.instr (.constN 110290 0)))

/-- The registers written by `zipBody`. -/
def BZB (r : ℕ) : Bool := BPR r || BLS r

/-- The pair function of a side. -/
noncomputable def zipF (C : Chain) (Q : Polygon) (N : NF) (d : Bool) : ℕ → Option (ℕ × ℕ) :=
  if d then zipSk C Q N else zipEk C Q N

theorem zipBody_exec {P : Polygon} {W lo : ℕ} {C : Chain} {N : NF} {V : QV} {c : Config}
    (hw : WordsBounded W c) (h : ZEnv P W lo C N V c) {x : ℕ} (hx : c.nreg 110299 = x)
    (hxA : x < V.A) (d : Bool) :
    ∃ c' k, Exec P W (zipBody d) c c' k ∧ k ≤ 5500 * (V.L + 1) + 400 ∧ FrameB BZB c c' ∧
      (zipF C (Qof P) N d x = none → c'.nreg 110290 = 0) ∧
      ∀ z, zipF C (Qof P) N d x = some z →
        c'.nreg 110290 = 1 ∧ c'.nreg 110291 = z.1 ∧ c'.nreg 110292 = z.2 := by
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, o₁, fl₁, mir₁⟩ := prepS_exec hw h hx hxA d
  have h₁ : ZEnv P W lo C N V c₁ := h.stable (fun r hr => f₁.1 r (by
    simp only [ZKeep, Bool.or_eq_true, decide_eq_true_eq] at hr
    simp only [BPR, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega))
    (fun a _ => by rw [f₁.2.2.1])
  have x₁ : c₁.nreg 110299 = x := by rw [f₁.1 _ (by decide), hx]
  have hA := h.mem.1.A
  have hkx : (chainModel C).key C.P (endPos N d x) =
      if d then sk (chainModel C) (Qof P) N x else ek (chainModel C) (Qof P) N x := by
    rw [h.CQ, key_endPos]
  have hkx' : (chainModel C).key (Qof P) (endPos N d x) =
      if d then sk (chainModel C) (Qof P) N x else ek (chainModel C) (Qof P) N x := by
    rw [key_endPos]
  have hGM : GoodModel (chainModel C) := Or.inl ⟨C, h.simple, rfl⟩
  by_cases hI : InI C ((chainModel C).key C.P (endPos N d x))
  · rw [ite_eq_left hI] at fl₁
    have ht : c₁.nreg 120012 < c₁.nreg 110104 := by rw [h₁.pk.zero, fl₁]; exact Nat.one_pos
    obtain ⟨c₂, k₂, e₂, hk₂, f₂, q, hqA, hq, n₂, s₂⟩ := locS_exec e₁.wb_right h₁ x₁ hxA d o₁ hI mir₁
    have ex : Exec P W (zipBody d) c c₂ _ :=
      .seq e₁ (.ifLtN_true (e := .instr (.constN 110290 0)) ht e₂)
    have fr : FrameB BZB c c₂ := (FrameB.mono f₁ fun r hr => by simp [BZB, hr]).trans
      (FrameB.mono f₂ fun r hr => by simp [BZB, hr])
    -- the pair function is `normP x q`
    suffices H : zipF C (Qof P) N d x = normP x q by
      rw [H]; exact ⟨_, _, ex, by omega, fr, n₂, s₂⟩
    rw [hkx] at hI
    have hqN : q < N.arcs.length := by rwa [← hA]
    by_cases hne : (N.F (chainModel C) (Qof P)).Nonempty
    · have hq' := hq hne
      rw [hkx'] at hq'
      unfold zipF
      cases d
      · simp only [Bool.false_eq_true, ite_false] at hI hq' ⊢
        have hex : ∃ p, p < N.arcs.length ∧
            After C (Qof P) N p (mk C (ek (chainModel C) (Qof P) N x)) := ⟨q, hqN, hq'⟩
        obtain ⟨ha, hA'⟩ := aftArc_spec C (Qof P) N hex
        unfold zipEk
        rw [ite_eq_left ⟨hI, hex⟩, after_unique h.isNF h.simple hne ha hqN hA' hq', normP_comm]
      · simp only [ite_true] at hI hq' ⊢
        have hex : ∃ p, p < N.arcs.length ∧
            Before C (Qof P) N p (mk C (sk (chainModel C) (Qof P) N x)) := ⟨q, hqN, hq'⟩
        obtain ⟨hb, hB'⟩ := befArc_spec C (Qof P) N hex
        unfold zipSk
        rw [ite_eq_left ⟨hI, hex⟩, before_unique h.isNF h.simple hne hb hqN hB' hq']
    · have hA1 := arcs_le_one_of_empty h.isNF hGM (Set.not_nonempty_iff_eq_empty.1 hne)
      rw [normP_none_of_le_one hA1 (by omega) (by omega)]
      unfold zipF
      cases d
      · simp only [Bool.false_eq_true, ite_false]
        unfold zipEk; split_ifs
        · exact normP_none_of_le_one hA1 (aftArc_lt C (Qof P) N _) (by omega)
        · rfl
      · simp only [ite_true]
        unfold zipSk; split_ifs
        · exact normP_none_of_le_one hA1 (by omega) (befArc_lt C (Qof P) N _)
        · rfl
  · rw [ite_eq_right hI] at fl₁
    have ht : ¬ c₁.nreg 120012 < c₁.nreg 110104 := by rw [h₁.pk.zero, fl₁]; exact Nat.lt_irrefl 0
    have e₂ := Exec.constN (P := P) e₁.wb_right 110290 0 (Nat.zero_le _)
    have ex : Exec P W (zipBody d) c _ _ := .seq e₁ (.ifLtN_false (t := locS d) ht e₂)
    have fr : FrameB BZB c _ := (FrameB.mono f₁ fun r hr => by simp [BZB, hr]).trans
      (FrameB.mono (exec_frameB e₂ (B := fun r => decide (r = 110290)) (by decide))
        fun r hr => by simp at hr; subst hr; decide)
    have hnone : zipF C (Qof P) N d x = none := by
      rw [hkx] at hI
      unfold zipF
      cases d
      · simp only [Bool.false_eq_true, ite_false] at hI ⊢
        unfold zipEk; rw [ite_eq_right (fun h' => hI h'.1)]
      · simp only [ite_true] at hI ⊢
        unfold zipSk; rw [ite_eq_right (fun h' => hI h'.1)]
    refine ⟨_, _, ex, by omega, fr, fun _ => by config_simp, fun z hz => ?_⟩
    rw [hnone] at hz; cases hz

theorem BZB_keep {r : ℕ} (h : ZKeep r = true ∨ (110293 ≤ r ∧ r ≤ 110299)) : BZB r = false := by
  simp only [ZKeep, Bool.or_eq_true, decide_eq_true_eq] at h
  simp [BZB, BPR, BLS, BL, Bdir, Bloc, Bcmp, Bk]
  omega

/-- The capacity of the raw pair arrays. -/
def zCap (A : ℕ) : ℕ := 2 * A + 5

/-- **The zipper loops.** -/
def zS : Stmt :=
  .seq (block [.copyN 110293 9999, .addN 110297 120030 120030, .constN 110298 5,
      .addN 110297 110297 110298, .addN 110294 110293 110297, .addN 9999 110294 110297,
      .constN 110295 0])
    (.seq (emitS 110299 120030 120011 110290 110291 110292 110293 110294 110295 110296 (zipBody true))
      (emitS 110299 120030 120011 110290 110291 110292 110293 110294 110295 110296 (zipBody false)))

/-- The registers written by `zS`. -/
def BZS (r : ℕ) : Bool := decide (r = 9999) || BZB r || decide (110293 ≤ r ∧ r ≤ 110299)

theorem zS_exec {P : Polygon} {W lo : ℕ} {C : Chain} {N : NF} {V : QV} {c : Config}
    (hw : WordsBounded W c) (h : ZEnv P W lo C N V c) {A₀ : ℕ} (hAl : c.nreg 9999 = A₀)
    (hlo : lo ≤ A₀) (hW : A₀ + 2 * zCap V.A ≤ W) :
    ∃ c' k, Exec P W zS c c' k ∧ k ≤ 2 * V.A * (5500 * (V.L + 1) + 410) + 20 ∧ PF BZS A₀ c c' ∧
      c'.nreg 9999 = A₀ + 2 * zCap V.A ∧ c'.nreg 110293 = A₀ ∧
      c'.nreg 110294 = A₀ + zCap V.A ∧ c'.nreg 110297 = zCap V.A ∧
      c'.nreg 110295 = (emitted (zipSk C (Qof P) N) V.A ++ emitted (zipEk C (Qof P) N) V.A).length ∧
      PairsAt c'.nmem A₀ (A₀ + zCap V.A)
        (emitted (zipSk C (Qof P) N) V.A ++ emitted (zipEk C (Qof P) N) V.A) ∧
      ZEnv P W lo C N V c' := by
  obtain ⟨c₁, k₁, e₁, hk₁, n₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 110293 9999,
      .addN 110297 120030 120030, .constN 110298 5, .addN 110297 110297 110298,
      .addN 110294 110293 110297, .addN 9999 110294 110297, .constN 110295 0]) c c₁ k₁ ∧ k₁ = 7 ∧
      c₁.nreg = upd (upd (upd (upd (upd (upd c.nreg 110293 A₀) 110297 (zCap V.A)) 110298 5)
        110294 (A₀ + zCap V.A)) 9999 (A₀ + 2 * zCap V.A)) 110295 0 ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold zCap at hW ⊢
    have hA := h.rA
    exec_block
    · config_simp; rw [hA]; omega
    · omega
    · config_simp; rw [hA]; omega
    · config_simp; rw [hA, hAl]; omega
    · config_simp; rw [hA, hAl]; omega
    · omega
    · refine ⟨rfl, ?_, rfl, rfl, rfl, rfl⟩
      config_simp; rw [hA, hAl]
      funext r; simp only [upd]; split_ifs <;> first | omega
  have R₁ : ∀ r, BZS r = false → c₁.nreg r = c.nreg r := fun r hr => by
    simp only [BZS, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
    rw [n₁]; simp only [upd]; split_ifs <;> first | omega
  have h₁ : ZEnv P W lo C N V c₁ := h.stable (fun r hr => R₁ r (by
      simp only [BZS, Bool.or_eq_false_iff, decide_eq_false_iff_not]
      refine ⟨⟨?_, BZB_keep (Or.inl hr)⟩, ?_⟩ <;>
      simp only [ZKeep, Bool.or_eq_true, decide_eq_true_eq] at hr <;> omega))
    (fun a _ => by rw [m₁])
  have v93 : c₁.nreg 110293 = A₀ := by rw [n₁]; config_simp
  have v94 : c₁.nreg 110294 = A₀ + zCap V.A := by rw [n₁]; config_simp
  have v95 : c₁.nreg 110295 = 0 := by rw [n₁]; config_simp
  have v97 : c₁.nreg 110297 = zCap V.A := by rw [n₁]; config_simp
  have v9 : c₁.nreg 9999 = A₀ + 2 * zCap V.A := by rw [n₁]; config_simp
  have hJs : ∀ d d', ZEnv P W lo C N V d →
      (∀ r, BZB r = false → r ≠ 110299 → r ≠ 110295 → r ≠ 110296 → d'.nreg r = d.nreg r) →
      (∀ a, a < A₀ → d'.nmem a = d.nmem a) → ZEnv P W lo C N V d' := fun d d' hJ hr hm =>
    hJ.stable (fun r hr' => hr r (BZB_keep (Or.inl hr')) (by
        simp only [ZKeep, Bool.or_eq_true, decide_eq_true_eq] at hr'; omega) (by
        simp only [ZKeep, Bool.or_eq_true, decide_eq_true_eq] at hr'; omega) (by
        simp only [ZKeep, Bool.or_eq_true, decide_eq_true_eq] at hr'; omega))
      (fun a ha => hm a (by omega))
  -- the starts
  obtain ⟨c₂, k₂, e₂, hk₂, r₂, rr₂, cnt₂, pr₂, mm₂, rm₂, o₂, J₂⟩ := emitS_exec (P := P) (W := W)
    (ri := 110299) (rn := 120030) (r1 := 120011) (rf := 110290) (rv1 := 110291) (rv2 := 110292)
    (rR1 := 110293) (rR2 := 110294) (rc := 110295) (rt := 110296) (body := zipBody true)
    (B := BZB) (by decide) (BZB_keep (Or.inr (by norm_num))) (BZB_keep (Or.inl (by decide)))
    (BZB_keep (Or.inl (by decide))) (BZB_keep (Or.inr (by norm_num))) (BZB_keep (Or.inr (by norm_num)))
    (BZB_keep (Or.inr (by norm_num))) (R1 := A₀) (ZEnv P W lo C N V)
    (fun d d' hJ hr hm => hJs d d' hJ hr (fun a ha => hm a (Or.inl (by omega)))) (n := V.A)
    (κ := 5500 * (V.L + 1) + 400) (zipSk C (Qof P) N)
    (fun i d hi hJ hwd hri => by
      obtain ⟨d', k, e, hk, f, a, b⟩ := zipBody_exec hwd hJ hri hi true
      exact ⟨d', k, e, hk, f, a, b⟩)
    e₁.wb_right h₁ h₁.rA h₁.pk.one v93 v94 v95 (by unfold zCap; omega)
    (by unfold zCap at hW ⊢; omega)
  rw [Nat.zero_add] at cnt₂
  simp only [Nat.add_zero] at pr₂
  set L1 := emitted (zipSk C (Qof P) N) V.A
  have hL1 : L1.length ≤ V.A := emitted_length_le _ _
  -- the ends
  have g93 : c₂.nreg 110293 = A₀ := by
    rw [r₂ _ (BZB_keep (Or.inr (by norm_num))) (by decide) (by decide) (by decide), v93]
  have g94 : c₂.nreg 110294 = A₀ + zCap V.A := by
    rw [r₂ _ (BZB_keep (Or.inr (by norm_num))) (by decide) (by decide) (by decide), v94]
  obtain ⟨c₃, k₃, e₃, hk₃, r₃, rr₃, cnt₃, pr₃, mm₃, rm₃, o₃, J₃⟩ := emitS_exec (P := P) (W := W)
    (ri := 110299) (rn := 120030) (r1 := 120011) (rf := 110290) (rv1 := 110291) (rv2 := 110292)
    (rR1 := 110293) (rR2 := 110294) (rc := 110295) (rt := 110296) (body := zipBody false)
    (B := BZB) (by decide) (BZB_keep (Or.inr (by norm_num))) (BZB_keep (Or.inl (by decide)))
    (BZB_keep (Or.inl (by decide))) (BZB_keep (Or.inr (by norm_num))) (BZB_keep (Or.inr (by norm_num)))
    (BZB_keep (Or.inr (by norm_num))) (R1 := A₀) (ZEnv P W lo C N V)
    (fun d d' hJ hr hm => hJs d d' hJ hr (fun a ha => hm a (Or.inl (by omega)))) (n := V.A)
    (κ := 5500 * (V.L + 1) + 400) (zipEk C (Qof P) N)
    (fun i d hi hJ hwd hri => by
      obtain ⟨d', k, e, hk, f, a, b⟩ := zipBody_exec hwd hJ hri hi false
      exact ⟨d', k, e, hk, f, a, b⟩)
    e₂.wb_right J₂ J₂.rA J₂.pk.one g93 g94 cnt₂ (by unfold zCap; omega)
    (by unfold zCap at hW ⊢; omega)
  set L2 := emitted (zipEk C (Qof P) N) V.A
  have hL2 : L2.length ≤ V.A := emitted_length_le _ _
  have hB : ∀ r, BZS r = false → BZB r = false ∧ r ≠ 110299 ∧ r ≠ 110295 ∧ r ≠ 110296 := by
    intro r hr
    simp only [BZS, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
    exact ⟨hr.1.2, by omega, by omega, by omega⟩
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), ?_, ⟨fun r hr => ?_, fun r hr => ?_, fun a ha => ?_,
    fun a _ => by rw [rm₃, rm₂, rm₁], by rw [o₃, o₂, o₁]⟩, ?_, ?_, ?_, ?_, ?_, ?_, J₃⟩
  · have : V.A * (5500 * (V.L + 1) + 400 + 10) ≤ V.A * (5500 * (V.L + 1) + 410) := le_refl _
    nlinarith
  · obtain ⟨a, b, c', d'⟩ := hB r hr
    rw [r₃ r a b c' d', r₂ r a b c' d']; exact R₁ r hr
  · obtain ⟨a, -⟩ := hB r hr
    rw [rr₃ r a, rr₂ r a, rr₁]
  · have ha1 : a < A₀ + L1.length := by omega
    have ha2 : a < A₀ + 0 := by omega
    rw [mm₃ a (Or.inl ha1), mm₂ a (Or.inl ha2), m₁]
  · rw [r₃ _ (by decide) (by decide) (by decide) (by decide),
      r₂ _ (by decide) (by decide) (by decide) (by decide), v9]
  · rw [r₃ _ (BZB_keep (Or.inr (by norm_num))) (by decide) (by decide) (by decide), g93]
  · rw [r₃ _ (BZB_keep (Or.inr (by norm_num))) (by decide) (by decide) (by decide), g94]
  · rw [r₃ _ (BZB_keep (Or.inr (by norm_num))) (by decide) (by decide) (by decide),
      r₂ _ (BZB_keep (Or.inr (by norm_num))) (by decide) (by decide) (by decide), v97]
  · rw [cnt₃, List.length_append]
  · refine PairsAt.append (PairsAt.congr pr₂ fun t ht => ⟨mm₃ _ (Or.inl (by omega)),
      mm₃ _ (Or.inr (Or.inl ⟨by unfold zCap at *; omega, by omega⟩))⟩) pr₃

end

end OracleR

end Chazelle.Core
