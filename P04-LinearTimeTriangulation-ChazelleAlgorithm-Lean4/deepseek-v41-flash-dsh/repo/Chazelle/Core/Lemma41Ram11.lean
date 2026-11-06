module

public import Chazelle.Golf

public import Chazelle.Core.Lemma41Ram10

/-!
# WP-J, part 19: one level of the merge tree

`levelS sM`: set up the pair loop (target `γ₀ + 1`, or the final granularity `Gλ` when at most two
nodes are left), merge neighbours (`pairL`), carry an odd last node (`carryS`), and write the
array of the next level (`rbS`).  `level_exec`: the next level `pairUp ns t` is held at a fresh
array, everything below the entry allocator is kept, the cost is at most `lvCost`.

Registers: `160066` the level base, `160014` its count, `160033` its granularity bound `γ₀`,
`160034` the target, `160032` the final granularity `Gλ`.
-/

namespace Chazelle.Core.L41

open Machine Machine.Stmt Programs Chazelle.Merge Finset

@[expose] public section

/-- The start of a level. -/
def lvInit : Stmt := block [.constN 160062 0, .constN 160064 0, .copyN 160065 160066,
  .subN 160067 160014 160024, .addN 160034 160033 160024]

/-- The target: the final granularity when at most two nodes are left. -/
def tgtS : Stmt := .ifLtN 160014 160083 (block [.copyN 160034 160032]) .skip

/-- The end of a level. -/
def lvFin : Stmt := block [.copyN 160066 160094, .copyN 160014 160064, .copyN 160033 160034]

/-- **One level of the merge tree.** -/
def levelS (sM : Stmt) : Stmt :=
  .seq lvInit (.seq tgtS (.seq (pairL sM) (.seq carryS (.seq rbS lvFin))))

/-- The target of a level of `j` nodes. -/
def lvTgt (Gl j γ₀ : ℕ) : ℕ := if j < 3 then Gl else γ₀ + 1

/-- The cost bound of a level. -/
def lvCost (κ F G H : ℕ → ℕ) (ns : List Shp) (γ₀ : ℕ) : ℕ :=
  (∑ q ∈ range (ns.length / 2), (pairCost κ F G H ns γ₀ q + 331)) +
    13 * ((ns.length + 1) / 2) + 40

/-- The registers of band `bL41` written by a level. -/
def LvRG (r : ℕ) : Prop :=
  PairRG r ∨ RbRG r ∨ r = 160066 ∨ r = 160014 ∨ r = 160033 ∨ r = 160034 ∨ r = 160067

section proofs

variable {P : Polygon} {W : ℕ}


theorem lvInit_exec {c : Config} (hw : WordsBounded W c) {B j γ₀ : ℕ}
    (h66 : c.nreg 160066 = B) (h14 : c.nreg 160014 = j) (h33 : c.nreg 160033 = γ₀)
    (h24 : c.nreg 160024 = 1) (hW : γ₀ + 1 ≤ W) :
    ∃ c' k, Exec P W lvInit c c' k ∧ k = 5 ∧ WordsBounded W c' ∧
      c'.nreg 160062 = 0 ∧ c'.nreg 160064 = 0 ∧ c'.nreg 160065 = B ∧ c'.nreg 160067 = j - 1 ∧
      c'.nreg 160034 = γ₀ + 1 ∧
      (∀ r, r ≠ 160062 → r ≠ 160064 → r ≠ 160065 → r ≠ 160067 → r ≠ 160034 →
        c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lvInit
  exec_block
  all_goals try (config_simp; (try simp only [h66, h14, h33, h24]); omega)
  refine ⟨rfl, ‹_›, by config_simp, by config_simp, by config_simp; exact h66,
    by config_simp; simp only [h14, h24], by config_simp; simp only [h33, h24],
    fun r a1 a2 a3 a4 a5 => ?_, rfl, rfl, rfl, rfl⟩
  simp only
  repeat (rw [Machine.upd_other _ _ _ (⋄)])


theorem tgtS_exec {c : Config} (hw : WordsBounded W c) :
    ∃ c' k, Exec P W tgtS c c' k ∧ k ≤ 2 ∧ WordsBounded W c' ∧
      c'.nreg 160034 = (if c.nreg 160014 < c.nreg 160083 then c.nreg 160032 else c.nreg 160034) ∧
      (∀ r, r ≠ 160034 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  by_cases h : c.nreg 160014 < c.nreg 160083
  · obtain ⟨c', k, e, hk, hw', h34, fr, hm, hrr, hrm, ho⟩ : ∃ c' k, Exec P W
        (block [.copyN 160034 160032]) c c' k ∧ k = 1 ∧ WordsBounded W c' ∧
        c'.nreg 160034 = c.nreg 160032 ∧ (∀ r, r ≠ 160034 → c'.nreg r = c.nreg r) ∧
        c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
      exec_block
      refine ⟨rfl, ‹_›, by config_simp, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
      simp only
      repeat (rw [Machine.upd_other _ _ _ (by omega)])
    exact ⟨c', k + 1, .ifLtN_true h e, by omega, hw', by rw [ite_eq_left h]; exact h34, fr, hm, hrr,
      hrm, ho⟩
  · exact ⟨c, 2, .ifLtN_false h (.skip hw), le_rfl, hw, by rw [ite_eq_right h], fun _ _ => rfl, rfl,
      rfl, rfl, rfl⟩


theorem lvFin_exec {c : Config} (hw : WordsBounded W c) :
    ∃ c' k, Exec P W lvFin c c' k ∧ k = 3 ∧ WordsBounded W c' ∧
      c'.nreg 160066 = c.nreg 160094 ∧ c'.nreg 160014 = c.nreg 160064 ∧
      c'.nreg 160033 = c.nreg 160034 ∧
      (∀ r, r ≠ 160066 → r ≠ 160014 → r ≠ 160033 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lvFin
  exec_block
  refine ⟨rfl, ‹_›, by config_simp, by config_simp, by config_simp, fun r a1 a2 a3 => ?_, rfl,
    rfl, rfl, rfl⟩
  simp only
  repeat (rw [Machine.upd_other _ _ _ (⋄)])


/-- **One level of the merge tree on the RAM.** -/
theorem level_exec (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) (hWn : P.n + 3 ≤ W)
    {sM : Stmt} {κ F G H : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
    (hMM : MergeMeets sM κ F G H X Ok) (hXc : X.CapLocal)
    (hOk : ∀ C : Chain, C.P = Qof P → Ok P (chainModel C))
    {c : Config} (hw : WordsBounded W c) {A0 B hp hX γ₀ Gl : ℕ} {ns : List Shp}
    (hj : 2 ≤ ns.length)
    (hA : c.nreg ALLOC = A0) (h66 : c.nreg 160066 = B) (h14 : c.nreg 160014 = ns.length)
    (h33 : c.nreg 160033 = γ₀) (h32 : c.nreg 160032 = Gl) (h00 : c.nreg 160000 = hX)
    (h24 : c.nreg 160024 = 1) (h80 : c.nreg 160080 = 2) (h81 : c.nreg 160081 = 5)
    (h83 : c.nreg 160083 = 3) (h84 : c.nreg 160084 = 4)
    (hL : LevelAt P c.nmem A0 B hp ns) (hc : Consec ns) (hB : B + 2 * ns.length ≤ A0)
    (hγ : ∀ k, k < ns.length → (nd ns k).2.2 ≤ γ₀)
    (hγ1 : ∀ k, k < ns.length → 1 ≤ (nd ns k).2.2)
    (hXh : X.holds P c.nmem hX A0) (hcap : γ₀ + fuseLoss ≤ X.cap P c.nmem hX)
    (htg : γ₀ + fuseLoss ≤ lvTgt Gl ns.length γ₀) (hγW : γ₀ + 1 ≤ W)
    (hbud : A0 + lvCost κ F G H ns γ₀ ≤ W) :
    ∃ c' k, Exec P W (levelS sM) c c' k ∧ k ≤ lvCost κ F G H ns γ₀ ∧ WordsBounded W c' ∧
      A0 ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ A0 + k ∧
      c'.nreg 160014 = (pairUp ns (lvTgt Gl ns.length γ₀)).length ∧
      c'.nreg 160033 = lvTgt Gl ns.length γ₀ ∧
      (∃ B', c'.nreg 160066 = B' ∧
        B' + 2 * (pairUp ns (lvTgt Gl ns.length γ₀)).length ≤ c'.nreg ALLOC ∧
        LevelAt P c'.nmem (c'.nreg ALLOC) B' hp (pairUp ns (lvTgt Gl ns.length γ₀))) ∧
      (∀ a, a < A0 → c'.nmem a = c.nmem a) ∧ (∀ a, a < A0 → c'.rmem a = c.rmem a) ∧
      c'.output = c.output ∧
      (∀ r, bandOf r ∉ mergeBands ∪ oracleBands → ¬ LvRG r → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      (∀ r, bandOf r ∉ mergeBands ∪ oracleBands → ¬ LvRG r → c'.rreg r = c.rreg r) ∧
      X.holds P c'.nmem hX (c'.nreg ALLOC) ∧ X.cap P c'.nmem hX = X.cap P c.nmem hX := by
  have hAl : ALLOC = 9999 := rfl
  simp only [lvCost] at hbud ⊢
  set t := lvTgt Gl ns.length γ₀ with htdef
  have hlen' : (pairUp ns t).length = (ns.length + 1) / 2 := pairUp_length ns t
  -- 1. init
  obtain ⟨c1, k1, e1, hk1, hw1, i62, i64, i65, i67, i34, fr1, hm1, hrr1, hrm1, ho1⟩ :=
    lvInit_exec (P := P) hw h66 h14 h33 h24 hγW
  have r1 : ∀ r, 160000 ≤ r → r < 160034 → c1.nreg r = c.nreg r := fun r a b =>
    fr1 r (by omega) (by omega) (by omega) (by omega) (by omega)
  have r1' : ∀ r, 160067 < r → c1.nreg r = c.nreg r := fun r a =>
    fr1 r (by omega) (by omega) (by omega) (by omega) (by omega)
  -- 2. the target
  obtain ⟨c2, k2, e2, hk2, hw2, t34, fr2, hm2, hrr2, hrm2, ho2⟩ := tgtS_exec (P := P) hw1
  have t34' : c2.nreg 160034 = t := by
    rw [t34, r1 _ (by omega) (by omega), r1' _ (by omega), r1 _ (by omega) (by omega), i34, h14,
      h83, h32, htdef]
    unfold lvTgt; rfl
  have r2 : ∀ r, r ≠ 160034 → r ≠ 160062 → r ≠ 160064 → r ≠ 160065 → r ≠ 160067 →
      c2.nreg r = c.nreg r := fun r a1 a2 a3 a4 a5 => by
    rw [fr2 r a1]; exact fr1 r a2 a3 a4 a5 a1
  have m2 : c2.nmem = c.nmem := by rw [hm2, hm1]
  have hA2 : c2.nreg ALLOC = A0 := by
    rw [r2 _ (by rw [hAl]; omega) (by rw [hAl]; omega) (by rw [hAl]; omega)
      (by rw [hAl]; omega) (by rw [hAl]; omega)]; exact hA
  -- 3. the pair loop
  have hbud' : A0 + ∑ q ∈ range (ns.length / 2), (pairCost κ F G H ns γ₀ q + 8) ≤ W := by
    have : ∑ q ∈ range (ns.length / 2), (pairCost κ F G H ns γ₀ q + 8) ≤
        ∑ q ∈ range (ns.length / 2), (pairCost κ F G H ns γ₀ q + 331) :=
      Finset.sum_le_sum fun _ _ => by omega
    omega
  obtain ⟨c3, k3, e3, hk3, hψ3, hst⟩ := pairL_exec hG hWh hWn hMM hXc hOk hw2 (A0 := A0) (B := B)
    (hp := hp) (hX := hX) (γ₀ := γ₀) (tgt := t) (ns := ns) (by omega) hA2
    ((fr2 _ (by omega)).trans i62) ((fr2 _ (by omega)).trans i65)
    ((fr2 _ (by omega)).trans i64) ((fr2 _ (by omega)).trans i67)
    (by rw [r2 _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h33) t34'
    (by rw [r2 _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h00)
    (by rw [r2 _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h24)
    (by rw [r2 _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h80)
    (by rw [r2 _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h81)
    (by rw [r2 _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h83)
    (by rw [r2 _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h84)
    (by rw [m2]; exact hL) hc hB hγ hγ1 (by rw [m2]; exact hXh) (by rw [m2]; exact hcap) htg
    hbud'
  have hst' := hst
  obtain ⟨-, -, -, -, s3A0, s3A1, s3m, s3rm, s3o, s3r, s3rr, s3X, s3cap, -⟩ := hst'
  -- 4. the carry
  obtain ⟨c4, k4, e4, hk4, hw4, a41, a42, a43, m43, rm43, o43, rr43, fr43, c64, ee, hcell, h63,
      hee0⟩ :=
    carryS_exec (hj := by omega) hst
      (by rw [r2 _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h14)
      (by rw [r2 _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h24)
      (by rw [r2 _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h83)
      (by rw [m2]; exact hL) hB (by
        have : ∑ q ∈ range (ns.length / 2), (pairCost κ F G H ns γ₀ q + 8) ≤
            ∑ q ∈ range (ns.length / 2), (pairCost κ F G H ns γ₀ q + 331) :=
          Finset.sum_le_sum fun _ _ => by omega
        omega)
  -- 5. the rebuild
  set B' := c4.nreg ALLOC with hB'
  have c4_24 : c4.nreg 160024 = 1 := by
    rw [fr43 _ (not_pairRG (by omega)) (by rw [hAl]; omega),
      s3r _ (bandOK_l41 (by omega) (by omega)) (not_pairRG (by omega)) (by rw [hAl]; omega),
      r2 _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h24
  have c4_80 : c4.nreg 160080 = 2 := by
    rw [fr43 _ (not_pairRG (by omega)) (by rw [hAl]; omega),
      s3r _ (bandOK_l41 (by omega) (by omega)) (not_pairRG (by omega)) (by rw [hAl]; omega),
      r2 _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h80
  have hsum8 : ∑ q ∈ range (ns.length / 2), (pairCost κ F G H ns γ₀ q + 8) + 13 * (pairUp ns t).length ≤
      ∑ q ∈ range (ns.length / 2), (pairCost κ F G H ns γ₀ q + 331) + 13 * ((ns.length + 1) / 2) := by
    have : ∑ q ∈ range (ns.length / 2), (pairCost κ F G H ns γ₀ q + 8) ≤
        ∑ q ∈ range (ns.length / 2), (pairCost κ F G H ns γ₀ q + 331) :=
      Finset.sum_le_sum fun _ _ => by omega
    rw [hlen']; omega
  obtain ⟨c5, k5, e5, hk5, hw5, a5, a5k, b94, hent, hout, fr54, hrr54, hrm54, ho54⟩ :=
    rbS_exec (P := P) hw4 (J := (pairUp ns t).length) (e := ee) rfl c64 c4_24 c4_80
      (fun h => h63) (fun q hq => (hcell q hq).1) (fun q hq h1 => (hcell q hq).2.1 h1)
      (by omega)
  have hLv : LevelAt P c5.nmem (B' + 2 * (pairUp ns t).length) B' hp (pairUp ns t) :=
    levelAt_of_cells hcell hent (fun a ha => hout a (Or.inl ha))
  -- 6. the end
  obtain ⟨c6, k6, e6, hk6, hw6, f66, f14, f33, fr65, hm65, hrr65, hrm65, ho65⟩ :=
    lvFin_exec (P := P) hw5
  have hA6 : c6.nreg ALLOC = B' + 2 * (pairUp ns t).length := by
    rw [fr65 _ (by rw [hAl]; omega) (by rw [hAl]; omega) (by rw [hAl]; omega)]; exact a5
  have mem64 : ∀ a, a < B' → c6.nmem a = c4.nmem a := fun a ha => by
    rw [hm65]; exact hout a (Or.inl ha)
  have hA3 := s3A0
  have f33' : c6.nreg 160033 = t := by
    rw [f33, fr54 _ (by unfold RbRG; omega) (by rw [hAl]; omega),
      fr43 _ (not_pairRG (by omega)) (by rw [hAl]; omega),
      s3r _ (bandOK_l41 (by omega) (by omega)) (not_pairRG (by omega)) (by rw [hAl]; omega)]
    exact t34'
  refine ⟨c6, k1 + (k2 + (k3 + (k4 + (k5 + k6)))),
    .seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq e5 e6)))), ?_, hw6, by omega, by omega,
    by rw [f14, fr54 _ (by unfold RbRG; omega) (by rw [hAl]; omega), c64],
    f33',
    ⟨B', by rw [f66, b94], by rw [hA6], by rw [hA6, hm65]; exact hLv⟩,
    fun a ha => ?_, fun a ha => ?_, by rw [ho65, ho54, o43, s3o, ho2, ho1],
    fun r h1 h2 h3 => ?_, fun r h1 h2 => ?_, ?_, ?_⟩
  · rw [hk1, hk6]; omega
  · rw [mem64 a (by omega), m43 a (by omega), s3m a ha, m2]
  · rw [hrm65, hrm54, rm43, s3rm a ha, hrm2, hrm1]
  · unfold LvRG at h2
    rw [fr65 r (by omega) (by omega) (by omega), fr54 r (fun h => h2 (Or.inr (Or.inl h))) h3,
      fr43 r (by tauto) h3, s3r r h1 (by tauto) h3]
    exact r2 r (by omega) (by unfold PairRG at h2; omega) (by unfold PairRG at h2; omega)
      (by unfold PairRG at h2; omega) (by omega)
  · unfold LvRG at h2
    rw [hrr65, hrr54, rr43, s3rr r h1 (by tauto), hrr2, hrr1]
  · rw [hA6]
    refine X.mono _ _ _ _ _ (show c3.nreg ALLOC ≤ B' + 2 * (pairUp ns t).length by omega)
      (X.local_ _ _ _ _ _ ?_ s3X)
    intro a ha; rw [mem64 a (by omega), m43 a ha]
  · rw [hXc _ _ _ _ _ (fun a ha => by rw [mem64 a (by omega), m43 a ha]) s3X, s3cap, m2]

end proofs

end

end Chazelle.Core.L41
