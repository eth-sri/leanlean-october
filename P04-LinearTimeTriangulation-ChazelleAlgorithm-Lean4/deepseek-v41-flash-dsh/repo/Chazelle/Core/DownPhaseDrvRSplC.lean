module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvRSplB

/-!
# Down-phase driver (RAM side): the splice, part 2 (records, buckets, sorted new codes)

`splB_exec`: `spl2 ; phaseAS ; spl3 ; bktS ; r210050 := 0 ; bsLoop` writes the event records of
`L'` and a `codeLe`-sorted permutation of the new event codes `2K … 2K' - 1` (array at
`r210048`).
-/

namespace Chazelle.Core

namespace DrvR

open Machine Machine.Stmt Programs SortL BuildRam SignK

@[expose] public section

theorem wrM_spl2 : wrM (fun r => decide (40000 ≤ r ∧ r ≤ 40002)) spl2 = true := ⌖

theorem notin_rot {x a b c : ℕ} (h : x ∉ ({a, b, c} : Finset ℕ)) : x ∉ ({c, a, b} : Finset ℕ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢; tauto

theorem band4_notin {r : ℕ} (h : bandOf r ∉ ({bSort, bSign, bBuild} : Finset ℕ)) :
    r < 40000 ∨ 50000 ≤ r := by
  simp only [Finset.mem_insert, Finset.mem_singleton, bandOf, bSort, bSign, bBuild] at h; omega
theorem wrM_spl3 : wrM (fun r => decide (210031 ≤ r ∧ r ≤ 210033)) spl3 = true := ⌖

section exec

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 2000000 in
/-- **The records of `L'` and the bucket arguments.** -/
theorem splB1_exec (hWn : hostWords P.n ≤ W) (c : Config) (hw : WordsBounded W c)
    {D B' K K₂ A : ℕ} {M : Model} {L' : List (ℕ × ℕ × ℕ)}
    (h01 : c.nreg 210001 = D) (h26 : c.nreg 210026 = B') (h25 : c.nreg 210025 = K + K₂)
    (h27 : c.nreg 210027 = 2 * K) (h28 : c.nreg 210028 = 2 * K₂)
    (h23 : c.nreg 210023 = A) (hlen : L'.length = K + K₂)
    (hok : ChordTriplesOK M (Qof P) L') (hCL : ChordListAt c.nmem B' L')
    (hA : c.nreg ALLOC = B' + 3 * (K + K₂))
    (hroom : c.nreg ALLOC + 32 * (K + K₂) + 22 ≤ W) :
    ∃ c' k, Exec P W (.seq spl2 (.seq DownNF.phaseAS spl3)) c c' k ∧ k ≤ 32 * (K + K₂) + 24 ∧
      WordsBounded W c' ∧
      c'.nreg 40000 = D ∧ c'.nreg 42000 = c.nreg ALLOC ∧ c'.nreg 42001 = 2 * (K + K₂) ∧
      c'.nreg 210031 = 2 * K₂ ∧ c'.nreg 210032 = A ∧ c'.nreg 210033 = 2 * K ∧
      c'.nreg ALLOC = c.nreg ALLOC + 10 * (K + K₂) ∧
      RecsAt c'.nmem (c.nreg ALLOC) L' ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      (∀ a, c.nreg ALLOC + 10 * (K + K₂) ≤ a → c'.nmem a = c.nmem a ∨ True) ∧
      (∀ r, bandOf r ∉ ({bSort, bSign, bBuild} : Finset ℕ) → (r < 210031 ∨ 210033 < r) →
        r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      (∀ r, bandOf r ∉ ({bSort, bSign, bBuild} : Finset ℕ) → c'.rreg r = c.rreg r) ∧
      (∀ a, a < c.nreg ALLOC → c'.rmem a = c.rmem a) ∧ c'.output = c.output := by
  -- the records' arguments
  obtain ⟨c₁, k₁, e₁, hk₁, v0, v1, v2, hm₁⟩ : ∃ c₁ k₁, Exec P W spl2 c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 40000 = D ∧ c₁.nreg 40001 = B' ∧ c₁.nreg 40002 = K + K₂ ∧ c₁.nmem = c.nmem := by
    unfold spl2
    exec_block
    refine ⟨rfl, ?_, ?_, ?_, rfl⟩ <;> config_simp <;> (try simp only [h01, h26, h25])
  have f₁ := exec_frameM e₁ wrM_spl2
  have g₁ : ∀ r, (r < 40000 ∨ 40002 < r) → c₁.nreg r = c.nreg r := fun r hr =>
    f₁.1 r (by simp only [decide_eq_false_iff_not]; omega)
  have hA₁' : c₁.nreg ALLOC = c.nreg ALLOC := g₁ _ (⌖)
  -- the records
  obtain ⟨c₂, k₂, e₂, hk₂, w₂, F₂, d1, d2, d3, -, -, -, -, hrec, -, hA₂⟩ :=
    DownNF.phaseAS_exec (P := P) hWn c₁ e₁.wb_right (M := M) (L := L') (D := D) (B := B')
      (SE := c₁.nreg 40004) hok (by rw [hm₁]; exact hCL) (Ρ hA₁', hA, hlen) v0 v1
      (Ρ v2, hlen) rfl (by rw [hA₁', hlen]; omega)
  rw [hA₁'] at hrec hA₂ d2
  rw [hlen] at hA₂ hk₂ d3
  have b21 : ∀ r, 210000 ≤ r → r < 220000 → bandOf r ∉ ({bBuild, bSort, bSign} : Finset ℕ) := by
    intro r h1 h2
    ϴ Finset.mem_insert, Finset.mem_singleton, bandOf, bSort, bSign, bBuild
    omega
  have g₂ : ∀ r, 210000 ≤ r → r < 220000 → c₂.nreg r = c.nreg r := fun r h1 h2 => by
    rw [F₂.1 r (b21 r h1 h2) (by unfold ALLOC; omega), g₁ r (⋄)]
  -- the bucket arguments
  obtain ⟨c₃, k₃, e₃, hk₃, u31, u32, u33, hm₃⟩ : ∃ c₃ k₃, Exec P W spl3 c₂ c₃ k₃ ∧ k₃ = 3 ∧
      c₃.nreg 210031 = 2 * K₂ ∧ c₃.nreg 210032 = A ∧ c₃.nreg 210033 = 2 * K ∧
      c₃.nmem = c₂.nmem := by
    have a28 := g₂ 210028 (⊛) (⊛)
    have a23 := g₂ 210023 (⊛) (⊛)
    have a27 := g₂ 210027 (⊛) (⊛)
    unfold spl3
    exec_block
    refine ⟨rfl, ?_, ?_, ?_, rfl⟩ <;> config_simp
    · Ξ a28, h28
    · Ξ a23, h23
    · Ξ a27, h27
  have f₃ := exec_frameM e₃ wrM_spl3
  have g₃ : ∀ r, (r < 210031 ∨ 210033 < r) → c₃.nreg r = c₂.nreg r := fun r hr =>
    f₃.1 r (by simp only [decide_eq_false_iff_not]; omega)
  refine ⟨c₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), ⋄, e₃.wb_right,
    by rw [g₃ _ (⌖)]; exact d1, by rw [g₃ _ (by decide)]; exact d2,
    by rw [g₃ _ (⌖)]; exact d3, u31, u32, u33, by rw [g₃ _ (by decide)]; exact hA₂,
    by rw [hm₃]; exact hrec, fun a ha => ?_, fun _ _ => Or.inr trivial, fun r hr hr' hra => ?_,
    fun r hr => ?_, fun a ha => ?_, ?_⟩
  · Ξ hm₃, F₂.2.2.1 a (by rw [hA₁']; exact ha), hm₁
  · Ξ g₃ r hr', F₂.1 r (notin_rot hr) hra
    exact f₁.1 r (by simp only [decide_eq_false_iff_not]; have := band4_notin hr; omega)
  · rw [exec_frameM2 e₃ (BN := fun r => decide (210031 ≤ r ∧ r ≤ 210033)) (BR := fun _ => false)
      (⌖) r rfl, F₂.2.1 r (notin_rot hr)]
    exact f₁.2.1 r (by simp only [decide_eq_false_iff_not]; have := band4_notin hr; omega)
  · Ξ f₃.2.2.1, F₂.2.2.2.1 a (by rw [hA₁']; exact ha), f₁.2.2.1
  · Ξ f₃.2.2.2, F₂.2.2.2.2.1, f₁.2.2.2

/-- The cost of the buckets part. -/
noncomputable def splB2Cost (bk : ℕ → ℕ) (n A : ℕ) : ℕ :=
  21 * (A + 1) + 21 * n + 31 + ∑ b ∈ Finset.range (A + 1), (bsCost bk n b + 2) + 2

set_option maxHeartbeats 4000000 in
/-- **The sorted new codes, from the records.** -/
theorem splB2_exec (hG : GoodEnv P) (hWn : hostWords P.n ≤ W) (c : Config)
    (hw : WordsBounded W c) {D T BB n A base : ℕ} {M : Model} {L' : List (ℕ × ℕ × ℕ)}
    {bk : ℕ → ℕ}
    (h22 : c.nreg 210022 = BB) (h31 : c.nreg 210031 = n) (h32 : c.nreg 210032 = A)
    (h33 : c.nreg 210033 = base) (h40 : c.nreg 40000 = D) (h42 : c.nreg 42000 = T)
    (h42' : c.nreg 42001 = 2 * L'.length)
    (hwf : ModelDescWF P (c.nreg ALLOC) c.nmem D) (hM : ModelDescAt c.nmem D (Qof P) M)
    (hok : ChordTriplesOK M (Qof P) L') (hrec : RecsAt c.nmem T L')
    (hT : T + 8 * L'.length ≤ c.nreg ALLOC) (hcodes : base + n ≤ 2 * L'.length)
    (hBB : BB + n ≤ c.nreg ALLOC)
    (hbkd : ∀ q, q < n → c.nmem (BB + q) = bk q) (hbk : ∀ q, q < n → bk q ≤ A)
    (hmono : ∀ q q', q < n → q' < n → bk q < bk q' →
      BuildNF.codeLe M (Qof P) L' (base + q) (base + q'))
    (hroom : c.nreg ALLOC + splB2Cost bk n A + 1 ≤ W) :
    ∃ c' k, Exec P W (.seq bktS (.seq (.instr (.constN 210050 0)) bsLoop)) c c' k ∧
      k ≤ splB2Cost bk n A ∧ WordsBounded W c' ∧
      c'.nreg 210048 = c.nreg ALLOC + (A + 1) + (A + 1) ∧
      (seg c'.nmem (c'.nreg 210048) n).Perm ((List.range n).map (base + ·)) ∧
      (seg c'.nmem (c'.nreg 210048) n).Pairwise (BuildNF.codeLe M (Qof P) L') ∧
      c'.nreg 210048 + n ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + splB2Cost bk n A ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      c'.nreg 40000 = D ∧ c'.nreg 42000 = T ∧ c'.nreg 42001 = 2 * L'.length ∧
      c'.nreg 210034 = 1 ∧
      (∀ r, bandOf r ∉ ({bSort, bSign, bBuild} : Finset ℕ) → (r < 210034 ∨ 210059 < r) →
        r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      (∀ r, bandOf r ∉ ({bSort, bSign, bBuild} : Finset ℕ) → (r < 210034 ∨ 210059 < r) →
        c'.rreg r = c.rreg r) ∧
      (∀ a, a < c.nreg ALLOC → c'.rmem a = c.rmem a) ∧ c'.output = c.output := by
  set A₂ := c.nreg ALLOC with hA₂
  obtain ⟨c₄, k₄, e₄, hk₄, b36, b37, b48, bA, b34, b39, bseg, bst, bcn, blow, bfr, brr', brm, bout⟩ :=
    bktS_exec (P := P) c hw (BB := BB) (n := n) (A := A) (base := base) (bk := bk) h22 h31 h32 h33
      hBB hbkd hbk (by unfold splB2Cost at hroom; omega) (⋄)
  have w₄ := e₄.wb_right
  have e₅ := Exec.constN (P := P) w₄ 210050 0 (Nat.zero_le _)
  set c₅ : Config := { c₄ with nreg := upd c₄.nreg 210050 0 } with hc₅
  have g₅ : ∀ r, r ≠ 210050 → c₅.nreg r = c₄.nreg r := fun r hr => by rw [hc₅]; simp [hr]
  have bkf : ∀ r, Bbkt r = false → r ≠ 210050 → c₅.nreg r = c.nreg r := fun r hr h50 => by
    Ξ g₅ r h50, bfr r hr
  have hlow5 : ∀ a, a < A₂ → c₅.nmem a = c.nmem a := fun a ha => blow a ha
  have Ebs : BsEnv P W c₅.nmem bk n A base A₂ (A₂ + (A + 1)) (A₂ + (A + 1) + (A + 1)) D T M L' :=
    { good := hG, hw := hWn, bkA := hbk, hS := rfl, hR := rfl,
      cnt := fun b hb => bcn b hb, st := fun b hb => bst b hb,
      wf := (desc_agree hwf hM (m' := c₅.nmem) fun a ha => hlow5 a ha).2,
      desc := (desc_agree hwf hM (m' := c₅.nmem) fun a ha => hlow5 a ha).1,
      ok := hok,
      recs := fun q hq => by
        obtain ⟨r1, r2, r3, r4⟩ := hrec q hq
        exact ⟨by rw [hlow5 _ (⋄)]; exact r1, by rw [hlow5 _ (by omega)]; exact r2,
          by rw [hlow5 _ (⋄)]; exact r3, by rw [hlow5 _ (by omega)]; exact r4⟩
      hT := hT, codes := hcodes }
  have Ibs : BsI P W c₅ c₅.nmem bk n A base A₂ (A₂ + (A + 1)) (A₂ + (A + 1) + (A + 1)) D T M L'
      0 c₅ :=
    { wb := e₅.wb_right, r34 := by rw [g₅ _ (⌖), b34], r36 := by rw [g₅ _ (by decide), b36],
      r37 := by rw [g₅ _ (⌖), b37], r39 := by rw [g₅ _ (by decide), b39],
      r48 := by rw [g₅ _ (⌖), b48], r50 := by rw [hc₅]; simp,
      r40 := by rw [bkf _ (⌖) (by decide), h40],
      r42 := by rw [bkf _ (⌖) (by decide), h42],
      r42' := by rw [bkf _ (⌖) (by decide), h42'],
      alloc := by rw [g₅ _ (⌖), bA],
      low := fun _ _ => rfl, done := fun b hb => absurd hb (⋄),
      todo := fun b _ hb => seg_bkt hbk bseg hb,
      fr := fun _ _ _ _ => rfl, r43 := fun _ _ _ => rfl, rr := fun _ _ _ => rfl,
      rm := fun _ _ => rfl, out := rfl }
  have hle : ∑ b ∈ Finset.range (A + 1), bsCost bk n b ≤
      ∑ b ∈ Finset.range (A + 1), (bsCost bk n b + 2) :=
    Finset.sum_le_sum fun b _ => ⋄
  have hroom' : c₅.nreg ALLOC + (∑ b ∈ Finset.range (A + 1), bsCost bk n b) + 1 ≤ W := by
    rw [g₅ _ (⌖), bA]; unfold splB2Cost at hroom; omega
  obtain ⟨c₆, k₆, e₆, I₆, hk₆, hA₆⟩ := bsLoop_exec Ebs Ibs hroom'
  obtain ⟨hperm, hsort⟩ := bs_result Ebs I₆ hmono
  have hc5A : c₅.nreg ALLOC = A₂ + (A + 1) + (A + 1) + n := by rw [g₅ _ (⌖), bA]
  refine ⟨c₆, k₄ + (1 + k₆), .seq e₄ (.seq e₅ e₆), by unfold splB2Cost; omega, I₆.wb,
    I₆.r48, by rw [I₆.r48]; exact hperm, by rw [I₆.r48]; exact hsort,
    by rw [I₆.r48]; have := I₆.alloc; omega, by unfold splB2Cost; omega,
    fun a ha => by rw [I₆.low a (⋄), hlow5 a ha], I₆.r40, I₆.r42, I₆.r42', I₆.r34,
    fun r hr hr' hra => ?_, fun r hr hr' => ?_, fun a ha => ?_, ?_⟩
  · have hb : Bbl r = false := by simp only [Bbl, decide_eq_false_iff_not]; omega
    rw [I₆.fr r hr hb hra, g₅ r (⋄), bfr r (by
      simp only [Bbkt, Bool.or_eq_false_iff, decide_eq_false_iff_not]; exact ⟨⋄, hra⟩)]
  · have hb : Bbl r = false := by simp only [Bbl, decide_eq_false_iff_not]; omega
    Ξ I₆.rr r hr hb, show c₅.rreg = c₄.rreg from rfl, brr'
  · rw [I₆.rm a (⋄), show c₅.rmem = c₄.rmem from rfl, brm]
  · Ξ I₆.out, show c₅.output = c₄.output from rfl, bout

end exec

end

end DrvR

end Chazelle.Core
