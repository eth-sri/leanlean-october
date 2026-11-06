module

public import Chazelle.Core.ClusterSplitRam

/-!
# WP-I, part 34: the tail of the split step on the RAM

After the climb has found the centroid face `f` (register `130344`): the marks of the three
corners (`marksF`), the copy of the segment to `TMP` (`copyF`), the three class passes
(`passC`), the release of the separator (`sepMem`), the pushes of the large classes (`pushF`)
and the split counter.

* `StaticEq`: memories agreeing on the static slots (below slot `43` and from slot `49` on);
  `CpMem.of_static`, `MarkMem.of_static`;
* `splitTail_exec`.
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs

@[expose] public section

/-- Memories agreeing on the static slots. -/
def StaticEq (A0 U : ℕ) (m m' : ℕ → ℕ) : Prop :=
  ∀ a, (a < A0 + 43 * U ∨ A0 + 49 * U ≤ a) → m' a = m a

theorem StaticEq.refl (A0 U : ℕ) (m : ℕ → ℕ) : StaticEq A0 U m m := fun _ _ => rfl

theorem StaticEq.trans {A0 U : ℕ} {m1 m2 m3 : ℕ → ℕ} (h1 : StaticEq A0 U m1 m2)
    (h2 : StaticEq A0 U m2 m3) : StaticEq A0 U m1 m3 := fun a ha => (h2 a ha).trans (h1 a ha)

section

variable {W : ℕ} {S : SS} {A0 U : ℕ}

theorem CpMem.of_static (hL : S.Lay A0 U W) {m m' : ℕ → ℕ} (h : StaticEq A0 U m m')
    (hCp : CpMem m W S.bSO S.bSF S.bFPAR S.bFPRE S.bFSZ S.N) :
    CpMem m' W S.bSO S.bSF S.bFPAR S.bFPRE S.bFSZ S.N := by
  have := hL.hFPRE; have := hL.hμU; have := hL.hNU
  have := hL.hSO; have := hL.hSF; have := hL.hFPAR; have := hL.hFSZ
  refine ⟨hCp.wSO, hCp.wSF, hCp.wFP, hCp.wPR, hCp.wSZ, fun x hx => ?_, fun x hx => ?_,
    fun g hg => ?_, fun g hg => ?_⟩
  · rw [h _ (by omega)]; exact hCp.so_lt x hx
  · rw [h _ (by omega)]; exact hCp.sf_lt x hx
  · rw [h _ (by omega)]; exact hCp.fp_lt g hg
  · rw [h _ (by omega), h _ (by omega)]; exact hCp.prsz g hg

end

/-- The marks of the three corners of `f`, as a memory. -/
noncomputable def marksF (m0 : ℕ → ℕ) (S : SS) (lo hi lbot ltop : ℕ) (up : ℕ → ℕ) (f : ℕ) :
    ℕ → ℕ :=
  markStep (markStep (markStep m0 S lo hi lbot ltop up (m0 (S.bVERT + f))) S lo hi lbot ltop up
    (m0 (S.bVERT + m0 (S.bOPP + f)))) S lo hi lbot ltop up (m0 (S.bVERT + m0 (S.bATT + f)))

/-- The copy of the segment to `TMP`. -/
def copyF (m1 : ℕ → ℕ) (S : SS) (lo hi : ℕ) : ℕ → ℕ := fun a =>
  if S.bTMP + lo ≤ a ∧ a < S.bTMP + hi then m1 (S.bACT + (a - S.bTMP)) else m1 a

/-- The split counter. -/
def nspI : Stmt := .instr (.addN 130704 130704 130001)

/-- **The tail of the split step.** -/
def splitTail : Stmt := .seq marksS (.seq copyS (.seq passesS (.seq sepStmt (.seq pushS nspI))))

/-- A pass does not touch `TMP`. -/
theorem passMem_tmp {W : ℕ} {S : SS} {A0 U : ℕ} (_hL : S.Lay A0 U W) {m0 : ℕ → ℕ}
    {sel : ℕ → Prop} {lo hi e : ℕ} (hhi : hi ≤ S.μ) (he : e ≤ hi)
    (hit : ∀ i, lo ≤ i → i < hi → m0 (S.bTMP + i) < S.μ) {x : ℕ}
    (hx : ¬ (S.bACT ≤ x ∧ x < S.bACT + 2 * S.μ) ∧ ¬ (S.bPOS ≤ x ∧ x < S.bPOS + S.μ)) :
    (passMem m0 sel S.bACT S.bPOS S.bTMP lo e (hi - lo)).1 x = m0 x := by
  have := passMem_ptr m0 sel S.bACT S.bPOS S.bTMP lo e (hi - lo)
  refine passMem_other m0 sel (hi - lo) (fun i a b => hit i a (by omega)) ⟨fun h => hx.1 ?_, hx.2⟩
  omega

theorem passC_tmp {W : ℕ} {S : SS} {A0 U : ℕ} (hL : S.Lay A0 U W) {m : ℕ → ℕ} {lo hi f : ℕ}
    (hlh : lo ≤ hi) (hhi : hi ≤ S.μ) (hit : ∀ i, lo ≤ i → i < hi → m (S.bTMP + i) < S.μ) {x : ℕ}
    (hx : ¬ (S.bACT ≤ x ∧ x < S.bACT + 2 * S.μ) ∧ ¬ (S.bPOS ≤ x ∧ x < S.bPOS + S.μ))
    (hsum : (passB m S lo hi f).2 ≤ hi ∧ (passA m S lo hi f).2 ≤ hi) :
    (passC m S lo hi f).1 x = m x := by
  have := hL.hACT; have := hL.hPOS; have := hL.hTMP; have := hL.hμU
  have tA : ∀ i, lo ≤ i → i < hi → (passA m S lo hi f).1 (S.bTMP + i) = m (S.bTMP + i) :=
    fun i h1 h2 => passMem_tmp hL hhi hlh hit ⟨by omega, by omega⟩
  have tB : ∀ i, lo ≤ i → i < hi → (passB m S lo hi f).1 (S.bTMP + i) = m (S.bTMP + i) := by
    intro i h1 h2
    unfold passB
    rw [passMem_tmp hL hhi hsum.2 (fun i a b => by rw [tA i a b]; exact hit i a b)
      ⟨by omega, by omega⟩]
    exact tA i h1 h2
  unfold passC
  rw [passMem_tmp hL hhi hsum.1 (fun i a b => by rw [tB i a b]; exact hit i a b) hx]
  unfold passB
  rw [passMem_tmp hL hhi hsum.2 (fun i a b => by rw [tA i a b]; exact hit i a b) hx]
  exact passMem_tmp hL hhi hlh hit hx

section proofs

variable {P : Polygon} {W : ℕ}

/-- **The tail of the split step.** -/
theorem splitTail_exec {S : SS} {A0 U : ℕ} {c : Config} (hw : WordsBounded W c)
    (hR : S.Regs c) (hL : S.Lay A0 U W) {lo hi lbot ltop f tp nsp : ℕ} {up : ℕ → ℕ}
    (hlo : c.nreg 130300 = lo) (hhi : c.nreg 130301 = hi) (hbot : c.nreg 130609 = lbot)
    (htop : c.nreg 130610 = ltop) (hf : c.nreg 130344 = f) (htp : c.nreg 130701 = tp)
    (hnsp : c.nreg 130704 = nsp) (hlh : lo ≤ hi) (hhiμ : hi ≤ S.μ) (hfN : f < S.N)
    (hM : MarkMem c.nmem W S.bLEV S.bUPT S.bPOW S.L S.bPV S.bPOS S.bDF S.μ up)
    (hvert : ∀ d, d < S.N → c.nmem (S.bVERT + d) < S.μ)
    (hopp : c.nmem (S.bOPP + f) < S.N) (hatt : c.nmem (S.bATT + f) < S.N)
    (hCp : CpMem c.nmem W S.bSO S.bSF S.bFPAR S.bFPRE S.bFSZ S.N)
    (hfp : c.nmem (S.bFP + f) < S.N) (hfirst : ∀ v, v < S.μ → c.nmem (S.bFIRST + v) < S.N)
    (hact : ∀ i, lo ≤ i → i < hi → c.nmem (S.bACT + i) < S.μ)
    (hsum : let m2 := copyF (marksF c.nmem S lo hi lbot ltop up f) S lo hi
      cntS (SelI m2 S f f) lo hi + cntS (SelI m2 S (2 * S.N + m2 (S.bFP + f)) f) lo hi +
        cntS (SelI m2 S (S.N + f) f) lo hi ≤ hi - lo)
    (hwS : S.bSTK + tp + 6 ≤ W) (hnspW : nsp + 1 ≤ W) :
    let m2 := copyF (marksF c.nmem S lo hi lbot ltop up f) S lo hi
    let s0 := SelI m2 S f f
    let s1 := SelI m2 S (2 * S.N + m2 (S.bFP + f)) f
    let s2 := SelI m2 S (S.N + f) f
    let e1 := lo + cntS s0 lo hi
    let e2 := e1 + cntS s1 lo hi
    let e3 := e2 + cntS s2 lo hi
    ∃ c' k, Exec P W splitTail c c' k ∧
      k ≤ 3 * (12 * S.L + 12 * (ltop + 1 - lbot) + 34) + 8 * (hi - lo) + 7 +
        (3 * (32 * (hi - lo) + 48) + 20) + (15 * (hi - lo) + 3) + 27 + 1 ∧ WordsBounded W c' ∧
      (c'.nmem, c'.nreg 130701) = pushF S.bSTK S.s e2 e3 (pushF S.bSTK S.s e1 e2
        (pushF S.bSTK S.s lo e1 (sepMem (passC m2 S lo hi f).1 S.bTMP S.bPOS S.bDF S.μ lo
          (hi - lo), tp))) ∧
      c'.nreg 130704 = nsp + 1 ∧ (∀ r, ¬ SplitRG r → r ≠ 130701 → r ≠ 130704 →
        c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  intro m2 s0 s1 s2 e1 e2 e3
  have := hL.hACT; have := hL.hPOS; have := hL.hTMP; have := hL.hDF; have := hL.hμU
  have := hL.hNU; have := hL.hVERT; have := hL.hOPP; have := hL.hATT; have := hL.hW
  have := hL.hFIRST; have := hL.hLEV; have := hL.hPV; have := hL.hFP; have := hL.hSTK
  have := hL.hμN
  have hLU0 : 0 ≤ S.L * U := Nat.zero_le _
  -- the marks
  obtain ⟨c1, k1, x1, hk1, hw1, hm1, hr1, h1f, h1lo, h1hi, hrr1, hrm1, ho1⟩ :=
    marksS_exec (P := P) hw hR hlo hhi hbot htop hf hM rfl rfl rfl (hvert f (by omega))
      (hvert _ hopp) (hvert _ hatt) (by omega) (by omega) (by omega)
      (by have := hvert f (by omega); omega) (by omega)
      (fun a ha => by
        rcases ha with rfl | rfl | rfl | rfl | rfl <;> omega)
  have hmu := hM.up_lt
  have hm1' : c1.nmem = marksF c.nmem S lo hi lbot ltop up f := hm1
  have hk1out : ∀ a, ¬ (S.bDF ≤ a ∧ a < S.bDF + S.μ) → c1.nmem a = c.nmem a := by
    intro a ha
    rw [hm1', marksF, markStep_other hmu (hvert _ hatt) ha, markStep_other hmu (hvert _ hopp) ha,
      markStep_other hmu (hvert f (by omega)) ha]
  have hR1 := hR.of_frame hr1
  -- the copy
  obtain ⟨c2, k2, x2, hk2, hw2, hm2, hr2, hg2, hrr2, hrm2, ho2⟩ := copyS_exec (P := P) hw1 hR1 hL
    h1lo h1hi hlh hhiμ
  have hm2' : c2.nmem = m2 := by
    funext a
    rw [hm2 a]
    show _ = copyF (marksF c.nmem S lo hi lbot ltop up f) S lo hi a
    unfold copyF; rw [hm1']
  have hk2out : ∀ a, ¬ (S.bDF ≤ a ∧ a < S.bDF + S.μ) → ¬ (S.bTMP ≤ a ∧ a < S.bTMP + S.μ) →
      c2.nmem a = c.nmem a := by
    intro a h1 h2
    rw [hm2 a, ite_eq_right (by omega)]; exact hk1out a h1
  have hst2 : StaticEq A0 U c.nmem c2.nmem := fun a ha => hk2out a (by omega) (by omega)
  have htmp2 : ∀ i, lo ≤ i → i < hi → c2.nmem (S.bTMP + i) = c.nmem (S.bACT + i) := by
    intro i h1 h2
    rw [hm2, ite_eq_left (by omega), show S.bTMP + i - S.bTMP = i by omega]
    exact hk1out _ (by omega)
  have hR2 := hR1.of_frame hr2
  -- the passes
  have hfp2 : c2.nmem (S.bFP + f) = c.nmem (S.bFP + f) := hst2 _ (by omega)
  obtain ⟨c3, k3, x3, hk3, hw3, hm3, h3e0, h3e1, h3e2, h3e3, hr3, h3f, h3lo, h3hi, hrr3, hrm3,
    ho3⟩ := passesS_exec (P := P) hw2 hR2 hL (by rw [hg2 _ (by omega)]; exact h1lo)
    (by rw [hg2 _ (by omega)]; exact h1hi) (by rw [hg2 _ (by omega)]; exact h1f) hfN
    (by rw [hfp2]; exact hfp) (CpMem.of_static hL hst2 hCp) hlh hhiμ
    (fun i h1 h2 => by rw [htmp2 i h1 h2]; exact hact i h1 h2)
    (fun v hv => by rw [hst2 _ (by omega)]; exact hfirst v hv) (by rw [hm2']; exact hsum)
  rw [hm2'] at hm3 h3e1 h3e2 h3e3
  have hR3 := hR2.of_frame hr3
  -- the pass pointers
  have hsum' : cntS s0 lo hi + cntS s1 lo hi + cntS s2 lo hi ≤ hi - lo := hsum
  have hpA : (passA m2 S lo hi f).2 = e1 := by
    show (passMem m2 s0 S.bACT S.bPOS S.bTMP lo lo (hi - lo)).2 = e1
    rw [passMem_ptr_eq, show lo + (hi - lo) = hi by omega]
  have hpB : (passB m2 S lo hi f).2 = e2 := by
    unfold passB; rw [hpA, passMem_ptr_eq, show lo + (hi - lo) = hi by omega]
  have hit2 : ∀ i, lo ≤ i → i < hi → m2 (S.bTMP + i) < S.μ := fun i h1 h2 => by
    rw [← hm2', htmp2 i h1 h2]; exact hact i h1 h2
  -- `TMP` after the passes
  have htmp3 : ∀ i, lo ≤ i → i < hi → c3.nmem (S.bTMP + i) = c.nmem (S.bACT + i) := by
    intro i h1 h2
    rw [hm3, passC_tmp hL hlh hhiμ hit2 ⟨by omega, by omega⟩ ⟨by rw [hpB]; omega,
      by rw [hpA]; omega⟩, ← hm2', htmp2 i h1 h2]
  -- the release of the separator
  obtain ⟨c4, k4, x4, hk4, hw4, hm4, hr4, hrr4, hrm4, ho4⟩ := sepStmt_exec (P := P) hw3 hR3.one
    h3lo h3hi hR3.aTMP hR3.aPOS hR3.aDF hR3.rμ hlh
    (fun i h1 h2 => by rw [htmp3 i h1 h2]; exact hact i h1 h2) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  -- the pushes
  have g4 : ∀ r, r = 130670 ∨ r = 130671 ∨ r = 130672 ∨ r = 130673 ∨ r = 130701 ∨ r = 130704 →
      c4.nreg r = c3.nreg r := fun r hr => hr4 r (by unfold SepRG; omega)
  have htp3 : c3.nreg 130701 = tp := by
    rw [hr3 _ (by unfold SplitRG; omega), hr2 _ (by unfold SplitRG; omega),
      hr1 _ (by unfold SplitRG; omega)]; exact htp
  have hnsp3 : c3.nreg 130704 = nsp := by
    rw [hr3 _ (by unfold SplitRG; omega), hr2 _ (by unfold SplitRG; omega),
      hr1 _ (by unfold SplitRG; omega)]; exact hnsp
  have hR4 := hR3.of_frame (fun r hr => hr4 r (by unfold SepRG; unfold SplitRG at hr; omega))
  obtain ⟨c5, k5, x5, hk5, hw5, hq5, hr5, hrr5, hrm5, ho5⟩ := pushS_exec (P := P) hw4 hR4
    ((g4 _ (by omega)).trans h3e0) ((g4 _ (by omega)).trans h3e1)
    ((g4 _ (by omega)).trans h3e2) ((g4 _ (by omega)).trans h3e3)
    ((g4 _ (by omega)).trans htp3) hwS
  -- the counter
  have h5n : c5.nreg 130704 = nsp := by
    rw [hr5 _ (by omega) (by omega) (by omega), g4 _ (by omega)]; exact hnsp3
  have h51 : c5.nreg 130001 = 1 := (hr5 _ (by omega) (by omega) (by omega)).trans hR4.one
  have x6 := Exec.addN (P := P) hw5 130704 130704 130001 (by rw [h5n, h51]; omega)
  have hm4' : c4.nmem = sepMem (passC m2 S lo hi f).1 S.bTMP S.bPOS S.bDF S.μ lo (hi - lo) := by
    rw [hm4, hm3]
  refine ⟨_, k1 + (k2 + (k3 + (k4 + (k5 + 1)))), .seq x1 (.seq x2 (.seq x3 (.seq x4 (.seq x5
    x6)))), by omega, x6.wb_right, ?_, by simp [h5n, h51], fun r hr h1 h2 => ?_, ?_, ?_, ?_⟩
  · show (c5.nmem, upd c5.nreg 130704 (c5.nreg 130704 + c5.nreg 130001) 130701) = _
    rw [Machine.upd_other _ _ _ (by omega), hq5, hm4']
  · simp only [Machine.upd_apply]
    rw [ite_eq_right h2, hr5 r h1 (by unfold SplitRG at hr; omega) (by unfold SplitRG at hr; omega),
      hr4 r (by unfold SepRG; unfold SplitRG at hr; omega), hr3 r hr, hr2 r hr, hr1 r hr]
  · show c5.rreg = c.rreg; rw [hrr5, hrr4, hrr3, hrr2, hrr1]
  · show c5.rmem = c.rmem; rw [hrm5, hrm4, hrm3, hrm2, hrm1]
  · show c5.output = c.output; rw [ho5, ho4, ho3, ho2, ho1]

end proofs

end

end Chazelle.Core.Cluster
