module

public import Chazelle.Golf

public import Chazelle.Golf

public import Chazelle.Core.ClusterSFacts

/-!
# WP-I, part 61: the registers of the split driver

`regsS` loads the registers of `SS.Regs (ssOf g)` from the global registers (a block of copies,
`2N`, and a loop of `L` steps for `bUP + L N` and `bUPT + L μ`) and zeroes the counter `130704`
of separator vertices.
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs

@[expose] public section

/-- A block of register copies. -/
def copies (l : List (ℕ × ℕ)) : Stmt := block (l.map (fun p => .copyN p.1 p.2))

/-- The copies of the driver registers (destination, source). -/
def regCopies : List (ℕ × ℕ) :=
  [(130320, 130073), (130321, 130030), (130322, 130059), (130323, 130070), (130324, 130017),
   (130325, 130058), (130326, 130085), (130327, 130085), (130328, 130014), (130345, 130017),
   (130601, 130033), (130602, 130084), (130603, 130070), (130604, 130017), (130605, 130036),
   (130606, 130074), (130607, 130078), (130608, 130011), (130620, 130084), (130632, 130041),
   (130633, 130047), (130634, 130056), (130635, 130059), (130636, 130058), (130650, 130075),
   (130651, 130073), (130652, 130074), (130653, 130078), (130654, 130030), (130655, 130059),
   (130674, 130016), (130675, 130011), (130680, 130037), (130682, 130014), (130692, 130069),
   (130694, 130067), (130695, 130068), (130696, 130023), (130697, 130021), (130698, 130039),
   (130700, 130076), (130704, 130009), (130880, 130009)]

/-- One step of the products `L N` and `L μ`. -/
def mulBody : Stmt := block [.addN 130327 130327 130014, .addN 130620 130620 130011,
  .addN 130880 130880 130001]

/-- **The driver registers.** -/
def regsS : Stmt := .seq (copies regCopies) (.seq (.instr (.addN 130681 130014 130014))
  (.whileLtN 130880 130017 mulBody))

/-- The registers written by `regsS`. -/
def RegRG (r : ℕ) : Prop := 130300 ≤ r ∧ r ≤ 130889

section proofs

variable {P : Polygon} {W : ℕ}

/-- **A block of copies** with sources below `b ≤` destinations, destinations distinct. -/
theorem copies_exec {c : Config} (hw : WordsBounded W c) (l : List (ℕ × ℕ)) {b : ℕ}
    (hsep : ∀ p ∈ l, p.2 < b ∧ b ≤ p.1) (hnd : (l.map Prod.fst).Nodup) :
    ∃ c', Exec P W (copies l) c c' l.length ∧ WordsBounded W c' ∧
      (∀ p ∈ l, c'.nreg p.1 = c.nreg p.2) ∧ (∀ r, (∀ p ∈ l, p.1 ≠ r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  induction l generalizing c with
  | nil => exact ⟨c, .skip hw, hw, fun p hp => by simp at hp, fun r _ => rfl, rfl, rfl, rfl, rfl⟩
  | cons p t ih =>
    have e1 := Exec.copyN (P := P) hw p.1 p.2
    set c1 := { c with nreg := upd c.nreg p.1 (c.nreg p.2) } with hc1
    ϴ' List.map_cons, List.nodup_cons, List.mem_map at hnd
    obtain ⟨c', e', hw', h1, h2, hm, hr, hrm, ho⟩ := ih e1.wb_right
      (fun q hq => hsep q (List.mem_cons_of_mem _ hq)) hnd.2
    have hp := hsep p (List.mem_cons_self)
    refine ⟨c', ?_, hw', fun q hq => ?_, fun r hr' => ?_, hm, hr, hrm, ho⟩
    · show Exec P W (.seq (.instr (.copyN p.1 p.2)) (copies t)) c c' (t.length + 1)
      rw [Nat.add_comm]; exact .seq e1 e'
    · rcases List.mem_cons.mp hq with rfl | hq
      · Ξ h2 _ (fun q' hq' h => hnd.1 ⟨q', hq', h⟩)
        Θ c1
      · have := hsep q (List.mem_cons_of_mem _ hq)
        rw [h1 q hq]; ϴ c1
        Ξ Machine.upd_other _ _ _ (⋄)
    · Ξ h2 r (fun q hq => hr' q (List.mem_cons_of_mem _ hq))
      ϴ c1
      Ξ Machine.upd_other _ _ _ (fun h => hr' p List.mem_cons_self h.symm)


/-- **The driver registers.** -/
theorem regsS_exec {g : GV} {c : Config} (hw : WordsBounded W c) (hG : GR g c)
    (hW : g.END ≤ W) :
    ∃ c' k, Exec P W regsS c c' k ∧ k ≤ 5 * g.L + 50 ∧ WordsBounded W c' ∧
      (ssOf g).Regs c' ∧ c'.nreg 130704 = 0 ∧ (∀ r, ¬ RegRG r → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hU := g.U_ge; have hE := g.END_eq; have hLU := g.L_le_U
  have hLN : g.L * g.N ≤ g.L * g.U := Nat.mul_le_mul_left _ (⋄)
  have hLμ : g.L * g.μ ≤ g.L * g.U := Nat.mul_le_mul_left _ (⋄)
  unfold regsS
  obtain ⟨c1, e1, hw1, h1, h2, hm1, hr1, hrm1, ho1⟩ := copies_exec (P := P) hw regCopies
    (b := 130300) (⌖) (⌖)
  have g1 : ∀ r, r < 130300 → c1.nreg r = c.nreg r := fun r hr =>
    h2 r (fun p hp h => by have := ((show ∀ p ∈ regCopies, 130300 ≤ p.1 by decide) p hp); omega)
  have hG1 : GR g c1 := hG.frame (fun r hr => g1 r (by unfold GRReg at hr; omega))
  have cp : ∀ d s, (d, s) ∈ regCopies → c1.nreg d = c.nreg s := fun d s h => h1 _ h
  have e2 := Exec.addN (P := P) hw1 130681 130014 130014 (by rw [hG1.rN]; omega)
  set c2 := { c1 with nreg := upd c1.nreg 130681 (c1.nreg 130014 + c1.nreg 130014) } with hc2
  have k12 : ∀ r, r ≠ 130681 → c2.nreg r = c1.nreg r := fun r h => by
    simp only [c2]; Ξ Machine.upd_other _ _ _ h
  have hG2 : GR g c2 := hG1.frame (fun r hr => k12 r (by unfold GRReg at hr; omega))
  have h681 : c2.nreg 130681 = 2 * g.N := by
    simp only [c2, Machine.upd_same]; rw [hG1.rN]; ring
  obtain ⟨c3, k3, e3, hk3, ⟨hw3, h880, hL3, h327, h620, hk23, hm3, hr3, hrm3, ho3⟩⟩ := forN (P := P) (W := W)
    (ri := 130880) (rn := 130017) (body := mulBody)
    (fun j c' => WordsBounded W c' ∧ c'.nreg 130880 = j ∧ c'.nreg 130017 = g.L ∧
      c'.nreg 130327 = g.A0 + 54 * g.U + g.L * g.U + j * g.N ∧
      c'.nreg 130620 = g.A0 + 54 * g.U + j * g.μ ∧
      (∀ r, r ≠ 130327 → r ≠ 130620 → r ≠ 130880 → c'.nreg r = c2.nreg r) ∧
      c'.nmem = c2.nmem ∧ c'.rreg = c2.rreg ∧ c'.rmem = c2.rmem ∧ c'.output = c2.output)
    g.L 3 (fun j c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j c4 hj ⟨hw4, h4i, h4n, h4a, h4b, h4r, h4m, h4rr, h4rm, h4o⟩ => by
      have hN4 : c4.nreg 130014 = g.N := by rw [h4r _ (⋄) (⋄) (⋄)]; exact hG2.rN
      have hμ4 : c4.nreg 130011 = g.μ := by rw [h4r _ (⋄) (⋄) (⋄)]; exact hG2.rμ
      have h14 : c4.nreg 130001 = 1 := by rw [h4r _ (⋄) (⋄) (⋄)]; exact hG2.one
      have hjN : (j + 1) * g.N ≤ g.L * g.N := Nat.mul_le_mul_right _ (⋄)
      have hjμ : (j + 1) * g.μ ≤ g.L * g.μ := Nat.mul_le_mul_right _ (⋄)
      Ξ' Nat.succ_mul at hjN hjμ
      unfold mulBody
      exec_block
      · rw [h4a, hN4]; omega
      · config_simp; rw [h4b, hμ4]; omega
      · config_simp; rw [h4i, h14]; omega
      · refine ⟨le_refl _, ‹_›, by config_simp; rw [h4i, h14], by config_simp; exact h4n,
          by config_simp; rw [h4a, hN4, Nat.succ_mul]; ring,
          by config_simp; rw [h4b, hμ4, Nat.succ_mul]; ring, fun r a1 a2 a3 => ?_, h4m, h4rr,
          h4rm, h4o⟩
        simp only
        Ξ Machine.upd_other _ _ _ a3, Machine.upd_other _ _ _ a2, Machine.upd_other _ _ _ a1
        exact h4r r a1 a2 a3)
    (j₀ := 0) ⟨e2.wb_right, by rw [k12 _ (⋄), cp 130880 130009 (⌖)]; exact hG.zero,
      hG2.rL, by rw [k12 _ (⋄), cp 130327 130085 (⌖), hG.rUP]; ring,
      by rw [k12 _ (⋄), cp 130620 130084 (⌖), hG.rbase 54 (⋄), g.base_eq]; ring,
      fun r _ _ _ => rfl, rfl, rfl, rfl, rfl⟩ (Nat.zero_le _)
  have kk3 : ∀ r, r ≠ 130327 → r ≠ 130620 → r ≠ 130880 → r ≠ 130681 → c3.nreg r = c1.nreg r :=
    fun r a1 a2 a3 a4 => Ρ hk23 r a1 a2 a3, k12 r a4
  have R : ∀ d s, (d, s) ∈ regCopies → d ≠ 130327 → d ≠ 130620 → d ≠ 130880 → d ≠ 130681 →
      c3.nreg d = c.nreg s := fun d s h a1 a2 a3 a4 => by rw [kk3 d a1 a2 a3 a4]; exact cp d s h
  have hlen : regCopies.length = 43 := rfl
  refine ⟨c3, regCopies.length + (1 + k3), .seq e1 (.seq e2 e3), ⋄, hw3, ?_,
    by rw [R 130704 130009 (⌖) (⋄) (⋄) (⋄) (⋄)]; exact hG.zero,
    fun r hr => ?_, by rw [hm3]; exact hm1, by rw [hr3]; exact hr1, by rw [hrm3]; exact hrm1,
    by rw [ho3]; exact ho1⟩
  · refine ⟨by rw [kk3 _ (⋄) (⋄) (⋄) (⋄), g1 _ (⋄)]; exact hG.one,
      by rw [kk3 _ (⋄) (⋄) (⋄) (⋄), g1 _ (⋄)]; exact hG.zero,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [R 130320 130073 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rbase 43 (⋄)]; rfl
    · rw [R 130321 130030 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rbase 0 (⋄)]; rfl
    · rw [R 130322 130059 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rbase 29 (⋄)]; rfl
    · rw [R 130323 130070 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rbase 40 (⋄)]; rfl
    · rw [R 130324 130017 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rL]; rfl
    · rw [R 130325 130058 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rbase 28 (⋄)]; rfl
    · rw [R 130326 130085 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rUP]; rfl
    · rw [h327]; rfl
    · rw [R 130328 130014 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rN]; rfl
    · rw [R 130345 130017 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rL]; rfl
    · rw [R 130601 130033 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rbase 3 (⋄)]; rfl
    · rw [R 130602 130084 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rbase 54 (⋄)]; rfl
    · rw [R 130603 130070 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rbase 40 (⋄)]; rfl
    · rw [R 130604 130017 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rL]; rfl
    · rw [R 130605 130036 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rbase 6 (⋄)]; rfl
    · rw [R 130606 130074 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rbase 44 (⋄)]; rfl
    · rw [R 130607 130078 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rbase 48 (⋄)]; rfl
    · rw [R 130608 130011 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rμ]; rfl
    · rw [h620]; rfl
    · rw [R 130632 130041 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rbase 11 (⋄)]; rfl
    · rw [R 130633 130047 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rbase 17 (⋄)]; rfl
    · rw [R 130634 130056 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rbase 26 (⋄)]; rfl
    · rw [R 130635 130059 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rbase 29 (⋄)]; rfl
    · rw [R 130636 130058 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rbase 28 (⋄)]; rfl
    · rw [R 130650 130075 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rbase 45 (⋄)]; rfl
    · rw [R 130651 130073 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rbase 43 (⋄)]; rfl
    · rw [R 130652 130074 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rbase 44 (⋄)]; rfl
    · rw [R 130653 130078 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rbase 48 (⋄)]; rfl
    · rw [R 130654 130030 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rbase 0 (⋄)]; rfl
    · rw [R 130655 130059 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rbase 29 (⋄)]; rfl
    · rw [R 130674 130016 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rs]; rfl
    · rw [R 130675 130011 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rμ]; rfl
    · rw [R 130680 130037 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rbase 7 (⋄)]; rfl
    · rw [hk23 _ (⋄) (⋄) (⋄), h681]; rfl
    · rw [R 130682 130014 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rN]; rfl
    · rw [R 130692 130069 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rbase 39 (⋄)]; rfl
    · rw [R 130694 130067 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rbase 37 (⋄)]; rfl
    · rw [R 130695 130068 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rbase 38 (⋄)]; rfl
    · rw [R 130696 130023 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rV]; rfl
    · rw [R 130697 130021 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rO]; rfl
    · rw [R 130698 130039 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rbase 9 (⋄)]; rfl
    · rw [R 130700 130076 (⌖) (⋄) (⋄) (⋄) (⋄), hG.rbase 46 (⋄)]; rfl
  · unfold RegRG at hr
    Ξ kk3 _ (⋄) (⋄) (⋄) (⋄)
    exact h2 r (fun p hp h => by
      have := (show ∀ p ∈ regCopies, 130300 ≤ p.1 ∧ p.1 ≤ 130889 by decide) p hp; omega)

end proofs

end

end Chazelle.Core.Cluster
