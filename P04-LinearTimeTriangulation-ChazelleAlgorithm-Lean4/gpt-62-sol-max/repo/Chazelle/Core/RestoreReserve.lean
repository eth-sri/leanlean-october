module

public import Chazelle.Core.RestoreDrvProg
public import Chazelle.Machine.Footprint

/-! The common reservation loop used by restoration and the down-phase driver. -/

namespace Chazelle.Core.Restore

open Machine Machine.Stmt Programs

@[expose] public section

/-- Only the allocator and the loop counter change. -/
def reserveFoot (ctr : ℕ) : Footprint :=
  ⟨fun r => decide (r = ctr ∨ r = ALLOC), fun _ => false, false, false, false⟩

private theorem reserveBlock_check (m ctr one : ℕ) :
    (reserveBlock m ctr one).check (reserveFoot ctr).allows = true := by
  induction m with
  | zero => simp [reserveBlock, block, write_check, reserveFoot]
  | succ m ih => simpa [reserveBlock, List.replicate_succ, block_cons, write_check, reserveFoot]
      using ih

private theorem reserveBlock_exec {P : Polygon} {W ctr one : ℕ}
    (hctr : ctr ≠ ALLOC) (hone : one ≠ ALLOC) (m : ℕ) {c : Config}
    (hw : WordsBounded W c) (hu : c.nreg one = 1)
    (hA : c.nreg ALLOC + m ≤ W) (hj : c.nreg ctr + 1 ≤ W) :
    ∃ d k, Exec P W (reserveBlock m ctr one) c d k ∧ k = m + 1 ∧
      d.nreg ALLOC = c.nreg ALLOC + m ∧ d.nreg ctr = c.nreg ctr + 1 := by
  induction m generalizing c with
  | zero =>
    have ex := Exec.addN (P := P) hw ctr ctr one (by omega)
    exact ⟨_, 1, Exec.block_cons ex (.skip ex.wb_right), rfl,
      by simp [upd_other _ _ _ hctr.symm], by simp [hu]⟩
  | succ m ih =>
    let d := {c with nreg := upd c.nreg ALLOC (c.nreg ALLOC + c.nreg one)}
    have ex : Exec P W (.instr (.addN ALLOC ALLOC one)) c d 1 :=
      Exec.addN hw ALLOC ALLOC one (by omega)
    have ha : d.nreg ALLOC = c.nreg ALLOC + 1 := by simp [d, hu]
    have ht : d.nreg ctr = c.nreg ctr := upd_other _ _ _ hctr
    obtain ⟨e, k, run, hk, hA', hj'⟩ := ih ex.wb_right
      (by simpa [d, upd_other _ _ _ hone] using hu) (by omega) (by omega)
    exact ⟨e, _, Exec.block_cons ex run, by omega, by omega, by omega⟩

/-- Reserve `m` words for each of `R` records, with the same proof for any
  choice of the counter, limit, and constant registers. -/
theorem reserveLoop_exec {P : Polygon} {W m ctr lim one R A₀ : ℕ} {B : Finset ℕ} {c : Config}
    (hctr : ctr ≠ ALLOC) (hlim : lim ≠ ctr ∧ lim ≠ ALLOC)
    (hone : one ≠ ctr) (honA : one ≠ ALLOC) (hband : bandOf ctr ∈ B)
    (hw : WordsBounded W c) (hl : c.nreg lim = R) (hj : c.nreg ctr = 0) (hu : c.nreg one = 1)
    (hA : c.nreg ALLOC + m * R ≤ W) :
    ∃ d k, Exec P W (reserveLoop m ctr lim one) c d k ∧ k ≤ (m + 3) * R + 2 ∧
      d.nreg ALLOC = c.nreg ALLOC + m * R ∧ d.nreg ctr = R ∧ (reserveFoot ctr).Keeps c d ∧
      RF B A₀ c d k := by
  have hRW : R ≤ W := hl ▸ hw.1 lim
  let I (e : Config) := WordsBounded W e ∧ e.nreg ctr ≤ R ∧ e.nreg lim = R ∧ e.nreg one = 1 ∧
    e.nreg ALLOC = c.nreg ALLOC + m * e.nreg ctr
  have check := reserveBlock_check m ctr one
  have start : I c := ⟨hw, by omega, hl, hu, by simp [hj]⟩
  obtain ⟨d, k, run, ⟨-, hle, hlim', -, hA'⟩, hstop, hf, hk⟩ := whileLtN_frame
    (P := P) (a := ctr) (b := lim) (body := reserveBlock m ctr one) (B := B) (A₀ := A₀) I (fun e => R - e.nreg ctr) (m + 1) (fun _ h => h.1)
    (fun e ⟨hw, hle, hl, hu, ha⟩ ht => by
      rw [hl] at ht
      have hjm : m * (e.nreg ctr + 1) ≤ m * R := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_succ] at hjm
      obtain ⟨f, k, run, hk, ha', hj'⟩  := reserveBlock_exec (P := P) hctr honA m hw hu (by omega) (by omega)
      have keep := run.keeps check
      have hn {r : ℕ} (a : r ≠ ctr) (b : r ≠ ALLOC) : f.nreg r = e.nreg r :=
        keep.nr r (by simp [reserveFoot, a, b])
      refine ⟨f, k, run, ⟨run.wb_right, by omega, (hn hlim.1 hlim.2).trans hl,
        (hn hone honA).trans hu, ?_⟩, ⟨fun r hr h => hn (fun he => hr (he ▸ hband)) h,
        fun r _ => keep.rr r rfl, fun a _ => congrFun (keep.nm rfl) a,
        fun a _ => congrFun (keep.rm rfl) a, keep.out rfl, by omega, by omega⟩,
        hk.le, by omega⟩
      rw [ha', ha, hj', Nat.mul_succ, Nat.add_assoc]) start
  have hdn : d.nreg ctr = R := by rw [hlim'] at hstop; omega
  exact ⟨d, k, run, by simpa [hj, Nat.add_assoc] using hk, by rwa [hdn] at hA', hdn,
    run.keeps check, hf⟩

end

end Chazelle.Core.Restore
