module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepEvLoop2

/-!
# The sweep (WP-D), stage 3: the event loop (RAM)

`loop_irs`: `while (dF < K1) body`, from `LoopInv`, ends in a configuration with `dF = 1` and the
outputs `RunOut`, given one iteration (`IterRel`) and the step and done mathematics.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep

@[expose] public section

variable {P : Polygon} {J : Merge.Junction} {N₁ N₂ : NF}

/-- **The registers an iteration keeps.** -/
theorem iter_keep {c cw cs co c' : Config} (h : IterRel P J N₁ N₂ c cw cs co c') :
    (∀ r, KeepR r → ¬ KR r → c'.nreg r = c.nreg r) ∧ c.nreg ALLOC ≤ c'.nreg ALLOC := by
  obtain ⟨hWO, hAw, ⟨-, -, -, hsO⟩, ⟨hregO, hAO, -⟩, ⟨hfrK, hAK, -⟩⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hfrW⟩ := hWO
  have hsA : cs.nreg ALLOC = cw.nreg ALLOC :=
    hsO _ (by omega_nf) (by omega_nf)
  refine ⟨fun r hr hk => ?_, by omega⟩
  have hb := band_sw_not ⟨hr.1, hr.2.1⟩
  have hra : r ≠ ALLOC := by have := hr.1; omega_nf
  rw [hfrK r hb hk hra, hregO r hb hr.2.2.2.2.2.1 hr.2.2.2.2.2.2 hra,
    hsO r hr.2.2.2.1 hr.2.2.2.2.1, hfrW r hb hr.2.2.1 hra]

section
variable (P : Polygon) (J : Merge.Junction) (N₁ N₂ : NF)
include P J N₁ N₂
/-- The end of the loop. -/
def FinS (c₀ c : Config) : Prop :=
  c.nreg dF = 1 ∧ RunOut P J N₁ N₂ c₀ c

/-- The measure of the loop. -/
noncomputable def μL (c : Config) : ℕ :=
  if c.nreg dF = 0 then (keyS P J N₁ N₂ ∩ Ioi (keyOff P J c)).ncard + 1 else 0


end

/-- **The outputs after the last iteration.** -/
theorem done_runOut {c₀ c cw cs co c' : Config} (hL : LoopInv P J N₁ N₂ c₀ c)
    (hIR : IterRel P J N₁ N₂ c cw cs co c') (hOut : Out P J N₂ (finCfg c'))
    (hlC : c'.nreg lC ≤ logCap N₁ N₂) : RunOut P J N₁ N₂ c₀ c' := by
  obtain ⟨hk, hA⟩ := iter_keep hIR
  have esB : c'.nreg sB = c.nreg sB :=
    hk _ (keepR_of (by omega_nf)) (by omega_nf)
  have esC : c'.nreg sC = c.nreg sC :=
    hk _ (keepR_of (by omega_nf)) (by omega_nf)
  have elB : c'.nreg lB = c.nreg lB :=
    hk _ (keepR_of (by omega_nf)) (by omega_nf)
  have eTB : c'.nreg cTB = c.nreg cTB :=
    hk _ (keepR_of (by omega_nf)) (by omega_nf)
  obtain ⟨rs, ax, hlen, -, -, -, -, -, -, hsize⟩ := hL.stops
  have h0 := hL.tab0; have h1 := hL.lay1; have h2 := hL.lay2; have h4 := hL.lay4
  unfold logCap at h2 hlC
  refine ⟨hOut, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega <;> try omega

/-- **The event loop.** -/
theorem loop_irs {W : ℕ} {c₀ : Config} {body : Stmt} {Kb : ℕ}
    (hiter : ∀ c, IInv W c₀ c → LoopInv P J N₁ N₂ c₀ c → c.nreg ALLOC + Kb ≤ W →
      IRS P W c₀ body c Kb (fun c' => ∃ cw cs co, IterRel P J N₁ N₂ c cw cs co c'))
    (hstep : ∀ c cw cs co c', LoopInv P J N₁ N₂ c₀ c → IterRel P J N₁ N₂ c cw cs co c' →
      c'.nreg dF = 0 → LoopInv P J N₁ N₂ c₀ c' ∧
        (keyS P J N₁ N₂ ∩ Ioi (keyOff P J c')).ncard < (keyS P J N₁ N₂ ∩ Ioi (keyOff P J c)).ncard)
    (hdone : ∀ c cw cs co c', LoopInv P J N₁ N₂ c₀ c → IterRel P J N₁ N₂ c cw cs co c' →
      c'.nreg dF = 1 → Out P J N₂ (finCfg c') ∧ c'.nreg lC ≤ logCap N₁ N₂)
    (hfin : (keyS P J N₁ N₂).Finite)
    {c : Config} (hI : IInv W c₀ c) (hK1 : c.nreg K1 = 1) (hL : LoopInv P J N₁ N₂ c₀ c)
    (hroom : c.nreg ALLOC + (Kb + 2) * ((keyS P J N₁ N₂).ncard + 1) ≤ W) :
    IRS P W c₀ (.whileLtN dF K1 body) c ((Kb + 2) * ((keyS P J N₁ N₂).ncard + 1) + 2)
      (fun c' => FinS P J N₁ N₂ c₀ c') := by
  have hle : ∀ c : Config, μL P J N₁ N₂ c ≤ (keyS P J N₁ N₂).ncard + 1 := fun c => by
    unfold μL; split_ifs
    · have := Set.ncard_le_ncard (Set.inter_subset_left (s := keyS P J N₁ N₂)
        (t := Ioi (keyOff P J c))) hfin
      omega
    · omega
  have hμ : ∀ c : Config, LoopInv P J N₁ N₂ c₀ c →
      μL P J N₁ N₂ c = (keyS P J N₁ N₂ ∩ Ioi (keyOff P J c)).ncard + 1 := fun c h => by
    unfold μL; rw [ite_eq_left h.done0]
  have hw := IRS.while (P := P) (W := W) (c₀ := c₀) (a := dF) (b := K1) (body := body)
    (fun c => c.nreg K1 = 1 ∧ (LoopInv P J N₁ N₂ c₀ c ∨ FinS P J N₁ N₂ c₀ c)) (μL P J N₁ N₂) Kb
    (fun c ⟨hk, h⟩ ht => by
      rcases h with h | h
      · grind
      · rw [hk, h.1] at ht; omega)
    (fun c hIc ⟨hk, h⟩ ht hr => by
      have hLc : LoopInv P J N₁ N₂ c₀ c := by
        rcases h with h | h
        · exact h
        · rw [hk, h.1] at ht; omega
      refine (hiter c hIc hLc hr).mono le_rfl ?_
      rintro c' ⟨cw, cs, co, hIR⟩
      have hkeep := (iter_keep hIR).1
      have hk' : c'.nreg K1 = 1 := by
        rw [hkeep _ (keepR_of (by omega_nf)) (by omega_nf)]
        exact hk
      by_cases hd : c'.nreg dF = 0
      · ram_grind
      · have hd1 : c'.nreg dF = 1 := by
          obtain ⟨-, -, -, -, hK⟩ := hIR
          obtain ⟨-, -, hnone, hsome⟩ := hK
          ram_grind
        obtain ⟨hOut, hlC⟩ := hdone c cw cs co c' hLc hIR hd1
        refine ⟨⟨hk', Or.inr ⟨hd1, done_runOut hLc hIR hOut hlC⟩⟩, ?_⟩
        core_grind)
    hI ⟨hK1, Or.inl hL⟩ (by have := Nat.mul_le_mul_left (Kb + 2) (hle c); omega)
  refine hw.mono (by have := Nat.mul_le_mul_left (Kb + 2) (hle c); omega) ?_
  rintro c' ⟨⟨hk, h⟩, ht⟩
  rcases h with h | h
  · rw [hk, h.done0] at ht; omega
  · exact h

end

end SweepEv

end Chazelle.Core
