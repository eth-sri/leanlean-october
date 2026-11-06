module

public import Chazelle.Core.SweepIoCand1ShrSpec
public import Chazelle.Core.SweepIoCand1L

/-!
# The sweep RAM (WP-D), answers: the shared-vertex step of a side-1 query

`shrB sh`: the arrival position of the shared vertex in the walk of the model of `C₁`
(`callArr (sw 20) (sw 46) K0 qD shO`, outputs `shO … shO + 2 = sw 4840 … 4842`), then the local
hit in the model of `C₁` at `(shO + 1, qH)` with tag `0` (`Cand1.lhs`).  The arrival exists
(`freeAt_left_of`, `freeAt_iff_arr`), so the flag is `1`; `Cand1.lhGeo_arr` gives `LHGeo`, so the
first hit of `C₁` is a candidate after the local hit.

**`shrStep : ShrStepSpec`**.
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)

@[expose] public section

/-- The outputs of the arrival of the shared vertex (`shO`, `shO + 1`, `shO + 2`). -/
def shO : ℕ := sw 4840

/-- **The shared-vertex step.** -/
def shrB (sh : Stmt) : Stmt :=
  .seq (callArr (sw 20) (sw 46) K0 qD shO) (Cand1.lhs (sw 30) (sw 3) (sw 33) (shO + 1) 0 sh)

set_option maxHeartbeats 4000000 in
/-- **The shared-vertex step of a side-1 query.** -/
theorem shrStep : ShrStepSpec := by
  refine ⟨shrB, 35007, ?_⟩
  intro sh Bs F X Ok hsh hBs hXl P W c₀ c J H N₁ N₂ E L hA hI hq1 hqn hqh hfree hbL hacc hroom
  set σ := dirOf (c.nreg qD) with hσdef
  have hσ : σ = 1 ∨ σ = -1 := by rw [hσdef]; unfold dirOf; split_ifs <;> simp
  have hK := hA.hK.fix hI
  have hP := hA.hP
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h45, -⟩ := hA.hst
  have h46 : c.nreg (sw 46) = cstL J 1 := by
    rw [hI.hin _ (by unfold IFix sw; omega)]; exact h45 1 (by norm_num)
  have k0 : c.nreg K0 = 0 := hK.1
  obtain ⟨hlt, hpp0, hpos0⟩ := Cand1.shared_posL hP (Qof P) P.n
  have hsL : J.shared ∈ J.left.set := J.shared_mem_left
  have hsT : J.shared.2 ≤ J.left.top.2 := J.left.snd_le_top_of_mem_set hsL
  have hyR : |J.shared.2| < J.left.radius := by
    rw [radius_left J]; exact (Cand1.abs_lt_whole J.shared_mem_right).2
  have hctx := AEnv.ctxL hA hI
  have hPL : J.left.P.Simple := hctx.2.2.2.2.1
  have hlK : 8 ≤ Cand1.lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) := by
    unfold Cand1.lhsK; omega
  -- the arrival position of the shared vertex
  refine (IRS.seq (K₁ := 35007) (callArr_irs (dsc := sw 20) (re := sw 46) (rh := K0) (rd := qD)
    (o := shO) hI hctx (by unfold K0 qD sw; omega) (by unfold shO sw; omega)
    (by rwa [h46]) (by rwa [h46, k0]) (by rwa [h46, k0, hpos0])
    (by omega)) ?_).mono le_rfl (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' ⟨hArr, fr1, hal1, hm1⟩
  rw [h46, k0] at hArr
  unfold ArrAt at hArr
  rw [hpos0] at hArr
  obtain ⟨-, hon, hoff⟩ := hArr
  have fr1' : ∀ r, 240000 ≤ r → r < 250000 → (r < shO ∨ shO + 2 < r) → c₁.nreg r = c.nreg r :=
    fun r h1 h2 h3 => fr1 r (not_oracle_sw h1 h2) (by omega) (by omega) (by omega)
      (by unfold ALLOC; omega)
  have qD1 : c₁.nreg qD = c.nreg qD := fr1' _ (by unfold qD sw; omega) (by unfold qD sw; omega)
    (by unfold qD shO sw; omega)
  have qH1 : c₁.nreg qH = c.nreg qH := fr1' _ (by unfold qH sw; omega) (by unfold qH sw; omega)
    (by unfold qH shO sw; omega)
  have hfL : FreeAt J.left J.shared σ := freeAt_left_of J hsT hfree
  obtain ⟨p, t, harr⟩ := (freeAt_iff_arr J.left hPL hσ (Or.inl hsL)).1 hfL
  have f1 : c₁.nreg shO = 1 := by
    by_contra h
    exact hoff h p t harr
  obtain ⟨hpn, -, harr'⟩ := hon f1
  obtain ⟨hgeo, hposx, hparx⟩ := Cand1.lhGeo_arr harr' (h := c.nreg qH - 1) (by omega) hqh hsT
    (d := c.nreg qD) rfl
  have eH : c.nreg qH - 1 + 1 = c.nreg qH := Nat.sub_add_cancel hq1
  rw [eH] at hgeo hposx hparx
  obtain ⟨-, ht0, ht1, -, -⟩ := harr'
  have hacc₁ : AccOK P accA (ModB J (c.nreg bL) (c.nreg bR)) J.whole.radius J.shared
      (dirOf (c₁.nreg qD)) L c₁ := by
    rw [qD1]
    exact hacc.transport (fun i hi => fr1' _ (by unfold accA sw; omega)
      (by unfold accA sw; omega) (by unfold accA shO sw; omega))
  have hpp : ProperPos (chainModel J.left) (Qof P) P.n ⟨c₁.nreg (shO + 1), c₁.nreg qH⟩ := by
    rw [qH1]; exact ⟨by rwa [hparx], by rwa [hparx], hqn⟩
  have hloc : (c₁.nreg (shO + 1) = 1 ∨ c₁.nreg (shO + 1) = 3) ∨
      (6 ≤ c₁.nreg (shO + 1) ∧ J.shared ∈ J.left.set) := by
    have hc := posClass_of (C := J.left) (Q := Qof P) (x := ⟨c₁.nreg (shO + 1), c.nreg qH⟩) hpn
      (by rwa [hparx]) (by rwa [hparx]) (by rwa [hposx])
      (Or.inl (by rwa [hposx]))
    rcases hc with h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.1, hsL⟩
    · exact Or.inr ⟨by have := h.1; simp only at this; omega, hsL⟩
  have hMod : ModB J (c.nreg bL) (c.nreg bR) 0 = J.left := by simp [ModB, hbL]
  refine (Cand1.lhsL_irs (e := shO + 1) (t := 0) hsh hBs hXl hA (by unfold Cand1.OutL shO sw; omega)
    hI₁ hpn hpp (by rwa [qH1]) hyR hloc hacc₁ (by norm_num) hMod (radius_left J)
    (by omega)).mono le_rfl ?_
  rintro c' ⟨⟨L', a', s', g', geo'⟩, fr, hal, hm⟩
  rw [qD1] at a' g' geo'
  refine ⟨⟨L', a', s', g', geo' (by rwa [qH1])⟩,
    fun r hr0 hr1 hr2 hr3 hr4 => ?_, hal1.trans hal, fun a ha => ?_⟩
  · rw [fr r hr0 (by unfold LHW sw at *; omega) hr4]
    exact fr1 r hr0 (by unfold shO sw at *; omega) (by unfold shO sw at *; omega)
      (by unfold shO sw at *; omega) hr4
  · rw [hm a (by omega), hm1 a ha]

end

end SweepIo

end Chazelle.Core
