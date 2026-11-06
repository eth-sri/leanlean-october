module

public import Chazelle.Golf

public import Chazelle.Core.ShotListG
public import Chazelle.Core.RestoreTDisp

/-!
# WP-E, the candidate test on the RAM: the shot wrapper's environment and key comparison

The candidate test shoots with the model-generic wrapper `ShotListG.shotListG` from the register
block `R = 84000` of band `bRestore`.  Its environment is the run invariant `TInv W c₀`, which
survives the wrapper's frames (`stable_tinv`), and its key comparison is the dispatching `gKey`
(`gKey_keyG`, from `gKey_ok`, with the register frame `BgK`).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim SignK NFLoc ShotList ShotListG

/-- The register block of the candidate test's shots. -/
def RS0 : ℕ := 84000

theorem regsOK_RS0 : RegsOK RS0 := by unfold RegsOK RS0; omega

theorem band8_not_oracle {q : ℕ} (h1 : 80000 ≤ q) (h2 : q < 90000) : bandOf q ∉ oracleBands := by
  rw [band8 h1 h2]; decide

/-- **The run invariant survives the wrapper's frames.** -/
theorem stable_tinv {W : ℕ} {c₀ : Config} {Bo : Finset ℕ} (hB8 : bRestore ∉ Bo) :
    Stable Bo W RS0 (TInv W c₀) := by
  intro c c' k hI hw' hf
  obtain ⟨r₁, -, m₁, -, -, a₁, -⟩ := hf
  have keep : ∀ q, 80000 ≤ q → q < 84000 → c'.nreg q = c.nreg q := fun q h1 h2 =>
    r₁ q (by rw [band8 h1 (⋄)]; exact hB8) (by unfold ALLOC; omega)
      (by unfold RS0; omega)
  refine ⟨hw', fun q h1 h2 => by rw [keep q h1 (⋄)]; exact hI.hin q h1 h2,
    le_trans hI.hA a₁, fun a ha => by rw [m₁ a (by have := hI.hA; omega)]; exact hI.hm a ha,
    by rw [keep _ (⊛) (⊛)]; exact hI.h20,
    by rw [keep _ (⊛) (⊛)]; exact hI.h21,
    by rw [keep _ (⊛) (⊛)]; exact hI.h22,
    by rw [keep _ (⊛) (⊛)]; exact hI.h23⟩

/-- The registers written by `gKey`. -/
def BgK (r : ℕ) : Bool := Bprim r || decide (50200 ≤ r ∧ r < 50210)

theorem opW_BgK : OpW BgK := fun r hr => by
  simp only [BgK, Bool.or_eq_true, decide_eq_true_eq] at hr
  rcases hr with hr | hr
  · have := Bprim_band r hr
    refine ⟨?_, this.2⟩
    have h1 := this.1
    simp only [primBands, Finset.mem_insert, Finset.mem_singleton] at h1
    simp only [oracleBands, kernelBands, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton]
    tauto
  · refine ⟨?_, by unfold ALLOC; omega⟩
    have : bandOf r = bLocate := by unfold bandOf bLocate; omega
    rw [this]; decide

theorem wr_gKey (a b d e : ℕ) : wr BgK (gKey a b d e) = true := by
  have h1 : wr BgK offCmp = true := wr_mono wr_offCmp (fun r h => ⊚ BgK, h)
  have h2 : wr BgK (iKey a b d e) = true := wr_mono (wr_iKey a b d e) (fun r h => by
    have : Bprim r = true := by
      unfold Bik at h
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
      ϴ Bprim, Bool.or_eq_true, decide_eq_true_eq
      rcases h with ((((h | h) | h) | h) | h) | h
      · simp only [Bdir, Bool.or_eq_true, decide_eq_true_eq] at h; omega
      · omega
      · omega
      · omega
      · omega
      · omega
    simp [BgK, this])
  simp only [gKey, keyCmp, kcL, copies, wr, block, wrOK, h1, h2, List.map_cons, List.map_nil,
    Bool.and_true]
  decide

/-- **The key comparison of the test is a key comparison of the wrapper.** -/
theorem gKey_keyG {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ : Config}
    (hE : TGood P W M N c₀) : KeyG P W M RS0 (TInv W c₀) gKey BgK 11010 := by
  intro a b d e ha hb hd he c hw hctx hx hxe hx0 hy hye hy0 hroom
  have hI : TInv W c₀ c := hctx.1
  have inR : ∀ r, InB RS0 r → InR r := fun r h => by unfold InB RS0 at h; unfold InR; omega
  obtain ⟨c', k, ex, hk, b1, -, -⟩ := gKey_ok a b d e (inR a ha) (inR b hb) (inR d hd) (inR e he)
    P W M N c₀ c hE hI ⟨hxe, hx, fun C _ h0 => by simp only at h0; omega⟩
    ⟨hye, hy, fun C _ h0 => by simp only at h0; omega⟩ hroom
  exact ⟨c', k, ex, hk, b1, exec_frameB ex (wr_gKey a b d e)⟩

end

end Restore

end Chazelle.Core
