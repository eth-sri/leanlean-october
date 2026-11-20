module

public import ThreeSumApsp.Lang.Lib.Seg
public import ThreeSumApsp.Lang.Frames

@[expose] public section

namespace Light

/-- Short-circuit boolean tests, compiled to nested branches. -/
inductive Guard where
  | atom (c : Cond)
  | both (a b : Guard)
  | either (a b : Guard)
  | neg (a : Guard)

@[simp] def Guard.branch : Guard → Stmt → Stmt → Stmt
  | .atom c, s, t => .ite c s t
  | .both a b, s, t => a.branch (b.branch s t) t
  | .either a b, s, t => a.branch s (b.branch s t)
  | .neg a, s, t => a.branch t s

@[simp] def Guard.Holds (σ : State) : Guard → Prop
  | .atom c => c.Holds σ
  | .both a b => a.Holds σ ∧ b.Holds σ
  | .either a b => a.Holds σ ∨ b.Holds σ
  | .neg a => ¬ a.Holds σ

@[simp] def Guard.Safe (lim : Limits) (σ : State) : Guard → Prop
  | .atom c => c.Safe lim σ
  | .both a b => a.Safe lim σ ∧ (a.Holds σ → b.Safe lim σ)
  | .either a b => a.Safe lim σ ∧ (¬ a.Holds σ → b.Safe lim σ)
  | .neg a => a.Safe lim σ

private theorem Guard.blockSafe (g : Guard) (s t : Stmt) (lim : Limits) (σ : State) :
    (g.branch s t).BlockSafe lim σ ↔
      g.Safe lim σ ∧ (g.Holds σ → s.BlockSafe lim σ) ∧ (¬ g.Holds σ → t.BlockSafe lim σ) := by
  induction g generalizing s t <;> simp_all <;> tauto

open Classical in
private theorem Guard.after (g : Guard) (s t : Stmt) (σ : State) :
    (g.branch s t).after σ = (if g.Holds σ then s.after σ else t.after σ) := by
  classical
  induction g generalizing s t <;> simp_all <;> split_ifs <;> simp_all

/-- Test an element, and append its value when selected. -/
def filterStep (dst count : ℕ) (g : Guard) (e : Expr) : Stmt :=
  g.branch (.store (v dst +' v count) e ;; .set count (v count +' k 1)) .skip

/-- Run a filter and leave the number of selected elements in `count`. -/
def filterPass (idx len dst count : ℕ) (g : Guard) (e : Expr) : Stmt :=
  .set count (k 0) ;; .for idx (v len) (filterStep dst count g e)

abbrev filterState (loc : ℕ → ℤ) (idx count j : ℕ) (L : List ℤ) (ν : ℕ → ℤ) : State :=
  ⟨Function.update (Function.update loc idx j) count L.length, ν⟩

/-- The data selected so far. Only the written prefix, not the whole output buffer, may have
changed. This also supports compaction in place. -/
structure FilterMem (μ ν : ℕ → ℤ) (dst j : ℕ) (L : List ℤ) : Prop where
  seg : Seg ν dst L
  same : SameOutside μ ν dst L.length
  size : L.length ≤ j

private theorem FilterMem.push {μ ν : ℕ → ℤ} {dst j : ℕ} {L : List ℤ}
    (h : FilterMem μ ν dst j L) (z : ℤ) :
    FilterMem μ (Function.update ν (dst + L.length) z) dst (j + 1) (L ++ [z]) := by
  have hs : SameOutside μ ν dst (L ++ [z]).length := h.same.mono le_rfl (by simp)
  exact ⟨h.seg.snoc z, hs.update (by simp) z, by simpa using Nat.succ_le_succ h.size⟩

/-- A filter pass with a user invariant on the selected values. Each step only needs to verify
its test and read, and say how the invariant changes on append or skip. -/
theorem Ends.filterPass {lim : Limits} {P : Program} {d T idx len dst count n out : ℕ}
    {loc μ : ℕ → ℤ} {Q : State → Prop} (g : Guard) (e : Expr) (I : ℕ → List ℤ → Prop)
    (start : I 0 [])
    (step : ∀ i L ν, i < n → I i L → FilterMem μ ν out i L →
      let σ := filterState loc idx count i L ν
      g.Safe lim σ ∧ e.Safe lim σ ∧
        (g.Holds σ → I (i + 1) (L ++ [e.val σ])) ∧ (¬ g.Holds σ → I (i + 1) L))
    (done : ∀ L ν, I n L → FilterMem μ ν out n L → Q (filterState loc idx count n L ν))
    (hw : (lim.space : ℤ) ≤ lim.word) (ho : out + n ≤ lim.space)
    (hl : loc len = n) (hd : loc dst = out)
    (hic : idx ≠ count := by decide) (hli : len ≠ idx := by decide)
    (hlc : len ≠ count := by decide) (hdi : dst ≠ idx := by decide) (hdc : dst ≠ count := by decide)
    (hT : n * ((filterStep dst count g e).blockCost + 8) + 8 ≤ T := by light_time [filterStep]) :
    Ends lim P d (Light.filterPass idx len dst count g e) ⟨loc, μ⟩ T Q := by
  classical
  unfold Light.filterPass
  refine Ends.setThen ?_ (by simp; omega) (by simp; omega)
  have ht : 1 + (filterStep dst count g e).blockCost + 7 = (filterStep dst count g e).blockCost + 8 := by omega
  refine Ends.for (fun i σ => ∃ L ν, σ = filterState loc idx count i L ν ∧ I i L ∧
    FilterMem μ ν out i L) n (filterStep dst count g e).blockCost ?_ ?_ ?_ ?_ (by omega) (by simp only [Expr.cost, ht]; omega)
  · exact ⟨[], μ, by simp [filterState, Function.update_comm hic], start, .nil, .refl, by simp⟩
  · rintro i _ hi - ⟨L, ν, rfl, hI, hM⟩
    obtain ⟨hg, he, hTake, hSkip⟩ := step i L ν hi hI hM
    have hsize := hM.size
    refine Ends.block ⟨?_, ?_⟩ le_rfl
    · rw [filterStep, Guard.blockSafe]
      refine ⟨hg, fun _ => ?_, by simp⟩
      simp [filterState, hdi, hdc, hd, he, Limits.Addr, abs_le]
      omega
    · rw [filterStep, Guard.after]
      split_ifs with h
      · refine ⟨?_, _, _, ?_, hTake h, hM.push _⟩
        · simp [filterState, hic]
        · simp [filterState, hdc, hdi, hd, Function.update_comm hic.symm]
      · refine ⟨by simp [filterState, hic], L, ν, ?_, hSkip h, {hM with size := hM.size.step}⟩
        simp [filterState, Function.update_comm hic.symm]
  · rintro _ - ⟨L, ν, rfl, hI, hM⟩
    exact done L ν hI hM
  · rintro i _ - - ⟨L, ν, rfl, -⟩
    simp [hli, hlc, hl]

end Light
