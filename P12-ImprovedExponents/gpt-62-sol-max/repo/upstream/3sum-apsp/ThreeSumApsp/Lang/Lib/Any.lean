module

public import ThreeSumApsp.Lang.Frames
public import ThreeSumApsp.Util.Flag

@[expose] public section

namespace Light

open ThreeSumApsp

/-- Scan a fixed range and set `out` if any test holds, without changing memory. -/
def anyPass (idx len out : ℕ) (c : Cond) : Stmt :=
  .set out (k 0) ;; .for idx (v len) (.ite c (.set out (k 1)) .skip)

abbrev anyState (loc : ℕ → ℤ) (idx out j : ℕ) (z : ℤ) (μ : ℕ → ℤ) : State :=
  ⟨Function.update (Function.update loc idx j) out z, μ⟩

theorem Ends.anyPass {lim : Limits} {P : Program} {d T idx len out n : ℕ} {loc μ : ℕ → ℤ}
    {Q : State → Prop} (c : Cond) (p : ℕ → Prop)
    (check : ∀ j < n, let σ := anyState loc idx out j (flag (∃ i < j, p i)) μ
      c.Safe lim σ ∧ (c.Holds σ ↔ p j))
    (done : Q (anyState loc idx out n (flag (∃ i < n, p i)) μ))
    (hl : loc len = n) (hn : (n : ℤ) ≤ lim.word) (h1 : (1 : ℤ) ≤ lim.word)
    (hio : idx ≠ out := by decide) (hli : len ≠ idx := by decide) (hlo : len ≠ out := by decide)
    (hT : n * (c.cost + 11) + 8 ≤ T := by light_time) :
    Ends lim P d (Light.anyPass idx len out c) ⟨loc, μ⟩ T Q := by
  unfold Light.anyPass
  refine Ends.setThen (hT := by light_time) ?_
  refine Ends.forShape (anyState loc idx out) (fun j z ν => z = flag (∃ i < j, p i) ∧ ν = μ)
    n (c.cost + 3) 0 ⟨by simp [flag], rfl⟩ ?_ (by rintro _ _ ⟨rfl, rfl⟩; exact done)
    (first := by simp [Function.update_comm hio.symm])
    (bound := by simp [hlo, hli, hl])
    (counter := by simp [hio])
    (next := by simp [← Function.update_comm hio, Function.update_idem])
    hn (by simp only [Expr.cost, show 1 + (c.cost + 3) + 7 = c.cost + 11 by omega]; omega)
  rintro j _ ν hj ⟨rfl, hν⟩
  subst ν
  have hs : (∃ i < j + 1, p i) ↔ (∃ i < j, p i) ∨ p j := by grind
  refine Ends.iteIffLast (p j) ?_ ?_ (check j hj)
  · intro hit
    exact Ends.setLast ⟨1, μ, by simp, flag_of (hs.2 (Or.inr hit)) |>.symm, rfl⟩
  · intro miss
    exact Ends.skip ⟨_, μ, rfl, flag_congr (by simpa [miss] using hs.symm), rfl⟩

end Light
