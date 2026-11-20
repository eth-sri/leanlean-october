module

public import ThreeSumApsp.Lang.Lib.Rect
public import ThreeSumApsp.Lang.Lib.Pass

@[expose] public section

namespace Light

abbrev squarePass (r c : ℕ) (body : Stmt) : Stmt := .for r (v 0) (.for c (v 0) body)

/-- Verify a square matrix pass by giving the effect of the body at a single cell. -/
theorem Ends.squarePass {lim : Limits} {P : Program} {d n r c dst T : ℕ} {s : Stmt}
    {loc μ : ℕ → ℤ} (f : ℕ → ℤ) (hn : (n : ℤ) ≤ lim.word) (hlen : loc 0 = n)
    (step : ∀ i j : ℕ, i < n → j < n →
      Ends lim P d s ⟨rectLoc loc r c i j, wrote μ dst f (i * n + j)⟩ s.blockCost
        (· = ⟨rectLoc loc r c i j, wrote μ dst f (i * n + (j + 1))⟩))
    (hrc : r ≠ c := by decide) (hr : 0 ≠ r := by decide) (hc : 0 ≠ c := by decide)
    (hT : n * (n * (s.blockCost + 8) + 14) + 6 ≤ T := by light_time) :
    Ends lim P d (squarePass r c s) ⟨loc, μ⟩ T (·.mem = wrote μ dst f (n * n)) := by
  refine Ends.forRect (fun _ : Unit => loc) (fun i j _ ν => ν = wrote μ dst f (i * n + j)) ()
    (by simp [wrote_zero]) hn hn (fun _ => hlen) (fun _ => hlen) ?_ ?_ (fun _ _ _ h => by simpa using h) hrc hr hc hr hc hT
  · rintro i j _ ν hi hj rfl
    exact (step i j hi hj).mono le_rfl (by simp)
  grind

end Light
