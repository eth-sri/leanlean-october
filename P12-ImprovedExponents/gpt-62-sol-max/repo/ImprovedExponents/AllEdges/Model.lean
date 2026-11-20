module

public import ImprovedExponents.AllEdges.Task
public import ImprovedExponents.Pipeline.HostBound
public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Text

@[expose] public section

/-! The time model in which Exact Triangle means its all-edges version. -/

namespace ImprovedExponents.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

/-- Upstream's `lightModel`, with "Exact Triangle" read as all-edges Exact Triangle. -/
noncomputable def lightModelAE : DetTimeModel :=
  { lightModel with exactTriangle := SolvedIn aeTask }

/-- The host's time bound for every solver, expressed as a function of the solver's time. -/
def ObeysBound17Mid (MM : ℕ → ℝ) (D g : ℕ → ℕ) (time : (List ℕ → ℕ) → ℕ → ℕ → ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (Tn : List ℕ → ℕ) (T : ℕ → ℕ → ℕ → ℝ),
    (∀ m d w w' : ℕ, 1 ≤ m → 1 ≤ d → w ≤ w' → (Tn [m, d, w] : ℝ) ≤ T m d w') →
    ∀ (n U : ℕ) (κ : ℝ), 16 ≤ D n → D n ≤ n → 1 ≤ g n → (g n : ℝ) ≤ Real.sqrt (D n) → 1 ≤ κ →
      (U : ℝ) ≤ (n : ℝ) ^ κ → (time Tn n U : ℝ) ≤
        hostCharge MM n (D n) (g n) (midSize (D n) (g n)) C κ T

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Claim.lean
/-- **From an all-edges host to the claim.**
`time` and `need` are the host's time and need as functions of those of the solver. -/
theorem claim17MidAE_of_host (MM : ℕ → ℝ) (D g : ℕ → ℕ) (time : (List ℕ → ℕ) → ℕ → ℕ → ℕ)
    (need : (List ℕ → Need) → ℕ → ℕ → Need)
    (host : ∀ (Q : Program) (pS : ℕ) (Tn : List ℕ → ℕ) (r : List ℕ → Need), PolyNeedN r →
      SolvesN lopDetectTask Q pS Tn r →
      ∃ (R : Program) (p' : ℕ), Solves aeTask (Q ++ R) p' (time Tn) (need r) ∧ PolyNeed (need r))
    (bound : ObeysBound17Mid MM D g time) :
    HostBound lightModelAE MM D g (fun n => midSize (D n) (g n)) := by
  obtain ⟨C, hC, bound⟩ := bound
  refine ⟨C, hC, fun T hT => ?_⟩
  obtain ⟨Q, pS, Tn, r, hpoly, hsolves, hle⟩ := hT
  obtain ⟨R, p', hs, hp⟩ := host Q pS Tn r hpoly hsolves
  exact ⟨timeUpTo (time Tn), hs.solvedIn hp, fun n κ u h16 hDn hg1 hg hκ hu =>
    timeUpTo_le fun U hU =>
      bound Tn T hle n U κ h16 hDn hg1 hg hκ (hU.trans (max_le hu (by positivity)))⟩

end ImprovedExponents.AllEdges
