module

public import RequestProject.CombUniversalCover
public import RequestProject.PathVoltage

@[expose] public section

namespace FiniteChains.Comb

variable {X : Complex2} {a : X.V} {G : Type*} [Group G]

/-- A sheet coordinate intertwining single edge extensions intertwines the path lifts. -/
theorem map_uLiftPath_voltage (v : X.E × Bool → G) (q : UV X a → G)
    (hq : ∀ c e, endV c = germSrc X.src X.tgt e → q (extend e c) = q c * v e)
    {l : List (X.E × Bool)} {c : UV X a} {b : X.V}
    (hl : IsPath X.src X.tgt l (endV c) b) :
    (uLiftPath l c).map (fun e => ((q e.1.1.1, e.1.1.2), e.2)) =
      PathVoltage.liftPath v l (q c) := by
  induction l generalizing c with
  | nil => rfl
  | cons e l ih =>
    have he := hq c e hl.1
    rw [uLiftPath_cons hl.1, List.map_cons]
    have ht : IsPath X.src X.tgt l (endV (extend e c)) b := by
      rw [endV_extend hl.1]
      exact hl.2
    rw [ih ht, he]
    obtain ⟨e, s⟩ := e
    cases s <;> simp [PathVoltage.liftPath, PathVoltage.liftGerm, he]

end FiniteChains.Comb
