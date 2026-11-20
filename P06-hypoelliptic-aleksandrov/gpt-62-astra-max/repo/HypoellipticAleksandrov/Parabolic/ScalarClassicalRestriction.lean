module
public import HypoellipticAleksandrov.Parabolic.ScalarClassical

public section
namespace HypoellipticAleksandrov.Parabolic

/-- Restricting a supplied classical jet preserves its actual derivative functions. -/
theorem IsScalarC12On.mono {d : ℕ} {U V : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ} (hu : IsScalarC12On u U) (hVU : V ⊆ U) :
    IsScalarC12On u V := by
  rcases hu with ⟨hv, ht, hs, hdt, hdg, hdh⟩
  exact ⟨hv.mono hVU, fun z hz => ht z (hVU hz), fun z hz => hs z (hVU hz),
    hdt.mono hVU, hdg.mono hVU, hdh.mono hVU⟩

end HypoellipticAleksandrov.Parabolic
