module

public import Mathlib.LinearAlgebra.Span.Basic

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

noncomputable section

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

def rankOneGenerators : Set M :=
  {w | Function.Bijective (fun k : R => k • w)}

variable {R M}

theorem smul_mem_rankOneGenerators_iff (z : M)
    (hz : Function.Bijective (fun k : R => k • z)) (k : R) :
    k • z ∈ rankOneGenerators R M ↔ IsUnit k := by
  constructor
  · intro hw
    obtain ⟨l, hl⟩ := hw.2 z
    have h : l * k = 1 := hz.1 (by simpa [smul_smul] using hl)
    exact ⟨⟨k, l, by simpa [mul_comm] using h, h⟩, rfl⟩
  · rintro ⟨u, rfl⟩
    constructor
    · intro a b hab
      have h : a * (u : R) = b * (u : R) := hz.1 (by
        simpa [smul_smul] using hab)
      simp_all
    · intro w
      obtain ⟨k, hk⟩ := hz.2 w
      refine ⟨k * (↑(u⁻¹) : R), ?_⟩
      simpa [smul_smul] using hk

end

end DedekindZetaZeroFree.Hecke
