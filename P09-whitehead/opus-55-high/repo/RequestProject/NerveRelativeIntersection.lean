import RequestProject.NerveIntersectionGeneration


/-! Relative chains, whose boundary need only lie in the intersection. -/
namespace FiniteChains.Nerve
universe u
variable {P : Type u} [Preorder P]

/-- Ambient generation and one-degree-lower fillings in the other piece give
actual relative fillings in the first piece. The input is not assumed to be a cycle. -/
theorem relative_filling_intersection_of_ambient {A B U} {n}
    (hAU : ∀ p, A p → U p) (hBU : ∀ p, B p → U p)
    (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b))
    (hgen : GeneratesDegreeIn U B (n + 1)) (hfill : FillsDegreeIn B n)
    z (hz : z ∈ IncOn A) (hd : lengthProjection (n + 1) z = z)
    (hdz : bdry z ∈ IncOn B) :
    ∃ t ∈ IncOn (fun p => A p ∧ B p), lengthProjection (n + 1) t = t ∧
      bdry t = bdry z ∧ ∃ y ∈ IncOn A, lengthProjection (n + 2) y = y ∧
        z = t + bdry y := by
  have hdd : lengthProjection n (bdry z) = bdry z := by
    rw [lengthProjection_bdry, hd]
  obtain ⟨v₀, hv₀, hdv₀⟩ := hfill _ hdz hdd (bdry_bdry z)
  let v := lengthProjection (n + 1) v₀
  have hv : v ∈ IncOn B := lengthProjection_mem_incOn _ hv₀
  have hvd : lengthProjection (n + 1) v = v := lengthProjection_idempotent _ _
  have hdv : bdry v = bdry z := by
    rw [← lengthProjection_bdry, hdv₀, hdd]
  obtain ⟨c, hc, y, hy, _, he⟩ := hgen _
    (AddSubgroup.sub_mem _ (incOn_mono hAU hz) (incOn_mono hBU hv))
    (by simp_all) (by simp_all)
  obtain ⟨a, ha, b, hb, hyab⟩ := exists_split_of_unmixed hmix hy
  let t₀ := z - bdry a
  have htA : t₀ ∈ IncOn A := AddSubgroup.sub_mem _ hz (bdry_mem_incOn ha)
  have htB : t₀ ∈ IncOn B := by
    have ht : t₀ = v + c + bdry b := by
      grind
    rw [ht]
    exact AddSubgroup.add_mem _ (AddSubgroup.add_mem _ hv hc) (bdry_mem_incOn hb)
  have htJ : t₀ ∈ IncOn (fun p => A p ∧ B p) := by
    rw [← incOn_inf]
    simp_all
  have hdt : bdry t₀ = bdry z := by simp [t₀, map_sub, bdry_bdry, sub_zero]
  have he₀ : z = t₀ + bdry a := by grind
  refine ⟨lengthProjection (n + 1) t₀, lengthProjection_mem_incOn _ htJ,
    lengthProjection_idempotent _ _, ?_, lengthProjection (n + 2) a,
    lengthProjection_mem_incOn _ ha, lengthProjection_idempotent _ _, ?_⟩
  · rw [← lengthProjection_bdry, hdt, hdd]
  · have h := congrArg (lengthProjection (n + 1)) he₀
    rwa [hd, map_add, lengthProjection_bdry] at h
