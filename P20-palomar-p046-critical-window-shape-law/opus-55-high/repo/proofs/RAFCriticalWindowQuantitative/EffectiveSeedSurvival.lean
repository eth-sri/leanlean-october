module

public import proofs.RAFCriticalWindowQuantitative.EffectiveBulk
public import proofs.HordijkSteelThreshold.StaticParameterMonotonicity
public import proofs.HordijkSteelThreshold.SprinkledSeedLowerBound
public import proofs.HordijkSteelThreshold.StaticClosureMass
public import proofs.HordijkSteelThreshold.AmbientEscapeBound
public import proofs.HordijkSteelThreshold.SourceTerminalRAF

public section

namespace RAFCriticalWindowQuantitative
open Classical Filter MeasureTheory HordijkSteelThreshold RAF.Polymer RAF.Concrete unitInterval
open scoped ENNReal Topology

theorem _root_.HordijkSteelThreshold.SplitModel.seed_survival (M : SplitModel) (b : I) (m L : ℕ) (hm : 2 ≤ m)
    (hbulk : ∀ N, 0 < N → M.μ N b {q | m*(M.cl N L q).card < (m-1)*Fintype.card (Molecule N)} ≤ (m : ENNReal)⁻¹) :
    M.ν b {field | ∀ w ∈ actualBinaryWords L, InfiniteReversibleGenerated 2 field w} ≤
      M.ν b {field | ReversibleUnbounded 2 field} + (m : ENNReal)⁻¹ := by
  refine ge_of_tendsto' ((M.esc_tendsto b).add_const _) fun K => ?_
  apply le_of_tendsto $ M.seed_tendsto 2 b _
  filter_upwards [tendsto_atTop.mp card_molecule_tendsto_atTop
    (m*Fintype.card (Molecule $ K+2)+1),eventually_ge_atTop 1] with N hlarge hN
  refine (measure_mono fun ω hω => ?_).trans $ (measure_union_le _ _).trans
    (add_le_add (M.capped_le N K b) $ hbulk N hN)
  by_cases hb : m*(M.cl N L ω).card < (m-1)*Fintype.card (Molecule N)
  · exact Or.inr hb
  refine Or.inl $ by_contra fun h => ?_
  have hc := (Finset.card_le_card $ show M.cl N 2 ω ⊆ binaryFood N (K+2) from fun x hx =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,Nat.le_of_not_gt $ fun hl => h ⟨x,hx,hl⟩⟩).trans
    (binaryFood_card_le_cutoff N $ K+2)
  have : (M.cl N L ω).card ≤ (M.cl N 2 ω).card :=
    Finset.card_le_card $ temporaryReactionClosure_seed_transfer Finset.Subset.rfl fun x hx => ?_
  · have := Nat.mul_le_mul_right (Fintype.card $ Molecule N) (show 1 ≤ m-1 by omega)
    nlinarith
  obtain ⟨y,hy,he⟩ := hω _ $ (mem_actualBinaryWords _ _).mpr
    ⟨moleculeWord_nonempty x, by rwa [moleculeWord_length]⟩
  exact moleculeWord_injective he ▸ hy

end RAFCriticalWindowQuantitative
