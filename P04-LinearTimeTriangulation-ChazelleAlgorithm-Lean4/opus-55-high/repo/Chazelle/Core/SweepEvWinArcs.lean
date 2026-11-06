module

public import Chazelle.Core.SweepEvTasks
public import Chazelle.Core.FactsArcs
public import Chazelle.Core.GranSize
public import Chazelle.Core.FactsInterior

/-!
# The sweep (WP-D): the number of arcs of a normal form (task C2)

**`arcsTask : ArcsTask`**: a valid normal form `N` of a chain model of a simple chain has at most
`3 K + 1` arc records, `K` its number of chords:

* every arc record belongs to one of the `K + 1` regions (`ArcsOK`, `Gran.nRegions_eq`), and the
  arc records of one region have distinct start keys, so they are at most as many as the arcs of
  that region, at most `deg + 1` (`arcsPerRegion`);
* the degrees of the regions sum to at most `2 K` (`Merge.potential_le` with `Δ = 0`).
-/

namespace Chazelle.Core

namespace SweepEv

open Set

@[expose] public section

/-- **Task C2: the number of arcs** of a normal form of a chain model: `arcs ≤ 3 K + 1`. -/
theorem arcsTask : ArcsTask := by
  intro C Q N hP hN
  classical
  set M := chainModel C with hMdef
  have hGM : GoodModel M := Or.inl ⟨C, hP, rfl⟩
  have hM : WalkAx M := walkAx_of_goodModel hGM
  set F := N.F M Q with hF
  have hN' := hN
  obtain ⟨hFam, -, -, reg, hRC, -, hAO, -, -⟩ := hN
  set A := N.arcs.length with hA
  set R := N.nRegions with hR
  -- 1. the arcs by region
  have h1 : A = ∑ r ∈ Finset.range R, ((Finset.range A).filter fun j => (N.arc j).reg = r).card := by
    have := Finset.card_eq_sum_card_fiberwise (s := Finset.range A) (t := Finset.range R)
      (f := fun j => (N.arc j).reg) (fun j hj => by
        have hj' : j < A := by simpa using hj
        simpa using (hAO.1 j hj').1)
    simpa using this
  -- 2. per region: at most `deg + 1` arcs
  have h2 : ∀ r, r < R → ((Finset.range A).filter fun j => (N.arc j).reg = r).card ≤
      M.deg F (reg r) + 1 := by
    intro r hr
    have hU : reg r ∈ M.regions F := hRC.1 r hr
    obtain ⟨hfin, hle⟩ := arcsPerRegion M Q F hGM hFam (reg r) hU
    refine le_trans ?_ hle
    rw [← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard_of_injOn (fun j => (M.key Q (N.arc j).s, M.key Q (N.arc j).e))
      (fun j hj => ?_) (fun j hj j' hj' h => ?_) hfin
    · simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hj ⊢
      have := (hAO.1 j hj.1).2
      rw [hj.2] at this
      exact this
    · simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hj hj'
      have hk : M.key Q (N.arc j).s = M.key Q (N.arc j').s := congrArg Prod.fst h
      exact hAO.2.1 j j' hj.1 hj'.1 (by rw [hj.2, hj'.2]) hk
  -- 3. the degrees sum to at most `2 K`
  have hsys := hM.sys F hFam.2.1 hFam.1
  have hpot := Merge.potential_le hsys hM.preconn hM.nonempty (subset_refl F) 0
  have himg : M.regions F = reg '' ((Finset.range R : Finset ℕ) : Set ℕ) := by
    ext U
    simp only [Finset.coe_range, Set.mem_image, Set.mem_Iio]
    constructor
    · intro hU; obtain ⟨r, hr, rfl⟩ := hRC.2.2 U hU; exact ⟨r, hr, rfl⟩
    · rintro ⟨r, hr, rfl⟩; exact hRC.1 r hr
  have hinj : Set.InjOn reg ((Finset.range R : Finset ℕ) : Set ℕ) := fun r hr r' hr' h =>
    hRC.2.1 r r' (by simpa using hr) (by simpa using hr') h
  have h3 : ∑ r ∈ Finset.range R, M.deg F (reg r) ≤ 2 * F.ncard := by
    have e : Merge.potential M.D 0 F = ∑ r ∈ Finset.range R, M.deg F (reg r) := by
      unfold Merge.potential
      change ∑ᶠ U ∈ M.regions F, _ = _
      rw [himg, finsum_mem_image hinj, finsum_mem_coe_finset]
      rfl
    rw [← e]; exact hpot
  -- 4. the count
  have hK : F.ncard = N.nChords := Gran.ncard_F hN'
  have hRK : R = N.nChords + 1 := Gran.nRegions_eq hN' hM
  have h4 : ∑ r ∈ Finset.range R, ((Finset.range A).filter fun j => (N.arc j).reg = r).card ≤
      ∑ r ∈ Finset.range R, (M.deg F (reg r) + 1) :=
    Finset.sum_le_sum fun r hr => h2 r (Finset.mem_range.1 hr)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at h4
  omega

end

end SweepEv

end Chazelle.Core
