module

public import Chazelle.Core.DownPhaseArcBrk
public import Chazelle.Core.DownPhaseBoxAttach
public import Chazelle.Core.FactsInterior
public import Chazelle.Core.GranRemove

/-!
# WP-M (X, part 3): localization in the interior model

For a submap `F` of the interior model of a simple polygon `Q`:

* **near a non-cut position the domain is in the faced region** (`near_sub_region`): if `(p, t)`
  is not a cut of `F` and the positions just after it face `U`, then the domain points near its
  point lie in `U`;
* **localization** (`regions_local`, `touches_local`, `exits_local`): adding chords whose
  domain parts lie in one region `R` of `S` changes only the regions inside `R`, and the other
  regions keep their exits.
-/

namespace Chazelle.Core

namespace Loc

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideLeftOf sidePrev sideNext SideClean
  ChordSystem freeIn regionsIn TouchesIn IsHChordIn)
open Chazelle.Jordan (offset)
open Chazelle.Visibility (hseg)

/-- Scaling keeps the right-neighbourhood filter of `0`. -/
theorem tendsto_mul_const_nhdsGT {c : ℝ} (hc : 0 < c) :
    Tendsto (fun δ : ℝ => δ * c) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun x hx => ?_⟩
  · have : Tendsto (fun δ : ℝ => δ * c) (𝓝 0) (𝓝 (0 * c)) :=
      (continuous_id.mul continuous_const).tendsto 0
    rw [zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  simp_all

variable {Q : Polygon}

/-- **Near a non-cut position, the domain is in the region faced just after it.** -/
theorem near_sub_region (hQ : Q.Simple) {F : Set (Set Point)}
    (hF : F ⊆ (interiorModel Q).Adm) (hfin : F.Finite) {p : ℕ} {t : ℝ}
    (hp : p < (interiorModel Q).W.n) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hcut : ¬ (interiorModel Q).IsCut F (p + t)) {U : Set Point}
    (hU : U ∈ (interiorModel Q).regions F)
    (hfU : ∀ᶠ s in 𝓝[>] (0 : ℝ), (interiorModel Q).Faces p (t + s * (1 - t)) U) :
    ∃ r > 0, ∀ x ∈ ball (sidePt (interiorModel Q).W p t) r, x ∈ (interiorModel Q).D → x ∈ U := by
  set M := interiorModel Q with hMdef
  set W := M.W
  set z := sidePt W p t with hz
  obtain ⟨hWs, hWb, hWf, hWo⟩ := FactsInterior.interiorWalk_spec hQ
  have hM : WalkAx M := walkAx_interiorModel hQ
  
  obtain ⟨rL, hrL, hleft⟩ := FactsInterior.interior_left hWs hWo hp ht0 ht1
  obtain ⟨rC, hrC, hclean⟩ := FactsInterior.clean hWs hWo hp ht0 ht1
  -- the point is on no chord of `F`
  have hzF : ∀ c ∈ F, z ∉ c := by
    intro c hc hzc
    obtain ⟨y, a, b, hh, rfl⟩ := hF hc
    have hzD : z ∉ M.D := hM.trace p hp t ht0 ht1.le
    have hab := hh.lt
    have hzy : z.2 = y := hzc.1
    refine hcut ⟨hseg y a b, hc, p, t, ⟨hp, ht0, ht1, hzc, min (b - a) rL,
      lt_min (by linarith) hrL, fun x hx hxz hdist => ?_⟩, rfl⟩
    have hd1 : |x.1 - z.1| < b - a := by
      grind [Prod.dist_eq, Real.dist_eq]
    have hxy : x.2 = y := hx.1
    -- `z` is an end of the chord
    have hzend : z.1 = a ∨ z.1 = b := by
      by_contra hne
      push Not at hne
      apply hzD
      have := hh.open_mem z.1 (lt_of_le_of_ne hzc.2.1 (Ne.symm hne.1))
        (lt_of_le_of_ne hzc.2.2 hne.2)
      rw [← hzy] at this
      exact this
    have hx1 : x.1 ≠ z.1 := fun e => hxz (Prod.ext e (hxy.trans hzy.symm))
    have hxD : x ∈ M.D := by
      have hxo : a < x.1 ∧ x.1 < b := by
        rcases hzend with he | he <;> rw [abs_lt] at hd1 <;> refine ⟨?_, ?_⟩
        · exact lt_of_le_of_ne hx.2.1 (fun e => hx1 (by rw [he, e]))
        · linarith
        · linarith
        · exact lt_of_le_of_ne hx.2.2 (fun e => hx1 (by rw [he, e]))
      have := hh.open_mem x.1 hxo.1 hxo.2
      rw [← hxy] at this; exact this
    refine hleft x (lt_of_lt_of_le hdist (min_le_right _ _)) ?_
    rw [hWb, hWf]; exact hxD
  -- a ball avoiding all chords
  have hev : ∀ᶠ x in 𝓝 z, ∀ c ∈ F, x ∉ c := by
    refine (hfin.eventually_all (p := fun c x => x ∉ c)).2 fun c hc => ?_
    obtain ⟨y, a, b, -, rfl⟩ := hF hc
    exact (Chazelle.Chain.isClosed_hseg y a b).isOpen_compl.mem_nhds (hzF _ hc)
  obtain ⟨rF, hrF, hballF⟩ := Metric.eventually_nhds_iff.1 hev
  set r := min rF (min rL rC)
  have hr : 0 < r := lt_min hrF (lt_min hrL hrC)
  have hrF' : r ≤ rF := min_le_left _ _
  have hrL' : r ≤ rL := le_trans (min_le_right _ _) (min_le_left _ _)
  have hrC' : r ≤ rC := le_trans (min_le_right _ _) (min_le_right _ _)
  -- the corner
  have hnd := hM.nd p hp
  have hbv : sideNext W p ≠ z := by
    unfold sideNext
    rw [hz]
    unfold sidePt
    exact (Chazelle.Jordan.lerp_ne_right hnd ht1).symm
  have hav : sidePrev W p t ≠ z := by
    unfold sidePrev
    split_ifs with ht
    · subst ht
      rw [hz, Chazelle.Chain.sidePt_zero]
      have hn : 0 < W.n := by omega
      have hq := hM.nd ((p + W.n - 1) % W.n) (Nat.mod_lt _ hn)
      rw [BoxT.prev_succ hp] at hq
      exact hq
    · rw [hz]; unfold sidePt
      exact (Chazelle.Jordan.lerp_ne_left hnd (lt_of_le_of_ne ht0 (Ne.symm ht))).symm
  have hsec := Chazelle.Chain.sideSector (S := (freeIn M.D F)ᶜ) hav hbv hr (by
    intro x hx hxS hxl
    apply hxS
    refine ⟨?_, fun ⟨c, hc, hxc⟩ => hballF (lt_of_lt_of_le hx hrF') c hc hxc⟩
    by_contra hxD
    exact hclean x (lt_of_lt_of_le hx hrC') (by rw [hWb, hWf]; exact hxD) hxl)
  obtain ⟨hsub, hpre, hoff⟩ := hsec
  set L := ball z r ∩ {x | sideLeftOf (sidePrev W p t) z (sideNext W p) x}
  have hLfree : L ⊆ freeIn M.D F := fun x hx => not_not.1 (hsub hx)
  -- the sector meets `U`
  have hmeet : (L ∩ U).Nonempty := by
    have h1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), (∀ᶠ δ in 𝓝[>] (0 : ℝ),
        offset (sidePrev W p t) z (1 - s) (1 * δ) ∈ L ∧ offset z (sideNext W p) s (1 * δ) ∈ L) ∧
        M.Faces p (t + s * (1 - t)) U := hoff.and hfU
    obtain ⟨s, hs1, hs2⟩ := h1.exists
    have h2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        offset (M.wa p) (M.wb p) (t + s * (1 - t)) (δ * (1 - t)) ∈ U :=
      (tendsto_mul_const_nhdsGT (show 0 < 1 - t by linarith)).eventually hs2
    obtain ⟨δ, hδ1, hδ2⟩ := (hs1.and h2).exists
    refine ⟨_, hδ1.2, ?_⟩
    rw [one_mul]
    have e : offset z (sideNext W p) s δ =
        offset (M.wa p) (M.wb p) (t + s * (1 - t)) (δ * (1 - t)) := by
      rw [hz]; unfold sidePt sideNext
      exact Chazelle.Chain.offset_lerp_left _ _ _ _ _
    grind
  have hLU : L ⊆ U := Chazelle.Chain.subset_regionsIn_of_inter hU hpre hLfree hmeet
  refine ⟨r, hr, fun x hx hxD => hLU ⟨hx, ?_⟩⟩
  have := hleft x (lt_of_lt_of_le hx hrL') (by rw [hWb, hWf]; exact hxD)
  exact this

/-! ## Adding chords inside one region -/

section Local

variable {D : Set Point} {S F : Set (Set Point)} {R : Set Point}

end Local

/-! ## Weights of the other regions -/

end

end Loc

end Chazelle.Core
