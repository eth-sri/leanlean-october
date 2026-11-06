module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseHostSimple

/-!
# WP-M (X, part 5): the sorted host keys of a region

For a region `U` of a submap `F` (walk-axiom model), the sorted host keys `hk i` of `U`
(`hostKeyList`) are strictly increasing, they are exactly the host keys, and consecutive ones
(cyclically) span a **gap** of one of two kinds (`gap_cases`):
* **arc gap** (`ArcGap`): the gap lies in an arc of `U`;
* **chord gap** (`ChordGap`): a chord of `F` is attached at both ends.
No gap is of both kinds (`not_arc_and_chord`).
-/

namespace Chazelle.Core

namespace DownHost

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sideInArc sidePt)
open Chazelle.Geometry (lerp lerp_mem_segment)

variable {M : Model} {F : Set (Set Point)} {U : Set Point}

section
variable (M : Model) (F : Set (Set Point)) (U : Set Point)
include M F U
/-- The `i`-th host key. -/
noncomputable def hk (i : ℕ) : ℝ :=
  (hostKeyList M F U).getD i 0

/-- The number of host keys. -/
noncomputable def nk : ℕ :=
  (hostKeyList M F U).length


end

section

variable (hM : WalkAx M) (hF : F ⊆ M.Adm) (hfin : F.Finite)
include hM hF hfin

theorem hk_mem_iff (x : ℝ) : x ∈ hostKeyList M F U ↔ x ∈ hostKeys M F U := by
  rw [hostKeyList_eq (hostKeys_finite hM hF hfin), Finset.mem_sort, Set.Finite.mem_toFinset]

/-- **The host keys are strictly increasing.** -/
theorem hk_strictMono {i j : ℕ} (hij : i < j) (hj : j < nk M F U) : hk M F U i < hk M F U j := by
  have hS := hostKeys_finite (U := U) hM hF hfin
  have hL := hostKeyList_eq (U := U) hS
  have hsorted : (hostKeyList M F U).Pairwise (· ≤ ·) := by
    simp_all
  have hnodup : (hostKeyList M F U).Nodup := by simp_all
  unfold hk
  rw [List.getD_eq_getElem _ _ (lt_trans hij hj), List.getD_eq_getElem _ _ hj]
  refine lt_of_le_of_ne (List.pairwise_iff_getElem.1 hsorted i j (lt_trans hij hj) hj hij) ?_
  grind

theorem hk_inj {i j : ℕ} (hi : i < nk M F U) (hj : j < nk M F U) (h : hk M F U i = hk M F U j) :
    i = j := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h' | h'
  · exact absurd h (hk_strictMono hM hF hfin h' hj).ne
  · exact absurd h.symm (hk_strictMono hM hF hfin h' hi).ne

theorem hk_mem {i : ℕ} (hi : i < nk M F U) : hk M F U i ∈ hostKeys M F U := by
  rw [← hk_mem_iff hM hF hfin]; unfold hk; rw [List.getD_eq_getElem _ _ hi]
  grind

theorem exists_hk {x : ℝ} (hx : x ∈ hostKeys M F U) : ∃ i, i < nk M F U ∧ hk M F U i = x := by
  rw [← hk_mem_iff hM hF hfin] at hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  exact ⟨i, hi, by simp_all [hk] <;> omega_nf⟩

section
variable (h2 : 2 ≤ nk M F U) {i : ℕ} (hi : i < nk M F U)
include h2 hi
/-- **No host key inside a gap.** -/
theorem hk_gap {x : ℝ}
    (hx : x ∈ hostKeys M F U) :
    ¬ sideInArc (hk M F U i) (hk M F U ((i + 1) % nk M F U)) x :=
  sorted_gap (fun _ _ hij hj => hk_strictMono hM hF hfin hij hj) h2 hi
    ((hk_mem_iff hM hF hfin x).2 hx)

theorem hk_succ_ne :
    hk M F U i ≠ hk M F U ((i + 1) % nk M F U) := by
  intro h
  have := hk_inj hM hF hfin hi (Nat.mod_lt _ (by omega)) h
  by_cases h1 : i + 1 < nk M F U
  · rw [Nat.mod_eq_of_lt h1] at this; omega
  grind [Nat.mod_self]


end

end

section
variable (M : Model) (F : Set (Set Point)) (U : Set Point) (i : ℕ)
include M F U i
/-- **An arc gap**: the gap after the host key `i` lies in an arc of `U`. -/
def ArcGap : Prop :=
  ∃ a b : ℝ, M.IsArc F U a b ∧
    ∀ x : ℝ, 0 ≤ x → x < M.W.n →
      sideInArc (hk M F U i) (hk M F U ((i + 1) % nk M F U)) x → sideInArc a b x

/-- **A chord gap**: a chord of `F` is attached at both ends of the gap after the host key `i`,
at distinct points. -/
def ChordGap : Prop :=
  ∃ c ∈ F, ∃ (p p' : ℕ) (t t' : ℝ), SideAttach M.W c p t ∧ SideAttach M.W c p' t' ∧
    hk M F U i = p + t ∧ hk M F U ((i + 1) % nk M F U) = p' + t' ∧
    sidePt M.W p t ≠ sidePt M.W p' t'


end

section
variable (hM : WalkAx M) (hF : F ⊆ M.Adm) (hfin : F.Finite)
include hM hF hfin
/-- **Every gap is an arc gap or a chord gap.** -/
theorem gap_cases (hne : F.Nonempty)
    (hU : U ∈ M.regions F) (h2 : 2 ≤ nk M F U) {i : ℕ} (hi : i < nk M F U) :
    ArcGap M F U i ∨ ChordGap M F U i := by
  have hsi : (i + 1) % nk M F U < nk M F U := Nat.mod_lt _ (by omega)
  rcases gap hM hF hfin hne hU (hk_mem hM hF hfin hi) (hk_mem hM hF hfin hsi)
    (hk_succ_ne hM hF hfin h2 hi) (fun x hx => hk_gap hM hF hfin h2 hi hx) with
    ⟨a, b, harc, hsub⟩ | h
  · exact Or.inl ⟨a, b, harc, fun x _ _ hx => hsub x hx⟩
  · exact Or.inr h

/-- **No gap is of both kinds**: the chord would run along the walk. -/
theorem not_arc_and_chord
    (h2 : 2 ≤ nk M F U) {i : ℕ} (hi : i < nk M F U) (hA : ArcGap M F U i)
    (hC : ChordGap M F U i) : False := by
  obtain ⟨a', b', harc, hsub⟩ := hA
  obtain ⟨c, hc, p, p', t, t', hAt, hBt, ha, hb, hAB⟩ := hC
  have hsi : (i + 1) % nk M F U < nk M F U := Nat.mod_lt _ (by omega)
  have hb1 := hostKeys_bounds (hk_mem hM hF hfin hi)
  have hb2 := hostKeys_bounds (hk_mem hM hF hfin hsi)
  have hnv : ∀ k : ℕ, k < M.W.n →
      ¬ sideInArc (hk M F U i) (hk M F U ((i + 1) % nk M F U)) k := by
    intro k hk hkin
    exact hk_gap hM hF hfin h2 hi
      (Or.inr ⟨k, hk, rfl, a', b', harc, hsub k (Nat.cast_nonneg k) (by exact_mod_cast hk) hkin⟩)
      hkin
  have hPa : hostPt M.W (hk M F U i) = sidePt M.W p t := by
    rw [ha, hostPt_eq M.W hAt.2.1 hAt.2.2.1]
  have hPb : hostPt M.W (hk M F U ((i + 1) % nk M F U)) = sidePt M.W p' t' := by
    rw [hb, hostPt_eq M.W hBt.2.1 hBt.2.2.1]
  obtain ⟨-, -, hopen, -, -⟩ := hM.attach_seg (hF hc) hAt hBt hAB
  obtain ⟨q, hq, s, hs0, hs1, hz, -⟩ := arcEdge_of_noVertex M.W hb1.1 hb1.2 hb2.1 hb2.2
    (hk_succ_ne hM hF hfin h2 hi) hnv
    (lerp (hostPt M.W (hk M F U i)) (hostPt M.W (hk M F U ((i + 1) % nk M F U))) (1 / 2))
    (lerp_mem_segment _ _ (by norm_num) (by norm_num))
  have hD := hopen (1 / 2) ⟨by norm_num, by norm_num⟩
  rw [← hPa, ← hPb, hz] at hD
  exact hM.trace q hq s hs0 hs1.le hD


end

end

end DownHost

end Chazelle.Core
