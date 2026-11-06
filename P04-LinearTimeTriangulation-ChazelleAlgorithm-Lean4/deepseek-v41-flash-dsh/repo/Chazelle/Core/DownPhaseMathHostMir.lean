module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseMathWalkAll

/-!
# Down phase, math (H-R1): host keys of a mirrored region

For the mirror image `Q.mir` of `Q` (`Mir.modelMir_interior`, shift `c = n - 1`, `n` the length of
the interior walk), the host keys of the mirrored region `mir '' R` of `mirF S` are the reflected
keys `rk n c x` of the host keys `x` of `R` (`hostKeys_mir`), their walk points are the mirrored
walk points (`hostPt_mir`), the sorted lists are reversed up to rotation (`hk_mir`), and chord gaps
correspond (`chordGap_mir`).
-/

namespace Chazelle.Core

namespace DownMath

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sideInArc sidePt TouchesIn)
open DownHost Mir

variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point}

/-- The walk points of a mirrored walk. -/
theorem hostPt_mir (hQ : Q.Simple) {x' : ℝ} (hx0 : 0 ≤ x') (hxn : x' < (interiorModel Q).W.n) :
    hostPt (interiorModel Q.mir).W x' =
      mir (hostPt (interiorModel Q).W (rk (interiorModel Q).W.n (Q.n - 1) x')) := by
  have h := modelMir_interior hQ
  have hn := h.walk.n_pos
  have hc := h.walk.c_lt
  set p := ⌊x'⌋₊ with hp
  set t := x' - ⌊x'⌋₊ with ht
  have ht0 : 0 ≤ t := by rw [ht]; linarith [Nat.floor_le hx0]
  have ht1 : t < 1 := by rw [ht]; linarith [Nat.lt_floor_add_one x']
  have hpn : p < (interiorModel Q).W.n := by
    have : (p : ℝ) < (interiorModel Q).W.n := lt_of_le_of_lt (Nat.floor_le hx0) hxn
    exact_mod_cast this
  have hx : x' = p + t := by rw [ht]; ring
  have hkey := posMir_key hc hpn ht0 ht1
  obtain ⟨b1, b2, b3⟩ := posMir_bounds (c := Q.n - 1) (p' := p) hn ht0 ht1
  have hs := h.walk.sidePt_mir hpn t
  have e1 : hostPt (interiorModel Q.mir).W x' = sidePt (interiorModel Q.mir).W p t := by
    rw [hx]; exact hostPt_eq _ ht0 ht1
  Ξ e1, hs, hx, ← hkey, hostPt_eq _ b2 b3

section

variable (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S) (hne : S.Nonempty)
  (hR : R ∈ (interiorModel Q).regions S)
include hQ hFam hne hR

omit hQ hFam hne hR in
/-- **Host keys of the mirrored region are the reflected host keys.** -/
theorem hostKeys_mir (hQ : Q.Simple) (_hFam : (interiorModel Q).ChordFamily Q S) (hne : S.Nonempty)
    (_hR : R ∈ (interiorModel Q).regions S) {x' : ℝ} (hx0 : 0 ≤ x')
    (hxn : x' < (interiorModel Q).W.n) :
    x' ∈ hostKeys (interiorModel Q.mir) (mirF S) (mir '' R) ↔
      rk (interiorModel Q).W.n (Q.n - 1) x' ∈ hostKeys (interiorModel Q) S R := by
  have h := modelMir_interior hQ
  have hc := h.walk.c_lt
  have hrk := rk_bounds hc hx0 hxn
  have hT : ∀ c : Set Point, TouchesIn (interiorModel Q.mir).D (mir '' c) (mir '' R) ↔
      TouchesIn (interiorModel Q).D c R := by
    intro c; rw [h.D]; exact touchesIn_mir
  have hnat : ∀ k : ℕ, k < (interiorModel Q).W.n →
      ∃ k' : ℕ, k' < (interiorModel Q).W.n ∧ rk (interiorModel Q).W.n (Q.n - 1) k = k' := by
    intro k hk
    exact ⟨_, Nat.mod_lt _ h.walk.n_pos, rk_nat hc hk⟩
  constructor
  · rintro (⟨c', hc', ht', p', t', hA', rfl⟩ | ⟨k, hk, rfl, a', b', harc', hin'⟩)
    · -- an exit key
      left
      have hp : p' < (interiorModel Q).W.n := h.n_eq ▸ hA'.1
      have hA'' : SideAttach (interiorModel Q.mir).W (mir '' (mir '' c')) p' t' := by
        rwa [image_mir_image_mir]
      Ξ' h.walk.sideAttach_mir hp hA'.2.1 hA'.2.2.1 at hA''
      refine ⟨mir '' c', mem_mirF.1 hc', ?_, _, _, hA'', ?_⟩
      · rw [← hT, image_mir_image_mir]; exact ht'
      · Ξ posMir_key hc hp hA'.2.1 hA'.2.2.1
    · -- a vertex key
      right
      have hk' : k < (interiorModel Q).W.n := h.n_eq ▸ hk
      have ha0 := harc'.1
      have han := harc'.2.1
      have hb0 := harc'.2.2.1
      have hbn := harc'.2.2.2.1
      Ξ' h.n_eq at han hbn
      Ξ' h.isArc hne R ha0 han hb0 hbn at harc'
      obtain ⟨k', hk'n, hkk⟩ := hnat k hk'
      refine ⟨k', hk'n, hkk, _, _, harc', ?_⟩
      Ξ ← hkk
      exact (sideInArc_rk hc ha0 han hb0 hbn (Nat.cast_nonneg k) (by exact_mod_cast hk')).1 hin'
  · rintro (⟨c, hc', ht, p, t, hA, hx⟩ | ⟨k, hk, hkx, a, b, harc, hin⟩)
    · -- an exit key
      left
      have hp : p < (interiorModel Q.mir).W.n := h.n_eq.symm ▸ hA.1
      have hA'' : SideAttach (interiorModel Q).W (mir '' (mir '' c)) p t := by
        rwa [image_mir_image_mir]
      Ξ' h.walk.symm.sideAttach_mir hp hA.2.1 hA.2.2.1 at hA''
      refine ⟨mir '' c, image_mem_mirF.2 hc', (hT c).2 ht, _, _, hA'', ?_⟩
      Ξ posMir_key h.walk.symm.c_lt hp hA.2.1 hA.2.2.1, h.n_eq, ← hx, rk_rk hc hx0 hxn
    · -- a vertex key
      right
      obtain ⟨k', hk'n, hkk⟩ := hnat k hk
      have hx' : x' = k' := Ρ ← rk_rk hc hx0 hxn, hkx, hkk
      have ha0 := harc.1
      have han := harc.2.1
      have hb0 := harc.2.2.1
      have hbn := harc.2.2.2.1
      obtain ⟨ra0, ran⟩ := rk_bounds hc ha0 han
      obtain ⟨rb0, rbn⟩ := rk_bounds hc hb0 hbn
      refine ⟨k', h.n_eq ▸ hk'n, hx', rk (interiorModel Q).W.n (Q.n - 1) b,
        rk (interiorModel Q).W.n (Q.n - 1) a, ?_, ?_⟩
      · Ξ h.isArc hne R rb0 rbn ra0 ran, rk_rk hc hb0 hbn, rk_rk hc ha0 han
        exact harc
      · Ξ ← hkk
        exact (sideInArc_rk hc ha0 han hb0 hbn (Nat.cast_nonneg k) (by exact_mod_cast hk)).1 hin

/-- **The sorted host keys of the mirrored region**: the reflected host keys of `R` in reversed
order, rotated (`a` the number of host keys `≤ c`). -/
theorem hk_mir : ∃ a, nk (interiorModel Q.mir) (mirF S) (mir '' R) = nk (interiorModel Q) S R ∧
    a ≤ nk (interiorModel Q) S R ∧
    ∀ j, j < nk (interiorModel Q) S R →
      hk (interiorModel Q.mir) (mirF S) (mir '' R) j =
        rk (interiorModel Q).W.n (Q.n - 1) (hk (interiorModel Q) S R
          ((a + nk (interiorModel Q) S R - 1 - j) % nk (interiorModel Q) S R)) := by
  classical
  set I := interiorModel Q with hI
  set I' := interiorModel Q.mir with hI'
  set K := nk I S R with hK
  set n := I.W.n with hn
  set c := Q.n - 1 with hcdef
  have h := modelMir_interior hQ
  have hc := h.walk.c_lt
  have hM : WalkAx I := walkAx_interiorModel hQ
  have hF := hFam.2.1
  have hfin := hFam.1
  have h3 : 3 ≤ K := three_le_nk hQ hFam hne hR
  have hb : ∀ i, i < K → 0 ≤ hk I S R i ∧ hk I S R i < n := fun i hi =>
    hostKeys_bounds (hk_mem hM hF hfin hi)
  -- the number of host keys `≤ c`
  have hex : ∃ i, K ≤ i ∨ (c : ℝ) < hk I S R i := ⟨K, Or.inl le_rfl⟩
  set a := Nat.find hex with ha
  have haK : a ≤ K := Nat.find_min' hex (Or.inl le_rfl)
  have hlow : ∀ i, i < a → hk I S R i ≤ c := by
    intro i hi
    have := Nat.find_min hex hi
    push Not at this
    exact this.2
  have hhigh : ∀ i, a ≤ i → i < K → (c : ℝ) < hk I S R i := by
    intro i hai hi
    rcases Nat.find_spec hex with h1 | h1
    · omega
    · rcases hai.lt_or_eq with h2 | h2
      · exact lt_trans h1 (hk_strictMono (U := R) hM hF hfin h2 hi)
      · rw [← h2]; exact h1
  -- the index map
  set σ : ℕ → ℕ := fun j => (a + K - 1 - j) % K with hσ
  have hσlo : ∀ j, j < a → σ j = a - 1 - j := by
    intro j hj
    ϴ hσ
    rw [show a + K - 1 - j = (a - 1 - j) + K by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (⋄)]
  have hσhi : ∀ j, a ≤ j → j < K → σ j = a + K - 1 - j := by
    intro j hj hjK
    ϴ hσ
    Ξ Nat.mod_eq_of_lt (⋄)
  have hσlt : ∀ j, j < K → σ j < K := fun j _ => Nat.mod_lt _ (⋄)
  have hσσ : ∀ i, i < K → σ (σ i) = i := by
    intro i hi
    by_cases hia : i < a
    · rw [hσlo i hia, hσlo _ (⋄)]; omega
    · rw [hσhi i (⋄) hi, hσhi _ (⋄) (⋄)]; omega
  -- the reflected keys
  have hrklo : ∀ i, i < a → rk n c (hk I S R i) = c - hk I S R i := by
    intro i hi; unfold rk; Ξ ite_eq_left (hlow i hi)
  have hrkhi : ∀ i, a ≤ i → i < K → rk n c (hk I S R i) = c - hk I S R i + n := by
    intro i hai hi; unfold rk; Ξ ite_eq_right (not_le.2 (hhigh i hai hi))
  set L' : List ℝ := (List.range K).map fun j => rk n c (hk I S R (σ j)) with hL'
  have hL'len : L'.length = K := ⊚ hL'
  have hL'get : ∀ j, j < K → L'.getD j 0 = rk n c (hk I S R (σ j)) := by
    intro j hj
    Ξ List.getD_eq_getElem _ _ (by rw [hL'len]; exact hj)
    Θ hL'
  -- strictly increasing
  have hcn : (c : ℝ) < n := by exact_mod_cast hc
  have hmono : ∀ j j', j < j' → j' < K → L'.getD j 0 < L'.getD j' 0 := by
    intro j j' hjj hj'
    Ξ hL'get j (⋄), hL'get j' hj'
    by_cases h1 : j' < a
    · Ξ hσlo j (⋄), hσlo j' h1, hrklo _ (⋄), hrklo _ (⋄)
      have := hk_strictMono (U := R) hM hF hfin (show a - 1 - j' < a - 1 - j by omega) (⋄)
      linarith
    · by_cases h2 : j < a
      · rw [hσlo j h2, hσhi j' (⋄) hj', hrklo _ (⋄),
          hrkhi _ (⋄) (⋄)]
        have := (hb (a - 1 - j) (⋄)).1
        have := (hb (a + K - 1 - j') (⋄)).2
        linarith
      · rw [hσhi j (⋄) (⋄), hσhi j' (⋄) hj', hrkhi _ (⋄) (⋄),
          hrkhi _ (⋄) (⋄)]
        have := hk_strictMono (U := R) hM hF hfin (show a + K - 1 - j' < a + K - 1 - j by omega)
          (⋄)
        linarith
  -- the same elements
  have hmem : ∀ x, x ∈ L' ↔ x ∈ hostKeys I' (mirF S) (mir '' R) := by
    intro x
    constructor
    · intro hx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
      Ξ' List.mem_range at hj
      have hb' := hb _ (hσlt j hj)
      obtain ⟨r0, rn⟩ := rk_bounds hc hb'.1 hb'.2
      Ξ hostKeys_mir hQ hFam hne hR r0 rn, rk_rk hc hb'.1 hb'.2
      exact hk_mem hM hF hfin (hσlt j hj)
    · intro hx
      have hM' : WalkAx I' := walkAx_interiorModel (mir_simple Q hQ)
      have hxb := hostKeys_bounds hx
      Ξ' h.n_eq at hxb
      have := (hostKeys_mir hQ hFam hne hR hxb.1 hxb.2).1 hx
      obtain ⟨i, hi, hie⟩ := exists_hk hM hF hfin this
      refine List.mem_map.2 ⟨σ i, List.mem_range.2 (hσlt i hi), ?_⟩
      Ξ hσσ i hi, hie, rk_rk hc hxb.1 hxb.2
  -- `L'` is the sorted host key list
  have hfin' : (hostKeys I' (mirF S) (mir '' R)).Finite := by
    have hM' : WalkAx I' := walkAx_interiorModel (mir_simple Q hQ)
    have hFam' := (h.chordFamily Q S).2 hFam
    exact hostKeys_finite hM' hFam'.2.1 hFam'.1
  have hsortL' : L'.Pairwise (· < ·) := by
    Ξ List.pairwise_iff_getElem
    intro j j' hj hj' hjj
    have := hmono j j' hjj (by rw [← hL'len]; exact hj')
    rwa [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj'] at this
  have heq : hostKeyList I' (mirF S) (mir '' R) = L' := by
    Ξ hostKeyList_eq hfin'
    apply List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 => le_antisymm h1 h2)
      (Finset.pairwise_sort _ _) (hsortL'.imp le_of_lt)
    Ξ List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) hsortL'.nodup
    intro x
    Ξ Finset.mem_sort, Set.Finite.mem_toFinset, hmem
  refine ⟨a, ?_, haK, fun j hj => ?_⟩
  · unfold nk; Ξ heq, hL'len
  · have e : hk I' (mirF S) (mir '' R) j = (hostKeyList I' (mirF S) (mir '' R)).getD j 0 := rfl
    Ξ e, heq, hL'get j hj

omit hFam hne hR in
/-- **Chord gaps correspond**: the gap of the mirrored region between the reflected keys of
`hk (g + 1)` and `hk g` is a chord gap. -/
theorem chordGap_mir {g : ℕ} (hC : ChordGap (interiorModel Q) S R g) {j : ℕ}
    (h1 : hk (interiorModel Q.mir) (mirF S) (mir '' R) j =
      rk (interiorModel Q).W.n (Q.n - 1) (hk (interiorModel Q) S R ((g + 1) % nk (interiorModel Q) S R)))
    (h2 : hk (interiorModel Q.mir) (mirF S) (mir '' R)
        ((j + 1) % nk (interiorModel Q.mir) (mirF S) (mir '' R)) =
      rk (interiorModel Q).W.n (Q.n - 1) (hk (interiorModel Q) S R g)) :
    ChordGap (interiorModel Q.mir) (mirF S) (mir '' R) j := by
  have h := modelMir_interior hQ
  have hc := h.walk.c_lt
  have hn := h.walk.n_pos
  obtain ⟨c0, hc0, p, p', t, t', hA, hA', e1, e2, hne'⟩ := hC
  -- the mirrored attachment of a position
  have hmir : ∀ (q : ℕ) (s : ℝ), SideAttach (interiorModel Q).W c0 q s →
      SideAttach (interiorModel Q.mir).W (mir '' c0) (posMir (interiorModel Q).W.n (Q.n - 1) q s).1
        (posMir (interiorModel Q).W.n (Q.n - 1) q s).2 ∧
      ((posMir (interiorModel Q).W.n (Q.n - 1) q s).1 : ℝ) +
        (posMir (interiorModel Q).W.n (Q.n - 1) q s).2 = rk (interiorModel Q).W.n (Q.n - 1) (q + s) ∧
      sidePt (interiorModel Q.mir).W (posMir (interiorModel Q).W.n (Q.n - 1) q s).1
        (posMir (interiorModel Q).W.n (Q.n - 1) q s).2 = mir (sidePt (interiorModel Q).W q s) := by
    intro q s hAq
    obtain ⟨b1, b2, b3⟩ := posMir_bounds (c := Q.n - 1) (p' := q) hn hAq.2.1 hAq.2.2.1
    have hpp := posMir_posMir hc hAq.1 hAq.2.2.1
    refine ⟨?_, posMir_key hc hAq.1 hAq.2.1 hAq.2.2.1, ?_⟩
    · rw [h.walk.sideAttach_mir b1 b2 b3, hpp]; exact hAq
    · Ξ h.walk.sidePt_mir b1, hpp
  obtain ⟨hB', hk', hs'⟩ := hmir p' t' hA'
  obtain ⟨hB, hk0, hs⟩ := hmir p t hA
  refine ⟨mir '' c0, image_mem_mirF.2 hc0, _, _, _, _, hB', hB, ?_, ?_, ?_⟩
  · Ξ h1, e2, hk'
  · Ξ h2, e1, hk0
  · rw [hs', hs]; exact fun e => hne' (mir_injective e).symm

end

end

end DownMath

end Chazelle.Core
