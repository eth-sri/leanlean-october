module

public import Chazelle.Core.RestoreFTile
public import Chazelle.Core.RestoreFPieceGeo

/-!
# WP-E, the search: the walk vertices of a light key interval

The walk vertices of a closed key interval of weight `≤ 1` lie within `9` steps of its start edge
(at most one counted and seven uncounted walk edges come before them) — the cover of a kind-0
piece by its vertex tests.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Chazelle.Chain (sideInArc)
open DownHost ArcT

/-- The walk edges meeting the open cyclic key interval `(a, b)`. -/
def MeetsArc (M : Model) (a b : ℝ) (p : ℕ) : Prop :=
  p < M.W.n ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧ sideInArc a b (p + t)

theorem wrapK_bounds {n x : ℝ} (h0 : 0 ≤ x) (h1 : x < 2 * n) :
    0 ≤ wrapK n x ∧ wrapK n x < n := by
  unfold wrapK; split_ifs with h <;> constructor <;> linarith

theorem unwrapK_wrapK {n l x : ℝ} (_hl : 0 ≤ l ∧ l < n) (h0 : l ≤ x) (h1 : x < l + n) :
    unwrapK n l (wrapK n x) = x := by
  unfold wrapK unwrapK
  split_ifs with h2 h3 <;> linarith

/-- **An edge of the unwrapped interval `[⌊a⌋, P)` meets the interval `(a, b)`.** -/
theorem meets_of_unwrapped {M : Model} {a b : ℝ} (ha : 0 ≤ a ∧ a < M.W.n)
    (hb : 0 ≤ b ∧ b < M.W.n) (hab : a < unwrapK M.W.n a b) {j : ℕ} (hja : (j : ℝ) + 1 > a)
    (hjb : (j : ℝ) + 1 ≤ unwrapK M.W.n a b) (_hjn : (j : ℝ) < a + M.W.n) :
    MeetsArc M a b (j % M.W.n) := by
  set n := M.W.n
  have hn : (0 : ℝ) < n := by linarith [ha.1, ha.2]
  have hnN : 0 < n := by exact_mod_cast hn
  set y : ℝ := (max a j + (j + 1)) / 2 with hy
  have hy1 : a < y := by
    have := le_max_left a (j : ℝ); have := max_lt (show a < (j : ℝ) + 1 by linarith)
      (show (j : ℝ) < (j : ℝ) + 1 by linarith); rw [hy]; linarith
  have hy2 : (j : ℝ) < y := by
    have := le_max_right a (j : ℝ)
    rw [hy]
    rcases le_or_gt a j with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h.le]; linarith
  have hy3 : y < j + 1 := by
    have := max_lt (show a < (j : ℝ) + 1 by linarith) (show (j : ℝ) < (j : ℝ) + 1 by linarith)
    rw [hy]; linarith
  have hub := (unwrapK_bounds ha hb).2
  -- the wrapped point
  have hyb : 0 ≤ y ∧ y < 2 * n := ⟨by linarith [ha.1], by linarith⟩
  have hw := wrapK_bounds hyb.1 hyb.2
  have huw : unwrapK n a (wrapK n y) = y := unwrapK_wrapK ha hy1.le (by linarith)
  have hin : sideInArc a b (wrapK n y) :=
    (cyc_unwrap ha ha hb hw (by rw [unwrapK_self]; exact hab)).2
      ⟨by rw [unwrapK_self, huw]; exact hy1, by rw [huw]; linarith⟩
  refine ⟨Nat.mod_lt _ hnN, y - j, by linarith, by linarith, ?_⟩
  have e : ((j % n : ℕ) : ℝ) + (y - j) = wrapK n y := by
    unfold wrapK
    by_cases hj : j < n
    · rw [Nat.mod_eq_of_lt hj]
      have : y < n := by
        have : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
        linarith
      rw [ite_eq_left this]; ring
    · have hj2 : j - n < n := by
        have : (j : ℝ) < 2 * n := by linarith
        have : j < 2 * n := by exact_mod_cast this
        omega
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hj2]
      have : ¬ y < n := by
        have : (n : ℝ) ≤ j := by exact_mod_cast (by omega : n ≤ j)
        linarith
      rw [ite_eq_right this, Nat.cast_sub (by omega)]; ring
  rw [e]; exact hin

/-- **The walk vertices of a light closed key interval** are within `9` steps of its start edge. -/
theorem light_cover {M : Model} {Q : Polygon} {n0 : ℕ}
    (hunc : {p | p < M.W.n ∧ ¬ M.counted p}.ncard ≤ 7) {s e : WPos}
    (hs : ProperPos M Q n0 s) (hse : s.edge < M.W.n) (hke : 0 ≤ M.key Q e ∧ M.key Q e < M.W.n)
    (hne : M.key Q s ≠ M.key Q e) (hwt : M.arcWt (M.key Q s) (M.key Q e) ≤ 1) {p : ℕ}
    (hp : p < M.W.n) (hx : ClosedArc (M.key Q s) (M.key Q e) p) :
    ∃ t, t < 10 ∧ (s.edge + t) % M.W.n = p := by
  classical
  set n := M.W.n with hndef
  have hnN : 0 < n := by omega
  set a := M.key Q s with hadef
  set b := M.key Q e with hbdef
  have hkey : a = s.edge + M.param Q s := rfl
  have ha : 0 ≤ a ∧ a < n := by
    have : (s.edge : ℝ) + 1 ≤ n := by exact_mod_cast hse
    constructor <;> linarith [hs.1, hs.2.1]
  have hab : a < unwrapK n a b := by
    have := unwrapK_bounds ha hke
    unfold unwrapK at *
    split_ifs at * with h1
    · exact lt_of_le_of_ne h1 hne
    · linarith [ha.2, hke.1]
  have hpn : (0 : ℝ) ≤ p ∧ (p : ℝ) < n := ⟨by positivity, by exact_mod_cast hp⟩
  -- the unwrapped vertex
  set P := unwrapK n a p with hPdef
  have hPb : a ≤ P ∧ P ≤ unwrapK n a b := by
    rcases hx with hx | hx | hx
    · have := (cyc_unwrap ha ha hke hpn (by rw [unwrapK_self]; exact hab)).1 hx
      rw [unwrapK_self] at this; exact ⟨this.1.le, this.2.le⟩
    · rw [hPdef, hx, unwrapK_self]; exact ⟨le_rfl, hab.le⟩
    · rw [hPdef, hx]; exact ⟨hab.le, le_rfl⟩
  -- `P` is the natural `p` or `p + n`
  obtain ⟨Pn, hPn, hPmod⟩ : ∃ Pn : ℕ, (Pn : ℝ) = P ∧ Pn % n = p := by
    rw [hPdef]; unfold unwrapK
    split_ifs
    · exact ⟨p, rfl, Nat.mod_eq_of_lt hp⟩
    · exact ⟨p + n, by push_cast; ring, by rw [Nat.add_mod_right, Nat.mod_eq_of_lt hp]⟩
  have hsP : s.edge ≤ Pn := by
    have : (s.edge : ℝ) ≤ Pn := by rw [hPn]; linarith [hPb.1, hs.1]
    exact_mod_cast this
  set t := Pn - s.edge with htdef
  have hub := (unwrapK_bounds ha hke).2
  have htn : t ≤ n := by
    have : (Pn : ℝ) < s.edge + 1 + n := by rw [hPn]; linarith [hs.2.1]
    have : Pn < s.edge + 1 + n := by exact_mod_cast this
    omega
  -- the `t` edges before the vertex meet the interval
  have hmeet : ∀ d, d < t → MeetsArc M a b ((s.edge + d) % n) := fun d hd =>
    meets_of_unwrapped ha hke hab
      (by have : (s.edge : ℝ) ≤ ((s.edge + d : ℕ) : ℝ) := by exact_mod_cast (by omega)
          linarith [hs.2.1])
      (by have : ((s.edge + d : ℕ) : ℝ) + 1 ≤ Pn := by exact_mod_cast (by omega)
          linarith [hPb.2])
      (by have : ((s.edge + d : ℕ) : ℝ) + 1 ≤ Pn := by exact_mod_cast (by omega)
          linarith [hPb.2])
  -- counting
  set S : Set ℕ := (fun d => (s.edge + d) % n) '' Set.Iio t with hS
  have hinj : Set.InjOn (fun d => (s.edge + d) % n) (Set.Iio t) := by
    intro x hx y hy hxy
    simp only [Set.mem_Iio] at hx hy
    simp only at hxy
    by_contra hne'
    rcases Nat.lt_or_gt_of_ne hne' with h | h
    · obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' h.le).1 (Nat.ModEq.add_left_cancel' _ hxy)
      rcases k with _ | k
      · omega
      · have : n * (k + 1) ≥ n := Nat.le_mul_of_pos_right _ (by omega)
        omega
    · obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' h.le).1 (Nat.ModEq.add_left_cancel' _ hxy).symm
      rcases k with _ | k
      · omega
      · have : n * (k + 1) ≥ n := Nat.le_mul_of_pos_right _ (by omega)
        omega
  have hcS : S.ncard = t := by
    rw [hS, hinj.ncard_image, Set.ncard_eq_toFinset_card', Set.toFinset_Iio]
    simp
  have hSf : S.Finite := (Set.finite_Iio t).image _
  have h1 : (S ∩ {p | M.counted p}).ncard ≤ 1 := by
    refine le_trans (Set.ncard_le_ncard ?_ ?_) hwt
    · rintro x ⟨⟨d, hd, rfl⟩, hc⟩
      obtain ⟨hlt, τ, h0, h1, hi⟩ := hmeet d hd
      exact ⟨hlt, hc, τ, h0, h1, hi⟩
    · exact (Set.finite_Iio n).subset (fun x hx => hx.1)
  have h2 : (S \ {p | M.counted p}).ncard ≤ 7 := by
    refine le_trans (Set.ncard_le_ncard ?_ ?_) hunc
    · rintro x ⟨⟨d, hd, rfl⟩, hc⟩
      exact ⟨Nat.mod_lt _ hnN, hc⟩
    · exact (Set.finite_Iio n).subset (fun x hx => hx.1)
  have h3 := Set.ncard_inter_add_ncard_sdiff_eq_ncard S {p | M.counted p} hSf
  refine ⟨t, by omega, ?_⟩
  rw [htdef, show s.edge + (Pn - s.edge) = Pn by omega, hPmod]

/-- **The steps from the start edge to a walk vertex of a closed key interval** are at most its
weight plus the uncounted edges. -/
theorem steps_le {M : Model} {Q : Polygon} {n0 : ℕ}
    {w u : ℕ} (hunc : {p | p < M.W.n ∧ ¬ M.counted p}.ncard ≤ u) {s e : WPos}
    (hs : ProperPos M Q n0 s) (hse : s.edge < M.W.n) (hke : 0 ≤ M.key Q e ∧ M.key Q e < M.W.n)
    (hne : M.key Q s ≠ M.key Q e) (hwt : M.arcWt (M.key Q s) (M.key Q e) ≤ w) {p : ℕ}
    (hp : p < M.W.n) (hx : ClosedArc (M.key Q s) (M.key Q e) p) :
    ∃ t, t ≤ w + u ∧ (s.edge + t) % M.W.n = p ∧
      ((s.edge + t : ℕ) : ℝ) = unwrapK M.W.n (M.key Q s) p := by
  classical
  set n := M.W.n with hndef
  have hnN : 0 < n := by omega
  set a := M.key Q s with hadef
  set b := M.key Q e with hbdef
  have hkey : a = s.edge + M.param Q s := rfl
  have ha : 0 ≤ a ∧ a < n := by
    have : (s.edge : ℝ) + 1 ≤ n := by exact_mod_cast hse
    constructor <;> linarith [hs.1, hs.2.1]
  have hab : a < unwrapK n a b := by
    have := unwrapK_bounds ha hke
    unfold unwrapK at *
    split_ifs at * with h1
    · exact lt_of_le_of_ne h1 hne
    · linarith [ha.2, hke.1]
  have hpn : (0 : ℝ) ≤ p ∧ (p : ℝ) < n := ⟨by positivity, by exact_mod_cast hp⟩
  -- the unwrapped vertex
  set P := unwrapK n a p with hPdef
  have hPb : a ≤ P ∧ P ≤ unwrapK n a b := by
    rcases hx with hx | hx | hx
    · have := (cyc_unwrap ha ha hke hpn (by rw [unwrapK_self]; exact hab)).1 hx
      rw [unwrapK_self] at this; exact ⟨this.1.le, this.2.le⟩
    · rw [hPdef, hx, unwrapK_self]; exact ⟨le_rfl, hab.le⟩
    · rw [hPdef, hx]; exact ⟨hab.le, le_rfl⟩
  -- `P` is the natural `p` or `p + n`
  obtain ⟨Pn, hPn, hPmod⟩ : ∃ Pn : ℕ, (Pn : ℝ) = P ∧ Pn % n = p := by
    rw [hPdef]; unfold unwrapK
    split_ifs
    · exact ⟨p, rfl, Nat.mod_eq_of_lt hp⟩
    · exact ⟨p + n, by push_cast; ring, by rw [Nat.add_mod_right, Nat.mod_eq_of_lt hp]⟩
  have hsP : s.edge ≤ Pn := by
    have : (s.edge : ℝ) ≤ Pn := by rw [hPn]; linarith [hPb.1, hs.1]
    exact_mod_cast this
  set t := Pn - s.edge with htdef
  have hub := (unwrapK_bounds ha hke).2
  have htn : t ≤ n := by
    have : (Pn : ℝ) < s.edge + 1 + n := by rw [hPn]; linarith [hs.2.1]
    have : Pn < s.edge + 1 + n := by exact_mod_cast this
    omega
  -- the `t` edges before the vertex meet the interval
  have hmeet : ∀ d, d < t → MeetsArc M a b ((s.edge + d) % n) := fun d hd =>
    meets_of_unwrapped ha hke hab
      (by have : (s.edge : ℝ) ≤ ((s.edge + d : ℕ) : ℝ) := by exact_mod_cast (by omega)
          linarith [hs.2.1])
      (by have : ((s.edge + d : ℕ) : ℝ) + 1 ≤ Pn := by exact_mod_cast (by omega)
          linarith [hPb.2])
      (by have : ((s.edge + d : ℕ) : ℝ) + 1 ≤ Pn := by exact_mod_cast (by omega)
          linarith [hPb.2])
  -- counting
  set S : Set ℕ := (fun d => (s.edge + d) % n) '' Set.Iio t with hS
  have hinj : Set.InjOn (fun d => (s.edge + d) % n) (Set.Iio t) := by
    intro x hx y hy hxy
    simp only [Set.mem_Iio] at hx hy
    simp only at hxy
    by_contra hne'
    rcases Nat.lt_or_gt_of_ne hne' with h | h
    · obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' h.le).1 (Nat.ModEq.add_left_cancel' _ hxy)
      rcases k with _ | k
      · omega
      · have : n * (k + 1) ≥ n := Nat.le_mul_of_pos_right _ (by omega)
        omega
    · obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' h.le).1 (Nat.ModEq.add_left_cancel' _ hxy).symm
      rcases k with _ | k
      · omega
      · have : n * (k + 1) ≥ n := Nat.le_mul_of_pos_right _ (by omega)
        omega
  have hcS : S.ncard = t := by
    rw [hS, hinj.ncard_image, Set.ncard_eq_toFinset_card', Set.toFinset_Iio]
    simp
  have hSf : S.Finite := (Set.finite_Iio t).image _
  have h1 : (S ∩ {p | M.counted p}).ncard ≤ w := by
    refine le_trans (Set.ncard_le_ncard ?_ ?_) hwt
    · rintro x ⟨⟨d, hd, rfl⟩, hc⟩
      obtain ⟨hlt, τ, h0, h1, hi⟩ := hmeet d hd
      exact ⟨hlt, hc, τ, h0, h1, hi⟩
    · exact (Set.finite_Iio n).subset (fun x hx => hx.1)
  have h2 : (S \ {p | M.counted p}).ncard ≤ u := by
    refine le_trans (Set.ncard_le_ncard ?_ ?_) hunc
    · rintro x ⟨⟨d, hd, rfl⟩, hc⟩
      exact ⟨Nat.mod_lt _ hnN, hc⟩
    · exact (Set.finite_Iio n).subset (fun x hx => hx.1)
  have h3 := Set.ncard_inter_add_ncard_sdiff_eq_ncard S {p | M.counted p} hSf
  refine ⟨t, by omega, ?_, ?_⟩
  · rw [htdef, show s.edge + (Pn - s.edge) = Pn by omega, hPmod]
  · rw [htdef, show s.edge + (Pn - s.edge) = Pn by omega, hPn]

end

end Restore

end Chazelle.Core
