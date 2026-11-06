module

public import proofs.HordijkSteelThreshold.ReversibleRecordWords

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory

def reversibleRecordEvent (L M : ℕ) : Set InfiniteSplitEnvironment :=
  {field | ∃ w, w.length = M ∧ FiniteReversibleGenerated M L field w}

def firstRecordEvent (L B M : ℕ) : Set InfiniteSplitEnvironment :=
  {field | B < M ∧ field ∈ reversibleRecordEvent L M ∧
    ∀ k, B < k → k < M → field ∉ reversibleRecordEvent L k}

theorem firstRecordEvent_disjoint (L B : ℕ) {M N : ℕ} (hMN : M ≠ N) :
    Disjoint (firstRecordEvent L B M) (firstRecordEvent L B N) :=
  Set.disjoint_left.mpr fun _ hM hN =>
    (lt_or_gt_of_ne hMN).elim (fun hlt => hN.2.2 M hM.1 hlt hM.2.1) (fun hgt => hM.2.2 N hN.1 hgt hN.2.1)

theorem finiteReversibleGenerated_transfer_prefix {N M L : ℕ} (hNM : N ≤ M)
    {field other : InfiniteSplitEnvironment}
    (he : ∀ w : List Bool, w.length ≤ M → ∀ k : ℕ, k ≤ M → field w k = other w k)
    {w : List Bool} (h : FiniteReversibleGenerated N L field w) :
    FiniteReversibleGenerated N L other w := by
  induction h with
  | food hn hL hN => exact .food hn hL hN
  | @ligate u v _ _ ho hN ihu ihv =>
    exact .ligate ihu ihv (he (u ++ v) (hN.trans hNM) u.length (by simp at hN; omega) ▸ ho) hN
  | @left u v hu hv hp ho ih =>
    have hlen := finiteReversibleGenerated_length_le hp
    exact .left hu hv ih (he (u ++ v) (hlen.trans hNM) u.length (by simp at hlen; omega) ▸ ho)
  | @right u v hu hv hp ho ih =>
    have hlen := finiteReversibleGenerated_length_le hp
    exact .right hu hv ih (he (u ++ v) (hlen.trans hNM) u.length (by simp at hlen; omega) ▸ ho)

theorem firstRecordEvent_congr_prefix {L B M : ℕ}
    {field other : InfiniteSplitEnvironment}
    (he : ∀ w : List Bool, w.length ≤ M → ∀ k : ℕ, k ≤ M → field w k = other w k) :
    field ∈ firstRecordEvent L B M ↔ other ∈ firstRecordEvent L B M := by
  have hr {N : ℕ} (hNM : N ≤ M) : field ∈ reversibleRecordEvent L N ↔ other ∈ reversibleRecordEvent L N :=
    ⟨fun ⟨w, hw, hg⟩ => ⟨w, hw, finiteReversibleGenerated_transfer_prefix hNM he hg⟩,
     fun ⟨w, hw, hg⟩ => ⟨w, hw, finiteReversibleGenerated_transfer_prefix hNM (fun w hw k hk => (he w hw k hk).symm) hg⟩⟩
  exact and_congr_right' <| and_congr (hr le_rfl) <| forall₂_congr fun k _ =>
    forall_congr' fun hk => not_congr (hr hk.le)

end HordijkSteelThreshold
