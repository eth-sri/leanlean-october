module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SortList
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Basic

/-!
# Down-phase driver (RAM side): the mathematics of the bucket distribution

The splice of the down phase distributes the `n` new event codes `base + q` (`q < n`) into the
buckets `0 … A` given by `bk q` (a counting sort), then sorts every bucket.

* `bfilt bk n b`: the `q < n` with `bk q = b`, in increasing order; `bcnt bk q b` its length up to
  `q`; `bstart bk n b`: the first position of bucket `b`;
* **`bktList bk n A base`**: the codes grouped by bucket, `bfilt` order inside a bucket;
* `slot bk n q`: the position of `base + q` in `bktList` (`bktList_getD_slot`);
* `seg_eq_bktList`: a memory segment with `base + q` at every slot is `bktList`.
-/

namespace Chazelle.Core

namespace DrvR

open SortL

@[expose] public section

variable (bk : ℕ → ℕ)

/-- The `q < n` in bucket `b`, in increasing order. -/
def bfilt (n b : ℕ) : List ℕ := (List.range n).filter fun q => bk q = b

/-- The number of `q' < q` in bucket `b`. -/
def bcnt (q b : ℕ) : ℕ := (bfilt bk q b).length

/-- The first position of bucket `b`. -/
def bstart (n b : ℕ) : ℕ := ∑ b' ∈ Finset.range b, bcnt bk n b'

/-- **The codes grouped by bucket.** -/
def bktList (n A base : ℕ) : List ℕ :=
  (List.range (A + 1)).flatMap fun b => (bfilt bk n b).map (base + ·)

/-- The position of `base + q` in `bktList`. -/
def slot (n q : ℕ) : ℕ := bstart bk n (bk q) + bcnt bk q (bk q)

variable {bk}

theorem bfilt_succ (q b : ℕ) :
    bfilt bk (q + 1) b = bfilt bk q b ++ (if bk q = b then [q] else []) := by
  aesop (add simp [bfilt, List.range_succ, List.filter_append]) (add safe (by omega))

theorem bcnt_succ (q b : ℕ) : bcnt bk (q + 1) b = bcnt bk q b + (if bk q = b then 1 else 0) := by
  core_grind [bfilt_succ]


theorem bcnt_mono {q q' : ℕ} (h : q ≤ q') (b : ℕ) : bcnt bk q b ≤ bcnt bk q' b := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => grind [bcnt_succ]

theorem bstart_succ (n b : ℕ) : bstart bk n (b + 1) = bstart bk n b + bcnt bk n b := by
  core_grind [Finset.sum_range_succ]

theorem bstart_mono (n : ℕ) {b b' : ℕ} (h : b ≤ b') : bstart bk n b ≤ bstart bk n b' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => grind [bstart_succ]

/-- Elements of `bfilt` are below `n` and in the bucket. -/
theorem mem_bfilt {n b q : ℕ} : q ∈ bfilt bk n b ↔ q < n ∧ bk q = b := by
  unfold bfilt; simp

/-- The sum of the bucket sizes is `n` when every bucket is at most `A`. -/
theorem bstart_all {n A : ℕ} (hA : ∀ q, q < n → bk q ≤ A) : bstart bk n (A + 1) = n := by
  induction n with
  | zero => unfold bstart; aesop
  | succ n ih =>
    have ih' := ih fun q hq => hA q (by omega)
    unfold bstart at ih' ⊢
    simp_all [bcnt_succ, Finset.sum_add_distrib] 

/-- The first `b` buckets. -/
def bktPre (bk : ℕ → ℕ) (n b base : ℕ) : List ℕ :=
  (List.range b).flatMap fun b' => (bfilt bk n b').map (base + ·)

theorem getD_append_right' {l₁ l₂ : List ℕ} {i d : ℕ} (h : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i d = l₂.getD (i - l₁.length) d := by
  grind

theorem bktPre_succ (n b base : ℕ) :
    bktPre bk n (b + 1) base = bktPre bk n b base ++ (bfilt bk n b).map (base + ·) := by
  core_grind [List.range_succ, List.flatMap_append]

theorem bktPre_length (n b base : ℕ) : (bktPre bk n b base).length = bstart bk n b := by
  induction b with
  | zero => rfl
  | succ b ih => rw [bktPre_succ, List.length_append, ih, bstart_succ, List.length_map]; rfl

theorem bktList_eq (n A base : ℕ) : bktList bk n A base = bktPre bk n (A + 1) base := rfl

theorem bktList_length {n A base : ℕ} (hA : ∀ q, q < n → bk q ≤ A) :
    (bktList bk n A base).length = n := by
  rw [bktList_eq, bktPre_length, bstart_all hA]

/-- `bfilt n b` at index `bcnt q b` is `q`, for `q < n` in bucket `b`. -/
theorem bfilt_getD {n q b : ℕ} (hq : q < n) (hb : bk q = b) :
    (bfilt bk n b).getD (bcnt bk q b) 0 = q := by
  have hsplit : ∀ m, q < m → ∃ t, bfilt bk m b = bfilt bk q b ++ q :: t := by
    intro m
    induction m with
    | zero => omega
    | succ m ih =>
      intro hm
      rcases Nat.lt_or_ge q m with h | h
      · aesop (add simp [bfilt_succ]) (add safe (by omega))
      · have hqm : q = m := by omega
        simp_all [bfilt_succ] 
  obtain ⟨t, ht⟩ := hsplit n hq
  simp_all [bcnt, Nat.sub_self] 

/-- **The slot of a code.** -/
theorem bktList_getD_slot {n A base q : ℕ} (hq : q < n) (hA : bk q ≤ A) :
    (bktList bk n A base).getD (slot bk n q) 0 = base + q := by
  rw [bktList_eq]
  have hle : bk q + 1 ≤ A + 1 := by omega
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  have hpre : ∀ e, bktPre bk n (bk q + 1 + e) base =
      bktPre bk n (bk q) base ++ (bfilt bk n (bk q)).map (base + ·) ++
        (List.range' (bk q + 1) e).flatMap (fun b' => (bfilt bk n b').map (base + ·)) := by
    intro e
    induction e with
    | zero => rw [Nat.add_zero, bktPre_succ]; simp
    | succ e ih =>
      grind [bktPre_succ, List.range'_concat, List.flatMap_append]
  rw [hd, hpre, List.append_assoc, getD_append_right' (by
    core_grind [bktPre_length])]
  rw [bktPre_length, show slot bk n q - bstart bk n (bk q) = bcnt bk q (bk q) by unfold slot; omega]
  have hlt : bcnt bk q (bk q) < (bfilt bk n (bk q)).length := by
    have h1 := bcnt_mono (bk := bk) (show q + 1 ≤ n by omega) (bk q)
    core_grind [bcnt_succ]
  rw [List.getD_append _ _ _ _ (by simp_all)]
  rw [List.getD_eq_getElem _ _ (by simp_all), List.getElem_map]
  have := bfilt_getD (bk := bk) hq rfl
  simp_all

/-- The slot is below `n`. -/
theorem slot_lt {n A q : ℕ} (hq : q < n) (hA : ∀ q, q < n → bk q ≤ A) : slot bk n q < n := by
  have h1 := bcnt_mono (bk := bk) (show q + 1 ≤ n by omega) (bk q)
  rw [bcnt_succ, ite_eq_left rfl] at h1
  have h2 := bstart_mono (bk := bk) n (show bk q + 1 ≤ A + 1 by simp_all)
  rw [bstart_succ, bstart_all hA] at h2
  unfold slot; omega

/-- The slot lies in the range of its bucket. -/
theorem slot_range {n q : ℕ} (hq : q < n) :
    bstart bk n (bk q) ≤ slot bk n q ∧ slot bk n q < bstart bk n (bk q + 1) := by
  have h1 := bcnt_mono (bk := bk) (show q + 1 ≤ n by omega) (bk q)
  simp_all [bcnt_succ, bstart_succ, slot] 

/-- Slots are injective. -/
theorem slot_inj {n q q' : ℕ} (hq : q < n) (hq' : q' < n) (h : slot bk n q = slot bk n q') :
    q = q' := by
  have hb : bk q = bk q' := by
    rcases Nat.lt_trichotomy (bk q) (bk q') with hl | he | hl
    · have := slot_range (bk := bk) hq; have := slot_range (bk := bk) hq'
      have := bstart_mono (bk := bk) n (show bk q + 1 ≤ bk q' by omega); omega
    · exact he
    · have := slot_range (bk := bk) hq; have := slot_range (bk := bk) hq'
      have := bstart_mono (bk := bk) n (show bk q' + 1 ≤ bk q by omega); omega
  have hc : bcnt bk q (bk q) = bcnt bk q' (bk q) := by simp_all [slot] 
  rcases Nat.lt_trichotomy q q' with hl | he | hl
  · have := bcnt_mono (bk := bk) (show q + 1 ≤ q' by omega) (bk q)
    simp_all [bcnt_succ] <;> omega_nf
  · exact he
  · have := bcnt_mono (bk := bk) (show q' + 1 ≤ q by omega) (bk q)
    simp_all [bcnt_succ] <;> omega_nf

/-- Every position below `n` is a slot. -/
theorem exists_slot {n A p : ℕ} (hA : ∀ q, q < n → bk q ≤ A) (hp : p < n) :
    ∃ q, q < n ∧ slot bk n q = p := by
  let f : Fin n → Fin n := fun q => ⟨slot bk n q, slot_lt q.2 hA⟩
  have hf : Function.Injective f := fun a b h => Fin.ext (slot_inj a.2 b.2 (congrArg Fin.val h))
  obtain ⟨q, hq⟩ := (Finite.injective_iff_surjective.1 hf) ⟨p, hp⟩
  ram_grind

/-- **A memory segment with `base + q` at every slot is the bucket list.** -/
theorem seg_eq_bktList {m : ℕ → ℕ} {R n A base : ℕ} (hA : ∀ q, q < n → bk q ≤ A)
    (h : ∀ q, q < n → m (R + slot bk n q) = base + q) : seg m R n = bktList bk n A base := by
  apply List.ext_getElem (by rw [seg_length, bktList_length hA])
  intro p hp _
  rw [seg_length] at hp
  obtain ⟨q, hq, rfl⟩ := exists_slot hA hp
  have e1 : (seg m R n)[slot bk n q]'(by omega) = m (R + slot bk n q) := by
    simp [seg]
  have e2 := bktList_getD_slot (bk := bk) (base := base) hq (hA q hq)
  simp_all

end

end DrvR

end Chazelle.Core
