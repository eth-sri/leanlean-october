module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Sum
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.ByContra

@[expose] public section

open Classical Finset Sum

namespace Scarf

variable {T I α : Type*} [Fintype T] [Fintype I] [LinearOrder α] {r : I → T → α}

def Dm (r : I → T → α) (s : Finset (T ⊕ I)) : Prop :=
  ∀ y, ∃ i, inr i ∉ s ∧ ∀ x, inl x ∈ s → r i y ≤ r i x

lemma L (hr : ∀ i, Function.Injective (r i)) {s} (hs : Dm r s) (hn : Fintype.card I ≤ #s) {i k x}
    (hi : inr i ∉ s) (hk : inr k ∉ s) (hx : inl x ∈ s)
    (hxi : ∀ z, inl z ∈ s → r i x ≤ r i z) (hxk : ∀ z, inl z ∈ s → r k x ≤ r k z) : i = k := by
  choose f hf1 hf2 using hs
  have hinj : Set.InjOn f s.toLeft := fun z hz z' hz' h =>
    hr (f z) (le_antisymm (hf2 z z' (mem_toLeft.1 hz')) (by simp_all))
  have := card_toLeft_add_card_toRight (u := s)
  have he : s.toLeft.image f = s.toRightᶜ := eq_of_subset_of_card_le
    (fun j hj => by aesop)
    (by rw [card_image_of_injOn hinj, card_compl]; omega)
  have hmin (j) (hj : inr j ∉ s) (hxj : ∀ z, inl z ∈ s → r j x ≤ r j z) : f x = j := by
    obtain ⟨z, hz, rfl⟩ := mem_image.1 (he ▸ (by simp_all) : j ∈ s.toLeft.image f)
    rw [hr (f z) (le_antisymm (hxj z (mem_toLeft.1 hz)) (hf2 z x hx))]
  grind

lemma label {V : Type*} [DecidableEq V] (ℓ : V → I) (R : Finset V) (hR : #R = Fintype.card I)
    (hne : R.image ℓ ≠ univ) (i₀ : I) :
    Even #(R.filter fun a => (R.erase a).image ℓ = univ.erase i₀) := by
  by_cases h : ∃ a ∈ R, (R.erase a).image ℓ = univ.erase i₀
  swap
  · simp_all
  obtain ⟨a, ha, hae⟩ := h
  have hi₀ : i₀ ∉ R.image ℓ := fun h => hne (eq_univ_of_forall fun i => by
    by_cases hi : i = i₀
    · grind
    · exact image_subset_image (erase_subset _ _) (hae ▸ mem_erase.2 ⟨hi, mem_univ i⟩))
  have char (a') (ha' : a' ∈ R) : (R.erase a').image ℓ = univ.erase i₀ ↔ Set.InjOn ℓ (R.erase a') := by
    rw [← card_image_iff]
    have : (R.erase a').image ℓ ⊆ univ.erase i₀ := by grind
    refine ⟨fun h => ?_, fun h => eq_of_subset_of_card_le this ?_⟩ <;>
      simp_all [card_erase_of_mem]
  obtain ⟨b, hb, hba⟩ := mem_image.1 (hae ▸ mem_erase.2 ⟨fun h => hi₀ (h ▸ mem_image_of_mem ℓ ha), mem_univ _⟩ :
    ℓ a ∈ (R.erase a).image ℓ)
  rw [mem_erase] at hb
  convert (even_two : Even 2)
  rw [card_eq_two]
  refine ⟨a, b, hb.1.symm, ext fun a' => ?_⟩
  simp
  constructor
  · rintro ⟨ha', h⟩
    by_contra hne
    exact hb.1 (((char a' ha').1 h) (by grind)
      (by grind) hba)
  grind

lemma door (hr : ∀ i, Function.Injective (r i)) {e : Finset (T ⊕ I)} (hD : Dm r e)
    (hc : #e + 1 = Fintype.card I) (hne : e.toLeft.Nonempty) :
    #(univ.filter fun v => v ∉ e ∧ Dm r (insert v e)) = 2 := by
  have : ∀ k, ∃ x, inl x ∈ e ∧ ∀ z, inl z ∈ e → r k x ≤ r k z := fun k => by
    simpa using exists_min_image e.toLeft (r k) hne
  choose m hm1 hm2 using this
  have := card_toLeft_add_card_toRight (u := e)
  obtain ⟨a, ha, b, hb, hab, hm⟩ := exists_ne_map_eq_of_card_lt_of_maps_to (s := e.toRightᶜ)
    (t := e.toLeft) (f := m) (by rw [card_compl]; omega) fun k _ => by simp_all
  simp only [mem_compl, mem_toRight] at ha hb
  let Q j y := ∀ k, inr k ∉ e → k ≠ j → r k (m k) < r k y
  let Piv j v := (v = inr j ∧ ∀ y, ¬Q j y) ∨ ∃ x, v = inl x ∧ Q j x ∧ ∀ y, Q j y → r j y ≤ r j x
  have hQ (j z) (h : Q j z) : r j z ≤ r j (m j) := by
    obtain ⟨i, hi, hz⟩ := hD z
    grind
  have hins (k x y) (h1 : r k y ≤ r k x) (h2 : ∀ z, inl z ∈ e → r k y ≤ r k z) (z)
      (hz : inl z ∈ insert (inl x) e) : r k y ≤ r k z := by
    grind
  have ex (j) : ∃ v, Piv j v := by
    by_cases h : ∃ y, Q j y
    · obtain ⟨x, hx, hmax⟩ := exists_max_image (univ.filter (Q j)) (r j)
        (by obtain ⟨y, hy⟩ := h; exact ⟨y, by grind⟩)
      exact ⟨_, .inr ⟨x, rfl, (mem_filter.1 hx).2, fun y hy => hmax y (mem_filter.2 ⟨mem_univ _, hy⟩)⟩⟩
    aesop
  have uniq (j v w) (hv : Piv j v) (hw : Piv j w) : v = w := by
    rcases hv with ⟨rfl, h⟩ | ⟨x, rfl, hx, hxm⟩ <;> rcases hw with ⟨rfl, h'⟩ | ⟨x', rfl, hx', hxm'⟩
    · rfl
    · simp_all
    · simp_all
    grind
  have good (j v) (hj : j = a ∨ j = b) (hv : Piv j v) : v ∉ e ∧ Dm r (insert v e) := by
    have hjC : inr j ∉ e := by grind
    rcases hv with ⟨rfl, h⟩ | ⟨x, rfl, hx, hxm⟩
    · refine ⟨hjC, fun y => ?_⟩
      have := h y
      grind
    have hxj := hQ j x hx
    refine ⟨fun hxe => ?_, fun z => ?_⟩
    · grind
    by_cases hz : Q j z
    · exact ⟨j, by grind, hins _ _ _ (hxm z hz) fun x' h => (hxm z hz).trans (hxj.trans (by grind))⟩
    simp only [Q, not_forall, not_lt] at hz
    obtain ⟨k, hk, hkj, hle⟩ := hz
    exact ⟨k, by grind, hins _ _ _ (hle.trans (hx k hk hkj).le) fun x' h => hle.trans (by grind)⟩
  have back (v) (hv : v ∉ e) (hDv : Dm r (insert v e)) : Piv a v ∨ Piv b v := by
    have hc' : Fintype.card I ≤ #(insert v e) := by grind
    rcases v with y | j
    · obtain ⟨j, hj, hy⟩ := hDv y
      have hj' : inr j ∉ e := by grind
      have hQy : Q j y := fun k hk hkj => not_le.1 fun hle => hkj (L hr hDv hc' (by grind) hj
        (by simp) (hins _ _ _ le_rfl fun z h => hle.trans (hm2 k z h)) hy)
      have hP : Piv j (inl y) := .inr ⟨y, rfl, hQy, fun z hz => by
        obtain ⟨i, hi, hzi⟩ := hDv z
        grind⟩
      by_cases hja : j = a
      · grind
      by_cases j = b
      · grind
      exact (hab (L hr hDv hc' (by grind) (by grind) (by grind)
        (hins _ _ _ (hQy a ha (Ne.symm hja)).le (hm2 a))
        (by grind))).elim
    · have hP : Piv j (inr j) := .inl ⟨rfl, fun y hy => by
        obtain ⟨i, hi, hyi⟩ := hDv y
        grind⟩
      by_cases j = a
      · simp_all
      by_cases j = b
      · simp_all
      exact (hab (L hr hDv hc' (by grind) (by grind)
        (mem_insert_of_mem (hm1 a)) (fun z hz => hm2 a z (by grind))
        (by grind))).elim
  obtain ⟨va, hva⟩ := ex a
  obtain ⟨vb, hvb⟩ := ex b
  rw [card_eq_two]
  refine ⟨va, vb, fun h => by grind, ext fun v => ?_⟩
  simp
  refine ⟨fun ⟨h1, h2⟩ => (back v h1 h2).imp (uniq a v va · hva) (uniq b v vb · hvb), ?_⟩
  rintro (rfl | rfl) <;> grind

theorem scarf [Nonempty T] (hr : ∀ i, Function.Injective (r i)) (c : T → I) (i₀ : I) :
    ∃ σ : Finset T, ∃ C : Finset I, (∀ y, ∃ i ∈ C, ∀ x ∈ σ, r i y ≤ r i x) ∧ ∀ i ∈ C, ∃ y ∈ σ, c y = i := by
  by_contra hcon
  let ℓ : T ⊕ I → I := Sum.elim c id
  have hI : 0 < Fintype.card I := Fintype.card_pos_iff.2 ⟨i₀⟩
  have hnot (R) (hR : Dm r R) : R.image ℓ ≠ univ := fun h => hcon ⟨R.toLeft, R.toRightᶜ,
    by aesop,
    fun i hi => by
      obtain ⟨w | j, hw, rfl⟩ := mem_image.1 (h ▸ mem_univ i)
      · aesop
      aesop⟩
  have hanti (v e) (h : Dm r (insert v e)) : Dm r e := fun y =>
    let ⟨i, hi, h⟩ := h y; (by grind)
  let D e := univ.filter fun v => v ∉ e ∧ Dm r (insert v e)
  have hS := card_nbij' (s := (univ.filter fun e : Finset (T ⊕ I) => #e + 1 = Fintype.card I ∧
      e.image ℓ = univ.erase i₀).sigma D)
    (t := (univ.filter fun R => Dm r R ∧ #R = Fintype.card I).sigma fun R =>
      R.filter fun v => (R.erase v).image ℓ = univ.erase i₀)
    (fun p => ⟨insert p.2 p.1, p.2⟩) (fun p => ⟨p.1.erase p.2, p.2⟩)
    (by rintro ⟨e, v⟩ h; grind)
    (by rintro ⟨R, v⟩ h; simp_all [D]; omega)
    (by rintro ⟨e, v⟩ h; aesop)
    (by rintro ⟨R, v⟩ h; simp_all)
  rw [card_sigma, card_sigma] at hS
  obtain ⟨k, hk⟩ := even_sum (s := univ.filter fun R : Finset (T ⊕ I) => Dm r R ∧ #R = Fintype.card I) _ fun R hR => label ℓ R (by grind) (by grind) i₀
  let e₀ := (univ.erase i₀).image (inr (α := T))
  obtain ⟨x, -, hx⟩ := exists_max_image univ (r i₀) univ_nonempty
  have he₀ : e₀ ∈ univ.filter fun e : Finset (T ⊕ I) => #e + 1 = Fintype.card I ∧
      e.image ℓ = univ.erase i₀ := by
    simp [e₀, ℓ, card_image_of_injective _ inr_injective, image_image]; omega
  have hD₀ : #(D e₀) = 1 := card_eq_one.2 ⟨inl x, ext fun v => by
    rcases v with y | j <;> simp [D, Dm, e₀]
    · grind
    grind⟩
  rw [← add_sum_erase _ _ he₀] at hS
  obtain ⟨k', hk'⟩ : Even (∑ e ∈ (univ.filter fun e : Finset (T ⊕ I) => #e + 1 = Fintype.card I ∧
      e.image ℓ = univ.erase i₀).erase e₀, #(D e)) := even_sum _ fun e he => by
    obtain ⟨hne, he⟩ := mem_erase.1 he
    rw [mem_filter] at he
    by_cases hDe : Dm r e
    · by_cases hl : e.toLeft.Nonempty
      · rw [door hr hDe he.2.1 hl]; simp
      have hl' : ∀ y, inl y ∉ e := fun y h => hl ⟨y, mem_toLeft.2 h⟩
      grind
    · rw [show D e = ∅ from (by grind)]; simp
  omega

end Scarf
