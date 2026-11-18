module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic

@[expose] public section

open Set

namespace PolyaNeumann

theorem phase_le_count_of_jumps (lam : ℕ → ℝ) (h0 : lam 0 = 0) (M : ℝ → ℝ)
    (hinit : ∃ δ > 0, ∀ E, 0 < E → E < δ → (∀ j, lam j ≠ E) → M E ≤ 1)
    (hconst : ∀ E₁ E₂, 0 < E₁ → E₁ ≤ E₂ → (∀ j, lam j ∉ Icc E₁ E₂) → M E₂ ≤ M E₁)
    (hjump : ∀ j, 0 < lam j → ∀ m : ℕ, {i | lam i = lam j}.encard = m →
      ∃ δ > 0, ∀ E₁ E₂, 0 < E₁ → lam j - δ < E₁ → E₁ < lam j →
      lam j < E₂ → E₂ < lam j + δ → (∀ i, lam i ≠ E₁) → (∀ i, lam i ≠ E₂) → M E₂ ≤ M E₁ + m)
    (E : ℝ) (hE : 0 < E) (hnr : ∀ j, lam j ≠ E) (hfin : {j | lam j < E}.Finite) :
    M E ≤ {j | lam j < E}.ncard := by
  obtain ⟨δ0, hδ0, hinit⟩ := hinit
  induction h : (lam '' {j | 0 < lam j ∧ lam j < E}).ncard using Nat.strong_induction_on
    generalizing E with
  | _ n ih =>
  set P := lam '' {j | 0 < lam j ∧ lam j < E}
  have hPfin : P.Finite := (hfin.subset fun _ hj => hj.2).image lam
  have hone : (1 : ℝ) ≤ {j | lam j < E}.ncard := by
    exact_mod_cast (Set.ncard_pos hfin).2 ⟨0, by simp [h0, hE]⟩
  rcases P.eq_empty_or_nonempty with hPe | hPne
  · set E' := min (δ0 / 2) E
    have hE'pos : 0 < E' := lt_min (by positivity) hE
    have hE'le : E' ≤ E := min_le_right _ _
    have hno : ∀ j, lam j ∉ Icc E' E := fun j hj =>
      hPe.subset ⟨j, ⟨hE'pos.trans_le hj.1, lt_of_le_of_ne hj.2 (hnr j)⟩, rfl⟩
    linarith [hconst E' E hE'pos hE'le hno,
      hinit E' hE'pos ((min_le_left _ _).trans_lt (by linarith))
        fun j hj => hno j ⟨hj.symm.le, hj.symm ▸ hE'le⟩]
  · have hne : hPfin.toFinset.Nonempty := hPfin.toFinset_nonempty.mpr hPne
    set e := hPfin.toFinset.max' hne
    obtain ⟨j0, ⟨hj0pos, hj0E⟩, hj0e⟩ := hPfin.mem_toFinset.mp (hPfin.toFinset.max'_mem hne)
    have hj0e' : lam j0 = e := hj0e
    have hemax : ∀ x ∈ P, x ≤ e := fun x hx => hPfin.toFinset.le_max' x (hPfin.mem_toFinset.mpr hx)
    have hepos : 0 < e := hj0e' ▸ hj0pos
    have heE : e < E := hj0e' ▸ hj0E
    set A := insert (0 : ℝ) (hPfin.toFinset.erase e)
    set a := A.max' (Finset.insert_nonempty _ _)
    have ha0 : 0 ≤ a := A.le_max' 0 (Finset.mem_insert_self _ _)
    have haP : ∀ x ∈ P, x ≠ e → x ≤ a := fun x hx hxe =>
      A.le_max' x (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hxe, hPfin.mem_toFinset.mpr hx⟩))
    have hae : a < e := (Finset.max'_lt_iff A _).mpr fun x hx => by
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hepos
      · exact lt_of_le_of_ne (hemax x (hPfin.mem_toFinset.mp (Finset.mem_of_mem_erase hx)))
          (Finset.ne_of_mem_erase hx)
    have hmfin : {i | lam i = e}.Finite := hfin.subset fun i hi => (hi : lam i = e).trans_lt heE
    obtain ⟨δ, hδ, hjump⟩ := hjump j0 hj0pos _ (by rw [hj0e']; exact hmfin.cast_ncard_eq.symm)
    rw [hj0e'] at hjump
    set ε := min (min (e - a) (E - e)) δ / 2 with hε_def
    have hε : 0 < ε := half_pos (lt_min (lt_min (sub_pos.mpr hae) (sub_pos.mpr heE)) hδ)
    have hεa : 2 * ε ≤ e - a := by
      rw [hε_def]; linarith [(min_le_left (min (e - a) (E - e)) δ).trans (min_le_left _ _)]
    have hεE : 2 * ε ≤ E - e := by
      rw [hε_def]; linarith [(min_le_left (min (e - a) (E - e)) δ).trans (min_le_right _ _)]
    have hεδ : 2 * ε ≤ δ := by rw [hε_def]; linarith [min_le_right (min (e - a) (E - e)) δ]
    set E₁ := e - ε with hE₁
    set E₂ := e + ε with hE₂
    have hnr₁ : ∀ i, lam i ≠ E₁ := fun i hi => by
      have hiP : lam i ∈ P := ⟨i, ⟨by linarith, by linarith⟩, rfl⟩
      linarith [haP _ hiP (by linarith)]
    have hno₂ : ∀ i, lam i ∉ Icc E₂ E := fun i hi => by
      have hiP : lam i ∈ P := ⟨i, ⟨by linarith [hi.1], lt_of_le_of_ne hi.2 (hnr i)⟩, rfl⟩
      linarith [hemax _ hiP, hi.1]
    have hjmp := hjump E₁ E₂ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
      hnr₁ (fun i hi => hno₂ i ⟨hi.symm.le, by linarith⟩)
    have hfin₁ : {j | lam j < E₁}.Finite :=
      hfin.subset fun j (hj : lam j < E₁) => show lam j < E by linarith
    have hlt : (lam '' {j | 0 < lam j ∧ lam j < E₁}).ncard < n := by
      rw [← h]
      refine Set.ncard_lt_ncard ⟨?_, fun hsub' => ?_⟩ hPfin
      · rintro _ ⟨j, ⟨hj1, hj2⟩, rfl⟩; exact ⟨j, ⟨hj1, by linarith⟩, rfl⟩
      · obtain ⟨j, ⟨-, hj2⟩, hje⟩ := hsub' ⟨j0, ⟨hj0pos, hj0E⟩, hj0e'⟩; linarith
    have hih := ih _ hlt E₁ (by linarith) hnr₁ hfin₁ rfl
    have hsplit : {j | lam j < E} = {j | lam j < E₁} ∪ {i | lam i = e} := by
      ext j; simp only [mem_setOf_eq, mem_union]; constructor
      · intro hj
        by_cases hj0 : lam j ≤ 0
        · left; linarith
        · by_cases hje : lam j = e
          · exact Or.inr hje
          · exact Or.inl (lt_of_le_of_lt (haP _ ⟨j, ⟨lt_of_not_ge hj0, hj⟩, rfl⟩ hje) (by linarith))
      · rintro (hj | hj) <;> linarith
    have hdisj : Disjoint {j | lam j < E₁} {i | lam i = e} :=
      Set.disjoint_left.mpr fun j (hj1 : lam j < E₁) (hj2 : lam j = e) => by linarith
    have hcount : ({j | lam j < E}.ncard : ℝ) =
        {j | lam j < E₁}.ncard + {i | lam i = e}.ncard := by
      rw [hsplit, Set.ncard_union_eq hdisj hfin₁ hmfin]; push_cast; ring
    linarith [hconst E₂ E (by linarith) (by linarith) hno₂]

end PolyaNeumann
