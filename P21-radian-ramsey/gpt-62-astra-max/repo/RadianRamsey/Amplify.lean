module
public import RadianRamsey.SimilarityTrade

@[expose] public noncomputable section
namespace RadianRamsey
open Multiset OAI.EuclideanRamsey

/-! Translation of all rows of a trade does not affect their energies. Averaging
along a long progression lets us discard any pair of rows with equal slope:
all but the two ends cancel. On slopes alone we can then *multiply* trades,
since complex multiplication commutes. Powers amplify any strict energy gap. -/
variable {s : ℕ} {z : Fin s → ℂ}

private def comp (p q : Sim) : Sim := (p.1*q.1,p.2+p.1*q.2)
private def act (p : Sim) := mapAddMonoidHom (comp p)
private def chain (P A : Rows) := P.bind (act · A)

private lemma act_trade (p : Sim) {A B} (h : Trade z A B) : Trade z (act p A) (act p B) := fun i => by
  simpa [act,comp,value,Function.comp_def,mul_add,mul_assoc,add_assoc] using congrArg (map (value · p)) (h i)
private lemma chain_trade (P : Rows) {A B} (h : Trade z A B) : Trade z (chain P A) (chain P B) := fun i => by
  simp [chain,map_bind,fun p => act_trade p h i]
private lemma chain_energy (P A : Rows) : energy (chain P A) = energy P * energy A := by
  simp [energy,chain,act,map_bind,comp,←sum_map_mul_left,←sum_map_mul_right,Function.comp_def]; exact sum_map_sum_map ..

private abbrev shift (h : ℂ) := act (1,h)
private def double (h : ℂ) := AddMonoidHom.id Rows + shift h

@[simp] private lemma E_shift h (A : Rows) : energy (shift h A) = energy A := by simp [energy,shift,act,comp]
private lemma shift_add (h k : ℂ) (A : Rows) : shift h (shift k A) = shift (h+k) A := by simp [shift,act]; congr 1; ext <;> simp [comp,add_assoc]

/-- Allow `n` uncancelled pairs of translates in the histogram comparison. -/
private def Approx (z : Fin s → ℂ) : ℕ → Rows → Rows → Prop
  | 0 => Trade z
  | n+1 => fun A B => ∃ h C, Approx z n (A+C) (B+shift h C)

private lemma peel {L R : Rows} (hs : L.Rel (fun p q => p.1=q.1) R) {A B}
    (H : Trade z (A+L) (B+R)) : Approx z L.card A B := by
  induction hs generalizing A B with
  | zero => simpa [Approx] using H
  | @cons p q L R hp _ ih =>
    rw [card_cons]; refine ⟨q.2-p.2,{p},ih ?_⟩
    simpa [shift,act,comp,hp,←singleton_add,add_assoc] using H

private lemma double_trade (n) {h A B C} (H : Approx z n (A+C) (B+shift h C)) :
    Approx z n (double h A+C) (double h B+shift (h+h) C) := by
  induction n generalizing A B with
  | zero =>
    intro i
    have hh := act_trade (1,h) H i
    have hi := H i
    rw [←shift] at hh
    simp [double,shift_add] at hh hi ⊢
    grind
  | succ n ih =>
    obtain ⟨k,D,H⟩ := H
    have hh := ih (A:=A+D) (B:=B+shift k D) (by simpa [add_right_comm] using H)
    exact ⟨k,double h D,by simpa [double,shift_add,add_comm,add_assoc,add_left_comm] using hh⟩

private lemma wash {r t : ℝ} (bound : ∀ A B, Trade z A B → r*energy A ≤ t*energy B)
    {n A B} (H : Approx z n A B) : r*energy A ≤ t*energy B := by
  induction n generalizing A B with
  | zero => exact bound _ _ H
  | succ n ih =>
    obtain ⟨h,C,H⟩ := H
    have est (m : ℕ) (h A B) (H : Approx z n (A+C) (B+shift h C)) :
        r*energy A-t*energy B ≤ (1/2)^m*((t-r)*energy C) := by
      induction m generalizing h A B with
      | zero => have hi := ih H; simp at hi ⊢; linarith
      | succ m step =>
        have hh := step _ _ _ (double_trade n H)
        rw [pow_succ]; simp [double] at hh ⊢; linarith
    have lim := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1/2:ℝ)) (by norm_num)
    simpa using ge_of_tendsto' (lim.mul_const _) (fun m => est m h A B H)

theorem amplify {P Q} (h : Trade z P Q) (hlt : energy Q < energy P) (r : ℝ) (hr : 0 < r) :
    ∃ A B, Trade z A B ∧ energy B < r * energy A := by
  by_contra! bad
  have hpos : 0 < energy P := lt_of_le_of_lt (sum_nonneg (forall_mem_map_iff.mpr fun _ _ => Complex.normSq_nonneg _)) hlt
  let ρ := energy Q / energy P
  have pow_bound (n : ℕ) (A B) (ht : Trade z A B) : r*energy A ≤ ρ^n * energy B := by
    induction n generalizing A B with
    | zero => simp_all
    | succ n ih =>
      have hs : (chain B P).Rel (fun p q => p.1=q.1) (chain P B) := by
        apply rel_map.mp ∘ rel_eq.mpr
        simp [chain,act,map_bind,comp,map_map,Function.comp_def]
        rw [Multiset.bind_map_comm]; simp [mul_comm]
      have H := wash ih (peel (A:=chain P A) (B:=chain B Q) hs (by
        intro i; simp [chain_trade P ht i,chain_trade B h i,add_comm]))
      simp [chain_energy] at H
      dsimp [ρ]; rw [pow_succ]; field_simp; linarith
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one hr ((div_lt_one hpos).mpr hlt)
  linarith [pow_bound n P P (fun _ => rfl),mul_lt_mul_of_pos_right hn hpos]

end RadianRamsey
