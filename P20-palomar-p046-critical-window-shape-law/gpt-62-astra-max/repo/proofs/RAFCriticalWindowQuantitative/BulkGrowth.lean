module
public import proofs.RAFCriticalWindowQuantitative.RecordContraction

/-! Simultaneous middle-length growth by paired open cuts and a first-moment deficit bound. -/

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical Function HordijkSteelThreshold ProbabilityTheory MeasureTheory unitInterval Finset

/-- The event that no row of the indicated finite array is entirely open. -/
abbrev Failed {J D : Type*} (f : J × D → Coord) : Set SplitField :=
  (fun ω j d => ω (f (j,d))) ⁻¹' Set.univ.pi (fun _ : J => {v : D → Prop | ∀ d, v d}ᶜ)

@[simp] lemma mem_failed {J D : Type*} {f : J × D → Coord} {ω} : ω ∈ Failed f ↔ ∀ j, ¬∀ d, ω (f (j,d)) := by simp [Failed,Set.mem_pi]

lemma blocks_failed {J D : Type*} [Fintype J] [Fintype D] (a : I) (f : J × D → Coord) (hf : Injective f) (hD : Fintype.card D ≤ 2) :
    infiniteSplitPi a (Failed f) ≤ (missRate a 2)^Fintype.card J := by
  rw [Failed,infiniteSplitPi,(iid_rows a f hf).finite_event]
  simp [RAFEmergenceApprox.Generic.iid,RAFEmergenceApprox.Generic.law,Measure.pi_pi]
  exact pow_le_pow_left' (miss_mono a hD) _

namespace ChannelMap
variable (f : ChannelMap)
abbrev Gen (N k : ℕ) (ω : SplitField) := FiniteReversibleGenerated N (10*k) (f.field ω)

private lemma half_open {ω i} {w : List Bool} (h : 2*i ≤ w.length) : f.field ω w i = ω (w,i) := by
  simp [field,currySplitField,f.half w i h]

/-- A single open cut suffices when both of the shorter words are available. -/
private lemma cut {N k ω} {w : List Bool} {s : ℕ} (hs : s ≤ w.length) (hN : w.length ≤ N)
    (l : f.Gen N k ω (w.take s)) (r : f.Gen N k ω (w.drop s)) (ho : f.field ω w s) : f.Gen N k ω w := by
  have eq := List.take_append_drop s w
  exact eq ▸ InfiniteReversibleGenerated.ligate l r ⟨by simp_all,by simpa⟩

abbrev V (n : ℕ) := List.Vector Bool n
abbrev key (w : List Bool) (j : V (w.length/2) × Fin 2) : Coord :=
  (j.1.val ++ w,w.length/2+j.2.val)
abbrev blocked (w : List Bool) := Failed (key w)

private lemma power_count {n k : ℕ} (hn : 10*k < n) (hk : 0 < k) : k*(n+1) ≤ 2^(n/2) := by
  let d := n/2-k-2
  have hd : n/2 = k+(d+2) := by dsimp [d]; omega
  rw [hd,pow_add,pow_add]
  exact Nat.mul_le_mul Nat.lt_two_pow_self.le (by have : d < 2^d := Nat.lt_two_pow_self; dsimp [d] at *; omega)

noncomputable abbrev err (a : I) (k : ℕ) := (missRate a 2)^k

private lemma block_mass {k : ℕ} (a : I) (hk : 0 < k) {n : ℕ} (hl : 10*k < n) (w : V n) :
    infiniteSplitPi a (blocked w.val) ≤ (err a k)^(n+1) := by
  have inj : Injective (key w.val) := by
    rintro ⟨u,i⟩ ⟨v,j⟩ he; simp [key,Prod.ext_iff] at he; exact Prod.ext (Subtype.ext he.1) (Fin.ext he.2)
  apply (blocks_failed a (key w.val) inj (by simp)).trans
  simp only [card_vector,Fintype.card_bool,err,←pow_mul,w.property]
  exact pow_le_pow_of_le_one bot_le tsub_le_self (power_count hl hk)

/-- A bad middle length anywhere in the infinite field. -/
def defects (k : ℕ) := ⋃ n, ⋃ (_ : 10*k<n), ⋃ w : V n, blocked w.val

lemma defects_mass {k : ℕ} (a : I) (hk : 0 < k) (ht : 2*err a k ≤ 2⁻¹) :
    infiniteSplitPi a (defects k) ≤ 2*err a k := by
  apply (measure_iUnion_le _).trans
  calc
    _ ≤ ∑' n : ℕ, (2⁻¹:ENNReal)^n*err a k := ENNReal.tsum_le_tsum fun n => ?_
    _ = _ := by rw [ENNReal.tsum_mul_right,ENNReal.tsum_geometric_two]
  by_cases hn : 10*k<n
  · simp only [hn,Set.iUnion_true]
    apply (finite_cover _ _ (fun ω => Set.mem_iUnion.mp) (block_mass a hk hn)).trans
    simp
    rw [pow_succ,←mul_assoc,←mul_pow]; gcongr
  · simp [hn]

/-- Grow w by cleaving zw, built from shorter words at the neighboring cut.
Both marks lie on the left half, even in the commuting-factor quotient. -/
private lemma middle {N k : ℕ} (hk : 0 < k) {ω : SplitField} (good : ω ∉ defects k)
    (w : List Bool) (hw : 0 < w.length) (hn : w.length ≤ 2*N/3) : f.Gen N k ω w := by
  induction e : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
    by_cases hl : w.length ≤ 10*k
    · exact .food (List.ne_nil_of_length_pos hw) (le_min hl (by omega))
    simp only [defects,Set.mem_iUnion,not_exists] at good
    obtain ⟨z,hz⟩ : ∃ z, ∀ i, ω (key w (z,i)) := by simpa [blocked] using good _ (by omega) ⟨w,e⟩
    have short {u : List Bool} (hp : 0 < u.length) (hs : u.length < n) : f.Gen N k ω u :=
      ih _ hs u hp (by omega) rfl
    let v := z.val ++ w
    have len : v.length = n/2+n := by grind [List.Vector.length_val]
    have mark (i : Fin 2) : f.field ω v (z.val.length+i) ∧ v.length ≤ N :=
      ⟨by rw [f.half_open (by have := z.property; omega)]; simpa [z.property] using hz i,by omega⟩
    apply InfiniteReversibleGenerated.right (u := z.val) (by grind [List.Vector.length_val]) (by grind) _ (by simpa [v] using mark 0)
    apply f.cut (s := z.val.length+1) (by have := z.property; omega) (mark 1).2 _ _ (mark 1).1
    all_goals apply short <;> simp [len,z.property] <;> omega

/-- Off the same exceptional event, any generated seed gives unbounded growth. -/
lemma unbounded_of_seed {k K ω} (hk : 0 < k) (good : ω ∉ defects k) (hs : ω ∈ f.seed (10*k) K) :
    ReversibleUnbounded 2 (f.field ω) := by
  intro n
  let w := List.replicate (n+1) false
  refine ⟨w,by simp [w],(f.middle (N := 3*(n+1)) hk good w (by simp [w]) (by grind)).bind ?_ (fun _ _ h => h.1)⟩
  intro u ne hl
  rw [←sourceWordMolecule_word u ne (le_min_iff.mp hl).1]
  exact finiteReversibleGenerated_to_infinite (hs _)

/-- For a target outside the middle lengths, test k distinct balanced cuts. -/
lemma missing_word {N k : ℕ} (a : I) (hk : 0 < k) (ht : 2*err a k ≤ 2⁻¹)
    (w : List Bool) (hw : 0 < w.length) (hn : w.length ≤ N) :
    infiniteSplitPi a {ω | ¬f.Gen N k ω w} ≤ 3*err a k := by
  by_cases hl : w.length ≤ 10*k
  · simp [show ∀ ω, f.Gen N k ω w from fun _ => .food (List.ne_nil_of_length_pos hw) (le_min hl hn)]
  let s (i : Fin k) := w.length/2-k+i.val
  let j (z : Fin k × Unit) : Coord := (w,s z.1)
  have inj : Injective j := by rintro ⟨i,⟨⟩⟩ ⟨l,⟨⟩⟩ h; simpa [j,s,Prod.ext_iff,Fin.ext_iff] using h
  apply (measure_alternatives _ ?_).trans ((add_le_add (defects_mass a hk ht) (blocks_failed a j inj (by simp))).trans ?_)
  · intro ω hm good; rw [mem_failed]; intro i ho
    apply hm; apply f.cut (s := s i) (by dsimp [s]; omega) hn
    · apply f.middle hk good <;> simp [s] <;> omega
    · apply f.middle hk good <;> simp [s] <;> omega
    · rw [f.half_open (by dsimp [s]; omega)]; exact ho ()
  · simp [err]; ring_nf; rfl

end ChannelMap

/-- Markov's inequality applied to the number of missing molecules. -/
lemma deficit_bound {X Ω : Type*} [Fintype X] [DecidableEq X] [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) (P : Ω → Finset X) {m : ℕ} {t : ENNReal} (h : ∀ x, μ {ω | x ∉ P ω} ≤ t) :
    μ {ω | Fintype.card X < m*(P ω)ᶜ.card} ≤ m*t := by
  let U := Fintype.card X
  let B (x : X) := {ω | x ∉ P ω}
  rcases isEmpty_or_nonempty X with hX|hX
  · simp [Finset.Nonempty]
  apply (ENNReal.mul_le_mul_iff_right (a := (U:ENNReal)) (by positivity) (by finiteness)).mp
  calc
    _ ≤ (U:ENNReal) * μ {ω | (U:ENNReal) ≤ (m:ENNReal)*∑ x, (B x).indicator (fun _ => (1:ENNReal)) ω} := by
      gcongr with ω; intro hω
      simp only [B,Set.mem_ofPred_eq,Set.indicator_apply,sum_boole,filter_notMem_eq_sdiff]
      exact_mod_cast (le_of_lt hω : U ≤ m*(P ω)ᶜ.card)
    _ ≤ _ := mul_meas_ge_le_lintegral (measurable_of_finite _) _
    _ = (m:ENNReal)*∑ x, μ (B x) := by
      rw [lintegral_const_mul _ (measurable_of_finite _),lintegral_finsetSum _ fun _ _ => measurable_of_finite _]; simp [(Set.toFinite _).measurableSet]
    _ ≤ m * ∑ _ : X, t := by gcongr with x; exact h x
    _ = _ := by simp [U]; ring

end RAFCriticalWindowQuantitative
