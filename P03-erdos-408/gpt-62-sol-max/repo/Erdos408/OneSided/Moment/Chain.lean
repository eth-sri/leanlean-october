module

import OAI.RpowArithmetic
public import Erdos408.OneSided.Moment.PathExpansion
public import Erdos408.OneSided.Bands
public import Erdos408.OneSided.Memory.Ghost
public import Erdos408.OneSided.Memory.Partition

/-!
# The memory chain

The operators of PD §4 at a real root (`blueprint/one_sided_type_ii.md` §12), as choice
operators on chain states.

* A chain state has a position `z`, active lists `act` and a memory `S` of size at most the
  cap `B`. The memory is a multiplicity function on particles `(p, ℓ)`, with `p` a band prime
  and `ℓ ≤ p`.
* The ghost `chainGhost j` is the ghost operation of `Memory/Ghost.lean` at the current
  position, with `del = -η'_j/ρ`, `surv = q_j/ρ²` and `cre(p, ℓ) = -η'_j V(p)/ρ`.
* The edge `chainEdge` makes these choices:
  - a source symmetrization;
  - the groups whose unshared source prime is stored as `(p, [z]_p)`;
  - a target `z'`;
  - for each group, a new label, either a promoted pending particle (weight `S(x)/V`) or a
    fresh prime (weight `ν(p)`, a birth);
  - a target symmetrization.

  The coefficient carries `ρ^{hits}` at both ends and the line-free kernel `κ` of the row
  operation, together with the ban, distinctness of the target lists, the pad dyad,
  `D ∣ det`, and goodness at both ends.

PD's global birth distinctness is not a local restriction, so it is imposed on the expanded
history. A history is a ghost choice at each of the `N + 1` visits and an edge choice at
each of the `N` edges; `chainProduct_eq_sum_history` expands `𝒢₀ ℰ 𝒢₁ ⋯ ℰ 𝒢_N` into
histories. Its births sit at fixed addresses (`BirthAddr`): the initial slots, the fresh
labels of each edge, and the batch indices of each ghost.

The memory identity S3, `lineAverage_rootMoment_eq_chain` in `Moment/Chain/Identity.lean`, is
`𝔼_ℓ rootMoment = (∏_p b'_p) ∑ [𝐛_init] w(history) [𝐛_fin]`, over histories with distinct
births and with the cap `B` the number of band primes.
-/

@[expose] public section

noncomputable section

namespace Erdos408.OneSided

open Filter Finset Real

variable {K : ℕ}

section Chain

variable (q A₀ x : ℝ) (d : Data K) (Y d₀ u v r : ℝ) (B : ℕ)

/-- The particles `(p, ℓ)`: a band prime `p` and a line `ℓ ≤ p`. -/
def particles : Finset (ℕ × ℕ) :=
  (bandPrimes x d).biUnion fun p => (range (p + 1)).image fun ℓ => (p, ℓ)

/-- The particle type. -/
abbrev Particle := ↥(particles x d)

/-- The harmonic mass of the band containing `p` (for disjoint bands, `V_i` when `p ∈ 𝒫_i`). -/
def primeMass (p : ℕ) : ℝ :=
  ∑ i, if p ∈ band x (d.a i) then harmonicMass (band x (d.a i)) else 0

/-- The baseline `b'_p = 1 - (p + 1)⁻¹ ∑_{j ≤ N} η'_j`. -/
def baseline (N p : ℕ) : ℝ := 1 - ((p : ℝ) + 1)⁻¹ * ∑ j ∈ range (N + 1), dampDefect q N j

/-- The birth weight `ν(p) = 1 / (V(p) (p + 1) b'_p)`. -/
def primeWeight (N p : ℕ) : ℝ := 1 / (primeMass x d p * ((p : ℝ) + 1) * baseline q N p)

/-- The pending weight `ρ = q^{1/8}`: `0 < ρ < 1` and `ρ² > √q`. -/
def pendingWeight : ℝ := q ^ (1 / 8 : ℝ)

/-- The memory cap: with distinct births no more particles than band primes are pending. -/
def memCap : ℕ := (bandPrimes x d).card

/-- The chain states: a position, active lists, and a memory of size at most `B`. -/
abbrev ChainState :=
  ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) × ↥(lists x d (padCount x)) ×
    MemState (Particle x d) B

/-- The measure of a chain state: `∏_{i,h} ν(act_{i,h})` times the memory weight. -/
def chainMeasure (N : ℕ) (s : ChainState x d Y d₀ u v r B) : ℝ :=
  (∏ i, ∏ h, primeWeight q x d N (s.2.1.1 i h)) *
    memWeight (fun xp : Particle x d => primeWeight q x d N xp.1.1) s.2.2.1

/-- The number of pending particles hitting `z`, with multiplicity. -/
def pendingHits (z : ℤ × ℤ) (S : Particle x d → ℕ) : ℕ :=
  ∑ xp, if lineOf xp.1.1 z = xp.1.2 then S xp else 0

/-- The particle hits the position `z`: its line is `[z]_p`. -/
def HitsAt (z : ℤ × ℤ) (xp : Particle x d) : Prop := lineOf xp.1.1 z = xp.1.2

instance (z : ℤ × ℤ) : DecidablePred (HitsAt x d z) := fun _ => inferInstanceAs (Decidable (_ = _))

open scoped Classical in
/-- The ghost coefficient: `ghostCoef` at the current position with `del = -η'_j/ρ`,
`surv = q_j/ρ²`, `cre(p, ℓ) = -η'_j V(p)/ρ` and particle measure `ν(p)`; zero unless the choice
is admissible. -/
def chainGhostCoef (N j : ℕ) (s : ChainState x d Y d₀ u v r B)
    (c : (Particle x d → ℕ) × (Particle x d → ℕ)) : ℂ :=
  ghostCoef (HitsAt x d s.1.1) (fun xp : Particle x d => primeWeight q x d N xp.1.1)
      (-dampDefect q N j / pendingWeight q) ((1 - dampDefect q N j) / pendingWeight q ^ 2)
    (fun xp : Particle x d => -dampDefect q N j * primeMass x d xp.1.1 / pendingWeight q)
    B s.2.2 c

/-- The output of a ghost choice: delete `D` and create the batch. -/
def chainGhostOut (s : ChainState x d Y d₀ u v r B)
    (c : (Particle x d → ℕ) × (Particle x d → ℕ)) : ChainState x d Y d₀ u v r B :=
  (s.1, s.2.1, ghostOut (HitsAt x d s.1.1) B s.2.2 c)

/-- An edge choice: the source symmetrization, the stored groups, the target, a new label
`(prime, promoted?)` per group, and the target symmetrization. -/
abbrev EdgeChoice :=
  (Fin K → Equiv.Perm (Fin (padCount x + 1))) × Finset (Fin K) ×
    ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) × (Fin K → ℕ × Bool) ×
    (Fin K → Equiv.Perm (Fin (padCount x + 1)))

/-- The edge choices: the new label of group `i` is a prime of `𝒫_i`. -/
def edgeChoices : Finset (EdgeChoice x d Y d₀ u v r) :=
  univ ×ˢ univ ×ˢ univ ×ˢ (Fintype.piFinset fun i => band x (d.a i) ×ˢ univ) ×ˢ univ

section Edge

variable {x d Y d₀ u v r B}

/-- The source lists reordered by the source symmetrization. -/
def edgeSrc (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) :
    Lists K (padCount x) := fun i h => s.2.1.1 i (c.1 i h)

/-- The target lists: the copied pads and the new labels, reordered by `σ'`. -/
def edgeTgt (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) :
    Lists K (padCount x) := fun i h =>
  let h' := c.2.2.2.2 i h
  if h' = Fin.last _ then (c.2.2.2.1 i).1 else edgeSrc s c i h'

/-- The particle promoted in group `i`: the new label with its line at the target. -/
def edgePromoted (c : EdgeChoice x d Y d₀ u v r) (i : Fin K) : ℕ × ℕ :=
  ((c.2.2.2.1 i).1, lineOf (c.2.2.2.1 i).1 c.2.2.1.1)

/-- The particle stored from group `i`: the unshared source prime with its line at the
source. -/
def edgeStored (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) (i : Fin K) :
    ℕ × ℕ :=
  (edgeSrc s c i (Fin.last _), lineOf (edgeSrc s c i (Fin.last _)) s.1.1)

open scoped Classical in
/-- The memory after the edge: promoted particles removed, stored particles added. -/
def edgeMem (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) :
    Particle x d → ℕ := fun xp =>
  s.2.2.1 xp - (univ.filter fun i => (c.2.2.2.1 i).2 ∧ edgePromoted c i = xp.1).card +
    (c.2.1.filter fun i => edgeStored s c i = xp.1).card

/-- The pad product `D` of the edge. -/
def edgePad (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) : ℕ :=
  ∏ i, ∏ h : Fin (padCount x), edgeSrc s c i h.castSucc

/-- The determinant `det(z, z')`. -/
def edgeDet (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) : ℤ :=
  s.1.1.1 * c.2.2.1.1.2 - s.1.1.2 * c.2.2.1.1.1

end Edge

/-- An edge choice at `s` is admissible:
* the target lists are valid lists;
* the new labels avoid every source label (the cross-edge ban);
* the pad product lies in `[d₀, 2d₀)` and divides `det(z, z')`;
* both ends pass the good-state tests;
* every promoted particle is pending and hits the target, and every stored particle is a
  particle;
* the new memory respects the cap. -/
def EdgeValid (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) : Prop :=
  edgeTgt s c ∈ lists x d (padCount x) ∧
    (∀ i i' h, (c.2.2.2.1 i).1 ≠ s.2.1.1 i' h) ∧
    d₀ ≤ (edgePad s c : ℝ) ∧ (edgePad s c : ℝ) < 2 * d₀ ∧ (edgePad s c : ℤ) ∣ edgeDet s c ∧
    (GoodFirst Y d₀ (tau r (complement s.1.1) / tau r s.1.1) s.2.1.1 ∧
      GoodSecond x d d₀ (tau r (complement s.1.1) / tau r s.1.1) s.2.1.1) ∧
    (GoodFirst Y d₀ (tau r (complement c.2.2.1.1) / tau r c.2.2.1.1) (edgeTgt s c) ∧
      GoodSecond x d d₀ (tau r (complement c.2.2.1.1) / tau r c.2.2.1.1) (edgeTgt s c)) ∧
    (∀ i, (c.2.2.2.1 i).2 = true → ∃ xp : Particle x d, xp.1 = edgePromoted c i ∧
      1 ≤ s.2.2.1 xp) ∧
    (∀ i ∈ c.2.1, edgeStored s c i ∈ particles x d) ∧
    edgeMem s c ∈ memStates B

open scoped Classical in
/-- The edge coefficient:
`M!^{-2K} ρ^{hits(S, z)} ρ^{hits(S', z')} ∏_i w_i κ(t; b, a)`, where
* `w_i` is `S(x_i)/V(p_i)` for a promotion and `ν(p_i)` for a fresh prime;
* `κ(t; b, a) = (d₀/D) η(b/Y) η(a/Y) ψ(t/Y) {[t = b - a] - ∫_𝔐 e(θ(t - b + a))}` with
  `t = det/D`.

It is zero unless the choice is admissible. -/
def chainEdgeCoef (N : ℕ) (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) : ℂ :=
  if EdgeValid x d Y d₀ u v r B s c then
    let D := edgePad s c
    let b := ∏ i, edgeSrc s c i (Fin.last _)
    let a := ∏ i, (c.2.2.2.1 i).1
    let t := edgeDet s c / D
    (((((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 *
        pendingWeight q ^ pendingHits x d s.1.1 s.2.2.1 *
        pendingWeight q ^ pendingHits x d c.2.2.1.1 (edgeMem s c) *
        (∏ i, if (c.2.2.2.1 i).2 then
          (∑ xp : Particle x d, if xp.1 = edgePromoted c i then (s.2.2.1 xp : ℝ) else 0) /
            primeMass x d (c.2.2.2.1 i).1
        else primeWeight q x d N (c.2.2.2.1 i).1) *
        (d₀ / D) * dyadicBump (b / Y) * dyadicBump (a / Y) * plateau (t / Y) : ℝ) : ℂ) *
      ((if t = (b : ℤ) - a then 1 else 0) - arcIntegral A₀ x Y (t - b + a))
  else 0

open scoped Classical in
/-- The output of an edge choice. -/
def chainEdgeOut (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) :
    ChainState x d Y d₀ u v r B :=
  if h : EdgeValid x d Y d₀ u v r B s c then
    (c.2.2.1, ⟨edgeTgt s c, h.1⟩, ⟨edgeMem s c, h.2.2.2.2.2.2.2.2.2⟩)
  else s

/-- The edge operation `ℰ`. -/
def chainEdge (N : ℕ) :
    (ChainState x d Y d₀ u v r B → ℂ) → ChainState x d Y d₀ u v r B → ℂ :=
  choiceOp (edgeChoices x d Y d₀ u v r) (chainEdgeCoef q A₀ x d Y d₀ u v r B N)
    (chainEdgeOut x d Y d₀ u v r B)

open scoped Classical in
/-- The initial vector: at `e₁`, with empty memory. -/
def chainInit (s : ChainState x d Y d₀ u v r B) : ℂ :=
  if s.1.1 = (1, 0) ∧ memSize s.2.2.1 = 0 then 1 else 0

/-- A ghost choice `(D, n)`: the deleted and the created multiplicities. -/
abbrev GhostChoice := (Particle x d → ℕ) × (Particle x d → ℕ)

/-- A history of `𝒢₀ ℰ 𝒢₁ ⋯ ℰ 𝒢_N`: a ghost choice at each visit and an edge choice at each
edge. -/
abbrev History (N : ℕ) := (Fin (N + 1) → GhostChoice x d) × (Fin N → EdgeChoice x d Y d₀ u v r)

/-- The histories whose choices are drawn from the choice sets of the operators. -/
def histories (N : ℕ) : Finset (History x d Y d₀ u v r N) :=
  Fintype.piFinset (fun _ => multBox B ×ˢ multBox B) ×ˢ
    Fintype.piFinset fun _ => edgeChoices x d Y d₀ u v r

variable {x d Y d₀ u v r B} in
/-- The state at visit `j` of the history `h` from `s`, before its ghost. -/
def chainVisit {N : ℕ} (s : ChainState x d Y d₀ u v r B) (h : History x d Y d₀ u v r N) :
    Fin (N + 1) → ChainState x d Y d₀ u v r B :=
  Fin.induction s fun j t =>
    chainEdgeOut x d Y d₀ u v r B (chainGhostOut x d Y d₀ u v r B t (h.1 j.castSucc)) (h.2 j)

variable {x d Y d₀ u v r B} in
/-- The final state of the history `h` from `s`. -/
def chainEnd {N : ℕ} (s : ChainState x d Y d₀ u v r B) (h : History x d Y d₀ u v r N) :
    ChainState x d Y d₀ u v r B :=
  chainGhostOut x d Y d₀ u v r B (chainVisit s h (Fin.last N)) (h.1 (Fin.last N))

section
variable {x d Y d₀ u v r B}

/-- The visits of a history after its first edge are the visits of its tail from the state
after that edge. -/
theorem chainVisit_cons_succ {N : ℕ} (s : ChainState x d Y d₀ u v r B)
    (c : GhostChoice x d) (e : EdgeChoice x d Y d₀ u v r) (h : History x d Y d₀ u v r N)
    (j : Fin (N + 1)) :
    chainVisit (N := N + 1) s (Fin.cons c h.1, Fin.cons e h.2) j.succ =
      chainVisit (chainEdgeOut x d Y d₀ u v r B (chainGhostOut x d Y d₀ u v r B s c) e) h j := by
  induction j using Fin.induction with
  | zero => rfl
  | succ j ih =>
    simp only [chainVisit] at ih ⊢
    rw [Fin.induction_succ, Fin.induction_succ, ← Fin.succ_castSucc, ih]
    simp

/-- The end of a history is the end of its tail from the state after its first edge. -/
theorem chainEnd_cons {N : ℕ} (s : ChainState x d Y d₀ u v r B)
    (c : GhostChoice x d) (e : EdgeChoice x d Y d₀ u v r) (h : History x d Y d₀ u v r N) :
    chainEnd (N := N + 1) s (Fin.cons c h.1, Fin.cons e h.2) =
      chainEnd (chainEdgeOut x d Y d₀ u v r B (chainGhostOut x d Y d₀ u v r B s c) e) h := by
  rw [chainEnd, ← Fin.succ_last, chainVisit_cons_succ]
  rfl

/-- A history with no edges is a single ghost choice. -/
theorem sum_histories_zero {A : Type*} [AddCommMonoid A] (F : History x d Y d₀ u v r 0 → A) :
    ∑ h ∈ histories x d Y d₀ u v r B 0, F h =
      ∑ c ∈ multBox B ×ˢ multBox B, F (fun _ => c, Fin.elim0) := by
  refine sum_nbij' (fun h => h.1 0) (fun c => (fun _ => c, Fin.elim0)) ?_ ?_ ?_ ?_ ?_
  · intro h hh
    simp only [histories, mem_product, Fintype.mem_piFinset] at hh ⊢
    exact hh.1 0
  · intro c hc
    simp only [histories, mem_product, Fintype.mem_piFinset] at hc ⊢
    exact ⟨fun _ => hc, fun i => i.elim0⟩
  · intro h _
    exact Prod.ext (funext fun k => by rw [Fin.fin_one_eq_zero k]) (Subsingleton.elim _ _)
  · intro c _
    rfl
  · intro h _
    congr 1
    exact Prod.ext (funext fun k => by rw [Fin.fin_one_eq_zero k]) (Subsingleton.elim _ _)

/-- A history with `N + 1` edges is a first ghost choice, a first edge choice, and a history
with `N` edges. -/
theorem sum_histories_succ {A : Type*} [AddCommMonoid A] {N : ℕ} (F : History x d Y d₀ u v r (N + 1) → A) :
    ∑ h ∈ histories x d Y d₀ u v r B (N + 1), F h =
      ∑ c ∈ multBox B ×ˢ multBox B, ∑ e ∈ edgeChoices x d Y d₀ u v r,
        ∑ h ∈ histories x d Y d₀ u v r B N, F (Fin.cons c h.1, Fin.cons e h.2) := by
  simp only [← sum_product']
  refine sum_nbij' (fun h => (h.1 0, h.2 0, Fin.tail h.1, Fin.tail h.2))
    (fun t => (Fin.cons t.1 t.2.2.1, Fin.cons t.2.1 t.2.2.2)) ?_ ?_ ?_ ?_ ?_
  · intro h hh
    simp only [histories, mem_product, Fintype.mem_piFinset] at hh ⊢
    exact ⟨hh.1 0, hh.2 0, fun i => hh.1 _, fun i => hh.2 _⟩
  · intro t ht
    simp only [histories, mem_product, Fintype.mem_piFinset] at ht ⊢
    exact ⟨fun i => Fin.cases ht.1 ht.2.2.1 i, fun i => Fin.cases ht.2.1 ht.2.2.2 i⟩
  · intro h _
    simp
  · intro t _
    simp
  · intro h _
    simp

end

variable {x d Y d₀ u v r B} in
/-- The weight of the history `h` from `s`: the product of its ghost and edge
coefficients. -/
def chainWeight {N : ℕ} (s : ChainState x d Y d₀ u v r B) (h : History x d Y d₀ u v r N) : ℂ :=
  (∏ j : Fin (N + 1), chainGhostCoef q x d Y d₀ u v r B N j (chainVisit s h j) (h.1 j)) *
    ∏ j : Fin N, chainEdgeCoef q A₀ x d Y d₀ u v r B N
      (chainGhostOut x d Y d₀ u v r B (chainVisit s h j.castSucc) (h.1 j.castSucc)) (h.2 j)

/-- The birth addresses: the initial slots, the label of each group at each edge, and the
first `B` batch indices of each ghost. -/
abbrev BirthAddr (N : ℕ) :=
  (Fin K × Fin (padCount x + 1)) ⊕ (Fin N × Fin K) ⊕ (Fin (N + 1) × Fin B)

/-- The primes of a ghost batch, with multiplicity, in increasing order. -/
def batchPrimes (n : Particle x d → ℕ) : List ℕ :=
  (∑ xp : Particle x d, Multiset.replicate (n xp) xp.1.1).sort (· ≤ ·)

variable {x d Y d₀ u v r B} in
/-- The births of the history `h` from `s`: the prime born at each address, or `none` if the
address is not performed (a promoted label, or a batch index beyond the batch). -/
def births {N : ℕ} (s : ChainState x d Y d₀ u v r B) (h : History x d Y d₀ u v r N) :
    BirthAddr (K := K) x B N → Option ℕ
  | .inl (i, k) => some (s.2.1.1 i k)
  | .inr (.inl (j, i)) => if (h.2 j).2.2.2.1 i |>.2 then none else some ((h.2 j).2.2.2.1 i).1
  | .inr (.inr (j, k)) => (batchPrimes x d (h.1 j).2)[k.1]?

open scoped Classical in
/-- The history sum `∑_s μ(s) 𝐛(s) ∑_h w(s, h) 𝐛(end(s, h))` over the histories with distinct
births, with memory cap `B`; here `𝐛` is `chainInit`, the indicator of `e₁` with empty
memory. -/
def distinctSum (N : ℕ) : ℂ :=
  ∑ s, (chainMeasure q x d Y d₀ u v r B N s : ℂ) * chainInit x d Y d₀ u v r B s *
    ∑ h ∈ (histories x d Y d₀ u v r B N).filter (fun h => BirthsDistinct (births s h)),
      chainWeight q A₀ s h * chainInit x d Y d₀ u v r B (chainEnd s h)

end Chain

section Weights

variable {q x : ℝ} {d : Data K} {N : ℕ}

/-- The prime of a particle is a band prime. -/
theorem particle_mem_bandPrimes (xp : Particle x d) : xp.1.1 ∈ bandPrimes x d := by
  obtain ⟨p, hp, hxp⟩ := mem_biUnion.1 xp.2
  obtain ⟨ℓ, -, hℓ⟩ := mem_image.1 hxp
  rw [← hℓ]
  exact hp

/-- Two particles hitting the same position with the same prime are equal: the line of a
hitting particle is `[z]_p`. -/
theorem hitsAt_eq_of_prime {z : ℤ × ℤ} {xp yp : Particle x d} (hx : HitsAt x d z xp)
    (hy : HitsAt x d z yp) (h : xp.1.1 = yp.1.1) : xp = yp := by
  refine Subtype.ext (Prod.ext h ?_)
  rw [← hx, ← hy, h]

/-- A band prime is a band prime of the data. -/
theorem mem_bandPrimes_of_mem_band {i : Fin K} {p : ℕ} (hp : p ∈ band x (d.a i)) :
    p ∈ bandPrimes x d :=
  mem_biUnion.2 ⟨i, mem_univ i, hp⟩

/-- `ρ⁴ = √q`. -/
theorem pendingWeight_pow_four {q : ℝ} (hq : 0 < q) :
    pendingWeight q ^ 4 = Real.sqrt q := by
  unfold pendingWeight
  rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le, Real.sqrt_eq_rpow]
  norm_num

private theorem sum_dampDefect_le {q : ℝ} (hq : 0 ≤ q) (N : ℕ) :
    ∑ j ∈ range (N + 1), dampDefect q N j ≤ (N : ℝ) + 1 :=
  (sum_le_sum (g := fun _ => (1 : ℝ)) fun j _ => by
    unfold dampDefect
    split_ifs <;> linarith [Real.sqrt_nonneg q]).trans_eq (by simp)

/-- For primes `p ≥ 2N + 1` the baseline is at least one half. -/
theorem half_le_baseline {q : ℝ} (hq : 0 ≤ q) {N p : ℕ} (hp : 2 * N + 1 ≤ p) :
    1 / 2 ≤ baseline q N p := by
  have hNp : 2 * ((N : ℝ) + 1) ≤ p + 1 := by exact_mod_cast (show 2 * (N + 1) ≤ p + 1 by omega)
  have h := (inv_mul_le_iff₀ (by positivity : 0 < (p : ℝ) + 1)).2
    (show ∑ j ∈ range (N + 1), dampDefect q N j ≤ ((p : ℝ) + 1) * (1 / 2) by
      linarith [sum_dampDefect_le hq N])
  unfold baseline
  linarith

theorem baseline_nonneg {q : ℝ} (hq : 0 ≤ q) {N p : ℕ} (hp : N ≤ p) : 0 ≤ baseline q N p := by
  rw [baseline, sub_nonneg, inv_mul_le_iff₀ (by positivity), mul_one]
  exact (sum_dampDefect_le hq N).trans (by gcongr)

theorem baseline_mem_Icc {q : ℝ} (hq : 0 < q) (hq₁ : q < 1) {N p : ℕ} (hp : N < p) :
    0 ≤ baseline q N p ∧ baseline q N p ≤ 1 := by
  refine ⟨baseline_nonneg hq.le hp.le, ?_⟩
  have hsum := sum_nonneg fun j (_ : j ∈ range (N + 1)) => (dampDefect_mem_Icc hq hq₁ N j).1
  rw [baseline, sub_le_self_iff]
  positivity

/-- The harmonic mass is nonnegative. -/
private theorem harmonicMass_nonneg (S : Finset ℕ) : 0 ≤ harmonicMass S :=
  sum_nonneg fun p _ => by positivity

theorem primeMass_nonneg (p : ℕ) : 0 ≤ primeMass x d p :=
  sum_nonneg fun i _ => by split_ifs <;> first | exact harmonicMass_nonneg _ | rfl

/-- With band masses at most `1`, `V(p) ≤ K`. -/
theorem primeMass_le (hV : ∀ i, harmonicMass (band x (d.a i)) ≤ 1) (p : ℕ) :
    primeMass x d p ≤ K :=
  calc primeMass x d p ≤ ∑ _i : Fin K, (1 : ℝ) :=
        sum_le_sum fun i _ => by
          split_ifs
          · exact hV i
          · norm_num
    _ = K := by simp

theorem harmonicMass_le_primeMass {i : Fin K} {p : ℕ} (hp : p ∈ band x (d.a i)) :
    harmonicMass (band x (d.a i)) ≤ primeMass x d p := by
  simpa [primeMass, hp] using single_le_sum
    (f := fun i : Fin K => if p ∈ band x (d.a i) then harmonicMass (band x (d.a i)) else 0)
    (fun j _ => by split_ifs; exact harmonicMass_nonneg _; exact le_rfl) (mem_univ i)

/-- With band masses at least `1/2`, a prime of a band has `V(p) ≥ 1/2`. -/
theorem half_le_primeMass (hV : d.BandsLower x) {i : Fin K}
    {p : ℕ} (hpi : p ∈ band x (d.a i)) : 1 / 2 ≤ primeMass x d p :=
  (hV i).trans (harmonicMass_le_primeMass hpi)


/-- A nonnegative baseline suffices: outside the bands the weight vanishes. -/
theorem primeWeight_nonneg_of_nonneg_baseline (hb : ∀ p ∈ bandPrimes x d, 0 ≤ baseline q N p)
    (p : ℕ) : 0 ≤ primeWeight q x d N p := by
  by_cases hp : p ∈ bandPrimes x d
  · exact one_div_nonneg.2 (mul_nonneg (mul_nonneg (primeMass_nonneg p) (by positivity)) (hb p hp))
  · have h₀ : primeMass x d p = 0 :=
      sum_eq_zero fun i _ => ite_eq_right fun hpi => hp (mem_bandPrimes_of_mem_band hpi)
    simp [primeWeight, h₀]

theorem primeWeight_nonneg_of_baseline (hb : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p)
    (p : ℕ) : 0 ≤ primeWeight q x d N p :=
  primeWeight_nonneg_of_nonneg_baseline (fun p hp => (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (hb p hp)) p

/-- At a prime of band `i`, `0 < ν(p) ≤ 2 μ_i(p)` with `μ_i(p) = 1/(p V_i)`
(`mem:measure-masses`). -/
theorem primeWeight_le_two
    (hV : d.BandsLower x)
    (hb : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p) {i : Fin K} {p : ℕ}
    (hp : p ∈ band x (d.a i)) :
    0 < primeWeight q x d N p ∧
      primeWeight q x d N p ≤ 2 * (1 / (p * harmonicMass (band x (d.a i)))) := by
  have hVi : 0 < harmonicMass (band x (d.a i)) := by linarith [hV i]
  have hb₁ := hb p (mem_biUnion.2 ⟨i, mem_univ i, hp⟩)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (TypeII.band_prime hp).pos
  unfold primeWeight
  have hV₁ := harmonicMass_le_primeMass hp
  have hVpos := hVi.trans_le hV₁
  have hbase : 0 < baseline q N p := by linarith [hb₁]
  refine ⟨one_div_pos.2 (by positivity : 0 < primeMass x d p * (p + 1) * baseline q N p), ?_⟩
  rw [show 2 * (1 / (p * harmonicMass (band x (d.a i)))) =
    1 / (harmonicMass (band x (d.a i)) * p * (1 / 2)) by field_simp]
  exact one_div_le_one_div_of_le (by positivity)
    (mul_le_mul (mul_le_mul hV₁ (by linarith) hp0.le (by positivity)) hb₁
      (by norm_num) (by positivity))

/-- The birth weights of a band sum to at most `2`. -/
theorem sum_primeWeight_band_le_two
    (hV : d.BandsLower x)
    (hb : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p) (i : Fin K) :
    ∑ p ∈ band x (d.a i), primeWeight q x d N p ≤ 2 := by
  have hVi : 0 < harmonicMass (band x (d.a i)) := by linarith [hV i]
  calc ∑ p ∈ band x (d.a i), primeWeight q x d N p
      ≤ ∑ p ∈ band x (d.a i), 2 * (1 / (p * harmonicMass (band x (d.a i)))) :=
        sum_le_sum fun p hp => (primeWeight_le_two hV hb hp).2
    _ = 2 / harmonicMass (band x (d.a i)) * harmonicMass (band x (d.a i)) := by
        nth_rewrite 3 [harmonicMass]
        rw [mul_sum]
        refine sum_congr rfl fun p _ => ?_
        field_simp
    _ = 2 := by field_simp

/-- At a prime of a band, `0 < ν(p) ≤ 4/p`. -/
theorem primeWeight_pos_le (hV : d.BandsLower x)
    (hb : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p) {i : Fin K} {p : ℕ}
    (hp : p ∈ band x (d.a i)) :
    0 < primeWeight q x d N p ∧ primeWeight q x d N p ≤ 4 * (1 / p) := by
  obtain ⟨hpos, hbound⟩ := primeWeight_le_two hV hb hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (TypeII.band_prime hp).pos
  refine ⟨hpos, hbound.trans ?_⟩
  calc 2 * (1 / ((p : ℝ) * harmonicMass (band x (d.a i)))) ≤ 2 * (1 / (p * (1 / 2))) :=
        mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by positivity) (by gcongr; exact hV i)) (by norm_num)
    _ = 4 * (1 / p) := by field_simp; ring

/-- At a band prime, `ν(p) ≤ 4/p` and `V(p) ν(p) ≤ 2/p`. -/
theorem primeWeight_le {N : ℕ} (hV : d.BandsLower x)
    (hb : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p) {p : ℕ} (hp : p ∈ bandPrimes x d) :
    primeWeight q x d N p ≤ 4 * (1 / p) ∧
      primeMass x d p * primeWeight q x d N p ≤ 2 * (1 / p) := by
  obtain ⟨i, -, hpi⟩ := mem_biUnion.1 hp
  have hV₁ := half_le_primeMass hV hpi
  have hb₁ := hb p hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (TypeII.band_prime hpi).pos
  refine ⟨(primeWeight_pos_le hV hb hpi).2, ?_⟩
  rw [primeWeight]
  calc primeMass x d p * (1 / (primeMass x d p * ((p : ℝ) + 1) * baseline q N p))
      = 1 / (((p : ℝ) + 1) * baseline q N p) := by field_simp [show primeMass x d p ≠ 0 by linarith]
    _ ≤ 1 / (p * (1 / 2)) := one_div_le_one_div_of_le (by positivity) (by gcongr <;> linarith)
    _ = 2 * (1 / p) := by ring

/-- The hitting particles have one line per band prime, so a sum over them of a nonnegative
function of the prime is at most the sum over the band primes. -/
theorem sum_hits_le_sum_bandPrimes (z : ℤ × ℤ) {f : ℕ → ℝ} (hf : ∀ p, 0 ≤ f p) :
    ∑ xp with HitsAt x d z xp, f xp.1.1 ≤ ∑ p ∈ bandPrimes x d, f p := by
  rw [← sum_image (f := f) (g := fun xp : Particle x d => xp.1.1)]
  · exact sum_le_sum_of_subset_of_nonneg
      (image_subset_iff.2 fun xp _ => particle_mem_bandPrimes xp) fun p _ _ => hf p
  · intro xp hxp yp hyp h
    exact hitsAt_eq_of_prime (mem_filter.1 (mem_coe.1 hxp)).2 (mem_filter.1 (mem_coe.1 hyp)).2 h

/-- With band masses at most one, the harmonic mass of their union is at most `K`. -/
theorem sum_one_div_bandPrimes_le (hV : ∀ i, harmonicMass (band x (d.a i)) ≤ 1) :
    ∑ p ∈ bandPrimes x d, (1 : ℝ) / p ≤ K := by
  let S := univ.sigma fun i : Fin K => band x (d.a i)
  have h : bandPrimes x d = S.image Sigma.snd := by
    ext p
    simp only [S, bandPrimes, mem_biUnion, mem_image, mem_sigma, mem_univ, true_and]
    exact ⟨fun ⟨i, hi⟩ => ⟨⟨i, p⟩, hi, rfl⟩, fun ⟨⟨i, n⟩, hn, h⟩ => ⟨i, h ▸ hn⟩⟩
  rw [h]
  refine (sum_image_le_of_nonneg (fun p _ => by positivity)).trans ?_
  rw [sum_sigma]
  exact (sum_le_sum fun i _ => hV i).trans_eq (by simp)

/-- Eventually every band prime is at least `2N + 1` for `N = 2R`. -/
theorem eventually_two_mul_add_one_le {C CX alo ahi g : ℝ} (halo : 1 / 10 < alo) :
    ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d →
      ∀ p ∈ bandPrimes x d, 2 * (2 * momentPower x) + 1 ≤ p := by
  have hL := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp Real.tendsto_log_atTop
  filter_upwards [eventually_rpow_lt_of_mem_band (by linarith : 0 < alo) 1,
    hL.eventually_ge_atTop 8, Real.tendsto_log_atTop.eventually_gt_atTop 0]
    with x hbig hs8 hL0 d hd p hp
  obtain ⟨i, -, hpi⟩ := mem_biUnion.1 hp
  have hLp := hbig (d.a i) (hd.window i).1 p hpi
  rw [Real.rpow_one] at hLp
  set s := Real.log x ^ (1 / 2 : ℝ) with hs
  have hs8' : 8 ≤ s := hs8
  have hss : s * s = Real.log x := by rpow_ring hL0
  have hR : (momentPower x : ℝ) < s / 2 + 1 := by
    unfold momentPower
    exact Nat.ceil_lt_add_one (by linarith)
  have h8 : 8 * s ≤ s * s := mul_le_mul_of_nonneg_right hs8' (by linarith)
  have : ((2 * (2 * momentPower x) + 1 : ℕ) : ℝ) < p := by
    push_cast
    linarith
  exact_mod_cast this.le

section Boundary

variable {Y d₀ u v r : ℝ} {B : ℕ}

/-- The active labels of group `i` are primes of `𝒫_i`. -/
theorem chainState_mem_band (s : ChainState x d Y d₀ u v r B) (i : Fin K)
    (k : Fin (padCount x + 1)) : s.2.1.1 i k ∈ band x (d.a i) := by
  have h := s.2.1.2
  unfold lists at h
  exact Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 (mem_filter.1 h).1 i) k

/-- The chain measure is nonnegative when the birth weights of band primes are. -/
theorem chainMeasure_nonneg (hν : ∀ p ∈ bandPrimes x d, 0 ≤ primeWeight q x d N p)
    (s : ChainState x d Y d₀ u v r B) : 0 ≤ chainMeasure q x d Y d₀ u v r B N s :=
  mul_nonneg
    (prod_nonneg fun i _ => prod_nonneg fun k _ =>
      hν _ (mem_biUnion.2 ⟨i, mem_univ _, chainState_mem_band s i k⟩))
    (memWeight_nonneg (fun xp => hν _ (particle_mem_bandPrimes xp)) _)

/-- The boundary vector has entries zero or one. -/
theorem norm_sq_chainInit (s : ChainState x d Y d₀ u v r B) :
    ‖chainInit x d Y d₀ u v r B s‖ ^ 2 = ‖chainInit x d Y d₀ u v r B s‖ := by
  unfold chainInit
  split <;> simp

/-- **The boundary mass**: if the birth weights of each band sum to at most `c`, then
`∑_s μ(s) |𝐛(s)| ≤ c^{KM}`. On the support of `𝐛` the memory is empty, and the active lists
carry at most `∏_{i,k} ∑_{p ∈ 𝒫_i} ν(p)`. -/
theorem sum_chainMeasure_norm_chainInit_le {c : ℝ}
    (hν₀ : ∀ p ∈ bandPrimes x d, 0 ≤ primeWeight q x d N p)
    (hν : ∀ i, ∑ p ∈ band x (d.a i), primeWeight q x d N p ≤ c) :
    ∑ s, chainMeasure q x d Y d₀ u v r B N s * ‖chainInit x d Y d₀ u v r B s‖ ≤
      c ^ (K * (padCount x + 1)) := by
  -- on the support of `𝐛` the memory weight is one
  have hpt : ∀ s : ChainState x d Y d₀ u v r B,
      chainMeasure q x d Y d₀ u v r B N s * ‖chainInit x d Y d₀ u v r B s‖ =
        (if s.1.1 = (1, 0) then 1 else 0) *
          ((∏ i, ∏ k, primeWeight q x d N (s.2.1.1 i k)) *
            if memSize s.2.2.1 = 0 then 1 else 0) := by
    intro s
    unfold chainInit chainMeasure
    by_cases h₁ : s.1.1 = (1, 0) <;> by_cases h₂ : memSize s.2.2.1 = 0 <;> simp [h₁, h₂]
    have h0 : ∀ xp, s.2.2.1 xp = 0 := fun xp => by
      have := le_memSize s.2.2.1 xp
      omega
    simp [memWeight, h0]
  -- at most one position is `e₁`, and at most one memory is empty
  have hz : ∑ z : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r),
      (if z.1 = (1, 0) then (1 : ℝ) else 0) ≤ 1 := by
    have hc : #(univ.filter fun z : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) =>
        z.1 = (1, 0)) ≤ 1 :=
      card_le_one.2 fun a ha b hb =>
        Subtype.ext ((mem_filter.1 ha).2.trans (mem_filter.1 hb).2.symm)
    rw [sum_boole]
    exact_mod_cast hc
  have hS : ∑ S : MemState (Particle x d) B, (if memSize S.1 = 0 then (1 : ℝ) else 0) ≤ 1 := by
    have hc : #(univ.filter fun S : MemState (Particle x d) B => memSize S.1 = 0) ≤ 1 := by
      refine card_le_one.2 fun a ha b hb => Subtype.ext (funext fun xp => ?_)
      have ha' := le_memSize a.1 xp
      have hb' := le_memSize b.1 xp
      rw [(mem_filter.1 ha).2] at ha'
      rw [(mem_filter.1 hb).2] at hb'
      omega
    rw [sum_boole]
    exact_mod_cast hc
  -- the lists carry at most `c^{KM}`
  have hlists : ∑ a : ↥(lists x d (padCount x)), ∏ i, ∏ k, primeWeight q x d N (a.1 i k) ≤
      c ^ (K * (padCount x + 1)) :=
    calc ∑ a : ↥(lists x d (padCount x)), ∏ i, ∏ k, primeWeight q x d N (a.1 i k)
        = ∑ a ∈ lists x d (padCount x), ∏ i, ∏ k, primeWeight q x d N (a i k) :=
          sum_coe_sort _ (fun a : Lists K (padCount x) => ∏ i, ∏ k, primeWeight q x d N (a i k))
      _ ≤ ∑ a ∈ Fintype.piFinset fun i => Fintype.piFinset fun _ : Fin (padCount x + 1) =>
            band x (d.a i), ∏ i, ∏ k, primeWeight q x d N (a i k) := by
          refine sum_le_sum_of_subset_of_nonneg (by unfold lists; exact filter_subset _ _)
            fun a ha _ => prod_nonneg fun i _ => prod_nonneg fun k _ => hν₀ _ ?_
          exact mem_biUnion.2 ⟨i, mem_univ _,
            Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 ha i) k⟩
      _ = ∏ i, ∑ a ∈ Fintype.piFinset fun _ : Fin (padCount x + 1) => band x (d.a i),
            ∏ k, primeWeight q x d N (a k) :=
          (prod_univ_sum (fun i => Fintype.piFinset fun _ : Fin (padCount x + 1) =>
            band x (d.a i)) fun i a => ∏ k, primeWeight q x d N (a k)).symm
      _ = ∏ i, ∏ _k : Fin (padCount x + 1), ∑ p ∈ band x (d.a i), primeWeight q x d N p :=
          prod_congr rfl fun i _ => sum_prod_piFinset _ _
      _ ≤ ∏ _i : Fin K, ∏ _k : Fin (padCount x + 1), c :=
          prod_le_prod₀ (fun i _ => prod_nonneg fun k _ =>
              sum_nonneg fun p hp => hν₀ p (mem_biUnion.2 ⟨i, mem_univ _, hp⟩))
            fun i _ => prod_le_prod₀ (fun k _ =>
              sum_nonneg fun p hp => hν₀ p (mem_biUnion.2 ⟨i, mem_univ _, hp⟩))
              fun k _ => hν i
      _ = c ^ (K * (padCount x + 1)) := by
          rw [prod_const, prod_const, card_univ, card_univ, Fintype.card_fin, Fintype.card_fin,
            ← pow_mul, mul_comm]
  have hL : 0 ≤ ∑ a : ↥(lists x d (padCount x)), ∏ i, ∏ k, primeWeight q x d N (a.1 i k) :=
    sum_nonneg fun a _ => prod_nonneg fun i _ => prod_nonneg fun k _ =>
      hν₀ _ (mem_biUnion.2 ⟨i, mem_univ _,
        Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 (mem_filter.1 a.2).1 i) k⟩)
  calc ∑ s, chainMeasure q x d Y d₀ u v r B N s * ‖chainInit x d Y d₀ u v r B s‖
      = ∑ s : ChainState x d Y d₀ u v r B, (if s.1.1 = (1, 0) then 1 else 0) *
          ((∏ i, ∏ k, primeWeight q x d N (s.2.1.1 i k)) *
            if memSize s.2.2.1 = 0 then 1 else 0) := sum_congr rfl fun s _ => hpt s
    _ = (∑ z : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r),
          (if z.1 = (1, 0) then (1 : ℝ) else 0)) *
        ((∑ a : ↥(lists x d (padCount x)), ∏ i, ∏ k, primeWeight q x d N (a.1 i k)) *
          ∑ S : MemState (Particle x d) B, (if memSize S.1 = 0 then (1 : ℝ) else 0)) := by
        rw [sum_mul_sum, sum_mul_sum]
        simp only [Fintype.sum_prod_type, mul_sum]
    _ ≤ 1 * ((∑ a : ↥(lists x d (padCount x)), ∏ i, ∏ k, primeWeight q x d N (a.1 i k)) * 1) := by
        gcongr
    _ ≤ c ^ (K * (padCount x + 1)) := by rw [one_mul, mul_one]; exact hlists

end Boundary

end Weights

end Erdos408.OneSided
