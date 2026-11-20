module
public import PottsDiscontinuity.TorusTopology.SquareSecants

/-! # Secants of a periodic simple lattice path

Move the forward end of every secant out one edge at a time. Summed over a
period the variation is independent of this separation: the mixed cells are
disjoint, and the two ends of the strip agree by translation. At separation
one it reads the tangent turn. At a full period every secant is the same deck
vector, and the variation is zero.
-/
@[expose] public section
namespace PottsDiscontinuity.TorusTopology
open FK Secant Planar.Medial Finset

theorem periodic_lattice_turn_eq_zero (f : ℕ → V) (hadj : ∀ n, G.Adj (f n) (f (n+1)))
    (hf : Function.Injective f) (L : ℕ) (D : V) (hL : 0 < L) (hper : ∀ n, f (n+L) = f n+D) :
    (∑ n ∈ range L, primalCompassQuarterTurn (lab (f n) (f (n+1))) (lab (f (n+1)) (f (n+2)))) = 0 := by
  let s := fun i k => f (i+k) - f i
  let H := fun i k => cut (s i k) (s i (k+1))
  let W := fun i k => cut (s i (k+1)) (s (i+1) k)
  let T := fun k => ∑ i ∈ range L, (H i k + W i k)
  have shift (g : ℕ → ℤ) (h : g L = g 0) : ∑ i ∈ range L, g (i+1) = ∑ i ∈ range L, g i := by
    have hh := sum_range_succ' g L; rw [sum_range_succ] at hh; omega
  have per i k : s (i+L) k = s i k := by
    simp only [s, show i+L+k=i+k+L by omega, hper]; abel
  have step (k) (hk : 1 ≤ k) : T (k+1) = T k := by
    have hc i : H i (k+1) + W i (k+1) = W i k + H (i+1) k := by
      have h := cell (hadj i) (hadj (i+(k+1))) (hf.ne (by omega)) (hf.ne (by omega)) (hf.ne (by omega)) (hf.ne (by omega))
      simpa only [s,H,W,Nat.add_assoc,Nat.add_comm 1 k,Nat.add_left_comm k 1] using h
    change ∑ i ∈ range L, _ = _; simp_rw [hc]; simp only [T,sum_add_distrib]
    rw [shift (fun i => H i k) (by have h := per 0; simpa [H] using congrArg₂ cut (h k) (h (k+1)))]; ring
  have ht : ∀ k, 1 ≤ k → T k = T 1 := fun _ h => Nat.le_induction rfl (fun k hk ih => (step k hk).trans ih) _ h
  have htop : T L = 0 := by
    apply sum_eq_zero; intro i _
    have h (j) : s j L = D := by simp [s,hper]
    simp only [H,W,h]
    have hxy := (squareLattice_adj_iff _ _).mp (hadj (i+L))
    rw [hper] at hxy
    have hv : (s i (L+1)).1 = D.1 ∨ (s i (L+1)).2 = D.2 := by
      dsimp [s]; rw [← Nat.add_assoc]; simp only [Prod.fst_add,Prod.snd_add] at hxy; omega
    rcases hv with h | h <;> simp only [cut,up,h,sub_self,ite_self,add_zero] <;> split_ifs <;> omega
  let A := fun i => idx (lab (f i) (f (i+1)))
  have hA : A L = A 0 := by
    have hp i : lab (f (i+L)) (f ((i+1)+L)) = lab (f i) (f (i+1)) := by simp [hper,lab]
    simpa [A,Nat.add_comm L 1] using congrArg idx (hp 0)
  have hturn i := local_turn (hadj i) (hadj (i+1)) (hf.ne (by omega))
  change ∑ i ∈ range L, _ = _
  calc
    _ = ∑ i ∈ range L, (A (i+1)-A i + 4*(H i 1+W i 1)) := sum_congr rfl fun i _ => hturn i
    _ = 0 := by rw [sum_add_distrib,sum_sub_distrib,shift A hA,sub_self,zero_add,← mul_sum]; change 4*T 1 = 0; rw [← ht L hL,htop,mul_zero]

end PottsDiscontinuity.TorusTopology
