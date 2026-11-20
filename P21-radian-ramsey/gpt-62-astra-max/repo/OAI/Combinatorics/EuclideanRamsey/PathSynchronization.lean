/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/PathSynchronization.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Ported to the Lean module system; proofs simplified for the radian configuration.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.PathWords

@[expose] public noncomputable section

namespace OAI.EuclideanRamsey

variable {ι : Type*} {a : ι → ℂ}

def scaleGroup (c : ℝ) := letterLift (fun z => atom (Real.sqrt c • z))
lemma Path.scale {w lmb} (h : Path a w lmb) (c : ℝ) (hc : 0 ≤ c) :
    Path a (fun i => scaleGroup c (w i)) (c*lmb) := by
  induction h with
  | diag g => simpa using (Path.diag (a:=a) (scaleGroup c g))
  | copy p =>
    simpa [scaleGroup,value,mul_add, mul_assoc, ← Complex.sq_norm, mul_pow, Real.sq_sqrt hc] using
      Path.copy (a:=a) (Real.sqrt c • p.1,Real.sqrt c • p.2)
  | mul _ _ ihu ihv => simpa [Pi.mul_def, mul_add] using ihu.mul ihv

private lemma Path.power {w u} (h : Path a w u) (n : ℕ) : Path a (w^n) (n*u) := by
  simpa [Pi.pow_def] using Path.list (List.replicate n ()) (fun _ => h)

/-- A single word admits cost `1/k` for every possible size of the active
set in a Hales–Jewett line. Use a factorial as common denominator. -/
theorem unit_shares (wide : Wide a) (N : ℕ) : ∃ W, ∀ k ≤ N, 0 < k → Path a W (k:ℝ)⁻¹ := by
  let n := N.factorial
  have hn : 0 < n := Nat.factorial_pos _
  obtain ⟨w,u,v,hu,hv,h⟩ := wide ((n:ℝ)+1)⁻¹ (by positivity)
  obtain ⟨c,hc,rfl⟩ := exists_pos_add_of_lt' ((lt_inv_mul_iff₀ (by positivity)).mp h)
  have := hv.nonneg
  let d := n*v+c
  have hd : 0 < d := by positivity
  obtain ⟨F,fill⟩ : ∃ F, Path a F c := ⟨_,by simpa [Complex.normSq_ofReal,←sq,Real.sq_sqrt hc.le] using Path.copy (a:=a) ((Real.sqrt c : ℂ),0)⟩
  refine ⟨fun i => scaleGroup ((n:ℝ)*d)⁻¹ ((w^n*F) i),fun k hk hp => ?_⟩
  obtain ⟨m,hm : n = _⟩ := Nat.dvd_factorial hp hk
  cases m with
  | zero => simp_all
  | succ m =>
    have hmn : m ≤ n := by nlinarith
    have H := ((hu.power m).mul (hv.power (n-m))).mul fill
    rw [←pow_add,Nat.add_sub_of_le hmn,Nat.cast_sub hmn] at H
    convert H.scale ((n:ℝ)*d)⁻¹ (by positivity) using 1
    field_simp
    have eq : (n:ℝ) = k*(m+1) := by exact_mod_cast hm
    dsimp [d]; nlinarith

end OAI.EuclideanRamsey
