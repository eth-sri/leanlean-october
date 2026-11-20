/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Need
public import ThreeSumApsp.Spec.Sec3.Theorem17.ClassStarts

/-! Layout and resource bounds for the host’s array passes. -/

@[expose] public section

open ThreeSumApsp.Spec

namespace Light.Sec3

open ThreeSumApsp

namespace Et17

/-- The source matrices, as a triangle instance with the addresses from `x`. -/
abbrev hostInput (X : HostData) (x : TriInst) : TriInst :=
  { x with n := X.n, AB := X.AB, BC := X.BC, AC := X.AC }

/-- The limits, the prime, and the three matrices below the free pointer. -/
structure Ready (lim : Limits) (d : ℕ) (x : TriInst) (X : HostData) (μ : ℕ → ℤ) (fr : ℕ) :
    Prop extends (hostInput X x).Arrays μ fr where
  space : (lim.space : ℤ) ≤ lim.word
  depth : d + 2 ≤ lim.depth
  prime : 1 ≤ X.p
  word : ((X.p * 2 ^ (bitLen x.U + 1) : ℕ) : ℤ) ≤ lim.word
  top : aFr X x.U fr < lim.space

variable {lim : Limits} {d : ℕ} {x : TriInst} {X : HostData} {μ : ℕ → ℤ} {fr : ℕ}

/-- There are at most n² + p chunks. -/
theorem Ready.chunkCount_le (hr : Ready lim d x X μ fr) (hcap : 1 ≤ X.cap) :
    X.chunkCount ≤ X.n * X.n + X.p :=
  length_chunkTab_le_add hcap fun i hi => lt_of_mem_residList hr.prime (by
    rw [List.getD_eq_getElem _ _ (by rw [HostData.RAB, length_residList, hr.arrAB.len]; exact hi)]
    exact List.getElem_mem _)

/-- Where the arrays lie, for the addresses of et17. -/
theorem hostLay_of (hr : Ready lim d x X μ fr) (hchunks : X.chunkCount ≤ X.n * X.n + X.p) :
    HostLay X (hostAddr x X fr) := by
  light_facts hr.arrAB hr.arrBC hr.arrAC
  dsimp only [hostInput] at *
  have hplaces := host_places X x.U fr
  have hcomm : X.D * X.n = X.n * X.D := Nat.mul_comm _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun t ht => ?_⟩
  case refine_13 =>
    have := X.w_le_cap ht
    simp only [hostAddr]
    omega
  all_goals
    simp only [hostAddr]
    omega

/-- What the third part needs holds for the data of a run of et17. -/
theorem ready_of {need : List ℕ → Need} {D g a b : ℕ} (hpre : x.Pre μ fr)
    (hbig : BigCase x.n D g) (hok : (hostNeedAt a b need x.n x.U D g).Ok lim fr d) :
    Ready lim d x (hostData x D g) μ fr := by
  have hD16 := hbig.sixteen_le
  have hcells := hok.cells
  have hdepth := hok.depth
  have htop := aFr_le (x := x) (g := g) hD16 fr
  have hp := two_le_hostData_p x g hD16
  have hps := Nat.mul_le_mul_right (2 ^ (bitLen x.U + 1)) (hostData_p_le x g hD16)
  simp only [hostNeedAt] at hcells hdepth
  exact
    { space := hok.space
      depth := by omega
      prime := by omega
      word := le_word_of_le_hostWord hok
      top := by omega
      toArrays := hpre.toArrays }

end Et17

end Light.Sec3
