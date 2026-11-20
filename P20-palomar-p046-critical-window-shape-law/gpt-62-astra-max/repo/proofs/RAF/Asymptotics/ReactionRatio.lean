module

public import proofs.RAF.Polymer.Counts

@[expose] public section

namespace RAF.Asymptotics

def binaryCardX (n : Nat) : Nat := 2 ^ (n + 1) - 2

theorem binaryCardX_tendsto : Filter.Tendsto binaryCardX Filter.atTop Filter.atTop := by
  have hsucc : Filter.Tendsto (fun n : Nat => n + 1) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono (fun n => Nat.le_succ n) Filter.tendsto_id
  have hpow : Filter.Tendsto (fun n : Nat => 2 ^ (n + 1))
      Filter.atTop Filter.atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : Nat) < 2)).comp hsucc
  apply Filter.tendsto_atTop.2
  intro b
  have hb : ∀ᶠ n in Filter.atTop, b + 2 ≤ 2 ^ (n + 1) :=
    hpow (Filter.eventually_ge_atTop (b + 2))
  filter_upwards [hb] with n hn
  simp only [binaryCardX]
  omega

end RAF.Asymptotics
