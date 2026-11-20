module

public import Erdos821.Blueprint.Classical
public import PrimeNumberTheoremAnd.IEANTN.Mertens

@[expose] public section

namespace Erdos821.P1

private theorem primesUpTo_eq (y : ℝ) :
    Erdos821.Blueprint.primesUpTo y = (Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime := by
  ext p
  simp [Erdos821.Blueprint.primesUpTo, Nat.lt_iff_add_one_le]

theorem mertens_proof : Erdos821.Blueprint.MertensEstimates := by
  constructor
  · simpa [primesUpTo_eq, one_div] using Mertens.sum_prime_div_eq_log_log
  · simpa [Erdos821.Blueprint.sieveProduct, primesUpTo_eq, one_div]
      using Mertens.tendsto_log_mul_primeProduct

end Erdos821.P1
