import data.nat.choose.sum

namespace nat

open finset

lemma choose_le_two_pow {n k : ℕ} : n.choose k ≤ 2 ^ n :=
begin
  cases le_or_lt k n,
  { rw ←sum_range_choose n,
    refine single_le_sum (λ _ _, zero_le') _,
    rwa mem_range_succ_iff },
  rw choose_eq_zero_of_lt h,
  exact zero_le'
end

end nat
