
import system.random.basic data.nat.prime

instance fin.has_one' {n} [fact (0 < n)] : has_one (fin n) :=
⟨ fin.of_nat' 1 ⟩

instance fin.has_pow' {n} [fact (0 < n)] : has_pow (fin n) ℕ :=
⟨ monoid.pow ⟩

/-- fermat's primality test -/
def primality_test (p : ℕ) (h : fact (0 < p)) : rand bool :=
if h : p-1 ≥ 2 then do
  n ← rand.random_r _ 2 (p-1), -- `random_r` requires a proof of `2 ≤ p-1` but it is dischared using `assumption`
  return $ (fin.of_nat' n : fin p)^(p-1) = 1 -- we do arithmetic with `fin n` so that modulo and multiplication are interleaved
else return ff

def iterated_primality_test_aux (p : ℕ) (h : fact (0 < p)) : ℕ → rand bool
| 0 := pure tt
| (n+1) := do
  b ← primality_test p h,
  if b
    then iterated_primality_test_aux n
    else pure ff

def iterated_primality_test (p : ℕ) : rand bool :=
if h : 0 < p
  then iterated_primality_test_aux p h 10
  else pure ff

open tactic

/- this should print `[97, 101, 103, 107, 109, 113]` but
it uses a pseudo primality test and some composite numbers
also sneak in -/
run_cmd do
  let xs := list.range' 90 30,
  ps ← tactic.run_rand (xs.mfilter iterated_primality_test),
  trace ps

/- this should print `[97, 101, 103, 107, 109, 113]`. This
test is deterministic because we pick the random seed -/
run_cmd do
  let xs := list.range' 90 30,
  let ⟨ps, _⟩ := (xs.mfilter iterated_primality_test).run ⟨ mk_std_gen 10 ⟩,
  guard (ps = [97, 101, 103, 107, 109, 113]) <|> fail "wrong list of prime numbers",
  trace ps
