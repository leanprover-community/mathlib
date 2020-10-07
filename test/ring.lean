import tactic.ring
import data.real.basic

example (x y : ℕ) : x + y = y + x := by ring
example (x y : ℕ) : x + y + y = 2 * y + x := by ring
example (x y : ℕ) : x + id y = y + id x := by ring!
example {α} [comm_ring α] (x y : α) : x + y + y - x = 2 * y := by ring
example (x y : ℚ) : x / 2 + x / 2 = x := by ring
example (x y : ℚ) : (x + y) ^ 3 = x ^ 3 + y ^ 3 + 3 * (x * y ^ 2 + x ^ 2 * y) := by ring
example (x y : ℝ) : (x + y) ^ 3 = x ^ 3 + y ^ 3 + 3 * (x * y ^ 2 + x ^ 2 * y) := by ring
example {α} [comm_semiring α] (x : α) : (x + 1) ^ 6 = (1 + x) ^ 6 := by try_for 15000 {ring}
example (n : ℕ) : (n / 2) + (n / 2) = 2 * (n / 2) := by ring
example {α} [linear_ordered_field α] (a b c : α) :
  a * (-c / b) * (-c / b) + -c + c = a * (c / b * (c / b)) := by ring
example {α} [linear_ordered_field α] (a b c : α) :
  b ^ 2 - 4 * c * a = -(4 * c * a) + b ^ 2 := by ring
example (x : ℚ) : x ^ (2 + 2) = x^4 := by ring
example {α} [comm_ring α] (x : α) : x ^ 2 = x * x := by ring
example {α} [linear_ordered_field α] (a b c : α) :
  b ^ 2 - 4 * c * a = -(4 * c * a) + b ^ 2 := by ring
example {α} [linear_ordered_field α] (a b c : α) :
  b ^ 2 - 4 * a * c = 4 * a * 0 + b * b - 4 * a * c := by ring
example {α} [comm_semiring α] (x y z : α) (n : ℕ) :
  (x + y) * (z * (y * y) + (x * x ^ n + (1 + ↑n) * x ^ n * y)) =
    x * (x * x ^ n) + ((2 + ↑n) * (x * x ^ n) * y + (x * z + (z * y + (1 + ↑n) * x ^ n)) * (y * y)) := by ring
example {α} [comm_ring α] (a b c d e : α) :
  (-(a * b) + c + d) * e = (c + (d + -a * b)) * e := by ring
example (a n s: ℕ) : a * (n - s) = (n - s) * a := by ring

example (x y z : ℚ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
  x / (y / z) + y ⁻¹ + 1 / (y * -x) = -1/ (x * y) + (x * z + 1) / y :=
begin
  field_simp [hx, hy, hz],
  ring
end

example (a b c d x y : ℚ) (hx : x ≠ 0) (hy : y ≠ 0) :
  a + b / x - c / x^2 + d / x^3 = a + x⁻¹ * (y * b / y + (d / x - c) / x) :=
begin
  field_simp [hx, hy],
  ring
end

example : (876544 : ℤ) * -1 + (1000000 - 123456) = 0 := by ring
