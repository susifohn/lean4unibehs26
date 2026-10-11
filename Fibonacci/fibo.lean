import Mathlib

/-!
# My Fibonacci project

Some experiments with Lean and Mathlib.
-/

#check Nat
#check Nat.add
#check add_mul

variable (a b c d : ℝ)
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  rw [ add_mul, mul_add, mul_add, ← add_assoc]

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
  calc
    (a + b) * (c + d) = a * (c + d) + b * (c + d) := by
      rw [add_mul]
    _ = (a * c + a * d) + (b * c + b * d) := by
      rw [mul_add, mul_add]
    _ = a * c + a * d + b * c + b * d := by
      rw [← add_assoc]
