import Mathlib

theorem my_sub_sq :
    ∀ (a b : ℤ), (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by
  intro a b
  rw [sq]
  rw [sub_mul]
  rw [mul_sub]
  rw [mul_sub]
  rw [← sub_add]
  rw [← sq]
  rw [← sq]
  rw [mul_comm b a]
  rw [Int.sub_sub]
  rw [← two_mul]
  rw [← mul_assoc]
