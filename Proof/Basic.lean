import Mathlib

theorem my_add_sq :
    ∀ (a b : ℕ), (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  intro a b
  rw [sq]
  rw [add_mul]
  rw [mul_add]
  rw [mul_add]
  rw [← sq]
  rw [← sq]
  rw [← add_assoc]
  rw [add_assoc (a := a ^ 2)]
  rw [mul_comm (a := b)]
  rw [← two_mul]
  rw [← mul_assoc]

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

theorem my_add_add_sq :
    ∀ (a b c : ℕ), (a + b + c) ^ 2 =
      a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b + 2 * b * c + 2 * a * c := by
  intro a b c
  rw [sq]
  rw [add_mul]
  rw [add_mul]
  rw [mul_add]
  rw [mul_add]
  rw [mul_add]
  rw [mul_add]
  rw [mul_add]
  rw [mul_add]
  rw [← sq]
  rw [← sq]
  rw [← sq]
  rw [← add_assoc]
  rw [← add_assoc]
  rw [← add_assoc]
  rw [← add_assoc]
  rw[add_comm, add_assoc, add_assoc, add_comm (b*c), add_assoc (c*a)]
  rw [mul_comm c b, ← two_mul, ← mul_assoc]
  rw[← add_assoc (a ^ 2 + a * b + a * c + b * a + b ^ 2)]
  rw[← add_assoc, add_comm, ← add_assoc]
  rw[add_assoc (a^2), add_assoc (a^2), add_comm (a*b), mul_comm b a,add_assoc (a*c) , ← two_mul, ← mul_assoc]
  rw[add_comm (a*c), ← add_assoc (a^2), add_assoc (a ^ 2 + 2 * a * b), add_comm (a*c), add_assoc (a ^ 2 + 2 * a * b), add_assoc (b ^ 2 )]
  rw[mul_comm c a, ← two_mul, ← mul_assoc]
  rw[← add_assoc, ← add_assoc, ← add_assoc]
  rw[add_comm _ (a^2), add_comm _ (c^2), ← add_assoc, ]
  rw[add_right_comm _ (2*a*b), add_right_comm _ (2*b*c), add_right_comm _ (c^2), add_right_comm _ (2*b*c)]
