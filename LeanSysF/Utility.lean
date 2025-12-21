
@[simp]
def iterate (f : T -> T) : Nat -> T -> T
| 0 => λ x => x
| n + 1 => λ x => f $ (iterate f n) x

notation f "^[" n "]" => iterate f n

@[simp]
theorem iterate_succ {x : Nat} : ((· + 1)^[n]) x = x + n := by
  induction n <;> simp at *
  case succ n ih => rw [ih]; omega
